-- Prove2me | solution 1 for MarketFreeze.Hetero.dPi_strictConcaveOn
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:10:43.457441+00:00
-- url     : https://prove2.me/submissions/85959281-cf29-4c6d-b708-b48d1098672a

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero.P2Aux

open MarketFreeze.Hetero Set

lemma cc {h : ℝ → ℝ} {s : Set ℝ} (hc : ConcaveOn ℝ s h) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * h x + t * h y ≤ h ((1 - t) * x + t * y) := by
  have := hc.2 hx hy (sub_nonneg.2 ht1) ht0 (by ring)
  simpa only [smul_eq_mul] using this

/-- Concave function, positive at `0`, vanishing at `r ∈ [0,b]`: positive before `r`,
negative after `r`. -/
lemma concave_sign {h : ℝ → ℝ} {b r : ℝ} (hc : ConcaveOn ℝ (Icc 0 b) h) (h0 : 0 < h 0)
    (hr : r ∈ Icc 0 b) (hhr : h r = 0) :
    (∀ θ ∈ Icc 0 b, θ < r → 0 < h θ) ∧ (∀ θ ∈ Icc 0 b, r < θ → h θ < 0) := by
  have hr0 : 0 < r := by
    rcases eq_or_lt_of_le hr.1 with h' | h'
    · subst h'; linarith
    · exact h'
  have h0mem : (0:ℝ) ∈ Icc 0 b := ⟨le_refl _, hr.1.trans hr.2⟩
  constructor
  · intro θ hθ hθr
    have key := cc hc h0mem hr (θ / r) (div_nonneg hθ.1 hr0.le) (by rw [div_le_one hr0]; linarith)
    simp only [mul_zero, zero_add] at key
    have : θ / r * r = θ := by field_simp
    rw [this, hhr, mul_zero, add_zero] at key
    have : 0 < 1 - θ / r := by rw [sub_pos, div_lt_one hr0]; exact hθr
    nlinarith
  · intro θ hθ hθr
    have hθ0 : 0 < θ := hr0.trans hθr
    have key := cc hc h0mem hθ (r / θ) (div_nonneg hr0.le hθ0.le) (by rw [div_le_one hθ0]; linarith)
    simp only [mul_zero, zero_add] at key
    have : r / θ * θ = r := by field_simp
    rw [this, hhr] at key
    have h1 : 0 < 1 - r / θ := by rw [sub_pos, div_lt_one hθ0]; exact hθr
    have h2 : 0 < r / θ := div_pos hr0 hθ0
    by_contra hc'
    push Not at hc'
    nlinarith [mul_pos h1 h0, mul_nonneg h2.le hc']

/-- Concave function on `[0,b]` with `h r < h 0` for some `r > 0` is strictly decreasing
on `[r, b]`. -/
lemma concave_strictAnti {h : ℝ → ℝ} {b r : ℝ} (hc : ConcaveOn ℝ (Icc 0 b) h)
    (hr0 : 0 < r) (hlt : h r < h 0) {x y : ℝ} (hrx : r ≤ x) (hxy : x < y) (hyb : y ≤ b) :
    h y < h x := by
  have h0mem : (0:ℝ) ∈ Icc 0 b := ⟨le_refl _, (hr0.le.trans hrx).trans (hxy.le.trans hyb)⟩
  have hy0 : 0 < y := lt_of_lt_of_le hr0 (hrx.trans hxy.le)
  have hymem : y ∈ Icc 0 b := ⟨hy0.le, hyb⟩
  -- first, h y < h 0
  have hy : h y < h 0 := by
    have key := cc hc h0mem hymem (r / y) (div_nonneg hr0.le hy0.le) (by rw [div_le_one hy0]; linarith)
    simp only [mul_zero, zero_add] at key
    have : r / y * y = r := by field_simp
    rw [this] at key
    have h2 : 0 < r / y := div_pos hr0 hy0
    nlinarith
  have hx0 : 0 < x := hr0.trans_le hrx
  have key := cc hc h0mem hymem (x / y) (div_nonneg hx0.le hy0.le) (by rw [div_le_one hy0]; linarith)
  simp only [mul_zero, zero_add] at key
  have : x / y * y = x := by field_simp
  rw [this] at key
  have h1 : 0 < 1 - x / y := by rw [sub_pos, div_lt_one hy0]; exact hxy
  nlinarith [mul_lt_mul_of_pos_left hy h1]

lemma concave_add_affine {h : ℝ → ℝ} {b : ℝ} (hc : ConcaveOn ℝ (Icc 0 b) h) (α β : ℝ) :
    ConcaveOn ℝ (Icc 0 b) (fun θ => h θ + (α * θ + β)) := by
  refine hc.add ⟨convex_Icc 0 b, ?_⟩
  intro x _ y _ a c _ _ hac
  simp only [smul_eq_mul]
  have : c = 1 - a := by linarith
  subst this
  apply le_of_eq; ring

lemma concave_inv_part {b K : ℝ} (hb : b < 1) (hK : 0 ≤ K) :
    ConcaveOn ℝ (Icc 0 b) (fun θ : ℝ => -K / (1 - θ)) := by
  refine ⟨convex_Icc 0 b, ?_⟩
  intro x hx y hy a c ha hc hac
  simp only [smul_eq_mul]
  have hu : 0 < 1 - x := by linarith [hx.2]
  have hv : 0 < 1 - y := by linarith [hy.2]
  have hc' : c = 1 - a := by linarith
  subst hc'
  have hw : 1 - (a * x + (1 - a) * y) = a * (1 - x) + (1 - a) * (1 - y) := by ring
  rw [hw]
  set u := 1 - x
  set v := 1 - y
  have hc0 : 0 ≤ 1 - a := hc
  have hw' : 0 < a * u + (1 - a) * v := by
    nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hc0]
  have key : K / (a * u + (1 - a) * v) ≤ a * (K / u) + (1 - a) * (K / v) := by
    rw [div_le_iff₀ hw']
    have e : (a * (K / u) + (1 - a) * (K / v)) * (a * u + (1 - a) * v)
        = K * (a ^ 2 + (1 - a) ^ 2) + a * (1 - a) * K * (u / v + v / u) := by
      field_simp; ring
    rw [e]
    have : 2 ≤ u / v + v / u := by
      rw [div_add_div _ _ hv.ne' hu.ne', le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (u - v)]
    nlinarith [mul_nonneg (mul_nonneg ha hc0) hK]
  have e1 : a * (-K / u) + (1 - a) * (-K / v) = -(a * (K / u) + (1 - a) * (K / v)) := by ring
  rw [e1, neg_div]
  linarith


lemma basics (P : Params) (h0 : Standing P) (h1 : Assumption1 P) :
    P.I < P.X ∧ 0 < P.X ∧ P.θbar < 1 := by
  obtain ⟨hI, hδ0, hδ1, -, hθb, -, -⟩ := h0
  have hXI : P.I < P.X := by nlinarith [h1.1]
  have hX : 0 < P.X := hI.trans hXI
  refine ⟨hXI, hX, hθb.trans ?_⟩
  rw [div_lt_one hX]; exact hXI

lemma dPi_concave (P : Params) (h0 : Standing P) (h1 : Assumption1 P) (h2 : Assumption2 P) :
    ConcaveOn ℝ (Icc 0 P.θbar) (dPi P) := by
  obtain ⟨hXI, hX, hb⟩ := basics P h0 h1
  have hψ : 0 < P.ψ := h0.2.2.2.2.2.2
  have hc : 0 < P.c := h0.2.2.2.2.2.1
  have hK : 0 ≤ 2 * P.ψ * (P.X - P.I + P.c) := by
    have : 0 < P.X - P.I + P.c := by linarith
    positivity
  have hA := concave_inv_part hb hK
  have hY : ConcaveOn ℝ (Icc 0 P.θbar) P.Y := h2.2.1
  have hψY := hY.smul hψ.le
  have hf : ConcaveOn ℝ (Icc 0 P.θbar) (fun θ : ℝ => (1 - θ)) := by
    refine ⟨convex_Icc 0 P.θbar, ?_⟩
    intro x _ y _ a c _ _ hac
    simp only [smul_eq_mul]
    apply le_of_eq
    have : c = 1 - a := by linarith
    subst this; ring
  have hg : ConcaveOn ℝ (Icc 0 P.θbar) (fun θ : ℝ => P.Y θ - P.Y 0) := by
    have := concave_add_affine hY 0 (-P.Y 0)
    refine this.congr ?_
    intro θ _
    simp only; ring
  have hprod := hf.mul hg (fun x hx => by show (0:ℝ) ≤ 1 - x; linarith [hx.2])
    (fun x hx => by
      show (0:ℝ) ≤ P.Y x - P.Y 0
      have := h2.1 ⟨le_refl 0, h0.2.2.2.1⟩ hx hx.1
      linarith)
    (by
      intro i hi j hj hgij
      simp only at hgij ⊢
      by_contra hcon
      push Not at hcon
      have := h2.1 hj hi (by linarith)
      linarith)
  have hprod2 := hprod.smul (c := (1 / 2 : ℝ)) (by norm_num)
  have hsum := concave_add_affine ((hA.add hψY).add hprod2)
    (-(P.X / 2) - (P.X - P.I) - P.Y 0 / 2) (P.X / 2 - P.c + 2 * P.ψ * (P.X - P.I) + P.Y 0 / 2)
  refine hsum.congr ?_
  intro θ hθ
  have h1θ : 1 - θ ≠ 0 := by linarith [hθ.2]
  simp only [Pi.add_apply, Pi.mul_apply, smul_eq_mul, dPi, piS, piNS, Ehom]
  field_simp
  ring


lemma dPi_cont (P : Params) (h0 : Standing P) (h1 : Assumption1 P) (h2 : Assumption2 P) :
    ContinuousOn (dPi P) (Icc 0 P.θbar) := by
  obtain ⟨-, -, hb⟩ := basics P h0 h1
  have hY : ContinuousOn P.Y (Icc 0 P.θbar) :=
    fun x hx => (h2.2.2.1 x hx).continuousAt.continuousWithinAt
  have hq : ContinuousOn (fun θ : ℝ => (2 * θ * (P.X - P.I) + 2 * P.c) / (1 - θ))
      (Icc 0 P.θbar) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) (fun x hx => by linarith [hx.2])
  have : ContinuousOn (fun θ : ℝ => P.X - P.I - P.ψ * ((2 * θ * (P.X - P.I) + 2 * P.c) / (1 - θ)
      - P.Y θ) - P.c - ((θ + (1 / 2 : ℝ) * (1 - θ)) * P.X - P.I + θ * (P.X - P.I) -
        (1 / 2 : ℝ) * (1 - θ) * P.Y θ)) (Icc 0 P.θbar) := by
    apply_rules [ContinuousOn.sub, ContinuousOn.add, ContinuousOn.mul, continuousOn_const,
      continuousOn_id]
  exact this

lemma eq_one_iff (P : Params) (θ : ℝ) :
    IsEquilibrium P θ 1 ↔ (1 / 2 : ℝ) * P.lam * (1 - θ) * (P.X - P.I) ≤ dPi P θ := by
  unfold IsEquilibrium soleSellerProfit dPi
  constructor
  · rintro ⟨-, -, h, -, -⟩; linarith [h rfl]
  · intro h
    refine ⟨by norm_num, le_refl _, fun _ => by linarith, fun h' => by norm_num at h',
      fun _ h' => by norm_num at h'⟩

lemma buyer0 (P : Params) (θ : ℝ) :
    buyerProfit P θ 0 = piS P θ + P.ψ * P.lam * (P.X - P.I) +
      (1 / 2 : ℝ) * P.lam * (1 - θ) * (P.X - P.I) := by
  unfold buyerProfit icLHS Ehet price buyerMeet piS
  simp only [add_zero, div_one]
  ring

lemma eq_zero_iff (P : Params) (θ : ℝ) :
    IsEquilibrium P θ 0 ↔ dPi P θ + (1 / 2 : ℝ) * P.lam * (1 - θ) * (P.X - P.I) +
      P.ψ * P.lam * (P.X - P.I) ≤ 0 := by
  unfold IsEquilibrium
  rw [buyer0]
  unfold dPi
  constructor
  · rintro ⟨-, -, -, h, -⟩; linarith [h rfl]
  · intro h
    refine ⟨le_refl _, by norm_num, fun h' => by norm_num at h', fun _ => by linarith,
      fun h' _ => by norm_num at h'⟩

lemma eq15_upper (P : Params) (hXI : P.I < P.X) (hlam : 0 < P.lam) (hψ : 0 < P.ψ)
    (θ : ℝ) (hθ : θ < 1) (n : ℝ) (hn : 0 ≤ n) :
    eq15LHS P θ n < (1 / 2 : ℝ) * P.lam * (1 - θ) * (P.X - P.I) := by
  unfold eq15LHS
  have hK : 0 < P.lam * (P.X - P.I) := mul_pos hlam (by linarith)
  have h1 : (n - 1) / (n + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h2 : 0 < P.ψ / (n + 1) ^ 2 := by positivity
  have h3 : (1 - θ) / 2 * ((n - 1) / (n + 1)) - P.ψ / (n + 1) ^ 2 < (1 - θ) / 2 := by
    nlinarith
  nlinarith

lemma eq15_lower (P : Params) (hXI : P.I < P.X) (hlam : 0 < P.lam) (hψ : 0 < P.ψ)
    (θ : ℝ) (hθ : θ < 1) (n : ℝ) (hn : 0 < n) :
    -(P.lam * (P.X - P.I) * ((1 - θ) / 2 + P.ψ)) < eq15LHS P θ n := by
  unfold eq15LHS
  have hK : 0 < P.lam * (P.X - P.I) := mul_pos hlam (by linarith)
  have h1 : -1 < (n - 1) / (n + 1) := by rw [lt_div_iff₀ (by linarith)]; linarith
  have h2 : P.ψ / (n + 1) ^ 2 < P.ψ := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith [mul_pos hψ (show 0 < (n + 1) ^ 2 - 1 by nlinarith)]
  have h3 : -((1 - θ) / 2 + P.ψ) < (1 - θ) / 2 * ((n - 1) / (n + 1)) - P.ψ / (n + 1) ^ 2 := by
    nlinarith
  nlinarith


lemma interior_exists (P : Params) (hXI : P.I < P.X) (hlam : 0 < P.lam) (hψ : 0 < P.ψ)
    (θ : ℝ) (hθ : θ < 1) (d : ℝ)
    (hlo : -(P.lam * (P.X - P.I) * ((1 - θ) / 2 + P.ψ)) < d)
    (hhi : d < (1 / 2 : ℝ) * P.lam * (1 - θ) * (P.X - P.I)) :
    ∃ u : ℝ, 0 < u ∧ u < 1 ∧ eq15LHS P θ ((1 - u) / (1 - (1 - u))) = d := by
  let q : ℝ → ℝ := fun u => P.lam * (P.X - P.I) * ((1 - θ) / 2 * (1 - 2 * u) - P.ψ * u ^ 2)
  have hqc : ContinuousOn q (Icc 0 1) := by fun_prop
  have hq0 : d < q 0 := by simp only [q]; nlinarith
  have hq1 : q 1 < d := by simp only [q]; nlinarith
  obtain ⟨u, hum, hqu⟩ := intermediate_value_Icc' (zero_le_one) hqc ⟨hq1.le, hq0.le⟩
  have hu0 : 0 < u := by
    rcases eq_or_lt_of_le hum.1 with h | h
    · rw [← h] at hqu; linarith
    · exact h
  have hu1 : u < 1 := by
    rcases eq_or_lt_of_le hum.2 with h | h
    · rw [h] at hqu; linarith
    · exact h
  refine ⟨u, hu0, hu1, ?_⟩
  rw [← hqu]
  have hn : (1 - u) / (1 - (1 - u)) = (1 - u) / u := by ring_nf
  rw [hn]
  unfold eq15LHS
  have hu0' : u ≠ 0 := hu0.ne'
  have : (1 - u) / u + 1 = 1 / u := by field_simp; ring
  rw [this]
  show _ = P.lam * (P.X - P.I) * ((1 - θ) / 2 * (1 - 2 * u) - P.ψ * u ^ 2)
  field_simp
  ring

lemma hasDerivAt_Ehom (P : Params) (θ : ℝ) (hθ : θ < 1) (hY : DifferentiableAt ℝ P.Y θ) :
    HasDerivAt (Ehom P) (2 * (P.X - P.I + P.c) / (1 - θ) ^ 2 - deriv P.Y θ) θ := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * x * (P.X - P.I) + 2 * P.c) (2 * (P.X - P.I)) θ := by
    have := ((hasDerivAt_id θ).const_mul 2).mul_const (P.X - P.I) |>.add_const (2 * P.c)
    simpa using this
  have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) θ := by
    simpa using (hasDerivAt_id θ).const_sub 1
  have h3 := (h1.div h2 (by linarith)).sub hY.hasDerivAt
  have hne : (1 - θ) ≠ 0 := by linarith
  have e : (2 * (P.X - P.I) * (1 - θ) - (2 * θ * (P.X - P.I) + 2 * P.c) * -1) / (1 - θ) ^ 2
      - deriv P.Y θ = 2 * (P.X - P.I + P.c) / (1 - θ) ^ 2 - deriv P.Y θ := by
    congr 1; ring
  rw [← e]
  exact h3


lemma strict_inv_part {b K : ℝ} (hb : b < 1) (hK : 0 < K) :
    StrictConcaveOn ℝ (Icc 0 b) (fun θ : ℝ => -K / (1 - θ)) := by
  refine ⟨convex_Icc 0 b, ?_⟩
  intro x hx y hy hxy a c ha hc hac
  simp only [smul_eq_mul]
  have hu : 0 < 1 - x := by linarith [hx.2]
  have hv : 0 < 1 - y := by linarith [hy.2]
  have hc' : c = 1 - a := by linarith
  subst hc'
  have hw : 1 - (a * x + (1 - a) * y) = a * (1 - x) + (1 - a) * (1 - y) := by ring
  rw [hw]
  have huv : 1 - x ≠ 1 - y := by intro h; apply hxy; linarith
  set u := 1 - x
  set v := 1 - y
  have hw' : 0 < a * u + (1 - a) * v := by nlinarith
  have key : K / (a * u + (1 - a) * v) < a * (K / u) + (1 - a) * (K / v) := by
    rw [div_lt_iff₀ hw']
    have e : (a * (K / u) + (1 - a) * (K / v)) * (a * u + (1 - a) * v)
        = K * (a ^ 2 + (1 - a) ^ 2) + a * (1 - a) * K * (u / v + v / u) := by
      field_simp; ring
    rw [e]
    have : 2 < u / v + v / u := by
      rw [div_add_div _ _ hv.ne' hu.ne', lt_div_iff₀ (by positivity)]
      have : 0 < (u - v) ^ 2 := by
        have : u - v ≠ 0 := sub_ne_zero.2 huv
        positivity
      nlinarith
    have : 0 < a * (1 - a) * K := by positivity
    nlinarith
  have e1 : a * (-K / u) + (1 - a) * (-K / v) = -(a * (K / u) + (1 - a) * (K / v)) := by ring
  rw [e1, neg_div]
  linarith

lemma accPt_Icc_of_mem_Ioo {a b θ : ℝ} (h : θ ∈ Ioo a b) : AccPt θ (Filter.principal (Icc a b)) := by
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  set m := min (ε / 2) ((b - θ) / 2) with hm
  have hm0 : 0 < m := lt_min (by linarith) (by linarith [h.2])
  have hm1 : m ≤ ε / 2 := min_le_left _ _
  have hm2 : m ≤ (b - θ) / 2 := min_le_right _ _
  refine ⟨θ + m, ⟨hball ?_, ⟨by linarith [h.1], by linarith⟩⟩, by linarith⟩
  rw [Metric.mem_ball, Real.dist_eq]
  rw [abs_of_pos (by linarith)]; linarith

end MarketFreeze.Hetero.P2Aux

open MarketFreeze.Hetero MarketFreeze.Hetero.P2Aux Set in
theorem solution (P : Params)
    (h0 : Standing P) (h1 : Assumption1 P) (h2 : Assumption2 P)
    (h3 : Assumption3 P) (h4 : Assumption4 P) (h5 : Assumption5 P) :
    StrictConcaveOn ℝ (Set.Icc 0 P.θbar) (dPi P) ∧
    (∀ θ ∈ Set.Ioo 0 P.θbar, DifferentiableAt ℝ (deriv P.Y) θ →
      deriv (deriv (dPi P)) θ =
        (P.ψ + (1 / 2 : ℝ) * (1 - θ)) * deriv (deriv P.Y) θ -
          deriv P.Y θ - 4 * P.ψ * (P.X - P.I + P.c) / (1 - θ) ^ 3 ∧
      deriv (deriv (dPi P)) θ < 0) := by
  obtain ⟨hXI, hX, hb⟩ := basics P h0 h1
  have hψ : 0 < P.ψ := h0.2.2.2.2.2.2
  have hc : 0 < P.c := h0.2.2.2.2.2.1
  have hK0 : 0 < P.X - P.I + P.c := by linarith
  have hK : 0 < 2 * P.ψ * (P.X - P.I + P.c) := by positivity
  constructor
  · have hA := strict_inv_part hb hK
    have hY : ConcaveOn ℝ (Icc 0 P.θbar) P.Y := h2.2.1
    have hψY := hY.smul hψ.le
    have hf : ConcaveOn ℝ (Icc 0 P.θbar) (fun θ : ℝ => (1 - θ)) := by
      refine ⟨convex_Icc 0 P.θbar, ?_⟩
      intro x _ y _ a c _ _ hac
      simp only [smul_eq_mul]
      apply le_of_eq
      have : c = 1 - a := by linarith
      subst this; ring
    have hg : ConcaveOn ℝ (Icc 0 P.θbar) (fun θ : ℝ => P.Y θ - P.Y 0) := by
      have := concave_add_affine hY 0 (-P.Y 0)
      refine this.congr ?_
      intro θ _
      simp only; ring
    have hprod := hf.mul hg (fun x hx => by show (0:ℝ) ≤ 1 - x; linarith [hx.2])
      (fun x hx => by
        show (0:ℝ) ≤ P.Y x - P.Y 0
        have := h2.1 ⟨le_refl 0, h0.2.2.2.1⟩ hx hx.1
        linarith)
      (by
        intro i hi j hj hgij
        simp only at hgij ⊢
        by_contra hcon
        push Not at hcon
        have := h2.1 hj hi (by linarith)
        linarith)
    have hprod2 := hprod.smul (c := (1 / 2 : ℝ)) (by norm_num)
    have hrest := concave_add_affine (hψY.add hprod2)
      (-(P.X / 2) - (P.X - P.I) - P.Y 0 / 2) (P.X / 2 - P.c + 2 * P.ψ * (P.X - P.I) + P.Y 0 / 2)
    refine (hA.add_concaveOn hrest).congr ?_
    intro θ hθ
    have h1θ : 1 - θ ≠ 0 := by linarith [hθ.2]
    simp only [Pi.add_apply, Pi.mul_apply, smul_eq_mul, dPi, piS, piNS, Ehom]
    field_simp
    ring
  · intro θ hθ hYd2
    have hθm : θ ∈ Icc 0 P.θbar := Ioo_subset_Icc_self hθ
    have hθ1 : θ < 1 := lt_trans hθ.2 hb
    -- first derivative of dPi
    have hfun : dPi P = fun x => (P.X / 2 - P.c) + (-(P.X / 2 + (P.X - P.I))) * x -
        P.ψ * Ehom P x + (1 / 2 : ℝ) * ((1 - x) * P.Y x) := by
      funext x; simp only [dPi, piS, piNS]; ring
    have hD1 : ∀ x, x < 1 → DifferentiableAt ℝ P.Y x → HasDerivAt (dPi P)
        (P.ψ * deriv P.Y x + 1 / 2 * (1 - x) * deriv P.Y x -
          2 * P.ψ * (P.X - P.I + P.c) * ((1 - x) * (1 - x))⁻¹ - P.X / 2 - (P.X - P.I) -
          P.Y x / 2) x := by
      intro x hx hYx
      have hE := hasDerivAt_Ehom P x hx hYx
      have hl : HasDerivAt (fun x : ℝ => (P.X / 2 - P.c) + (-(P.X / 2 + (P.X - P.I))) * x)
          (-(P.X / 2 + (P.X - P.I)) * 1) x :=
        ((hasDerivAt_id x).const_mul _).const_add _
      have h1x : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      have hp := (h1x.mul hYx.hasDerivAt).const_mul (1 / 2 : ℝ)
      have hall := (hl.sub (hE.const_mul P.ψ)).add hp
      have hall' : HasDerivAt (fun x => (P.X / 2 - P.c) + (-(P.X / 2 + (P.X - P.I))) * x -
          P.ψ * Ehom P x + (1 / 2 : ℝ) * ((1 - x) * P.Y x)) _ x := hall
      rw [hfun]
      have hne : 1 - x ≠ 0 := by linarith
      refine hall'.congr_deriv ?_
      field_simp
      ring
    have hev : deriv (dPi P) =ᶠ[nhds θ] (fun x => P.ψ * deriv P.Y x + 1 / 2 * (1 - x) * deriv P.Y x -
          2 * P.ψ * (P.X - P.I + P.c) * ((1 - x) * (1 - x))⁻¹ - P.X / 2 - (P.X - P.I) -
          P.Y x / 2) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
      exact (hD1 x (lt_trans hx.2 hb) (h2.2.2.1 x (Ioo_subset_Icc_self hx))).deriv
    rw [hev.deriv_eq]
    have hYθ : DifferentiableAt ℝ P.Y θ := h2.2.2.1 θ hθm
    have h1x : HasDerivAt (fun x : ℝ => 1 - x) (-1) θ := by
      simpa using (hasDerivAt_id θ).const_sub 1
    have hne : 1 - θ ≠ 0 := by linarith
    have hinv := (h1x.mul h1x).inv (mul_ne_zero hne hne)
    have hD2 := ((((hYd2.hasDerivAt.const_mul P.ψ).add
      ((h1x.const_mul (1 / 2 : ℝ)).mul hYd2.hasDerivAt)).sub
      (hinv.const_mul (2 * P.ψ * (P.X - P.I + P.c)))).sub_const (P.X / 2)).sub_const (P.X - P.I)
      |>.sub (hYθ.hasDerivAt.div_const 2)
    have hformula : deriv (fun x => P.ψ * deriv P.Y x + 1 / 2 * (1 - x) * deriv P.Y x -
          2 * P.ψ * (P.X - P.I + P.c) * ((1 - x) * (1 - x))⁻¹ - P.X / 2 - (P.X - P.I) -
          P.Y x / 2) θ = (P.ψ + (1 / 2 : ℝ) * (1 - θ)) * deriv (deriv P.Y) θ -
        deriv P.Y θ - 4 * P.ψ * (P.X - P.I + P.c) / (1 - θ) ^ 3 := by
      have hD2' : HasDerivAt (fun x => P.ψ * deriv P.Y x + 1 / 2 * (1 - x) * deriv P.Y x -
          2 * P.ψ * (P.X - P.I + P.c) * ((1 - x) * (1 - x))⁻¹ - P.X / 2 - (P.X - P.I) -
          P.Y x / 2) _ θ := hD2
      rw [hD2'.deriv]
      simp only [Pi.mul_apply]
      field_simp
      ring
    refine ⟨hformula, ?_⟩
    rw [hformula]
    -- signs
    have hacc := accPt_Icc_of_mem_Ioo hθ
    have hY2 : deriv (deriv P.Y) θ ≤ 0 :=
      hYd2.hasDerivAt.hasDerivWithinAt.nonpos_of_antitoneOn hacc
        (h2.2.1.antitoneOn_deriv h2.2.2.1)
    have hY1 : 0 ≤ deriv P.Y θ :=
      hYθ.hasDerivAt.hasDerivWithinAt.nonneg_of_monotoneOn hacc h2.1
    have h3pos : 0 < 4 * P.ψ * (P.X - P.I + P.c) / (1 - θ) ^ 3 := by
      have : 0 < 1 - θ := by linarith
      positivity
    have hcoef : 0 < P.ψ + (1 / 2 : ℝ) * (1 - θ) := by linarith
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hcoef.le hY2]
