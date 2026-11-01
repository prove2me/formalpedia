-- Prove2me | solution 1 for MarketFreeze.Hetero.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:00:25.914783+00:00
-- url     : https://prove2.me/submissions/fc2ad782-b85e-4f95-8b24-dddb2de56540

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model
import Theorems.Thm_MarketFreeze_Hetero_eq_A9_indifference
import Theorems.Thm_MarketFreeze_Hetero_eq15LHS_strictMonoOn

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

lemma eq_int_iff (P : Params) (h0 : Standing P) (θ : ℝ) (hθ : θ ∈ Icc 0 P.θbar) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) :
    IsEquilibrium P θ s ↔ eq15LHS P θ (s / (1 - s)) = dPi P θ := by
  have hn : 0 < s / (1 - s) := div_pos hs0 (by linarith)
  rw [← (eq_A9_indifference P h0 θ hθ _ hn).2]
  unfold IsEquilibrium
  constructor
  · rintro ⟨-, -, -, -, h⟩; exact h hs0 hs1
  · intro h
    exact ⟨hs0.le, hs1.le, fun h' => by linarith, fun h' => by linarith, fun _ _ => h⟩

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

end MarketFreeze.Hetero.P2Aux

set_option maxHeartbeats 1000000 in
open MarketFreeze.Hetero MarketFreeze.Hetero.P2Aux Set in
theorem solution (P : Params)
    (h0 : Standing P) (h1 : Assumption1 P) (h2 : Assumption2 P)
    (h3 : Assumption3 P) (h4 : Assumption4 P) (h5 : Assumption5 P)
    (hlam : 0 < P.lam) (hA1 : CondA1 P) (hA3 : CondA3 P)
    (hA6 : CondA6 P) :
    ∃ θL θH : ℝ, 0 < θL ∧ θL < θH ∧ θH < P.θbar ∧
      CondA4 P θL ∧ CondA7 P θH ∧
      (∀ θ ∈ Set.Icc 0 P.θbar, CondA4 P θ → θ = θL) ∧
      (∀ θ ∈ Set.Icc 0 P.θbar, CondA7 P θ → θ = θH) ∧
      (∀ θ ∈ Set.Icc 0 θL, ∀ s : ℝ, IsEquilibrium P θ s ↔ s = 1) ∧
      (∀ θ ∈ Set.Icc θH P.θbar, ∀ s : ℝ, IsEquilibrium P θ s ↔ s = 0) ∧
      (∀ θ ∈ Set.Ioo θL θH,
        ∃ s : ℝ, 0 < s ∧ s < 1 ∧
          (∀ s' : ℝ, IsEquilibrium P θ s' ↔ s' = s) ∧
          eq15LHS P θ (s / (1 - s)) = dPi P θ) ∧
      (∀ lam' θL' θH' : ℝ, P.lam < lam' → lam' ≤ 1 →
        CondA3 { P with lam := lam' } → CondA6 { P with lam := lam' } →
        θL' ∈ Set.Icc 0 P.θbar → CondA4 { P with lam := lam' } θL' →
        θH' ∈ Set.Icc 0 P.θbar → CondA7 { P with lam := lam' } θH' →
        θL' < θL ∧ θH < θH') ∧
      (∀ θ₁ θ₂ s₁ s₂ : ℝ, θL < θ₁ → θ₁ < θ₂ → θ₂ < θH →
        IsEquilibrium P θ₁ s₁ → IsEquilibrium P θ₂ s₂ →
        s₂ / (1 - s₂) < s₁ / (1 - s₁) ∧
          price P (s₂ / (1 - s₂)) < price P (s₁ / (1 - s₁))) := by
  obtain ⟨hXI, hX, hb1⟩ := basics P h0 h1
  have hψ : 0 < P.ψ := h0.2.2.2.2.2.2
  have hb0 : 0 ≤ P.θbar := h0.2.2.2.1
  have hXI' : 0 < P.X - P.I := by linarith
  have hconc := dPi_concave P h0 h1 h2
  have hcont := dPi_cont P h0 h1 h2
  have mem0 : (0:ℝ) ∈ Icc 0 P.θbar := ⟨le_refl _, hb0⟩
  have memb : P.θbar ∈ Icc 0 P.θbar := ⟨hb0, le_refl _⟩
  have hA3' : (1 / 2 : ℝ) * P.lam * (P.X - P.I) < dPi P 0 := hA3
  have hA6' := hA6
  unfold CondA6 at hA6'
  have hd0 : 0 < dPi P 0 := by nlinarith
  -- the two families of functions
  set F : ℝ → ℝ → ℝ := fun l θ => dPi P θ - (1 / 2 : ℝ) * l * (1 - θ) * (P.X - P.I) with hFdef
  set G : ℝ → ℝ → ℝ := fun l θ => dPi P θ + (1 / 2 : ℝ) * l * (1 - θ) * (P.X - P.I) +
    P.ψ * l * (P.X - P.I) with hGdef
  have hFc : ∀ l, ConcaveOn ℝ (Icc 0 P.θbar) (F l) := by
    intro l
    refine (concave_add_affine hconc ((1 / 2 : ℝ) * l * (P.X - P.I))
      (-((1 / 2 : ℝ) * l * (P.X - P.I)))).congr ?_
    intro θ _; simp only [hFdef]; ring
  have hGc : ∀ l, ConcaveOn ℝ (Icc 0 P.θbar) (G l) := by
    intro l
    refine (concave_add_affine hconc (-((1 / 2 : ℝ) * l * (P.X - P.I)))
      ((1 / 2 : ℝ) * l * (P.X - P.I) + P.ψ * l * (P.X - P.I))).congr ?_
    intro θ _; simp only [hGdef]; ring
  have hFcont : ContinuousOn (F P.lam) (Icc 0 P.θbar) :=
    hcont.sub (by fun_prop)
  have hGcont : ContinuousOn (G P.lam) (Icc 0 P.θbar) :=
    (hcont.add (by fun_prop)).add (by fun_prop)
  have hF0 : 0 < F P.lam 0 := by simp only [hFdef]; linarith
  have hFb : F P.lam P.θbar < 0 := by
    simp only [hFdef]
    nlinarith [mul_pos (mul_pos hψ hlam) hXI', mul_nonneg (mul_nonneg hlam.le (sub_nonneg.2 hb1.le)) hXI'.le]
  have hG0 : 0 < G P.lam 0 := by
    simp only [hGdef]; nlinarith [mul_pos (mul_pos hψ hlam) hXI', mul_pos hlam hXI']
  have hGb : G P.lam P.θbar < 0 := by simp only [hGdef]; linarith
  -- θL
  obtain ⟨θL, hθLm, hFθL⟩ := intermediate_value_Icc' hb0 hFcont ⟨hFb.le, hF0.le⟩
  obtain ⟨θH, hθHm, hGθH⟩ := intermediate_value_Icc' hb0 hGcont ⟨hGb.le, hG0.le⟩
  obtain ⟨hFpos, hFneg⟩ := concave_sign (hFc P.lam) hF0 hθLm hFθL
  obtain ⟨hGpos, hGneg⟩ := concave_sign (hGc P.lam) hG0 hθHm hGθH
  have hθL0 : 0 < θL := by
    rcases eq_or_lt_of_le hθLm.1 with h | h
    · rw [← h] at hFθL; linarith
    · exact h
  have hdL : dPi P θL = (1 / 2 : ℝ) * P.lam * (1 - θL) * (P.X - P.I) := by
    simp only [hFdef] at hFθL; linarith
  have hGL : 0 < G P.lam θL := by
    simp only [hGdef]; rw [hdL]
    nlinarith [mul_pos (mul_pos hψ hlam) hXI',
      mul_nonneg (mul_nonneg hlam.le (sub_nonneg.2 (hθLm.2.trans hb1.le))) hXI'.le]
  have hLH : θL < θH := by
    rcases lt_trichotomy θL θH with h | h | h
    · exact h
    · rw [h] at hGL; linarith
    · linarith [hGneg θL hθLm h]
  have hHb : θH < P.θbar := by
    rcases eq_or_lt_of_le hθHm.2 with h | h
    · rw [h] at hGθH; linarith
    · exact h
  have hA4iff : ∀ θ, CondA4 P θ ↔ F P.lam θ = 0 := by
    intro θ; unfold CondA4; simp only [hFdef]; constructor <;> intro h <;> linarith
  have hA7iff : ∀ θ, CondA7 P θ ↔ G P.lam θ = 0 := by
    intro θ; unfold CondA7; simp only [hGdef]
  -- facts at an arbitrary θ in [0, θbar]
  have hθ1 : ∀ θ ∈ Icc 0 P.θbar, θ < 1 := fun θ hθ => lt_of_le_of_lt hθ.2 hb1
  -- interior characterization
  have hint : ∀ θ ∈ Icc 0 P.θbar, F P.lam θ < 0 → 0 < G P.lam θ → ∀ s,
      IsEquilibrium P θ s → 0 < s ∧ s < 1 ∧ eq15LHS P θ (s / (1 - s)) = dPi P θ := by
    intro θ hθ hF hG s hs
    have hs0 : 0 < s := by
      rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← h, eq_zero_iff] at hs; simp only [hGdef] at hG; linarith
      · exact h
    have hs1 : s < 1 := by
      rcases eq_or_lt_of_le hs.2.1 with h | h
      · rw [h, eq_one_iff] at hs; simp only [hFdef] at hF; linarith
      · exact h
    exact ⟨hs0, hs1, (eq_int_iff P h0 θ hθ s hs0 hs1).1 hs⟩
  have hmono := (eq15LHS_strictMonoOn P h0 hXI hlam)
  refine ⟨θL, θH, hθL0, hLH, hHb, (hA4iff θL).2 hFθL, (hA7iff θH).2 hGθH, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ hθ h
    rw [hA4iff] at h
    rcases lt_trichotomy θ θL with h' | h' | h'
    · linarith [hFpos θ hθ h']
    · exact h'
    · linarith [hFneg θ hθ h']
  · intro θ hθ h
    rw [hA7iff] at h
    rcases lt_trichotomy θ θH with h' | h' | h'
    · linarith [hGpos θ hθ h']
    · exact h'
    · linarith [hGneg θ hθ h']
  · intro θ hθ s
    have hθm : θ ∈ Icc 0 P.θbar := ⟨hθ.1, hθ.2.trans hθLm.2⟩
    have hF : 0 ≤ F P.lam θ := by
      rcases eq_or_lt_of_le hθ.2 with h | h
      · rw [h, hFθL]
      · exact (hFpos θ hθm h).le
    have hG : 0 < G P.lam θ := hGpos θ hθm (lt_of_le_of_lt hθ.2 hLH)
    simp only [hFdef] at hF
    simp only [hGdef] at hG
    constructor
    · intro hs
      rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← h, eq_zero_iff] at hs; linarith
      rcases eq_or_lt_of_le hs.2.1 with h' | h'
      · exact h'
      have := (eq_int_iff P h0 θ hθm s h h').1 hs
      have := eq15_upper P hXI hlam hψ θ (hθ1 θ hθm) (s / (1 - s))
        (div_nonneg h.le (by linarith))
      linarith
    · rintro rfl; rw [eq_one_iff]; linarith
  · intro θ hθ s
    have hθm : θ ∈ Icc 0 P.θbar := ⟨hθLm.1.trans (hLH.le.trans hθ.1), hθ.2⟩
    have hG : G P.lam θ ≤ 0 := by
      rcases eq_or_lt_of_le hθ.1 with h | h
      · rw [← h, hGθH]
      · exact (hGneg θ hθm h).le
    have hF : F P.lam θ < 0 := hFneg θ hθm (lt_of_lt_of_le hLH hθ.1)
    simp only [hFdef] at hF
    simp only [hGdef] at hG
    constructor
    · intro hs
      rcases eq_or_lt_of_le hs.2.1 with h' | h'
      · rw [h', eq_one_iff] at hs; linarith
      rcases eq_or_lt_of_le hs.1 with h | h
      · exact h.symm
      have := (eq_int_iff P h0 θ hθm s h h').1 hs
      have := eq15_lower P hXI hlam hψ θ (hθ1 θ hθm) (s / (1 - s))
        (div_pos h (by linarith))
      nlinarith
    · rintro rfl; rw [eq_zero_iff]; linarith
  · intro θ hθ
    have hθm : θ ∈ Icc 0 P.θbar := ⟨hθLm.1.trans hθ.1.le, hθ.2.le.trans hθHm.2⟩
    have hF : F P.lam θ < 0 := hFneg θ hθm hθ.1
    have hG : 0 < G P.lam θ := hGpos θ hθm hθ.2
    have hF' := hF
    have hG' := hG
    simp only [hFdef] at hF'
    simp only [hGdef] at hG'
    obtain ⟨u, hu0, hu1, heq⟩ := interior_exists P hXI hlam hψ θ (hθ1 θ hθm) (dPi P θ)
      (by nlinarith) (by nlinarith)
    have hn : (1 - u) / (1 - (1 - u)) = (1 - u) / u := by ring_nf
    refine ⟨1 - u, by linarith, by linarith, ?_, heq⟩
    intro s'
    constructor
    · intro hs
      obtain ⟨hs0, hs1, hse⟩ := hint θ hθm hF hG s' hs
      have hn' : 0 < s' / (1 - s') := div_pos hs0 (by linarith)
      have hnn : 0 < (1 - u) / (1 - (1 - u)) := by rw [hn]; exact div_pos (by linarith) hu0
      have := (hmono θ (hθ1 θ hθm)).1.injOn (x₁ := s' / (1 - s')) (x₂ := (1 - u) / (1 - (1 - u)))
        (mem_Ici.2 hn'.le) (mem_Ici.2 hnn.le) (by rw [hse, heq])
      rw [hn] at this
      have h1s : (1 - s') ≠ 0 := by linarith
      field_simp at this
      nlinarith
    · rintro rfl
      exact (eq_int_iff P h0 θ hθm _ (by linarith) (by linarith)).2 heq
  · intro lam' θL' θH' hll hl1 hA3l _ hθL'm hA4l hθH'm hA7l
    have hA3l' : (1 / 2 : ℝ) * lam' * (P.X - P.I) < dPi P 0 := hA3l
    have hA4l' : -dPi P θL' + (1 / 2 : ℝ) * lam' * (1 - θL') * (P.X - P.I) = 0 := hA4l
    have hA7l' : dPi P θH' + (1 / 2 : ℝ) * lam' * (1 - θH') * (P.X - P.I) +
        P.ψ * lam' * (P.X - P.I) = 0 := hA7l
    have hF'0 : 0 < F lam' 0 := by simp only [hFdef]; linarith
    have hF'r : F lam' θL' = 0 := by simp only [hFdef]; linarith
    have hG'0 : 0 < G lam' 0 := by
      simp only [hGdef]
      nlinarith [mul_pos (mul_pos hψ (hlam.trans hll)) hXI', mul_pos (hlam.trans hll) hXI']
    have hG'r : G lam' θH' = 0 := by simp only [hGdef]; linarith
    obtain ⟨hF'pos, -⟩ := concave_sign (hFc lam') hF'0 hθL'm hF'r
    obtain ⟨-, hG'neg⟩ := concave_sign (hGc lam') hG'0 hθH'm hG'r
    have hFL : F lam' θL < 0 := by
      simp only [hFdef]; rw [hdL]
      have : 0 < 1 - θL := by linarith [hθ1 θL hθLm]
      nlinarith [mul_pos (mul_pos (sub_pos.2 hll) this) hXI']
    have hGH : 0 < G lam' θH := by
      have hGθH' := hGθH
      simp only [hGdef] at hGθH' ⊢
      have : 0 < 1 - θH := by linarith [hθ1 θH hθHm]
      nlinarith [mul_pos (mul_pos (sub_pos.2 hll) this) hXI',
        mul_pos (mul_pos hψ (sub_pos.2 hll)) hXI']
    constructor
    · rcases lt_trichotomy θL' θL with h | h | h
      · exact h
      · rw [h] at hF'r; linarith
      · linarith [hF'pos θL hθLm h]
    · rcases lt_trichotomy θH θH' with h | h | h
      · exact h
      · rw [h] at hGH; linarith
      · linarith [hG'neg θH hθHm h]
  · intro θ₁ θ₂ s₁ s₂ h1L h12 h2H hs₁ hs₂
    have hm1 : θ₁ ∈ Icc 0 P.θbar := ⟨hθLm.1.trans h1L.le, (h12.trans h2H).le.trans hθHm.2⟩
    have hm2 : θ₂ ∈ Icc 0 P.θbar := ⟨hθLm.1.trans (h1L.trans h12).le, h2H.le.trans hθHm.2⟩
    obtain ⟨a0, a1, ae⟩ := hint θ₁ hm1 (hFneg θ₁ hm1 h1L) (hGpos θ₁ hm1 (h12.trans h2H)) s₁ hs₁
    obtain ⟨b0, b1, be⟩ := hint θ₂ hm2 (hFneg θ₂ hm2 (h1L.trans h12)) (hGpos θ₂ hm2 h2H) s₂ hs₂
    -- D strictly decreasing on [θL, θbar]
    have hD := concave_add_affine hconc ((1 / 2 : ℝ) * P.lam * (P.X - P.I)) 0
    have hDlt : dPi P θL + ((1 / 2 : ℝ) * P.lam * (P.X - P.I) * θL + 0) <
        dPi P 0 + ((1 / 2 : ℝ) * P.lam * (P.X - P.I) * 0 + 0) := by
      rw [hdL]; nlinarith
    have hDec := concave_strictAnti hD hθL0 hDlt h1L.le h12 hm2.2
    set n₁ := s₁ / (1 - s₁) with hn₁
    set n₂ := s₂ / (1 - s₂) with hn₂
    have hn1 : 0 < n₁ := div_pos a0 (by linarith)
    have hn2 : 0 < n₂ := div_pos b0 (by linarith)
    have hlt : n₂ < n₁ := by
      by_contra hcon
      push Not at hcon
      unfold eq15LHS at ae be
      set u₁ := 1 / (n₁ + 1) with hu₁
      set u₂ := 1 / (n₂ + 1) with hu₂
      have e1 : (n₁ - 1) / (n₁ + 1) = 1 - 2 * u₁ := by rw [hu₁]; field_simp; ring
      have e2 : (n₂ - 1) / (n₂ + 1) = 1 - 2 * u₂ := by rw [hu₂]; field_simp; ring
      have f1 : P.ψ / (n₁ + 1) ^ 2 = P.ψ * u₁ ^ 2 := by rw [hu₁]; field_simp
      have f2 : P.ψ / (n₂ + 1) ^ 2 = P.ψ * u₂ ^ 2 := by rw [hu₂]; field_simp
      rw [e1, f1] at ae
      rw [e2, f2] at be
      have hu1p : 0 < u₁ := by positivity
      have hu21 : u₂ ≤ u₁ := one_div_le_one_div_of_le (by linarith) (by linarith)
      have hu2p : 0 < u₂ := by positivity
      have hK : 0 < P.lam * (P.X - P.I) := mul_pos hlam hXI'
      have h1θ2 : 0 < 1 - θ₂ := by linarith [hθ1 θ₂ hm2]
      nlinarith [mul_pos (mul_pos hK (sub_pos.2 h12)) hu1p,
        mul_nonneg (mul_nonneg hK.le h1θ2.le) (sub_nonneg.2 hu21),
        mul_nonneg (mul_nonneg hK.le hψ.le) (mul_nonneg (sub_nonneg.2 hu21) (add_pos hu1p hu2p).le)]
    refine ⟨hlt, ?_⟩
    unfold price
    have : (P.X - P.I) / (1 + n₁) < (P.X - P.I) / (1 + n₂) :=
      div_lt_div_of_pos_left hXI' (by linarith) (by linarith)
    linarith
