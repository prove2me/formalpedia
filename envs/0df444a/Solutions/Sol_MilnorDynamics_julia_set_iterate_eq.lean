-- Prove2me | solution 1 for MilnorDynamics.julia_set_iterate_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:04:57.646491+00:00
-- url     : https://prove2.me/submissions/5647ad79-6e1a-4a16-a6ed-1800de522ef0

import Mathlib
import Definitions.Def_MilnorDynamics_RationalMaps

open scoped OnePoint
open Filter Set Topology

namespace MilnorDynamics

noncomputable def aux_jie_S : OnePoint ℂ → ℂ
  | some z => ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z
  | none => 0

noncomputable def aux_jie_T : OnePoint ℂ → ℝ
  | some z => 1 - 2 / (1 + ‖z‖ ^ 2)
  | none => 1

lemma aux_jie_normsq (u : ℂ) : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

lemma aux_jie_cd_eq (a b : OnePoint ℂ) :
    chordalDist a b = Real.sqrt (‖aux_jie_S a - aux_jie_S b‖ ^ 2 + (aux_jie_T a - aux_jie_T b) ^ 2) := by
  rcases a with _ | z <;> rcases b with _ | w
  · simp [chordalDist, aux_jie_S, aux_jie_T]
  · have hB : 0 < 1 + ‖w‖ ^ 2 := by positivity
    have key : ‖aux_jie_S none - aux_jie_S (some w)‖ ^ 2 + (aux_jie_T none - aux_jie_T (some w)) ^ 2
        = (2 / Real.sqrt (1 + ‖w‖ ^ 2)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hB.le]
      simp only [aux_jie_S, aux_jie_T, zero_sub, norm_neg, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, mul_pow, sq_abs]
      field_simp
      ring
    rw [key, Real.sqrt_sq (by positivity)]
    rfl
  · have hB : 0 < 1 + ‖z‖ ^ 2 := by positivity
    have key : ‖aux_jie_S (some z) - aux_jie_S none‖ ^ 2 + (aux_jie_T (some z) - aux_jie_T none) ^ 2
        = (2 / Real.sqrt (1 + ‖z‖ ^ 2)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hB.le]
      simp only [aux_jie_S, aux_jie_T, sub_zero, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, mul_pow, sq_abs]
      field_simp
      ring
    rw [key, Real.sqrt_sq (by positivity)]
    rfl
  · have hA : 0 < 1 + ‖z‖ ^ 2 := by positivity
    have hB : 0 < 1 + ‖w‖ ^ 2 := by positivity
    have key : ‖aux_jie_S (some z) - aux_jie_S (some w)‖ ^ 2
        + (aux_jie_T (some z) - aux_jie_T (some w)) ^ 2
        = (2 * ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2))) ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
      simp only [aux_jie_S, aux_jie_T]
      rw [aux_jie_normsq (_ - _), aux_jie_normsq (z - w)]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      rw [aux_jie_normsq z] at hA ⊢
      rw [aux_jie_normsq w] at hB ⊢
      field_simp
      ring
    rw [key, Real.sqrt_sq (by positivity)]
    rfl

lemma aux_jie_S_coe (z : ℂ) : aux_jie_S (z : OnePoint ℂ) = ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z := rfl
lemma aux_jie_T_coe (z : ℂ) : aux_jie_T (z : OnePoint ℂ) = 1 - 2 / (1 + ‖z‖ ^ 2) := rfl
lemma aux_jie_S_infty : aux_jie_S ∞ = 0 := rfl
lemma aux_jie_T_infty : aux_jie_T ∞ = 1 := rfl

lemma aux_jie_S_cont : Continuous aux_jie_S := by
  rw [OnePoint.continuous_iff]
  simp only [aux_jie_S_coe, aux_jie_S_infty]
  constructor
  · rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    have h2 : Tendsto (fun z : ℂ => 2 * ‖z‖⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp tendsto_norm_cobounded_atTop).const_mul (2:ℝ)
    refine squeeze_zero_norm (fun z => ?_) h2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rcases eq_or_ne ‖z‖ 0 with h | h
    · simp [h]
    · have hz : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [sq_nonneg ‖z‖]
  · have : ∀ z : ℂ, (1 + ‖z‖ ^ 2) ≠ 0 := fun z => by positivity
    fun_prop (disch := exact this _)

lemma aux_jie_T_cont : Continuous aux_jie_T := by
  rw [OnePoint.continuous_iff]
  simp only [aux_jie_T_coe, aux_jie_T_infty]
  constructor
  · rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    have h1 : Tendsto (fun z : ℂ => 1 + ‖z‖ ^ 2) (Bornology.cobounded ℂ) atTop :=
      tendsto_atTop_add_const_left _ _ ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop)
    have h2 := (tendsto_const_nhds (x := (2:ℝ))).div_atTop h1
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub h2
  · have : ∀ z : ℂ, (1 + ‖z‖ ^ 2) ≠ 0 := fun z => by positivity
    fun_prop (disch := exact this _)

lemma aux_jie_cd_cont : Continuous (fun p : OnePoint ℂ × OnePoint ℂ => chordalDist p.1 p.2) := by
  simp only [aux_jie_cd_eq]
  have := aux_jie_S_cont
  have := aux_jie_T_cont
  fun_prop

lemma aux_jie_cd_nonneg (a b : OnePoint ℂ) : 0 ≤ chordalDist a b := by
  rw [aux_jie_cd_eq]; exact Real.sqrt_nonneg _

lemma aux_jie_cd_self (a : OnePoint ℂ) : chordalDist a a = 0 := by
  simp [aux_jie_cd_eq]

lemma aux_jie_cd_eq_zero (a b : OnePoint ℂ) (h : chordalDist a b = 0) : a = b := by
  rcases a with _ | z <;> rcases b with _ | w
  · rfl
  · exfalso
    have : 0 < chordalDist none (some w) := by
      show 0 < 2 / Real.sqrt (1 + ‖w‖ ^ 2)
      positivity
    linarith
  · exfalso
    have : 0 < chordalDist (some z) none := by
      show 0 < 2 / Real.sqrt (1 + ‖z‖ ^ 2)
      positivity
    linarith
  · have h' : 2 * ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2)) = 0 := h
    have hA : 0 < Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2) := by positivity
    rw [div_eq_zero_iff] at h'
    rcases h' with h' | h'
    · have : ‖z - w‖ = 0 := by linarith
      rw [norm_eq_zero, sub_eq_zero] at this
      rw [this]
    · linarith

lemma aux_jie_unif (h : OnePoint ℂ → OnePoint ℂ) (hh : Continuous h) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ a b, chordalDist a b < δ → chordalDist (h a) (h b) < ε := by
  set C : Set (OnePoint ℂ × OnePoint ℂ) := {p | ε ≤ chordalDist (h p.1) (h p.2)} with hC
  have hEc : Continuous (fun p : OnePoint ℂ × OnePoint ℂ => chordalDist (h p.1) (h p.2)) :=
    aux_jie_cd_cont.comp ((hh.comp continuous_fst).prodMk (hh.comp continuous_snd))
  have hCc : IsCompact C := (isClosed_le continuous_const hEc).isCompact
  rcases C.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun a b _ => ?_⟩
    by_contra hab
    have : (a, b) ∈ C := le_of_not_gt hab
    rw [he] at this; exact this
  · obtain ⟨x0, hx0, hmin⟩ := hCc.exists_isMinOn hne aux_jie_cd_cont.continuousOn
    refine ⟨chordalDist x0.1 x0.2, ?_, fun a b hab => ?_⟩
    · rcases (aux_jie_cd_nonneg x0.1 x0.2).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have := aux_jie_cd_eq_zero _ _ heq.symm
        have hx0' : ε ≤ chordalDist (h x0.1) (h x0.2) := hx0
        rw [this, aux_jie_cd_self] at hx0'
        linarith
    · by_contra hc
      have hm : (a, b) ∈ C := le_of_not_gt hc
      have h2 : chordalDist x0.1 x0.2 ≤ chordalDist a b := hmin hm
      linarith


lemma aux_jie_toFun_coe (f : RationalMap) (z : ℂ) : f.toFun (z : OnePoint ℂ) =
    if f.den.eval z = 0 then ∞ else ((f.num.eval z / f.den.eval z : ℂ) : OnePoint ℂ) := rfl

lemma aux_jie_toFun_infty (f : RationalMap) : f.toFun ∞ =
    if f.den.natDegree < f.num.natDegree then ∞
    else ((f.num.coeff f.den.natDegree / f.den.leadingCoeff : ℂ) : OnePoint ℂ) := rfl

lemma aux_jie_tendsto_infty {α : Type*} {l : Filter α} (p q : α → ℂ) (a : ℂ) (ha : a ≠ 0)
    (hp : Tendsto p l (𝓝 a)) (hq : Tendsto q l (𝓝 0)) :
    Tendsto (fun x => if q x = 0 then (∞ : OnePoint ℂ) else ((p x / q x : ℂ) : OnePoint ℂ))
      l (𝓝 ∞) := by
  rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
  rintro K ⟨-, hK⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have h1 : ∀ᶠ x in l, ‖a‖ / 2 < ‖p x‖ := hp.norm.eventually (lt_mem_nhds (by linarith))
  have h2 : ∀ᶠ x in l, ‖q x‖ < ‖a‖ / 2 / (|R| + 1) := by
    have := hq.norm; simp only [norm_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [h1, h2] with x hx1 hx2
  by_cases hqx : q x = 0
  · simp [hqx]
  · simp only [hqx, if_false]
    refine Or.inl ⟨p x / q x, fun hmem => ?_, rfl⟩
    have := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, norm_div] at this
    have hqpos : 0 < ‖q x‖ := norm_pos_iff.mpr hqx
    rw [div_le_iff₀ hqpos] at this
    rw [lt_div_iff₀ (by positivity)] at hx2
    nlinarith [mul_nonneg hqpos.le (sub_nonneg.2 (le_abs_self R))]

lemma aux_jie_reflect (P : Polynomial ℂ) (N : ℕ) (hN : P.natDegree ≤ N) (z : ℂ) (hz : z ≠ 0) :
    P.eval z = (Polynomial.reflect N P).eval z⁻¹ * z ^ N := by
  let _ := invertibleOfNonzero hz
  have := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) z N P hN
  rw [invOf_eq_inv] at this
  exact this.symm

lemma aux_jie_reflect_tendsto (P : Polynomial ℂ) (N : ℕ) :
    Tendsto (fun z : ℂ => (Polynomial.reflect N P).eval z⁻¹) (Bornology.cobounded ℂ)
      (𝓝 (P.coeff N)) := by
  have h := ((Polynomial.reflect N P).continuous.tendsto 0).comp tendsto_inv₀_cobounded
  have h0 : (Polynomial.reflect N P).eval 0 = P.coeff N := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect, Polynomial.revAt_zero]
  rw [h0] at h
  exact h

lemma aux_jie_num_ne_zero (f : RationalMap) (z : ℂ) (hz : f.den.eval z = 0) :
    f.num.eval z ≠ 0 := by
  obtain ⟨u, v, huv⟩ := f.coprime
  have := congrArg (Polynomial.eval z) huv
  simp only [Polynomial.eval_add, Polynomial.eval_mul, hz, mul_zero, add_zero,
    Polynomial.eval_one] at this
  intro h
  rw [h, mul_zero] at this
  exact zero_ne_one this

lemma aux_jie_cont (f : RationalMap) : Continuous f.toFun := by
  rw [continuous_iff_continuousAt]
  intro p
  induction p using OnePoint.rec with
  | infty =>
    rw [OnePoint.continuousAt_infty', Filter.coclosedCompact_eq_cocompact,
      ← Metric.cobounded_eq_cocompact]
    have hne : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z ≠ 0 := by
      filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with z hz
      exact norm_pos_iff.mp hz
    by_cases hnm : f.den.natDegree < f.num.natDegree
    · rw [aux_jie_toFun_infty, if_pos hnm]
      set m := f.num.natDegree
      have hnum0 : f.num ≠ 0 := by
        intro h0; simp [m, h0] at hnm
      have hL := aux_jie_tendsto_infty (l := Bornology.cobounded ℂ)
        (fun z => (Polynomial.reflect m f.num).eval z⁻¹)
        (fun z => (Polynomial.reflect m f.den).eval z⁻¹) (f.num.coeff m)
        (by simpa [m] using hnum0) (aux_jie_reflect_tendsto _ _)
        (by
          have := aux_jie_reflect_tendsto f.den m
          rwa [Polynomial.coeff_eq_zero_of_natDegree_lt hnm] at this)
      refine hL.congr' ?_
      filter_upwards [hne] with z hz
      have e1 := aux_jie_reflect f.num m le_rfl z hz
      have e2 := aux_jie_reflect f.den m hnm.le z hz
      have hzm : z ^ m ≠ 0 := pow_ne_zero _ hz
      simp only [Function.comp, aux_jie_toFun_coe, e1, e2, mul_eq_zero, hzm, or_false]
      split_ifs
      · rfl
      · rw [mul_div_mul_right _ _ hzm]
    · rw [aux_jie_toFun_infty, if_neg hnm]
      rw [not_lt] at hnm
      set n := f.den.natDegree
      have hlead : f.den.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr f.den_ne_zero
      have hG : Tendsto (fun z : ℂ => (Polynomial.reflect n f.num).eval z⁻¹ /
          (Polynomial.reflect n f.den).eval z⁻¹) (Bornology.cobounded ℂ)
          (𝓝 (f.num.coeff n / f.den.leadingCoeff)) :=
        (aux_jie_reflect_tendsto _ _).div (aux_jie_reflect_tendsto _ _) hlead
      have hd : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, (Polynomial.reflect n f.den).eval z⁻¹ ≠ 0 :=
        (aux_jie_reflect_tendsto f.den n).eventually_ne hlead
      refine ((OnePoint.continuous_coe.tendsto _).comp hG).congr' ?_
      filter_upwards [hne, hd] with z hz hdz
      have e1 := aux_jie_reflect f.num n hnm z hz
      have e2 := aux_jie_reflect f.den n le_rfl z hz
      have hzm : z ^ n ≠ 0 := pow_ne_zero _ hz
      simp only [Function.comp, aux_jie_toFun_coe, e1, e2, mul_eq_zero, hzm, or_false, hdz,
        if_false]
      rw [mul_div_mul_right _ _ hzm]
  | coe z =>
    rw [OnePoint.continuousAt_coe]
    by_cases hz : f.den.eval z = 0
    · have hfun : (f.toFun ∘ ((↑) : ℂ → OnePoint ℂ)) = fun w => if f.den.eval w = 0 then
          (∞ : OnePoint ℂ) else ((f.num.eval w / f.den.eval w : ℂ) : OnePoint ℂ) := by
        funext w; rfl
      have hval : (f.toFun ∘ ((↑) : ℂ → OnePoint ℂ)) z = ∞ := by
        simp [Function.comp, aux_jie_toFun_coe, hz]
      rw [ContinuousAt, hval, hfun]
      refine aux_jie_tendsto_infty _ _ (f.num.eval z) (aux_jie_num_ne_zero f z hz)
        (f.num.continuous.tendsto z) ?_
      have := f.den.continuous.tendsto z
      rwa [hz] at this
    · have hev : (fun w => ((f.num.eval w / f.den.eval w : ℂ) : OnePoint ℂ)) =ᶠ[𝓝 z]
          (f.toFun ∘ ((↑) : ℂ → OnePoint ℂ)) := by
        have : ∀ᶠ w in 𝓝 z, f.den.eval w ≠ 0 :=
          (f.den.continuous.continuousAt).eventually_ne hz
        filter_upwards [this] with w hw
        simp [Function.comp, aux_jie_toFun_coe, hw]
      refine ContinuousAt.congr_of_eventuallyEq ?_ hev.symm
      exact OnePoint.continuous_coe.continuousAt.comp
        (f.num.continuous.continuousAt.div f.den.continuous.continuousAt hz)


lemma aux_jie_mono (V : Set ℂ) (A B : Set (ℂ → OnePoint ℂ)) (hBA : B ⊆ A)
    (hA : IsNormalFamily V A) : IsNormalFamily V B :=
  fun F hF => hA F (fun n => hBA (hF n))

lemma aux_jie_sub (g : OnePoint ℂ → OnePoint ℂ) (k : ℕ) (c : ℂ → OnePoint ℂ) :
    (fun h : OnePoint ℂ → OnePoint ℂ => fun w => h (c w)) '' (Set.range fun n => (g^[k])^[n]) ⊆
    (fun h : OnePoint ℂ → OnePoint ℂ => fun w => h (c w)) '' (Set.range fun n => g^[n]) := by
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  exact ⟨g^[k * n], ⟨k * n, rfl⟩, by rw [Function.iterate_mul]⟩

lemma aux_jie_comp (g : OnePoint ℂ → OnePoint ℂ) (hg : Continuous g) (k : ℕ) (hk : 0 < k)
    (c : ℂ → OnePoint ℂ) (V : Set ℂ)
    (hN : IsNormalFamily V ((fun h : OnePoint ℂ → OnePoint ℂ => fun w => h (c w)) ''
      (Set.range fun n => (g^[k])^[n]))) :
    IsNormalFamily V ((fun h : OnePoint ℂ → OnePoint ℂ => fun w => h (c w)) ''
      (Set.range fun n => g^[n])) := by
  intro F hF
  have hF' : ∀ j, ∃ m : ℕ, (fun w => g^[m] (c w)) = F j := fun j => by
    obtain ⟨_, ⟨m, rfl⟩, e⟩ := hF j
    exact ⟨m, e⟩
  choose n hn using hF'
  obtain ⟨r, hr⟩ := Finite.exists_infinite_fiber
    (fun j => (⟨n j % k, Nat.mod_lt _ hk⟩ : Fin k))
  have hfreq : ∃ᶠ j in atTop, n j % k = r.1 := by
    rw [Nat.frequently_atTop_iff_infinite]
    refine (Set.infinite_coe_iff.mp hr).mono ?_
    intro j hj
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hj
    rw [← hj]
    rfl
  obtain ⟨φ0, hφ0, hφ0r⟩ := extraction_of_frequently_atTop hfreq
  have key : ∀ j x, F (φ0 j) x = g^[r.1] ((g^[k])^[n (φ0 j) / k] (c x)) := by
    intro j x
    rw [← hn (φ0 j), ← Function.iterate_mul, ← Function.iterate_add_apply, ← hφ0r j,
      Nat.mod_add_div]
  have hmem : ∀ j, (fun w => (g^[k])^[n (φ0 j) / k] (c w)) ∈
      (fun h : OnePoint ℂ → OnePoint ℂ => fun w => h (c w)) ''
        (Set.range fun n => (g^[k])^[n]) := fun j => ⟨_, ⟨n (φ0 j) / k, rfl⟩, rfl⟩
  obtain ⟨ψ, hψ, G, hGc, hGt⟩ := hN _ hmem
  have hgr : Continuous (g^[r.1]) := hg.iterate _
  refine ⟨φ0 ∘ ψ, hφ0.comp hψ, fun w => g^[r.1] (G w), hgr.comp_continuousOn hGc, ?_⟩
  intro K hK hKc ε hε
  obtain ⟨δ, hδ, hδε⟩ := aux_jie_unif _ hgr ε hε
  filter_upwards [hGt K hK hKc δ hδ] with j hj x hx
  simp only [Function.comp_apply]
  rw [key]
  exact hδε _ _ (hj x hx)

end MilnorDynamics

open MilnorDynamics

theorem solution (f : RationalMap) (hf : 1 ≤ f.degree) (k : ℕ) (hk : 0 < k) :
    juliaSet (f.toFun^[k]) = juliaSet f.toFun := by
  unfold juliaSet
  congr 1
  ext p
  simp only [fatouSet, Set.mem_setOf_eq]
  induction p using OnePoint.rec with
  | infty =>
    constructor
    · rintro ⟨V, hV, h0, hN⟩
      exact ⟨V, hV, h0, aux_jie_comp _ (aux_jie_cont f) k hk invChart V hN⟩
    · rintro ⟨V, hV, h0, hN⟩
      exact ⟨V, hV, h0, aux_jie_mono _ _ _ (aux_jie_sub _ k invChart) hN⟩
  | coe z =>
    constructor
    · rintro ⟨V, hV, h0, hN⟩
      exact ⟨V, hV, h0, aux_jie_comp _ (aux_jie_cont f) k hk OnePoint.some V hN⟩
    · rintro ⟨V, hV, h0, hN⟩
      exact ⟨V, hV, h0, aux_jie_mono _ _ _ (aux_jie_sub _ k OnePoint.some) hN⟩
