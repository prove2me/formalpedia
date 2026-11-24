-- Prove2me | solution 1 for HamLocality237.Testing.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T09:49:16.862799+00:00
-- url     : https://prove2.me/submissions/a8451152-bbac-4ede-8b2f-26849bc6daff

import Definitions.Def_HamLocality237_Testing_Adversary

open MeasureTheory Set QAlgorithms ComplexConjugate
open scoped BigOperators TensorProduct

namespace HamLocality237.Testing



theorem ac_of_dist_le {X : Type*} [PseudoMetricSpace X] {f : ℝ → X} {G : ℝ → ℝ} {a b C : ℝ}
    (hC : 0 ≤ C) (hG : AbsolutelyContinuousOnInterval G a b)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ C * dist (G x) (G y)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hG ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hG (ε / (C + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hs => ?_⟩
  have h1 := hδ' E hE hs
  calc ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)
      ≤ ∑ i ∈ Finset.range E.1, C * dist (G (E.2 i).1) (G (E.2 i).2) :=
        Finset.sum_le_sum (fun i hi => h _ (hE.1 i hi).1 _ (hE.1 i hi).2)
    _ = C * ∑ i ∈ Finset.range E.1, dist (G (E.2 i).1) (G (E.2 i).2) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (ε / (C + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith

theorem ac_pow {G : ℝ → ℝ} {a b : ℝ} (hG : AbsolutelyContinuousOnInterval G a b) :
    ∀ m : ℕ, AbsolutelyContinuousOnInterval (fun x => G x ^ m) a b
  | 0 => by
    simp only [pow_zero]
    exact ((LipschitzWith.const (1 : ℝ)).lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval
  | m + 1 => by
    simp only [pow_succ]
    exact (ac_pow hG m).fun_mul hG

set_option linter.unusedSectionVars false

section Dyson
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The accumulated norm. -/
noncomputable def dG (F : ℝ → E →L[ℂ] E) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, ‖F s‖

theorem dG_props (F : ℝ → E →L[ℂ] E) (tf : ℝ) (htf : 0 ≤ tf)
    (hint : IntegrableOn F (Icc 0 tf)) :
    AbsolutelyContinuousOnInterval (dG F) 0 tf ∧ ContinuousOn (dG F) (Icc 0 tf) ∧
    (∀ᵐ x, x ∈ uIcc 0 tf → HasDerivAt (dG F) (‖F x‖) x) ∧
    (∀ t ∈ Icc 0 tf, 0 ≤ dG F t ∧ dG F t ≤ dG F tf) := by
  have hn : IntegrableOn (fun s => ‖F s‖) (Icc 0 tf) := hint.norm
  have hii : IntervalIntegrable (fun s => ‖F s‖) volume 0 tf :=
    (hn.mono_set (by rw [uIcc_of_le htf])).intervalIntegrable
  refine ⟨hii.absolutelyContinuousOnInterval_intervalIntegral (by simp [htf]), ?_, ?_, ?_⟩
  · have := intervalIntegral.continuousOn_primitive_interval (a := (0:ℝ)) (b := tf)
      (μ := volume) (f := fun s => ‖F s‖) (by rwa [uIcc_of_le htf])
    rwa [uIcc_of_le htf] at this
  · filter_upwards [hii.ae_hasDerivAt_integral] with x hx hxm
    exact hx hxm 0 (by simp [htf])
  · intro t ht
    constructor
    · exact intervalIntegral.integral_nonneg ht.1 (fun _ _ => norm_nonneg _)
    · exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hii

theorem dG_pow_integral (F : ℝ → E →L[ℂ] E) (tf : ℝ) (htf : 0 ≤ tf)
    (hint : IntegrableOn F (Icc 0 tf)) (t : ℝ) (ht : t ∈ Icc 0 tf) (m : ℕ) :
    ∫ s in (0 : ℝ)..t, ‖F s‖ * dG F s ^ m = dG F t ^ (m + 1) / (m + 1) := by
  obtain ⟨hac, -, hder, -⟩ := dG_props F tf htf hint
  have hac' : AbsolutelyContinuousOnInterval (fun x => dG F x ^ (m + 1)) 0 t :=
    (ac_pow hac (m + 1)).mono (by
      rw [uIcc_of_le ht.1, uIcc_of_le htf]; exact Icc_subset_Icc le_rfl ht.2)
  have key := hac'.integral_deriv_eq_sub
  have h0 : dG F 0 = 0 := by simp [dG]
  rw [h0] at key
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, sub_zero] at key
  have hcongr : ∫ s in (0 : ℝ)..t, deriv (fun x => dG F x ^ (m + 1)) s =
      ∫ s in (0 : ℝ)..t, ((m : ℝ) + 1) * (‖F s‖ * dG F s ^ m) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hder] with x hx hxm
    have hxm' : x ∈ uIcc 0 tf := by
      rw [uIoc_of_le ht.1] at hxm
      rw [uIcc_of_le htf]; exact ⟨hxm.1.le, hxm.2.trans ht.2⟩
    have : HasDerivAt (fun x => dG F x ^ (m + 1))
        (↑(m + 1) * dG F x ^ (m + 1 - 1) * ‖F x‖) x := (hx hxm').pow (m + 1)
    rw [this.deriv]
    push_cast
    ring
  rw [hcongr, intervalIntegral.integral_const_mul] at key
  field_simp
  linarith

theorem dyson_bound (F : ℝ → E →L[ℂ] E) (tf : ℝ) (htf : 0 ≤ tf)
    (hint : IntegrableOn F (Icc 0 tf)) :
    ∀ m : ℕ, ContinuousOn (dysonTerm F m) (Icc 0 tf) ∧
      ∀ t ∈ Icc 0 tf, ‖dysonTerm F m t‖ ≤ dG F t ^ m / m.factorial := by
  obtain ⟨-, hGc, -, hGb⟩ := dG_props F tf htf hint
  intro m
  induction m with
  | zero =>
    refine ⟨continuousOn_const, fun t _ => ?_⟩
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    exact ContinuousLinearMap.norm_id_le
  | succ m ih =>
    have hi : IntegrableOn (fun s => F s * dysonTerm F m s) (Icc 0 tf) :=
      hint.mul_continuousOn ih.1 isCompact_Icc
    have heq : dysonTerm F (m + 1) = fun t => (-Complex.I) • ∫ s in (0 : ℝ)..t, F s * dysonTerm F m s := by
      funext t; rfl
    rw [heq]
    refine ⟨?_, fun t ht => ?_⟩
    · have := intervalIntegral.continuousOn_primitive_interval (a := (0:ℝ)) (b := tf)
        (μ := volume) (f := fun s => F s * dysonTerm F m s) (by rwa [uIcc_of_le htf])
      rw [uIcc_of_le htf] at this
      exact this.const_smul (-Complex.I)
    · rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
      have hsub : Icc 0 t ⊆ Icc 0 tf := Icc_subset_Icc le_rfl ht.2
      have hbi : IntervalIntegrable (fun s => ‖F s‖ * (dG F s ^ m / m.factorial)) volume 0 t := by
        apply IntegrableOn.intervalIntegrable
        rw [uIcc_of_le ht.1]
        exact ((show IntegrableOn (fun s => ‖F s‖) (Icc 0 tf) volume from hint.norm).mono_set hsub).mul_continuousOn
          (((hGc.mono hsub).pow m).div_const _) isCompact_Icc
      calc ‖∫ s in (0 : ℝ)..t, F s * dysonTerm F m s‖
          ≤ ∫ s in (0 : ℝ)..t, ‖F s‖ * (dG F s ^ m / m.factorial) := by
            apply intervalIntegral.norm_integral_le_of_norm_le ht.1 _ hbi
            refine Filter.Eventually.of_forall (fun s hs => ?_)
            exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
              (ih.2 s ⟨hs.1.le, hs.2.trans ht.2⟩) (norm_nonneg _))
        _ = (∫ s in (0 : ℝ)..t, ‖F s‖ * dG F s ^ m) / m.factorial := by
            rw [← intervalIntegral.integral_div]
            congr 1; funext s; ring
        _ = dG F t ^ (m + 1) / (m + 1).factorial := by
            rw [dG_pow_integral F tf htf hint t ht m, Nat.factorial_succ]
            push_cast
            field_simp

theorem dyson_term_le (F : ℝ → E →L[ℂ] E) (tf : ℝ) (htf : 0 ≤ tf)
    (hint : IntegrableOn F (Icc 0 tf)) (m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 tf) :
    ‖dysonTerm F m t‖ ≤ dG F tf ^ m / m.factorial := by
  obtain ⟨-, -, -, hGb⟩ := dG_props F tf htf hint
  refine ((dyson_bound F tf htf hint m).2 t ht).trans ?_
  gcongr
  · exact (hGb t ht).1
  · exact (hGb t ht).2

theorem dyson_hasSum (F : ℝ → E →L[ℂ] E) (tf : ℝ) (htf : 0 ≤ tf)
    (hint : IntegrableOn F (Icc 0 tf)) (t : ℝ) (ht : t ∈ Icc 0 tf) :
    HasSum (fun m => dysonTerm F m t) (dysonEvolution F t) :=
  (Summable.of_norm_bounded (Real.summable_pow_div_factorial (dG F tf))
    (fun m => dyson_term_le F tf htf hint m t ht)).hasSum

theorem dyson_cont (F : ℝ → E →L[ℂ] E) (tf : ℝ) (htf : 0 ≤ tf)
    (hint : IntegrableOn F (Icc 0 tf)) : ContinuousOn (dysonEvolution F) (Icc 0 tf) :=
  continuousOn_tsum (fun m => (dyson_bound F tf htf hint m).1)
    (Real.summable_pow_div_factorial (dG F tf)) (fun m x hx => dyson_term_le F tf htf hint m x hx)

theorem dyson_norm_bound (F : ℝ → E →L[ℂ] E) (tf : ℝ) (htf : 0 ≤ tf)
    (hint : IntegrableOn F (Icc 0 tf)) (t : ℝ) (ht : t ∈ Icc 0 tf) :
    ‖dysonEvolution F t‖ ≤ ∑' m : ℕ, dG F tf ^ m / m.factorial :=
  tsum_of_norm_bounded (Real.summable_pow_div_factorial (dG F tf)).hasSum
    (fun m => dyson_term_le F tf htf hint m t ht)

theorem dyson_eq (F : ℝ → E →L[ℂ] E) (tf : ℝ) (htf : 0 ≤ tf)
    (hint : IntegrableOn F (Icc 0 tf)) (t : ℝ) (ht : t ∈ Icc 0 tf) :
    dysonEvolution F t = 1 + (-Complex.I) • ∫ s in (0 : ℝ)..t, F s * dysonEvolution F s := by
  have hmem : ∀ s ∈ uIoc 0 t, s ∈ Icc 0 tf := by
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    exact ⟨hs.1.le, hs.2.trans ht.2⟩
  have hS : HasSum (fun m => ∫ s in (0 : ℝ)..t, F s * dysonTerm F m s)
      (∫ s in (0 : ℝ)..t, F s * dysonEvolution F s) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m s => ‖F s‖ * (dG F tf ^ m / m.factorial))
    · intro m
      exact ((hint.mul_continuousOn (dyson_bound F tf htf hint m).1 isCompact_Icc).mono_set
        hmem).aestronglyMeasurable
    · intro m
      exact Filter.Eventually.of_forall (fun s hs => (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (dyson_term_le F tf htf hint m s (hmem s hs)) (norm_nonneg _)))
    · exact Filter.Eventually.of_forall
        (fun s _ => (Real.summable_pow_div_factorial _).mul_left _)
    · have : (fun s => ∑' m : ℕ, ‖F s‖ * (dG F tf ^ m / m.factorial)) =
          fun s => ‖F s‖ * ∑' m : ℕ, dG F tf ^ m / m.factorial := by
        funext s; exact tsum_mul_left
      rw [this]
      apply IntegrableOn.intervalIntegrable
      rw [uIcc_of_le ht.1]
      exact ((show IntegrableOn (fun s => ‖F s‖) (Icc 0 tf) volume from hint.norm).mono_set
        (Icc_subset_Icc le_rfl ht.2)).mul_const _
    · exact Filter.Eventually.of_forall
        (fun s hs => (dyson_hasSum F tf htf hint s (hmem s hs)).mul_left (F s))
  have h2 := hS.const_smul (-Complex.I)
  have h3 : HasSum (fun m => dysonTerm F m t)
      (1 + (-Complex.I) • ∫ s in (0 : ℝ)..t, F s * dysonEvolution F s) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [dysonTerm] using h2
  exact (dyson_hasSum F tf htf hint t ht).unique h3

theorem dyson_isometry (F : ℝ → E →L[ℂ] E) (tf : ℝ) (htf : 0 ≤ tf)
    (hint : IntegrableOn F (Icc 0 tf))
    (hsa : ∀ᵐ t ∂volume.restrict (Icc 0 tf), IsSelfAdjoint (F t))
    (t : ℝ) (ht : t ∈ Icc 0 tf) (v : E) : ‖dysonEvolution F t v‖ = ‖v‖ := by
  set U := dysonEvolution F with hU
  set M0 : ℝ := ∑' m : ℕ, dG F tf ^ m / m.factorial
  have hM0 : 0 ≤ M0 := tsum_nonneg (fun m => by
    have := (dG_props F tf htf hint).2.2.2 tf ⟨htf, le_rfl⟩
    have := this.1
    positivity)
  have hH : IntegrableOn (fun s => F s * U s) (Icc 0 tf) :=
    hint.mul_continuousOn (dyson_cont F tf htf hint) isCompact_Icc
  set h : ℝ → E := fun s => F s (U s v) with hh
  have hhi : IntegrableOn h (Icc 0 tf) := hH.apply_continuousLinearMap v
  have hsubI : ∀ x ∈ Icc (0 : ℝ) tf, uIcc 0 x ⊆ Icc 0 tf := fun x hx => by
    rw [uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2
  have hiH : ∀ x ∈ Icc (0 : ℝ) tf, IntervalIntegrable (fun s => F s * U s) volume 0 x :=
    fun x hx => (hH.mono_set (hsubI x hx)).intervalIntegrable
  have hih : ∀ x ∈ Icc (0 : ℝ) tf, IntervalIntegrable h volume 0 x :=
    fun x hx => (hhi.mono_set (hsubI x hx)).intervalIntegrable
  have hihn : ∀ x ∈ Icc (0 : ℝ) tf, IntervalIntegrable (fun s => ‖h s‖) volume 0 x :=
    fun x hx => (hih x hx).norm
  set w : ℝ → E := fun x => v + (-Complex.I) • ∫ s in (0 : ℝ)..x, h s with hw_def
  have hw : ∀ x ∈ Icc (0 : ℝ) tf, U x v = w x := by
    intro x hx
    rw [hU, dyson_eq F tf htf hint x hx, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.intervalIntegral_apply (hiH x hx),
      ContinuousLinearMap.one_apply]
    rfl
  have hwb : ∀ x ∈ Icc (0 : ℝ) tf, ‖w x‖ ≤ M0 * ‖v‖ := by
    intro x hx
    rw [← hw x hx]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (dyson_norm_bound F tf htf hint x hx) (norm_nonneg _))
  set Gh : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, ‖h s‖ with hGh_def
  have hGh : AbsolutelyContinuousOnInterval Gh 0 tf :=
    (hihn tf ⟨htf, le_rfl⟩).absolutelyContinuousOnInterval_intervalIntegral (by simp [htf])
  have hdw : ∀ x ∈ Icc (0 : ℝ) tf, ∀ y ∈ Icc (0 : ℝ) tf, ‖w x - w y‖ ≤ dist (Gh x) (Gh y) := by
    intro x hx y hy
    have e1 : w x - w y = (-Complex.I) • ∫ s in y..x, h s := by
      rw [← intervalIntegral.integral_interval_sub_left (hih x hx) (hih y hy)]
      simp only [hw_def, smul_sub]
      abel
    have e2 : Gh x - Gh y = ∫ s in y..x, ‖h s‖ := by
      simp only [hGh_def]
      exact intervalIntegral.integral_interval_sub_left (hihn x hx) (hihn y hy)
    rw [e1, norm_smul, norm_neg, Complex.norm_I, one_mul, Real.dist_eq, e2]
    exact intervalIntegral.norm_integral_le_abs_integral_norm
  set ψ : ℝ → ℂ := fun x => inner ℂ (w x) (w x) with hψ_def
  have hψac : AbsolutelyContinuousOnInterval ψ 0 tf := by
    refine ac_of_dist_le (C := 2 * (M0 * ‖v‖)) (by positivity) hGh (fun x hx y hy => ?_)
    rw [uIcc_of_le htf] at hx hy
    rw [dist_eq_norm]
    have e : ψ x - ψ y = inner ℂ (w x - w y) (w x) + inner ℂ (w y) (w x - w y) := by
      simp only [hψ_def, inner_sub_left, inner_sub_right]
      ring
    rw [e]
    have hx1 := hwb x hx
    have hy1 := hwb y hy
    have hd := hdw x hx y hy
    calc ‖inner ℂ (w x - w y) (w x) + inner ℂ (w y) (w x - w y)‖
        ≤ ‖w x - w y‖ * ‖w x‖ + ‖w y‖ * ‖w x - w y‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
      _ ≤ ‖w x - w y‖ * (M0 * ‖v‖) + (M0 * ‖v‖) * ‖w x - w y‖ := by
          gcongr
      _ = 2 * (M0 * ‖v‖) * ‖w x - w y‖ := by ring
      _ ≤ 2 * (M0 * ‖v‖) * dist (Gh x) (Gh y) := by gcongr
  have hder : ∀ᵐ x, x ∈ uIcc 0 tf → HasDerivAt ψ 0 x := by
    filter_upwards [(hih tf ⟨htf, le_rfl⟩).ae_hasDerivAt_integral,
      (ae_restrict_iff' measurableSet_Icc).mp hsa] with x hx hsx hxm
    have hxI : x ∈ Icc 0 tf := by rwa [uIcc_of_le htf] at hxm
    have hd : HasDerivAt w ((-Complex.I) • h x) x :=
      ((hx hxm 0 (by simp [htf])).const_smul (-Complex.I)).const_add v
    have := hd.inner ℂ hd
    have hsym : inner ℂ (F x (U x v)) (U x v) = inner ℂ (U x v) (F x (U x v)) := by
      conv_lhs => rw [← (hsx hxI).adjoint_eq]
      exact ContinuousLinearMap.adjoint_inner_left _ _ _
    have e : inner ℂ (w x) ((-Complex.I) • h x) + inner ℂ ((-Complex.I) • h x) (w x) = 0 := by
      rw [← hw x hxI]
      simp only [hh, inner_smul_right, inner_smul_left, hsym]
      simp
    rw [e] at this
    exact this
  obtain ⟨C, hC⟩ := hψac.const_of_ae_hasDerivAt_zero hder
  have h0 : ψ 0 = inner ℂ v v := by simp [hψ_def, hw_def]
  have ht' : ψ t = inner ℂ v v := by
    rw [hC t (by rw [uIcc_of_le htf]; exact ht), ← h0, hC 0 (by simp [htf])]
  have hfin : inner ℂ (U t v) (U t v) = inner ℂ v v := by rw [hw t ht]; exact ht'
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hfin
  have hr : ‖U t v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast hfin
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hr

/-- Unitarity of the Dyson series gives contractivity. -/
theorem dyson_norm_le_one (F : ℝ → E →L[ℂ] E) (tf : ℝ)
    (hint : IntegrableOn F (Icc 0 tf))
    (hsa : ∀ᵐ t ∂volume.restrict (Icc 0 tf), IsSelfAdjoint (F t))
    (t : ℝ) (ht : t ∈ Icc 0 tf) : ‖dysonEvolution F t‖ ≤ 1 := by
  have htf : 0 ≤ tf := ht.1.trans ht.2
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [dyson_isometry F tf htf hint hsa t ht v, one_mul]

end Dyson

section Ops

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- `g` is a formal adjoint of `f`. -/
def AdjPair {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (f g : X →L[ℂ] X) : Prop :=
  ∀ x y, inner ℂ (f x) y = inner ℂ x (g y)

theorem completion_norm_le (f : V →L[ℂ] W) : ‖f.completion‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le (continuous_norm.comp f.completion.continuous)
      (continuous_const.mul continuous_norm)
  | ih a =>
    rw [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    exact f.le_opNorm a

theorem completion_add (f g : V →L[ℂ] W) : (f + g).completion = f.completion + g.completion := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (f + g).completion.continuous
      (f.completion + g.completion).continuous
  | ih a =>
    simp [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.coe_add]

theorem completion_smul (c : ℂ) (f : V →L[ℂ] W) : (c • f).completion = c • f.completion := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (c • f).completion.continuous (c • f.completion).continuous
  | ih a =>
    simp [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.coe_smul]

theorem AdjPair.completion {f g : V →L[ℂ] V} (h : AdjPair f g) :
    AdjPair f.completion g.completion := by
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq
      (continuous_inner.comp ((f.completion.continuous.comp continuous_fst).prodMk continuous_snd))
      (continuous_inner.comp (continuous_fst.prodMk (g.completion.continuous.comp continuous_snd)))
  | ih a b =>
    simp only [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.inner_coe]
    exact h a b

theorem AdjPair.mapL {a a' : V →L[ℂ] V} {b b' : W →L[ℂ] W} (ha : AdjPair a a') (hb : AdjPair b b') :
    AdjPair (TensorProduct.mapL a b) (TensorProduct.mapL a' b') := by
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | tmul v w =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | tmul v' w' =>
      simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul, ha v v', hb w w']

theorem AdjPair.add {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    {f g f' g' : X →L[ℂ] X} (h1 : AdjPair f g) (h2 : AdjPair f' g') : AdjPair (f + f') (g + g') :=
  fun x y => by
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right, h1 x y, h2 x y]

theorem AdjPair.smul_real {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    {f g : X →L[ℂ] X} (r : ℝ) (h : AdjPair f g) : AdjPair ((r : ℂ) • f) ((r : ℂ) • g) :=
  fun x y => by
    simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, h x y]

theorem AdjPair.sum {X ι : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (s : Finset ι) (f : ι → X →L[ℂ] X) (h : ∀ i ∈ s, AdjPair (f i) (f i)) :
    AdjPair (∑ i ∈ s, f i) (∑ i ∈ s, f i) := fun x y => by
  simp only [ContinuousLinearMap.sum_apply, sum_inner, inner_sum]
  exact Finset.sum_congr rfl (fun i hi => h i hi x y)

theorem adjPair_one {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] :
    AdjPair (1 : X →L[ℂ] X) 1 := fun _ _ => rfl

theorem adjPair_id {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] :
    AdjPair (ContinuousLinearMap.id ℂ X) (ContinuousLinearMap.id ℂ X) := fun _ _ => rfl

theorem adjPair_of_selfAdjoint {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] {f : X →L[ℂ] X} (h : IsSelfAdjoint f) : AdjPair f f := by
  intro x y
  conv_lhs => rw [← h.adjoint_eq]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

theorem selfAdjoint_of_adjPair {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] {f : X →L[ℂ] X} (h : AdjPair f f) : IsSelfAdjoint f := by
  have : f = ContinuousLinearMap.adjoint f := (ContinuousLinearMap.eq_adjoint_iff f f).mpr h
  exact this.symm

theorem AdjPair.algebraicLift {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {a a' : E →L[ℂ] E} (h : AdjPair a a') :
    ∀ (m : ℕ) (j : Fin m), AdjPair (algebraicLift m j a) (algebraicLift m j a')
  | 0, j => j.elim0
  | m + 1, j => by
    cases j using Fin.cases with
    | zero =>
      simp only [HamLocality237.Testing.algebraicLift, Fin.cases_zero]
      exact h.mapL adjPair_id
    | succ i =>
      simp only [HamLocality237.Testing.algebraicLift, Fin.cases_succ]
      exact adjPair_id.mapL (AdjPair.algebraicLift h m i)

/-- `a ↦ (a ⊗ b)` on completions, as a bounded linear map. -/
noncomputable def liftL (b : W →L[ℂ] W) :
    (V →L[ℂ] V) →L[ℂ] (UniformSpace.Completion (V ⊗[ℂ] W) →L[ℂ] UniformSpace.Completion (V ⊗[ℂ] W)) :=
  LinearMap.mkContinuous
    { toFun := fun a => (TensorProduct.mapL a b).completion
      map_add' := fun a a' => by
        rw [TensorProduct.mapL_add_left, completion_add]
      map_smul' := fun c a => by
        rw [TensorProduct.mapL_smul_left, completion_smul]
        rfl }
    ‖b‖ (fun a => by
      refine (completion_norm_le _).trans ?_
      refine (TensorProduct.norm_mapL_le _ _).trans ?_
      rw [mul_comm])

theorem liftL_apply (b : W →L[ℂ] W) (a : V →L[ℂ] V) :
    liftL b a = (TensorProduct.mapL a b).completion := rfl

theorem liftL_norm_le (b : W →L[ℂ] W) (a : V →L[ℂ] V) :
    ‖(TensorProduct.mapL a b).completion‖ ≤ ‖b‖ * ‖a‖ :=
  (completion_norm_le _).trans ((TensorProduct.norm_mapL_le _ _).trans (le_of_eq (mul_comm _ _)))

theorem integrable_liftL (b : W →L[ℂ] W) {μ : Measure ℝ} {f : ℝ → V →L[ℂ] V}
    (hf : Integrable f μ) : Integrable (fun s => (TensorProduct.mapL (f s) b).completion) μ :=
  Integrable.mono' (hf.norm.const_mul ‖b‖)
    ((liftL b).continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun s => liftL_norm_le b (f s)))

end Ops


theorem jointLift_eq {n : ℕ} (A : ContinuousAlgorithm n) (a : A.Space →L[ℂ] A.Space)
    (b : InputRegister n →L[ℂ] InputRegister n) : jointLift A a b = liftL b a := rfl

theorem jointLift_selfAdjoint {n : ℕ} (A : ContinuousAlgorithm n) {a : A.Space →L[ℂ] A.Space}
    {b : InputRegister n →L[ℂ] InputRegister n} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    IsSelfAdjoint (jointLift A a b) :=
  selfAdjoint_of_adjPair ((adjPair_of_selfAdjoint ha).mapL (adjPair_of_selfAdjoint hb)).completion

theorem hilbertLift_adjPair {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {a : E →L[ℂ] E} (ha : AdjPair a a) (m : ℕ) (j : Fin m) :
    AdjPair (hilbertLift j a) (hilbertLift j a) := by
  have h1 : AdjPair (algebraicLift m j a) (algebraicLift m j a) := AdjPair.algebraicLift ha m j
  exact h1.completion

theorem hilbertLift_selfAdjoint {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {a : E →L[ℂ] E} (ha : IsSelfAdjoint a) (m : ℕ) (j : Fin m) :
    IsSelfAdjoint (hilbertLift j a) :=
  selfAdjoint_of_adjPair (hilbertLift_adjPair (adjPair_of_selfAdjoint ha) m j)

theorem inputLift_selfAdjoint {n : ℕ} (x : Qubits n) {a : SingleRegister →L[ℂ] SingleRegister}
    (ha : IsSelfAdjoint a) : IsSelfAdjoint (inputLift x a) := by
  unfold inputLift InputRegister
  generalize siteEnumeration n x = j
  generalize Fintype.card (Qubits n) = m at j ⊢
  exact hilbertLift_selfAdjoint ha m j

theorem mult_symm (r s : BandSpace) :
    inner ℂ (multiplicationOperator r) s = inner ℂ r (multiplicationOperator s) := by
  have hr : multiplicationOperator r = multiplyCoordinate r := rfl
  have hs : multiplicationOperator s = multiplyCoordinate s := rfl
  rw [hr, hs, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplyCoordinate_ae r, multiplyCoordinate_ae s] with w h1 h2
  rw [h1, h2]
  have hc : conj (coordinate w) = coordinate w := by simp [coordinate]
  simp only [RCLike.inner_apply, map_mul, hc]
  ring

theorem hard_key (ε : ℝ) (z : SingleRegister) :
    (ε • (WithLp.fstL 2 ℂ ℂ BandSpace).smulRight bumpVector) z =
      ((ε : ℂ) * WithLp.fst z) • bumpVector := by
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, ← smul_smul,
    Complex.coe_smul]
  rfl

theorem hard_symm (ε : ℝ) (x y : SingleRegister) :
    inner ℂ (hardOperator ε x) y = inner ℂ x (hardOperator ε y) := by
  have key : ∀ z : SingleRegister, (((ε : ℂ) • (scalarPart.smulRight bumpVector)) z) =
      ((ε : ℂ) * scalarPart z) • bumpVector := by
    intro z
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_smul]
  simp [-Complex.coe_smul, hardOperator, pairRegister, WithLp.prod_inner_apply, key, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, mult_symm, Complex.conj_ofReal]
  simp [scalarPart, bandPart]
  ring

theorem projection_norm_le {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    {P : X →L[ℂ] X} (hP : IsProjection P) : ‖P‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  have hs : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y) := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_left, hP.1.adjoint_eq]
  have hpp : P (P v) = P v := congrArg (fun T => T v) hP.2
  have h1 : inner ℂ (P v) (P v) = inner ℂ v (P v) := by
    rw [hs, hpp]
  have h2 : ‖P v‖ ^ 2 ≤ ‖v‖ * ‖P v‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) v (P v)
    rw [← h1, inner_self_eq_norm_sq_to_K] at this
    simpa using this
  rw [one_mul]
  nlinarith [norm_nonneg (P v), norm_nonneg v]

theorem hard_selfAdjoint (ε : ℝ) : IsSelfAdjoint (hardOperator ε) :=
  selfAdjoint_of_adjPair (hard_symm ε)

theorem jointHamiltonian_sa {n : ℕ} (A : ContinuousAlgorithm n) (ε : ℝ) :
    ∀ᵐ t ∂volume.restrict (Set.Icc 0 A.finalTime), IsSelfAdjoint (jointHamiltonian A ε t) := by
  filter_upwards [A.driver_selfAdjoint, A.query_projection] with t hd hq
  have hH := hard_selfAdjoint ε
  have hI : ∀ x : Qubits n, IsSelfAdjoint (inputLift x (hardOperator ε)) :=
    fun x => inputLift_selfAdjoint x hH
  have hJ : ∀ x : Qubits n, AdjPair (jointLift A (A.query x t) (inputLift x (hardOperator ε)))
      (jointLift A (A.query x t) (inputLift x (hardOperator ε))) :=
    fun x => ((adjPair_of_selfAdjoint (hq x).1).mapL (adjPair_of_selfAdjoint (hI x))).completion
  have hD : AdjPair (jointLift A (A.driver t) 1) (jointLift A (A.driver t) 1) :=
    ((adjPair_of_selfAdjoint hd).mapL adjPair_one).completion
  exact selfAdjoint_of_adjPair
    (hD.add ((AdjPair.sum _ _ (fun x _ => hJ x)).smul_real (A.intensity t)))

noncomputable instance jointOpNormedAddCommGroup {n : ℕ} (A : ContinuousAlgorithm n) :
    NormedAddCommGroup (JointRegister A →L[ℂ] JointRegister A) := inferInstance

theorem jointDriver_props {n : ℕ} (A : ContinuousAlgorithm n) :
    IntegrableOn (fun s => jointLift A (A.driver s) 1) (Set.Icc 0 A.finalTime) ∧
    ∀ᵐ t ∂volume.restrict (Set.Icc 0 A.finalTime), IsSelfAdjoint (jointLift A (A.driver t) 1) := by
  refine ⟨?_, ?_⟩
  · exact integrable_liftL 1 A.driver_integrable
  · filter_upwards [A.driver_selfAdjoint] with t ht
    exact jointLift_selfAdjoint A ht (IsSelfAdjoint.one _)

theorem integrable_sum_smul {V W ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Fintype ι] {μ : Measure ℝ}
    (b : ι → W →L[ℂ] W) {φ : ℝ → ℝ} (hφ : Integrable φ μ) (q : ι → ℝ → V →L[ℂ] V)
    (hq : ∀ i, AEStronglyMeasurable (q i) μ) (hb : ∀ᵐ t ∂μ, ∀ i, ‖q i t‖ ≤ 1) :
    Integrable (fun t => ((φ t : ℂ)) • ∑ i, (TensorProduct.mapL (q i t) (b i)).completion) μ := by
  have hmeas : AEStronglyMeasurable (fun t => ∑ i, (TensorProduct.mapL (q i t) (b i)).completion) μ := by
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact (liftL (b i)).continuous.comp_aestronglyMeasurable (hq i)
  have hbound : ∀ᵐ t ∂μ, ‖∑ i, (TensorProduct.mapL (q i t) (b i)).completion‖ ≤ ∑ i, ‖b i‖ := by
    filter_upwards [hb] with t ht
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (liftL_norm_le _ _).trans ?_
    exact mul_le_of_le_one_right (norm_nonneg _) (ht i)
  exact Integrable.smul_of_top_left (hφ.ofReal (𝕜 := ℂ)) (memLp_top_of_bound hmeas _ hbound)

theorem jointHamiltonian_props {n : ℕ} (A : ContinuousAlgorithm n) (ε : ℝ) :
    IntegrableOn (jointHamiltonian A ε) (Set.Icc 0 A.finalTime) ∧
    ∀ᵐ t ∂volume.restrict (Set.Icc 0 A.finalTime), IsSelfAdjoint (jointHamiltonian A ε t) := by
  refine ⟨?_, ?_⟩
  · have h1 : IntegrableOn (fun t => jointLift A (A.driver t) 1) (Set.Icc 0 A.finalTime) :=
      integrable_liftL 1 A.driver_integrable
    have hb : ∀ᵐ t ∂volume.restrict (Set.Icc 0 A.finalTime), ∀ x, ‖A.query x t‖ ≤ 1 := by
      filter_upwards [A.query_projection] with t ht x
      exact projection_norm_le (ht x)
    have h2 := integrable_sum_smul (fun x => inputLift x (hardOperator ε)) A.intensity_integrable
      A.query A.query_measurable hb
    exact h1.add h2
  · exact jointHamiltonian_sa A ε


section Corr
variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem completion_mul (f g : V →L[ℂ] V) : (f * g).completion = f.completion * g.completion := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (f * g).completion.continuous (f.completion * g.completion).continuous
  | ih a =>
    simp [ContinuousLinearMap.completion_apply_coe]

theorem completion_zero_apply (x : UniformSpace.Completion V) :
    (0 : V →L[ℂ] W).completion x = 0 := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (0 : V →L[ℂ] W).completion.continuous continuous_const
  | ih a => simp [ContinuousLinearMap.completion_apply_coe]

theorem completion_mapL_sum_apply {ι : Type} (s : Finset ι) (a : V →L[ℂ] V) (b : ι → W →L[ℂ] W)
    (w : UniformSpace.Completion (V ⊗[ℂ] W)) :
    (TensorProduct.mapL a (∑ i ∈ s, b i)).completion w =
      ∑ i ∈ s, (TensorProduct.mapL a (b i)).completion w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, TensorProduct.mapL_zero_right]
    exact completion_zero_apply w
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, TensorProduct.mapL_add_right, completion_add,
      ContinuousLinearMap.add_apply, ih]

theorem algebraicLift_mul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b : E →L[ℂ] E) :
    ∀ (m : ℕ) (j : Fin m), algebraicLift m j (a * b) = algebraicLift m j a * algebraicLift m j b
  | 0, j => j.elim0
  | m + 1, j => by
    cases j using Fin.cases with
    | zero =>
      simp only [HamLocality237.Testing.algebraicLift, Fin.cases_zero]
      rw [← TensorProduct.mapL_mul]
      rfl
    | succ i =>
      simp only [HamLocality237.Testing.algebraicLift, Fin.cases_succ]
      rw [algebraicLift_mul a b m i, ← TensorProduct.mapL_mul]
      rfl

theorem pos_of_adj_sq {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (T : X →L[ℂ] X)
    (hT : AdjPair T T) (w : X) : 0 ≤ (inner ℂ w ((T * T) w)).re := by
  have : inner ℂ w ((T * T) w) = inner ℂ (T w) (T w) := (hT w (T w)).symm
  rw [this]
  simpa only [RCLike.re_to_complex] using inner_self_nonneg (𝕜 := ℂ) (x := T w)

theorem term_nonneg {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (d : E →L[ℂ] E)
    (hd : AdjPair d d) (m : ℕ) (j : Fin m)
    (w : UniformSpace.Completion (V ⊗[ℂ] HilbertPower E m)) :
    0 ≤ (inner ℂ w ((TensorProduct.mapL (1 : V →L[ℂ] V) (hilbertLift j (d * d))).completion w)).re := by
  have h1 : hilbertLift j (d * d) = hilbertLift j d * hilbertLift j d := by
    simp only [hilbertLift]
    rw [algebraicLift_mul, completion_mul]
  have hL : AdjPair (hilbertLift j d) (hilbertLift j d) := hilbertLift_adjPair hd m j
  have h2 : TensorProduct.mapL (1 : V →L[ℂ] V) (hilbertLift j d * hilbertLift j d) =
      TensorProduct.mapL 1 (hilbertLift j d) * TensorProduct.mapL 1 (hilbertLift j d) := by
    rw [← TensorProduct.mapL_mul, one_mul]
  rw [h1, h2, completion_mul]
  exact pos_of_adj_sq _ ((adjPair_one.mapL hL).completion) w

end Corr

theorem penalty_symm (x y : HalfLineSpace) :
    inner ℂ (penaltyOperator x) y = inner ℂ x (penaltyOperator y) := by
  simp only [penaltyOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

theorem penalty_inner (z : HalfLineSpace) :
    (inner ℂ z (penaltyOperator z)).re = etaSquared * ‖z‖ ^ 2 - ‖responseOperator z‖ ^ 2 := by
  simp only [penaltyOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply, inner_sub_right,
    inner_smul_right, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem penaltyInverse_props :
    AdjPair penaltyInverse penaltyInverse ∧ ∀ y, 0 ≤ (inner ℂ (penaltyInverse y) y).re := by
  unfold penaltyInverse
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h.choose_spec
    set B := h.choose
    have hPB : ∀ y, penaltyOperator (B y) = y := fun y => congrArg (fun T => T y) h2
    refine ⟨fun x y => ?_, fun y => ?_⟩
    · conv_lhs => rw [← hPB y]
      rw [← penalty_symm, hPB x]
    · rw [show inner ℂ (B y) y = inner ℂ (B y) (penaltyOperator (B y)) by rw [hPB]]
      rw [penalty_inner]
      have hR := responseOperator.le_opNorm (B y)
      have hn := norm_nonneg (responseOperator (B y))
      have : ‖responseOperator (B y)‖ ^ 2 ≤ ‖responseOperator‖ ^ 2 * ‖B y‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hn hR 2
      unfold etaSquared
      nlinarith [sq_nonneg ‖B y‖]
  · exact ⟨fun x y => by simp, fun y => by simp⟩

theorem bandCorrection_inner (r s : BandSpace) :
    inner ℂ (bandCorrection r) s = inner ℂ (observationOperator r) (observationOperator s) +
      inner ℂ (penaltyInverse (responseOperator.adjoint (observationOperator r)))
        (responseOperator.adjoint (observationOperator s)) := by
  simp only [bandCorrection, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

theorem bandCorrection_props :
    AdjPair bandCorrection bandCorrection ∧ ∀ r, 0 ≤ (inner ℂ (bandCorrection r) r).re := by
  obtain ⟨hB1, hB2⟩ := penaltyInverse_props
  refine ⟨fun r s => ?_, fun r => ?_⟩
  · rw [bandCorrection_inner, ← inner_conj_symm r, bandCorrection_inner, map_add,
      inner_conj_symm, hB1, inner_conj_symm]
  · rw [bandCorrection_inner, Complex.add_re]
    have := hB2 (responseOperator.adjoint (observationOperator r))
    have h2 : (0 : ℝ) ≤ (inner ℂ (observationOperator r) (observationOperator r)).re := by
      simpa only [RCLike.re_to_complex] using
        inner_self_nonneg (𝕜 := ℂ) (x := observationOperator r)
    linarith

theorem singleCorrection_inner (x y : SingleRegister) :
    inner ℂ (singleCorrection x) y = inner ℂ (bandCorrection (bandPart x)) (bandPart y) := by
  simp [singleCorrection, pairRegister, WithLp.prod_inner_apply, bandPart]

theorem exists_sqrt_adj {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (a : H →L[ℂ] H) (h : a.IsPositive) :
    ∃ d : H →L[ℂ] H, IsSelfAdjoint d ∧ d * d = a := by
  have h0 : 0 ≤ a := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr h
  exact ⟨CFC.sqrt a, IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _), CFC.sqrt_mul_sqrt_self _ h0⟩

theorem singleCorrection_sqrt :
    ∃ d : SingleRegister →L[ℂ] SingleRegister, AdjPair d d ∧ d * d = singleCorrection := by
  obtain ⟨hC1, hC2⟩ := bandCorrection_props
  have hpos : singleCorrection.IsPositive := by
    rw [ContinuousLinearMap.isPositive_def]
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · change inner ℂ (singleCorrection x) y = inner ℂ x (singleCorrection y)
      rw [singleCorrection_inner, hC1, ← inner_conj_symm x, singleCorrection_inner,
        inner_conj_symm]
    · simp only [ContinuousLinearMap.reApplyInnerSelf, singleCorrection_inner, RCLike.re_to_complex]
      exact hC2 _
  obtain ⟨d, hd, hdd⟩ := exists_sqrt_adj singleCorrection hpos
  exact ⟨d, adjPair_of_selfAdjoint hd, hdd⟩

theorem correction_nonneg {n : ℕ} (A : ContinuousAlgorithm n) (w : JointRegister A) :
    0 ≤ (inner ℂ w (jointLift A 1 (fullCorrection n) w)).re := by
  obtain ⟨d, hd, hdd⟩ := singleCorrection_sqrt
  unfold jointLift fullCorrection
  rw [completion_mapL_sum_apply, inner_sum, Complex.re_sum]
  refine Finset.sum_nonneg (fun x _ => ?_)
  unfold inputLift
  rw [← hdd]
  exact term_nonneg d hd _ _ w

theorem bottom_inner : inner ℂ bottomVector bottomVector = 1 := by
  simp [bottomVector]

theorem inputVacuum_norm (n : ℕ) : ‖inputVacuum n‖ = 1 := by
  have h := hilbertProduct_inner (fun (_ : Fin (Fintype.card (Qubits n))) => bottomVector)
    (fun _ => bottomVector)
  rw [bottom_inner, Finset.prod_const_one, inner_self_eq_norm_sq_to_K] at h
  have h3 : ‖(hilbertProduct (fun (_ : Fin (Fintype.card (Qubits n))) => bottomVector))‖ ^ 2 = 1 := by
    have := congrArg Complex.re h
    simpa [← Complex.ofReal_pow] using this
  have := norm_nonneg (inputVacuum n)
  unfold inputVacuum
  nlinarith [norm_nonneg (hilbertProduct (fun (_ : Fin (Fintype.card (Qubits n))) => bottomVector))]

theorem jointProduct_norm {n : ℕ} (A : ContinuousAlgorithm n) (v : A.Space) (r : InputRegister n) :
    ‖jointProduct A v r‖ = ‖v‖ * ‖r‖ := by
  rw [jointProduct, UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul]

theorem norm_sub_sq_aux {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (F Z : E) :
    ‖F - Z‖ ^ 2 = ‖F‖ ^ 2 + ‖Z‖ ^ 2 - 2 * (inner ℂ Z F).re := by
  rw [norm_sub_sq (𝕜 := ℂ), ← inner_conj_symm Z F]
  rw [Complex.conj_re]
  simp only [RCLike.re_to_complex]
  ring

theorem final_aux {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (F Z : E)
    (c : ℝ) (hF : ‖F‖ ≤ 1) (hZ : ‖Z‖ ≤ 1) (hc : 0 ≤ c) :
    ‖F - Z‖ ^ 2 / 2 ≤ 1 - (inner ℂ Z F).re + c / 4 := by
  rw [norm_sub_sq_aux]
  nlinarith [norm_nonneg F, norm_nonneg Z]

theorem lemma_3_6 (n : ℕ) (A : ContinuousAlgorithm n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ‖purifiedFar A ε A.finalTime - purifiedZero A A.finalTime‖ ^ 2 / 2 ≤
      progress A ε A.finalTime := by
  have hT : A.finalTime ∈ Set.Icc 0 A.finalTime := ⟨A.finalTime_nonneg, le_rfl⟩
  obtain ⟨h1, h2⟩ := jointHamiltonian_props A ε
  obtain ⟨h3, h4⟩ := jointDriver_props A
  have hF := dyson_norm_le_one _ _ h1 h2 _ hT
  have hZ := dyson_norm_le_one _ _ h3 h4 _ hT
  have hv : ‖jointProduct A A.initial (inputVacuum n)‖ ≤ 1 := by
    rw [jointProduct_norm, inputVacuum_norm, A.initial_unit, one_mul]
  have hF' : ‖purifiedFar A ε A.finalTime‖ ≤ 1 :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by nlinarith [norm_nonneg (jointProduct A A.initial (inputVacuum n)), norm_nonneg (dysonEvolution (jointHamiltonian A ε) A.finalTime)])
  have hZ' : ‖purifiedZero A A.finalTime‖ ≤ 1 :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by nlinarith [norm_nonneg (jointProduct A A.initial (inputVacuum n)), norm_nonneg (dysonEvolution (fun s => jointLift A (A.driver s) 1) A.finalTime)])
  exact final_aux _ _ _ hF' hZ' (correction_nonneg A _)

end HamLocality237.Testing

open HamLocality237.Testing in
theorem solution (n : ℕ) (A : ContinuousAlgorithm n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ‖purifiedFar A ε A.finalTime - purifiedZero A A.finalTime‖ ^ 2 / 2 ≤
      progress A ε A.finalTime :=
  HamLocality237.Testing.lemma_3_6 n A ε hε hε'
