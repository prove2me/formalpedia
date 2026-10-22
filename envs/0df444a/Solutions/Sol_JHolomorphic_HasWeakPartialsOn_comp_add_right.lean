-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.comp_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T15:58:55.590453+00:00
-- url     : https://prove2.me/submissions/8257cbad-6dcd-4f24-a949-06c0a6930dc5

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact
import Theorems.Thm_JHolomorphic_fderiv_apply_isTestFunction
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_clm_apply
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Integral



namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

/-- Weak partial derivatives are compatible with translation. -/
theorem HasWeakPartialsOn.comp_add_right_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {f fs ft : ℂ → E} (h : HasWeakPartialsOn U f fs ft) (a : ℂ) :
    HasWeakPartialsOn ((· + a) ⁻¹' U) (fun z => f (z + a)) (fun z => fs (z + a))
      (fun z => ft (z + a)) := by
  intro φ hφ hc hU
  set ψ : ℂ → ℝ := fun z => φ (z - a) with hψ
  have hψs : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_id.sub contDiff_const)
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.subRight a)
  have hψU : tsupport ψ ⊆ U := by
    intro z hz
    have : z - a ∈ tsupport φ := by
      have := tsupport_comp_subset_preimage φ (f := fun z => z - a) (continuous_sub_right a) hz
      exact this
    simpa using hU this
  obtain ⟨h1, h2⟩ := h ψ hψs hψc hψU
  have hd : ∀ z, fderiv ℝ ψ z = fderiv ℝ φ (z - a) := fun z => fderiv_comp_sub (f := φ) a
  constructor
  · calc ∫ z, fderiv ℝ φ z 1 • f (z + a)
        = ∫ z, fderiv ℝ φ (z - a) 1 • f (z - a + a) :=
          (integral_sub_right_eq_self (fun z => fderiv ℝ φ z 1 • f (z + a)) a).symm
      _ = ∫ z, fderiv ℝ ψ z 1 • f z := by simp [hd]
      _ = -∫ z, ψ z • fs z := h1
      _ = -∫ z, φ z • fs (z + a) := by
          rw [← integral_add_right_eq_self (fun z => ψ z • fs z) a]; simp [hψ]
  · calc ∫ z, fderiv ℝ φ z Complex.I • f (z + a)
        = ∫ z, fderiv ℝ φ (z - a) Complex.I • f (z - a + a) :=
          (integral_sub_right_eq_self (fun z => fderiv ℝ φ z Complex.I • f (z + a)) a).symm
      _ = ∫ z, fderiv ℝ ψ z Complex.I • f z := by simp [hd]
      _ = -∫ z, ψ z • ft z := h2
      _ = -∫ z, φ z • ft (z + a) := by
          rw [← integral_add_right_eq_self (fun z => ψ z • ft z) a]; simp [hψ]

/-- Weak partial derivatives of `c • (f - g)`. -/
theorem HasWeakPartialsOn.smul_sub_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} {f fs ft g gs gt : ℂ → E} (hf : HasWeakPartialsOn U f fs ft)
    (hg : HasWeakPartialsOn U g gs gt)
    (hfi : ∀ K ⊆ U, IsCompact K → IntegrableOn f K ∧ IntegrableOn fs K ∧ IntegrableOn ft K)
    (hgi : ∀ K ⊆ U, IsCompact K → IntegrableOn g K ∧ IntegrableOn gs K ∧ IntegrableOn gt K)
    (c : ℝ) :
    HasWeakPartialsOn U (fun z => c • (f z - g z)) (fun z => c • (fs z - gs z))
      (fun z => c • (ft z - gt z)) := by
  intro φ hφ hc hU
  obtain ⟨hf1, hf2⟩ := hf φ hφ hc hU
  obtain ⟨hg1, hg2⟩ := hg φ hφ hc hU
  have hI : ∀ (v : ℂ) {k : ℂ → E}, (∀ K ⊆ U, IsCompact K → IntegrableOn k K) →
      Integrable (fun z => fderiv ℝ φ z v • k z) := by
    intro v k hk
    obtain ⟨h1, h2, h3⟩ := fderiv_apply_isTestFunction hφ hc hU v
    exact integrable_smul_of_integrableOn_compact hk h1.continuous.continuousOn h2 h3
  have hJ : ∀ {k : ℂ → E}, (∀ K ⊆ U, IsCompact K → IntegrableOn k K) →
      Integrable (fun z => φ z • k z) := fun hk =>
    integrable_smul_of_integrableOn_compact hk hφ.continuous.continuousOn hc hU
  have e1 : ∀ (v : ℂ) z, fderiv ℝ φ z v • (c • (f z - g z)) =
      c • (fderiv ℝ φ z v • f z - fderiv ℝ φ z v • g z) := by
    intro v z; rw [smul_comm, smul_sub]
  have e2 : ∀ z (k l : ℂ → E), φ z • (c • (k z - l z)) = c • (φ z • k z - φ z • l z) := by
    intro z k l; rw [smul_comm, smul_sub]
  constructor
  · simp_rw [e1, e2]
    rw [integral_smul, integral_smul, integral_sub (hI 1 fun K hK hKc => (hfi K hK hKc).1)
      (hI 1 fun K hK hKc => (hgi K hK hKc).1),
      integral_sub (hJ fun K hK hKc => (hfi K hK hKc).2.1)
      (hJ fun K hK hKc => (hgi K hK hKc).2.1), hf1, hg1]
    module
  · simp_rw [e1, e2]
    rw [integral_smul, integral_smul, integral_sub (hI Complex.I fun K hK hKc => (hfi K hK hKc).1)
      (hI Complex.I fun K hK hKc => (hgi K hK hKc).1),
      integral_sub (hJ fun K hK hKc => (hfi K hK hKc).2.2)
      (hJ fun K hK hKc => (hgi K hK hKc).2.2), hf2, hg2]
    module

/-- Weak partial derivatives of `β • w` for a real `C¹` function `β`. -/
theorem HasWeakPartialsOn.smul_left_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {β : ℂ → ℝ} (hβ : ContDiff ℝ 1 β)
    {w ws wt : ℂ → E} (hw : HasWeakPartialsOn U w ws wt)
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn w K ∧ IntegrableOn ws K ∧ IntegrableOn wt K) :
    HasWeakPartialsOn U (fun z => β z • w z) (fun z => fderiv ℝ β z 1 • w z + β z • ws z)
      (fun z => fderiv ℝ β z Complex.I • w z + β z • wt z) := by
  have hA : ContDiffOn ℝ 1 (fun z => β z • ContinuousLinearMap.id ℝ E) U :=
    (hβ.smul contDiff_const).contDiffOn
  have h := HasWeakPartialsOn.clm_apply hU hA hw hint
  have hd : ∀ z, fderiv ℝ (fun z => β z • ContinuousLinearMap.id ℝ E) z =
      (fderiv ℝ β z).smulRight (ContinuousLinearMap.id ℝ E) := fun z =>
    fderiv_smul_const (c := β) (f := ContinuousLinearMap.id ℝ E)
      ((hβ.differentiable (by norm_num)) z)
  simpa [hd] using h

/-- Translation of `L^p` membership and norm on a restricted measure. -/
theorem memLp_comp_add_right_aux {E : Type*} [NormedAddCommGroup E] {μ : Measure ℂ}
    [μ.IsAddRightInvariant] {q : ENNReal} {g : ℂ → E} {S : Set ℂ} (hS : MeasurableSet S) (a : ℂ)
    (hg : MemLp g q (μ.restrict S)) :
    MemLp (fun z => g (z + a)) q (μ.restrict ((· + a) ⁻¹' S)) ∧
      eLpNorm (fun z => g (z + a)) q (μ.restrict ((· + a) ⁻¹' S)) = eLpNorm g q (μ.restrict S) := by
  have hmp := (measurePreserving_add_right μ a).restrict_preimage hS
  exact ⟨hg.comp_measurePreserving hmp, eLpNorm_comp_measurePreserving hg.1 hmp⟩

end JHolomorphic

open JHolomorphic JHolomorphic.HasWeakPartialsOn

open MeasureTheory Metric
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {f fs ft : ℂ → E} (h : HasWeakPartialsOn U f fs ft) (a : ℂ) :
    HasWeakPartialsOn ((· + a) ⁻¹' U) (fun z => f (z + a)) (fun z => fs (z + a))
      (fun z => ft (z + a)) :=
  HasWeakPartialsOn.comp_add_right_aux h a
