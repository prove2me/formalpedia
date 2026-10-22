-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.ae_eq_mixed
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T13:54:22.459107+00:00
-- url     : https://prove2.me/submissions/de2a88fd-5a9f-4de6-ba43-e4ac7c697c21

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Theorems.Thm_JHolomorphic_ae_eq_of_forall_integral_smul_eq
import Theorems.Thm_JHolomorphic_fderiv_apply_isTestFunction



namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- Weak mixed partial derivatives agree: if `u` has weak partials `uₛ`, `uₜ` on an open set `U`,
and these have weak partials `(uₛₛ, uₛₜ)` and `(uₜₛ, uₜₜ)`, then `uₛₜ = uₜₛ` almost everywhere
on `U`. -/
theorem HasWeakPartialsOn.ae_eq_mixed_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {u us ut uss ust uts utt : ℂ → E}
    (h : HasWeakPartialsOn U u us ut) (hs : HasWeakPartialsOn U us uss ust)
    (ht : HasWeakPartialsOn U ut uts utt)
    (hint : ∀ K ⊆ U, IsCompact K → IntegrableOn ust K ∧ IntegrableOn uts K) :
    ∀ᵐ z ∂(volume.restrict U), ust z = uts z := by
  refine ae_eq_of_forall_integral_smul_eq hU (fun K hKU hK => (hint K hKU hK).1)
    (fun K hKU hK => (hint K hKU hK).2) fun φ hφ hφc hφU => ?_
  obtain ⟨hd1, hc1, hU1⟩ := fderiv_apply_isTestFunction hφ hφc hφU 1
  obtain ⟨hdI, hcI, hUI⟩ := fderiv_apply_isTestFunction hφ hφc hφU Complex.I
  have hsym : ∀ z, fderiv ℝ (fun y => fderiv ℝ φ y Complex.I) z 1 =
      fderiv ℝ (fun y => fderiv ℝ φ y 1) z Complex.I := by
    intro z
    have hdiff : DifferentiableAt ℝ (fderiv ℝ φ) z :=
      ((hφ.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiable one_ne_zero) z
    have hS := (hφ.contDiffAt (x := z)).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    rw [fderiv_clm_apply hdiff (differentiableAt_const _),
      fderiv_clm_apply hdiff (differentiableAt_const _)]
    simpa using hS 1 Complex.I
  have e1 := (hs φ hφ hφc hφU).2
  have e2 := (h _ hdI hcI hUI).1
  have e3 := (ht φ hφ hφc hφU).1
  have e4 := (h _ hd1 hc1 hU1).2
  calc ∫ z, φ z • ust z = -∫ z, fderiv ℝ φ z Complex.I • us z := by rw [e1, neg_neg]
    _ = ∫ z, fderiv ℝ (fun y => fderiv ℝ φ y Complex.I) z 1 • u z := by rw [e2]
    _ = ∫ z, fderiv ℝ (fun y => fderiv ℝ φ y 1) z Complex.I • u z := by
        congr 1; funext z; rw [hsym z]
    _ = -∫ z, fderiv ℝ φ z 1 • ut z := e4
    _ = ∫ z, φ z • uts z := by rw [e3, neg_neg]

end JHolomorphic

open JHolomorphic JHolomorphic.HasWeakPartialsOn

open MeasureTheory Filter Topology
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {u us ut uss ust uts utt : ℂ → E}
    (h : HasWeakPartialsOn U u us ut) (hs : HasWeakPartialsOn U us uss ust)
    (ht : HasWeakPartialsOn U ut uts utt)
    (hint : ∀ K ⊆ U, IsCompact K → IntegrableOn ust K ∧ IntegrableOn uts K) :
    ∀ᵐ z ∂(volume.restrict U), ust z = uts z :=
  HasWeakPartialsOn.ae_eq_mixed_aux hU h hs ht hint
