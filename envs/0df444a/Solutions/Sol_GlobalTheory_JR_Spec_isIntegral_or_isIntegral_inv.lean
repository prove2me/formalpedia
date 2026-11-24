-- Prove2me | solution 1 for GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:29:45.817488+00:00
-- url     : https://prove2.me/submissions/3a2ecfa0-a152-48a5-8965-bb7c7421d796

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametric
import Theorems.Thm_GlobalTheory_JR_Spec_isIntegral_integer_of_spectralNorm_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open Polynomial
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Spec
variable {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
  {k : Type} [Field k] [Algebra F k]
namespace GlobalTheory.JR.Spec
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 →
    IsIntegral (NormedField.valuation (K := F)).integer y ∨
      IsIntegral (NormedField.valuation (K := F)).integer y⁻¹ := by
  intro F _ _ _ k _ _ _ y hy0
  have hmul : spectralNorm F k y * spectralNorm F k y⁻¹ = 1 := by
    have := spectralAlgNorm_mul (K := F) (L := k) y y⁻¹
    rw [spectralAlgNorm_def, spectralAlgNorm_def, spectralAlgNorm_def, mul_inv_cancel₀ hy0,
      spectralNorm_one] at this
    exact this.symm
  by_cases h : spectralNorm F k y ≤ 1
  · exact Or.inl (isIntegral_integer_of_spectralNorm_le_one h)
  · right
    apply isIntegral_integer_of_spectralNorm_le_one
    have h1 : 1 < spectralNorm F k y := lt_of_not_ge h
    by_contra h2
    have h2 : 1 < spectralNorm F k y⁻¹ := lt_of_not_ge h2
    have : 1 < spectralNorm F k y * spectralNorm F k y⁻¹ := one_lt_mul_of_lt_of_le h1 h2.le
    linarith
end GlobalTheory.JR.Spec
