-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.FiniteReduction.map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:49.326209+00:00
-- url     : https://prove2.me/submissions/327f5aec-4c9e-4f1e-ba61-f3741d3714c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_FormalIsogeny_finiteReduction_iff
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.FormalIsogeny
variable {R : Type*} [CommRing R] {σ τ : Type*} [Finite σ]
variable [IsLocalRing R]
namespace GlobalTheory.FormalIsogeny
namespace FiniteReduction
theorem _root_.solution {S : Type*} [CommRing S] [IsLocalRing S] (ρ : R →+* S) [IsLocalHom ρ]
    {f : τ → MvPowerSeries σ R} (h : FiniteReduction f) :
    FiniteReduction fun j => MvPowerSeries.map ρ (f j) := by
  obtain ⟨N, hN⟩ := finiteReduction_iff.1 h
  refine finiteReduction_iff.2 ⟨N, ?_⟩
  have := Ideal.map_mono (f := MvPowerSeries.map (σ := σ) (ResidueField.map ρ)) hN
  rw [Ideal.map_pow, Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp] at this
  have e1 : (MvPowerSeries.map (σ := σ) (ResidueField.map ρ)) ∘ X = X := by
    ext1 i
    simp
  have e2 : ((MvPowerSeries.map (ResidueField.map ρ)) ∘
      fun j => MvPowerSeries.map (residue R) (f j)) =
      fun j => MvPowerSeries.map (residue S) (MvPowerSeries.map ρ (f j)) := by
    ext j d
    simp only [Function.comp_apply, coeff_map, ResidueField.map_residue]
  rwa [e1, e2] at this
end FiniteReduction
end GlobalTheory.FormalIsogeny
