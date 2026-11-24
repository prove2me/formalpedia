-- Prove2me | solution 1 for GlobalTheory.ArcAvoid.surjective_residue_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:09.844887+00:00
-- url     : https://prove2.me/submissions/4d5bc186-b96d-4482-b601-29c3b6216baf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_StalkGenericPointSpecializesOfSpecializes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingEquivPowerSeriesOfComplete
import Theorems.Thm_GlobalTheory_powerSeriesPrimeX_asIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.powerSeriesPrimeX_asIdeal



set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.ArcAvoid
open Polynomial
namespace GlobalTheory.ArcAvoid
theorem _root_.solution {k V : Type*} [Field k] [IsAlgClosed k] [CommRing V]
    [IsDomain V] [IsLocalRing V] [Algebra k[X] V] [Algebra.IsAlgebraic k[X] V]
    [FaithfulSMul k[X] V] (hX : algebraMap k[X] V X ∈ maximalIdeal V) :
    Function.Surjective ((residue V).comp ((algebraMap k[X] V).comp C)) := by
  classical
  letI : Algebra k (ResidueField V) := ((residue V).comp ((algebraMap k[X] V).comp C)).toAlgebra
  have hc : (algebraMap k (ResidueField V)).comp (constantCoeff : k[X] →+* k) =
      (residue V).comp (algebraMap k[X] V) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [RingHom.algebraMap_toAlgebra]
    · simpa using ((residue_eq_zero_iff _).mpr hX).symm
  have : Algebra.IsAlgebraic k (ResidueField V) := ⟨fun y => by
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := k[X]) x
    have h1 := aeval_primPart_eq_zero hp0 hp
    refine ⟨p.primPart.map constantCoeff, fun h => ?_, ?_⟩
    · refine Polynomial.not_isUnit_X (R := k) (p.isPrimitive_primPart X ?_)
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have := congrArg (fun q => q.coeff i) h
      simpa [X_dvd_iff] using this
    · rw [aeval_def, eval₂_map, hc, ← hom_eval₂, ← aeval_def, h1, map_zero]⟩
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := ResidueField V)).2
end GlobalTheory.ArcAvoid
