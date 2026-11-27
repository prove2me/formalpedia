-- Prove2me | solution 1 for GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:13.673883+00:00
-- url     : https://prove2.me/submissions/4cb3ad85-d649-48c6-aaef-6107c33edd6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Theorems.Thm_GlobalTheory_essFiniteType_stalkMap_SpecMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {X Y : Scheme.{u}} {o : CommRingCat.{u}} [IsDedekindDomain o]
  (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o) [LocallyOfFiniteType g]
include g
omit f
namespace GlobalTheory
theorem _root_.solution (y : Y) {L : Type u} [Field L]
    [CharZero L] (φ : Y.presheaf.stalk y ⟶ .of L) (hφ : φ.hom.EssFiniteType) :
    IsFinite (Spec.map φ ≫ Y.fromSpecStalk y).fromNormalization := by
  refine isFinite_fromNormalization_of_genericPoints _ g (fun x _ => charZero_of_injective_ringHom
    ((Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).Γevaluation x).hom.injective) fun x _ => ?_
  have h : ((Spec.map φ ≫ Y.fromSpecStalk y).stalkMap x).hom.EssFiniteType := by
    rw [Scheme.Hom.stalkMap_comp]
    exact .comp (RingHom.FiniteType.of_surjective _
      (Scheme.Hom.stalkMap_surjective _ _)).essFiniteType (essFiniteType_stalkMap_SpecMap φ hφ x)
  exact h.residueFieldMap
end GlobalTheory
