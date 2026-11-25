-- Prove2me | solution 1 for GlobalTheory.isFinite_fromNormalization_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:53.384848+00:00
-- url     : https://prove2.me/submissions/d9de9873-6318-4a3f-9c33-2a4285f1a970

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField

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
namespace GlobalTheory
theorem _root_.solution [IsIntegral X] [CharZero X.functionField]
    (hess : (f.stalkMap (genericPoint X)).hom.EssFiniteType) : IsFinite f.fromNormalization := by
  refine isFinite_fromNormalization_of_dense f g (D := {genericPoint X})
    (dense_iff_closure_eq.mpr (genericPoint_spec X))
    (fun W _ => (Set.finite_singleton _).inter_of_left _)
    ?_ ?_
  · rintro _ rfl
    exact charZero_of_injective_ringHom (R := X.functionField)
      (X.residue (genericPoint X)).hom.injective
  · rintro _ rfl
    exact hess.residueFieldMap
end GlobalTheory
