-- Prove2me | solution 1 for GlobalTheory.UnitLemma.StabIndex.isUnit_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:00:13.441524+00:00
-- url     : https://prove2.me/submissions/39a59b07-8c9d-41a9-a86a-cb8c406cc2a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelIndexNeZeroOfBetween

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open scoped Pointwise
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.StabIndex
namespace GlobalTheory.UnitLemma.StabIndex
theorem _root_.solution (K : UQ) (B : InvAlg K) (c : K.O) (hc : c ≠ 0) :
    IsUnit (algebraMap K.O B.A c) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
  refine (isUnit_iff_ne_zero.mpr ?_).map (algebraMap K.E B.A)
  exact (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).mpr hc
end GlobalTheory.UnitLemma.StabIndex
