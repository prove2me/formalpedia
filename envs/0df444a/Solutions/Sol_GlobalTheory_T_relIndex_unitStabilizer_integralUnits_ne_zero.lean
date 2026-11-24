-- Prove2me | solution 1 for GlobalTheory.T.relIndex_unitStabilizer_integralUnits_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:41:29.470356+00:00
-- url     : https://prove2.me/submissions/df87fd47-1aaf-4042-a8cf-2f342ca9127c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelIndexUnitStabilizerIntegralUnitsNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelIndexUnitStabilizerIntegralUnitsNeZeroStatement
import Theorems.Thm_GlobalTheory_UnitLemma_StabIndex_relIndex_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 → (∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) → (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  first | exact @GlobalTheory.UnitLemma.StabIndex.relIndex_ne_zero | exact GlobalTheory.UnitLemma.StabIndex.relIndex_ne_zero | (intros; apply GlobalTheory.UnitLemma.StabIndex.relIndex_ne_zero <;> assumption)
end _root_.GlobalTheory.T
