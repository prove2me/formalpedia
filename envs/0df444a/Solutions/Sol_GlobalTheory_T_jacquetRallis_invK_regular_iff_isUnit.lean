-- Prove2me | solution 1 for GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:41:49.684733+00:00
-- url     : https://prove2.me/submissions/da2d6b9f-bed7-4380-a1b8-34e60cab0541

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Theorems.Thm_GlobalTheory_JR_EtInv_invK_regular_iff_isUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → Function.Bijective (fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a)) ∧ ∀ a : A.K, (∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a)) ∧ (Delta (A.invK τ p lam a) ≠ 0 ↔ IsUnit a) := by
  first | exact @GlobalTheory.JR.EtInv.invK_regular_iff_isUnit | exact GlobalTheory.JR.EtInv.invK_regular_iff_isUnit | (intros; apply GlobalTheory.JR.EtInv.invK_regular_iff_isUnit <;> assumption)
end _root_.GlobalTheory.T
