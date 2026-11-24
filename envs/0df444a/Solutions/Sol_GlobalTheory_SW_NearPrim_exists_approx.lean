-- Prove2me | solution 1 for GlobalTheory.SW.NearPrim.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:16:00.138252+00:00
-- url     : https://prove2.me/submissions/8730cc7b-72ca-4ac7-8bb9-1417015f66a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsBoundedMultipleNearInteger
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Theorems.Thm_GlobalTheory_SimultaneousDiophantineApprox_exists_bounded_multiple_near_integer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.NearPrim
namespace GlobalTheory.SW.NearPrim
theorem _root_.solution (E : Type) [Field E] [NumberField E] :
    ∃ M : ℕ, ∀ x : E, ∃ (m : ℕ) (y : E), 0 < m ∧ m ≤ M ∧ IsIntegral ℤ y ∧
      ‖canonicalEmbedding E (m * x - y)‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer
  | exact _root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer
  | (apply _root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer <;> assumption)
  | (intros; apply _root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer ..)
end GlobalTheory.SW.NearPrim
