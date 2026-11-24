-- Prove2me | solution 1 for GlobalTheory.Cube.termUpper_d_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:46.975825+00:00
-- url     : https://prove2.me/submissions/460fcea5-f555-4e46-b5dd-c179ecb7e9e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι}
variable (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R)
namespace GlobalTheory.Cube
theorem _root_.solution (x : Term A 0) :
    termUpper he A 0 (d A 0 x) = termMap (faceMap e i A) 0 (termLower e A 0 x) := by
  funext ⟨s, hs⟩
  rw [termUpper_apply, d_apply_eq_totalD A x _ (fun s => (extend_apply_of_eq A x s.2).symm),
    totalD_insert_map he]
  obtain rfl := Finset.card_eq_zero.1 hs
  refine (congrArg (· + _) (totalD_apply (upperFace e i A) _ ∅)).trans ?_
  rw [Finset.sum_empty, zero_add, Finset.card_empty, pow_zero, one_smul,
    extend_apply_of_eq A x ((Finset.card_map _).trans hs)]
  rfl
end GlobalTheory.Cube
