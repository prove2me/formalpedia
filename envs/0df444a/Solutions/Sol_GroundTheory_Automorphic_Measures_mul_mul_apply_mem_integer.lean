-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.mul_mul_apply_mem_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:45.601069+00:00
-- url     : https://prove2.me/submissions/6ffec834-a8ec-4f99-8b2b-b53c39aa5a57

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel Iwasawa
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution {A M B : Matrix (Fin n) (Fin n) F} (hA : ∀ i j, A i j ∈ 𝒪[F])
    (hM : ∀ i j, M i j ∈ 𝒪[F]) (hB : ∀ i j, B i j ∈ 𝒪[F]) (i j : Fin n) :
    (A * M * B) i j ∈ 𝒪[F] := by
  rw [Matrix.mul_apply]
  refine Subring.sum_mem _ fun b _ => Subring.mul_mem _ ?_ (hB b j)
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun a _ => Subring.mul_mem _ (hA i a) (hM a b)
end GroundTheory.Automorphic.Measures
