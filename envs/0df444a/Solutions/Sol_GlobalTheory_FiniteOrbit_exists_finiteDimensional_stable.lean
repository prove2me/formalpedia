-- Prove2me | solution 1 for GlobalTheory.FiniteOrbit.exists_finiteDimensional_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:59:31.642166+00:00
-- url     : https://prove2.me/submissions/6def6034-ae4a-4279-afd3-b84b30c99883

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutingAlgebrasFiniteSpan
import Theorems.Thm_GlobalTheory_OrbitGrowth_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.FiniteOrbit
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.FiniteOrbit
theorem _root_.solution (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type)
    [Finite ι] (A : ι → Subalgebra ℂ (Module.End ℂ M))
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) (m : M)
    (hm : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ {x : M | ∃ a ∈ A i, x = a m})) :
    ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧ m ∈ W ∧ ∀ i, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W := by
  first
  | exact @_root_.GlobalTheory.OrbitGrowth.main
  | exact _root_.GlobalTheory.OrbitGrowth.main
  | (apply _root_.GlobalTheory.OrbitGrowth.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrbitGrowth.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrbitGrowth.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrbitGrowth.main ..)
end GlobalTheory.FiniteOrbit
