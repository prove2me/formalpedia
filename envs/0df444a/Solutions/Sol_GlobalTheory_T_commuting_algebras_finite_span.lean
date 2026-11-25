-- Prove2me | solution 1 for GlobalTheory.T.commuting_algebras_finite_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:31.076127+00:00
-- url     : https://prove2.me/submissions/a970b301-6fc3-4f8c-ba2d-10b5631aae8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutingAlgebrasFiniteSpan
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutingAlgebrasFiniteSpanStatement
import Theorems.Thm_GlobalTheory_FiniteOrbit_exists_finiteDimensional_stable


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Finite ι] (A : ι → Subalgebra ℂ (Module.End ℂ M)), (∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) → ∀ m : M, (∀ i, FiniteDimensional ℂ (Submodule.span ℂ {x : M | ∃ a ∈ A i, x = a m})) → ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧ m ∈ W ∧ ∀ i, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W := by
  first | exact @GlobalTheory.FiniteOrbit.exists_finiteDimensional_stable | exact GlobalTheory.FiniteOrbit.exists_finiteDimensional_stable | (intros; apply GlobalTheory.FiniteOrbit.exists_finiteDimensional_stable <;> assumption)
end _root_.GlobalTheory.T
