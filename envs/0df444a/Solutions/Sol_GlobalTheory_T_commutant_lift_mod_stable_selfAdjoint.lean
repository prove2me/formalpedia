-- Prove2me | solution 1 for GlobalTheory.T.commutant_lift_mod_stable_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:44.640416+00:00
-- url     : https://prove2.me/submissions/1a11524f-e182-4165-a71e-71f540e5928d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutantLiftModStableSelfAdjoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutantLiftModStableSelfAdjointStatement
import Theorems.Thm_GlobalTheory_matrix_commutant_lift_mod_stable


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
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (Matrix ι ι ℂ)) (N : Submodule ℂ (Matrix ι ι ℂ)), (∀ x ∈ S, xᴴ ∈ S) → (∀ x ∈ S, ∀ y ∈ N, x * y - y * x ∈ N) → ∀ M : Matrix ι ι ℂ, (∀ x ∈ S, x * M - M * x ∈ N) → ∃ M₀ : Matrix ι ι ℂ, M - M₀ ∈ N ∧ ∀ x ∈ S, x * M₀ = M₀ * x := by
  first | exact @GlobalTheory.matrix_commutant_lift_mod_stable | exact GlobalTheory.matrix_commutant_lift_mod_stable | (intros; apply GlobalTheory.matrix_commutant_lift_mod_stable <;> assumption)
end _root_.GlobalTheory.T
