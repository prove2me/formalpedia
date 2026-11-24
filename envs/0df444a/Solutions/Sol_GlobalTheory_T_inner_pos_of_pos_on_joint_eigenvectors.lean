-- Prove2me | solution 1 for GlobalTheory.T.inner_pos_of_pos_on_joint_eigenvectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:16.253191+00:00
-- url     : https://prove2.me/submissions/629c0251-f00b-4c67-a16e-c37f24c2a9bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosOfPosMulInnerOnJointEigenvectors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosOfPosMulInnerOnJointEigenvectorsStatement
import Theorems.Thm_GlobalTheory_pos_of_pos_mul_inner_on_joint_eigenvectors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (W : Submodule ℂ V), FiniteDimensional ℂ W → ∀ (I : Type) (T : I → Module.End ℂ V), (∀ i, ∀ w ∈ W, T i w ∈ W) → (∀ i x y, inner ℂ (ι (T i x)) (ι y) = inner ℂ (ι x) (ι (T i y))) → (∀ i j, T i * T j = T j * T i) → ∀ (u : V →ₗ[ℂ] H), (∀ (m : I → ℝ), ∀ y ∈ W, (∀ i, T i y = (m i : ℂ) • y) → ∃ c : ℝ, 0 < c ∧ ∀ x ∈ W, inner ℂ (ι x) (u y) = (c : ℂ) * inner ℂ (ι x) (ι y)) → ∀ x ∈ W, x ≠ 0 → (inner ℂ (ι x) (u x)).im = 0 ∧ 0 < (inner ℂ (ι x) (u x)).re := by
  first | exact @GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors | exact GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors | (intros; apply GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors <;> assumption)
end _root_.GlobalTheory.T
