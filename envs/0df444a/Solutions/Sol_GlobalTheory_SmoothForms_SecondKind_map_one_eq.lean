-- Prove2me | solution 1 for GlobalTheory.SmoothForms.SecondKind.map_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:36.936797+00:00
-- url     : https://prove2.me/submissions/9e02d451-07e2-4ac7-a736-3538ed3aac2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SmoothInExponentialCoordsIffFirstSecondKind

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
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.SecondKind
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
open NumberField Matrix
open scoped ContDiff Topology
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
omit [FiniteDimensional ℝ 𝔸]
namespace GlobalTheory.SmoothForms.SecondKind
namespace _root_.GlobalTheory.SmoothForms.SecondKind
theorem _root_.solution (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) : s 1 = 1 := by
  have h := H.mul 1 1 (by rw [H.one, one_mul])
    (by rw [H.one, one_mul])
  rw [one_mul] at h
  exact mul_left_cancel (a := s 1) (by rw [mul_one]; exact h.symm)
end _root_.GlobalTheory.SmoothForms.SecondKind
end GlobalTheory.SmoothForms.SecondKind
