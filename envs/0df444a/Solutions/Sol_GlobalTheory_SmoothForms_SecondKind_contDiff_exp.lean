-- Prove2me | solution 1 for GlobalTheory.SmoothForms.SecondKind.contDiff_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:17.435803+00:00
-- url     : https://prove2.me/submissions/cd0b014e-be33-4c09-9748-d61dd9f4c08b

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
namespace GlobalTheory.SmoothForms.SecondKind
namespace _root_.GlobalTheory.SmoothForms.SecondKind
theorem _root_.solution : ContDiff ℝ ∞ (exp : 𝔸 → 𝔸) := by
  haveI := FiniteDimensional.complete ℝ 𝔸
  exact AnalyticOnNhd.contDiff fun x _ => exp_analytic x
end _root_.GlobalTheory.SmoothForms.SecondKind
end GlobalTheory.SmoothForms.SecondKind
