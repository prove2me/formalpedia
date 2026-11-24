-- Prove2me | solution 1 for GlobalTheory.SmoothForms.DerLinear.contDiff_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:26.102802+00:00
-- url     : https://prove2.me/submissions/a4f970b3-a3e2-4bbd-a8f2-358807527577

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinear

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
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.DerLinear
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
namespace GlobalTheory.SmoothForms.DerLinear
theorem _root_.solution (H : IsLieData σ j s) : ContDiff ℝ ∞ fun X : L => NormedSpace.exp (j X) := by
  have : FiniteDimensional ℝ L := Module.Finite.of_injective j H.inj
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact hexp.comp (LinearMap.toContinuousLinearMap j).contDiff
end GlobalTheory.SmoothForms.DerLinear
