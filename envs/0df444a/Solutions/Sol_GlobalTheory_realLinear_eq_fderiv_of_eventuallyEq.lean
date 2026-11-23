-- Prove2me | solution 1 for GlobalTheory.realLinear_eq_fderiv_of_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:19.610636+00:00
-- url     : https://prove2.me/submissions/0e1b0b5c-bd06-453b-a7ad-67a5e4937b6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [IsScalarTower ℝ 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W]
namespace GlobalTheory
theorem _root_.solution {g : V → W} (hd : DifferentiableAt 𝕜 g 0)
    {L : V →L[ℝ] W} {c : W} (hL : ∀ᶠ z in 𝓝 0, g z = L z + c) :
    L = (fderiv 𝕜 g 0).restrictScalars ℝ :=
  ((L.hasFDerivAt.add_const c).congr_of_eventuallyEq hL).unique
    (hd.hasFDerivAt.restrictScalars ℝ)
end GlobalTheory
