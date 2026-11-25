-- Prove2me | solution 1 for GroundTheory.Automorphic.logCoord_coe_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:59.861736+00:00
-- url     : https://prove2.me/submissions/c30a8dfc-8cf4-424d-8464-5d09e207ba37

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {𝔤 : Submodule ℝ 𝔸}
namespace GroundTheory.Automorphic
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (t : Fin d → ℝ) :
    b.equivFun.toContinuousLinearEquiv (subspaceProj 𝔤 (∑ i, t i • (b i : 𝔸))) = t := by
  have : (∑ i, t i • (b i : 𝔸)) = ((b.equivFun.symm t : 𝔤) : 𝔸) := by
    rw [Module.Basis.equivFun_symm_apply]; simp
  rw [this, subspaceProj_coe]
  exact b.equivFun.apply_symm_apply t
end GroundTheory.Automorphic
