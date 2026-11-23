-- Prove2me | solution 1 for GroundTheory.Automorphic.contDiffOn_logCoord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:40.182798+00:00
-- url     : https://prove2.me/submissions/9197847a-c32f-4e77-aebe-9f4ee18940d2

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
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiffOn ℝ ∞ (logCoord b) (expPartialHomeomorph ℝ 𝔸).target :=
  (b.equivFun.toContinuousLinearEquiv.contDiff.comp (subspaceProj 𝔤).contDiff).comp_contDiffOn
    (contDiffOn_expPartialHomeomorph_symm ℝ 𝔸)
end GroundTheory.Automorphic
