-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.contDiff_comp_coordEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:16.785288+00:00
-- url     : https://prove2.me/submissions/2fac93d5-e63f-491d-8e91-d8346e9900cc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : G → F} (hf : h.IsSmoothFun f) (g : G) {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin d) => f (g * h.expG (coordEquiv b x))) :=
  ((h.isSmoothFun_iff).1 hf g).comp (coordEquiv b).contDiff
end GroundTheory.Automorphic.IsExpLieAlgebra
