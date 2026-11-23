-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.contDiff_comp_expG_mul_expG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:43.363891+00:00
-- url     : https://prove2.me/submissions/1518bcdf-1f5b-4bd0-95b9-1243b8643467

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : G → F} (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, F) ∞ f)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ₁ φ₂ : V → 𝔤}
    (h₁ : ContDiff ℝ ∞ φ₁) (a : G) (h₂ : ContDiff ℝ ∞ φ₂) :
    ContDiff ℝ ∞ (fun p => f (h.expG (φ₁ p) * a * h.expG (φ₂ p))) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, 𝔤) ∞ (fun p => h.expG (φ₁ p) * a * h.expG (φ₂ p)) :=
    ((h.contMDiff_expG_comp h₁).mul contMDiff_const).mul (h.contMDiff_expG_comp h₂)
  exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf hm).contDiff
end GroundTheory.Automorphic.IsExpLieAlgebra
