-- Prove2me | solution 1 for GroundTheory.Automorphic.contDiff_smul_of_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:57.223917+00:00
-- url     : https://prove2.me/submissions/5db509ba-965f-47b3-b186-e543ab1fb328

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
theorem _root_.solution {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {O : Set V} (hO : IsOpen O) {f : V → F}
    {g : V → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiff ℝ ∞ g) (hgO : tsupport g ⊆ O) :
    ContDiff ℝ ∞ (fun x => g x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ O
  · exact hg.contDiffAt.smul (hf.contDiffAt (hO.mem_nhds hx))
  · have hx' : x ∉ tsupport g := fun h' => hx (hgO h')
    have : (fun x => g x • f x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq this
end GroundTheory.Automorphic
