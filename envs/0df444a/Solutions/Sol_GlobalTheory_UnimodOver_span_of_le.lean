-- Prove2me | solution 1 for GlobalTheory.UnimodOver.span_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:14.09281+00:00
-- url     : https://prove2.me/submissions/6662fb16-c943-43a8-afe0-2135631be348

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnimodOver
open Module
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory.UnimodOver
theorem _root_.solution {L M : Submodule ℤ V} (hs : Submodule.span ℝ (L : Set V) = ⊤) (h : L ≤ M) :
    Submodule.span ℝ (M : Set V) = ⊤ := by
  rw [eq_top_iff, ← hs]
  exact Submodule.span_mono h
end GlobalTheory.UnimodOver
