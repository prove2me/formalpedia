-- Prove2me | solution 1 for GlobalTheory.CubeFace.sum_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:54.064916+00:00
-- url     : https://prove2.me/submissions/1acb2463-10d4-4a0a-beca-131a4e567d60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.CubeFace
namespace GlobalTheory.CubeFace
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] (z : V) (J : Finset (Fin 3)) :
    ∑ a ∈ J, (![z, z, -z] : Fin 3 → V) a = diagChart z (-z) ((2 : ℂ) • z) 0 J := by
  have : J ∈ ({∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} :
      Finset (Finset (Fin 3))) := by revert J; decide
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [diagChart, two_smul]
end GlobalTheory.CubeFace
