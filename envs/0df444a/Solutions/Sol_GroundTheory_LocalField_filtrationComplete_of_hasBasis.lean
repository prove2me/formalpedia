-- Prove2me | solution 1 for GroundTheory.LocalField.filtrationComplete_of_hasBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:46:41.321171+00:00
-- url     : https://prove2.me/submissions/3a134603-8835-4d24-a470-a13896f2b1f0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Theorems.Thm_GroundTheory_LocalField_map_eq_of_graded_surjective
import Theorems.Thm_GroundTheory_LocalField_surjective_of_graded_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Filter Topology Uniformity
namespace GroundTheory.LocalField
theorem _root_.solution {G : Type*} [Group G] [UniformSpace G]
    [IsRightUniformGroup G] [CompleteSpace G] {F : ℕ → Subgroup G}
    (hb : (𝓝 (1 : G)).HasBasis (fun _ => True) (fun n => (F n : Set G))) :
    FiltrationComplete F := by
  intro x hx
  have hU : (𝓤 G).HasBasis (fun _ : ℕ => True)
      (fun n => (fun p : G × G => p.2 / p.1) ⁻¹' (F n : Set G)) := by
    rw [uniformity_eq_comap_nhds_one G]
    exact hb.comap _
  have hcs : CauchySeq x := by
    rw [hU.cauchySeq_iff]
    intro N _
    obtain ⟨M, hM⟩ := hx N
    exact ⟨M, fun m hm n hn => hM m hm n hn⟩
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨y, fun N => ?_⟩
  have h1 : Tendsto (fun n => x n / y) atTop (𝓝 1) := by
    simpa using hy.div_const' y
  exact eventually_atTop.mp ((hb.tendsto_right_iff.mp h1) N trivial)
end GroundTheory.LocalField
