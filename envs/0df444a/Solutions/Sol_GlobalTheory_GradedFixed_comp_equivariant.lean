-- Prove2me | solution 1 for GlobalTheory.GradedFixed.comp_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:36:38.627707+00:00
-- url     : https://prove2.me/submissions/22a7bb33-d605-453d-8f06-c34d74581c32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
open GlobalTheory GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
variable (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (c : ι → M →ₗ[ℂ] M)
  (hc1 : ∀ i w, c i w ∈ V i) (hc2 : ∀ i v, v ∈ V i → c i v = v)
  (hc3 : ∀ i j v, i ≠ j → v ∈ V j → c i v = 0) (hc4 : ∀ w, ∃ F : Finset ι, w = ∑ i ∈ F, c i w)
include hc1 hc2 hc3 hc4
namespace GlobalTheory.GradedFixed
theorem _root_.solution (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i))
    (g : G) (i : ι) (w : M) : c (g • i) (π g w) = π g (c i w) := by
  obtain ⟨F, hF⟩ := hc4 w
  rw [hF, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hmem : π g (c j w) ∈ V (g • j) := hπ g j (Submodule.mem_map_of_mem (hc1 j w))
  by_cases hij : j = i
  · subst hij
    rw [hc2 _ _ hmem, hc2 _ _ (hc1 j w)]
  · rw [hc3 _ _ _ (fun h => hij (smul_left_cancel g h).symm) hmem, hc3 _ _ _ (Ne.symm hij) (hc1 j w),
      map_zero]
end GlobalTheory.GradedFixed
