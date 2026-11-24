-- Prove2me | solution 1 for GlobalTheory.GradedFixed.mem_WA_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:36:33.494829+00:00
-- url     : https://prove2.me/submissions/a731b060-9be0-4d1d-a1d1-427d98ca461f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight
import Theorems.Thm_GlobalTheory_GradedFixed_le_WA

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
omit hc2 hc4
namespace GlobalTheory.GradedFixed
theorem _root_.solution {A : Set ι} {F : Finset ι} (hF : ∀ j ∈ F, j ∈ A) (w : M)
    (hw : w = ∑ i ∈ F, c i w) : w ∈ WA V A := by
  rw [hw]
  exact Submodule.sum_mem _ fun j hj => le_WA V (hF j hj) (hc1 j w)
end GlobalTheory.GradedFixed
