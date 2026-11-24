-- Prove2me | solution 1 for GlobalTheory.GradedFixed.eq_zero_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:36:39.296803+00:00
-- url     : https://prove2.me/submissions/aa368511-a5d0-446e-b093-308f4dc53a6d

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
omit hc1 hc2 hc3
namespace GlobalTheory.GradedFixed
theorem _root_.solution {x : M} (h : ∀ l, c l x = 0) : x = 0 := by
  obtain ⟨F, hF⟩ := hc4 x
  rw [hF]
  exact Finset.sum_eq_zero fun l _ => h l
end GlobalTheory.GradedFixed
