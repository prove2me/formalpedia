-- Prove2me | solution 1 for GlobalTheory.ClosedResidueExt.Unram.factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:46.961899+00:00
-- url     : https://prove2.me/submissions/53e6aa4b-6e7b-46aa-83c5-2770fbde6e33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueField
import Theorems.Thm_GlobalTheory_ClosedResidueExt_Unram_isUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedResidueExt
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]
namespace GlobalTheory.ClosedResidueExt
namespace Unram
theorem _root_.solution {π : W} {R : Subalgebra W Ω} (h : Unram π R) (x : R) (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : Rˣ), algebraMap W R π ^ n * u = x := by
  have hx' : (x : Ω) ≠ 0 := fun e => hx (Subtype.ext e)
  obtain ⟨n, u, hu, hu', e⟩ := h.2.2 x x.2 hx'
  have h0 : u ≠ 0 := by
    rintro rfl
    exact hx' (by simpa using e)
  refine ⟨n, (Unram.isUnit hu hu' h0).unit, Subtype.ext ?_⟩
  simp [e]
end Unram
end GlobalTheory.ClosedResidueExt
