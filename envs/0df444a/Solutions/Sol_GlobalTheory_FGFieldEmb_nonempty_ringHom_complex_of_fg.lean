-- Prove2me | solution 1 for GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:42:19.408176+00:00
-- url     : https://prove2.me/submissions/e647c904-8869-4856-89db-756b1cab0214

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonemptyRingHomComplexOfFg
import Theorems.Thm_GlobalTheory_FGFieldEmb_nonempty_ringHom_complex_of_mk_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.FGFieldEmb
open Cardinal
namespace GlobalTheory.FGFieldEmb
theorem _root_.solution :
    ∀ (K : Type) [Field K] [CharZero K] (k : IntermediateField ℚ K), k.FG → Nonempty (k →+* ℂ) := by
  intro K _ _ k hk
  obtain ⟨t, rfl⟩ := hk
  refine nonempty_ringHom_complex_of_mk_le _ ?_
  refine le_trans ?_ Cardinal.aleph0_le_continuum
  refine (IntermediateField.cardinalMk_adjoin_le ℚ (t : Set K)).trans ?_
  refine max_le (max_le ?_ ?_) le_rfl
  · simp [Cardinal.mkRat]
  · exact (Cardinal.lt_aleph0_of_finite _).le
end GlobalTheory.FGFieldEmb
