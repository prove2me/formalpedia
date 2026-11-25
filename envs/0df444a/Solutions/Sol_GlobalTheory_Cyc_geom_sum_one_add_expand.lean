-- Prove2me | solution 1 for GlobalTheory.Cyc.geom_sum_one_add_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:55:26.481607+00:00
-- url     : https://prove2.me/submissions/71c18d59-5eca-40d1-9f0a-380bf2672d3a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneOfNotDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Cyc
namespace GlobalTheory.Cyc
theorem _root_.solution {R : Type*} [CommRing R] (y : R) (n : ℕ) :
    ∃ z : R, (1 + y) ^ n - 1 = y * ((n : R) + (n.choose 2 : ℕ) * y + y ^ 2 * z) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨z + (n.choose 2 : ℕ) + y * z, ?_⟩
    have h : (1 + y) ^ n = 1 + y * ((n : R) + (n.choose 2 : ℕ) * y + y ^ 2 * z) := by
      rw [← hz]; ring
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    rw [pow_succ, h, hc]
    push_cast
    ring
end GlobalTheory.Cyc
