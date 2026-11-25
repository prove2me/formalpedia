-- Prove2me | solution 1 for GlobalTheory.BadShare.SqCount.exists_sq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:59:39.052295+00:00
-- url     : https://prove2.me/submissions/98897361-7d3d-4a2f-b0d4-2b708662fd2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.SqCount
namespace GlobalTheory.BadShare.SqCount
theorem _root_.solution {k : Type} [Field k] {f : k[X]} (hf : f.Monic) :
    ∃ a b : k[X], a.Monic ∧ b.Monic ∧ Squarefree b ∧ f = a ^ 2 * b := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  by_cases hs : Squarefree f
  · exact ⟨1, f, monic_one, hf, hs, by simp⟩
  obtain ⟨x, hx, hu⟩ : ∃ x, x * x ∣ f ∧ ¬ IsUnit x := by
    by_contra hc
    exact hs fun x hx => by_contra fun hu => hc ⟨x, hx, hu⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hf.ne_zero (by simpa using hx)
  have hy : (normalize x).Monic := monic_normalize hx0
  have hass : Associated (normalize x) x := normalize_associated x
  obtain ⟨h, rfl⟩ := (hass.mul_mul hass).dvd.trans hx
  have hh : h.Monic := (hy.mul hy).of_mul_monic_left hf
  have hpos : 0 < (normalize x).natDegree :=
    natDegree_pos_of_not_isUnit_of_dvd_monic hy (fun hu' => hu (hass.isUnit hu')) dvd_rfl
  rw [(hy.mul hy).natDegree_mul hh, hy.natDegree_mul hy] at hn
  obtain ⟨a, b, ha, hb, hsq, rfl⟩ := ih h.natDegree (by omega) hh rfl
  exact ⟨normalize x * a, b, hy.mul ha, hb, hsq, by ring⟩
end GlobalTheory.BadShare.SqCount
