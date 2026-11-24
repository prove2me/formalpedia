-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.cone_ex_of_acyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:45:46.213009+00:00
-- url     : https://prove2.me/submissions/bf9f8ff7-b201-45b2-9386-c848388107c8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_Cx_ex_succ_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_cone_ex_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_cone_ex_one
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_cone_ex_succ

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
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.NerveCoh
theorem _root_.solution {A B : Cx R} (f : Hm A B) (hA : ∀ k, A.Ex (k + 1)) (hB : ∀ k, B.Ex (k + 1))
    (h0 : ∀ a, A.d 0 a = 0 → f.f 0 a = 0 → a = 0)
    (h1 : ∀ b, B.d 0 b = 0 → ∃ a, A.d 0 a = 0 ∧ f.f 0 a = b) (k : ℕ) : (cone f).Ex k := by
  match k with
  | 0 => exact (cone_ex_zero f).2 h0
  | 1 =>
    refine (cone_ex_one f).2 fun a b ha hb ↦ ?_
    obtain ⟨y, rfl⟩ := Cx.ex_succ_iff.1 (hA 0) a ha
    obtain ⟨y', h2, h3⟩ := h1 (b - f.f 0 y) (by rw [map_sub, ← hb, f.f_d, sub_self])
    exact ⟨y + y', by rw [map_add, h2, add_zero], by rw [map_add, h3, add_sub_cancel]⟩
  | k + 2 =>
    refine (cone_ex_succ f k).2 fun a b ha hb ↦ ?_
    obtain ⟨y, rfl⟩ := Cx.ex_succ_iff.1 (hA (k + 1)) a ha
    obtain ⟨z, hz⟩ := Cx.ex_succ_iff.1 (hB k) (f.f (k + 1) y - b) (by
      rw [map_sub, ← hb, f.f_d, sub_self])
    exact ⟨y, z, rfl, by rw [hz, sub_sub_cancel]⟩
end GlobalTheory.CompanionTheory.NerveCoh
