-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.qiso_of_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:45:46.90569+00:00
-- url     : https://prove2.me/submissions/3b1e02e7-4096-47b8-9ec2-09f16b34249b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_cone_ex_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_cone_ex_one
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_cone_ex_succ
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero


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
theorem _root_.solution {A B : Cx R} (f : Hm A B) (h : ∀ k, (cone f).Ex k) :
    (∀ a, A.d 0 a = 0 → f.f 0 a = 0 → a = 0) ∧
    (∀ b, B.d 0 b = 0 → ∃ a, A.d 0 a = 0 ∧ f.f 0 a = b) ∧
    (∀ n a, A.d (n + 1) a = 0 → ∀ b, B.d n b = f.f (n + 1) a → ∃ y, A.d n y = a) ∧
    (∀ n z, B.d (n + 1) z = 0 → ∃ x y, A.d (n + 1) x = 0 ∧ f.f (n + 1) x - z = B.d n y) := by
  refine ⟨(cone_ex_zero f).1 (h 0), fun b hb ↦ ?_, fun n a ha b hb ↦ ?_, fun n z hz ↦ ?_⟩
  · exact (cone_ex_one f).1 (h 1) 0 b (map_zero _) (by rw [map_zero, hb])
  · cases n with
    | zero =>
      obtain ⟨y, h1, -⟩ := (cone_ex_one f).1 (h 1) a b ha hb.symm
      exact ⟨y, h1⟩
    | succ k =>
      obtain ⟨y, z, h1, -⟩ := (cone_ex_succ f k).1 (h (k + 2)) a b ha hb.symm
      exact ⟨y, h1⟩
  · obtain ⟨y, w, h1, h2⟩ := (cone_ex_succ f n).1 (h (n + 2)) 0 z (map_zero _) (by rw [map_zero, hz])
    exact ⟨y, w, h1, by rw [← h2]; abel⟩
end GlobalTheory.CompanionTheory.NerveCoh
