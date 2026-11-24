-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.SES.ex_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:36:04.851923+00:00
-- url     : https://prove2.me/submissions/5be115dd-7550-429b-9f23-3f10cdb38d9f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_Cx_ex_zero_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_Cx_ex_succ_iff
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
namespace SES
theorem _root_.solution {A B C : Cx R} (S : SES A B C) (hA : ∀ k, A.Ex k) (hB : ∀ k, B.Ex k) (k : ℕ) :
    C.Ex k := by
  have key : ∀ (k : ℕ) (y : B.X k), C.d k (S.p.f k y) = 0 →
      ∃ x' : A.X k, B.d k (y - S.i.f k x') = 0 := by
    intro k y hy
    obtain ⟨x, hx⟩ := (S.ex (k + 1) (B.d k y)).1 (by rw [S.p.f_d, hy])
    obtain ⟨x', rfl⟩ := Cx.ex_succ_iff.1 (hA (k + 1)) x (S.inj (k + 2) (by
      rw [S.i.f_d, hx, B.d_d, map_zero]))
    refine ⟨x', ?_⟩
    rw [map_sub, ← S.i.f_d, hx, sub_self]
  cases k with
  | zero =>
    rw [Cx.ex_zero_iff]
    intro z hz
    obtain ⟨y, rfl⟩ := S.surj 0 z
    obtain ⟨x', hx'⟩ := key 0 y hz
    have := Cx.ex_zero_iff.1 (hB 0) _ hx'
    rw [sub_eq_zero] at this
    rw [this]
    exact (S.ex 0 _).2 ⟨x', rfl⟩
  | succ k =>
    rw [Cx.ex_succ_iff]
    intro z hz
    obtain ⟨y, rfl⟩ := S.surj (k + 1) z
    obtain ⟨x', hx'⟩ := key (k + 1) y hz
    obtain ⟨y', hy'⟩ := Cx.ex_succ_iff.1 (hB (k + 1)) _ hx'
    refine ⟨S.p.f k y', ?_⟩
    rw [← S.p.f_d, hy', map_sub, (S.ex (k + 1) _).2 ⟨x', rfl⟩, sub_zero]
end SES
end GlobalTheory.CompanionTheory.NerveCoh
