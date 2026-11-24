-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.SES.ex_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:36:05.704818+00:00
-- url     : https://prove2.me/submissions/16f16f19-c065-4fcb-ac1b-2e19fe5ef790

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
theorem _root_.solution {A B C : Cx R} (S : SES A B C) (hB : ∀ k, B.Ex k) {k : ℕ} (hC : C.Ex k) :
    A.Ex (k + 1) := by
  rw [Cx.ex_succ_iff]
  intro x hx
  obtain ⟨y, hy⟩ := Cx.ex_succ_iff.1 (hB (k + 1)) (S.i.f (k + 1) x) (by
    rw [← S.i.f_d, hx, map_zero])
  have hpy : C.d k (S.p.f k y) = 0 := by
    rw [← S.p.f_d, hy]
    exact (S.ex (k + 1) _).2 ⟨x, rfl⟩
  suffices h : ∃ y' : B.X k, B.d k y' = B.d k y ∧ S.p.f k y' = 0 by
    obtain ⟨y', h1, h2⟩ := h
    obtain ⟨x', rfl⟩ := (S.ex k y').1 h2
    refine ⟨x', S.inj (k + 1) ?_⟩
    rw [S.i.f_d, h1, hy]
  cases k with
  | zero =>
    exact ⟨y, rfl, Cx.ex_zero_iff.1 hC _ hpy⟩
  | succ k =>
    obtain ⟨z, hz⟩ := Cx.ex_succ_iff.1 hC _ hpy
    obtain ⟨y', rfl⟩ := S.surj k z
    refine ⟨y - B.d k y', ?_, ?_⟩
    · rw [map_sub, B.d_d, sub_zero]
    · rw [map_sub, S.p.f_d, hz, sub_self]
end SES
end GlobalTheory.CompanionTheory.NerveCoh
