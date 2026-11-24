-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.exists_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:52:00.927777+00:00
-- url     : https://prove2.me/submissions/a56712de-b315-4953-be8b-dde973a61c6d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_nontrivial_of_resAlg
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_fixed_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormUnit
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormUnit
theorem _root_.solution (h : ResAlg E τ q ε) (hnf : ¬ IsField E) :
    ∃ e : E, e + τ e = 1 ∧ e * τ e = 0 := by
  have := nontrivial_of_resAlg h
  obtain ⟨u, hu, -⟩ := h.basis
  obtain ⟨a, ha0, hau⟩ : ∃ a : E, a ≠ 0 ∧ ¬ IsUnit a := by
    by_contra hc
    push Not at hc
    exact hnf ⟨exists_pair_ne E, mul_comm, fun {a} ha => by
      obtain ⟨b, hb⟩ := (hc a ha).exists_right_inv
      exact ⟨b, hb⟩⟩
  have haτ : a * τ a = 0 := by
    by_contra hne
    apply hau
    have hfix : τ (a * τ a) = a * τ a := by rw [map_mul, h.inv, mul_comm]
    exact isUnit_of_mul_isUnit_left (h.fixedUnit _ hfix hne)
  have hw : ∃ w : E, a * w + τ (a * w) ≠ 0 := by
    by_contra hc
    push Not at hc
    have h1 := hc 1
    have h2 := hc u
    rw [mul_one] at h1
    apply ha0
    have h3 : a * (u - τ u) = 0 := by
      rw [map_mul] at h2
      linear_combination h2 - τ u * h1
    exact hu.mul_left_eq_zero.1 h3
  obtain ⟨w, hw⟩ := hw
  have hTfix : τ (a * w + τ (a * w)) = a * w + τ (a * w) := by rw [map_add, h.inv, add_comm]
  obtain ⟨s, hs⟩ := (h.fixedUnit _ hTfix hw).exists_right_inv
  have hsf : τ s = s := fixed_inv hTfix hs
  refine ⟨a * w * s, ?_, ?_⟩
  · rw [map_mul, hsf]
    linear_combination hs
  · rw [map_mul, hsf, map_mul]
    linear_combination (w * τ w * s * s) * haτ
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
