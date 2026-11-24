-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LinAlg.exists_common_eigenvector_in_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:34.702858+00:00
-- url     : https://prove2.me/submissions/250d9f28-b98e-4555-8ac7-7b14419b175d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsJointEigenvectorNonzero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LinAlg
open Module
namespace GlobalTheory.CompanionTheory.LinAlg
theorem _root_.solution {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {ι : Type} (H : ι → End ℂ W)
    (hc : ∀ i i', Commute (H i) (H i')) :
    ∀ (n : ℕ) (U : Submodule ℂ W), finrank ℂ U ≤ n → U ≠ ⊥ →
      (∀ i, ∀ x ∈ U, H i x ∈ U) →
      ∃ v ∈ U, v ≠ 0 ∧ ∃ χ : ι → ℂ, ∀ i, H i v = χ i • v := by
  intro n
  induction n with
  | zero =>
    intro U hU hne _
    exact absurd (Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hU)) hne
  | succ n ih =>
    intro U hU hne hinv
    by_cases hs : ∀ i, ∃ a : ℂ, ∀ x ∈ U, H i x = a • x
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      choose χ hχ using hs
      exact ⟨v, hv, hv0, χ, fun i => hχ i v hv⟩
    · push_neg at hs
      obtain ⟨i, hi⟩ := hs
      haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne
      let R : End ℂ U := (H i).restrict (hinv i)
      obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue R
      obtain ⟨⟨w, hwU⟩, hw⟩ := ha.exists_hasEigenvector
      have hw' : H i w = a • w := by
        have h1 := congrArg Subtype.val hw.apply_eq_smul
        simpa [R] using h1
      have hw0 : w ≠ 0 := by
        intro h
        exact hw.2 (Subtype.ext h)
      have hmem : ∀ {x : W}, x ∈ End.eigenspace (H i) a ↔ H i x = a • x := by
        intro x
        exact End.mem_eigenspace_iff
      have hU'ne : U ⊓ End.eigenspace (H i) a ≠ ⊥ := by
        intro h
        have : w ∈ U ⊓ End.eigenspace (H i) a := ⟨hwU, hmem.mpr hw'⟩
        rw [h] at this
        exact hw0 ((Submodule.mem_bot ℂ).mp this)
      have hlt : U ⊓ End.eigenspace (H i) a < U := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro h
        obtain ⟨x, hx, hne'⟩ := hi a
        have : x ∈ U ⊓ End.eigenspace (H i) a := by rw [h]; exact hx
        exact hne' (hmem.mp this.2)
      have hfr := Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨v, hv, hv0, χ, hχ⟩ := ih (U ⊓ End.eigenspace (H i) a) (by omega) hU'ne (by
        intro k x hx
        refine ⟨hinv k x hx.1, hmem.mpr ?_⟩
        have h2 : H i x = a • x := hmem.mp hx.2
        have h3 : H i (H k x) = H k (H i x) := by
          have := congrArg (fun f : End ℂ W => f x) (hc i k).eq
          simpa using this
        rw [h3, h2, map_smul])
      exact ⟨v, hv.1, hv0, χ, hχ⟩
end GlobalTheory.CompanionTheory.LinAlg
