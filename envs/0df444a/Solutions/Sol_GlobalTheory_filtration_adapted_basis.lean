-- Prove2me | solution 1 for GlobalTheory.filtration_adapted_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:54.924595+00:00
-- url     : https://prove2.me/submissions/bf434e82-242b-4726-a35a-824c6322a128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AntitoneFiltrationExistsAdaptedLinearIndepSet
import Theorems.Thm_GlobalTheory_antitone_filtration_exists_adapted_linearIndep_set

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Submodule
namespace GlobalTheory
theorem _root_.solution {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (A : ℤ → Submodule L M) (hA : Antitone A) (hfd : FiniteDimensional L ↥(⨆ a, A a))
    (hsep : ∀ x, (∀ a, x ∈ A a) → x = 0) :
    ∃ (m : ℕ) (d : Fin m → M) (k : Fin m → ℤ), LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {i | a ≤ k i}) := by
  classical
  have hle : ∀ a, A a ≤ ⨆ b, A b := fun a => le_iSup A a
  have hfa : ∀ a, FiniteDimensional L (A a) := fun a => Submodule.finiteDimensional_of_le (hle a)
  obtain ⟨a0, ha0⟩ : ∃ a0, ∀ a, Module.finrank L (A a0) ≤ Module.finrank L (A a) := by
    have hex : ∃ m, ∃ a, Module.finrank L (A a) = m := ⟨_, 0, rfl⟩
    obtain ⟨a0, h0⟩ := Nat.find_spec hex
    refine ⟨a0, fun a => ?_⟩
    have h := Nat.find_min' hex ⟨a, rfl⟩
    rw [← h0] at h
    exact h
  have hbot : A a0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply hsep
    intro a
    rcases le_total a a0 with h | h
    · exact hA h hx
    · rw [Submodule.eq_of_le_of_finrank_le (hA h) (ha0 a)]
      exact hx
  obtain ⟨a1, ha1⟩ : ∃ a1, ∀ a, Module.finrank L (A a) ≤ Module.finrank L (A a1) := by
    have hex : ∃ m, ∃ a, Module.finrank L ↥(⨆ b, A b) - Module.finrank L (A a) = m := ⟨_, 0, rfl⟩
    obtain ⟨a1, h1⟩ := Nat.find_spec hex
    refine ⟨a1, fun a => ?_⟩
    have h2 := Nat.find_min' hex ⟨a, rfl⟩
    rw [← h1] at h2
    have h3 := Submodule.finrank_mono (hle a)
    have h4 := Submodule.finrank_mono (hle a1)
    omega
  have htop : ⨆ b, A b = A a1 := by
    refine le_antisymm (iSup_le fun a => ?_) (hle a1)
    rcases le_total a1 a with h | h
    · exact hA h
    · exact (Submodule.eq_of_le_of_finrank_le (hA h) (ha1 a)).symm.le
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a0 - n ≤ a1 := ⟨(a0 - a1).toNat, by omega⟩
  obtain ⟨s, k, hs, hk, hspan⟩ := antitone_filtration_exists_adapted_linearIndep_set A hA a0 hbot n
  have hlow : ∀ a, a ≤ a0 - n → A a = A (a0 - n) := by
    intro a ha
    refine le_antisymm ?_ (hA ha)
    calc A a ≤ ⨆ c, A c := hle a
      _ = A a1 := htop
      _ ≤ A (a0 - n) := hA hn
  have hsU : ∀ x ∈ s, x ∈ (⨆ b, A b : Submodule L M) := by
    intro x hx
    have hx' : x ∈ A (a0 - n) := by
      rw [hspan _ le_rfl]
      exact Submodule.subset_span ⟨hx, hk x hx⟩
    exact hle _ hx'
  have hli : LinearIndependent L (fun x : s => (⟨x, hsU x x.2⟩ : (⨆ b, A b : Submodule L M))) :=
    LinearIndependent.of_comp (⨆ b, A b).subtype hs
  have hfin : s.Finite := Set.finite_coe_iff.1 hli.finite
  have _ := hfin.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => (e.symm i : M), fun i => k (e.symm i),
    LinearIndependent.comp hs e.symm e.symm.injective, fun a => ?_⟩
  show A a = Submodule.span L ((fun i => (e.symm i : M)) '' {i | a ≤ k (e.symm i)})
  have himg : (fun i => (e.symm i : M)) '' {i | a ≤ k (e.symm i)} = {x | x ∈ s ∧ a ≤ k x} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(e.symm i).2, hi⟩
    · rintro ⟨hx, hkx⟩
      exact ⟨e ⟨x, hx⟩, by simpa using hkx, by simp⟩
  rw [himg]
  rcases le_or_gt (a0 - n) a with h | h
  · exact hspan a h
  · rw [hlow a h.le, hspan _ le_rfl]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, -⟩
      exact ⟨hx, by have := hk x hx; omega⟩
    · rintro ⟨hx, -⟩
      exact ⟨hx, hk x hx⟩
end GlobalTheory
