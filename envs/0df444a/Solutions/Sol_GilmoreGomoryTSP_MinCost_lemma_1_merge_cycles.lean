-- Prove2me | solution 1 for GilmoreGomoryTSP.MinCost.lemma_1_merge_cycles
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:34:36.773832+00:00
-- url     : https://prove2.me/submissions/42102220-05bf-46f9-8336-7f261a747b16

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate



namespace GilmoreGomoryTSP.MinCost

variable {n : ℕ}

lemma l1_pow_eq (ψ : Equiv.Perm (Fin (n+1))) (i j : Fin (n+1)) :
    ∀ (m : ℕ) (x : Fin (n+1)), (∀ s < m, (ψ^s) x ≠ i ∧ (ψ^s) x ≠ j) →
      ((ψ * alpha i j)^m) x = (ψ^m) x := by
  intro m
  induction m with
  | zero => intros; simp
  | succ m ih =>
    intro x h
    have h0 := h 0 (Nat.succ_pos m)
    simp only [pow_zero, Equiv.Perm.one_apply] at h0
    have hs : (ψ * alpha i j) x = ψ x := by
      simp only [alpha, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne h0.1 h0.2]
    have e1 : ((ψ * alpha i j)^(m+1)) x = ((ψ * alpha i j)^m) ((ψ * alpha i j) x) := by
      rw [pow_succ]; rfl
    have e2 : (ψ^(m+1)) x = (ψ^m) (ψ x) := by rw [pow_succ]; rfl
    rw [e1, e2, hs]
    apply ih
    intro s hsm
    have e : (ψ^s) (ψ x) = (ψ^(s+1)) x := by rw [pow_succ]; rfl
    rw [e]
    exact h (s+1) (by omega)

lemma l1_reach (ψ : Equiv.Perm (Fin (n+1))) (i j : Fin (n+1)) (hij : ¬ ψ.SameCycle i j)
    (x : Fin (n+1)) (hx : ψ.SameCycle i x) : (ψ * alpha i j).SameCycle x i := by
  classical
  by_cases hxi : x = i
  · subst hxi; exact Equiv.Perm.SameCycle.refl _ _
  have hex : ∃ m : ℕ, (ψ^m) x = i := hx.symm.exists_nat_pow_eq
  let m := Nat.find hex
  have hm : (ψ^m) x = i := Nat.find_spec hex
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; apply hxi; have := hm; rw [h0] at this; simpa using this
    · exact h0
  have hcond : ∀ s < m, (ψ^s) x ≠ i ∧ (ψ^s) x ≠ j := by
    intro s hs
    refine ⟨Nat.find_min hex hs, ?_⟩
    intro hsj
    apply hij
    have h1 : ψ.SameCycle x j := ⟨(s : ℤ), by simpa [zpow_natCast] using hsj⟩
    exact hx.trans h1
  have := l1_pow_eq ψ i j m x hcond
  refine ⟨(m : ℤ), ?_⟩
  rw [zpow_natCast, this, hm]

lemma l1_main {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1))
    (hij : ¬ ψ.SameCycle i j) (k l : Fin (n + 1)) :
    (ψ * alpha i j).SameCycle k l ↔
      ψ.SameCycle k l ∨ (ψ.SameCycle k i ∧ ψ.SameCycle l j) ∨
        (ψ.SameCycle k j ∧ ψ.SameCycle l i) := by
  classical
  set σ := ψ * alpha i j with hσ
  let U : Fin (n+1) → Prop := fun x => ψ.SameCycle i x ∨ ψ.SameCycle j x
  have hUcl : ∀ a b, ψ.SameCycle a b → U b → U a := by
    intro a b hab hb
    rcases hb with h | h
    · exact Or.inl (h.trans hab.symm)
    · exact Or.inr (h.trans hab.symm)
  have hUcl' : ∀ a b, ψ.SameCycle a b → U a → U b := by
    intro a b hab ha
    exact hUcl b a hab.symm ha
  have hji : ¬ ψ.SameCycle j i := fun h => hij h.symm
  have hσ' : σ = ψ * alpha j i := by
    simp only [hσ, alpha, Equiv.swap_comm]
  -- reach i
  have hreach_i : ∀ x, ψ.SameCycle i x → σ.SameCycle x i := fun x hx => l1_reach ψ i j hij x hx
  have hreach_j : ∀ x, ψ.SameCycle j x → σ.SameCycle x j := by
    intro x hx
    rw [hσ']
    exact l1_reach ψ j i hji x hx
  have hσi : σ i = ψ j := by
    simp [hσ, alpha]
  have hσj : σ j = ψ i := by
    simp [hσ, alpha]
  have hji_σ : σ.SameCycle j i := by
    have h1 : σ.SameCycle i (ψ j) := ⟨1, by simp [hσi]⟩
    have h2 : σ.SameCycle (ψ j) j := hreach_j _ (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))
    exact (h1.trans h2).symm
  have hreachU : ∀ x, U x → σ.SameCycle x i := by
    intro x hx
    rcases hx with h | h
    · exact hreach_i x h
    · exact (hreach_j x h).trans hji_σ
  have hstep : ∀ x, ψ.SameCycle x (σ x) ∨ (U x ∧ U (σ x)) := by
    intro x
    by_cases hxi : x = i
    · subst hxi
      right
      refine ⟨Or.inl (Equiv.Perm.SameCycle.refl _ _), ?_⟩
      rw [hσi]
      exact Or.inr (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))
    by_cases hxj : x = j
    · subst hxj
      right
      refine ⟨Or.inr (Equiv.Perm.SameCycle.refl _ _), ?_⟩
      rw [hσj]
      exact Or.inl (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))
    · left
      have : σ x = ψ x := by
        simp only [hσ, alpha, Equiv.Perm.mul_apply]
        rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
      rw [this]
      exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  have key : σ.SameCycle k l ↔ ψ.SameCycle k l ∨ (U k ∧ U l) := by
    constructor
    · intro h
      obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
      have : ∀ m : ℕ, ψ.SameCycle k ((σ^m) k) ∨ (U k ∧ U ((σ^m) k)) := by
        intro m
        induction m with
        | zero => left; simpa using Equiv.Perm.SameCycle.refl ψ k
        | succ m ih =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          set y := (σ^m) k
          rcases hstep y with h1 | h1
          · rcases ih with h2 | h2
            · left; exact h2.trans h1
            · right; exact ⟨h2.1, hUcl' _ _ h1 h2.2⟩
          · rcases ih with h2 | h2
            · right; exact ⟨hUcl _ _ h2 h1.1, h1.2⟩
            · right; exact ⟨h2.1, h1.2⟩
      rw [← hm]
      exact this m
    · intro h
      rcases h with h | h
      · by_cases hk : U k
        · exact (hreachU k hk).trans (hreachU l (hUcl' _ _ h hk)).symm
        · obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
          have hc : ∀ s < m, (ψ^s) k ≠ i ∧ (ψ^s) k ≠ j := by
            intro s _
            constructor
            · intro hs; apply hk; left
              exact ⟨-(s:ℤ), by rw [zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq]; exact hs.symm⟩
            · intro hs; apply hk; right
              exact ⟨-(s:ℤ), by rw [zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq]; exact hs.symm⟩
          have := l1_pow_eq ψ i j m k hc
          exact ⟨(m : ℤ), by rw [zpow_natCast, hσ, this, hm]⟩
      · exact (hreachU k h.1).trans (hreachU l h.2).symm
  rw [key]
  constructor
  · rintro (h | ⟨hk, hl⟩)
    · exact Or.inl h
    · rcases hk with hk | hk <;> rcases hl with hl | hl
      · exact Or.inl (hk.symm.trans hl)
      · exact Or.inr (Or.inl ⟨hk.symm, hl.symm⟩)
      · exact Or.inr (Or.inr ⟨hk.symm, hl.symm⟩)
      · exact Or.inl (hk.symm.trans hl)
  · rintro (h | ⟨hk, hl⟩ | ⟨hk, hl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl hk.symm, Or.inr hl.symm⟩
    · exact Or.inr ⟨Or.inr hk.symm, Or.inl hl.symm⟩

theorem lemma_1_core {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1))
    (hij : ¬ ψ.SameCycle i j) (k l : Fin (n + 1)) :
    (ψ * alpha i j).SameCycle k l ↔
      ψ.SameCycle k l ∨ (ψ.SameCycle k i ∧ ψ.SameCycle l j) ∨
        (ψ.SameCycle k j ∧ ψ.SameCycle l i) := l1_main ψ i j hij k l

end GilmoreGomoryTSP.MinCost

open GilmoreGomoryTSP.MinCost


theorem solution {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1))
    (hij : ¬ ψ.SameCycle i j) (k l : Fin (n + 1)) :
    (ψ * alpha i j).SameCycle k l ↔
      ψ.SameCycle k l ∨ (ψ.SameCycle k i ∧ ψ.SameCycle l j) ∨
        (ψ.SameCycle k j ∧ ψ.SameCycle l i) := by
  exact lemma_1_core ψ i j hij k l
