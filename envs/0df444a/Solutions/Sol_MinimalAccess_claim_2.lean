-- Prove2me | solution 1 for MinimalAccess.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:59:52.233803+00:00
-- url     : https://prove2.me/submissions/b251e1e0-909f-49e3-8d08-bb729a31fd18

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities
import Definitions.Def_MinimalAccess_DeferredAcceptance
import Definitions.Def_MinimalAccess_StudentTypes

set_option autoImplicit false

open GaleShapley1962.Admissions MinimalAccess

namespace MinimalAccess.Claim2Proof

theorem run_permissible {n m : ℕ} (M : Market n m) :
    ∀ k : ℕ,
      (∀ a c, c ∈ (M.run k).remaining a → c ∈ M.permissible a) ∧
      (∀ a c, (M.run k).held a = some c → c ∈ M.permissible a)
  | 0 => ⟨fun _ _ h => h, fun _ _ h => by simp [Market.run, Market.initial] at h⟩
  | k + 1 => by
    obtain ⟨ih_rem, ih_held⟩ := run_permissible M k
    set s := M.run k
    change (∀ a c, c ∈ (M.round s).remaining a → c ∈ M.permissible a) ∧
      (∀ a c, (M.round s).held a = some c → c ∈ M.permissible a)
    unfold Market.round
    split_ifs with hstop
    · exact ⟨ih_rem, ih_held⟩
    · constructor
      · intro a c hc
        dsimp only at hc
        split_ifs at hc with hprop
        · cases hrem : s.remaining a with
          | nil => simp [hrem] at hc
          | cons hd tl =>
            simp only [hrem, List.tail_cons] at hc
            exact ih_rem a c (by simp [hrem, hc])
        · exact ih_rem a c hc
      · intro a c hc
        dsimp only at hc
        have hdec := List.find?_some hc
        have hret : a ∈ M.retained s c := of_decide_eq_true hdec
        unfold Market.retained at hret
        have hmem := List.mem_of_mem_take hret
        have hor : s.held a = some c ∨ s.proposal a = some c :=
          of_decide_eq_true (List.mem_filter.mp hmem).2
        rcases hor with hh | hp
        · exact ih_held a c hh
        · unfold DAState.proposal at hp
          by_cases hnone : s.held a = none
          · rw [if_pos hnone] at hp
            cases hrem : s.remaining a with
            | nil => simp [hrem] at hp
            | cons hd tl =>
              simp only [hrem, List.head?_cons, Option.some.injEq] at hp
              subst hp
              exact ih_rem a hd (by simp [hrem])
          · rw [if_neg hnone] at hp
            cases hp

theorem gamma_acceptable {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) (ℓ : Fin n) (c : Fin m)
    (h : gamma q P pri r ℓ = some c) : Acceptable P ℓ c := by
  let M := toMarket q P (adjKey pri r)
  have hperm : c ∈ M.permissible ℓ := (run_permissible M M.fuel).2 ℓ c h
  have happ : c ∈ applicantList P ℓ := (List.mem_filter.mp hperm).1
  unfold applicantList at happ
  have hfilt := (List.perm_insertionSort _ _).mem_iff.mp happ
  exact of_decide_eq_true (List.mem_filter.mp hfilt).2

theorem ir_acceptable {n m : ℕ} (P : Fin n → Pref m) (ν : Assignment n m)
    (hIR : IsIndividuallyRational P ν) (ℓ : Fin n) (c : Fin m) (h : ν ℓ = some c) :
    Acceptable P ℓ c := by
  have hle := hIR ℓ
  rw [h] at hle
  have hne : P ℓ (some c) ≠ P ℓ none := fun heq => by
    have := (P ℓ).injective heq
    simp at this
  exact lt_of_le_of_ne hle hne

end MinimalAccess.Claim2Proof

open MinimalAccess.Claim2Proof in
theorem solution {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) (μ : Assignment n m) (hIR : IsIndividuallyRational P μ)
    (htb : OneAcceptableWhereDiffer P μ (gamma q P pri r)) (ℓ : Fin n) :
    (IsType1 P μ (gamma q P pri r) ℓ ∨ IsType2 P μ (gamma q P pri r) ℓ ∨
        IsType3 P μ (gamma q P pri r) ℓ) ∧
      ¬ (IsType1 P μ (gamma q P pri r) ℓ ∧ IsType2 P μ (gamma q P pri r) ℓ) ∧
      ¬ (IsType1 P μ (gamma q P pri r) ℓ ∧ IsType3 P μ (gamma q P pri r) ℓ) ∧
      ¬ (IsType2 P μ (gamma q P pri r) ℓ ∧ IsType3 P μ (gamma q P pri r) ℓ) := by
  set γ := gamma q P pri r
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases heq : μ ℓ = γ ℓ
    · exact Or.inr (Or.inr ⟨heq, hIR ℓ⟩)
    · obtain ⟨s, hs_acc, hs_uniq⟩ := htb ℓ heq
      have honly : OnlyAcceptable P ℓ s := fun t =>
        ⟨fun ht => hs_uniq t ht, fun hts => hts ▸ hs_acc⟩
      cases hμ : μ ℓ with
      | none =>
        cases hγ : γ ℓ with
        | none => exact absurd (hμ.trans hγ.symm) heq
        | some c =>
          have hcs : c = s := hs_uniq c (gamma_acceptable q P pri r ℓ c hγ)
          exact Or.inl ⟨⟨s, by rw [hγ, hcs], honly⟩, hμ⟩
      | some c =>
        have hcs : c = s := hs_uniq c (ir_acceptable P μ hIR ℓ c hμ)
        cases hγ : γ ℓ with
        | none =>
          exact Or.inr (Or.inl ⟨⟨s, by rw [hμ, hcs], honly⟩, hγ⟩)
        | some c' =>
          have hc's : c' = s := hs_uniq c' (gamma_acceptable q P pri r ℓ c' hγ)
          rw [hμ, hγ, hcs, hc's] at heq
          exact absurd rfl heq
  · rintro ⟨⟨⟨s, h1, -⟩, -⟩, ⟨-, h2⟩⟩
    rw [h1] at h2
    simp at h2
  · rintro ⟨⟨⟨s, h1, -⟩, h2⟩, ⟨h3, -⟩⟩
    rw [h2, h1] at h3
    simp at h3
  · rintro ⟨⟨⟨s, h1, -⟩, h2⟩, ⟨h3, -⟩⟩
    rw [h1, h2] at h3
    simp at h3
