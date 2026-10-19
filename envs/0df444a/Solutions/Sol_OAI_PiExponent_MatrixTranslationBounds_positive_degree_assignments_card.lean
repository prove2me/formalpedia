-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.positive_degree_assignments_card
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T19:13:26.781594+00:00
-- url     : https://prove2.me/submissions/91c395f7-bd12-431f-8e63-3a50ede62be9

import Mathlib.Tactic
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.Option

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ)
    [DecidablePred (fun f : ι → Fin (k + 1) => (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k)] :
    Fintype.card {f : ι → Fin (k + 1) //
      (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k} ≤
      Nat.choose k (Fintype.card ι) := by
  classical
  let A := {f : ι → Fin (k + 1) //
    (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k}
  change Fintype.card A ≤ Nat.choose k (Fintype.card ι)
  by_cases hn : Fintype.card ι ≤ k
  · -- Record the excess above one as multiplicities of the symbols `some i`.
    let encode : A → Sym (Option ι) (k - Fintype.card ι) := fun x =>
      ⟨∑ i, Multiset.replicate ((x.1 i).val - 1) (some i), by
        simp only [Multiset.card_sum, Multiset.card_replicate]
        rw [Finset.sum_tsub_distrib (f := fun i => (x.1 i).val)
          (g := fun _ => (1 : ℕ)) Finset.univ
          (fun i _ => Nat.succ_le_of_lt (x.2.1 i))]
        simp [x.2.2]⟩
    have hcount (x : A) (i : ι) :
        Multiset.count (some i) (encode x).val = (x.1 i).val - 1 := by
      change Multiset.count (some i)
        (∑ j, Multiset.replicate ((x.1 j).val - 1) (some j)) = _
      simp [Multiset.count_sum', Multiset.count_replicate]
    have hinj : Function.Injective encode := by
      intro x y h
      apply Subtype.ext
      funext i
      apply Fin.ext
      have he := congrArg
        (fun s : Sym (Option ι) (k - Fintype.card ι) =>
          Multiset.count (some i) s.val) h
      rw [hcount x i, hcount y i] at he
      have hx := x.2.1 i
      have hy := y.2.1 i
      omega
    calc
      Fintype.card A ≤ Fintype.card (Sym (Option ι) (k - Fintype.card ι)) :=
        Fintype.card_le_of_injective encode hinj
      _ = Nat.choose k (Fintype.card ι) := by
        rw [Sym.card_sym_eq_choose, Fintype.card_option]
        have htop : Fintype.card ι + 1 + (k - Fintype.card ι) - 1 = k := by
          omega
        rw [htop]
        exact Nat.choose_symm hn
  · -- Positivity forces at least one unit of total degree per index.
    haveI : IsEmpty A := ⟨fun x => by
      have hsum : (∑ _i : ι, (1 : ℕ)) ≤ ∑ i, (x.1 i).val :=
        Finset.sum_le_sum (fun i _ => Nat.succ_le_of_lt (x.2.1 i))
      apply hn
      simpa [x.2.2] using hsum⟩
    rw [Fintype.card_eq_zero]
    exact Nat.zero_le _