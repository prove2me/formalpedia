-- Prove2me | solution 1 for LocalSearchFL.KMedian.swap_inequality_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:52:11.586929+00:00
-- url     : https://prove2.me/submissions/00a3ceeb-8b46-4dcf-b619-e7121d99b3b8

import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_captures



namespace LocalSearchFL.KMedian

theorem swi_core {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (S O : Finset Fa) (hS : S.Nonempty)
    (hloc : IsSwapLocalOpt I S hS)
    (σS σO : Cl → Fa) (hσS : IsNearestAssignment I S σS) (hσO : IsNearestAssignment I O σO)
    (π : Equiv.Perm Cl) (hπO : ∀ j, σO (π j) = σO j)
    (hπ : ∀ s o : Fa, ¬ captures σS σO s o →
      ∀ j ∈ nbhd σO o ∩ nbhd σS s, π j ∉ nbhd σO o ∩ nbhd σS s)
    (s o : Fa) (hs : s ∈ S) (ho : o ∈ O)
    (hcap : ∀ o' ∈ O, o' ≠ o → ¬ captures σS σO s o') :
    0 ≤ ∑ j ∈ nbhd σO o, (I.c j (σO j) - I.c j (σS j)) +
      ∑ j ∈ nbhd σS s \ nbhd σO o,
        (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) - I.c j (σS j)) := by
  set S' := insert o (S.erase s) with hS'
  have hS'ne : S'.Nonempty := Finset.insert_nonempty _ _
  -- local optimality against S'
  have hle : kmCost I S hS ≤ kmCost I S' hS'ne := by
    by_cases hoS : o ∈ S
    · unfold kmCost
      apply Finset.sum_le_sum
      intro j _
      apply Finset.le_inf'
      intro i hi
      apply Finset.inf'_le
      rcases Finset.mem_insert.mp hi with h | h
      · rw [h]; exact hoS
      · exact (Finset.mem_erase.mp h).2
    · exact hloc s hs o hoS
  have hcS : kmCost I S hS = ∑ j, I.c j (σS j) := by
    unfold kmCost
    apply Finset.sum_congr rfl
    intro j _
    apply le_antisymm (Finset.inf'_le _ (hσS j).1)
    exact Finset.le_inf' _ _ (fun i hi => (hσS j).2 i hi)
  let A := nbhd σO o
  let B := nbhd σS s
  let T : Cl → ℝ := fun j =>
    I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j))
  let bnd : Cl → ℝ := fun j =>
    if j ∈ A then I.c j (σO j) else if j ∈ B then T j else I.c j (σS j)
  have hcS' : kmCost I S' hS'ne ≤ ∑ j, bnd j := by
    unfold kmCost
    apply Finset.sum_le_sum
    intro j _
    simp only [bnd]
    split_ifs with hA hB
    · have : σO j = o := by simpa [A, nbhd] using hA
      rw [this]; exact Finset.inf'_le _ (Finset.mem_insert_self _ _)
    · have hjs : σS j = s := by simpa [B, nbhd] using hB
      have hne : σO j ≠ o := by simpa [A, nbhd] using hA
      have hπs : σS (π j) ≠ s := by
        intro h
        refine hπ s (σO j) (hcap _ (hσO j).1 hne) j ?_ ?_
        · simp [nbhd, hjs]
        · simp [nbhd, hπO, h]
      have hmem : σS (π j) ∈ S' :=
        Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hπs, (hσS (π j)).1⟩)
      refine le_trans (Finset.inf'_le _ hmem) ?_
      simp only [T, LocalSearchFL.Shared.MetricInstance.c, hπO]
      have t1 := I.triangle (Sum.inl j) (Sum.inr (σO j)) (Sum.inr (σS (π j)))
      have t2 := I.triangle (Sum.inr (σO j)) (Sum.inl (π j)) (Sum.inr (σS (π j)))
      have t3 := I.symm (Sum.inr (σO j)) (Sum.inl (π j))
      linarith
    · have hjs : σS j ≠ s := by simpa [B, nbhd] using hB
      exact Finset.inf'_le _ (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hjs, (hσS j).1⟩))
  have key : 0 ≤ ∑ j, (bnd j - I.c j (σS j)) := by
    rw [Finset.sum_sub_distrib]; linarith
  have hsplit : ∑ j, (bnd j - I.c j (σS j)) =
      ∑ j ∈ A, (I.c j (σO j) - I.c j (σS j)) + ∑ j ∈ B \ A, (T j - I.c j (σS j)) := by
    rw [← Finset.sum_add_sum_compl A]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj; simp [bnd, hj]
    · have : B \ A = (Aᶜ).filter (fun j => j ∈ B) := by
        ext j; simp [and_comm]
      rw [this, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      have hjA : j ∉ A := Finset.mem_compl.mp hj
      by_cases hjB : j ∈ B <;> simp [bnd, hjA, hjB]
  rw [hsplit] at key
  exact key

end LocalSearchFL.KMedian

open LocalSearchFL.KMedian


theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (S O : Finset Fa) (hS : S.Nonempty)
    (hloc : IsSwapLocalOpt I S hS)
    (σS σO : Cl → Fa) (hσS : IsNearestAssignment I S σS) (hσO : IsNearestAssignment I O σO)
    (π : Equiv.Perm Cl) (hπO : ∀ j, σO (π j) = σO j)
    (hπ : ∀ s o : Fa, ¬ captures σS σO s o →
      ∀ j ∈ nbhd σO o ∩ nbhd σS s, π j ∉ nbhd σO o ∩ nbhd σS s)
    (s o : Fa) (hs : s ∈ S) (ho : o ∈ O)
    (hcap : ∀ o' ∈ O, o' ≠ o → ¬ captures σS σO s o') :
    0 ≤ ∑ j ∈ nbhd σO o, (I.c j (σO j) - I.c j (σS j)) +
      ∑ j ∈ nbhd σS s \ nbhd σO o,
        (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) - I.c j (σS j)) := by
  exact swi_core I S O hS hloc σS σO hσS hσO π hπO hπ s o hs ho hcap
