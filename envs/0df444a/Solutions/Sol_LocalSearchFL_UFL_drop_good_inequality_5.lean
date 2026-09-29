-- Prove2me | solution 1 for LocalSearchFL.UFL.drop_good_inequality_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:08:14.746208+00:00
-- url     : https://prove2.me/submissions/af1d9302-56e1-4382-a6ed-e526f6fe0746

import Mathlib
import Definitions.Def_LocalSearchFL_UFL_captures

namespace LocalSearchFL.UFL

theorem aux_dg5_pi_out {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (O : Finset Fa) (σS σO : Cl → Fa) (hσO : ∀ j, σO j ∈ O)
    (π : Equiv.Perm Cl) (hπ : IsRefinedPi σS σO π)
    (s : Fa) (hgood : IsGood σS σO O s) (j : Cl) (hj : σS j = s) : σS (π j) ≠ s := by
  intro h
  have := hπ.2.1 s (σO j) (hgood (σO j) (hσO j)) j (by simp [nbhd, hj])
  apply this
  simp [nbhd, h, hπ.1 j]

end LocalSearchFL.UFL

open LocalSearchFL.UFL

theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [Nonempty Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S O : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (σS σO : Cl → Fa) (hσS : IsNearestAssignment I S σS) (hσO : IsNearestAssignment I O σO)
    (π : Equiv.Perm Cl) (hπ : IsRefinedPi σS σO π)
    (s : Fa) (hs : s ∈ S) (hgood : IsGood σS σO O s) :
    0 ≤ -f s +
      ∑ j ∈ (nbhd σS s).filter (fun j => π j ≠ j),
        (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) - I.c j (σS j)) +
      2 * ∑ j ∈ (nbhd σS s).filter (fun j => π j = j), I.c j (σO j) := by
  have hout : ∀ j, σS j = s → σS (π j) ≠ s := fun j hj =>
    aux_dg5_pi_out O σS σO (fun j => (hσO j).1) π hπ s hgood j hj
  have hne : (S.erase s).Nonempty := by
    obtain ⟨j⟩ := ‹Nonempty Cl›
    by_cases hj : σS j = s
    · exact ⟨σS (π j), Finset.mem_erase.2 ⟨hout j hj, (hσS _).1⟩⟩
    · exact ⟨σS j, Finset.mem_erase.2 ⟨hj, (hσS _).1⟩⟩
  have hdrop := hloc.2.1 s hs hne
  have hfilt1 : (nbhd σS s).filter (fun j => π j ≠ j) = nbhd σS s := by
    apply Finset.filter_true_of_mem
    intro j hj h
    have hj' : σS j = s := by simpa [nbhd] using hj
    exact hout j hj' (by rw [h]; exact hj')
  have hsum2 : 0 ≤ ∑ j ∈ (nbhd σS s).filter (fun j => π j = j), I.c j (σO j) :=
    Finset.sum_nonneg (fun j _ => I.nonneg _ _)
  rw [hfilt1]
  have hcS : costS I S hS = ∑ j, I.c j (σS j) := by
    unfold costS
    apply Finset.sum_congr rfl
    intro j _
    apply le_antisymm
    · exact Finset.inf'_le _ (hσS j).1
    · exact Finset.le_inf' _ _ (fun i hi => (hσS j).2 i hi)
  have hcF : costF f S = f s + costF f (S.erase s) := by
    unfold costF
    rw [Finset.add_sum_erase _ _ hs]
  have hterm : ∀ j, (S.erase s).inf' hne (fun i => I.c j i) - I.c j (σS j) ≤
      if σS j = s then (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j))
        - I.c j (σS j)) else 0 := by
    intro j
    split_ifs with hj
    · have h1 : (S.erase s).inf' hne (fun i => I.c j i) ≤ I.c j (σS (π j)) :=
        Finset.inf'_le _ (Finset.mem_erase.2 ⟨hout j hj, (hσS _).1⟩)
      have h2 : I.c j (σS (π j)) ≤
          I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) := by
        unfold MetricInstance.c
        rw [hπ.1 j]
        have t1 := I.triangle (Sum.inl j) (Sum.inr (σO j)) (Sum.inr (σS (π j)))
        have t2 := I.triangle (Sum.inr (σO j)) (Sum.inl (π j)) (Sum.inr (σS (π j)))
        have t3 := I.symm (Sum.inr (σO j)) (Sum.inl (π j))
        linarith
      linarith
    · have h1 : (S.erase s).inf' hne (fun i => I.c j i) ≤ I.c j (σS j) :=
        Finset.inf'_le _ (Finset.mem_erase.2 ⟨hj, (hσS _).1⟩)
      linarith
  have hsumterm : costS I (S.erase s) hne - costS I S hS ≤
      ∑ j ∈ nbhd σS s, (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j))
        - I.c j (σS j)) := by
    rw [hcS]
    unfold costS
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ j, (if σS j = s then (I.c j (σO j) + I.c (π j) (σO (π j))
            + I.c (π j) (σS (π j)) - I.c j (σS j)) else 0) :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = _ := by
          rw [← Finset.sum_filter]
          rfl
  unfold uflCost at hdrop
  linarith
