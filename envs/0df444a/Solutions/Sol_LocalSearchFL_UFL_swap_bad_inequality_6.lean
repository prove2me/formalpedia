-- Prove2me | solution 1 for LocalSearchFL.UFL.swap_bad_inequality_6
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T11:34:45.201988+00:00
-- url     : https://prove2.me/submissions/e078f080-2f75-499f-a89e-9260944bbdcb

import Definitions.Def_LocalSearchFL_UFL_captures

open LocalSearchFL.UFL

private theorem assigned_cost {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (S : Finset Fa) (hS : S.Nonempty)
    (σ : Cl → Fa) (hσ : IsNearestAssignment I S σ) :
    costS I S hS = ∑ j, I.c j (σ j) := by
  apply Finset.sum_congr rfl
  intro j _
  exact le_antisymm (Finset.inf'_le _ (hσ j).1)
    (Finset.le_inf' _ _ (fun i hi => (hσ j).2 i hi))

private theorem same_block_fixed {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (π : Equiv.Perm Cl) (hπ : IsRefinedPi σS σO π)
    (j : Cl) (heq : σS (π j) = σS j) : π j = j := by
  have hj : j ∈ nbhd σO (σO j) ∩ nbhd σS (σS j) := by simp [nbhd]
  have hp : π j ∈ nbhd σO (σO j) ∩ nbhd σS (σS j) := by simp [nbhd, hπ.1 j, heq]
  by_cases hc : captures σS σO (σS j) (σO j)
  · exact hπ.2.2 _ _ hc j hj hp
  · exact False.elim (hπ.2.1 _ _ hc j hj hp)

private theorem fixed_captured {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (π : Equiv.Perm Cl) (hπ : IsRefinedPi σS σO π)
    (j : Cl) (heq : π j = j) : captures σS σO (σS j) (σO j) := by
  by_contra hc
  have hj : j ∈ nbhd σO (σO j) ∩ nbhd σS (σS j) := by simp [nbhd]
  exact hπ.2.1 _ _ hc j hj (by simpa only [heq] using hj)

theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S O : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (σS σO : Cl → Fa) (hσS : IsNearestAssignment I S σS) (hσO : IsNearestAssignment I O σO)
    (π : Equiv.Perm Cl) (hπ : IsRefinedPi σS σO π)
    (s o : Fa) (hs : s ∈ S) (ho : o ∈ O) (hcap : captures σS σO s o)
    (hnearest : ∀ o' ∈ O, captures σS σO s o' → I.cf s o ≤ I.cf s o') :
    0 ≤ f o - f s +
      ∑ j ∈ (nbhd σS s).filter (fun j => π j ≠ j),
        (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) - I.c j (σS j)) +
      ∑ j ∈ (nbhd σS s).filter (fun j => π j = j ∧ σO j = o),
        (I.c j (σO j) - I.c j (σS j)) +
      ∑ j ∈ (nbhd σS s).filter (fun j => π j = j ∧ σO j ≠ o),
        (I.c j (σS j) + I.c j (σS j) + I.c j (σO j) - I.c j (σS j)) := by
  classical
  let T := insert o (S.erase s)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  let d (j : Cl) :=
    (if σS j = s ∧ π j ≠ j then
      I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) - I.c j (σS j) else 0) +
    (if σS j = s ∧ π j = j ∧ σO j = o then I.c j (σO j) - I.c j (σS j) else 0) +
    (if σS j = s ∧ π j = j ∧ σO j ≠ o then
      I.c j (σS j) + I.c j (σS j) + I.c j (σO j) - I.c j (σS j) else 0)
  have hpoint : ∀ j, T.inf' hT (fun i => I.c j i) - I.c j (σS j) ≤ d j := by
    intro j
    by_cases hjs : σS j = s
    · by_cases hfix : π j = j
      · have hio : T.inf' hT (fun i => I.c j i) ≤ I.c j o :=
          Finset.inf'_le _ (Finset.mem_insert_self _ _)
        by_cases hjo : σO j = o
        · simpa [d, hjs, hfix, hjo] using sub_le_sub_right hio (I.c j (σS j))
        · have hc : captures σS σO s (σO j) := by
            simpa only [hjs] using fixed_captured σS σO π hπ j hfix
          have hn := hnearest (σO j) (hσO j).1 hc
          have h1 : I.c j o ≤ I.c j s + I.cf s o :=
            I.triangle (Sum.inl j) (Sum.inr s) (Sum.inr o)
          have h2 : I.cf s (σO j) ≤ I.c j s + I.c j (σO j) := by
            have ht := I.triangle (Sum.inr s) (Sum.inl j) (Sum.inr (σO j))
            have he := I.symm (Sum.inr s) (Sum.inl j)
            dsimp [MetricInstance.c, MetricInstance.cf]
            linarith
          have hb : T.inf' hT (fun i => I.c j i) - I.c j (σS j) ≤
              I.c j (σS j) + I.c j (σS j) + I.c j (σO j) - I.c j (σS j) := by
            rw [hjs]
            linarith
          simpa [d, hjs, hfix, hjo] using hb
      · have hout : σS (π j) ≠ s := by
          intro he
          exact hfix (same_block_fixed σS σO π hπ j (he.trans hjs.symm))
        have hi : T.inf' hT (fun i => I.c j i) ≤ I.c j (σS (π j)) :=
          Finset.inf'_le _ (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hout, (hσS _).1⟩))
        have hp : I.c j (σS (π j)) ≤ I.c j (σO j) +
            I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) := by
          unfold MetricInstance.c
          rw [hπ.1 j]
          have h1 := I.triangle (Sum.inl j) (Sum.inr (σO j)) (Sum.inr (σS (π j)))
          have h2 := I.triangle (Sum.inr (σO j)) (Sum.inl (π j)) (Sum.inr (σS (π j)))
          have h3 := I.symm (Sum.inr (σO j)) (Sum.inl (π j))
          linarith
        simpa [d, hjs, hfix] using sub_le_sub_right (hi.trans hp) (I.c j (σS j))
    · have hi : T.inf' hT (fun i => I.c j i) ≤ I.c j (σS j) :=
        Finset.inf'_le _ (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hjs, (hσS j).1⟩))
      simpa [d, hjs] using sub_nonpos.mpr hi
  have hservice : costS I T hT - costS I S hS ≤ ∑ j, d j := by
    rw [assigned_cost I S hS σS hσS]
    unfold costS
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun j _ => hpoint j)
  have hfacility : costF f T ≤ costF f S + f o - f s := by
    have he : costF f S = f s + costF f (S.erase s) := by
      exact (Finset.add_sum_erase _ _ hs).symm
    have hi : costF f T ≤ costF f (S.erase s) + f o := by
      dsimp [costF, T]
      by_cases ho : o ∈ S.erase s
      · rw [Finset.insert_eq_of_mem ho]; linarith [hf o]
      · rw [Finset.sum_insert ho]; linarith
    linarith
  have hlocal := hloc.2.2 s hs o
  change costF f S + costS I S hS ≤ costF f T + costS I T hT at hlocal
  have h : 0 ≤ f o - f s + ∑ j, d j := by linarith
  have hsumEq : ∑ j, d j =
      (∑ j ∈ (nbhd σS s).filter (fun j => π j ≠ j),
        (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) - I.c j (σS j))) +
      (∑ j ∈ (nbhd σS s).filter (fun j => π j = j ∧ σO j = o),
        (I.c j (σO j) - I.c j (σS j))) +
      ∑ j ∈ (nbhd σS s).filter (fun j => π j = j ∧ σO j ≠ o),
        (I.c j (σS j) + I.c j (σS j) + I.c j (σO j) - I.c j (σS j)) := by
    dsimp only [d]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [nbhd, Finset.sum_filter, ite_and]
  rw [hsumEq] at h
  linarith

#print axioms solution
