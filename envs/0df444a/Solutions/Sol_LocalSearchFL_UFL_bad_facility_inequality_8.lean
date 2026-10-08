-- Prove2me | solution 1 for LocalSearchFL.UFL.bad_facility_inequality_8
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T11:40:47.368986+00:00
-- url     : https://prove2.me/submissions/0620e1d4-1724-4ced-b71d-cc3d724d1325

import Theorems.Thm_LocalSearchFL_UFL_swap_bad_inequality_6

open LocalSearchFL.UFL

private theorem assigned_cost {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (S : Finset Fa) (hS : S.Nonempty)
    (σ : Cl → Fa) (hσ : IsNearestAssignment I S σ) :
    costS I S hS = ∑ j, I.c j (σ j) := by
  apply Finset.sum_congr rfl
  intro j _
  exact le_antisymm (Finset.inf'_le _ (hσ j).1)
    (Finset.le_inf' _ _ (fun i hi => (hσ j).2 i hi))

private theorem add_subset {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (σS σO : Cl → Fa) (hσS : IsNearestAssignment I S σS)
    (o : Fa) (J : Finset Cl) (hJ : ∀ j ∈ J, σO j = o) :
    0 ≤ f o + ∑ j ∈ J, (I.c j (σO j) - I.c j (σS j)) := by
  let T := insert o S
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  have hpt : ∀ j, T.inf' hT (fun i => I.c j i) - I.c j (σS j) ≤
      if j ∈ J then I.c j (σO j) - I.c j (σS j) else 0 := by
    intro j
    by_cases hj : j ∈ J
    · rw [if_pos hj, hJ j hj]
      exact sub_le_sub_right (Finset.inf'_le _ (Finset.mem_insert_self _ _)) _
    · rw [if_neg hj]
      exact sub_nonpos.mpr (Finset.inf'_le _ (Finset.mem_insert_of_mem (hσS j).1))
  have hservice : costS I T hT - costS I S hS ≤
      ∑ j ∈ J, (I.c j (σO j) - I.c j (σS j)) := by
    rw [assigned_cost I S hS σS hσS]
    unfold costS
    rw [← Finset.sum_sub_distrib]
    simpa only [Finset.sum_ite_mem, Finset.univ_inter] using
      Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpt j)
  have hfacility : costF f T ≤ costF f S + f o := by
    dsimp [T, costF]
    by_cases ho : o ∈ S
    · rw [Finset.insert_eq_of_mem ho]; linarith [hf o]
    · rw [Finset.sum_insert ho]; linarith
  have hl := hloc.1 o
  change costF f S + costS I S hS ≤ costF f T + costS I T hT at hl
  linarith

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
    (s : Fa) (hs : s ∈ S) (hbad : ¬ IsGood σS σO O s) :
    0 ≤ ∑ o' ∈ O.filter (fun o' => captures σS σO s o'), f o' - f s +
      ∑ j ∈ (nbhd σS s).filter (fun j => π j ≠ j),
        (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) - I.c j (σS j)) +
      2 * ∑ j ∈ (nbhd σS s).filter (fun j => π j = j), I.c j (σO j) := by
  classical
  let P := O.filter (fun o' => captures σS σO s o')
  have hP : P.Nonempty := by
    simp only [IsGood, not_forall, not_not] at hbad
    obtain ⟨o, ho, hcap⟩ := hbad
    exact ⟨o, Finset.mem_filter.mpr ⟨ho, hcap⟩⟩
  obtain ⟨o, hoP, hmin⟩ := Finset.exists_mem_eq_inf' hP (fun o' => I.cf s o')
  have hn : ∀ o' ∈ O, captures σS σO s o' → I.cf s o ≤ I.cf s o' := by
    intro o' ho' hc
    rw [← hmin]
    exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨ho', hc⟩)
  have hswap := swap_bad_inequality_6 I f hf S O hS hloc σS σO hσS hσO π hπ s o hs
    (Finset.mem_filter.mp hoP).1 (Finset.mem_filter.mp hoP).2 hn
  let a (j : Cl) := I.c j (σO j)
  let b (j : Cl) := I.c j (σS j)
  let d (j : Cl) := a j + a (π j) + b (π j) - b j
  let M := (nbhd σS s).filter (fun j => π j ≠ j)
  let Q := (nbhd σS s).filter (fun j => π j = j)
  let Q₁ := (nbhd σS s).filter (fun j => π j = j ∧ σO j = o)
  let Q₂ := (nbhd σS s).filter (fun j => π j = j ∧ σO j ≠ o)
  change 0 ≤ f o - f s + (∑ j ∈ M, d j) + (∑ j ∈ Q₁, (a j - b j)) +
    ∑ j ∈ Q₂, (b j + b j + a j - b j) at hswap
  change 0 ≤ (∑ o' ∈ P, f o') - f s + (∑ j ∈ M, d j) + 2 * ∑ j ∈ Q, a j
  have hadd : 0 ≤ ∑ o' ∈ P.erase o,
      (f o' + ∑ j ∈ (nbhd σS s).filter (fun j => π j = j ∧ σO j = o'), (a j - b j)) := by
    apply Finset.sum_nonneg
    intro o' _
    apply add_subset I f hf S hS hloc σS σO hσS o'
    intro j hj
    exact (Finset.mem_filter.mp hj).2.2
  have hfixed : ∀ j ∈ nbhd σS s, π j = j → σO j ∈ P := by
    intro j hj hfix
    have hjs : σS j = s := by simpa [nbhd] using hj
    exact Finset.mem_filter.mpr ⟨(hσO j).1, by
      simpa only [hjs] using fixed_captured σS σO π hπ j hfix⟩
  have hgroups :
      (∑ o' ∈ P.erase o, ∑ j ∈ (nbhd σS s).filter (fun j => π j = j ∧ σO j = o'), (a j - b j)) =
      ∑ j ∈ Q₂, (a j - b j) := by
    simp only [Q₂, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hfix : π j = j
    · have hmem := hfixed j hj hfix
      by_cases hjo : σO j = o
      · simp [hfix, hjo]
      · simp [hfix, hjo, hmem, Finset.sum_ite_eq']
    · simp [hfix]
  rw [Finset.sum_add_distrib, hgroups] at hadd
  have hbound : (∑ j ∈ Q₁, (a j - b j)) +
      (∑ j ∈ Q₂, (b j + b j + a j - b j)) + (∑ j ∈ Q₂, (a j - b j)) ≤
      2 * ∑ j ∈ Q, a j := by
    simp only [Q₁, Q₂, Q, Finset.sum_filter, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases hfix : π j = j
    · by_cases hjo : σO j = o
      · simp [hfix, hjo]
        dsimp [a, b]
        linarith only [show 0 ≤ I.c j (σO j) from I.nonneg _ _,
          show 0 ≤ I.c j (σS j) from I.nonneg _ _]
      · simp [hfix, hjo]; ring_nf; rfl
    · simp [hfix]
  have hfs : f o + ∑ o' ∈ P.erase o, f o' = ∑ o' ∈ P, f o' :=
    Finset.add_sum_erase P f hoP
  linarith

#print axioms solution
