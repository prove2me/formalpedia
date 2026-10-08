-- Prove2me | solution 1 for LocalSearchFL.UFL.facility_cost_lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T11:42:10.177272+00:00
-- url     : https://prove2.me/submissions/4b5e8119-a6b0-483e-9312-ea6d0e516542

import Theorems.Thm_LocalSearchFL_UFL_exists_refined_pi
import Theorems.Thm_LocalSearchFL_UFL_drop_good_inequality_5
import Theorems.Thm_LocalSearchFL_UFL_bad_facility_inequality_8

open LocalSearchFL.UFL

private theorem nearest_exists {Cl Fa : Type} (I : MetricInstance Cl Fa)
    (S : Finset Fa) (hS : S.Nonempty) : ∃ σ : Cl → Fa, IsNearestAssignment I S σ := by
  classical
  choose σ hm he using fun j : Cl => Finset.exists_mem_eq_inf' hS (fun i => I.c j i)
  refine ⟨σ, fun j => ⟨hm j, fun i hi => ?_⟩⟩
  rw [← he j]
  exact Finset.inf'_le _ hi

private theorem assigned_cost {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (S : Finset Fa) (hS : S.Nonempty)
    (σ : Cl → Fa) (hσ : IsNearestAssignment I S σ) :
    costS I S hS = ∑ j, I.c j (σ j) := by
  apply Finset.sum_congr rfl
  intro j _
  exact le_antisymm (Finset.inf'_le _ (hσ j).1)
    (Finset.le_inf' _ _ (fun i hi => (hσ j).2 i hi))

private theorem capture_unique {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (s t o : Fa)
    (hs : captures σS σO s o) (ht : captures σS σO t o) : s = t := by
  by_contra hne
  have hd : Disjoint (nbhd σO o ∩ nbhd σS s) (nbhd σO o ∩ nbhd σS t) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have hjs : σS j = s := by simpa [nbhd] using (Finset.mem_inter.mp hj).2
    have hjt : σS j = t := by simpa [nbhd] using (Finset.mem_inter.mp hk).2
    exact hne (hjs.symm.trans hjt)
  have hsub : (nbhd σO o ∩ nbhd σS s) ∪ (nbhd σO o ∩ nbhd σS t) ⊆ nbhd σO o :=
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at hc
  unfold captures at hs ht
  omega

private theorem empty_clients {Cl Fa : Type} [Fintype Cl] [IsEmpty Cl] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (O : Finset Fa) (hO : O.Nonempty) : costF f S ≤ costF f O := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨o, ho⟩ := hO
  by_cases he : S.erase s = ∅
  · have h := hloc.2.2 s hs o
    have hbound : costF f S ≤ f o := by simpa [uflCost, costS, he, costF] using h
    exact hbound.trans (Finset.single_le_sum (fun i _ => hf i) ho)
  · have hne := Finset.nonempty_iff_ne_empty.mpr he
    have hzero : ∀ t ∈ S, f t = 0 := by
      intro t ht
      have hT : (S.erase t).Nonempty := by
        by_cases hts : t = s
        · simpa only [hts] using hne
        · exact ⟨s, Finset.mem_erase.mpr ⟨Ne.symm hts, hs⟩⟩
      have h := hloc.2.1 t ht hT
      have hc : costF f S = f t + costF f (S.erase t) :=
        (Finset.add_sum_erase _ _ ht).symm
      simp only [uflCost, costS, Finset.univ_eq_empty, Finset.sum_empty, add_zero] at h
      linarith [hf t]
    have hsum : costF f S = 0 := Finset.sum_eq_zero hzero
    rw [hsum]
    exact Finset.sum_nonneg (fun i _ => hf i)

theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (O : Finset Fa) (hO : O.Nonempty) :
    costF f S ≤ costF f O + 2 * costS I O hO := by
  classical
  cases isEmpty_or_nonempty Cl with
  | inl hempty =>
    letI := hempty
    simpa [costS] using empty_clients I f hf S hS hloc O hO
  | inr hnonempty =>
    letI := hnonempty
    obtain ⟨σS, hσS⟩ := nearest_exists I S hS
    obtain ⟨σO, hσO⟩ := nearest_exists I O hO
    obtain ⟨π, hπ⟩ := exists_refined_pi σS σO
    let a (j : Cl) := I.c j (σO j)
    let b (j : Cl) := I.c j (σS j)
    let d (j : Cl) := a j + a (π j) + b (π j) - b j
    have hsplit (s : Fa) :
        (∑ j ∈ (nbhd σS s).filter (fun j => π j ≠ j), d j) +
        2 * (∑ j ∈ (nbhd σS s).filter (fun j => π j = j), a j) =
        ∑ j ∈ nbhd σS s, d j := by
      simp only [Finset.sum_filter, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : π j = j
      · simp [hj, d]; ring
      · simp [hj]
    have hpoint : ∀ s ∈ S, f s ≤
        (∑ o ∈ O.filter (fun o => captures σS σO s o), f o) + ∑ j ∈ nbhd σS s, d j := by
      intro s hs
      by_cases hg : IsGood σS σO O s
      · have h := drop_good_inequality_5 I f hf S O hS hloc σS σO hσS hσO π hπ s hs hg
        have he : O.filter (fun o => captures σS σO s o) = ∅ :=
          Finset.filter_eq_empty_iff.mpr (fun o ho => hg o ho)
        rw [he, Finset.sum_empty, zero_add]
        change 0 ≤ -f s + (∑ j ∈ (nbhd σS s).filter (fun j => π j ≠ j), d j) +
          2 * (∑ j ∈ (nbhd σS s).filter (fun j => π j = j), a j) at h
        linarith [hsplit s]
      · have h := bad_facility_inequality_8 I f hf S O hS hloc σS σO hσS hσO π hπ s hs hg
        change 0 ≤ (∑ o ∈ O.filter (fun o => captures σS σO s o), f o) - f s +
          (∑ j ∈ (nbhd σS s).filter (fun j => π j ≠ j), d j) +
          2 * (∑ j ∈ (nbhd σS s).filter (fun j => π j = j), a j) at h
        linarith [hsplit s]
    have hcharged : (∑ s ∈ S, ∑ o ∈ O.filter (fun o => captures σS σO s o), f o) ≤ costF f O := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro o _
      have hc : (S.filter (fun s => captures σS σO s o)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro s hs t ht
        exact capture_unique σS σO s t o (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp ht).2
      have hcr : ((S.filter (fun s => captures σS σO s o)).card : ℝ) ≤ 1 := by exact_mod_cast hc
      calc
        _ = ((S.filter (fun s => captures σS σO s o)).card : ℝ) * f o := by
          rw [← Finset.sum_filter]
          simp [nsmul_eq_mul]
        _ ≤ f o := mul_le_of_le_one_left (hf o) hcr
    have hpartition : (∑ s ∈ S, ∑ j ∈ nbhd σS s, d j) = ∑ j, d j := by
      simp only [nbhd, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp [(hσS j).1]
    have ha : (∑ j, a (π j)) = ∑ j, a j := Equiv.sum_comp π a
    have hb : (∑ j, b (π j)) = ∑ j, b j := Equiv.sum_comp π b
    have htotal : (∑ j, d j) = 2 * costS I O hO := by
      rw [assigned_cost I O hO σO hσO]
      change (∑ j, (a j + a (π j) + b (π j) - b j)) = 2 * ∑ j, a j
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ha, hb]
      ring
    have hsum := Finset.sum_le_sum hpoint
    rw [Finset.sum_add_distrib, hpartition, htotal] at hsum
    change costF f S ≤ _ at hsum
    linarith

#print axioms solution
