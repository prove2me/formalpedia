-- Prove2me | solution 1 for LawlerWCT.RhoMax.min_cut_max_weight
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:57:52.93943+00:00
-- url     : https://prove2.me/submissions/52c9dce0-d021-4767-84d4-84bdd95de733

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model
open LawlerWCT.RhoMax

private theorem finite_cut {ι : Type*} [DecidableEq ι] (N : Finset ι)
    (G : ι → ι → Prop) (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (w : ι → ℝ)
    (T : Finset (Node ι)) (hT : T ⊆ nodes N) (ht : Node.t ∈ T) (hs : Node.s ∉ T) :
    cutCapacity N G w T < ⊤ ↔ LawlerWCT.SeriesPar.IsInitialSet G N (jobsOf N T) := by
  classical
  have hcut : cutCapacity N G w T < ⊤ ↔
      ∀ i ∈ N, Node.job i ∉ T → ∀ j ∈ N, Node.job j ∈ T → ¬ G i j := by
    rw [lt_top_iff_ne_top]
    simp only [cutCapacity, WithTop.sum_ne_top]
    constructor
    · intro h i hi hit j hj hjt hg
      have hh := h (.job i) (by simp [nodes, hi, hit]) (.job j) hjt
      simpa [cap, hg] using hh
    · intro h u hu v hv
      have huN := (Finset.mem_sdiff.mp hu).1
      have huT := (Finset.mem_sdiff.mp hu).2
      cases u with
      | s => cases v <;> simp [cap]
      | t => cases v <;> simp [cap]
      | job i =>
        have hi : i ∈ N := by simpa [nodes] using huN
        cases v with
        | s => simp [cap]
        | t => simp [cap]
        | job j =>
          have hj : j ∈ N := by simpa [nodes] using hT hv
          simp [cap, h i hi huT j hj hv]
  rw [hcut]
  constructor
  · intro h
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro j hj i hi hg
    have hjT : Node.job j ∈ T := (Finset.mem_filter.mp hj).2
    have hc : ∀ a b, G a b → Node.job b ∈ T → Node.job a ∈ T := by
      intro a b hab hb
      by_contra ha
      exact h a (hGN a b hab).1 ha b (hGN a b hab).2 hb hab
    have hiT : Node.job i ∈ T := by
      induction hg using Relation.TransGen.head_induction_on with
      | single hab => exact hc _ _ hab hjT
      | head hab hbc ih => exact hc _ _ hab (ih (hGN _ _ hab).2)
    exact Finset.mem_filter.mpr ⟨hi, hiT⟩
  · intro h i hi hit j hj hjt hg
    have hjI : j ∈ jobsOf N T := Finset.mem_filter.mpr ⟨hj, hjt⟩
    have hiI := h.2 j hjI i hi (Relation.TransGen.single hg)
    exact hit (Finset.mem_filter.mp hiI).2




private theorem cut_formula {ι : Type*} [DecidableEq ι] (N : Finset ι)
    (G : ι → ι → Prop) (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (w : ι → ℝ)
    (T : Finset (Node ι)) (hT : T ⊆ nodes N) (ht : Node.t ∈ T) (hs : Node.s ∉ T)
    (hfin : cutCapacity N G w T < ⊤) :
    cutCapacity N G w T =
      ((∑ j ∈ N, max 0 (w j) - ∑ j ∈ jobsOf N T, w j : ℝ) : WithTop ℝ) := by
  classical
  let I := jobsOf N T
  have hi : I ⊆ N := Finset.filter_subset _ _
  have hTi : T = insert Node.t (I.image Node.job) := by
    ext v
    cases v <;> simp [I, jobsOf, ht, hs]
    case job j =>
      intro hj
      simpa [nodes] using hT hj
  have hSi : nodes N \ T = insert Node.s ((N \ I).image Node.job) := by
    ext v
    cases v <;> simp [nodes, I, jobsOf, ht, hs]
    tauto
  have hno : ∀ i ∈ N \ I, ∀ j ∈ I, ¬ G i j := by
    have hf := (WithTop.sum_lt_top.mp hfin)
    intro i hi' j hj hg
    have hiT : Node.job i ∉ T := by
      have hh := (Finset.mem_sdiff.mp hi').2
      simpa [I, jobsOf, (Finset.mem_sdiff.mp hi').1] using hh
    have hjT := (Finset.mem_filter.mp hj).2
    have hh := WithTop.sum_lt_top.mp (hf (.job i) (by simp [nodes, (Finset.mem_sdiff.mp hi').1, hiT])) (.job j) hjT
    simpa [cap, hg] using hh
  have hjinj : Function.Injective (Node.job : ι → Node ι) := by intro a b h; cases h; rfl
  have hc : cutCapacity N G w T =
      ((∑ j ∈ I, max 0 (-w j) : ℝ) : WithTop ℝ) +
      ((∑ j ∈ N \ I, max 0 (w j) : ℝ) : WithTop ℝ) := by
    unfold cutCapacity
    rw [hSi, hTi]
    have hsn : Node.s ∉ (N \ I).image Node.job := by simp
    have htn : Node.t ∉ I.image Node.job := by simp
    simp only [Finset.sum_insert hsn, Finset.sum_insert htn,
      Finset.sum_image (fun a ha b hb h => hjinj h)]
    simp only [cap, Finset.sum_const_zero, add_zero]
    congr 1
    · simp [WithTop.coe_sum]
    · rw [WithTop.coe_sum]
      apply Finset.sum_congr rfl
      intro i hi'
      have hz : ∑ j ∈ I, (if G i j then (⊤ : WithTop ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp [hno i hi' j hj]
      simp [hz]
  rw [hc, ← WithTop.coe_add, WithTop.coe_inj]
  have hsplit := Finset.sum_sdiff hi (f := fun j => max 0 (w j))
  have hneg : ∑ j ∈ I, max 0 (-w j) = ∑ j ∈ I, max 0 (w j) - ∑ j ∈ I, w j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hh : 0 ≤ w j
    · rw [max_eq_left (by linarith), max_eq_right hh]; ring
    · rw [max_eq_right (by linarith), max_eq_left (le_of_not_ge hh)]; ring
  rw [hneg]
  change _ = ∑ j ∈ N, max 0 (w j) - ∑ j ∈ I, w j
  linarith




theorem solution {ι : Type*} [DecidableEq ι] (N : Finset ι)
    (G : ι → ι → Prop) (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (w : ι → ℝ)
    (T : Finset (Node ι)) (hT : T ⊆ nodes N) (ht : Node.t ∈ T) (hs : Node.s ∉ T)
    (hmin : ∀ T' : Finset (Node ι), T' ⊆ nodes N → Node.t ∈ T' → Node.s ∉ T' →
      cutCapacity N G w T ≤ cutCapacity N G w T') :
    LawlerWCT.SeriesPar.IsInitialSet G N (jobsOf N T) ∧
      ∀ I, LawlerWCT.SeriesPar.IsInitialSet G N I → ∑ j ∈ I, w j ≤ ∑ j ∈ jobsOf N T, w j  := by
  classical
  let U : Finset (Node ι) := {Node.t}
  have hU : U ⊆ nodes N := by simp [U, nodes]
  have hUt : Node.t ∈ U := by simp [U]
  have hUs : Node.s ∉ U := by simp [U]
  have hUI : LawlerWCT.SeriesPar.IsInitialSet G N (jobsOf N U) := by
    simp [jobsOf, U, LawlerWCT.SeriesPar.IsInitialSet]
  have hUfin := (finite_cut N G hGN w U hU hUt hUs).2 hUI
  have hfin : cutCapacity N G w T < ⊤ := lt_of_le_of_lt (hmin U hU hUt hUs) hUfin
  have hinit := (finite_cut N G hGN w T hT ht hs).1 hfin
  refine ⟨hinit, ?_⟩
  intro I hI
  let TI := insert Node.t (I.image Node.job)
  have hTI : TI ⊆ nodes N := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp [nodes]
    · rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
      simp [nodes, hI.1 hi]
  have htI : Node.t ∈ TI := by simp [TI]
  have hsI : Node.s ∉ TI := by simp [TI]
  have hjI : jobsOf N TI = I := by
    ext i
    simp [jobsOf, TI]
    exact fun hi => hI.1 hi
  have hIfin := (finite_cut N G hGN w TI hTI htI hsI).2 (hjI ▸ hI)
  have hh := hmin TI hTI htI hsI
  rw [cut_formula N G hGN w T hT ht hs hfin,
    cut_formula N G hGN w TI hTI htI hsI hIfin, hjI, WithTop.coe_le_coe] at hh
  linarith



#print axioms solution
