-- Prove2me | solution 1 for LawlerWCT.RhoMax.cutCapacity_eq
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:50:34.438907+00:00
-- url     : https://prove2.me/submissions/046f4219-31a6-4749-92cc-1d81981670db

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model
open LawlerWCT.RhoMax

theorem solution {ι : Type*} [DecidableEq ι] (N : Finset ι)
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


#print axioms solution
