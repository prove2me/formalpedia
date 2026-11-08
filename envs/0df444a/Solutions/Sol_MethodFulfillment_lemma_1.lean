-- Prove2me | solution 1 for MethodFulfillment.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:51:13.462221+00:00
-- url     : https://prove2.me/submissions/27bb8bb9-17bd-45b1-9890-02e77a7d7961

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_Valid
import Definitions.Def_MethodFulfillment_expOPT
import Definitions.Def_MethodFulfillment_LPFeasible
import Definitions.Def_MethodFulfillment_lpObj

open MethodFulfillment in
theorem solution {I K Q : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    [Fintype Q] [DecidableEq Q] {T : ℕ} (P : Instance I K Q T) (hP : Valid P) :
    ∃ x, LPFeasible P x ∧ lpObj P x ≤ expOPT P := by
  classical
  -- probabilities of arrival sequences
  set Pr : (Fin T → Option Q) → ℝ := fun ω => ∏ t, arrProb P t (ω t) with hPr
  have harr0 : ∀ t o, 0 ≤ arrProb P t o := by
    intro t o
    cases o with
    | none => simp only [arrProb]; linarith [hP.prob_sum_le_one t]
    | some q => exact hP.prob_nonneg t q
  have harr1 : ∀ t, ∑ o, arrProb P t o = 1 := by
    intro t
    rw [Fintype.sum_option]
    simp only [arrProb]
    ring
  have hPr0 : ∀ ω, 0 ≤ Pr ω := fun ω => Finset.prod_nonneg fun t _ => harr0 t (ω t)
  have hprod : ∀ g : Fin T → Option Q → ℝ,
      ∑ ω : Fin T → Option Q, ∏ t, g t (ω t) = ∏ t, ∑ o, g t o := by
    intro g
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have hPr1 : ∑ ω, Pr ω = 1 := by
    rw [hPr]
    simp only
    rw [hprod]
    simp [harr1]
  have hmarg : ∀ t0 q, ∑ ω, Pr ω * (if ω t0 = some q then 1 else 0) = P.p t0 q := by
    intro t0 q
    have h1 : ∀ ω : Fin T → Option Q, Pr ω * (if ω t0 = some q then 1 else 0) =
        ∏ t, (arrProb P t (ω t) * (if t = t0 then (if ω t = some q then 1 else 0) else 1)) := by
      intro ω
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ t0]
      simp [hPr]
    simp only [h1]
    rw [hprod (fun t o => arrProb P t o * (if t = t0 then (if o = some q then 1 else 0) else 1))]
    have h2 : ∀ t, ∑ o, arrProb P t o * (if t = t0 then (if o = some q then 1 else 0) else 1) =
        if t = t0 then P.p t0 q else 1 := by
      intro t
      by_cases ht : t = t0
      · subst ht
        simp only [if_true, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ (some q)]
        simp [arrProb]
      · simp only [ht, if_false, mul_one]
        exact harr1 t
    simp only [h2]
    rw [Finset.prod_ite_eq' Finset.univ t0]
    simp
  -- optimal plans
  have hfeas0 : ∀ ω, PlanFeasible P ω (fun _ => ∅) := by
    intro ω
    refine ⟨fun _ _ => rfl, fun t q _ => hP.discard_mem q, fun i k => ?_⟩
    simp
  have hex : ∀ ω, ∃ a, PlanFeasible P ω a ∧
      ∀ a', PlanFeasible P ω a' → offCost P ω a ≤ offCost P ω a' := by
    intro ω
    obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (PlanFeasible P ω))
      (offCost P ω) ⟨fun _ => ∅, by simp [hfeas0 ω]⟩
    refine ⟨a, (Finset.mem_filter.mp ha).2, fun a' ha' => hmin a' ?_⟩
    simp [ha']
  choose A hA hAmin using hex
  have hOPT : ∀ ω, OPT P ω = offCost P ω (A ω) := by
    intro ω
    unfold OPT
    apply IsLeast.csInf_eq
    refine ⟨⟨A ω, hA ω, rfl⟩, ?_⟩
    rintro v ⟨a', ha', rfl⟩
    exact hAmin ω a' ha'
  -- counts
  set cnt : (Fin T → Option Q) → Q → Finset (I × K) → ℝ := fun ω q m =>
    ∑ t, (if ω t = some q ∧ A ω t = m then (1 : ℝ) else 0) with hcnt
  have hsplit : ∀ ω q (M : Finset (Finset (I × K))),
      ∑ m ∈ M, cnt ω q m = ∑ t, (if ω t = some q then (if A ω t ∈ M then (1 : ℝ) else 0) else 0) := by
    intro ω q M
    rw [hcnt]
    simp only
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : ω t = some q
    · simp only [h, true_and, if_true]
      rw [Finset.sum_ite_eq]
    · simp [h]
  have hL1 : ∀ ω q, ∑ m ∈ P.methods q, cnt ω q m = ∑ t, (if ω t = some q then (1 : ℝ) else 0) := by
    intro ω q
    rw [hsplit]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : ω t = some q
    · rw [if_pos h, if_pos h, if_pos ((hA ω).2.1 t q h)]
    · rw [if_neg h, if_neg h]
  have hL2 : ∀ ω i k, ∑ q, ∑ m ∈ (P.methods q).filter (fun m => (i, k) ∈ m), cnt ω q m ≤ P.S i k := by
    intro ω i k
    simp only [hsplit]
    rw [Finset.sum_comm]
    have hle : ∀ t, ∑ q, (if ω t = some q then
        (if A ω t ∈ (P.methods q).filter (fun m => (i, k) ∈ m) then (1 : ℝ) else 0) else 0) ≤
        if (i, k) ∈ A ω t then 1 else 0 := by
      intro t
      cases hωt : ω t with
      | none =>
        simp
        split_ifs <;> norm_num
      | some q0 =>
        simp only [Option.some.injEq]
        rw [Finset.sum_ite_eq Finset.univ q0]
        rw [if_pos (Finset.mem_univ q0)]
        by_cases hm : (i, k) ∈ A ω t
        · rw [if_pos hm]
          split_ifs <;> norm_num
        · rw [if_neg hm, if_neg]
          simp [Finset.mem_filter, hm]
    calc ∑ t, ∑ q, (if ω t = some q then
          (if A ω t ∈ (P.methods q).filter (fun m => (i, k) ∈ m) then (1 : ℝ) else 0) else 0)
        ≤ ∑ t, (if (i, k) ∈ A ω t then (1 : ℝ) else 0) := Finset.sum_le_sum fun t _ => hle t
      _ = ((Finset.univ.filter fun t => (i, k) ∈ A ω t).card : ℝ) := by
        rw [Finset.sum_boole]
      _ ≤ P.S i k := by exact_mod_cast (hA ω).2.2 i k
  have hL3 : ∀ ω, ∑ q, ∑ m ∈ P.methods q, P.c q m * cnt ω q m = offCost P ω (A ω) := by
    intro ω
    unfold offCost
    rw [hcnt]
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun q _ => Finset.sum_comm), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    cases hωt : ω t with
    | none => simp
    | some q0 =>
      simp only [Option.some.injEq]
      rw [Finset.sum_eq_single q0]
      · simp only [true_and, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq, if_pos ((hA ω).2.1 t q0 hωt)]
      · intro q _ hq
        apply Finset.sum_eq_zero
        intro m _
        rw [if_neg (fun h => hq h.1.symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ q0) h
  refine ⟨fun q m => ∑ ω, Pr ω * cnt ω q m, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro q m _
    exact Finset.sum_nonneg fun ω _ => mul_nonneg (hPr0 ω)
      (Finset.sum_nonneg fun t _ => by split_ifs <;> norm_num)
  · intro q
    show ∑ m ∈ P.methods q, ∑ ω, Pr ω * cnt ω q m = pa P q
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hL1]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold pa
    apply Finset.sum_congr rfl
    intro t _
    exact hmarg t q
  · intro i k
    show ∑ q, ∑ m ∈ (P.methods q).filter (fun m => (i, k) ∈ m), ∑ ω, Pr ω * cnt ω q m ≤ P.S i k
    rw [Finset.sum_congr rfl (fun q _ => Finset.sum_comm), Finset.sum_comm]
    calc ∑ ω, ∑ q, ∑ m ∈ (P.methods q).filter (fun m => (i, k) ∈ m), Pr ω * cnt ω q m
        ≤ ∑ ω, Pr ω * (P.S i k : ℝ) := by
          apply Finset.sum_le_sum
          intro ω _
          simp only [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (hL2 ω i k) (hPr0 ω)
      _ = P.S i k := by rw [← Finset.sum_mul, hPr1, one_mul]
  · apply le_of_eq
    unfold lpObj expOPT
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun q _ => Finset.sum_comm), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω _
    rw [hOPT ω, ← hL3 ω]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro m _
    rw [hPr]
    ring
