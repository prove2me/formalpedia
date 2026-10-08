-- Prove2me | solution 1 for MatousekLP.Scheduling.best_T_le_two_topt
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T05:06:23.380355+00:00
-- url     : https://prove2.me/submissions/aada672c-41bd-42e5-8154-9949b763b55c

import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_MatousekLP_Scheduling_LPRelaxation
import Mathlib

open MatousekLP.Scheduling

namespace SchedAux

lemma load_le_makespan {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    load d σ i ≤ makespan d σ :=
  le_ciSup (Set.finite_range _).bddAbove i

/-- The 0/1 matrix of a schedule is feasible for the relaxation with `T = t = makespan`. -/
lemma schedule_feasible {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (hd : ∀ i j, 0 < d i j)
    (σ : Fin n → Fin m) :
    LPRFeasible d (makespan d σ) (makespan d σ) (fun i j => if σ j = i then 1 else 0) := by
  classical
  refine ⟨fun j => ?_, fun i => ?_, fun i j => by dsimp only; split_ifs <;> norm_num, fun i j hT => ?_⟩
  · simp
  · have : ∑ j, d i j * (if σ j = i then (1 : ℝ) else 0) = load d σ i := by
      simp [load, Finset.sum_filter]
    rw [this]; exact load_le_makespan d σ i
  · by_contra hne
    simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hne
    have h1 : d i j ≤ load d σ i := by
      unfold load
      exact Finset.single_le_sum (f := fun j => d i j) (fun j _ => (hd i j).le)
        (by simp [hne])
    linarith [load_le_makespan d σ i]

end SchedAux


namespace SchedAux2

open SchedAux

/-- For `m ≥ 1`, the relaxation with a feasible `(T, T, x₀)` has an optimum `t* ≤ T`. -/
lemma exists_optimal {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (hd : ∀ i j, 0 < d i j) (hm : 0 < m)
    (T : ℝ) (x₀ : Matrix (Fin m) (Fin n) ℝ) (hx₀ : LPRFeasible d T T x₀) :
    ∃ (t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ), LPROptimal d T t x ∧ t ≤ T := by
  classical
  set K : Set (ℝ × (Fin m → Fin n → ℝ)) :=
    {p | ∀ j, ∑ i, p.2 i j = 1} ∩ {p | ∀ i, ∑ j, d i j * p.2 i j ≤ p.1} ∩
      {p | ∀ i j, 0 ≤ p.2 i j} ∩ {p | ∀ i j, T < d i j → p.2 i j = 0} ∩ {p | p.1 ≤ T}
  have hmemK : ∀ p : ℝ × (Fin m → Fin n → ℝ), p ∈ K ↔ LPRFeasible d T p.1 p.2 ∧ p.1 ≤ T := by
    intro p; simp only [K, Set.mem_inter_iff, Set.mem_setOf_eq, LPRFeasible, and_assoc]
  have hclosed : IsClosed K := by
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_) ?_
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun j => isClosed_eq (by fun_prop) continuous_const
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le (by fun_prop) (by fun_prop)
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le continuous_const (by fun_prop)
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_le (by fun_prop) continuous_const
  have hsub : K ⊆ Set.Icc (0, 0) (T, 1) := by
    intro p hp
    obtain ⟨⟨hcol, hrow, hnn, -⟩, hT⟩ := (hmemK p).mp hp
    refine ⟨⟨?_, fun i j => hnn i j⟩, ⟨hT, fun i j => ?_⟩⟩
    · have := hrow ⟨0, hm⟩
      exact le_trans (Finset.sum_nonneg fun j _ => mul_nonneg (hd _ j).le (hnn _ j)) this
    · show p.2 i j ≤ 1
      rw [← hcol j]
      exact Finset.single_le_sum (f := fun i => p.2 i j) (fun i _ => hnn i j) (Finset.mem_univ i)
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset hclosed hsub
  have hne : K.Nonempty := ⟨(T, x₀), (hmemK _).mpr ⟨hx₀, le_rfl⟩⟩
  obtain ⟨p, hpK, hpmin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
  obtain ⟨hpf, hpT⟩ := (hmemK p).mp hpK
  refine ⟨p.1, p.2, ⟨hpf, fun t' x' hf' => ?_⟩, hpT⟩
  by_cases ht' : t' ≤ T
  · exact hpmin ((hmemK (t', x')).mpr ⟨hf', ht'⟩)
  · linarith

end SchedAux2

open SchedAux SchedAux2 in
theorem solution {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (hd : ∀ i j, 0 < d i j) (σopt : Fin n → Fin m) (hσopt : IsOptimalSchedule d σopt)
    (Tstar tstar : ℝ) (xstar : Matrix (Fin m) (Fin n) ℝ)
    (hopt : LPROptimal d Tstar tstar xstar)
    (hmin : ∀ (T t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ),
      LPROptimal d T t x → tstar + Tstar ≤ t + T) :
    tstar + Tstar ≤ 2 * makespan d σopt := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- with no machines the row constraints are vacuous, so `tstar` cannot be minimal
    subst hm
    obtain ⟨⟨hcol, -, hnn, hz⟩, hmn⟩ := hopt
    have := hmn (tstar - 1) xstar ⟨hcol, fun i => i.elim0, hnn, hz⟩
    linarith
  · obtain ⟨t, x, hoptT, htT⟩ := exists_optimal d hd hm (makespan d σopt) _
      (schedule_feasible d hd σopt)
    have := hmin _ _ _ hoptT
    linarith
