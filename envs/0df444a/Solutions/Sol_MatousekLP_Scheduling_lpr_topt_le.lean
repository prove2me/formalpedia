-- Prove2me | solution 1 for MatousekLP.Scheduling.lpr_topt_le
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T05:05:47.35135+00:00
-- url     : https://prove2.me/submissions/10b1fbf6-0932-4fdb-9fca-83c0432c357f

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

open SchedAux in
theorem solution {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (hd : ∀ i j, 0 < d i j) (σopt : Fin n → Fin m) (hσopt : IsOptimalSchedule d σopt) :
    (∃ (t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ), LPRFeasible d (makespan d σopt) t x) ∧
      ∀ (t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ),
        LPROptimal d (makespan d σopt) t x → t ≤ makespan d σopt :=
  ⟨⟨_, _, schedule_feasible d hd σopt⟩,
    fun _ _ hopt => hopt.2 _ _ (schedule_feasible d hd σopt)⟩
