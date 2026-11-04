-- Prove2me | solution 1 for KarlinDynamicProgramming.Uniqueness.bellman_solution_eq_optimal_return
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T02:16:07.924729+00:00
-- url     : https://prove2.me/submissions/23309df8-0b47-4a5a-8a6f-0f2754b25c59

import Mathlib
import Definitions.Def_KarlinDynamicProgramming_Uniqueness_CandidateSolutions

set_option autoImplicit false

open Filter

namespace KarlinDPUniqSol

open KarlinDynamicProgramming.Uniqueness

variable {Ω D : Type*} [TopologicalSpace Ω] [TopologicalSpace D]

lemma weight_succ (m : Model Ω D) (s : Strategy D) (N : ℕ) :
    weight m s (N + 1) = weight m s N * m.P (s N) := by
  simp only [weight, Finset.prod_range_succ]

lemma weight_zero (m : Model Ω D) (s : Strategy D) : weight m s 0 = 1 := by
  simp only [weight, Finset.range_zero, Finset.prod_empty]

lemma weight_pos' (m : Model Ω D) (s : Strategy D) (N : ℕ) : 0 < weight m s N := by
  unfold weight
  exact Finset.prod_pos (fun j _ => m.weight_pos (s j))

lemma partial_succ (m : Model Ω D) (ω : Ω) (s : Strategy D) (N : ℕ) :
    partialReturn m ω s (N + 1) = partialReturn m ω s N + stageReturn m ω s N := by
  simp only [partialReturn, Finset.sum_range_succ]

lemma partial_zero (m : Model Ω D) (ω : Ω) (s : Strategy D) :
    partialReturn m ω s 0 = 0 := by
  simp only [partialReturn, Finset.range_zero, Finset.sum_empty]

lemma stage_nonneg (m : Model Ω D) (ω : Ω) (s : Strategy D) (j : ℕ) :
    0 ≤ stageReturn m ω s j :=
  mul_nonneg (weight_pos' m s j).le (m.reward_nonneg _ _)

/-- One Bellman step: partial + terminal is nonincreasing. -/
lemma step_le (m : Model Ω D) (M : Ω → ℝ) (hB : BellmanSolution m M) (ω : Ω)
    (s : Strategy D) (N : ℕ) :
    partialReturn m ω s (N + 1) + terminalValue m M ω s (N + 1) ≤
      partialReturn m ω s N + terminalValue m M ω s N := by
  have h : bellmanAction m M (trajectory m ω s N) (s N) ≤ M (trajectory m ω s N) :=
    (hB (trajectory m ω s N)).2 ⟨s N, rfl⟩
  simp only [bellmanAction] at h
  rw [partial_succ]
  simp only [terminalValue, stageReturn, weight_succ, trajectory]
  have hw := weight_pos' m s N
  have key := mul_le_mul_of_nonneg_left h hw.le
  nlinarith [key]

lemma partial_add_terminal_le (m : Model Ω D) (M : Ω → ℝ) (hB : BellmanSolution m M)
    (ω : Ω) (s : Strategy D) :
    ∀ N, partialReturn m ω s N + terminalValue m M ω s N ≤ M ω := by
  intro N
  induction N with
  | zero =>
    simp only [partial_zero, terminalValue, weight_zero, trajectory]
    linarith
  | succ n ih => exact (step_le m M hB ω s n).trans ih

lemma M_nonneg (m : Model Ω D) (M : Ω → ℝ) (hM : Admissible m M) (w : Ω) : 0 ≤ M w := by
  obtain ⟨r, hr, hlim⟩ := hM.2 w
  refine le_of_tendsto' hlim (fun N => ?_)
  refine (hr N).2 ?_
  rintro x ⟨s, rfl⟩
  have h1 := partial_add_terminal_le m M hM.1 w s N
  have h2 : 0 ≤ partialReturn m w s N := Finset.sum_nonneg (fun j _ => stage_nonneg m w s j)
  linarith

lemma partial_le (m : Model Ω D) (M : Ω → ℝ) (hM : Admissible m M) (ω : Ω)
    (s : Strategy D) (N : ℕ) : partialReturn m ω s N ≤ M ω := by
  have h1 := partial_add_terminal_le m M hM.1 ω s N
  have h2 : 0 ≤ terminalValue m M ω s N :=
    mul_nonneg (weight_pos' m s N).le (M_nonneg m M hM _)
  linarith

/-- Greedy state sequence. -/
noncomputable def gstate (m : Model Ω D) (a : Ω → D) (ω : Ω) : ℕ → Ω
  | 0 => ω
  | n + 1 => m.T (a (gstate m a ω n)) (gstate m a ω n)

lemma traj_greedy (m : Model Ω D) (a : Ω → D) (ω : Ω) :
    ∀ N, trajectory m ω (fun n => a (gstate m a ω n)) N = gstate m a ω N
  | 0 => rfl
  | N + 1 => by
    rw [trajectory, traj_greedy m a ω N]
    rfl

lemma greedy_eq (m : Model Ω D) (M : Ω → ℝ) (a : Ω → D)
    (ha : ∀ x, bellmanAction m M x (a x) = M x) (ω : Ω) :
    ∀ N, partialReturn m ω (fun n => a (gstate m a ω n)) N +
      terminalValue m M ω (fun n => a (gstate m a ω n)) N = M ω := by
  intro N
  induction N with
  | zero =>
    simp only [partial_zero, terminalValue, weight_zero, trajectory]
    linarith
  | succ n ih =>
    rw [← ih]
    have h := ha (gstate m a ω n)
    simp only [bellmanAction] at h
    rw [partial_succ]
    simp only [terminalValue, stageReturn, weight_succ, traj_greedy]
    have e : gstate m a ω (n + 1) = m.T (a (gstate m a ω n)) (gstate m a ω n) := rfl
    rw [e]
    have key := congrArg (fun t => weight m (fun n => a (gstate m a ω n)) n * t) h
    nlinarith [key]

lemma main_greatest (m : Model Ω D) (M : Ω → ℝ) (hM : Admissible m M) (ω : Ω) :
    IsGreatest (Set.range (totalReturn m ω)) (M ω) := by
  have hex : ∀ x, ∃ b, bellmanAction m M x b = M x := fun x => (hM.1 x).1
  choose a ha using hex
  set g : Strategy D := fun n => a (gstate m a ω n) with hg
  have hsum : ∀ s : Strategy D, Summable (stageReturn m ω s) := fun s =>
    summable_of_sum_range_le (fun j => stage_nonneg m ω s j) (fun N => partial_le m M hM ω s N)
  constructor
  · refine ⟨g, ?_⟩
    apply le_antisymm
    · exact Real.tsum_le_of_sum_range_le (fun j => stage_nonneg m ω g j)
        (fun N => partial_le m M hM ω g N)
    · obtain ⟨r, hr, hlim⟩ := hM.2 ω
      have hr' : Tendsto (fun N => M ω - r N) atTop (nhds (M ω - 0)) :=
        tendsto_const_nhds.sub hlim
      have := le_of_tendsto' hr' (fun N => by
        have h1 := greedy_eq m M a ha ω N
        have h2 : terminalValue m M ω g N ≤ r N := (hr N).1 ⟨g, rfl⟩
        have h3 : partialReturn m ω g N ≤ totalReturn m ω g :=
          (hsum g).sum_le_tsum (Finset.range N) (fun j _ => stage_nonneg m ω g j)
        show M ω - r N ≤ totalReturn m ω g
        linarith)
      simpa using this
  · rintro x ⟨s, rfl⟩
    exact Real.tsum_le_of_sum_range_le (fun j => stage_nonneg m ω s j)
      (fun N => partial_le m M hM ω s N)

end KarlinDPUniqSol

open KarlinDynamicProgramming.Uniqueness in
theorem solution
    {Ω D : Type*} [TopologicalSpace Ω] [T2Space Ω]
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (m : Model Ω D) (hreturns : UniformFiniteReturns m)
    (M : Ω → ℝ) (hM : Admissible m M) :
    (∀ ω, IsGreatest (Set.range (totalReturn m ω)) (M ω)) ∧
    (∀ M' : Ω → ℝ, Admissible m M' → M = M') := by
  refine ⟨fun ω => KarlinDPUniqSol.main_greatest m M hM ω, fun M' hM' => ?_⟩
  funext ω
  exact (KarlinDPUniqSol.main_greatest m M hM ω).unique
    (KarlinDPUniqSol.main_greatest m M' hM' ω)
