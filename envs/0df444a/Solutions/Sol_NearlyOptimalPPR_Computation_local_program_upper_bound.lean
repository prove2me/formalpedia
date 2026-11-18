-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.local_program_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:37:40.718368+00:00
-- url     : https://prove2.me/submissions/5f3619d3-5850-4328-8090-d3bfd197371c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NearlyOptimalPPR_Computation_uniform_local_algorithm
import Definitions.Def_NearlyOptimalPPR_Computation_push

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma scalar_step_cursor (p : LocalPush.Program) {n : ℕ}
    (neighbors : Fin n → List (Fin n)) (ω : ℕ → Bool) (st : LocalPush.State) :
    (LocalPush.step p neighbors ω st).cursor ≤ st.cursor+1 := by
  unfold LocalPush.step
  split
  · exact Nat.le_succ _
  · split <;> first | exact Nat.le_succ _ | exact le_rfl

lemma scalar_step_tape (p : LocalPush.Program) {n : ℕ}
    (neighbors : Fin n → List (Fin n)) (ω ω' : ℕ → Bool) (st : LocalPush.State)
    (hω : ω st.cursor = ω' st.cursor) :
    LocalPush.step p neighbors ω st = LocalPush.step p neighbors ω' st := by
  unfold LocalPush.step
  split
  · rfl
  · split <;> first | rfl | simp only [hω]

lemma machine_step_cursor (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (ω : ℕ → Bool) (st : MachineState) :
    (machineStep m p g ω st).scalar.cursor ≤ st.scalar.cursor+1 := by
  classical
  unfold machineStep
  split
  · exact Nat.le_succ _
  · split
    · exact Nat.le_succ _
    · exact scalar_step_cursor _ _ _ _
    · exact Nat.le_succ _
    · dsimp only
      split <;> exact Nat.le_succ _

lemma machine_step_tape (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (ω ω' : ℕ → Bool) (st : MachineState)
    (hω : ω st.scalar.cursor = ω' st.scalar.cursor) :
    machineStep m p g ω st = machineStep m p g ω' st := by
  classical
  unfold machineStep
  split
  · rfl
  · split
    · rfl
    · rw [scalar_step_tape _ _ ω ω' st.scalar hω]
    · rfl
    · rfl

lemma machine_run_cursor (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool) (t : ℕ) :
    (machineRun m p g s α ε ω t).scalar.cursor ≤ t := by
  induction t with
  | zero => simp [machineRun, machineInit, LocalPush.initState]
  | succ t ih =>
    have hs := machine_step_cursor m p g ω (machineRun m p g s α ε ω t)
    simpa only [machineRun, Function.iterate_succ_apply'] using
      hs.trans (Nat.add_le_add_right ih 1)

lemma machine_run_prefix (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ω ω' : ℕ → Bool) (t : ℕ)
    (hω : ∀ i < t, ω i = ω' i) :
    machineRun m p g s α ε ω t = machineRun m p g s α ε ω' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi := ih (fun i hi => hω i (Nat.lt_succ_of_lt hi))
    simp only [machineRun, Function.iterate_succ_apply']
    change machineStep m p g ω (machineRun m p g s α ε ω t) =
      machineStep m p g ω' (machineRun m p g s α ε ω' t)
    rw [← hi]
    apply machine_step_tape
    exact hω _ (Nat.lt_succ_of_le (machine_run_cursor m p g s α ε ω t))

def extendTape {t : ℕ} (a : Fin t → Bool) : ℕ → Bool :=
  fun i => if h : i < t then a ⟨i,h⟩ else false

lemma machine_run_observable_measurable {X : Type*} [MeasurableSpace X]
    (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (t : ℕ) (f : MachineState → X) :
    Measurable (fun ω => f (machineRun m p g s α ε ω t)) := by
  let obs : (Fin t → Bool) → X := fun a => f (machineRun m p g s α ε (extendTape a) t)
  have hobs : Measurable obs := measurable_of_countable _
  have hres : Measurable (fun ω : ℕ → Bool => (fun i : Fin t => ω i.val)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have he : (fun ω : ℕ → Bool => obs (fun i : Fin t => ω i.val)) =
      (fun ω => f (machineRun m p g s α ε ω t)) := by
    funext ω
    apply congrArg f
    apply machine_run_prefix
    intro i hi
    simp [extendTape,hi]
  rw [← he]
  exact hobs.comp hres

theorem execution_work_measurable (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (s : Fin n) (α ε : ℝ) :
    Measurable (executionWork m p g s α ε) := by
  classical
  have hhalt : MeasurableSet {ω : ℕ → Bool | ∃ t, (machineRun m p g s α ε ω t).scalar.halted = true} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro t
    exact (measurableSet_singleton true).preimage
      (machine_run_observable_measurable m p g s α ε t (fun st => st.scalar.halted))
  have hsup : Measurable (fun ω : ℕ → Bool => ⨆ t, (machineRun m p g s α ε ω t).work) :=
    Measurable.iSup (fun t => machine_run_observable_measurable m p g s α ε t (fun st => st.work))
  exact Measurable.ite hhalt hsup measurable_const

lemma expected_work_le (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (s : Fin n) (α ε : ℝ) (B : ℝ≥0∞)
    (hB : ∀ ω, executionWork m p g s α ε ω ≤ B) :
    expectedWork m p g s α ε ≤ B := by
  haveI : IsProbabilityMeasure LocalPush.coinTape := by
    unfold LocalPush.coinTape
    infer_instance
  unfold expectedWork
  calc
    _ ≤ ∫⁻ _ : ℕ → Bool, B ∂LocalPush.coinTape := lintegral_mono hB
    _ = B := by simp

end
end NearlyOptimalPPR.Computation


set_option autoImplicit false
open Filter Topology
namespace NearlyOptimalPPR.Computation

lemma sqrt_log_ratio_limit :
    Tendsto (fun t : ℝ => Real.sqrt ((Real.log 2 + t) * Real.log (Real.log 4 + t)) / t)
      atTop (𝓝 0) := by
  have hc (a : ℝ) : Tendsto (fun t : ℝ => a / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hr (a : ℝ) : Tendsto (fun t : ℝ => (a+t)/t) atTop (𝓝 1) := by
    have hh := (hc a).add_const 1
    have hh' : Tendsto (fun t : ℝ => a/t+1) atTop (𝓝 1) := by simpa using hh
    apply hh'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp [add_div, ht.ne']
  have hll : Tendsto (fun t : ℝ => Real.log (Real.log 4+t)/t) atTop (𝓝 0) := by
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-Real.log 4) 1 one_ne_zero).comp
      (show Tendsto (fun t : ℝ => Real.log 4 + t) atTop atTop from
        tendsto_const_nhds.add_atTop tendsto_id)
    convert! hh using 1
    ext t
    simp
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ((hr (Real.log 2)).mul hll)
  simp only [one_mul, Real.sqrt_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hprod : 0 ≤ (Real.log 2 + t) * Real.log (Real.log 4 + t) := by
    exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  simp only [Function.comp_apply]
  rw [show ((Real.log 2+t)/t) * (Real.log (Real.log 4+t)/t) =
    ((Real.log 2+t)*Real.log (Real.log 4+t))/(t^2) by ring]
  rw [Real.sqrt_div hprod, Real.sqrt_sq ht0.le]

theorem subpolynomial_envelope (C c : ℝ) (hC : 0 < C) : subpolynomialEnvelope C c := by
  intro η hη
  have hl : Tendsto (fun t : ℝ => Real.log C / t +
      c * (Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t))/t)) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds.div_atTop tendsto_id (a := Real.log C)).add
      (sqrt_log_ratio_limit.const_mul c)
    simpa using hh
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hl.eventually_lt_const hη)
  let B := max T 1
  let ε₀ := Real.exp (-B)
  have hB : 1 ≤ B := le_max_right _ _
  have hε₀ : 0 < ε₀ := Real.exp_pos _
  have hε₀one : ε₀ ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    dsimp [B]
    linarith [le_max_right T 1]
  refine ⟨ε₀, hε₀, hε₀one, ?_⟩
  intro ε hε hsmall
  let t := Real.log (1/ε)
  have htlog : t = -Real.log ε := by
    dsimp [t]
    rw [Real.log_div one_ne_zero hε.ne', Real.log_one, zero_sub]
  have hlogε : Real.log ε ≤ -B := by
    have hh := Real.log_le_log hε hsmall
    simpa only [ε₀, Real.log_exp] using hh
  have htB : B ≤ t := by rw [htlog]; linarith
  have htpos : 0 < t := by linarith
  have htT : T ≤ t := (le_max_left _ _).trans htB
  have hbound := hT t htT
  have halg : Real.log C / t + c * (Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t))/t) =
      (Real.log C + c * Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t)))/t := by ring
  rw [halg] at hbound
  have hexponent : Real.log C + c * Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t)) ≤ η*t :=
    ((div_lt_iff₀ htpos).mp hbound).le
  have h2 : Real.log (2/ε) = Real.log 2+t := by
    rw [Real.log_div (by norm_num) hε.ne', htlog]
    ring
  have h4 : Real.log (4/ε) = Real.log 4+t := by
    rw [Real.log_div (by norm_num) hε.ne', htlog]
    ring
  have hK : 0 < 1/ε := by positivity
  calc
    envelope C c ε = (1/ε) * Real.exp
        (Real.log C + c * Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t))) := by
      rw [envelope, h2, h4, Real.exp_add, Real.exp_log hC]
      ring
    _ ≤ (1/ε) * Real.exp (η*t) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hK.le
    _ = (1/ε) ^ (1+η) := by
      rw [Real.rpow_add hK, Real.rpow_one, Real.rpow_def_of_pos hK]
      congr 2
      ring

end NearlyOptimalPPR.Computation

open NearlyOptimalPPR.Computation
theorem solution (m : SolveModel) :
    ∃ (p : Program) (C c : ℝ), admissible p ∧ 0 < C ∧ 0 < c ∧
      (∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ),
        0 < α → α < 1 → 0 < ε → ε ≤ 1 →
          successful m p g s α ε ∧
          Measurable (executionWork m p g s α ε) ∧
          expectedWork m p g s α ε ≤ ENNReal.ofReal (envelope C c ε)) ∧
      subpolynomialEnvelope C c := by
  obtain ⟨p,C,c,had,hC,hc,hu⟩ := uniform_local_algorithm m
  refine ⟨p,C,c,had,hC,hc,?_,subpolynomial_envelope C c hC⟩
  intro n g s α ε hα hα' hε hε'
  have hh := hu n g s α ε hα hα' hε hε'
  exact ⟨hh.1, execution_work_measurable m p g s α ε, hh.2⟩
