-- Prove2me | solution 1 for OAI.Balanced.Selection.Process.selectionStatement_of_uniform_concentration_occupancy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:26:47.528028+00:00
-- url     : https://prove2.me/submissions/7728f28d-0800-422a-bcb4-b69183f74207

import Mathlib
import Definitions.Def_OAIQ63Br004

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_BernoulliTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Finset

namespace Balanced
open scoped _root_.Balanced

variable {Index Sample : Type*}

lemma esymm_cons_succ (x : ℝ) (s : Multiset ℝ) (k : ℕ) :
    (x ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + x * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map,
    Multiset.sum_map_mul_left]

lemma factorial_mul_esymm_le_sum_pow (s : Multiset ℝ)
    (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) :
    (k.factorial : ℝ) * s.esymm k ≤ s.sum ^ k := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
      cases k <;> simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | @cons x s ih =>
      have hx : 0 ≤ x := hs x (by simp)
      have hs' : ∀ y ∈ s, 0 ≤ y := fun y hy => hs y (by simp [hy])
      have hsum : 0 ≤ s.sum := Multiset.sum_nonneg hs'
      cases k with
      | zero => simp [Multiset.esymm]
      | succ k =>
          rw [esymm_cons_succ, Multiset.sum_cons]
          have h₁ := ih hs' (k + 1)
          have h₂ := mul_le_mul_of_nonneg_left (ih hs' k)
            (mul_nonneg (Nat.cast_nonneg (k + 1)) hx)
          have hb := pow_add_mul_le_add_pow hsum (by positivity : 0 ≤ 2 * s.sum + x) (k + 1)
          simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h₁ ⊢
          simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at hb h₂
          rw [add_comm x s.sum]
          nlinarith [hb]

lemma sum_prod_powersetCard_le (s : Finset Index) (p : Index → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (k : ℕ) :
    (∑ t ∈ s.powersetCard k, ∏ i ∈ t, p i) ≤ (∑ i ∈ s, p i) ^ k / k.factorial := by
  have h := factorial_mul_esymm_le_sum_pow (s.val.map p) (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    exact hp i hi) k
  rw [Finset.esymm_map_val] at h
  simp only [Finset.sum_map_val] at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < k.factorial)).2
  simpa [mul_comm] using h

lemma pow_div_factorial_le_exp_ratio (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) (hk : 0 < k) :
    μ ^ k / k.factorial ≤ (Real.exp 1 * μ / k) ^ k := by
  have hk₀ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  calc
    μ ^ k / k.factorial = (μ / k) ^ k * ((k : ℝ) ^ k / k.factorial) := by
      rw [div_pow]
      field_simp
    _ ≤ (μ / k) ^ k * Real.exp (k : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k)
        (pow_nonneg (div_nonneg hμ (Nat.cast_nonneg k)) k)
    _ = (Real.exp 1 * μ / k) ^ k := by
      rw [show Real.exp (k : ℝ) = Real.exp 1 ^ k by simp [← Real.exp_nat_mul],
        ← mul_pow]
      congr 1
      ring

open MeasureTheory ProbabilityTheory

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteHistory
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

namespace Balanced.FiniteHistory

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma measurable_stepObservable (n : ℕ) (f : Prefix S n → S → ℝ) :
    Measurable (stepObservable n f) := by
  have hm : Measurable (fun ω : Path S => (frestrictLe n ω, ω (n + 1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  exact (measurable_of_countable (Function.uncurry f)).comp hm

lemma integrable_stepObservable (n : ℕ) (f : Prefix S n → S → ℝ)
    (ν : Measure (Path S)) [IsFiniteMeasure ν] : Integrable (stepObservable n f) ν := by
  have hmap : Measurable (fun ω : Path S => (frestrictLe n ω, ω (n + 1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  have hi : Integrable (Function.uncurry f)
      (ν.map (fun ω : Path S => (frestrictLe n ω, ω (n + 1)))) := .of_finite
  exact hi.comp_measurable hmap

lemma map_next_traj (step : ℕ → S → PMF S) (n : ℕ) (h : Prefix S n) :
    (Kernel.traj (X := fun _ => S) (historyKernel step) n h).map (fun ω : Path S => ω (n + 1)) =
      (step n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure := by
  rw [← Kernel.map_apply _ (measurable_pi_apply (n + 1)), Kernel.map_traj_succ_self]
  rfl

lemma integral_stepObservable_traj (step : ℕ → S → PMF S) (n : ℕ)
    (h : Prefix S n) (f : Prefix S n → S → ℝ) :
    (∫ ω, stepObservable n f ω ∂Kernel.traj (X := fun _ => S) (historyKernel step) n h) =
      ∑ s, (step n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) s).toReal * f h s := by
  rw [Kernel.integral_traj h (measurable_stepObservable n f).stronglyMeasurable.aestronglyMeasurable]
  have hfreeze (ω : Path S) :
      stepObservable n f (Function.updateFinset ω (Finset.Iic n) h) = f h (ω (n + 1)) := by
    have hp : frestrictLe n (Function.updateFinset ω (Finset.Iic n) h) = h := by
      funext j
      simp [frestrictLe, Function.updateFinset, j.property]
    simp [stepObservable, hp, Function.updateFinset]
  simp_rw [hfreeze]
  rw [← integral_map (measurable_pi_apply (n + 1)).aemeasurable
    (measurable_of_countable (f h)).stronglyMeasurable.aestronglyMeasurable,
    map_next_traj, PMF.integral_eq_sum]
  rfl

theorem condExp_stepObservable (step : ℕ → S → PMF S) (s₀ : S)
    (n : ℕ) (f : Prefix S n → S → ℝ) :
    (pathLaw step s₀)[stepObservable n f | filtration n] =ᵐ[pathLaw step s₀]
      fun ω => ∑ s, (step n (ω n) s).toReal * f (frestrictLe n ω) s := by
  have h := Kernel.condExp_traj (X := fun _ => S) (κ := historyKernel step) (Nat.zero_le n)
    (x₀ := fun _ => s₀) (integrable_stepObservable n f (pathLaw step s₀))
  filter_upwards [h] with ω hω
  change (pathLaw step s₀)[stepObservable n f | filtration n] ω = _ at hω ⊢
  rw [hω, integral_stepObservable_traj]
  rfl

theorem map_prefix_pathLaw (step : ℕ → S → PMF S) (s₀ : S) (n : ℕ) :
    (pathLaw step s₀).map (frestrictLe n) =
      Kernel.partialTraj (X := fun _ => S) (historyKernel step) 0 n (fun _ => s₀) :=
  Kernel.traj_map_frestrictLe_apply (X := fun _ => S) (κ := historyKernel step) 0 n (fun _ => s₀)

theorem map_prefix_next_pathLaw (step : ℕ → S → PMF S) (s₀ : S) (n : ℕ) :
    (pathLaw step s₀).map (fun ω : Path S => (frestrictLe n ω, ω (n + 1))) =
      ((pathLaw step s₀).map (frestrictLe n)) ⊗ₘ historyKernel step n := by
  rw [map_prefix_pathLaw]
  exact (Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ => S) (κ := historyKernel step) (x₀ := fun _ => s₀) (Nat.zero_le n)).symm

end Balanced.FiniteHistory

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteHistoryInvariant
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter Finset Preorder
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.FiniteHistory

variable {S : Type*} [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

theorem ae_pmf_nonzero (p : PMF S) : ∀ᵐ s ∂p.toMeasure, p s ≠ 0 := by
  rw [ae_iff]
  change p.toMeasure p.supportᶜ = 0
  exact (p.toMeasure_apply_eq_zero_iff MeasurableSet.of_discrete).2
    disjoint_compl_right

theorem ae_initial_state (step : ℕ → S → PMF S) (s₀ : S) :
    ∀ᵐ ω ∂pathLaw step s₀, ω 0 = s₀ := by
  have hp : (pathLaw step s₀).map (frestrictLe 0) =
      Measure.dirac (fun _ : Iic 0 ↦ s₀) := by
    rw [map_prefix_pathLaw, Kernel.partialTraj_self, Kernel.id_apply]
  have hi : ∀ᵐ h ∂(pathLaw step s₀).map (frestrictLe 0),
      h ⟨0, mem_Iic.mpr le_rfl⟩ = s₀ := by
    rw [hp]
    exact (ae_dirac_iff MeasurableSet.of_discrete).2 rfl
  exact ae_of_ae_map (by fun_prop) hi

theorem ae_step_support (step : ℕ → S → PMF S) (s₀ : S) (n : ℕ) :
    ∀ᵐ ω ∂pathLaw step s₀, step n (ω n) (ω (n + 1)) ≠ 0 := by
  have hp : ∀ᵐ z ∂((pathLaw step s₀).map (frestrictLe n)) ⊗ₘ historyKernel step n,
      step n (z.1 ⟨n, mem_Iic.mpr le_rfl⟩) z.2 ≠ 0 := by
    apply Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete
    apply Eventually.of_forall
    intro h
    exact ae_pmf_nonzero (step n (h ⟨n, mem_Iic.mpr le_rfl⟩))
  rw [← map_prefix_next_pathLaw] at hp
  exact ae_of_ae_map (f := fun ω : Path S ↦ (frestrictLe n ω, ω (n + 1)))
    (by fun_prop) hp

theorem ae_all_invariant (step : ℕ → S → PMF S) (s₀ : S)
    (P : ℕ → S → Prop) (h₀ : P 0 s₀)
    (hstep : ∀ n s t, step n s t ≠ 0 → P n s → P (n + 1) t) :
    ∀ᵐ ω ∂pathLaw step s₀, ∀ n, P n (ω n) := by
  filter_upwards [ae_initial_state step s₀,
    ae_all_iff.2 (fun n ↦ ae_step_support step s₀ n)] with ω hi hs
  intro n
  induction n with
  | zero => simpa only [hi] using h₀
  | succ n ih => exact hstep n (ω n) (ω (n + 1)) (hs n) ih

end Balanced.FiniteHistory

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteKernelPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.FiniteKernelPotential

noncomputable section

variable {X : Type*} [Fintype X]

 theorem advance_nonneg (K : X → X → ℝ) (w : X → ℝ)
    (hK : ∀ x y, 0 ≤ K x y) (hw : ∀ x, 0 ≤ w x) (y : X) :
    0 ≤ advance K w y := by
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (hw x) (hK x y)

 theorem weights_nonneg (K : ℕ → X → X → ℝ) (w₀ : X → ℝ)
    (hK : ∀ t x y, 0 ≤ K t x y) (hw₀ : ∀ x, 0 ≤ w₀ x)
    (t : ℕ) (x : X) : 0 ≤ weights K w₀ t x := by
  induction t generalizing x with
  | zero => exact hw₀ x
  | succ t ih =>
    exact advance_nonneg (K t) (weights K w₀ t) (hK t)
      ih x

theorem advance_pairing (K : X → X → ℝ) (w Φ : X → ℝ) :
    ∑ y, advance K w y * Φ y = ∑ x, w x * ∑ y, K x y * Φ y := by
  simp only [advance, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem advance_potential_le (K : X → X → ℝ) (w Φ Ψ : X → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hstep : ∀ x, ∑ y, K x y * Ψ y ≤ Φ x) :
    ∑ y, advance K w y * Ψ y ≤ ∑ x, w x * Φ x := by
  rw [advance_pairing]
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul_of_nonneg_left (hstep x) (hw x)

theorem expected_potential_le (K : ℕ → X → X → ℝ) (w₀ : X → ℝ)
    (Φ : ℕ → X → ℝ)
    (hK : ∀ t x y, 0 ≤ K t x y) (hw₀ : ∀ x, 0 ≤ w₀ x)
    (hstep : ∀ t x, ∑ y, K t x y * Φ (t + 1) y ≤ Φ t x)
    (T : ℕ) :
    ∑ y, weights K w₀ T y * Φ T y ≤ ∑ x, w₀ x * Φ 0 x := by
  induction T with
  | zero => exact le_rfl
  | succ T ih =>
    exact (advance_potential_le (K T) (weights K w₀ T) (Φ T) (Φ (T + 1))
      (weights_nonneg K w₀ hK hw₀ T) (hstep T)).trans ih

theorem payoff_le (K : ℕ → X → X → ℝ) (w₀ : X → ℝ)
    (Φ : ℕ → X → ℝ) (payoff : X → ℝ)
    (hK : ∀ t x y, 0 ≤ K t x y) (hw₀ : ∀ x, 0 ≤ w₀ x)
    (hstep : ∀ t x, ∑ y, K t x y * Φ (t + 1) y ≤ Φ t x)
    (T : ℕ) (hpayoff : ∀ x, payoff x ≤ Φ T x) :
    ∑ y, weights K w₀ T y * payoff y ≤ ∑ x, w₀ x * Φ 0 x := by
  calc
    _ ≤ ∑ y, weights K w₀ T y * Φ T y := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left (hpayoff y) (weights_nonneg K w₀ hK hw₀ T y)
    _ ≤ _ := expected_potential_le K w₀ Φ hK hw₀ hstep T

theorem weights_eq_of_recurrence (K : ℕ → X → X → ℝ) (w : ℕ → X → ℝ)
    (hrec : ∀ t y, w (t + 1) y = ∑ x, w t x * K t x y) (T : ℕ) :
    weights K (w 0) T = w T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    funext y
    simp only [weights_succ, advance, ih]
    exact (hrec T y).symm

theorem evolution_payoff_le (K : ℕ → X → X → ℝ) (w : ℕ → X → ℝ)
    (Φ : ℕ → X → ℝ) (payoff : X → ℝ)
    (hrec : ∀ t y, w (t + 1) y = ∑ x, w t x * K t x y)
    (hK : ∀ t x y, 0 ≤ K t x y) (hw₀ : ∀ x, 0 ≤ w 0 x)
    (hstep : ∀ t x, ∑ y, K t x y * Φ (t + 1) y ≤ Φ t x)
    (T : ℕ) (hpayoff : ∀ x, payoff x ≤ Φ T x) :
    ∑ y, w T y * payoff y ≤ ∑ x, w 0 x * Φ 0 x := by
  rw [← weights_eq_of_recurrence K w hrec T]
  exact payoff_le K (w 0) Φ payoff hK hw₀ hstep T hpayoff

end
end Balanced.FiniteKernelPotential

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_LogTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace BalancedRyser

theorem polynomial_mul_ratio_pow_le_inv
    (q r B : ℕ) (C : ℝ) (hq : 0 < q) (hBpos : 0 < B)
    (hC : 0 ≤ C) (hlog : Real.log (q : ℝ) ≤ (B : ℝ))
    (hlarge : C * Real.exp ((r : ℝ) + 1) ≤ (B : ℝ)) :
    (q : ℝ) ^ r * (C / (B : ℝ)) ^ B ≤ (q : ℝ)⁻¹ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hbase : C / (B : ℝ) ≤ Real.exp (-((r : ℝ) + 1)) := by
    rw [Real.exp_neg]
    apply (div_le_iff₀ hBR).2
    simpa [div_eq_mul_inv, mul_comm] using
      ((le_div_iff₀ (Real.exp_pos ((r : ℝ) + 1))).2 hlarge)
  have hpow : (C / (B : ℝ)) ^ B ≤
      Real.exp (-((r : ℝ) + 1)) ^ B :=
    pow_le_pow_left₀ (div_nonneg hC hBR.le) hbase B
  calc
    (q : ℝ) ^ r * (C / (B : ℝ)) ^ B
        ≤ (q : ℝ) ^ r * Real.exp (-((r : ℝ) + 1)) ^ B :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg hqR.le _)
    _ = Real.exp ((r : ℝ) * Real.log (q : ℝ) - ((r : ℝ) + 1) * B) := by
      have hqpow : (q : ℝ) ^ r = Real.exp ((r : ℝ) * Real.log (q : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hqR]
      rw [hqpow, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log (q : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith
    _ = (q : ℝ)⁻¹ := by rw [Real.exp_neg, Real.exp_log hqR]

end BalancedRyser

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SlotConditionedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace Balanced.Slots

universe u v
variable {ι : Type u} {V : ι → Type v}
variable [Fintype ι] [∀ i, Fintype (V i)]
variable [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)]

theorem conditional_law_eq_uniformOn (G : Set (Assignment V)) :
    cond (law V) G = uniformOn G := by
  rw [law_eq_uniformOn]
  unfold uniformOn
  rw [cond_cond_eq_cond_inter MeasurableSet.univ (Set.toFinite G).measurableSet]
  simp

theorem conditional_law_eq_uniformOfFinset (G : Finset (Assignment V))
    (hG : G.Nonempty) :
    cond (law V) (G : Set (Assignment V)) = (PMF.uniformOfFinset G hG).toMeasure := by
  classical
  rw [conditional_law_eq_uniformOn]
  apply Measure.ext_of_singleton
  intro a
  rw [PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a),
    PMF.uniformOfFinset_apply]
  rw [← Finset.coe_singleton, uniformOn_apply_finset]
  by_cases ha : a ∈ G <;> simp [ha]

end Balanced.Slots

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TailProduct

open scoped BigOperators

theorem neg_log_one_sub_le_twice {x : ℝ} (hx : 0 ≤ x) (hhalf : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hp : 0 < 1 - x := by linarith
  have hi : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    apply (sub_le_iff_le_add).2
    apply (inv_le_iff_one_le_mul₀ hp).2
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hl
  exact hl.trans hi

end Balanced.TailProduct

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailConditioning2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced
open scoped _root_.Balanced
namespace TailConditioning

universe u v
variable {I : Type u} {Q : I → Type v}

theorem tail_conditioning_of_pointwise_bounds
    [Fintype I] [∀ i, Fintype (Q i)]
    [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)]
    (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj]
    (hno : TailGraph.NoWithinSlotEdges G Sigma.fst)
    (hsize : ∀ i, 3 ≤ Fintype.card (Q i))
    (hdegree : ∀ v i, 8 * G.degree v ≤ Fintype.card (Q i)) :
    0 < (Slots.law Q).real (independentTransversals Q G) ∧
      ∀ (J : Finset I) (a : Slots.Assignment Q),
        conditionalCylinder Q G J a ≤
          Real.exp ((J.card : ℝ) / 2) * ∏ i ∈ J, (Fintype.card (Q i) : ℝ)⁻¹ := by
  classical
  let : ∀ i, Nonempty (Q i) := fun i => Fintype.card_pos_iff.mp
    (lt_of_lt_of_le (show 0 < 3 by decide) (hsize i))
  cases isEmpty_or_nonempty I with
  | inl hI =>
    let := hI
    exact tail_conditioning_of_bounds G hno 3 0 (by decide)
      (fun i => isEmptyElim i) (fun v => isEmptyElim v.1) (by decide)
  | inr hI =>
    let := hI
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
      (fun i => Fintype.card (Q i)) Finset.univ_nonempty
    refine tail_conditioning_of_bounds G hno (Fintype.card (Q i))
      (Fintype.card (Q i) / 8) (hsize i)
      (fun j => hi j (Finset.mem_univ j)) ?_ (Nat.mul_div_le _ _)
    intro v
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).mpr
    simpa only [Nat.mul_comm] using hdegree v i

end TailConditioning
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailPrescriptions2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced.TailConditioning

universe u v w
variable {I : Type u} {Q : I → Type v} {V : Type w}

theorem ambientCylinder_eq_cylinder_of_mem
    (embed : ∀ i, Q i → V) (hinj : ∀ i, Function.Injective (embed i))
    (J : Finset I) (a : I → V) (b : Slots.Assignment Q)
    (hb : b ∈ ambientCylinder Q embed J a) :
    ambientCylinder Q embed J a = Slots.cylinder Q J b := by
  ext ω
  constructor
  · intro h i hi
    exact hinj i ((h i hi).trans (hb i hi).symm)
  · intro h i hi
    rw [h i hi]
    exact hb i hi

end Balanced.TailConditioning

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ThinningTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace Balanced.BernoulliTail

lemma tendsto_polynomial_mul_ratio_tail (B : ℕ → ℕ)
    (hB : Tendsto (fun q => (B q : ℝ)) atTop atTop)
    (hlog : ∀ᶠ q : ℕ in atTop, Real.log (q : ℝ) ≤ (B q : ℝ))
    (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ r * (C / (B q : ℝ)) ^ B q)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun q => by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hlog,
      hB.eventually (eventually_gt_atTop 0),
      hB.eventually (eventually_ge_atTop (C * Real.exp ((r : ℝ) + 1)))]
      with q hq hl hpos hlarge
    have hBn : 0 < B q := by exact_mod_cast hpos
    exact BalancedRyser.polynomial_mul_ratio_pow_le_inv q r (B q) C hq hBn hC hl hlarge
  · exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

lemma rpow_lt_thinningCutoff (β : ℝ) (q : ℕ) :
    (q : ℝ) ^ β < (thinningCutoff β q : ℝ) := by
  simpa [thinningCutoff] using Nat.lt_floor_add_one ((q : ℝ) ^ β)

lemma tendsto_thinningCutoff_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun q : ℕ => (thinningCutoff β q : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun q => (rpow_lt_thinningCutoff β q).le)
  exact (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop

lemma eventually_log_le_thinningCutoff {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ q : ℕ in atTop, Real.log (q : ℝ) ≤ (thinningCutoff β q : ℝ) := by
  have h := ((isLittleO_log_rpow_atTop hβ).comp_tendsto
    tendsto_natCast_atTop_atTop).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [h] with q hq
  have hnorm : |Real.log (q : ℝ)| ≤ (q : ℝ) ^ β := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) β)] using hq
  exact (le_abs_self _).trans (hnorm.trans (rpow_lt_thinningCutoff β q).le)

lemma tendsto_polynomial_mul_thinning_tail {β : ℝ} (hβ : 0 < β)
    (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ r *
      (C / (thinningCutoff β q : ℝ)) ^ thinningCutoff β q) atTop (𝓝 0) :=
  tendsto_polynomial_mul_ratio_tail (thinningCutoff β)
    (tendsto_thinningCutoff_atTop hβ) (eventually_log_le_thinningCutoff hβ) r C hC

lemma tendsto_post_step_abort_bound (m : ℝ) (hm : 0 ≤ m) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ 3 *
      (Real.exp 1 * m / (thinningCutoff (1 / 8) q : ℝ)) ^ thinningCutoff (1 / 8) q)
      atTop (𝓝 0) :=
  tendsto_polynomial_mul_thinning_tail (by norm_num : (0 : ℝ) < 1 / 8)
    3 (Real.exp 1 * m) (mul_nonneg (Real.exp_pos 1).le hm)

end Balanced.BernoulliTail

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionBarriers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Real
open scoped BigOperators Topology

namespace Balanced.SelectionBarriers

theorem finite_hazard_le {I : Type*} (R : Finset I) (L d : I → ℝ)
    {h m D : ℝ} (hh : 0 < h) (hm : 0 < m)
    (hL : ∀ i ∈ R, m ≤ L i) (hd : ∀ i ∈ R, 0 ≤ d i)
    (hD : ∑ i ∈ R, d i ≤ D) :
    (∑ i ∈ R, d i / L i) / h ≤ D / (h * m) := by
  have hsum : (∑ i ∈ R, d i / L i) ≤ (∑ i ∈ R, d i) / m := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i hi ↦ div_le_div_of_nonneg_left (hd i hi) hm (hL i hi)
  calc
    _ ≤ ((∑ i ∈ R, d i) / m) / h := div_le_div_of_nonneg_right hsum hh.le
    _ ≤ (D / m) / h := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hD hm.le) hh.le
    _ = D / (h * m) := by ring

theorem domain_barrier {s smin c q e L L₀ : ℝ}
    (hs : smin ≤ s) (hc : 0 < c) (hq : 0 < q)
    (he : e ≤ smin * c * q / 2) (hL₀ : c * q ≤ L₀)
    (hL : |L - s * L₀| ≤ e) (hsmin : 0 < smin) :
    s * c * q / 2 ≤ L := by
  have hs0 : 0 ≤ s := hsmin.le.trans hs
  have hsc : s * (c * q) ≤ s * L₀ := mul_le_mul_of_nonneg_left hL₀ hs0
  have hscale : smin * c * q ≤ s * c * q :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hc.le) hq.le
  have hlow := (abs_le.mp hL).1
  nlinarith

theorem hazard_barrier_arithmetic {q n h s smin c C a e : ℝ}
    (hq : 0 < q) (hqn : q ≤ n) (ha : 0 < a) (hh : a * q ≤ h)
    (hsmin : 0 < smin) (hs : smin ≤ s) (hc : 0 < c) (hC : 0 ≤ C)
    (he₁ : e ≤ smin * c * q / 2) (he₂ : e ≤ a * smin * c * q) :
    (s * (h / n) * C * q + e) / (h * (s * c * q - e)) ≤
      (2 * C / c + 2) / q := by
  have hn : 0 < n := hq.trans_le hqn
  have hh0 : 0 < h := (mul_pos ha hq).trans_le hh
  have hs0 : 0 < s := hsmin.trans_le hs
  have hscq : 0 < s * c * q := mul_pos (mul_pos hs0 hc) hq
  have hscale : smin * c * q ≤ s * c * q :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hc.le) hq.le
  have hem : e ≤ s * c * q / 2 := he₁.trans (by linarith)
  have hm : 0 < s * c * q - e := by linarith
  have heh : e ≤ h * s * c := by
    calc
      e ≤ a * smin * c * q := he₂
      _ = (a * q) * smin * c := by ring
      _ ≤ h * smin * c := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hh hsmin.le) hc.le
      _ ≤ h * s * c := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs hh0.le) hc.le
  have hfrac : h / n * q ≤ h := by
    calc
      h / n * q = h * q / n := by ring
      _ ≤ h := (div_le_iff₀ hn).2 (mul_le_mul_of_nonneg_left hqn hh0.le)
  have hdeg : s * (h / n) * C * q ≤ s * h * C := by
    calc
      s * (h / n) * C * q = (s * C) * (h / n * q) := by ring
      _ ≤ (s * C) * h := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hs0.le hC)
      _ = s * h * C := by ring
  have hcoef : 0 ≤ 2 * C / c + 2 := by positivity
  apply (div_le_iff₀ (mul_pos hh0 hm)).2
  have hbase : s * h * C + h * s * c ≤
      ((2 * C / c + 2) / q) * (h * (s * c * q - e)) := by
    have hlower : h * (s * c * q / 2) ≤ h * (s * c * q - e) :=
      mul_le_mul_of_nonneg_left (by linarith) hh0.le
    have hmul := mul_le_mul_of_nonneg_left hlower (div_nonneg hcoef hq.le)
    have hid : ((2 * C / c + 2) / q) * (h * (s * c * q / 2)) =
        s * h * C + h * s * c := by field_simp
    rw [hid] at hmul
    exact hmul
  nlinarith

theorem eventually_selection_error_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, (q : ℝ) ^ ((4 : ℝ) / 5) ≤ δ * q := by
  have ht := (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 : ℝ) / 5)).comp
    tendsto_natCast_atTop_atTop
  have hb : ∀ᶠ q : ℕ in atTop, (q : ℝ) ^ (-((1 : ℝ) / 5)) < δ :=
    ht.eventually (gt_mem_nhds hδ)
  filter_upwards [hb, eventually_ge_atTop 1] with q hb hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hid : (q : ℝ) ^ ((4 : ℝ) / 5) =
      (q : ℝ) ^ (-((1 : ℝ) / 5)) * q := by
    calc
      _ = (q : ℝ) ^ (-((1 : ℝ) / 5) + 1) := by norm_num
      _ = _ := by rw [Real.rpow_add hq0, Real.rpow_one]
  rw [hid]
  exact mul_le_mul_of_nonneg_right hb.le hq0.le

theorem eventually_selection_error_budgets {a smin c : ℝ}
    (ha : 0 < a) (hsmin : 0 < smin) (hc : 0 < c) :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ smin * c * q / 2 ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ a * smin * c * q := by
  have h₁ := eventually_selection_error_le (δ := smin * c / 2) (by positivity)
  have h₂ := eventually_selection_error_le (δ := a * smin * c) (by positivity)
  filter_upwards [h₁, h₂] with q h₁ h₂
  constructor
  · convert h₁ using 1; ring
  · exact h₂

end Balanced.SelectionBarriers

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionProcessLaw
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotMeasurableSingletonClass _root_.OAI.Balanced.Selection.Process.snapshotMeasurableSpace _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

theorem transitionWeight_eq_draw_pushforward (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Option (State I V)) :
    transitionWeight p q t G before out =
      ∑ draw, if advance q G before draw = out then drawStepWeight p q t G before draw else 0 := by
  cases before with
  | none =>
    by_cases ho : out = none <;> simp [transitionWeight, advance, drawStepWeight, ho, eq_comm]
  | some S =>
    by_cases hp : Precheck p q t G S
    · simp [transitionWeight, stepWeight, drawStepWeight, advance, hp, Fintype.sum_option]
    · by_cases ho : out = none <;>
        simp [transitionWeight, stepWeight, drawStepWeight, advance, hp, ho, Fintype.sum_option, eq_comm]

theorem snapshotPMF_apply_real (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) :
    (snapshotPMF p q t G before out).toReal = snapshotWeight p q t G before out :=
  ENNReal.toReal_ofReal (snapshotWeight_nonnegative p q t G before out)

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced.SelectionScales

private theorem rate_bounds {P : ℝ} {q : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) :
    0 ≤ P / q ∧ P / q ≤ 1 / 2 := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  constructor
  · exact div_nonneg hP hqR.le
  · apply (div_le_iff₀ hqR).2
    linarith

theorem domain_bounds {P : ℝ} {q t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) (ht : t ≤ 3 * q) :
    Real.exp (-6 * P) ≤ domain P q t ∧ domain P q t ≤ 1 := by
  obtain ⟨hx, hxhalf⟩ := rate_bounds hP hq hPq
  have hbase : 0 < 1 - P / q := by linarith
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have htR : (t : ℝ) ≤ 3 * q := by exact_mod_cast ht
  constructor
  · rw [domain, ← Real.exp_log (pow_pos hbase t)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    have hlog := Balanced.TailProduct.neg_log_one_sub_le_twice hx hxhalf
    have hmul := mul_le_mul_of_nonneg_left (show -2 * (P / q) ≤
        Real.log (1 - P / q) by linarith) (Nat.cast_nonneg t)
    have htime := mul_le_mul_of_nonpos_right htR (show -2 * (P / q) ≤ 0 by linarith)
    have heq : (3 * (q : ℝ)) * (-2 * (P / q)) = -6 * P := by
      field_simp
      ring
    rw [heq] at htime
    exact htime.trans hmul
  · exact pow_le_one₀ hbase.le (by linarith) (n := t)

theorem domain_pos {P : ℝ} {q t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) :
    0 < domain P q t := by
  obtain ⟨_, hx⟩ := rate_bounds hP hq hPq
  exact pow_pos (by linarith) t

theorem degree_bounds {P a : ℝ} {q n t : ℕ}
    (hP : 0 ≤ P) (ha : 0 ≤ a) (hq : 0 < q) (hn : 0 < n)
    (hPq : 2 * P ≤ q) (hnq : n ≤ 3 * q) (htn : t ≤ n)
    (hremain : a * q ≤ (n - t : ℕ)) :
    Real.exp (-6 * P) * a / 3 ≤ degree P q n t ∧ degree P q n t ≤ 1 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnqR : (n : ℝ) ≤ 3 * q := by exact_mod_cast hnq
  have hremn : ((n - t : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n t
  have hratio : a / 3 ≤ (n - t : ℕ) / (n : ℝ) := by
    apply (le_div_iff₀ hnR).2
    have hprod := mul_le_mul_of_nonneg_left hnqR ha
    nlinarith
  have hratio_one : (n - t : ℕ) / (n : ℝ) ≤ 1 := by
    exact (div_le_one hnR).2 hremn
  have hratio_nonneg : 0 ≤ (n - t : ℕ) / (n : ℝ) := by positivity
  obtain ⟨hdr, hdu⟩ := domain_bounds hP hq hPq (htn.trans hnq)
  change Real.exp (-6 * P) * a / 3 ≤ domain P q t * (n - t : ℕ) / n ∧ _
  rw [mul_div_assoc, mul_div_assoc]
  constructor
  · exact mul_le_mul hdr hratio (by positivity) (domain_pos hP hq hPq).le
  · change domain P q t * (n - t : ℕ) / n ≤ 1
    rw [mul_div_assoc]
    calc
      domain P q t * ((n - t : ℕ) / (n : ℝ)) ≤ 1 * 1 :=
        mul_le_mul hdu hratio_one hratio_nonneg (by norm_num)
      _ = 1 := by ring

end Balanced.SelectionScales

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionCylinder
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] [Fintype V] in
lemma cylinderPotential_nonneg (J : Finset I) (a : I → V) {c : ℝ} (hc : 0 ≤ c)
    (S : State I V) : 0 ≤ cylinderPotential J a c S := by
  unfold cylinderPotential
  split_ifs <;> positivity

lemma cylinderPotential_initial (J : Finset I) (a : I → V) (c : ℝ) :
    cylinderPotential J a c initialState = c ^ J.card := by
  simp [cylinderPotential, PrescriptionsAgree, initialState]

omit [Fintype I] [Fintype V] in
lemma prescriptionsAgree_update_iff (G : Input I V) (J : Finset I) (a : I → V)
    (S : State I V) (i : I) (hi : i ∈ S.remaining) (w : V) (flags : V → Bool) :
    PrescriptionsAgree J a (update G S i w flags) ↔
      PrescriptionsAgree J a S ∧ (i ∈ J → w = a i) := by
  constructor
  · intro h
    constructor
    · intro j hj hjR
      have hji : j ≠ i := by intro hji; subst j; contradiction
      have h' := h j hj (by simp [update, hjR])
      simpa [update, Function.update_of_ne hji] using h'
    · intro hiJ
      have h' := h i hiJ (by simp [update])
      simpa [update] using h'
  · rintro ⟨h, hw⟩ j hj hjR
    by_cases hji : j = i
    · subst j
      simp [update, hw hj]
    · have hjR' : j ∉ S.remaining := by
        simpa [update, Finset.mem_erase, hji] using hjR
      have h' := h j hj hjR'
      simpa [update, Function.update_of_ne hji] using h'

omit [Fintype I] [Fintype V] in
lemma cylinderPotential_update_flags (G : Input I V) (J : Finset I) (a : I → V)
    (c : ℝ) (S : State I V) (i : I) (w : V) (flags flags' : V → Bool) :
    cylinderPotential J a c (update G S i w flags) =
      cylinderPotential J a c (update G S i w flags') := rfl

omit [Fintype I] [Fintype V] in
lemma cylinderPotential_update_unprescribed (G : Input I V) (J : Finset I)
    (a : I → V) (c : ℝ) (S : State I V) (i : I) (hi : i ∈ S.remaining)
    (hiJ : i ∉ J) (w : V) (flags : V → Bool) :
    cylinderPotential J a c (update G S i w flags) = cylinderPotential J a c S := by
  have hset : J ∩ S.remaining.erase i = J ∩ S.remaining := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_erase]
    aesop
  simp only [cylinderPotential, prescriptionsAgree_update_iff G J a S i hi w flags,
    hiJ, false_implies, and_true]
  change (if PrescriptionsAgree J a S then c ^ (J ∩ S.remaining.erase i).card else 0) = _
  rw [hset]

omit [Fintype I] [Fintype V] in
lemma cylinderPotential_update_prescribed (G : Input I V) (J : Finset I)
    (a : I → V) (c : ℝ) (S : State I V) (i : I) (hi : i ∈ S.remaining)
    (hiJ : i ∈ J) (w : V) (flags : V → Bool) :
    cylinderPotential J a c (update G S i w flags) =
      if w = a i then cylinderPotential J a c (update G S i (a i) (fun _ => false)) else 0 := by
  simp only [cylinderPotential, prescriptionsAgree_update_iff G J a S i hi,
    hiJ, true_implies]
  by_cases hw : w = a i <;> simp [hw, update]

omit [Fintype I] [Fintype V] in
lemma cylinderPotential_pay_one (G : Input I V) (J : Finset I)
    (a : I → V) (c : ℝ) (S : State I V) (i : I) (hi : i ∈ S.remaining)
    (hiJ : i ∈ J) :
    c * cylinderPotential J a c (update G S i (a i) (fun _ => false)) =
      cylinderPotential J a c S := by
  have hmem : i ∈ J ∩ S.remaining := Finset.mem_inter.mpr ⟨hiJ, hi⟩
  have hset : J ∩ S.remaining.erase i = (J ∩ S.remaining).erase i := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_erase]
    tauto
  have hcard := Finset.card_erase_add_one hmem
  simp only [cylinderPotential, prescriptionsAgree_update_iff G J a S i hi,
    hiJ, true_implies, and_true]
  by_cases h : PrescriptionsAgree J a S
  · simp only [h, ite_true]
    change c * c ^ (J ∩ S.remaining.erase i).card = c ^ (J ∩ S.remaining).card
    rw [hset, ← hcard, pow_succ]
    ring
  · simp [h]

omit [Fintype I] in
lemma sum_flagsWeight_potential (p : Parameters) (q : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (S : State I V) (i : I) (w : V) :
    (∑ flags : V → Bool, flagsWeight p q G S flags *
      cylinderPotential J a c (update G S i w flags)) =
        cylinderPotential J a c (update G S i w (fun _ => false)) := by
  simp_rw [cylinderPotential_update_flags G J a c S i w _ (fun _ => false)]
  rw [← Finset.sum_mul, sum_flagsWeight, one_mul]

omit [Fintype I] in
lemma sum_drawWeight_potential_le (G : Input I V) (J : Finset I) (a : I → V)
    (c : ℝ) (hc : 0 ≤ c) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty)
    (i : I) (hi : i ∈ S.remaining) (hbound : ((domain G S i).card : ℝ)⁻¹ ≤ c) :
    (∑ w : V, drawWeight G S i w *
      cylinderPotential J a c (update G S i w (fun _ => false))) ≤
        (S.remaining.card : ℝ)⁻¹ * cylinderPotential J a c S := by
  by_cases hiJ : i ∈ J
  · have hsum : (∑ w : V, drawWeight G S i w *
        cylinderPotential J a c (update G S i w (fun _ => false))) =
        ∑ w : V, if w = a i then drawWeight G S i w *
          cylinderPotential J a c (update G S i (a i) (fun _ => false)) else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [cylinderPotential_update_prescribed G J a c S i hi hiJ]
      split_ifs <;> simp
    rw [hsum, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    by_cases ha : a i ∈ domain G S i
    · have hnonneg := cylinderPotential_nonneg J a hc (update G S i (a i) (fun _ => false))
      have hb := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbound hnonneg)
        (by positivity : (0 : ℝ) ≤ (S.remaining.card : ℝ)⁻¹)
      rw [cylinderPotential_pay_one G J a c S i hi hiJ] at hb
      simpa [drawWeight, hi, ha, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hb
    · simp only [drawWeight, hi, ha, and_false, ite_false, zero_mul]
      exact mul_nonneg (by positivity) (cylinderPotential_nonneg J a hc S)
  · simp_rw [cylinderPotential_update_unprescribed G J a c S i hi hiJ]
    rw [← Finset.sum_mul, sum_drawWeight_vertex G S hS hdom, ite_eq_left hi]

lemma sum_noiseWeight_potential_le (p : Parameters) (q : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (hc : 0 ≤ c) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty)
    (hbound : ∀ i ∈ S.remaining, ((domain G S i).card : ℝ)⁻¹ ≤ c) :
    (∑ r : Noise I V, noiseWeight p q G S r *
      cylinderPotential J a c (update G S r.1 r.2.1 r.2.2)) ≤
        cylinderPotential J a c S := by
  simp only [Noise, Fintype.sum_prod_type, noiseWeight, mul_assoc]
  simp_rw [← Finset.mul_sum, sum_flagsWeight_potential]
  calc
    (∑ i : I, ∑ w : V, drawWeight G S i w *
      cylinderPotential J a c (update G S i w (fun _ => false))) ≤
        ∑ i : I, if i ∈ S.remaining then
          (S.remaining.card : ℝ)⁻¹ * cylinderPotential J a c S else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hiR : i ∈ S.remaining
      · rw [ite_eq_left hiR]
        exact sum_drawWeight_potential_le G J a c hc S hS hdom i hiR (hbound i hiR)
      · simp [drawWeight, hiR]
    _ = cylinderPotential J a c S := by
      have hcardS : (S.remaining.card : ℝ) ≠ 0 := by
        exact_mod_cast Finset.card_ne_zero.mpr hS
      rw [← Finset.sum_filter]
      simp [hcardS]

omit [Fintype I] [Fintype V] in
lemma outcomePotential_nonneg (J : Finset I) (a : I → V) {c : ℝ} (hc : 0 ≤ c)
    (out : Option (State I V)) : 0 ≤ outcomePotential J a c out := by
  cases out with
  | none => exact le_rfl
  | some S => exact cylinderPotential_nonneg J a hc S

omit [Fintype I] in
lemma outcomePotential_performedResult_le (q : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (hc : 0 ≤ c) (S : State I V)
    (r : Noise I V) :
    outcomePotential J a c (performedResult q G S r) ≤
      cylinderPotential J a c (update G S r.1 r.2.1 r.2.2) := by
  unfold performedResult
  split_ifs
  · exact le_rfl
  · exact cylinderPotential_nonneg J a hc _

lemma sum_stepWeight_potential_eq (p : Parameters) (q t : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (S : State I V)
    (hp : Precheck p q t G S) :
    (∑ out, stepWeight p q t G S out * outcomePotential J a c out) =
      ∑ r : Noise I V, noiseWeight p q G S r *
        outcomePotential J a c (performedResult q G S r) := by
  simp only [stepWeight, hp, ite_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp_rw [ite_mul, zero_mul]
  simp

lemma sum_stepWeight_potential_le (p : Parameters) (q t : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (hc : 0 ≤ c) (S : State I V)
    (hbound : Precheck p q t G S →
      ∀ i ∈ S.remaining, ((domain G S i).card : ℝ)⁻¹ ≤ c) :
    (∑ out, stepWeight p q t G S out * outcomePotential J a c out) ≤
      cylinderPotential J a c S := by
  by_cases hp : Precheck p q t G S
  · rw [sum_stepWeight_potential_eq p q t G J a c S hp]
    calc
      (∑ r : Noise I V, noiseWeight p q G S r *
        outcomePotential J a c (performedResult q G S r)) ≤
          ∑ r : Noise I V, noiseWeight p q G S r *
            cylinderPotential J a c (update G S r.1 r.2.1 r.2.2) := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left
          (outcomePotential_performedResult_le q G J a c hc S r)
          (noiseWeight_nonnegative_of_precheck p q t G S hp r)
      _ ≤ cylinderPotential J a c S :=
        sum_noiseWeight_potential_le p q G J a c hc S hp.1
          (fun i hi => (hp.2.2.2.1 i hi).1) (hbound hp)
  · simpa [stepWeight, hp, outcomePotential] using cylinderPotential_nonneg J a hc S

lemma sum_transitionWeight_potential_le (p : Parameters) (q t : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ S : State I V, Precheck p q t G S →
      ∀ i ∈ S.remaining, ((domain G S i).card : ℝ)⁻¹ ≤ c)
    (before : Option (State I V)) :
    (∑ out, transitionWeight p q t G before out * outcomePotential J a c out) ≤
      outcomePotential J a c before := by
  cases before with
  | none => simp [transitionWeight, outcomePotential]
  | some S => exact sum_stepWeight_potential_le p q t G J a c hc S (hbound S)

omit [Fintype I] in

lemma domain_reciprocal_le (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (hc : 0 < p.c) (hq : 0 < q)
    (hs : p.smin ≤ p.sizeScale q t) (i : I) (hi : i ∈ S.remaining) :
    ((domain G S i).card : ℝ)⁻¹ ≤ 2 / (p.smin * p.c * q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmin : 0 < p.smin := Real.exp_pos _
  have hbase : 0 < p.smin * p.c * q / 2 := by positivity
  have hbarrier : p.smin * p.c * q / 2 ≤ ((domain G S i).card : ℝ) := by
    calc
      p.smin * p.c * q / 2 ≤ p.sizeScale q t * p.c * q / 2 := by
        gcongr
      _ ≤ _ := (hp.2.2.2.1 i hi).2
  have h := one_div_le_one_div_of_le hbase hbarrier
  simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using h

lemma historyWeight_payoff_le (p : Parameters) (q T : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ t < T, ∀ S : State I V, Precheck p q t G S →
      ∀ i ∈ S.remaining, ((domain G S i).card : ℝ)⁻¹ ≤ c)
    (payoff : Option (State I V) → ℝ)
    (hpayoff : ∀ out, payoff out ≤ outcomePotential J a c out) :
    (∑ out, historyWeight p q G T out * payoff out) ≤ c ^ J.card := by
  let Φ : ℕ → Option (State I V) → ℝ :=
    fun t out => if t ≤ T then outcomePotential J a c out else 0
  have hstep : ∀ t before,
      (∑ out, transitionWeight p q t G before out * Φ (t + 1) out) ≤ Φ t before := by
    intro t before
    by_cases ht : t < T
    · have ht1 : t + 1 ≤ T := ht
      simpa [Φ, ht.le, ht1] using
        sum_transitionWeight_potential_le p q t G J a c hc (hbound t ht) before
    · have ht1 : ¬ t + 1 ≤ T := by omega
      by_cases ht0 : t ≤ T
      · simpa [Φ, ht0, ht1] using outcomePotential_nonneg J a hc before
      · simp [Φ, ht0, ht1]
  have h := FiniteKernelPotential.evolution_payoff_le
    (fun t => transitionWeight p q t G) (historyWeight p q G) Φ payoff
    (fun _ _ => rfl) (transitionWeight_nonnegative p q · G)
    (historyWeight_nonnegative p q G 0) hstep T (by simpa [Φ] using hpayoff)
  simpa [Φ, historyWeight, outcomePotential, cylinderPotential_initial] using h

lemma cylinderConstant_pos (p : Parameters) : 0 < cylinderConstant p :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

lemma main_cost_le_cylinderConstant (p : Parameters) (q : ℕ)
    (hc : 0 < p.c) (hq : 0 < q) :
    2 / (p.smin * p.c * q) ≤ cylinderConstant p / q := by
  have hden : 0 < p.smin * p.c := mul_pos (Real.exp_pos _) hc
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hexp : 1 ≤ Real.exp (1 / 2 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hmain : 2 / (p.smin * p.c) ≤
      2 * Real.exp (1 / 2 : ℝ) / (p.smin * p.c) := by
    apply div_le_div_of_nonneg_right _ hden.le
    linarith
  have hK : 2 / (p.smin * p.c) ≤ cylinderConstant p :=
    hmain.trans (le_max_right _ _)
  simpa only [div_div] using div_le_div_of_nonneg_right hK hqR.le

lemma historyWeight_payoff_source_bound (p : Parameters) (q T : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (hc : 0 < p.c) (hP : 0 ≤ p.Pstar)
    (hq : 0 < q) (hPq : 2 * p.Pstar ≤ q) (hT : T ≤ 3 * q)
    (payoff : Option (State I V) → ℝ)
    (hpayoff : ∀ out, payoff out ≤
      outcomePotential J a (cylinderConstant p / q) out) :
    (∑ out, historyWeight p q G T out * payoff out) ≤
      (cylinderConstant p / q) ^ J.card := by
  apply historyWeight_payoff_le p q T G J a _
    (div_nonneg (cylinderConstant_pos p).le (Nat.cast_nonneg q)) _ payoff hpayoff
  intro t ht S hp i hi
  have hscale : p.smin ≤ p.sizeScale q t := by
    exact (SelectionScales.domain_bounds hP hq hPq (ht.le.trans hT)).1
  exact (domain_reciprocal_le p q t G S hp hc hq hscale i hi).trans
    (main_cost_le_cylinderConstant p q hc hq)

lemma tail_cost_le_cylinderConstant (p : Parameters) (q : ℕ) :
    Real.exp (1 / 2 : ℝ) * (2 / (p.smin * p.c * q)) ≤ cylinderConstant p / q := by
  have h := div_le_div_of_nonneg_right
    (le_max_right 1 (2 * Real.exp (1 / 2 : ℝ) / (p.smin * p.c))) (Nat.cast_nonneg q)
  change Real.exp (1 / 2 : ℝ) * (2 / (p.smin * p.c * q)) ≤
    max 1 (2 * Real.exp (1 / 2 : ℝ) / (p.smin * p.c)) / q
  calc
    _ = (2 * Real.exp (1 / 2 : ℝ) / (p.smin * p.c)) / q := by ring
    _ ≤ _ := h

omit [Fintype I] [Fintype V] in
lemma tail_product_source_bound (p : Parameters) (q : ℕ) (hc : 0 < p.c) (hq : 0 < q)
    (U : Finset I) (D : I → Finset V)
    (hsize : ∀ i ∈ U, p.smin * p.c * q / 2 ≤ ((D i).card : ℝ)) :
    Real.exp ((U.card : ℝ) / 2) * (∏ i ∈ U, ((D i).card : ℝ)⁻¹) ≤
      (cylinderConstant p / q) ^ U.card := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmin : 0 < p.smin := Real.exp_pos _
  have hbase : 0 < p.smin * p.c * q / 2 := by positivity
  have hbound (i : I) (hi : i ∈ U) :
      ((D i).card : ℝ)⁻¹ ≤ 2 / (p.smin * p.c * q) := by
    have h := one_div_le_one_div_of_le hbase (hsize i hi)
    simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using h
  have hprod : (∏ i ∈ U, ((D i).card : ℝ)⁻¹) ≤
      (2 / (p.smin * p.c * q)) ^ U.card := by
    calc
      _ ≤ ∏ _i ∈ U, (2 / (p.smin * p.c * q)) := by
        exact Finset.prod_le_prod (fun index _ => by positivity) hbound
      _ = _ := by simp only [Finset.prod_const]
  have hexp : Real.exp ((U.card : ℝ) / 2) = Real.exp (1 / 2 : ℝ) ^ U.card := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  calc
    _ ≤ Real.exp (1 / 2 : ℝ) ^ U.card *
        (2 / (p.smin * p.c * q)) ^ U.card :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (Real.exp (1 / 2 : ℝ) * (2 / (p.smin * p.c * q))) ^ U.card :=
      (mul_pow _ _ _).symm
    _ ≤ (cylinderConstant p / q) ^ U.card :=
      pow_le_pow_left₀ (by positivity) (tail_cost_le_cylinderConstant p q) _

lemma mainStageWeight_payoff_source_bound (p : Parameters) (q : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (hp : p.Admissible) (hq : 2 ≤ q)
    (hPq : 2 * p.Pstar ≤ q) (hG : GraphBounds G q p.c p.C)
    (payoff : Option (State I V) → ℝ)
    (hpayoff : ∀ out, payoff out ≤
      outcomePotential J a (cylinderConstant p / q) out) :
    (∑ out, mainStageWeight p q G out * payoff out) ≤
      (cylinderConstant p / q) ^ J.card := by
  have hP : 0 ≤ p.Pstar := by
    unfold Parameters.Pstar
    have hc := hp.1
    have hC := hp.2.1
    positivity
  have hT : p.lastMainTime q (Fintype.card I) ≤ 3 * q := by
    calc
      p.lastMainTime q (Fintype.card I) ≤ Fintype.card I := Nat.sub_le _ _
      _ = 2 * (q + 1) := hG.1
      _ ≤ 3 * q := by omega
  exact historyWeight_payoff_source_bound p q _ G J a hp.1 hP (by omega)
    hPq hT payoff hpayoff

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionState
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotMeasurableSingletonClass _root_.OAI.Balanced.Selection.Process.snapshotMeasurableSpace _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

private theorem exists_positive_of_sum_positive {α : Type*} [Fintype α]
    (f : α → ℝ) (h : 0 < ∑ a, f a) : ∃ a, 0 < f a := by
  by_contra hn
  push Not at hn
  exact (not_lt_of_ge (Finset.sum_nonpos (fun a _ => hn a))) h

theorem initialState_invariant (G : Input I V) : StateInvariant G initialState := by
  simp [StateInvariant, initialState]

omit [Fintype I] [Fintype V] in
theorem update_invariant (G : Input I V) (S : State I V) (hS : StateInvariant G S)
    (i : I) (w : V) (_hi : i ∈ S.remaining) (hw : w ∈ domain G S i)
    (flags : V → Bool) : StateInvariant G (update G S i w flags) := by
  have hwalive : w ∈ S.alive := (Finset.mem_filter.mp hw).1
  have hwslot : G.slot w = i := (Finset.mem_filter.mp hw).2
  have halive {v : V} (hv : v ∈ (update G S i w flags).alive) :
      v ∈ S.alive ∧ ¬ G.graph.Adj w v := by
    have hsurv := (Finset.mem_filter.mp hv).1
    have hc := Finset.mem_filter.mp hsurv
    exact ⟨(Finset.mem_filter.mp hc.1).1, hc.2.1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hsurv := (Finset.mem_filter.mp hv).1
    have hneq := (Finset.mem_filter.mp hv).2
    have hcurrent := (Finset.mem_filter.mp hsurv).1
    exact Finset.mem_erase.mpr ⟨hneq, (Finset.mem_filter.mp hcurrent).2⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simp [update]
    · simp [update, hj, hS.2.1 j]
  · intro j v hrec
    by_cases hj : j = i
    · subst j
      have heq : w = v := by simpa only [update, Function.update_self, Option.some.injEq] using hrec
      simpa only [← heq] using hwslot
    · exact hS.2.2.1 j v (by simpa [update, hj] using hrec)
  · intro j k v u hjrec hkrec hjk
    by_cases hj : j = i
    · subst j
      have hk : k ≠ i := Ne.symm hjk
      have hv : w = v := by simpa only [update, Function.update_self, Option.some.injEq] using hjrec
      have hkold : S.recorded k = some u := by simpa [update, hk] using hkrec
      intro hadj
      exact hS.2.2.2.2 k u hkold w hwalive (by simpa only [hv] using hadj.symm)
    · by_cases hk : k = i
      · subst k
        have hu : w = u := by simpa only [update, Function.update_self, Option.some.injEq] using hkrec
        have hjold : S.recorded j = some v := by simpa [update, hj] using hjrec
        simpa only [hu] using hS.2.2.2.2 j v hjold w hwalive
      · exact hS.2.2.2.1 j k v u (by simpa [update, hj] using hjrec)
          (by simpa [update, hk] using hkrec) hjk
  · intro j u hrec v hv
    by_cases hj : j = i
    · subst j
      have hu : w = u := by simpa only [update, Function.update_self, Option.some.injEq] using hrec
      simpa only [hu] using (halive hv).2
    · exact hS.2.2.2.2 j u (by simpa [update, hj] using hrec) v (halive hv).1

theorem positive_stepWeight_exists_update (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V)
    (hpos : 0 < stepWeight p q t G S (some S')) :
    ∃ r : Noise I V, r.1 ∈ S.remaining ∧ r.2.1 ∈ domain G S r.1 ∧
      update G S r.1 r.2.1 r.2.2 = S' := by
  by_cases hp : Precheck p q t G S
  · simp only [stepWeight, hp, ite_true] at hpos
    obtain ⟨r, hr⟩ := exists_positive_of_sum_positive _ hpos
    split at hr
    · rename_i hresult
      have hvalid : r.1 ∈ S.remaining ∧ r.2.1 ∈ domain G S r.1 := by
        by_contra h
        simp only [noiseWeight, drawWeight, h, ite_false, zero_mul, lt_self_iff_false] at hr
      have hup : update G S r.1 r.2.1 r.2.2 = S' := by
        unfold performedResult at hresult
        split at hresult
        · exact Option.some.inj hresult
        · contradiction
      exact ⟨r, hvalid.1, hvalid.2, hup⟩
    · exact False.elim (lt_irrefl 0 hr)
  · simp [stepWeight, hp] at hpos

theorem positive_stepWeight_invariant (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V) (hS : StateInvariant G S)
    (hpos : 0 < stepWeight p q t G S (some S')) : StateInvariant G S' := by
  obtain ⟨r, hi, hw, hup⟩ := positive_stepWeight_exists_update p q t G S S' hpos
  rw [← hup]
  exact update_invariant G S hS r.1 r.2.1 hi hw r.2.2

theorem positive_historyWeight_invariant (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (S : State I V) (hpos : 0 < historyWeight p q G t (some S)) :
    StateInvariant G S := by
  induction t generalizing S with
  | zero =>
    simp only [historyWeight] at hpos
    split at hpos
    · rename_i h
      have heq : S = initialState := Option.some.inj h
      simpa only [heq] using initialState_invariant G
    · exact False.elim (lt_irrefl 0 hpos)
  | succ t ih =>
    simp only [historyWeight] at hpos
    obtain ⟨before, hb⟩ := exists_positive_of_sum_positive _ hpos
    have hweights := (mul_pos_iff.mp hb).resolve_right (by
      intro hneg
      exact (not_lt_of_ge (historyWeight_nonnegative p q G t before)) hneg.1)
    cases before with
    | none => simp [transitionWeight] at hweights
    | some S₀ =>
      exact positive_stepWeight_invariant p q t G S₀ S (ih S₀ hweights.1) hweights.2

theorem positive_stepWeight_card (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V) (hpos : 0 < stepWeight p q t G S (some S')) :
    S'.remaining.card + 1 = S.remaining.card := by
  obtain ⟨r, hi, _, hup⟩ := positive_stepWeight_exists_update p q t G S S' hpos
  rw [← hup]
  exact Finset.card_erase_add_one hi

theorem sum_snapshotWeight_state (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Snapshot I V) (out : Option (State I V)) :
    (∑ draw, snapshotWeight p q t G before (out, draw)) =
      transitionWeight p q t G before.1 out := by
  rw [transitionWeight_eq_draw_pushforward]
  apply Finset.sum_congr rfl
  intro draw _
  simp only [snapshotWeight, eq_comm]

theorem positive_snapshotWeight_transition (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) (hp : 0 < snapshotWeight p q t G before out) :
    0 < transitionWeight p q t G before.1 out.1 := by
  rw [← sum_snapshotWeight_state p q t G before out.1]
  apply hp.trans_le
  exact Finset.single_le_sum (fun draw _ =>
    snapshotWeight_nonnegative p q t G before (out.1, draw)) (Finset.mem_univ out.2)

theorem positive_snapshotWeight_invariant (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V) (draw draw' : Option (Noise I V))
    (hS : StateInvariant G S)
    (hp : 0 < snapshotWeight p q t G (some S, draw) (some S', draw')) :
    StateInvariant G S' := by
  exact positive_stepWeight_invariant p q t G S S' hS
    (positive_snapshotWeight_transition p q t G _ _ hp)

theorem positive_snapshotWeight_card (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V) (draw draw' : Option (Noise I V))
    (hp : 0 < snapshotWeight p q t G (some S, draw) (some S', draw')) :
    S'.remaining.card + 1 = S.remaining.card := by
  exact positive_stepWeight_card p q t G S S'
    (positive_snapshotWeight_transition p q t G _ _ hp)

omit [Fintype I] in

theorem snapshotWeight_none_some (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (draw draw' : Option (Noise I V)) :
    snapshotWeight p q t G (none, draw) (some S, draw') = 0 := by
  simp [snapshotWeight, advance]

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionTailCompletion
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process.Tail

variable {I V : Type*} [Fintype I] [Fintype V]

theorem successMass_completionOutputLaw (G : Input I V) (S : State I V) (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty) :
    successMass (completionOutputLaw G S fixed hslot hind hcross hG) = 1 :=
  sum_pmf_real _

end Balanced.Selection.Process.Tail

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionFinalLaw
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in

theorem tailCheck_iff (G : Input I V) (S : State I V) :
    TailCheck G S ↔
      (∀ i ∈ S.remaining, 3 ≤ (domain G S i).card) ∧
      (∀ v ∈ currentVertices G S, ∀ i ∈ S.remaining,
        8 * degree G S v ≤ (domain G S i).card) := by
  constructor
  · rintro ⟨L, Δ, hL, hs, hd, hsp⟩
    exact ⟨fun i hi => hL.trans (hs i hi), fun v hv i hi =>
      (Nat.mul_le_mul_left 8 (hd v hv)).trans (hsp.trans (hs i hi))⟩
  · rintro ⟨hs, hd⟩
    let Δ := (currentVertices G S).sup (degree G S)
    refine ⟨max 3 (8 * Δ), Δ, le_max_left _ _, ?_, ?_, le_max_right _ _⟩
    · intro i hi
      apply max_le (hs i hi)
      have hdeg : Δ ≤ (domain G S i).card / 8 := by
        apply Finset.sup_le
        intro v hv
        exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa [Nat.mul_comm] using hd v hv i hi)
      exact (Nat.mul_le_mul_left 8 hdeg).trans (by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self (domain G S i).card 8)
    · intro v hv
      exact Finset.le_sup hv

section Nonempty
variable [Nonempty V]

theorem successMass_terminalLaw (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) (S : State I V) :
    successMass (terminalLaw G hno S) =
      if StateInvariant G S ∧ TailCheck G S then 1 else 0 := by
  unfold terminalLaw
  split
  · exact Tail.successMass_completionOutputLaw _ _ _ _ _ _ _
  · exact successMass_failureLaw G

theorem successMass_sourceTerminalLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) (S : State I V) :
    successMass (sourceTerminalLaw p q G hno S) =
      if StateInvariant G S ∧ SourceTailCheck p q G S then 1 else 0 := by
  by_cases ht : SourceTailCheck p q G S
  · simp only [sourceTerminalLaw, ht, ite_true, successMass_terminalLaw]
    simp only [ht.1, and_true]
  · simp [sourceTerminalLaw, ht]

theorem successMass_finalLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) :
    successMass (finalLaw p q G hno) =
      ∑ S : State I V, if SourceTailCheck p q G S then mainStageWeight p q G (some S) else 0 := by
  have he : successMass (finalLaw p q G hno) =
      ∑ out, mainStageWeight p q G out * successMass (sourceTerminalOutcomeLaw p q G hno out) := by
    unfold successMass finalLaw
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  rw [he, Fintype.sum_option]
  simp only [sourceTerminalOutcomeLaw, successMass_failureLaw, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [successMass_sourceTerminalLaw]
  by_cases hS : StateInvariant G S
  · by_cases ht : SourceTailCheck p q G S <;> simp [hS, ht]
  · have hz : mainStageWeight p q G (some S) = 0 := by
      apply le_antisymm _ (historyWeight_nonnegative p q G _ _)
      by_contra hn
      exact hS (positive_historyWeight_invariant p q G _ S (lt_of_not_ge hn))
    simp [hS, hz]

theorem cylinderMass_finalLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (J : Finset I) (prescribed : I → V) :
    cylinderMass (finalLaw p q G hno) J prescribed =
      ∑ out, mainStageWeight p q G out *
        cylinderMass (sourceTerminalOutcomeLaw p q G hno out) J prescribed := by
  unfold cylinderMass finalLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

end Nonempty

theorem graphBounds_vertex_nonempty (G : Input I V) (q : ℕ) (c C : ℝ)
    (hc : 0 < c) (hq : 0 < q) (hG : GraphBounds G q c C) : Nonempty V := by
  have hi : 0 < Fintype.card I := by rw [hG.1]; omega
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp hi
  have hs : 0 < ((slotVertices G i).card : ℝ) :=
    (mul_pos hc (by exact_mod_cast hq)).trans_le (hG.2.2.1 i).1
  have hn : (slotVertices G i).Nonempty := Finset.card_pos.mp (by exact_mod_cast hs)
  obtain ⟨v, _⟩ := hn
  exact ⟨v⟩

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

theorem condExp_snapshot_step (p : Parameters) (q : ℕ) (G : Input I V) (t : ℕ)
    (f : FiniteHistory.Prefix (Snapshot I V) t → Snapshot I V → ℝ) :
    (snapshotPathLaw p q G)[FiniteHistory.stepObservable t f | snapshotFiltration t]
      =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ out, snapshotWeight p q t G (ω t) out * f (frestrictLe t ω) out := by
  have h := FiniteHistory.condExp_stepObservable
    (fun n => snapshotPMF p q n G) (initialSnapshot (I := I) (V := V)) t f
  simpa only [snapshotPathLaw, snapshotFiltration, snapshotPMF_apply_real] using h

theorem sum_snapshotWeight_response (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Snapshot I V) (f : Snapshot I V → ℝ) :
    (∑ out, snapshotWeight p q t G before out * f out) =
      ∑ draw, drawStepWeight p q t G before.1 draw *
        f (advance q G before.1 draw, draw) := by
  simp only [Snapshot, Fintype.sum_prod_type, snapshotWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro draw _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem condExp_retained_draw (p : Parameters) (q : ℕ) (G : Input I V) (t : ℕ)
    (f : FiniteHistory.Prefix (Snapshot I V) t → Option (Noise I V) → ℝ) :
    (snapshotPathLaw p q G)[
      FiniteHistory.stepObservable t (fun h out => f h out.2) | snapshotFiltration t]
      =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ draw, drawStepWeight p q t G (ω t).1 draw *
          f (frestrictLe t ω) draw := by
  have h := condExp_snapshot_step p q G t (fun h out => f h out.2)
  filter_upwards [h] with ω hω
  rw [hω, sum_snapshotWeight_response]

theorem sum_drawStepWeight_of_precheck (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (f : Option (Noise I V) → ℝ) :
    (∑ draw, drawStepWeight p q t G (some S) draw * f draw) =
      ∑ r : Noise I V, noiseWeight p q G S r * f (some r) := by
  simp [Fintype.sum_option, drawStepWeight, hp]

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionHistoryInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter

namespace Balanced.Selection.Process

variable {I V : Type*} [Fintype I] [Fintype V]

theorem ae_snapshot_state_invariant (p : Parameters) (q : ℕ) (G : Input I V) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t S, (ω t).1 = some S →
      StateInvariant G S ∧ S.remaining.card + t = Fintype.card I := by
  classical
  apply FiniteHistory.ae_all_invariant (fun t => snapshotPMF p q t G)
    initialSnapshot
    (fun t snap => ∀ S, snap.1 = some S →
      StateInvariant G S ∧ S.remaining.card + t = Fintype.card I)
  · intro S hS
    have heq : S = initialState := (Option.some.inj hS).symm
    subst S
    exact ⟨initialState_invariant G, by simp [initialState]⟩
  · intro t before out hpos hbefore S hout
    have hp : 0 < snapshotWeight p q t G before out := by
      have hn : snapshotWeight p q t G before out ≠ 0 := by
        intro hz
        apply hpos
        change ENNReal.ofReal (snapshotWeight p q t G before out) = 0
        rw [hz, ENNReal.ofReal_zero]
      exact lt_of_le_of_ne (snapshotWeight_nonnegative p q t G before out) (Ne.symm hn)
    obtain ⟨before, draw⟩ := before
    obtain ⟨out, draw'⟩ := out
    dsimp only at hout
    subst out
    cases before with
    | none =>
        rw [snapshotWeight_none_some] at hp
        exact False.elim (lt_irrefl 0 hp)
    | some S₀ =>
        obtain ⟨hinv, hcard⟩ := hbefore S₀ rfl
        refine ⟨positive_snapshotWeight_invariant p q t G S₀ S draw draw' hinv hp, ?_⟩
        have hstep := positive_snapshotWeight_card p q t G S₀ S draw draw' hp
        omega

theorem ae_snapshot_remaining_card (p : Parameters) (q : ℕ) (G : Input I V) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t S, (ω t).1 = some S →
      S.remaining.card = Fintype.card I - t := by
  filter_upwards [ae_snapshot_state_invariant p q G] with ω hω
  intro t S hS
  have h := (hω t S hS).2
  omega

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionProcessScales
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process.Parameters

noncomputable section

variable {p : Parameters}

theorem Pstar_pos (hp : p.Admissible) : 0 < p.Pstar := by
  have hc := hp.1
  have hC := hp.2.1
  unfold Pstar
  positivity

theorem a_bounds (hp : p.Admissible) : 0 < p.a ∧ p.a < 1 := by
  exact ⟨hp.2.2.2.2.1, lt_of_lt_of_le hp.2.2.2.2.2 (min_le_left _ _)⟩

theorem tailSlots_le_order (hp : p.Admissible) (q : ℕ) : p.tailSlots q ≤ q := by
  unfold tailSlots
  apply Nat.ceil_le.mpr
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  nlinarith [(a_bounds hp).2]

theorem remaining_ge (hp : p.Admissible) {q n t : ℕ} (hqn : q ≤ n)
    (ht : t ≤ p.lastMainTime q n) : p.a * q ≤ ((n - t : ℕ) : ℝ) := by
  have htail : p.tailSlots q ≤ n := (tailSlots_le_order hp q).trans hqn
  have hrem : p.tailSlots q ≤ n - t := by
    unfold lastMainTime at ht
    omega
  exact (Nat.le_ceil (p.a * q)).trans (by exact_mod_cast hrem)

theorem source_scale_bounds (hp : p.Admissible) {q n t : ℕ}
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hn : n = 2 * (q + 1))
    (ht : t ≤ p.lastMainTime q n) :
    p.smin ≤ p.sizeScale q t ∧ p.sizeScale q t ≤ 1 ∧
      p.smin * p.a / 3 ≤ p.degreeScale q n t ∧ p.degreeScale q n t ≤ 1 := by
  have hqpos : 0 < q := by omega
  have hnpos : 0 < n := by omega
  have hnq : n ≤ 3 * q := by omega
  have hqn : q ≤ n := by omega
  have htn : t ≤ n := ht.trans (Nat.sub_le _ _)
  obtain ⟨hslo, hshi⟩ := SelectionScales.domain_bounds (Pstar_pos hp).le hqpos hPq
    (htn.trans hnq)
  obtain ⟨hblo, hbhi⟩ := SelectionScales.degree_bounds (Pstar_pos hp).le
    (a_bounds hp).1.le hqpos hnpos hPq hnq htn (remaining_ge hp hqn ht)
  exact ⟨hslo, hshi, hblo, hbhi⟩

theorem exists_admissible (c C c₀ : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hc₀ : 0 < c₀) (hc₀le : c₀ ≤ 1) :
    ∃ p : Parameters, p.c = c ∧ p.C = C ∧ p.c₀ = c₀ ∧ p.Admissible := by
  let p₀ : Parameters := ⟨c, C, c₀, 0⟩
  let m : ℝ := min 1 (min (p₀.rho / 2) (c / (100 * (C + 1))))
  have hrho : 0 < p₀.rho := by
    change 0 < c₀ * Real.exp (-6 * p₀.Bstar) / 4
    positivity
  have hm : 0 < m := by
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  refine ⟨⟨c, C, c₀, m / 2⟩, rfl, rfl, rfl, ?_⟩
  change 0 < c ∧ 0 < C ∧ 0 < c₀ ∧ c₀ ≤ 1 ∧ 0 < m / 2 ∧ m / 2 < m
  exact ⟨hc, hC, hc₀, hc₀le, by linarith, by linarith⟩

theorem eventually_scale_regime (p : Parameters) :
    ∀ᶠ q : ℕ in Filter.atTop, 2 ≤ q ∧ 2 * p.Pstar ≤ q := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * p.Pstar)
  apply Filter.eventually_atTop.mpr
  refine ⟨max 2 N, fun q hq => ?_⟩
  constructor
  · exact (le_max_left _ _).trans hq
  · have hNq : N ≤ q := (le_max_right _ _).trans hq
    exact hN.trans (by exact_mod_cast hNq)

theorem rho_pos (hp : p.Admissible) : 0 < p.rho := by
  exact div_pos (mul_pos hp.2.2.1 (Real.exp_pos _)) (by norm_num)

end
end Balanced.Selection.Process.Parameters

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionPrecheck
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Real
open scoped BigOperators Topology

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in

theorem degree_eq_sum_domain_neighbors (G : Input I V) (S : State I V) (v : V) :
    (∑ i ∈ S.remaining, ((neighbors G v) ∩ domain G S i).card) = degree G S v := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    ((neighbors G v) ∩ S.alive) S.remaining G.slot
  have hleft (i : I) : ((neighbors G v) ∩ S.alive).filter (fun w => G.slot w = i) =
      (neighbors G v) ∩ domain G S i := by
    ext w
    simp [domain, and_assoc]
  have hright : ((neighbors G v) ∩ S.alive).filter (fun w => G.slot w ∈ S.remaining) =
      (neighbors G v) ∩ currentVertices G S := by
    ext w
    simp [currentVertices, and_assoc]
  simpa only [hleft, hright, degree] using h

omit [Fintype I] in

theorem hazard_le_degree_div (G : Input I V) (S : State I V) (v : V)
    {m : ℝ} (hS : S.remaining.Nonempty) (hm : 0 < m)
    (hL : ∀ i ∈ S.remaining, m ≤ ((domain G S i).card : ℝ)) :
    hazard G S v ≤ (degree G S v : ℝ) / ((S.remaining.card : ℝ) * m) := by
  apply SelectionBarriers.finite_hazard_le S.remaining
    (fun i => ((domain G S i).card : ℝ))
    (fun i => (((neighbors G v) ∩ domain G S i).card : ℝ))
    (by exact_mod_cast Finset.card_pos.mpr hS) hm hL
    (fun _ _ => Nat.cast_nonneg _)
  exact le_of_eq (by exact_mod_cast degree_eq_sum_domain_neighbors G S v)

theorem precheck_of_concentration (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 0 < q) (halpha : p.Pstar < (q : ℝ))
    (hh : p.a * q ≤ (S.remaining.card : ℝ))
    (hcard : S.remaining.card = Fintype.card I - t)
    (hscale : p.smin ≤ p.sizeScale q t)
    (he₁ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q)
    (hL : ∀ i ∈ S.remaining,
      |((domain G S i).card : ℝ) - p.sizeScale q t * (slotVertices G i).card| ≤
        (q : ℝ) ^ ((4 : ℝ) / 5))
    (hD : ∀ v ∈ currentVertices G S,
      (degree G S v : ℝ) ≤ p.degreeScale q (Fintype.card I) t * (neighbors G v).card +
        (q : ℝ) ^ ((4 : ℝ) / 5)) :
    Precheck p q t G S := by
  rcases hp with ⟨hc, hC, hc₀, hc₀', ha, ha'⟩
  rcases hG with ⟨hcardI, hno, hslots, hdegrees, hrest⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmin : 0 < p.smin := Real.exp_pos _
  have hs : 0 < p.sizeScale q t := hsmin.trans_le hscale
  have hhR : (0 : ℝ) < S.remaining.card := (mul_pos ha hqR).trans_le hh
  have hS : S.remaining.Nonempty := Finset.card_pos.mp (by exact_mod_cast hhR)
  have hP : 0 < p.Pstar := by unfold Parameters.Pstar; positivity
  have hqn : (q : ℝ) ≤ Fintype.card I := by rw [hcardI]; norm_num; nlinarith
  have hm : 0 < p.sizeScale q t * p.c * q - (q : ℝ) ^ ((4 : ℝ) / 5) := by
    have hsc : p.smin * p.c * q ≤ p.sizeScale q t * p.c * q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscale hc.le) hqR.le
    have hpos : 0 < p.sizeScale q t * p.c * q := by positivity
    linarith
  have hlow (i : I) (hi : i ∈ S.remaining) :
      p.sizeScale q t * p.c * q - (q : ℝ) ^ ((4 : ℝ) / 5) ≤
        ((domain G S i).card : ℝ) := by
    have hinit := mul_le_mul_of_nonneg_left (hslots i).1 hs.le
    have hhL := (abs_le.mp (hL i hi)).1
    nlinarith
  refine ⟨hS, div_nonneg hP.le hqR.le, (div_lt_one hqR).2 halpha, ?_, ?_⟩
  · intro i hi
    constructor
    · exact Finset.card_pos.mp (by exact_mod_cast hm.trans_le (hlow i hi))
    · exact SelectionBarriers.domain_barrier hscale hc hqR he₁ (hslots i).1
        (hL i hi) hsmin
  · intro v hv
    have hdegree : (degree G S v : ℝ) ≤
        p.sizeScale q t * ((S.remaining.card : ℝ) / Fintype.card I) * p.C * q +
          (q : ℝ) ^ ((4 : ℝ) / 5) := by
      have hscale0 : 0 ≤ p.degreeScale q (Fintype.card I) t := by
        unfold Parameters.degreeScale
        positivity
      have hhdeg := mul_le_mul_of_nonneg_left (hdegrees v) hscale0
      have hd := (hD v hv).trans (add_le_add hhdeg le_rfl)
      have hid : p.degreeScale q (Fintype.card I) t * (p.C * q) =
          p.sizeScale q t * ((S.remaining.card : ℝ) / Fintype.card I) * p.C * q := by
        rw [Parameters.degreeScale, ← hcard]
        ring
      rwa [hid] at hd
    calc
      hazard G S v ≤ (degree G S v : ℝ) /
          ((S.remaining.card : ℝ) * (p.sizeScale q t * p.c * q -
            (q : ℝ) ^ ((4 : ℝ) / 5))) := hazard_le_degree_div G S v hS hm hlow
      _ ≤ (p.sizeScale q t * ((S.remaining.card : ℝ) / Fintype.card I) * p.C * q +
            (q : ℝ) ^ ((4 : ℝ) / 5)) /
          ((S.remaining.card : ℝ) * (p.sizeScale q t * p.c * q -
            (q : ℝ) ^ ((4 : ℝ) / 5))) :=
        div_le_div_of_nonneg_right hdegree (mul_nonneg hhR.le hm.le)
      _ ≤ (2 * p.C / p.c + 2) / q :=
        SelectionBarriers.hazard_barrier_arithmetic hqR hqn ha hh hsmin hscale hc hC.le he₁ he₂
      _ ≤ p.alpha q := by
        unfold Parameters.alpha Parameters.Pstar
        apply div_le_div_of_nonneg_right _ hqR.le
        exact add_le_add (div_le_div_of_nonneg_right (by linarith) hc.le) (by norm_num)

omit [Fintype I] [Fintype V] in

theorem exists_precheck_threshold (p : Parameters) (hp : p.Admissible) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      0 < q ∧ p.Pstar < (q : ℝ) ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2 ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q := by
  have hb := SelectionBarriers.eventually_selection_error_budgets (smin := p.smin)
    hp.2.2.2.2.1 (Real.exp_pos _) hp.1
  have hlarge : ∀ᶠ q : ℕ in atTop, p.Pstar < (q : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop p.Pstar)
  have hconditions : ∀ᶠ q : ℕ in atTop,
      0 < q ∧ p.Pstar < (q : ℝ) ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2 ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q := by
    filter_upwards [hb, hlarge, eventually_ge_atTop 1] with q hb hl hq
    exact ⟨by omega, hl, hb⟩
  exact eventually_atTop.mp hconditions

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionTailCheck
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Real
open scoped BigOperators Topology

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

theorem Parameters.small_tail_product (p : Parameters) (hp : p.Admissible) :
    p.a * p.C ≤ p.c / 100 := by
  rcases hp with ⟨hc, hC, hc₀, hc₀', ha, ha'⟩
  have hb : p.a < p.c / (100 * (p.C + 1)) :=
    (lt_min_iff.mp (lt_min_iff.mp ha').2).2
  have hden : 0 < 100 * (p.C + 1) := by positivity
  have hmul := (lt_div_iff₀ hden).mp hb
  nlinarith

theorem Parameters.tailSlots_le_twice (p : Parameters) (q : ℕ)
    (haq : 1 ≤ p.a * q) :
    (p.tailSlots q : ℝ) ≤ 2 * p.a * q := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ p.a * q by linarith)
  unfold Parameters.tailSlots
  linarith

variable {I V : Type*} [Fintype I] [Fintype V]

theorem tail_check_of_concentration (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 0 < q) (hcard : S.remaining.card = Fintype.card I - t)
    (hsmall : (S.remaining.card : ℝ) ≤ 2 * p.a * q)
    (hscale : p.smin ≤ p.sizeScale q t)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (hL : ∀ i ∈ S.remaining,
      |((domain G S i).card : ℝ) - p.sizeScale q t * (slotVertices G i).card| ≤
        (q : ℝ) ^ ((4 : ℝ) / 5))
    (hD : ∀ v ∈ currentVertices G S,
      (degree G S v : ℝ) ≤ p.degreeScale q (Fintype.card I) t * (neighbors G v).card +
        (q : ℝ) ^ ((4 : ℝ) / 5)) :
    (∀ i ∈ S.remaining, 3 ≤ (domain G S i).card) ∧
    (∀ v ∈ currentVertices G S, ∀ i ∈ S.remaining,
      8 * (degree G S v : ℝ) ≤ ((domain G S i).card : ℝ)) := by
  have hac := p.small_tail_product hp
  rcases hp with ⟨hc, hC, hc₀, hc₀', ha, ha'⟩
  rcases hG with ⟨hcardI, hno, hslots, hdegrees, hrest⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmin : 0 < p.smin := Real.exp_pos _
  have hs : 0 < p.sizeScale q t := hsmin.trans_le hscale
  have hqn : (q : ℝ) ≤ Fintype.card I := by rw [hcardI]; norm_num; nlinarith
  have hn : (0 : ℝ) < Fintype.card I := hqR.trans_le hqn
  have hsc : p.smin * p.c * q ≤ p.sizeScale q t * p.c * q :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscale hc.le) hqR.le
  have he' : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.sizeScale q t * p.c * q / 100 := by
    linarith
  have hlow (i : I) (hi : i ∈ S.remaining) :
      p.sizeScale q t * p.c * q / 2 ≤ ((domain G S i).card : ℝ) :=
    SelectionBarriers.domain_barrier hscale hc hqR (by linarith) (hslots i).1
      (hL i hi) hsmin
  constructor
  · intro i hi
    have h := hlow i hi
    have : (3 : ℝ) ≤ (domain G S i).card := by linarith
    exact_mod_cast this
  · intro v hv i hi
    have hratio : (S.remaining.card : ℝ) / Fintype.card I ≤ 2 * p.a := by
      apply (div_le_iff₀ hn).2
      exact hsmall.trans (mul_le_mul_of_nonneg_left hqn (by positivity))
    have hdegree : (degree G S v : ℝ) ≤
        p.sizeScale q t * ((S.remaining.card : ℝ) / Fintype.card I) * p.C * q +
          (q : ℝ) ^ ((4 : ℝ) / 5) := by
      have hscale0 : 0 ≤ p.degreeScale q (Fintype.card I) t := by
        unfold Parameters.degreeScale
        positivity
      have hhdeg := mul_le_mul_of_nonneg_left (hdegrees v) hscale0
      have hd := (hD v hv).trans (add_le_add hhdeg le_rfl)
      have hid : p.degreeScale q (Fintype.card I) t * (p.C * q) =
          p.sizeScale q t * ((S.remaining.card : ℝ) / Fintype.card I) * p.C * q := by
        rw [Parameters.degreeScale, ← hcard]
        ring
      rwa [hid] at hd
    have hratio' : p.sizeScale q t * ((S.remaining.card : ℝ) / Fintype.card I) * p.C * q ≤
        p.sizeScale q t * (2 * p.a) * p.C * q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio hs.le) hC.le) hqR.le
    have hmain : p.sizeScale q t * (2 * p.a) * p.C * q ≤
        p.sizeScale q t * p.c * q / 50 := by
      have h := mul_le_mul_of_nonneg_left hac
        (show 0 ≤ 2 * p.sizeScale q t * q by positivity)
      nlinarith
    have hdom := hlow i hi
    linarith

theorem exists_tail_check_threshold (p : Parameters) (hp : p.Admissible) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      0 < q ∧ (p.tailSlots q : ℝ) ≤ 2 * p.a * q ∧
      6 ≤ p.smin * p.c * q ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100 := by
  have ha := hp.2.2.2.2.1
  have hc := hp.1
  have hsmin : 0 < p.smin := Real.exp_pos _
  have he := SelectionBarriers.eventually_selection_error_le
    (δ := p.smin * p.c / 100) (by positivity)
  have hq₁ : ∀ᶠ q : ℕ in atTop, 1 / p.a ≤ (q : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 / p.a))
  have hq₂ : ∀ᶠ q : ℕ in atTop, 6 / (p.smin * p.c) ≤ (q : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (6 / (p.smin * p.c)))
  apply eventually_atTop.mp
  filter_upwards [he, hq₁, hq₂, eventually_ge_atTop 1] with q he hq₁ hq₂ hq
  have haq : 1 ≤ p.a * q := by
    have h := (div_le_iff₀ ha).mp hq₁
    nlinarith
  have hlarge : 6 ≤ p.smin * p.c * q := by
    have h := (div_le_iff₀ (mul_pos hsmin hc)).mp hq₂
    nlinarith
  refine ⟨by omega, p.tailSlots_le_twice q haq, hlarge, ?_⟩
  convert he using 1 <;> first | rfl | ring

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionFirstAbort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process.FirstAbort

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

theorem ae_supportedPath (p : Parameters) (q : ℕ) (G : Input I V) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, SupportedPath p q G ω := by
  filter_upwards [FiniteHistory.ae_initial_state (fun t => snapshotPMF p q t G)
      (initialSnapshot (I := I) (V := V)),
    ae_all_iff.2 (fun t => FiniteHistory.ae_step_support
      (fun n => snapshotPMF p q n G) (initialSnapshot (I := I) (V := V)) t)]
      with ω hzero hsupport
  refine ⟨hzero, fun t => ?_⟩
  have hn : snapshotWeight p q t G (ω t) (ω (t + 1)) ≠ 0 := by
    intro hz
    apply hsupport t
    change ENNReal.ofReal (snapshotWeight p q t G (ω t) (ω (t + 1))) = 0
    rw [hz, ENNReal.ofReal_zero]
  exact lt_of_le_of_ne (snapshotWeight_nonnegative p q t G _ _) (Ne.symm hn)

omit [Fintype I] in

theorem next_state_of_checks (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) (S : State I V)
    (hpos : 0 < snapshotWeight p q t G before out)
    (hbefore : before.1 = some S) (hpre : Precheck p q t G S)
    (hpost : ∀ r, out.2 = some r → Postcheck q G S r.2.1 r.2.2) :
    ∃ S', out.1 = some S' := by
  have heq : out.1 = advance q G before.1 out.2 := by
    by_contra hn
    simp [snapshotWeight, hn] at hpos
  have hw : 0 < drawStepWeight p q t G before.1 out.2 := by
    simpa only [snapshotWeight, heq, ite_true] using hpos
  cases hdraw : out.2 with
  | none => simp [hbefore, drawStepWeight, hpre, hdraw] at hw
  | some r =>
      refine ⟨update G S r.1 r.2.1 r.2.2, ?_⟩
      simpa only [hbefore, hdraw, advance, performedResult, hpost r hdraw, ite_true]
        using heq

theorem survives_of_checks (p : Parameters) (q : ℕ) (G : Input I V) (T : ℕ)
    (ω : FiniteHistory.Path (Snapshot I V))
    (hsupport : SupportedPath p q G ω)
    (hpre : ∀ t < T, ∀ S, (ω t).1 = some S → Precheck p q t G S)
    (hpost : NoPostAbort q G T ω) :
    ∀ t ≤ T, ∃ S, (ω t).1 = some S := by
  intro t ht
  induction t with
  | zero => exact ⟨initialState, by rw [hsupport.1]; rfl⟩
  | succ t ih =>
      obtain ⟨S, hS⟩ := ih (by omega)
      exact next_state_of_checks p q t G _ _ S (hsupport.2 t) hS
        (hpre t (by omega) S hS) (fun r hr => hpost t (by omega) S r hS hr)

theorem precheck_of_stateConcentration (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t ≤ p.lastMainTime q (Fintype.card I))
    (hcard : S.remaining.card = Fintype.card I - t)
    (he₁ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q)
    (hconc : StateConcentration p q G t S) : Precheck p q t G S := by
  have hqn : q ≤ Fintype.card I := by rw [hG.1]; omega
  have hh := Parameters.remaining_ge hp hqn ht
  rw [← hcard] at hh
  have hscale := (Parameters.source_scale_bounds hp hq hPq hG.1 ht).1
  have hP := Parameters.Pstar_pos hp
  exact precheck_of_concentration p q t G S hp hG (by omega) (by linarith)
    hh hcard hscale he₁ he₂ hconc.1 hconc.2

theorem survives_of_concentration (p : Parameters) (q : ℕ) (G : Input I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (he₁ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q)
    (ω : FiniteHistory.Path (Snapshot I V))
    (hsupport : SupportedPath p q G ω)
    (hcard : ∀ t S, (ω t).1 = some S → S.remaining.card = Fintype.card I - t)
    (hconc : ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω)
    (hpost : NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω) :
    ∀ t ≤ p.lastMainTime q (Fintype.card I), ∃ S, (ω t).1 = some S := by
  apply survives_of_checks p q G _ ω hsupport
  · intro t ht S hS
    exact precheck_of_stateConcentration p q t G S hp hG hq hPq ht.le
      (hcard t S hS) he₁ he₂ (hconc t ht.le S hS)
  · exact hpost

theorem ae_survives_of_concentration (p : Parameters) (q : ℕ) (G : Input I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (he₁ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω →
      NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω →
      ∀ t ≤ p.lastMainTime q (Fintype.card I), ∃ S, (ω t).1 = some S := by
  filter_upwards [ae_supportedPath p q G, ae_snapshot_remaining_card p q G]
    with ω hs hc
  exact survives_of_concentration p q G hp hG hq hPq he₁ he₂ ω hs hc

theorem exists_firstAbort_threshold (p : Parameters) (hp : p.Admissible) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
      2 ≤ q ∧ 2 * p.Pstar ≤ q ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2 ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q := by
  obtain ⟨N, hN⟩ := exists_precheck_threshold p hp
  obtain ⟨M, hM⟩ := eventually_atTop.mp (Parameters.eventually_scale_regime p)
  refine ⟨max N M, fun q hq => ?_⟩
  have hn := hN q ((le_max_left N M).trans hq)
  have hm := hM q ((le_max_right N M).trans hq)
  exact ⟨hm.1, hm.2, hn.2.2⟩

end Balanced.Selection.Process.FirstAbort

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionFirstAbortFinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process.FirstAbort

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

theorem sourceTailCheck_of_stateConcentration (p : Parameters) (q : ℕ)
    (G : Input I V) (S : State I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (htail : (p.tailSlots q : ℝ) ≤ 2 * p.a * q)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (hcard : S.remaining.card = Fintype.card I -
      p.lastMainTime q (Fintype.card I))
    (hconc : StateConcentration p q G
      (p.lastMainTime q (Fintype.card I)) S) : SourceTailCheck p q G S := by
  have htailn : p.tailSlots q ≤ Fintype.card I :=
    (Parameters.tailSlots_le_order hp q).trans (by rw [hG.1]; omega)
  have hremaining : S.remaining.card = p.tailSlots q := by
    rw [hcard, Parameters.lastMainTime, Nat.sub_sub_self htailn]
  have hsmall : (S.remaining.card : ℝ) ≤ 2 * p.a * q := by
    rwa [hremaining]
  have hscale := (Parameters.source_scale_bounds hp hq hPq hG.1
    (le_refl (p.lastMainTime q (Fintype.card I)))).1
  have hnum := tail_check_of_concentration p q _ G S hp hG (by omega)
    hcard hsmall hscale hlarge he hconc.1 hconc.2
  refine ⟨(tailCheck_iff G S).2 ⟨hnum.1, ?_⟩, ?_⟩
  · intro v hv i hi
    exact_mod_cast hnum.2 v hv i hi
  · intro i hi
    exact SelectionBarriers.domain_barrier hscale hp.1
      (by exact_mod_cast (show 0 < q by omega)) (by linarith)
      (hG.2.2.1 i).1 (hconc.1 i hi) (Real.exp_pos _)

theorem ae_sourceTailCheck_of_concentration (p : Parameters) (q : ℕ)
    (G : Input I V) (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (htail : (p.tailSlots q : ℝ) ≤ 2 * p.a * q)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω →
      NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω →
      ∃ S, (ω (p.lastMainTime q (Fintype.card I))).1 = some S ∧
        StateInvariant G S ∧ SourceTailCheck p q G S := by
  have he₁ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2 := by linarith
  filter_upwards [ae_survives_of_concentration p q G hp hG hq hPq he₁ he₂,
    ae_snapshot_state_invariant p q G] with ω hsurv hinv
  intro hc hb
  obtain ⟨S, hS⟩ := hsurv hc hb _ le_rfl
  obtain ⟨hInv, hcard⟩ := hinv _ S hS
  refine ⟨S, hS, hInv, ?_⟩
  exact sourceTailCheck_of_stateConcentration p q G S hp hG hq hPq htail hlarge he
    (by omega) (hc _ le_rfl S hS)

theorem terminal_failure_probability_le (p : Parameters) (q : ℕ) (G : Input I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (htail : (p.tailSlots q : ℝ) ≤ 2 * p.a * q)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q) :
    (snapshotPathLaw p q G).real
        {ω | ¬ ∃ S, (ω (p.lastMainTime q (Fintype.card I))).1 = some S ∧
          StateInvariant G S ∧ SourceTailCheck p q G S} ≤
      (snapshotPathLaw p q G).real
        {ω | ¬ ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω} +
      (snapshotPathLaw p q G).real
        {ω | ¬ NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω} := by
  let μ := snapshotPathLaw p q G
  let E : Set (FiniteHistory.Path (Snapshot I V)) :=
    {ω | ¬ ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω}
  let B : Set (FiniteHistory.Path (Snapshot I V)) :=
    {ω | ¬ NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω}
  apply le_trans (b := μ.real (E ∪ B)) _ (measureReal_union_le E B)
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [ae_sourceTailCheck_of_concentration p q G hp hG hq hPq
    htail hlarge he he₂] with ω hω
  intro hf
  by_cases hc : ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω
  · by_cases hb : NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω
    · exact False.elim (hf (hω hc hb))
    · exact Or.inr hb
  · exact Or.inl hc

theorem exists_terminal_threshold (p : Parameters) (hp : p.Admissible) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
      2 ≤ q ∧ 2 * p.Pstar ≤ q ∧
      (p.tailSlots q : ℝ) ≤ 2 * p.a * q ∧
      6 ≤ p.smin * p.c * q ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100 ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q := by
  obtain ⟨N, hN⟩ := exists_firstAbort_threshold p hp
  obtain ⟨M, hM⟩ := exists_tail_check_threshold p hp
  refine ⟨max N M, fun q hq => ?_⟩
  have hn := hN q ((le_max_left N M).trans hq)
  have hm := hM q ((le_max_right N M).trans hq)
  exact ⟨hn.1, hn.2.1, hm.2.1, hm.2.2.1, hm.2.2.2, hn.2.2.2⟩

end Balanced.Selection.Process.FirstAbort

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionFlagTail
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical

namespace Balanced.SelectionThinning

noncomputable section
variable {V : Type*} [Fintype V]

theorem thinning_true_cylinder (rate : V → ℝ) (A : Finset V) :
    (∑ b : V → Bool, if ∀ v ∈ A, b v = true then thinningMass rate b else 0) =
      ∏ v ∈ A, rate v := by
  have hprod (b : V → Bool) :
      (if ∀ v ∈ A, b v = true then thinningMass rate b else 0) =
        ∏ v, bitMass (rate v) (b v) *
          (if v ∈ A then (if b v = true then 1 else 0) else 1) := by
    by_cases hb : ∀ v ∈ A, b v = true
    · rw [ite_eq_left hb]
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ A
      · simp [hv, hb v hv]
      · simp [hv]
    · rw [ite_eq_right hb]
      obtain ⟨v, hv⟩ := not_forall.mp hb
      obtain ⟨hv, hflag⟩ := Classical.not_imp.mp hv
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      simp [hv, hflag]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun v (b : Bool) =>
    bitMass (rate v) b * (if v ∈ A then (if b = true then 1 else 0) else 1))]
  have hsum (v : V) :
      (∑ b : Bool, bitMass (rate v) b *
        (if v ∈ A then (if b = true then 1 else 0) else 1)) =
      if v ∈ A then rate v else 1 := by
    by_cases hv : v ∈ A <;> simp [hv, bitMass]
  simp_rw [hsum]
  simp

theorem thinning_count_tail (rate : V → ℝ)
    (hrate : ∀ v, 0 ≤ rate v ∧ rate v ≤ 1) (A : Finset V) (k : ℕ) :
    (∑ b : V → Bool,
      if k ≤ (A.filter (fun v => b v = true)).card then thinningMass rate b else 0) ≤
      (∑ v ∈ A, rate v) ^ k / k.factorial := by
  have hm (b : V → Bool) := thinningMass_nonneg rate hrate b
  calc
    _ ≤ ∑ b : V → Bool, ∑ T ∈ A.powersetCard k,
        if ∀ v ∈ T, b v = true then thinningMass rate b else 0 := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : k ≤ (A.filter (fun v => b v = true)).card
      · rw [ite_eq_left hb]
        obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hb
        have hTA : T ∈ A.powersetCard k :=
          Finset.mem_powersetCard.mpr ⟨hT.trans (Finset.filter_subset _ _), hcard⟩
        have htrue : ∀ v ∈ T, b v = true := fun v hv =>
          (Finset.mem_filter.mp (hT hv)).2
        calc
          thinningMass rate b =
              (if ∀ v ∈ T, b v = true then thinningMass rate b else 0) := by
                rw [ite_eq_left htrue]
          _ ≤ _ := Finset.single_le_sum (s := A.powersetCard k)
            (f := fun T : Finset V => if ∀ v ∈ T, b v = true then thinningMass rate b else 0)
            (fun T _ => by split <;> first | exact hm b | exact le_rfl) hTA
      · rw [ite_eq_right hb]
        exact Finset.sum_nonneg (fun T _ => by split <;> first | exact hm b | exact le_rfl)
    _ = ∑ T ∈ A.powersetCard k, ∏ v ∈ T, rate v := by
      rw [Finset.sum_comm]
      simp_rw [thinning_true_cylinder]
    _ ≤ _ := Balanced.sum_prod_powersetCard_le A rate (fun v _ => (hrate v).1) k

end
end Balanced.SelectionThinning

namespace Balanced.Selection.Process

noncomputable section
variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] [Fintype V] in

theorem thinned_inter_subset_true (G : Input I V) (S : State I V)
    (w : V) (flags : V → Bool) (A : Finset V) :
    thinned G S w flags ∩ A ⊆ A.filter (fun v => flags v = true) := by
  intro v hv
  rcases Finset.mem_inter.mp hv with ⟨hv, hA⟩
  exact Finset.mem_filter.mpr ⟨hA, (Finset.mem_filter.mp hv).2.2⟩

omit [Fintype I] in

theorem flags_thinned_tail_le (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hpre : Precheck p q t G S)
    (w : V) (A : Finset V) (m : ℝ)
    (hmean : ∑ v ∈ A, thinningRate p q G S v ≤ m) :
    (∑ flags : V → Bool,
      if (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S w flags ∩ A).card : ℝ)
      then flagsWeight p q G S flags else 0) ≤
      (Real.exp 1 * m / (BernoulliTail.thinningCutoff (1 / 8) q : ℝ)) ^
        BernoulliTail.thinningCutoff (1 / 8) q := by
  let k := BernoulliTail.thinningCutoff (1 / 8) q
  have hrate (v : V) : 0 ≤ thinningRate p q G S v ∧ thinningRate p q G S v ≤ 1 := by
    have h := thinningRate_bounds_of_precheck p q t G S hpre v
    exact ⟨h.1, h.2.trans hpre.2.2.1.le⟩
  have hm : 0 ≤ m := (Finset.sum_nonneg (fun v _ => (hrate v).1)).trans hmean
  calc
    _ ≤ ∑ flags : V → Bool,
        if k ≤ (A.filter (fun v => flags v = true)).card then
          SelectionThinning.thinningMass (thinningRate p q G S) flags else 0 := by
      apply Finset.sum_le_sum
      intro flags _
      by_cases hf : (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S w flags ∩ A).card : ℝ)
      · have hk : k ≤ (A.filter (fun v => flags v = true)).card := by
          have hsmall : k ≤ (thinned G S w flags ∩ A).card := by
            apply Nat.succ_le_iff.mpr
            exact (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg q) _)).mpr hf
          exact hsmall.trans (Finset.card_le_card (thinned_inter_subset_true G S w flags A))
        simp only [hf, ite_true, hk]
        rfl
      · rw [ite_eq_right hf]
        split
        · exact SelectionThinning.thinningMass_nonneg _ hrate flags
        · exact le_rfl
    _ ≤ (∑ v ∈ A, thinningRate p q G S v) ^ k / k.factorial :=
      SelectionThinning.thinning_count_tail _ hrate A k
    _ ≤ m ^ k / k.factorial := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (Finset.sum_nonneg (fun v _ => (hrate v).1)) hmean k
    _ ≤ _ := Balanced.pow_div_factorial_le_exp_ratio m hm k (by
      dsimp [k, BernoulliTail.thinningCutoff]
      omega)

theorem noise_thinned_tail_le (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hpre : Precheck p q t G S)
    (A : Finset V) (m : ℝ)
    (hmean : ∑ v ∈ A, thinningRate p q G S v ≤ m) :
    (∑ r : Noise I V,
      if (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S r.2.1 r.2.2 ∩ A).card : ℝ)
      then noiseWeight p q G S r else 0) ≤
      (Real.exp 1 * m / (BernoulliTail.thinningCutoff (1 / 8) q : ℝ)) ^
        BernoulliTail.thinningCutoff (1 / 8) q := by
  let ε := (Real.exp 1 * m / (BernoulliTail.thinningCutoff (1 / 8) q : ℝ)) ^
    BernoulliTail.thinningCutoff (1 / 8) q
  simp only [Noise, Fintype.sum_prod_type]
  calc
    _ = ∑ i : I, ∑ w : V, drawWeight G S i w *
        (∑ flags : V → Bool,
          if (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S w flags ∩ A).card : ℝ)
          then flagsWeight p q G S flags else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro flags _
      split <;> simp_all [noiseWeight]
    _ ≤ ∑ i : I, ∑ w : V, drawWeight G S i w * ε := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_left (flags_thinned_tail_le p q t G S hpre w A m hmean)
        (drawWeight_nonnegative G S i w)
    _ = ε := by
      simp_rw [← Finset.sum_mul]
      rw [sum_drawWeight G S hpre.1 (fun i hi => (hpre.2.2.2.1 i hi).1), one_mul]

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionHistoryMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem integrable_stateObservable (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (f : Option (State I V) → ℝ) :
    Integrable (fun ω => f (ω t).1) (snapshotPathLaw p q G) := by
  have hi : Integrable (fun s : Snapshot I V => f s.1)
      ((snapshotPathLaw p q G).map (fun ω => ω t)) := .of_finite
  exact hi.comp_measurable (measurable_pi_apply t)

theorem sum_snapshotWeight_stateObservable (p : Parameters) (q t : ℕ)
    (G : Input I V) (before : Snapshot I V) (f : Option (State I V) → ℝ) :
    (∑ out, snapshotWeight p q t G before out * f out.1) =
      ∑ out, transitionWeight p q t G before.1 out * f out := by
  simp only [Snapshot, Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul, sum_snapshotWeight_state]

theorem integral_stateObservable_eq_historyWeight (p : Parameters) (q : ℕ)
    (G : Input I V) (t : ℕ) (f : Option (State I V) → ℝ) :
    (∫ ω, f (ω t).1 ∂snapshotPathLaw p q G) =
      ∑ out, historyWeight p q G t out * f out := by
  induction t generalizing f with
  | zero =>
    have hi := FiniteHistory.ae_initial_state
      (fun t => snapshotPMF p q t G) (initialSnapshot (I := I) (V := V))
    have heq : (fun ω => f (ω 0).1) =ᵐ[snapshotPathLaw p q G]
        fun _ => f (some initialState) := by
      filter_upwards [hi] with ω hω
      simp only [hω, initialSnapshot]
    rw [integral_congr_ae heq]
    simp [historyWeight]
  | succ t ih =>
    have hce := condExp_snapshot_step p q G t (fun _ out => f out.1)
    have hce' : (snapshotPathLaw p q G)[
        (fun ω => f (ω (t + 1)).1) | snapshotFiltration t]
        =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ out, transitionWeight p q t G (ω t).1 out * f out := by
      change (snapshotPathLaw p q G)[
        (fun ω => f (ω (t + 1)).1) | snapshotFiltration t] =ᵐ[snapshotPathLaw p q G] _ at hce
      simpa only [sum_snapshotWeight_stateObservable] using hce
    calc
      (∫ ω, f (ω (t + 1)).1 ∂snapshotPathLaw p q G) =
          ∫ ω, ((snapshotPathLaw p q G)[
            (fun ω => f (ω (t + 1)).1) | snapshotFiltration t]) ω
              ∂snapshotPathLaw p q G :=
        (integral_condExp (snapshotFiltration.le t)).symm
      _ = ∫ ω, (∑ out, transitionWeight p q t G (ω t).1 out * f out)
          ∂snapshotPathLaw p q G := integral_congr_ae hce'
      _ = ∑ out, ∫ ω, transitionWeight p q t G (ω t).1 out * f out
          ∂snapshotPathLaw p q G :=
        integral_finsetSum _ (fun out _ =>
          integrable_stateObservable p q G t (fun s => transitionWeight p q t G s out * f out))
      _ = ∑ out, ∑ before, historyWeight p q G t before *
          (transitionWeight p q t G before out * f out) := by
        apply Finset.sum_congr rfl
        intro out _
        exact ih (fun before => transitionWeight p q t G before out * f out)
      _ = ∑ out, historyWeight p q G (t + 1) out * f out := by
        simp only [historyWeight, Finset.sum_mul, mul_assoc]

theorem state_event_real_eq_historyWeight (p : Parameters) (q : ℕ)
    (G : Input I V) (t : ℕ) (A : Set (Option (State I V))) :
    (snapshotPathLaw p q G).real {ω | (ω t).1 ∈ A} =
      ∑ out, if out ∈ A then historyWeight p q G t out else 0 := by
  have hm : MeasurableSet {ω : FiniteHistory.Path (Snapshot I V) | (ω t).1 ∈ A} :=
    (show MeasurableSet {s : Snapshot I V | s.1 ∈ A} from .of_discrete).preimage
      (measurable_pi_apply t)
  rw [← integral_indicator_one hm]
  have h := integral_stateObservable_eq_historyWeight p q G t
    (fun out => if out ∈ A then 1 else 0)
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, mul_ite,
    mul_one, mul_zero] using h

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionHistoryFinalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V] [Nonempty V]

theorem successMass_finalLaw_eq_path_probability (p : Parameters) (q : ℕ)
    (G : Input I V) (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) :
    successMass (finalLaw p q G hno) =
      (snapshotPathLaw p q G).real {ω | ∃ S,
        (ω (p.lastMainTime q (Fintype.card I))).1 = some S ∧ SourceTailCheck p q G S} := by
  rw [successMass_finalLaw]
  change _ = (snapshotPathLaw p q G).real {ω |
    (ω (p.lastMainTime q (Fintype.card I))).1 ∈
      {out | ∃ S, out = some S ∧ SourceTailCheck p q G S}}
  rw [state_event_real_eq_historyWeight, Fintype.sum_option]
  simp [mainStageWeight]

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionPostcheckTail
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical

namespace Balanced.Selection.Process

noncomputable section

private theorem finite_union_weight_le {Ω J : Type*} [Fintype Ω] [Fintype J]
    (weight : Ω → ℝ) (hw : ∀ ω, 0 ≤ weight ω) (E : J → Ω → Prop) :
    (∑ ω, if ∃ j, E j ω then weight ω else 0) ≤
      ∑ j, ∑ ω, if E j ω then weight ω else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ∃ j, E j ω
  · obtain ⟨j, hj⟩ := h
    rw [ite_eq_left ⟨j, hj⟩]
    calc
      weight ω = (if E j ω then weight ω else 0) := by rw [ite_eq_left hj]
      _ ≤ _ := Finset.single_le_sum (s := Finset.univ)
        (f := fun j => if E j ω then weight ω else 0)
        (fun j _ => by split <;> first | exact hw ω | exact le_rfl) (Finset.mem_univ j)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun j _ => by split <;> first | exact hw ω | exact le_rfl)

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in

theorem flag_mean_le_card_mul_alpha (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hpre : Precheck p q t G S) (A : Finset V) :
    (∑ v ∈ A, thinningRate p q G S v) ≤ (A.card : ℝ) * p.alpha q := by
  calc
    _ ≤ ∑ _v ∈ A, p.alpha q := Finset.sum_le_sum
      (fun v _ => (thinningRate_bounds_of_precheck p q t G S hpre v).2)
    _ = _ := by simp

theorem domain_flag_mean_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (hpre : Precheck p q t G S) (i : I) :
    (∑ v ∈ domain G S i, thinningRate p q G S v) ≤ postcheckMean p := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hP : 0 ≤ p.Pstar := by
    have h := hpre.2.1
    simpa using (le_div_iff₀ hqR).mp h
  have hdom : ((domain G S i).card : ℝ) ≤ q := by
    apply le_trans _ (show ((slotVertices G i).card : ℝ) ≤ q by exact_mod_cast (hG.2.2.1 i).2)
    exact_mod_cast Finset.card_le_card (show domain G S i ⊆ slotVertices G i from by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩)
  calc
    _ ≤ ((domain G S i).card : ℝ) * p.alpha q :=
      flag_mean_le_card_mul_alpha p q t G S hpre _
    _ ≤ (q : ℝ) * p.alpha q := mul_le_mul_of_nonneg_right hdom hpre.2.1
    _ = p.Pstar := by unfold Parameters.alpha; field_simp
    _ ≤ postcheckMean p := by
      unfold postcheckMean
      simpa using mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) p.C) hP

theorem neighbor_flag_mean_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (hpre : Precheck p q t G S) (v : V) :
    (∑ u ∈ neighbors G v, thinningRate p q G S u) ≤ postcheckMean p := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hP : 0 ≤ p.Pstar := by
    have h := hpre.2.1
    simpa using (le_div_iff₀ hqR).mp h
  calc
    _ ≤ ((neighbors G v).card : ℝ) * p.alpha q :=
      flag_mean_le_card_mul_alpha p q t G S hpre _
    _ ≤ (p.C * q) * p.alpha q :=
      mul_le_mul_of_nonneg_right (hG.2.2.2.1 v) hpre.2.1
    _ = p.Pstar * p.C := by unfold Parameters.alpha; field_simp
    _ ≤ postcheckMean p :=
      mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) p.C) hP

theorem postcheck_failure_mass_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (hpre : Precheck p q t G S) :
    (∑ r : Noise I V, if ¬ Postcheck q G S r.2.1 r.2.2 then
      noiseWeight p q G S r else 0) ≤
      ((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q := by
  let A : I ⊕ V → Finset V := Sum.elim (domain G S) (neighbors G)
  let E : (I ⊕ V) → Noise I V → Prop := fun j r =>
    (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S r.2.1 r.2.2 ∩ A j).card : ℝ)
  have hsub (r : Noise I V) (hr : ¬ Postcheck q G S r.2.1 r.2.2) : ∃ j, E j r := by
    unfold Postcheck at hr
    rcases not_and_or.mp hr with h | h
    · push Not at h
      obtain ⟨i, _, hi⟩ := h
      exact ⟨Sum.inl i, hi⟩
    · push Not at h
      obtain ⟨v, _, hv⟩ := h
      exact ⟨Sum.inr v, hv⟩
  calc
    _ ≤ ∑ r : Noise I V, if ∃ j, E j r then noiseWeight p q G S r else 0 := by
      apply Finset.sum_le_sum
      intro r _
      by_cases hr : ¬ Postcheck q G S r.2.1 r.2.2
      · simp only [hr, ite_true, hsub r hr]
        exact le_rfl
      · rw [ite_eq_right hr]
        split
        · exact noiseWeight_nonnegative_of_precheck p q t G S hpre r
        · exact le_rfl
    _ ≤ ∑ j : I ⊕ V, ∑ r : Noise I V, if E j r then noiseWeight p q G S r else 0 :=
      finite_union_weight_le _ (noiseWeight_nonnegative_of_precheck p q t G S hpre) E
    _ ≤ ∑ _j : I ⊕ V, postcheckTail p q := by
      apply Finset.sum_le_sum
      intro j _
      apply noise_thinned_tail_le p q t G S hpre (A j) (postcheckMean p)
      cases j with
      | inl i => exact domain_flag_mean_le p q t hq G hG S hpre i
      | inr v => exact neighbor_flag_mean_le p q t hq G hG S hpre v
    _ = _ := by simp [Nat.cast_add]

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionPostabort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Classical

namespace Balanced.Selection.Process

variable {I V : Type*} [Fintype I] [Fintype V]

theorem postcheckTail_nonneg (p : Parameters) (q : ℕ) (hP : 0 ≤ p.Pstar) :
    0 ≤ postcheckTail p q := by
  unfold postcheckTail postcheckMean
  have : 0 ≤ max (1 : ℝ) p.C := le_trans (by norm_num) (le_max_left _ _)
  positivity

theorem retained_postcheck_mean_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (hP : 0 ≤ p.Pstar) (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (before : Option (State I V)) :
    (∑ draw, drawStepWeight p q t G before draw *
      (if postcheckFailed q G before draw then (1 : ℝ) else 0)) ≤
      ((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q := by
  have hδ : 0 ≤ ((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q :=
    mul_nonneg (by positivity) (postcheckTail_nonneg p q hP)
  cases before with
  | none => simpa [postcheckFailed] using hδ
  | some S =>
      by_cases hp : Precheck p q t G S
      · rw [sum_drawStepWeight_of_precheck p q t G S hp]
        calc
          _ = ∑ draw : Noise I V,
              if ¬ Postcheck q G S draw.2.1 draw.2.2 then noiseWeight p q G S draw else 0 := by
            apply Finset.sum_congr rfl
            intro draw _
            by_cases hpost : Postcheck q G S draw.2.1 draw.2.2 <;>
              simp [postcheckFailed, hpost]
          _ ≤ _ := postcheck_failure_mass_le p q t hq G hG S hp
      · simpa [drawStepWeight, hp, Fintype.sum_option, postcheckFailed] using hδ

theorem measurableSet_postcheckEvent (q : ℕ) (G : Input I V) (t : ℕ) :
    MeasurableSet (postcheckEvent q G t) := by
  let f : FiniteHistory.Prefix (Snapshot I V) t → Snapshot I V → ℝ := fun h out =>
    if postcheckFailed q G (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1 out.2 then 1 else 0
  have hm := FiniteHistory.measurable_stepObservable t f
  have heq : postcheckEvent q G t = {ω | (0 : ℝ) < FiniteHistory.stepObservable t f ω} := by
    ext ω
    simp only [postcheckEvent, Set.mem_ofPred_eq, FiniteHistory.stepObservable, f, frestrictLe]
    split <;> simp_all
  rw [heq]
  exact measurableSet_lt measurable_const hm

theorem postcheckEvent_mass_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (hP : 0 ≤ p.Pstar) (G : Input I V) (hG : GraphBounds G q p.c p.C) :
    (snapshotPathLaw p q G).real (postcheckEvent q G t) ≤
      ((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q := by
  let μ := snapshotPathLaw p q G
  let δ := ((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q
  let f : FiniteHistory.Prefix (Snapshot I V) t → Option (Noise I V) → ℝ := fun h draw =>
    if postcheckFailed q G (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1 draw then 1 else 0
  let X := FiniteHistory.stepObservable t (fun h out => f h out.2)
  have hce := condExp_retained_draw p q G t f
  have hbound : ∀ᵐ ω ∂μ, μ[X | snapshotFiltration t] ω ≤ δ := by
    filter_upwards [hce] with ω hω
    rw [hω]
    exact retained_postcheck_mean_le p q t hq hP G hG (ω t).1
  have hind : X = (postcheckEvent q G t).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    rfl
  calc
    μ.real (postcheckEvent q G t) = ∫ ω, X ω ∂μ := by
      rw [hind, integral_indicator_const 1 (measurableSet_postcheckEvent q G t)]
      simp
    _ = ∫ ω, μ[X | snapshotFiltration t] ω ∂μ :=
      (integral_condExp (snapshotFiltration.le t)).symm
    _ ≤ ∫ _ω, δ ∂μ := integral_mono_ae integrable_condExp (integrable_const δ) hbound
    _ = δ := by simp [μ]

theorem postcheck_union_mass_le (p : Parameters) (q T : ℕ) (hq : 0 < q)
    (hP : 0 ≤ p.Pstar) (G : Input I V) (hG : GraphBounds G q p.c p.C) :
    (snapshotPathLaw p q G).real (⋃ t ∈ Finset.range T, postcheckEvent q G t) ≤
      (T : ℝ) * (((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q) := by
  calc
    _ ≤ ∑ t ∈ Finset.range T, (snapshotPathLaw p q G).real (postcheckEvent q G t) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ Finset.range T,
        ((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q :=
      Finset.sum_le_sum (fun t _ => postcheckEvent_mass_le p q t hq hP G hG)
    _ = _ := by simp

theorem graph_card_vertices_le (p : Parameters) (q : ℕ)
    (G : Input I V) (hG : GraphBounds G q p.c p.C) :
    Fintype.card V ≤ Fintype.card I * q := by
  have hpartition : Fintype.card V = ∑ i : I, (slotVertices G i).card := by
    simpa only [Finset.card_univ, slotVertices] using
      (Finset.card_eq_sum_card_fiberwise (f := G.slot)
        (s := Finset.univ) (t := Finset.univ) (by intro v _; exact Finset.mem_univ _))
  rw [hpartition]
  calc
    _ ≤ ∑ _i : I, q := Finset.sum_le_sum (fun i _ => (hG.2.2.1 i).2)
    _ = _ := by simp

theorem graph_time_test_count_le (p : Parameters) (q T : ℕ) (hq : 2 ≤ q)
    (hT : T ≤ 3 * q) (G : Input I V) (hG : GraphBounds G q p.c p.C) :
    (T : ℝ) * ((Fintype.card I : ℝ) + Fintype.card V) ≤ 18 * (q : ℝ) ^ 3 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hn : (Fintype.card I : ℝ) ≤ 3 * q := by
    exact_mod_cast (show Fintype.card I ≤ 3 * q by rw [hG.1]; omega)
  have hv : (Fintype.card V : ℝ) ≤ (Fintype.card I : ℝ) * q := by
    exact_mod_cast graph_card_vertices_le p q G hG
  have hv' : (Fintype.card V : ℝ) ≤ 3 * (q : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    nlinarith
  have hn' : (Fintype.card I : ℝ) ≤ 3 * (q : ℝ) ^ 2 := by nlinarith
  have ht : (T : ℝ) ≤ 3 * q := by exact_mod_cast hT
  calc
    _ ≤ (3 * q) * (6 * (q : ℝ) ^ 2) :=
      mul_le_mul ht (by linarith) (by positivity) (by positivity)
    _ = _ := by ring

theorem postcheck_union_mass_le_source (p : Parameters) (q T : ℕ) (hq : 2 ≤ q)
    (hP : 0 ≤ p.Pstar) (hT : T ≤ 3 * q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C) :
    (snapshotPathLaw p q G).real (⋃ t ∈ Finset.range T, postcheckEvent q G t) ≤
      18 * (q : ℝ) ^ 3 * postcheckTail p q := by
  apply (postcheck_union_mass_le p q T (by omega) hP G hG).trans
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (graph_time_test_count_le p q T hq hT G hG)
    (postcheckTail_nonneg p q hP)

theorem main_postcheck_union_mass_le (p : Parameters) (q : ℕ) (hq : 2 ≤ q)
    (hP : 0 ≤ p.Pstar) (G : Input I V) (hG : GraphBounds G q p.c p.C) :
    (snapshotPathLaw p q G).real
      (⋃ t ∈ Finset.range (p.lastMainTime q (Fintype.card I)), postcheckEvent q G t) ≤
      18 * (q : ℝ) ^ 3 * postcheckTail p q := by
  apply postcheck_union_mass_le_source p q _ hq hP _ G hG
  exact (Nat.sub_le _ _).trans (by rw [hG.1]; omega)

theorem tendsto_source_postcheck_bound (p : Parameters) (hP : 0 ≤ p.Pstar) :
    Tendsto (fun q : ℕ => 18 * (q : ℝ) ^ 3 * postcheckTail p q)
      atTop (nhds 0) := by
  have hm : 0 ≤ postcheckMean p :=
    mul_nonneg hP (le_trans (by norm_num) (le_max_left (1 : ℝ) p.C))
  have h := (BernoulliTail.tendsto_post_step_abort_bound (postcheckMean p) hm).const_mul 18
  simpa only [postcheckTail, mul_zero, mul_assoc] using h

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionSuccessBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in

theorem not_noPostAbort_eq_union (q : ℕ) (G : Input I V) (T : ℕ) :
    {ω | ¬ FirstAbort.NoPostAbort q G T ω} =
      ⋃ t ∈ Finset.range T, postcheckEvent q G t := by
  ext ω
  constructor
  · intro h
    change ¬ FirstAbort.NoPostAbort q G T ω at h
    unfold FirstAbort.NoPostAbort at h
    push Not at h
    obtain ⟨t, ht, S, r, hS, hr, hbad⟩ := h
    refine Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr ht, ?_⟩⟩
    simpa only [postcheckEvent, Set.mem_ofPred_eq, postcheckFailed, hS, hr] using hbad
  · intro h hgood
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp h
    obtain ⟨ht, hbad⟩ := Set.mem_iUnion.mp ht
    have htime := Finset.mem_range.mp ht
    change postcheckFailed q G (ω t).1 (ω (t + 1)).2 at hbad
    cases hS : (ω t).1 with
    | none => simp [hS, postcheckFailed] at hbad
    | some S =>
      cases hr : (ω (t + 1)).2 with
      | none => simp [hS, hr, postcheckFailed] at hbad
      | some r =>
        have hb : ¬ Postcheck q G S r.2.1 r.2.2 := by
          simpa only [hS, hr, postcheckFailed] using hbad
        exact hb (hgood t htime S r hS hr)

theorem successMass_finalLaw_ge_good_events [Nonempty V]
    (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (htail : (p.tailSlots q : ℝ) ≤ 2 * p.a * q)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q) :
    1 - (snapshotPathLaw p q G).real
        {ω | ¬ FirstAbort.ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω} -
      (snapshotPathLaw p q G).real
        {ω | ¬ FirstAbort.NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω} ≤
      successMass (finalLaw p q G hno) := by
  let T := p.lastMainTime q (Fintype.card I)
  let E : Set (FiniteHistory.Path (Snapshot I V)) :=
    {ω | ∃ S, (ω T).1 = some S ∧ SourceTailCheck p q G S}
  have hm : MeasurableSet E :=
    (show MeasurableSet {s : Snapshot I V | ∃ S, s.1 = some S ∧ SourceTailCheck p q G S}
      from .of_discrete).preimage (measurable_pi_apply T)
  have hsub : Eᶜ ⊆ {ω | ¬ ∃ S, (ω T).1 = some S ∧
      StateInvariant G S ∧ SourceTailCheck p q G S} := by
    intro ω hω ⟨S, hs, _, ht⟩
    exact hω ⟨S, hs, ht⟩
  have hle := (measureReal_mono hsub (measure_ne_top _ _)).trans
    (FirstAbort.terminal_failure_probability_le p q G hp hG hq hPq htail hlarge he he₂)
  have hcompl : (snapshotPathLaw p q G).real Eᶜ =
      1 - successMass (finalLaw p q G hno) := by
    rw [measureReal_compl hm, successMass_finalLaw_eq_path_probability]
    simp only [probReal_univ]
    rfl
  rw [hcompl] at hle
  linarith

theorem successMass_finalLaw_ge_concentration_sub_postcheck [Nonempty V]
    (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (htail : (p.tailSlots q : ℝ) ≤ 2 * p.a * q)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q) :
    1 - (snapshotPathLaw p q G).real
      {ω | ¬ FirstAbort.ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω} -
      18 * (q : ℝ) ^ 3 * postcheckTail p q ≤ successMass (finalLaw p q G hno) := by
  have hsuccess := successMass_finalLaw_ge_good_events p q G hno hp hG hq hPq
    htail hlarge he he₂
  rw [not_noPostAbort_eq_union] at hsuccess
  have hpost := main_postcheck_union_mass_le p q hq (Parameters.Pstar_pos hp).le G hG
  linarith

theorem successMass_outputLaw_ge_concentration_sub_postcheck
    (p : Parameters) (q : ℕ) (G : Input I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (htail : (p.tailSlots q : ℝ) ≤ 2 * p.a * q)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q) :
    1 - (snapshotPathLaw p q G).real
      {ω | ¬ FirstAbort.ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω} -
      18 * (q : ℝ) ^ 3 * postcheckTail p q ≤ successMass (outputLaw p q G hG.2.1) := by
  let : Nonempty V := graphBounds_vertex_nonempty G q p.c p.C hp.1 (by omega) hG
  rw [outputLaw_eq_finalLaw]
  exact successMass_finalLaw_ge_concentration_sub_postcheck p q G hG.2.1 hp hG hq hPq
    htail hlarge he he₂

universe u v

theorem exists_uniform_success_threshold (p : Parameters) (hp : p.Admissible) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
      ∀ {I : Type u} {V : Type v} [Fintype I] [Fintype V]
        (G : Input I V) (hG : GraphBounds G q p.c p.C),
      1 - (snapshotPathLaw p q G).real
        {ω | ¬ FirstAbort.ConcentratedPath p q G
          (p.lastMainTime q (Fintype.card I)) ω} -
        18 * (q : ℝ) ^ 3 * postcheckTail p q ≤
          successMass (outputLaw p q G hG.2.1) := by
  obtain ⟨N, hN⟩ := FirstAbort.exists_terminal_threshold p hp
  refine ⟨N, ?_⟩
  intro q hq I V _ _ G hG
  obtain ⟨hq, hPq, htail, hlarge, he, he₂⟩ := hN q hq
  exact successMass_outputLaw_ge_concentration_sub_postcheck p q G hp hG
    hq hPq htail hlarge he he₂

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionTailCylinder
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process.Tail
variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] [Fintype V] in

theorem complete_cylinder_iff (G : Input I V) (S : State I V)
    (fixed prescribed : I → V) (J : Finset I)
    (a : Slots.Assignment (Domain G S)) :
    (∀ i ∈ J, complete G S fixed a i = prescribed i) ↔
      (∀ i ∈ J, i ∉ S.remaining → fixed i = prescribed i) ∧
      a ∈ TailConditioning.ambientCylinder (Domain G S) (fun _ => Subtype.val)
        (residualIndices S J) (fun i => prescribed i.1) := by
  constructor
  · intro h
    constructor
    · intro i hi hr
      simpa only [complete_recorded G S fixed a i hr] using h i hi
    · intro i hi
      simpa only [complete_remaining] using h i.1 ((mem_residualIndices S J i).mp hi)
  · rintro ⟨hfixed, hremaining⟩ i hi
    by_cases hr : i ∈ S.remaining
    · simpa only [complete, dite_eq_left hr] using
        hremaining ⟨i, hr⟩ ((mem_residualIndices S J ⟨i, hr⟩).mpr hi)
    · rw [complete_recorded G S fixed a i hr]
      exact hfixed i hi hr

omit [Fintype I] [Fintype V] in

theorem image_residualIndices (S : State I V) (J : Finset I) :
    (residualIndices S J).image Subtype.val = J ∩ S.remaining := by
  ext i
  simp only [Finset.mem_image, mem_residualIndices, Finset.mem_inter]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨hj, j.property⟩
  · rintro ⟨hj, hr⟩
    exact ⟨⟨i, hr⟩, hj, rfl⟩

omit [Fintype I] [Fintype V] in

theorem card_residualIndices (S : State I V) (J : Finset I) :
    (residualIndices S J).card = (J ∩ S.remaining).card := by
  rw [← image_residualIndices S J, Finset.card_image_of_injective _ Subtype.val_injective]

omit [Fintype I] [Fintype V] in

theorem prod_residualIndices {M : Type*} [CommMonoid M]
    (S : State I V) (J : Finset I) (f : I → M) :
    (∏ i ∈ residualIndices S J, f i.1) = ∏ i ∈ J ∩ S.remaining, f i := by
  rw [← image_residualIndices S J, Finset.prod_image]
  exact fun _ _ _ _ h => Subtype.val_injective h

variable [MeasurableSpace V] [MeasurableSingletonClass V]

theorem cylinderMass_completion_eq_conditional (G : Input I V) (S : State I V)
    (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty)
    (J : Finset I) (prescribed : I → V) :
    cylinderMass (completionOutputLaw G S fixed hslot hind hcross hG) J prescribed =
      (cond (Slots.law (Domain G S))
        (TailConditioning.independentTransversals (Domain G S) (graph G S))).real
        {a | ∀ i ∈ J, complete G S fixed a i = prescribed i} := by
  classical
  let E : Finset (I → V) := Finset.univ.filter (fun a => ∀ i ∈ J, a i = prescribed i)
  have hmass : cylinderMass (completionOutputLaw G S fixed hslot hind hcross hG) J prescribed =
      (completionPMF G S fixed hG).toMeasure.real (E : Set (I → V)) := by
    unfold Measure.real
    rw [PMF.toMeasure_apply_finset, ENNReal.toReal_sum (fun a _ =>
      (completionPMF G S fixed hG).apply_ne_top a)]
    rfl
  rw [hmass]
  have he : (successfulAssignments G S : Set (Slots.Assignment (Domain G S))) =
      TailConditioning.independentTransversals (Domain G S) (graph G S) := by
    ext a
    exact mem_successfulAssignments G S a
  rw [← he, Slots.conditional_law_eq_uniformOfFinset _ hG]
  unfold completionPMF Measure.real
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) (E.finite_toSet.measurableSet)]
  congr 2
  ext a
  simp [E]

theorem cylinderMass_completion_eq_ambient (G : Input I V) (S : State I V)
    (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty)
    (J : Finset I) (prescribed : I → V)
    (hfixed : ∀ i ∈ J, i ∉ S.remaining → fixed i = prescribed i) :
    cylinderMass (completionOutputLaw G S fixed hslot hind hcross hG) J prescribed =
      TailConditioning.conditionalAmbientCylinder (Domain G S) (graph G S)
        (fun _ => Subtype.val) (residualIndices S J) (fun i => prescribed i.1) := by
  rw [cylinderMass_completion_eq_conditional]
  have he : {a | ∀ i ∈ J, complete G S fixed a i = prescribed i} =
      TailConditioning.ambientCylinder (Domain G S) (fun _ => Subtype.val)
        (residualIndices S J) (fun i => prescribed i.1) := by
    ext a
    exact (complete_cylinder_iff G S fixed prescribed J a).trans (and_iff_right hfixed)
  rw [he]
  simp [TailConditioning.conditionalAmbientCylinder, Measure.real,
    ProbabilityTheory.cond_apply
      (Set.toFinite (TailConditioning.independentTransversals (Domain G S) (graph G S))).measurableSet,
    ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm, Set.inter_comm]

theorem cylinderMass_completion_eq_zero_of_prefix_mismatch
    (G : Input I V) (S : State I V) (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty)
    (J : Finset I) (prescribed : I → V)
    (hbad : ¬ ∀ i ∈ J, i ∉ S.remaining → fixed i = prescribed i) :
    cylinderMass (completionOutputLaw G S fixed hslot hind hcross hG) J prescribed = 0 := by
  rw [cylinderMass_completion_eq_conditional]
  have he : {a | ∀ i ∈ J, complete G S fixed a i = prescribed i} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact hbad ((complete_cylinder_iff G S fixed prescribed J a).mp ha).1
  rw [he, measureReal_empty]

end Balanced.Selection.Process.Tail

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionTailNumerics
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced.TailConditioning

theorem tail_conditioning_ambient_of_pointwise_bounds
    {I V : Type*} {Q : I → Type*} [Fintype I] [∀ i, Fintype (Q i)]
    [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)]
    (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj]
    (hno : TailGraph.NoWithinSlotEdges G Sigma.fst)
    (hsize : ∀ i, 3 ≤ Fintype.card (Q i))
    (hdegree : ∀ v i, 8 * G.degree v ≤ Fintype.card (Q i))
    (embed : ∀ i, Q i → V) (hinj : ∀ i, Function.Injective (embed i)) :
    0 < (Slots.law Q).real (independentTransversals Q G) ∧
      ∀ (J : Finset I) (a : I → V),
        conditionalAmbientCylinder Q G embed J a ≤
          Real.exp ((J.card : ℝ) / 2) * ∏ i ∈ J, (Fintype.card (Q i) : ℝ)⁻¹ := by
  classical
  obtain ⟨hpos, hbound⟩ := tail_conditioning_of_pointwise_bounds G hno hsize hdegree
  refine ⟨hpos, ?_⟩
  intro J a
  by_cases hne : (ambientCylinder Q embed J a).Nonempty
  · obtain ⟨b, hb⟩ := hne
    have heq := ambientCylinder_eq_cylinder_of_mem embed hinj J a b hb
    simpa only [conditionalAmbientCylinder, conditionalCylinder, heq] using hbound J b
  · have heq := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [conditionalAmbientCylinder, heq, Set.empty_inter, measureReal_empty, zero_div]
    positivity

end Balanced.TailConditioning

namespace Balanced.Selection.Process.Tail

noncomputable section

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in
theorem conditionalAmbientCylinder_le_of_tailCheck
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (G : Input I V) (S : State I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (ht : TailCheck G S) (J : Finset (Slot S)) (a : Slot S → V) :
    TailConditioning.conditionalAmbientCylinder (Domain G S) (graph G S)
      (fun _ v => v.1) J a ≤
        Real.exp ((J.card : ℝ) / 2) *
          ∏ i ∈ J, ((domain G S i.1).card : ℝ)⁻¹ := by
  classical
  obtain ⟨hs, hd⟩ := (tailCheck_iff G S).mp ht
  have h := TailConditioning.tail_conditioning_ambient_of_pointwise_bounds
    (graph G S) (noWithinSlotEdges G S hno)
    (fun i => by simpa only [card_domain] using hs i.1 i.2)
    (fun v i => by
      rw [card_domain]
      exact (Nat.mul_le_mul_left 8 (degree_le G S v)).trans
        (hd _ (value_mem_current G S v) i.1 i.2))
    (fun _ v => v.1) (fun _ => Subtype.val_injective)
  simpa only [card_domain] using h.2 J a

end
end Balanced.Selection.Process.Tail

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionTailPotential
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]

section Nonempty
variable [Nonempty V]

theorem cylinderMass_terminalLaw_le_potential (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (S : State I V) (J : Finset I) (a : I → V) (c : ℝ) (hc : 0 ≤ c)
    (hproduct : Real.exp (((J ∩ S.remaining).card : ℝ) / 2) *
      (∏ i ∈ J ∩ S.remaining, ((domain G S i).card : ℝ)⁻¹) ≤
        c ^ (J ∩ S.remaining).card) :
    cylinderMass (terminalLaw G hno S) J a ≤ cylinderPotential J a c S := by
  let : MeasurableSpace V := ⊤
  let : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  unfold terminalLaw
  split
  · rename_i h
    by_cases ha : PrescriptionsAgree J a S
    · have hfixed : ∀ i ∈ J, i ∉ S.remaining → recordedAssignment S i = a i := by
        intro i hi hni
        exact Option.some.inj
          ((recordedAssignment_recorded G S h.1 i hni).symm.trans (ha i hi hni))
      rw [Tail.cylinderMass_completion_eq_ambient _ _ _ _ _ _ _ _ _ hfixed]
      rw [cylinderPotential, ite_eq_left ha]
      calc
        _ ≤ Real.exp (((Tail.residualIndices S J).card : ℝ) / 2) *
            (∏ i ∈ Tail.residualIndices S J, ((domain G S i.1).card : ℝ)⁻¹) :=
          Tail.conditionalAmbientCylinder_le_of_tailCheck G S hno h.2 _ _
        _ ≤ _ := by
          rw [Tail.card_residualIndices,
            Tail.prod_residualIndices S J (fun i => ((domain G S i).card : ℝ)⁻¹)]
          exact hproduct
    · have hbad : ¬ ∀ i ∈ J, i ∉ S.remaining → recordedAssignment S i = a i := by
        intro hfixed
        apply ha
        intro i hi hni
        rw [recordedAssignment_recorded G S h.1 i hni, hfixed i hi hni]
      rw [Tail.cylinderMass_completion_eq_zero_of_prefix_mismatch _ _ _ _ _ _ _ _ _ hbad]
      exact cylinderPotential_nonneg J a hc S
  · simpa only [cylinderMass_failureLaw] using cylinderPotential_nonneg J a hc S

theorem cylinderMass_sourceTerminalLaw_le_potential (p : Parameters) (q : ℕ)
    (G : Input I V) (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (S : State I V) (J : Finset I) (a : I → V)
    (hc : 0 < p.c) (hq : 0 < q)
    (hscale : p.smin ≤ p.sizeScale q (p.lastMainTime q (Fintype.card I))) :
    cylinderMass (sourceTerminalLaw p q G hno S) J a ≤
      cylinderPotential J a (cylinderConstant p / q) S := by
  have hcost : 0 ≤ cylinderConstant p / q :=
    div_nonneg (cylinderConstant_pos p).le (Nat.cast_nonneg q)
  by_cases ht : SourceTailCheck p q G S
  · rw [sourceTerminalLaw, ite_eq_left ht]
    apply cylinderMass_terminalLaw_le_potential G hno S J a _ hcost
    apply tail_product_source_bound p q hc hq (J ∩ S.remaining) (domain G S)
    intro i hi
    calc
      p.smin * p.c * q / 2 ≤
          p.sizeScale q (p.lastMainTime q (Fintype.card I)) * p.c * q / 2 := by
        gcongr
      _ ≤ _ := ht.2 i (Finset.mem_inter.mp hi).2
  · simpa only [sourceTerminalLaw, ite_eq_right ht, cylinderMass_failureLaw] using
      cylinderPotential_nonneg J a hcost S

theorem cylinderMass_sourceTerminalOutcomeLaw_le_potential (p : Parameters) (q : ℕ)
    (G : Input I V) (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (J : Finset I) (a : I → V) (hc : 0 < p.c) (hq : 0 < q)
    (hscale : p.smin ≤ p.sizeScale q (p.lastMainTime q (Fintype.card I)))
    (out : Option (State I V)) :
    cylinderMass (sourceTerminalOutcomeLaw p q G hno out) J a ≤
      outcomePotential J a (cylinderConstant p / q) out := by
  cases out with
  | none => simp [sourceTerminalOutcomeLaw, outcomePotential]
  | some S =>
      exact cylinderMass_sourceTerminalLaw_le_potential p q G hno S J a hc hq hscale

theorem cylinderMass_finalLaw_source_bound (p : Parameters) (q : ℕ)
    (G : Input I V) (hp : p.Admissible) (hq : 2 ≤ q)
    (hPq : 2 * p.Pstar ≤ q) (hG : GraphBounds G q p.c p.C)
    (J : Finset I) (a : I → V) :
    cylinderMass (finalLaw p q G hG.2.1) J a ≤
      (cylinderConstant p / q) ^ J.card := by
  have hP : 0 ≤ p.Pstar := by
    unfold Parameters.Pstar
    have hc := hp.1
    have hC := hp.2.1
    positivity
  have hT : p.lastMainTime q (Fintype.card I) ≤ 3 * q := by
    calc
      p.lastMainTime q (Fintype.card I) ≤ Fintype.card I := Nat.sub_le _ _
      _ = 2 * (q + 1) := hG.1
      _ ≤ 3 * q := by omega
  have hscale : p.smin ≤ p.sizeScale q (p.lastMainTime q (Fintype.card I)) :=
    (SelectionScales.domain_bounds hP (by omega) hPq hT).1
  rw [cylinderMass_finalLaw]
  apply mainStageWeight_payoff_source_bound p q G J a hp hq hPq hG
  exact cylinderMass_sourceTerminalOutcomeLaw_le_potential p q G hG.2.1 J a
    hp.1 (by omega) hscale

end Nonempty

theorem cylinderMass_outputLaw_source_bound (p : Parameters) (q : ℕ)
    (G : Input I V) (hp : p.Admissible) (hq : 2 ≤ q)
    (hPq : 2 * p.Pstar ≤ q) (hG : GraphBounds G q p.c p.C)
    (J : Finset I) (a : I → V) :
    cylinderMass (outputLaw p q G hG.2.1) J a ≤
      (cylinderConstant p / q) ^ J.card := by
  let : Nonempty V := graphBounds_vertex_nonempty G q p.c p.C hp.1 (by omega) hG
  rw [outputLaw_eq_finalLaw]
  exact cylinderMass_finalLaw_source_bound p q G hp hq hPq hG J a

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionUniformAssembly
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Balanced.Selection.Process

noncomputable section
universe u v w

theorem combined_error_tendsto_zero {ε δ : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun q => |ε q| + |δ q|) atTop (𝓝 0) := by
  simpa only [abs_zero, zero_add] using hε.abs.add hδ.abs

theorem selectionStatement_of_uniform_output_bounds
    (hsuccess : ∀ p : Parameters, p.Admissible →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ q : ℕ in atTop, UniformSuccessEstimate.{u,v} p ε q)
    (hoccupancy : ∀ p : Parameters, p.Admissible →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ q : ℕ in atTop, UniformOccupancyEstimate.{u,v,w} p ε q) :
    SelectionStatement.{u,v,w} := by
  intro c C c₀ hc hC hc₀ hc₀le
  obtain ⟨p, hpc, hpC, hpc₀, hp⟩ :=
    Parameters.exists_admissible c C c₀ hc hC hc₀ hc₀le
  obtain ⟨ε, hε, hsuccess⟩ := hsuccess p hp
  obtain ⟨δ, hδ, hoccupancy⟩ := hoccupancy p hp
  obtain ⟨q₀, hq₀⟩ := eventually_atTop.mp
    ((hsuccess.and hoccupancy).and (Parameters.eventually_scale_regime p))
  refine ⟨cylinderConstant p, p.rho, (fun q => |ε q| + |δ q|), q₀,
    cylinderConstant_pos p, Parameters.rho_pos hp,
    (fun q => add_nonneg (abs_nonneg _) (abs_nonneg _)),
    combined_error_tendsto_zero hε hδ, ?_⟩
  intro q hq I V _ _ G hG
  have hG' : GraphBounds G q p.c p.C := by
    simpa only [hpc, hpC] using hG
  have hb := hq₀ q hq
  have hεle : ε q ≤ |ε q| + |δ q| :=
    (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hδle : δ q ≤ |ε q| + |δ q| :=
    (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  refine ⟨outputLaw p q G hG'.2.1, ?_, ?_, ?_⟩
  · exact (sub_le_sub_left hεle 1).trans (hb.1.1 I V G hG')
  · intro J prescribed
    exact cylinderMass_outputLaw_source_bound p q G hp hb.2.1 hb.2.2 hG' J prescribed
  · intro P D L _ _ _ A index line hline T hT
    have hT' : TrackedSets A T p.c₀ := by simpa only [hpc₀] using hT
    exact (hb.1.2 I V G hG' P D L A index line hline T hT').trans hδle

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionSuccessUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace Balanced.Selection.Process

universe u v w

theorem uniformSuccessEstimate_of_concentration
    (p : Parameters) (hp : p.Admissible) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hconcentration : ∀ᶠ q : ℕ in atTop,
      UniformConcentrationEstimate.{u,v} p ε q) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ᶠ q : ℕ in atTop, UniformSuccessEstimate.{u,v} p δ q := by
  refine ⟨fun q => ε q + 18 * (q : ℝ) ^ 3 * postcheckTail p q, ?_, ?_⟩
  · simpa only [zero_add] using hε.add
      (tendsto_source_postcheck_bound p (Parameters.Pstar_pos hp).le)
  · obtain ⟨N, hN⟩ := exists_uniform_success_threshold.{u,v} p hp
    filter_upwards [hconcentration, eventually_ge_atTop N] with q hc hq
    intro I V _ _ G hG
    have hs := hN q hq G hG
    have hb := hc I V G hG
    change 1 - (ε q + 18 * (q : ℝ) ^ 3 * postcheckTail p q) ≤ _
    linarith

theorem selectionStatement_of_uniform_concentration_occupancy_oai
    (hconcentration : ∀ p : Parameters, p.Admissible →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ q : ℕ in atTop, UniformConcentrationEstimate.{u,v} p ε q)
    (hoccupancy : ∀ p : Parameters, p.Admissible →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ q : ℕ in atTop, UniformOccupancyEstimate.{u,v,w} p ε q) :
    SelectionStatement.{u,v,w} := by
  apply selectionStatement_of_uniform_output_bounds ?_ hoccupancy
  intro p hp
  obtain ⟨ε, hε, hc⟩ := hconcentration p hp
  exact uniformSuccessEstimate_of_concentration p hp ε hε hc

end Balanced.Selection.Process

end

end OAI
end

theorem solution.{u, v, w} : type_of% @OAI.Balanced.Selection.Process.selectionStatement_of_uniform_concentration_occupancy_oai.{u, v, w} := @OAI.Balanced.Selection.Process.selectionStatement_of_uniform_concentration_occupancy_oai.{u, v, w}
