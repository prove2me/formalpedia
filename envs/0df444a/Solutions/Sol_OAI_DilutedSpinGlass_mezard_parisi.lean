-- Prove2me | solution 1 for OAI.DilutedSpinGlass.mezard_parisi
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:12:34.634995+00:00
-- url     : https://prove2.me/submissions/2dec07a4-843d-482c-9d11-1aa938fca20d

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Theorems.Thm_OAI_DilutedSpinGlass_PrescribedTree_finiteTrial_upper_fixedField
import Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_full_regular_covariance_selection
import Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_increment_cavityProxy_bound
import Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_poissonInsertionOn_comparison_tendsto_ae

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)

theorem expect_congr {f g : Ω → ℝ} (h : ∀ x, f x = g x) : P.expect f = P.expect g := by
  exact congrArg P.expect (funext h)

theorem expect_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : P.expect f ≤ P.expect g := by
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (P.nonneg x))

variable {n : ℕ}

theorem logMean_mono {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    P.logMean m f ≤ P.logMean m g := by
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (P.expMoment_pos _ _)
  exact P.expect_mono (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (h x) hm.le))

/-- Root-measurable uniform bounds pass unchanged through each power mean. -/
theorem logMean_stability {m c : ℝ} (hm : 0 < m) {f g : Ω → ℝ}
    (h : ∀ x, |f x - g x| ≤ c) : |P.logMean m f - P.logMean m g| ≤ c := by
  have hfg : P.logMean m f ≤ P.logMean m g + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).2; linarith)
  have hgf : P.logMean m g ≤ P.logMean m f + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_expect_le {f : Ω → ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    |P.expect f| ≤ B := by
  apply abs_le.mpr
  constructor
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).1)
    simpa only [expect_const] using h
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).2)
    simpa only [expect_const] using h

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_KernelTower
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

namespace KernelTower

variable {Ω : Type} [Fintype Ω]

theorem backwardLog_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, m i ≠ 0) (c : ℝ) : backwardLog n T m (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog]
    have heq : (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun _ => c)) =
        (fun _ => c) := by
      funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ)
    rw [heq, FiniteLaw.logMean_const _ (hm 0)]

/-- The uniform insertion bound, with full arbitrary depth-dependent priors. -/
theorem backwardLog_stability (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f g : FinitePath Ω n → ℝ} {c : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ c) :
    |backwardLog n T m f - backwardLog n T m g| ≤ c := by
  induction n with
  | zero => exact hfg ()
  | succ n ih =>
    apply T.1.logMean_stability (hm 0)
    intro x
    exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ) (fun y => hfg (x,y))

/-- Pointwise bounds survive every backward step, uniformly in depth. -/
theorem backwardLog_bound (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f : FinitePath Ω n → ℝ} {c : ℝ}
    (hf : ∀ x, |f x| ≤ c) : |backwardLog n T m f| ≤ c := by
  have h := backwardLog_stability n T m hm (g := fun _ => 0)
    (fun x => by simpa only [sub_zero] using hf x)
  rwa [backwardLog_const n T m (fun i => ne_of_gt (hm i)), sub_zero] at h

end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonMoments
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Uniform bounds survive averaging a physical root coordinate. -/
theorem abs_integral_le_bound {f : Ω → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (μ := μ) (f := f) (C := B) (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hB x))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkedPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

theorem poissonWeight_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℕ) = (r : ℝ) * poissonWeight r n := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Poisson add-one (the count part of pert:palm), including zero rate. -/
theorem poisson_add_one (r : ℝ≥0) (f : ℕ → ℝ)
    (hf : Integrable (fun n => f (n+1)) (poissonMeasure r)) :
    (∫ n : ℕ, (n : ℝ) * f n ∂poissonMeasure r) =
      (r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r := by
  have hs := (hasSum_integral_poissonMeasure hf).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ) * f (n+1))
      ((r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r) := by
    simp_rw [poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ) * f n) ht
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add] at ht'
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul, ← mul_assoc, poissonWeight] using ht'.tsum_eq

/-- Integrability of the count is proved from the same add-one recurrence. -/
theorem poisson_integrable_count (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)) r := by
    simp_rw [poissonWeight_succ_mul]
    unfold poissonWeight
    simpa only [mul_one] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ)) ht
  simp only [Nat.cast_zero, mul_zero, zero_add] at ht'
  simpa only [Real.norm_natCast, poissonWeight] using ht'.summable

@[simp] theorem poisson_mean (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  simpa using poisson_add_one r (fun _ => 1) (integrable_const 1)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_AnchorExtension
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
@[simp] theorem tilt_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ j, m j ≠ 0) (c : ℝ) : tilt n T m (fun _ => c) = T := by
  induction n with
  | zero =>
    change () = T
    cases T
    rfl
  | succ n ih =>
    simp only [tilt, backwardLog_const n _ _ (fun j => hm j.succ),
      FiniteLaw.tilt_const, ih _ _ (fun j => hm j.succ)]
    cases T
    rfl
end DilutedSpinGlass.KernelTower

open Filter Set
open scoped Topology BigOperators

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators

namespace FiniteLaw
variable {Ω Λ Γ : Type*} [Fintype Ω] [Fintype Λ] [Fintype Γ]

lemma uniform_expect [Nonempty Ω] (f : Ω → ℝ) :
    (uniform : FiniteLaw Ω).expect f = (∑ x, f x)/(Fintype.card Ω) := by
  simp only [expect,uniform,← Finset.mul_sum]
  ring

end FiniteLaw

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountedSpinMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
theorem abs_expect_sub_le {f g : Ω → ℝ} {C : ℝ} (h : ∀ x, |f x-g x| ≤ C) :
    |P.expect f-P.expect g| ≤ C := by
  rw [← expect_sub]
  exact P.abs_expect_le h
end DilutedSpinGlass.FiniteLaw

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PerturbedSizeCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass
open scoped NNReal

lemma scoreScale_mono : Monotone scoreScale := by
  intro M N hMN
  exact Real.rpow_le_rpow (Nat.cast_nonneg M) (by exact_mod_cast hMN) (by norm_num)

end DilutedSpinGlass

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalIndex
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace DilutedSpinGlass

theorem abs_spin (s : Spin) : |spin s| = 1 := by cases s <;> norm_num [spin]

theorem sum_exp_pos {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    0 < ∑ i, Real.exp (f i) :=
  Finset.sum_pos' (fun _ _ => (Real.exp_pos _).le)
    ⟨Classical.arbitrary ι, Finset.mem_univ _, Real.exp_pos _⟩

theorem logSumExp_stability {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) {C : ℝ} (h : ∀ i, |f i-g i| ≤ C) :
    |Real.log (∑ i, Real.exp (f i)) - Real.log (∑ i, Real.exp (g i))| ≤ C := by
  have aux (f g : ι → ℝ) (h : ∀ i, f i ≤ g i+C) :
      Real.log (∑ i, Real.exp (f i)) ≤ Real.log (∑ i, Real.exp (g i)) + C := by
    have hb : (∑ i, Real.exp (f i)) ≤ (∑ i, Real.exp (g i))*Real.exp C := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (h i))
    have hl := Real.log_le_log (sum_exp_pos f) hb
    rwa [Real.log_mul (sum_exp_pos g).ne' (Real.exp_pos C).ne', Real.log_exp] at hl
  exact abs_le.mpr ⟨by have := aux g f (fun i => by have := (abs_le.mp (h i)).1; linarith); linarith,
    by have := aux f g (fun i => by have := (abs_le.mp (h i)).2; linarith); linarith⟩

theorem logWeight_bound {p N k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) (σ : Fin N → Spin) :
    |logWeight theta h indices σ| ≤ (∑ j, ‖(theta j).1‖) + ∑ i, |h i| := by
  apply (abs_add_le _ _).trans
  apply add_le_add
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (theta j).1 (fun l => σ (indices j l))))
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => by
      simp only [abs_mul, abs_spin, mul_one, le_refl]))

theorem logPartition_bound {p N k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) :
    |logPartition theta h indices - (N:ℝ)*Real.log 2| ≤
      (∑ j, ‖(theta j).1‖) + ∑ i, |h i| := by
  have hs : Real.log (∑ _σ : Fin N → Spin, Real.exp (0:ℝ)) = (N:ℝ)*Real.log 2 := by
    simp only [Real.exp_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Fintype.card_fun, Fintype.card_fin, show Fintype.card Spin = 2 from rfl,
      Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  simpa only [logPartition, hs, sub_zero] using
    logSumExp_stability (logWeight theta h indices) (fun _ => 0)
      (fun σ => by simpa using logWeight_bound theta h indices σ)

theorem logWeight_stability {p N k : ℕ} (theta theta' : Fin k → InteractionSample p)
    (h h' : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) (σ : Fin N → Spin) :
    |logWeight theta h indices σ - logWeight theta' h' indices σ| ≤
      (∑ j, ‖(theta j).1-(theta' j).1‖) + ∑ i, |h i-h' i| := by
  have he : logWeight theta h indices σ - logWeight theta' h' indices σ =
      (∑ j, ((theta j).1-(theta' j).1) (fun l => σ (indices j l))) +
        ∑ i, (h i-h' i)*spin (σ i) := by
    simp only [logWeight, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm ((theta j).1-(theta' j).1)
        (fun l => σ (indices j l))))
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => by
      simp only [abs_mul, abs_spin, mul_one, le_refl]))

theorem logPartition_stability {p N k : ℕ} (theta theta' : Fin k → InteractionSample p)
    (h h' : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) :
    |logPartition theta h indices - logPartition theta' h' indices| ≤
      (∑ j, ‖(theta j).1-(theta' j).1‖) + ∑ i, |h i-h' i| :=
  logSumExp_stability _ _ (logWeight_stability theta theta' h h' indices)

theorem indexAverage_bound {p N k : ℕ} (hN : 0 < N)
    (theta : Fin k → InteractionSample p) (h : Fin N → ℝ) :
    |indexAverage theta h - (N:ℝ)*Real.log 2| ≤
      (∑ j, ‖(theta j).1‖) + ∑ i, |h i| := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hc : (0:ℝ) < Fintype.card (Fin k → Fin p → Fin N) :=
    Nat.cast_pos.mpr Fintype.card_pos
  rw [indexAverage, div_sub' (ne_of_gt hc), abs_div,
    abs_of_pos hc, div_le_iff₀ hc]
  rw [show (∑ indices : Fin k → Fin p → Fin N, logPartition theta h indices) -
      (Fintype.card (Fin k → Fin p → Fin N):ℝ) * ((N:ℝ)*Real.log 2) =
        ∑ indices : Fin k → Fin p → Fin N,
          (logPartition theta h indices - (N:ℝ)*Real.log 2) by simp [Finset.sum_sub_distrib]]
  calc
    _ ≤ ∑ _indices : Fin k → Fin p → Fin N,
        ((∑ j, ‖(theta j).1‖) + ∑ i, |h i|) :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun indices _ => logPartition_bound theta h indices))
    _ = _ := by simp [mul_comm, mul_add]

theorem continuous_logPartition {p N k : ℕ} (indices : Fin k → Fin p → Fin N) :
    Continuous (fun z : (Fin k → InteractionSample p) × (Fin N → ℝ) =>
      logPartition z.1 z.2 indices) := by
  unfold logPartition
  apply Continuous.log
  · unfold logWeight
    fun_prop
  · intro z
    exact (sum_exp_pos _).ne'

theorem continuous_indexAverage {p N k : ℕ} :
    Continuous (fun z : (Fin k → InteractionSample p) × (Fin N → ℝ) =>
      indexAverage z.1 z.2) := by
  unfold indexAverage
  exact (continuous_finsetSum _ (fun indices _ => continuous_logPartition indices)).div_const _


end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalAverages
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace DilutedSpinGlass

/-- Integrate a deterministic logarithmic stability estimate without imposing
moments beyond the integrable envelope. -/
theorem probabilistic_center_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f g : X → ℝ} {c : ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : Integrable g μ)
    (hb : ∀ᵐ x ∂μ, |f x-c| ≤ g x) :
    Integrable f μ ∧ |(∫ x, f x ∂μ)-c| ≤ ∫ x, g x ∂μ := by
  have hfc : Integrable (fun x => f x-c) μ :=
    hg.mono' (hf.sub aestronglyMeasurable_const) (by simpa only [Real.norm_eq_abs] using hb)
  have hfi : Integrable f μ := by
    simpa only [Pi.add_def, sub_add_cancel] using hfc.add (integrable_const c)
  refine ⟨hfi, ?_⟩
  have hi : (∫ x, f x ∂μ)-c = ∫ x, f x-c ∂μ := by
    rw [integral_sub hfi (integrable_const c)]
    simp
  rw [hi]
  exact abs_integral_le_integral_abs.trans (integral_mono_ae hfc.abs hg hb)

theorem indexAverage_integrable_and_fieldAverage_bound {p : ℕ} (M : Model p)
    (hM : Integrable (fun h : ℝ => |h|) M.field.toMeasure) {N k : ℕ}
    (hN : 0 < N) (theta : Fin k → InteractionSample p) :
    Integrable (fun h : Fin N → ℝ => indexAverage theta h)
      (Measure.pi (fun _ : Fin N => M.field.toMeasure)) ∧
    |fieldAverage M (N := N) theta - (N:ℝ)*Real.log 2| ≤
      (∑ j, ‖(theta j).1‖) + N * fieldMoment M := by
  have hi : Integrable (fun h : Fin N → ℝ => ∑ i, |h i|)
      (Measure.pi (fun _ : Fin N => M.field.toMeasure)) := by
    exact integrable_finsetSum _ (fun i _ => integrable_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) hM)
  have he : (∫ h : Fin N → ℝ, (∑ j, ‖(theta j).1‖) + ∑ i, |h i|
      ∂Measure.pi (fun _ : Fin N => M.field.toMeasure)) =
        (∑ j, ‖(theta j).1‖) + N * fieldMoment M := by
    rw [integral_add (integrable_const _) hi, integral_finsetSum _
      (fun i _ => integrable_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) hM)]
    simp only [integral_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) hM.aestronglyMeasurable]
    simp [fieldMoment]
  have hm : AEStronglyMeasurable (fun h : Fin N → ℝ => indexAverage theta h)
      (Measure.pi (fun _ : Fin N => M.field.toMeasure)) :=
    (continuous_indexAverage.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  simpa only [fieldAverage, Pi.add_apply, he] using probabilistic_center_bound
    (Measure.pi (fun _ : Fin N => M.field.toMeasure)) hm
      ((integrable_const _).add hi) (ae_of_all _ (indexAverage_bound hN theta))

theorem stronglyMeasurable_fieldAverage {p : ℕ} (M : Model p) (N k : ℕ) :
    StronglyMeasurable (fieldAverage M (N := N) (k := k)) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  exact (continuous_indexAverage (p := p) (N := N) (k := k)).stronglyMeasurable.integral_prod_right

theorem fieldAverage_integrable_and_disorderAverage_bound {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) {N : ℕ}
    (hN : 0 < N) (k : ℕ) :
    Integrable (fieldAverage M (N := N) (k := k))
      (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) ∧
    |disorderAverage M N k - (N:ℝ)*Real.log 2| ≤
      k * interactionMoment M + N * fieldMoment M := by
  have hi : Integrable (fun theta : Fin k → InteractionSample p => ∑ j, ‖(theta j).1‖)
      (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) :=
    integrable_finsetSum _ (fun j _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)
  have he : (∫ theta : Fin k → InteractionSample p,
      (∑ j, ‖(theta j).1‖) + N * fieldMoment M
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) =
        k * interactionMoment M + N * fieldMoment M := by
    rw [integral_add hi (integrable_const _), integral_finsetSum _
      (fun j _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)]
    simp only [integral_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ.aestronglyMeasurable]
    simp [interactionMoment]
  simpa only [disorderAverage, Pi.add_apply, he] using probabilistic_center_bound
    (Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
      (stronglyMeasurable_fieldAverage M N k).aestronglyMeasurable
      (hi.add (integrable_const _)) (ae_of_all _ (fun theta =>
        (indexAverage_integrable_and_fieldAverage_bound M hh hN theta).2))


theorem disorderAverage_integrable_and_pressure_bound {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) {N : ℕ} (hN : 0 < N) :
    Integrable (disorderAverage M N) (poissonMeasure (M.alpha * N)) ∧
      |pressure M N - Real.log 2| ≤ (M.alpha:ℝ) * interactionMoment M + fieldMoment M := by
  have hi : Integrable (fun k : ℕ => (k:ℝ) * interactionMoment M + N * fieldMoment M)
      (poissonMeasure (M.alpha * N)) :=
    ((poisson_integrable_count _).mul_const _).add (integrable_const _)
  have he : (∫ k : ℕ, (k:ℝ) * interactionMoment M + N * fieldMoment M
      ∂poissonMeasure (M.alpha * N)) =
      ((M.alpha:ℝ)*N) * interactionMoment M + N * fieldMoment M := by
    rw [integral_add ((poisson_integrable_count _).mul_const _) (integrable_const _),
      integral_mul_const, poisson_mean]
    simp
  have hb := probabilistic_center_bound (poissonMeasure (M.alpha * N))
    (f := disorderAverage M N) (c := (N:ℝ)*Real.log 2)
    StronglyMeasurable.of_discrete.aestronglyMeasurable hi
    (ae_of_all _ (fun k => (fieldAverage_integrable_and_disorderAverage_bound M hθ hh hN k).2))
  refine ⟨hb.1, ?_⟩
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hp : pressure M N = (∫ k, disorderAverage M N k ∂poissonMeasure (M.alpha * N)) / N := rfl
  rw [hp, div_sub' (ne_of_gt hNr), abs_div, abs_of_pos hNr, div_le_iff₀ hNr]
  rw [he] at hb
  nlinarith [hb.2]


end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinBaseComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw

lemma expect_uniform {B : Type} [Fintype B] [Nonempty B] (f : B → ℝ) :
    (uniform : FiniteLaw B).expect f = (∑ x, f x)/(Fintype.card B) := by
  simp only [expect,uniform,← Finset.mul_sum,div_eq_mul_inv]
  ring

end DilutedSpinGlass.FiniteLaw

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedRegularity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal

lemma clipReal_bound {C : ℝ} (hC : 0 ≤ C) (x : ℝ) : |clipReal C x| ≤ C := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

lemma clipReal_eq {C x : ℝ} (hx : |x| ≤ C) : clipReal C x = x := by
  simp only [clipReal,min_eq_right (abs_le.mp hx).2,max_eq_right (abs_le.mp hx).1]

lemma clipSample_eq {p : ℕ} {C : ℝ} {z : InteractionSample p}
    (hz : ∀ σ, |z.1 σ| ≤ C) : clipSample C z = z := by
  apply Prod.ext
  · funext σ; exact clipReal_eq (hz σ)
  · rfl

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualLowIncrement
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Z I : Type} [MeasurableSpace Z] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] {A : I → Type} [∀ i, Fintype (A i)]

lemma scoreScale_div {N : ℕ} (hN : 0 < N) : scoreScale N/N = (N:ℝ)^(-(1:ℝ)/4) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  rw [scoreScale]
  convert (Real.rpow_sub hn ((3:ℝ)/4) 1).symm using 1 <;> norm_num

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullCubeConditionalContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

lemma gridExponents_lower (L : ℕ) (j : Fin (L+1)) :
    ((L+1:ℕ):ℝ)⁻¹ ≤ gridExponents L j := by
  change _ ≤ (((j:ℕ)+1:ℕ):ℝ)/((L+1:ℕ):ℝ)
  rw [inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Nat.le_add_left 1 j.val)

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRegularSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p L : ℕ}

noncomputable local instance fullRegularSelectionDecidableEq_r5cae82_1 (β : Type) :
    DecidableEq β := Classical.decEq β
lemma gridExponents_pos (L : ℕ) (j : Fin (L+1)) :
    0 < gridExponents L j :=
  (inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos L))).trans_le (gridExponents_lower L j)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators

namespace DilutedSpinGlass

/-- Product message probabilities have total mass exactly one. -/
theorem product_q_sum {p : ℕ} (x : Fin p → ℝ) :
    (∑ s : Fin p → Spin, ∏ l, q (x l) (s l)) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [q_sum, Finset.prod_const_one]


/-- Uniform bounds on a finite probability-weighted exponential sum. -/
theorem weighted_exp_bounds {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {B : ℝ}
    (hf : ∀ i, |f i| ≤ B) :
    Real.exp (-B) ≤ ∑ i, w i * Real.exp (f i) ∧
      (∑ i, w i * Real.exp (f i)) ≤ Real.exp B := by
  have hlo : ∀ i, Real.exp (-B) ≤ Real.exp (f i) :=
    fun i => Real.exp_le_exp.mpr (abs_le.mp (hf i)).1
  have hhi : ∀ i, Real.exp (f i) ≤ Real.exp B :=
    fun i => Real.exp_le_exp.mpr (abs_le.mp (hf i)).2
  constructor
  · calc
      Real.exp (-B) = ∑ i, w i * Real.exp (-B) := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlo i) (hw i))
  · calc
      _ ≤ ∑ i, w i * Real.exp B :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hhi i) (hw i))
      _ = Real.exp B := by rw [← Finset.sum_mul, hs, one_mul]

theorem weighted_log_exp_bound {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {B : ℝ}
    (hf : ∀ i, |f i| ≤ B) :
    |Real.log (∑ i, w i * Real.exp (f i))| ≤ B := by
  obtain ⟨hlo, hhi⟩ := weighted_exp_bounds w f hw hs hf
  have hp := (Real.exp_pos _).trans_le hlo
  exact abs_le.mpr ⟨(Real.le_log_iff_exp_le hp).mpr hlo,
    (Real.log_le_iff_le_exp hp).mpr hhi⟩

theorem edge_pos {p : ℕ} (theta : Interaction p) (x : Fin p → ℝ) :
    0 < edge theta x := by
  have hb := (weighted_exp_bounds (B := ‖theta‖) (fun s : Fin p → Spin => ∏ l, q (x l) (s l)) theta
    (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
    (product_q_sum x) (fun s => norm_le_pi_norm theta s)).1
  simpa only [edge, mul_comm] using (Real.exp_pos _).trans_le hb

/-- The message-free uniform edge bound, with only the physical interaction norm. -/
theorem log_edge_bound {p : ℕ} (theta : Interaction p) (x : Fin p → ℝ) :
    |Real.log (edge theta x)| ≤ ‖theta‖ := by
  simpa only [edge, mul_comm] using
    weighted_log_exp_bound (B := ‖theta‖) (fun s : Fin p → Spin => ∏ l, q (x l) (s l)) theta
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm theta s)

/-- The uniform cavity-message bound; no message moments occur. -/
theorem message_bound {p : ℕ} (theta : Interaction p)
    (x : Fin (p - 1) → ℝ) (ε : Spin) : |message theta x ε| ≤ ‖theta‖ := by
  simpa only [message, mul_comm] using
    weighted_log_exp_bound (B := ‖theta‖) (fun s : Fin (p-1) → Spin => ∏ l, q (x l) (s l))
      (fun s => theta (appendSpin s ε))
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm theta (appendSpin s ε))

 
theorem siteLog_bound {p k : ℕ} (theta : Fin k → InteractionSample p)
    (h : ℝ) (x : (Fin k × Fin (p-1)) → ℝ) :
    |siteLog theta h x| ≤ |h| + ∑ j, ‖(theta j).1‖ := by
  have hf : ∀ ε : Spin,
      |h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε| ≤
        |h| + ∑ j, ‖(theta j).1‖ := by
    intro ε
    apply (abs_add_le _ _).trans
    apply add_le_add
    · simp only [abs_mul, abs_spin, mul_one, le_refl]
    · exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j _ => message_bound _ _ _))
  have hw : (∑ _ε : Spin, (1/2 : ℝ)) = 1 := by norm_num [Fintype.sum_bool]
  have hb := weighted_log_exp_bound (fun _ε : Spin => (1/2 : ℝ))
    (fun ε => h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε)
    (fun _ => by norm_num) hw hf
  simpa only [siteLog, ← Finset.mul_sum, one_div, div_eq_mul_inv, one_mul, mul_comm] using hb

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MeasureHierarchy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

namespace DilutedSpinGlass.MeasureMean

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem bounded_integrable {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ B) : Integrable f μ :=
  (integrable_const B).mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))

theorem exp_integrable {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ B) (m : ℝ) : Integrable (fun x => Real.exp (m*f x)) μ := by
  apply bounded_integrable μ (hf.const_mul m).exp
  intro x
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc m*f x ≤ |m*f x| := le_abs_self _
       _ = |m| * |f x| := abs_mul _ _
       _ ≤ |m| * B := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)

theorem exp_integral_pos {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ B) (m : ℝ) : 0 < ∫ x, Real.exp (m*f x) ∂μ :=
  integral_exp_pos (exp_integrable μ hf hb m)

theorem logMean_const {m : ℝ} (hm : m ≠ 0) (a : ℝ) :
    logMean μ m (fun _ => a) = a := by
  simp [logMean, Real.log_exp, hm]

theorem logMean_mono {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} {B C : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfb : ∀ x, |f x| ≤ B)
    (hgb : ∀ x, |g x| ≤ C) (hfg : ∀ x, f x ≤ g x) :
    logMean μ m f ≤ logMean μ m g := by
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (exp_integral_pos μ hf hfb m)
  exact integral_mono (exp_integrable μ hf hfb m) (exp_integrable μ hg hgb m)
    (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hfg x) hm.le))

theorem logMean_add_const {m : ℝ} (hm : m ≠ 0) {f : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) (a : ℝ) :
    logMean μ m (fun x => f x+a) = logMean μ m f+a := by
  unfold logMean
  simp_rw [mul_add, Real.exp_add]
  rw [integral_mul_const, Real.log_mul (ne_of_gt (exp_integral_pos μ hf hb m))
    (Real.exp_ne_zero _), Real.log_exp]
  field_simp

theorem logMean_stability {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} {B C D : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfb : ∀ x, |f x| ≤ B)
    (hgb : ∀ x, |g x| ≤ C) (hfg : ∀ x, |f x-g x| ≤ D) :
    |logMean μ m f-logMean μ m g| ≤ D := by
  have haddb (g : Ω → ℝ) (C : ℝ) (hg : ∀ x, |g x| ≤ C) (x : Ω) :
      |g x+D| ≤ C+|D| := (abs_add_le _ _).trans (add_le_add (hg x) le_rfl)
  have h1 := logMean_mono μ hm hf (hg.add_const D) hfb (haddb g C hgb)
    (fun x => by have := (abs_le.mp (hfg x)).2; linarith)
  have h2 := logMean_mono μ hm hg (hf.add_const D) hgb (haddb f B hfb)
    (fun x => by have := (abs_le.mp (hfg x)).1; linarith)
  rw [logMean_add_const μ hm.ne' hg hgb] at h1
  rw [logMean_add_const μ hm.ne' hf hfb] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem logMean_bound {m : ℝ} (hm : 0 < m) {f : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) : |logMean μ m f| ≤ B := by
  have h := logMean_stability μ hm hf measurable_const hb
    (fun _ => (by simp : |(0 : ℝ)| ≤ 0)) (by simpa using hb)
  simpa only [logMean_const μ hm.ne', sub_zero] using h

end DilutedSpinGlass.MeasureMean

namespace DilutedSpinGlass
attribute [local instance] OAI.DilutedSpinGlass.measureHierarchyContinuousMeasurableSpace
local instance measureHierarchyContinuousBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

theorem logMean_continuous_bound {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x| ≤ B)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) :
    Continuous (logMean r g m) ∧ ∀ eta, |logMean r g m eta| ≤ B := by
  induction r with
  | zero => exact ⟨hg, hB⟩
  | succ r ih =>
    obtain ⟨hc, hb⟩ := ih (fun i => m i.succ) (fun i => hm i.succ)
    let f := logMean r g (fun i => m i.succ)
    let F : (ι → Hierarchy r) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => Real.exp (m 0 * f x)) (Real.continuous_exp.comp (hc.const_mul (m 0)))
      (Real.exp (|m 0| * B)) (fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        exact (le_abs_self _).trans (by rw [abs_mul]; gcongr; exact hb x))
    have hpos (eta : ι → Hierarchy (r+1)) : 0 < ∫ x, F x ∂(ProbabilityMeasure.pi eta) :=
      MeasureMean.exp_integral_pos (ProbabilityMeasure.pi eta).toMeasure hc.measurable hb (m 0)
    have hcont : Continuous (fun eta : ι → Hierarchy (r+1) => ∫ x, F x ∂(ProbabilityMeasure.pi eta)) :=
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).comp
        ProbabilityMeasure.continuous_pi
    refine ⟨(hcont.log (fun eta => (hpos eta).ne')).div_const (m 0), ?_⟩
    intro eta
    exact MeasureMean.logMean_bound (ProbabilityMeasure.pi eta).toMeasure (hm 0) hc.measurable hb

 theorem trialLog_continuous_bound {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x| ≤ B)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) :
    Continuous (fun ζ => trialLog r ζ m g) ∧ ∀ ζ, |trialLog r ζ m g| ≤ B := by
  obtain ⟨hc,hb⟩ := logMean_continuous_bound r g hg hB m hm
  let F : (ι → Hierarchy r) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (logMean r g m) hc B (fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hpi : Continuous (fun ζ : Hierarchy (r+1) => ProbabilityMeasure.pi (fun _ : ι => ζ)) :=
    ProbabilityMeasure.continuous_pi.comp (continuous_pi (fun _ => continuous_id))
  refine ⟨(ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).comp hpi, ?_⟩
  intro ζ
  change |∫ x, F x ∂(ProbabilityMeasure.pi (fun _ : ι => ζ)).toMeasure| ≤ B
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := (ProbabilityMeasure.pi (fun _ : ι => ζ)).toMeasure)
      (ae_of_all _ (fun x => (show ‖F x‖ ≤ B from by simpa [F] using hb x))))

end DilutedSpinGlass

namespace DilutedSpinGlass
attribute [local instance] OAI.DilutedSpinGlass.measureHierarchyStabilityMeasurableSpace
local instance measureHierarchyStabilityBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

theorem logMean_stability {ι : Type} [Fintype ι] (r : ℕ)
    (f g : (ι → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) {B C D : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) (hD : ∀ x, |f x-g x| ≤ D)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (eta : ι → Hierarchy r) :
    |logMean r f m eta-logMean r g m eta| ≤ D := by
  induction r with
  | zero => exact hD eta
  | succ r ih =>
    obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hB (fun i => m i.succ) (fun i => hm i.succ)
    obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hC (fun i => m i.succ) (fun i => hm i.succ)
    exact MeasureMean.logMean_stability (ProbabilityMeasure.pi eta).toMeasure (hm 0)
      hfc.measurable hgc.measurable hfb hgb (ih (fun i => m i.succ) (fun i => hm i.succ))

theorem trialLog_stability {ι : Type} [Fintype ι] (r : ℕ)
    (f g : (ι → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) {B C D : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) (hD : ∀ x, |f x-g x| ≤ D)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1)) :
    |trialLog r ζ m f-trialLog r ζ m g| ≤ D := by
  obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hB m hm
  obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hC m hm
  let μ := (ProbabilityMeasure.pi (fun _ : ι => ζ)).toMeasure
  have hiF : Integrable (logMean r f m) μ := MeasureMean.bounded_integrable μ hfc.measurable hfb
  have hiG : Integrable (logMean r g m) μ := MeasureMean.bounded_integrable μ hgc.measurable hgb
  change |(∫ eta, logMean r f m eta ∂μ)-(∫ eta, logMean r g m eta ∂μ)| ≤ D
  rw [← integral_sub hiF hiG]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ (fun eta =>
      (show ‖logMean r f m eta - logMean r g m eta‖ ≤ D from by
        simpa only [Real.norm_eq_abs] using logMean_stability r f g hf hg hB hC hD m hm eta)))

 theorem continuous_q (s : Spin) : Continuous (fun x => q x s) := by
  unfold q
  apply (Real.continuous_exp.comp (continuous_id.mul continuous_const)).div
    (continuous_const.mul Real.continuous_cosh)
  intro x
  exact mul_ne_zero (by norm_num) (Real.cosh_pos x).ne'

 theorem continuous_edge {p : ℕ} (theta : Interaction p) : Continuous (edge theta) := by
  unfold edge
  apply continuous_finsetSum
  intro s _
  apply continuous_const.mul
  exact continuous_finsetProd _ (fun l _ => (continuous_q (s l)).comp (continuous_apply l))

 theorem continuous_log_edge {p : ℕ} (theta : Interaction p) :
    Continuous (fun x => Real.log (edge theta x)) :=
  (continuous_edge theta).log (fun x => (edge_pos theta x).ne')

 theorem continuous_message {p : ℕ} (theta : Interaction p) (ε : Spin) :
    Continuous (fun x => message theta x ε) := by
  unfold message
  apply Continuous.log
  · apply continuous_finsetSum
    intro s _
    apply continuous_const.mul
    exact continuous_finsetProd _ (fun l _ => (continuous_q (s l)).comp (continuous_apply l))
  · intro x
    apply ne_of_gt
    apply Finset.sum_pos
    · intro s _
      exact mul_pos (Real.exp_pos _) (Finset.prod_pos (fun l _ => q_pos _ _))
    · exact Finset.univ_nonempty

 theorem continuous_siteLog {p k : ℕ} (theta : Fin k → InteractionSample p) (h : ℝ) :
    Continuous (siteLog theta h) := by
  unfold siteLog
  apply Continuous.log
  · apply Continuous.div_const
    apply continuous_finsetSum
    intro ε _
    apply Real.continuous_exp.comp
    apply continuous_const.add
    apply continuous_finsetSum
    intro j _
    exact (continuous_message (theta j).1 ε).comp
      (continuous_pi (fun l => continuous_apply (j,l)))
  · intro x
    apply ne_of_gt
    exact div_pos (sum_exp_pos _) (by norm_num)

end DilutedSpinGlass

namespace DilutedSpinGlass

theorem weighted_exp_pos {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    0 < ∑ i, w i * Real.exp (f i) :=
  (Real.exp_pos (-‖f‖)).trans_le
    (weighted_exp_bounds w f hw hs (fun i => norm_le_pi_norm f i)).1

/-- Stability before any disorder averaging; no lower bound on the positive
message probabilities or moment condition on the messages occurs. -/
theorem weighted_log_exp_stability {ι : Type*} [Fintype ι] (w f g : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {D : ℝ}
    (hD : ∀ i, |f i-g i| ≤ D) :
    |Real.log (∑ i, w i * Real.exp (f i)) -
      Real.log (∑ i, w i * Real.exp (g i))| ≤ D := by
  have aux (f g : ι → ℝ) (h : ∀ i, f i ≤ g i+D) :
      Real.log (∑ i, w i * Real.exp (f i)) ≤
        Real.log (∑ i, w i * Real.exp (g i)) + D := by
    have hle : (∑ i, w i * Real.exp (f i)) ≤
        (∑ i, w i * Real.exp (g i)) * Real.exp D := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => by
        rw [mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h i)) (hw i))
    have hl := Real.log_le_log (weighted_exp_pos w f hw hs) hle
    rw [Real.log_mul (weighted_exp_pos w g hw hs).ne' (Real.exp_pos D).ne', Real.log_exp] at hl
    exact hl
  have hfg := aux f g (fun i => by have h := (abs_le.mp (hD i)).2; linarith)
  have hgf := aux g f (fun i => by have h := (abs_le.mp (hD i)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem log_edge_stability {p : ℕ} (theta theta' : Interaction p) (x : Fin p → ℝ) :
    |Real.log (edge theta x)-Real.log (edge theta' x)| ≤ ‖theta-theta'‖ := by
  simpa only [edge, mul_comm] using
    weighted_log_exp_stability (fun s : Fin p → Spin => ∏ l, q (x l) (s l)) theta theta'
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm (theta-theta') s)

theorem message_stability {p : ℕ} (theta theta' : Interaction p)
    (x : Fin (p-1) → ℝ) (ε : Spin) :
    |message theta x ε-message theta' x ε| ≤ ‖theta-theta'‖ := by
  simpa only [message, mul_comm] using
    weighted_log_exp_stability (fun s : Fin (p-1) → Spin => ∏ l, q (x l) (s l))
      (fun s => theta (appendSpin s ε)) (fun s => theta' (appendSpin s ε))
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm (theta-theta') (appendSpin s ε))

theorem siteLog_stability {p k : ℕ} (theta theta' : Fin k → InteractionSample p) (h h' : ℝ)
    (x : (Fin k × Fin (p-1)) → ℝ) :
    |siteLog theta h x - siteLog theta' h' x| ≤
      |h-h'| + ∑ j, ‖(theta j).1-(theta' j).1‖ := by
  have hf : ∀ ε : Spin,
      |(h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε) -
        (h' * spin ε + ∑ j, message (theta' j).1 (fun l => x (j,l)) ε)| ≤
        |h-h'| + ∑ j, ‖(theta j).1-(theta' j).1‖ := by
    intro ε
    rw [show (h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε) -
        (h' * spin ε + ∑ j, message (theta' j).1 (fun l => x (j,l)) ε) =
        (h-h') * spin ε + ∑ j, (message (theta j).1 (fun l => x (j,l)) ε -
          message (theta' j).1 (fun l => x (j,l)) ε) by rw [Finset.sum_sub_distrib]; ring]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · simp only [abs_mul, abs_spin, mul_one, le_refl]
    · exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j _ => message_stability _ _ _ _))
  have hw : (∑ _ε : Spin, (1/2 : ℝ)) = 1 := by norm_num [Fintype.sum_bool]
  have hb := weighted_log_exp_stability (fun _ε : Spin => (1/2 : ℝ))
    (fun ε => h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε)
    (fun ε => h' * spin ε + ∑ j, message (theta' j).1 (fun l => x (j,l)) ε)
    (fun _ => by norm_num) hw hf
  simpa only [siteLog, ← Finset.mul_sum, one_div, div_eq_mul_inv, one_mul, mul_comm] using hb

theorem trial_edge_stability {p : ℕ} (r : ℕ) (theta theta' : Interaction p)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1)) :
    |trialLog r ζ m (fun x => Real.log (edge theta x)) -
      trialLog r ζ m (fun x => Real.log (edge theta' x))| ≤ ‖theta-theta'‖ :=
  trialLog_stability r _ _ (continuous_log_edge theta) (continuous_log_edge theta')
    (log_edge_bound theta) (log_edge_bound theta') (log_edge_stability theta theta') m hm ζ

theorem trial_site_stability {p k : ℕ} (r : ℕ)
    (theta theta' : Fin k → InteractionSample p) (h h' : ℝ)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1)) :
    |trialLog r ζ m (siteLog theta h)-trialLog r ζ m (siteLog theta' h')| ≤
      |h-h'| + ∑ j, ‖(theta j).1-(theta' j).1‖ :=
  trialLog_stability r _ _ (continuous_siteLog theta h) (continuous_siteLog theta' h')
    (siteLog_bound theta h) (siteLog_bound theta' h') (siteLog_stability theta theta' h h') m hm ζ

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteEncoding
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Set
open scoped NNReal BigOperators

namespace FiniteLaw
variable {Ω : Type} [Fintype Ω]

noncomputable local instance finiteEncodingDecidableEq_r5cae82_1 (type : Type) :
    DecidableEq type := Classical.decEq type
lemma integral_asProbability {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : FiniteLaw Ω) (f : Ω → X) (g : X → ℝ) :
    ∫ x, g x ∂(P.asProbability f)=P.expect (fun a => g (f a)) := by
  rw [asProbability,integral_atomicProbability]
  rfl

end FiniteLaw

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.finiteEncodingReindexMeasurableSpace
local instance finiteEncodingReindexBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

lemma piCongrLeft_const_apply {ι κ X : Type} [MeasurableSpace X]
    (e : ι ≃ κ) (x : κ → X) :
    (MeasurableEquiv.piCongrLeft (fun _ : ι => X) e.symm) x = fun i => x (e i) := by
  funext i
  change (Equiv.piCongrLeft (fun _ : ι => X) e.symm) x i = _
  rw [Equiv.piCongrLeft_apply]
  simp

lemma logMean_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (r : ℕ) (g : (ι → ℝ) → ℝ) (m : Fin r → ℝ) (eta : ι → Hierarchy r) :
    logMean r (fun x : κ → ℝ => g (fun i => x (e i))) m (fun j => eta (e.symm j)) =
      logMean r g m eta := by
  induction r with
  | zero => simp [logMean]
  | succ r ih =>
    change ι → ProbabilityMeasure (Hierarchy r) at eta
    simp only [logMean]
    congr 2
    have he := (measurePreserving_piCongrLeft
      (fun i : ι => (eta i).toMeasure) e.symm).integral_comp'
        (fun x : ι → Hierarchy r => Real.exp (m 0*logMean r g (fun i => m i.succ) x))
    rw [← he]
    apply integral_congr_ae
    filter_upwards [] with x
    congr 2
    simpa only [Equiv.apply_symm_apply,piCongrLeft_const_apply] using ih (fun i => m i.succ) (fun i => x (e i))

lemma trialLog_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (r : ℕ) (g : (ι → ℝ) → ℝ) (m : Fin r → ℝ) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun x : κ → ℝ => g (fun i => x (e i))) = trialLog r ζ m g := by
  change ProbabilityMeasure (Hierarchy r) at ζ
  unfold trialLog
  have he := (measurePreserving_piCongrLeft
    (fun _ : ι => ζ.toMeasure) e.symm).integral_comp' (logMean r g m)
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with x
  simpa only [Equiv.apply_symm_apply,piCongrLeft_const_apply] using logMean_reindex e r g m (fun i => x (e i))

lemma integral_sumPi_exp_add {ι κ X : Type} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (μ : ι ⊕ κ → Measure X) [∀ i,IsProbabilityMeasure (μ i)]
    (f : (ι → X) → ℝ) (g : (κ → X) → ℝ) (t : ℝ) :
    (∫ x : ι ⊕ κ → X,Real.exp (t*(f (fun i => x (.inl i))+g (fun j => x (.inr j))))
      ∂Measure.pi μ) =
    (∫ x,Real.exp (t*f x) ∂Measure.pi (fun i => μ (.inl i)))*
      (∫ y,Real.exp (t*g y) ∂Measure.pi (fun j => μ (.inr j))) := by
  have he := (measurePreserving_sumPiEquivProdPi μ).integral_comp'
    (fun z : (ι → X) × (κ → X) => Real.exp (t*f z.1)*Real.exp (t*g z.2))
  simpa only [mul_add,Real.exp_add,MeasurableEquiv.coe_sumPiEquivProdPi,Equiv.sumPiEquivProdPi_apply] using he.trans (integral_prod_mul (μ := Measure.pi (fun i => μ (.inl i)))
    (ν := Measure.pi (fun j => μ (.inr j)))
    (fun x => Real.exp (t*f x)) (fun y => Real.exp (t*g y)))

lemma logMean_sum_separate {ι κ : Type} [Fintype ι] [Fintype κ]
    (r : ℕ) (f : (ι → ℝ) → ℝ) (g : (κ → ℝ) → ℝ)
    (hf : Continuous f) (hg : Continuous g) {B C : ℝ}
    (hb : ∀ x,|f x|≤B) (hc : ∀ x,|g x|≤C)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (eta : ι ⊕ κ → Hierarchy r) :
    logMean r (fun x => f (fun i => x (.inl i))+g (fun j => x (.inr j))) m eta =
      logMean r f m (fun i => eta (.inl i))+logMean r g m (fun j => eta (.inr j)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change ι ⊕ κ → ProbabilityMeasure (Hierarchy r) at eta
    simp only [logMean]
    have he : (∫ x : ι ⊕ κ → Hierarchy r,Real.exp (m 0 *
        logMean r (fun x => f (fun i => x (.inl i))+g (fun j => x (.inr j)))
          (fun i => m i.succ) x) ∂Measure.pi (fun i => (eta i).toMeasure)) =
        (∫ x,Real.exp (m 0*logMean r f (fun i => m i.succ) x)
          ∂Measure.pi (fun i => (eta (.inl i)).toMeasure))*
        (∫ y,Real.exp (m 0*logMean r g (fun i => m i.succ) y)
          ∂Measure.pi (fun j => (eta (.inr j)).toMeasure)) := by
      simp_rw [ih (fun i => m i.succ) (fun i => hm i.succ)]
      exact integral_sumPi_exp_add _ _ _ _
    rw [he]
    obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hb (fun i => m i.succ) (fun i => hm i.succ)
    obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hc (fun i => m i.succ) (fun i => hm i.succ)
    rw [Real.log_mul
      (MeasureMean.exp_integral_pos _ hfc.measurable hfb (m 0)).ne'
      (MeasureMean.exp_integral_pos _ hgc.measurable hgb (m 0)).ne',add_div]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_QSubtreePotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.qSubtreePotentialMeasurableSpace
local instance qSubtreePotentialBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

lemma logMean_constant {ι : Type} [Fintype ι] (r : ℕ) (c : ℝ)
    (m : Fin r → ℝ) (hm : ∀ i,m i≠0) (eta : ι → Hierarchy r) :
    logMean r (fun _ : ι → ℝ => c) m eta = c := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change ι → ProbabilityMeasure (Hierarchy r) at eta
    simp only [logMean,ih (fun i => m i.succ) (fun i => hm i.succ),integral_const,
      probReal_univ,smul_eq_mul,one_mul,Real.log_exp]
    exact mul_div_cancel_left₀ c (hm 0)

lemma trialLog_constant {ι : Type} [Fintype ι] (r : ℕ) (c : ℝ)
    (m : Fin r → ℝ) (hm : ∀ i,m i≠0) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun _ : ι → ℝ => c) = c := by
  change ProbabilityMeasure (Hierarchy r) at ζ
  simp [trialLog,logMean_constant r c m hm]

lemma trialLog_sum_separate {ι κ : Type} [Fintype ι] [Fintype κ]
    (r : ℕ) (f : (ι → ℝ) → ℝ) (g : (κ → ℝ) → ℝ)
    (hf : Continuous f) (hg : Continuous g) {B C : ℝ}
    (hb : ∀ x,|f x|≤B) (hc : ∀ x,|g x|≤C)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun x : ι ⊕ κ → ℝ => f (fun i => x (.inl i))+g (fun j => x (.inr j))) =
      trialLog r ζ m f+trialLog r ζ m g := by
  change ProbabilityMeasure (Hierarchy r) at ζ
  unfold trialLog
  simp_rw [logMean_sum_separate r f g hf hg hb hc m hm]
  obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hb m hm
  obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hc m hm
  have hfi := MeasureMean.bounded_integrable (Measure.pi (fun _ : ι => ζ.toMeasure)) hfc.measurable hfb
  have hgi := MeasureMean.bounded_integrable (Measure.pi (fun _ : κ => ζ.toMeasure)) hgc.measurable hgb
  have he := (measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ κ => ζ.toMeasure)).integral_comp'
    (fun z : (ι → Hierarchy r) × (κ → Hierarchy r) => logMean r f m z.1+logMean r g m z.2)
  rw [integral_add (hfi.comp_fst (Measure.pi (fun _ : κ => ζ.toMeasure)))
      (hgi.comp_snd (Measure.pi (fun _ : ι => ζ.toMeasure))) ] at he
  simpa only [MeasurableEquiv.coe_sumPiEquivProdPi,Equiv.sumPiEquivProdPi_apply,
    integral_fun_fst,integral_fun_snd,probReal_univ,one_smul] using he

lemma trialLog_blocks {ι : Type} [Fintype ι] (r k : ℕ)
    (g : Fin k → (ι → ℝ) → ℝ) (hg : ∀ j,Continuous (g j))
    (B : Fin k → ℝ) (hb : ∀ j x,|g j x|≤B j)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun x : Fin k × ι → ℝ => ∑ j,g j (fun i => x (j,i))) =
      ∑ j,trialLog r ζ m (g j) := by
  induction k with
  | zero => simpa using trialLog_constant (ι := Fin 0 × ι) r 0 m (fun i => (hm i).ne') ζ
  | succ k ih =>
    let v := fun x : Fin k × ι → ℝ => ∑ j,g j.succ (fun i => x (j,i))
    have hv : Continuous v := continuous_finsetSum _ (fun j _ =>
      (hg j.succ).comp (continuous_pi (fun i => continuous_apply (j,i))))
    have hvb (x : Fin k × ι → ℝ) : |v x|≤∑ j : Fin k,B j.succ :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => hb j.succ _))
    have he := trialLog_reindex (blockSuccEquiv ι k) r
      (fun x : ι ⊕ (Fin k×ι) → ℝ => g 0 (fun i => x (.inl i))+v (fun j => x (.inr j))) m ζ
    have hh : (fun x : Fin (k+1) × ι → ℝ =>
        g 0 (fun i => x (blockSuccEquiv ι k (.inl i)))+
          v (fun j => x (blockSuccEquiv ι k (.inr j)))) =
        fun x => ∑ j,g j (fun i => x (j,i)) := by
      funext x
      simp only [blockSuccEquiv,Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr,v,Fin.sum_univ_succ]
    rw [hh] at he
    rw [he,trialLog_sum_separate r (g 0) v (hg 0) hv (hb 0) hvb m hm ζ,
      ih (fun j => g j.succ) (fun j => hg j.succ) (fun j => B j.succ) (fun j => hb j.succ),Fin.sum_univ_succ]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TopologyDecay
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
namespace FiniteLaw
variable {Ω β : Type} [Fintype Ω] [Fintype β]

attribute [local instance] OAI.DilutedSpinGlass.finiteMapDecEq
lemma expect_map (P : FiniteLaw Ω) (f : Ω → β) (g : β → ℝ) :
    (P.map f).expect g=P.expect (fun a => g (f a)) := by
  classical
  change (∑ b, P.expect (fun a => if f a=b then 1 else 0)*g b)=_
  simp_rw [← expect_mul_right]
  rw [← expect_fintype_sum]
  apply expect_congr
  intro a
  simp

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteHierarchyDense
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators

lemma atomicProbability_reindex {X ι κ : Type} [MeasurableSpace X] [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : ι → X) (w : AtomicWeights ι) :
    atomicProbability (fun j => x (e.symm j))
      ⟨fun j => w.val (e.symm j),by rw [e.symm.sum_comp w.val]; exact w.property⟩ =
      atomicProbability x w := by
  apply Subtype.ext
  change (∑ j : κ,(w.val (e.symm j):ℝ≥0∞) • Measure.dirac (x (e.symm j))) = _
  exact e.symm.sum_comp (fun i => (w.val i:ℝ≥0∞) • Measure.dirac (x i))

lemma continuous_atomicProbability_atoms {X ι : Type} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T1Space X] [Fintype ι] (w : AtomicWeights ι) :
    Continuous (fun x : ι → X => atomicProbability x w) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [integral_atomicProbability]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (f.continuous.comp (continuous_apply i)))

/-- Finite laws supported on any dense set are weakly dense. -/
lemma finite_atomic_dense {X : Type} [MetricSpace X] [SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (D : Set X) (hD : Dense D) :
    Dense {μ : ProbabilityMeasure X | ∃ (n : ℕ) (x : Fin n → X) (w : AtomicWeights (Fin n)),
      (∀ i,x i ∈ D) ∧ μ = atomicProbability x w} := by
  classical
  let S := {μ : ProbabilityMeasure X | ∃ (n : ℕ) (x : Fin n → X) (w : AtomicWeights (Fin n)),
      (∀ i,x i ∈ D) ∧ μ = atomicProbability x w}
  have ha (ι : Type) [Fintype ι] (x : ι → X) (w : AtomicWeights ι) :
      atomicProbability x w ∈ closure S := by
    have hd : Dense (Set.univ.pi (fun _ : ι => D)) := dense_pi Set.univ (fun _ _ => hD)
    obtain ⟨z,hz,ht⟩ := mem_closure_iff_seq_limit.mp (hd x)
    apply isClosed_closure.mem_of_tendsto ((continuous_atomicProbability_atoms w).tendsto x |>.comp ht)
    apply Eventually.of_forall
    intro n
    apply subset_closure
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι,fun j => z n (e.symm j),
      ⟨fun j => w.val (e.symm j),by rw [e.symm.sum_comp w.val]; exact w.property⟩,?_,?_⟩
    · intro j
      exact hz n (e.symm j) (Set.mem_univ _)
    · exact (atomicProbability_reindex e (z n) w).symm
  intro μ
  let h : StronglyMeasurable (id : X → X) := stronglyMeasurable_id
  apply isClosed_closure.mem_of_tendsto (probability_map_tendsto μ h.approx h.tendsto_approx)
  apply Eventually.of_forall
  intro n
  obtain ⟨w,hw⟩ := simple_map_atomic (h.approx n) μ
  rw [← hw]
  exact ha _ _ w

attribute [local instance] OAI.DilutedSpinGlass.finiteHierarchyDenseMeasurableSpace
local instance finiteHierarchyDenseBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

lemma finiteHierarchy_dense (r : ℕ) : Dense {ζ : Hierarchy r | FiniteHierarchy r ζ} := by
  induction r with
  | zero => simpa only [FiniteHierarchy,Set.ofPred_true] using (dense_univ : Dense (Set.univ : Set (Hierarchy 0)))
  | succ r ih =>
    let : MetrizableSpace (Hierarchy r) := (hierarchy_properties r).1
    let : MetricSpace (Hierarchy r) := metrizableSpaceMetric (Hierarchy r)
    let : SeparableSpace (Hierarchy r) := (hierarchy_properties r).2
    exact finite_atomic_dense {ζ : Hierarchy r | FiniteHierarchy r ζ} ih

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TrialPhysical
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter
open scoped Topology BigOperators NNReal

lemma trial_edge_lipschitz {p : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) :
    LipschitzWith 1 (fun θ : Interaction p => trialLog r ζ m (fun x => Real.log (edge θ x))) := by
  apply LipschitzWith.of_dist_le_mul
  intro θ θ'
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul] using trial_edge_stability r θ θ' m hm ζ

lemma trial_site_lipschitz {p k : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) :
    LipschitzWith (k+1) (fun z : (Fin k → InteractionSample p) × ℝ => trialLog r ζ m (siteLog z.1 z.2)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq]
  have h1 : |z.2-w.2|≤dist z w := by
    change |z.2-w.2|≤ max (dist z.1 w.1) (dist z.2 w.2)
    simpa only [Real.dist_eq] using le_max_right (dist z.1 w.1) (dist z.2 w.2)
  have h2 : ∑ j,‖(z.1 j).1-(w.1 j).1‖≤(k:ℝ)*dist z w := by
    calc
      _ ≤ ∑ j : Fin k,dist z w := Finset.sum_le_sum (fun j _ => by
        rw [← dist_eq_norm]
        exact (show dist (z.1 j).1 (w.1 j).1≤dist (z.1 j) (w.1 j) from le_max_left _ _).trans
          ((dist_le_pi_dist z.1 w.1 j).trans (show dist z.1 w.1≤dist z w from le_max_left _ _)))
      _ = _ := by simp
  have h := trial_site_stability r z.1 w.1 z.2 w.2 m hm ζ
  push_cast
  nlinarith

lemma trial_edge_bound {p : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (θ : Interaction p) :
    |trialLog r ζ m (fun x => Real.log (edge θ x))|≤‖θ‖ :=
  (trialLog_continuous_bound r _ (continuous_log_edge θ) (log_edge_bound θ) m hm).2 ζ

lemma trial_site_bound {p k : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (θ : Fin k → InteractionSample p) (h : ℝ) :
    |trialLog r ζ m (siteLog θ h)|≤|h|+∑ j,‖(θ j).1‖ :=
  (trialLog_continuous_bound r _ (continuous_siteLog θ h) (siteLog_bound θ h) m hm).2 ζ

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FunctionalContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal
variable {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)

include hm in
lemma integrable_trial_site_field (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {k : ℕ} (ζ : Hierarchy (r+1)) (θ : Fin k → InteractionSample p) :
    Integrable (fun h => trialLog r ζ m (siteLog θ h)) M.field.toMeasure := by
  apply (hh.add (integrable_const (∑ j,‖(θ j).1‖))).mono'
    (((trial_site_lipschitz r m hm ζ).continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_site_bound r m hm ζ θ h)

include hm in
lemma trialSiteField_bound (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {k : ℕ} (ζ : Hierarchy (r+1)) (θ : Fin k → InteractionSample p) :
    |trialSiteField M m ζ θ|≤(∫ h : ℝ,|h| ∂M.field.toMeasure)+∑ j,‖(θ j).1‖ := by
  have hb := norm_integral_le_of_norm_le (f := fun h => trialLog r ζ m (siteLog θ h)) (hh.add (integrable_const (∑ j,‖(θ j).1‖)))
    (ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_site_bound r m hm ζ θ h))
  simp only [Pi.add_apply] at hb
  simpa only [trialSiteField,Real.norm_eq_abs,integral_add hh (integrable_const _),integral_const,
    probReal_univ,one_smul] using hb

include hm in
lemma stronglyMeasurable_trialSiteField (ζ : Hierarchy (r+1)) (k : ℕ) :
    StronglyMeasurable (trialSiteField M m (k := k) ζ) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  exact ((trial_site_lipschitz (p := p) (k := k) r m hm ζ).continuous.stronglyMeasurable).integral_prod_right

include hm in
lemma trialSiteField_continuous {k : ℕ} (θ : Fin k → InteractionSample p)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    Continuous (fun ζ : Hierarchy (r+1) => trialSiteField M m ζ θ) := by
  apply continuous_of_dominated (bound := fun h : ℝ => |h|+∑ j,‖(θ j).1‖)
  · intro ζ
    exact (integrable_trial_site_field M m hm hh ζ θ).aestronglyMeasurable
  · intro ζ
    exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_site_bound r m hm ζ θ h)
  · exact hh.add (integrable_const _)
  · exact ae_of_all _ (fun h => (trialLog_continuous_bound r _ (continuous_siteLog θ h)
      (siteLog_bound θ h) m hm).1)

lemma interaction_sum_integrable (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) (k : ℕ) :
    Integrable (fun θ : Fin k → InteractionSample p => ∑ j,‖(θ j).1‖)
      (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) :=
  integrable_finsetSum _ (fun _ _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)

lemma integral_interaction_sum (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) (k : ℕ) :
    (∫ θ : Fin k → InteractionSample p,∑ j,‖(θ j).1‖ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) =
      k*(∫ z : InteractionSample p,‖z.1‖ ∂M.disorder.toMeasure) := by
  rw [integral_finsetSum _ (fun j _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)]
  simp only [integral_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ.aestronglyMeasurable,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

include hm in
lemma integrable_trialSiteField (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (ζ : Hierarchy (r+1)) (k : ℕ) :
    Integrable (trialSiteField M m (k := k) ζ) (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) := by
  apply ((integrable_const _).add (interaction_sum_integrable M hθ k)).mono'
    (stronglyMeasurable_trialSiteField M m hm ζ k).aestronglyMeasurable
  exact ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteField_bound M m hm hh ζ θ)

include hm in
lemma trialSiteDisorder_bound (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (ζ : Hierarchy (r+1)) (k : ℕ) :
    |trialSiteDisorder M m ζ k|≤(∫ h : ℝ,|h| ∂M.field.toMeasure)+k*(∫ z : InteractionSample p,‖z.1‖ ∂M.disorder.toMeasure) := by
  have hb := norm_integral_le_of_norm_le (f := trialSiteField M m (k := k) ζ) ((integrable_const _).add (interaction_sum_integrable M hθ k))
    (ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteField_bound M m hm hh ζ θ))
  simp only [Pi.add_apply] at hb
  simpa only [trialSiteDisorder,Real.norm_eq_abs,integral_add (integrable_const _) (interaction_sum_integrable M hθ k),
    integral_const,probReal_univ,one_smul,integral_interaction_sum M hθ k] using hb

include hm in
lemma trialSiteDisorder_continuous (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    Continuous (fun ζ : Hierarchy (r+1) => trialSiteDisorder M m ζ k) := by
  apply continuous_of_dominated (bound := fun θ : Fin k → InteractionSample p =>
    (∫ h : ℝ,|h| ∂M.field.toMeasure)+∑ j,‖(θ j).1‖)
  · intro ζ; exact (stronglyMeasurable_trialSiteField M m hm ζ k).aestronglyMeasurable
  · intro ζ; exact ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteField_bound M m hm hh ζ θ)
  · exact (integrable_const _).add (interaction_sum_integrable M hθ k)
  · exact ae_of_all _ (fun θ => trialSiteField_continuous M m hm θ hh)

include hm in
lemma functional_continuous (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    Continuous (fun ζ : Hierarchy (r+1) => functional M r ζ m) := by
  have hs : Continuous (fun ζ : Hierarchy (r+1) => ∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p)) := by
    apply continuous_of_dominated (bound := fun k : ℕ =>
      (∫ h : ℝ,|h| ∂M.field.toMeasure)+k*(∫ z : InteractionSample p,‖z.1‖ ∂M.disorder.toMeasure))
    · intro ζ; exact (measurable_of_countable _).aestronglyMeasurable
    · intro ζ; exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteDisorder_bound M m hm hθ hh ζ k)
    · exact (integrable_const _).add ((poisson_integrable_count _).mul_const _)
    · exact ae_of_all _ (trialSiteDisorder_continuous M m hm hθ hh)
  have he : Continuous (fun ζ : Hierarchy (r+1) => ∫ θ : InteractionSample p,
      trialLog r ζ m (fun x => Real.log (edge θ.1 x)) ∂M.disorder.toMeasure) := by
    apply continuous_of_dominated (bound := fun θ : InteractionSample p => ‖θ.1‖)
    · intro ζ
      exact (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
    · intro ζ; exact ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_edge_bound r m hm ζ θ.1)
    · exact hθ
    · exact ae_of_all _ (fun θ => (trialLog_continuous_bound r _ (continuous_log_edge θ.1) (log_edge_bound θ.1) m hm).1)
  exact (continuous_const.add hs).sub (continuous_const.mul he)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinLogContinuous
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
open scoped BigOperators
variable {ι : Type} [Fintype ι]
lemma spinLog_bound (F : (ι → Spin) → ℝ) {C : ℝ} (hF : ∀ s, |F s|≤C) (x : ι → ℝ) :
    |spinLog F x|≤C := by
  classical
  apply weighted_log_exp_bound _ _ (fun s => (Finset.prod_pos (fun i _ => q_pos _ _)).le) _ hF
  rw [← Fintype.prod_sum]
  simp only [q_sum, Finset.prod_const_one]
lemma spinLog_continuous (F : (ι → Spin) → ℝ) : Continuous (spinLog F) := by
  classical
  apply Continuous.log
  · exact continuous_finsetSum _ (fun s _ =>
      (continuous_finsetProd _ (fun i _ => (continuous_q (s i)).comp (continuous_apply i))).mul_const _)
  · intro x
    apply ne_of_gt
    exact Finset.sum_pos (fun s _ => mul_pos (Finset.prod_pos (fun i _ => q_pos _ _)) (Real.exp_pos _))
      Finset.univ_nonempty
end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MixedPatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open KernelTower _root_.MeasureTheory

lemma exponents_nonempty (r : ℕ) : ∃ m : Fin r → ℝ,Exponents m := by
  refine ⟨fun i => ((i:ℕ)+1:ℝ)/(r+1),?_,?_⟩
  · intro i j hij
    apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < r+1)).mpr
    simpa only [add_comm] using
      (add_lt_add_right (Nat.cast_lt.mpr hij : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ)) 1)
  · intro i
    constructor
    · positivity
    · rw [div_lt_one (by positivity : (0:ℝ) < r+1)]
      simpa only [add_comm] using
        (add_lt_add_right (Nat.cast_lt.mpr i.isLt : ((i : ℕ) : ℝ) < (r : ℝ)) 1)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RealEncoding
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma mapModel_interaction_integrable {p : ℕ} (M : Model p)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hi : Integrable (fun z => ‖(T z).1‖) M.disorder.toMeasure) :
    Integrable (fun z : InteractionSample p => ‖z.1‖) (mapModel M T g hT hg).disorder.toMeasure := by
  change Integrable (fun z : InteractionSample p => ‖z.1‖) (Measure.map T M.disorder.toMeasure)
  exact (integrable_map_measure (by fun_prop) hT.aemeasurable).mpr hi

lemma mapModel_field_integrable {p : ℕ} (M : Model p)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hi : Integrable (fun z => |g z|) M.field.toMeasure) :
    Integrable (fun z : ℝ => |z|) (mapModel M T g hT hg).field.toMeasure := by
  change Integrable (fun z : ℝ => |z|) (Measure.map g M.field.toMeasure)
  exact (integrable_map_measure (by fun_prop) hg.aemeasurable).mpr hi

lemma integral_pi_map {ι X Y : Type} [Fintype ι] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → Y) (hg : Measurable g)
    (F : (ι → Y) → ℝ) (hF : Measurable F) :
    (∫ y,F y ∂Measure.pi (fun _ : ι => Measure.map g μ)) =
      ∫ x,F (fun i => g (x i)) ∂Measure.pi (fun _ : ι => μ) := by
  let : IsProbabilityMeasure (Measure.map g μ) :=
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).mpr inferInstance
  rw [← Measure.pi_map_pi (fun _ : ι => hg.aemeasurable)]
  exact integral_map (Measurable.of_eval (fun index => hg.comp (measurable_pi_apply index))).aemeasurable hF.aestronglyMeasurable

lemma indexAverage_mapModel {p N k : ℕ} (M : Model p)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g) (θ : Fin k → InteractionSample p) :
    fieldAverage (N := N) (mapModel M T g hT hg) θ =
      ∫ h : Fin N → ℝ,indexAverage θ (fun i => g (h i)) ∂Measure.pi (fun _ : Fin N => M.field.toMeasure) := by
  change (∫ h : Fin N → ℝ,indexAverage θ h ∂Measure.pi (fun _ : Fin N => Measure.map g M.field.toMeasure))=_
  exact integral_pi_map _ g hg _ (continuous_indexAverage.comp (continuous_const.prodMk continuous_id)).measurable

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.hierarchyTranslationMeasurableSpace
local instance hierarchyTranslationBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

lemma logMean_add_constant {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x|≤B)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (a : ℝ) (eta : ι → Hierarchy r) :
    logMean r (fun x => g x+a) m eta=logMean r g m eta+a := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [logMean,ih (fun i => m i.succ) (fun i => hm i.succ)]
    obtain ⟨hc,hb⟩ := logMean_continuous_bound r g hg hB (fun i => m i.succ) (fun i => hm i.succ)
    exact MeasureMean.logMean_add_const (ProbabilityMeasure.pi eta).toMeasure (hm 0).ne' hc.measurable hb a

lemma trialLog_add_constant {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x|≤B)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (a : ℝ) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun x => g x+a)=trialLog r ζ m g+a := by
  unfold trialLog
  simp_rw [logMean_add_constant r g hg hB m hm a]
  obtain ⟨hc,hb⟩ := logMean_continuous_bound r g hg hB m hm
  let μ : ProbabilityMeasure (ι → Hierarchy r) := ProbabilityMeasure.pi (fun _ : ι => ζ)
  change (∫ x,logMean r g m x+a ∂μ.toMeasure)=(∫ x,logMean r g m x ∂μ.toMeasure)+a
  rw [integral_add (MeasureMean.bounded_integrable μ.toMeasure hc.measurable hb) (integrable_const a)]
  simp
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Set TopologicalSpace
open scoped BigOperators NNReal
attribute [local instance] OAI.DilutedSpinGlass.realEncodingMeasurableSpace
local instance realEncodingBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

namespace FiniteLaw
lemma asProbability_map {Ω Λ X : Type} [Fintype Ω] [Fintype Λ]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [MetrizableSpace X]
    (P : FiniteLaw Ω) (f : Ω → Λ) (v : Λ → X) :
    (P.map f).asProbability v = P.asProbability (fun x => v (f x)) := by
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  apply Subtype.ext
  change ((P.map f).asProbability v).toMeasure = (P.asProbability (fun x => v (f x))).toMeasure
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  simp only [integral_asProbability,expect_map]
end FiniteLaw

namespace KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

attribute [local instance] OAI.DilutedSpinGlass.realEncodingMeasurableSpace
lemma realEncode_embed (f : Ω → Λ) (g : Λ → Ω)
    (h : Function.LeftInverse g f) (r : ℕ) (T : KernelTower Ω r)
    (V : FinitePath Ω r → ℝ) :
    realEncode r (embed f g r T) (fun y => V (pathMap g r y)) = realEncode r T V := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change FiniteLaw Ω × (Ω → KernelTower Ω r) at T
    change (Ω × FinitePath Ω r) → ℝ at V
    rcases T with ⟨P,Q⟩
    let : MetrizableSpace (Hierarchy r) := (hierarchy_properties r).1
    change (P.map f).asProbability (fun a => realEncode r (embed f g r (Q (g a)))
      (fun y => V (g a,pathMap g r y))) =
      P.asProbability (fun a => realEncode r (Q a) (fun y => V (a,y)))
    have hc (a : Λ) := ih (Q (g a)) (fun y => V (g a,y))
    simp_rw [hc]
    rw [FiniteLaw.asProbability_map]
    congr 1
    funext a
    rw [h a]

end KernelTower

/-- Every genuinely finitely branching measure hierarchy has a finite alphabet
realization. Padding changes no law; in particular this imposes no restriction
on the original variational class after density. -/
lemma finiteHierarchy_realization (r : ℕ) (ζ : Hierarchy r) (hζ : FiniteHierarchy r ζ) :
    ∃ (n : ℕ) (_hn : 0 < n) (T : KernelTower (Fin n) r) (V : FinitePath (Fin n) r → ℝ),
      KernelTower.realEncode r T V = ζ := by
  classical
  induction r with
  | zero => exact ⟨1,by omega,(),fun _ => ζ,rfl⟩
  | succ r ih =>
    obtain ⟨k,x,w,hx,rfl⟩ := hζ
    choose n hn T V hV using fun i => ih (x i) (hx i)
    let P : FiniteLaw (Fin k) := ⟨fun i => w.val i,fun i => (w.val i).coe_nonneg,
      by simpa only [NNReal.coe_sum,NNReal.coe_one] using congrArg ((↑) : ℝ≥0 → ℝ) w.property⟩
    have hk : 0 < k := by
      by_contra hk
      have hk0 : k=0 := by omega
      subst k
      have hh := P.total
      simp at hh
    let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
    let (i : Fin k) : Nonempty (Fin (n i)) := ⟨⟨0,hn i⟩⟩
    let d : (i : Fin k) → Fin (n i) := fun i => ⟨0,hn i⟩
    let Ω := Fin k × ((i : Fin k) → Fin (n i))
    let f (i : Fin k) (a : Fin (n i)) : Ω := (i,Function.update d i a)
    let g (i : Fin k) (a : Ω) : Fin (n i) := a.2 i
    have hgf (i : Fin k) : Function.LeftInverse (g i) (f i) := by
      intro a
      exact Function.update_self i a d
    let U : KernelTower Ω (r+1) :=
      (P.map (fun i => (i,d)), fun a => KernelTower.embed (f a.1) (g a.1) r (T a.1))
    let W : FinitePath Ω (r+1) → ℝ := fun y =>
      V y.1.1 (KernelTower.pathMap (g y.1.1) r y.2)
    have hU : KernelTower.realEncode (r+1) U W = atomicProbability x w := by
      let : MetrizableSpace (Hierarchy r) := (hierarchy_properties r).1
      change (P.map (fun i => (i,d))).asProbability (fun a =>
        KernelTower.realEncode r (KernelTower.embed (f a.1) (g a.1) r (T a.1))
          (fun y => V a.1 (KernelTower.pathMap (g a.1) r y))) = _
      simp_rw [KernelTower.realEncode_embed _ _ (hgf _),hV]
      rw [FiniteLaw.asProbability_map]
      congr 1
    let e := Fintype.equivFin Ω
    refine ⟨Fintype.card Ω,Fintype.card_pos,
      KernelTower.embed e e.symm (r+1) U,
      fun y => W (KernelTower.pathMap e.symm (r+1) y),?_⟩
    rw [KernelTower.realEncode_embed e e.symm e.symm_apply_apply]
    exact hU

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_IntegralError
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma integrate_error {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f g E : X → ℝ} (hf : AEStronglyMeasurable f μ) (hg : Integrable g μ)
    (hE : Integrable E μ) (h : ∀ᵐ x ∂μ,|f x-g x|≤E x) :
    Integrable f μ ∧ |(∫ x,f x ∂μ)-(∫ x,g x ∂μ)|≤∫ x,E x ∂μ := by
  have hd : Integrable (fun x => f x-g x) μ := hE.mono' (hf.sub hg.aestronglyMeasurable) (by simpa only [Real.norm_eq_abs] using h)
  have hfi : Integrable f μ := by simpa only [Pi.add_def,sub_add_cancel] using hd.add hg
  refine ⟨hfi,?_⟩
  rw [← integral_sub hfi hg]
  calc
    _ ≤ ∫ x,|f x-g x| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x-g x)
    _ ≤ _ := integral_mono_ae hd.abs hE h

lemma integrable_pi_sum {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {g : X → ℝ} (hg : Integrable g μ) :
    Integrable (fun x : ι → X => ∑ i,g (x i)) (Measure.pi (fun _ : ι => μ)) :=
  integrable_finsetSum _ (fun _ _ => integrable_comp_eval (μ := fun _ : ι => μ) hg)

lemma integral_pi_sum {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {g : X → ℝ} (hg : Integrable g μ) :
    (∫ x : ι → X,∑ i,g (x i) ∂Measure.pi (fun _ : ι => μ))=(Fintype.card ι:ℝ)*(∫ x,g x ∂μ) := by
  rw [integral_finsetSum _ (fun i _ => integrable_comp_eval (μ := fun _ : ι => μ) hg)]
  simp only [integral_comp_eval (μ := fun _ : ι => μ) hg.aestronglyMeasurable,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

lemma indexAverage_stability {p N k : ℕ} (hN : 0<N) (θ θ' : Fin k → InteractionSample p)
    (h h' : Fin N → ℝ) :
    |indexAverage θ h-indexAverage θ' h'|≤∑ j,‖(θ j).1-(θ' j).1‖+∑ i,|h i-h' i| := by
  let : NeZero N := ⟨ne_of_gt hN⟩
  unfold indexAverage
  rw [← FiniteLaw.uniform_expect,← FiniteLaw.uniform_expect]
  apply FiniteLaw.abs_expect_sub_le
  intro i
  exact logPartition_stability θ θ' h h' i

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FunctionalStability
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma fieldAverage_map_stability {p N k : ℕ} (M : Model p) (hN : 0<N)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hd : Integrable (fun h => |g h-h|) M.field.toMeasure) (θ : Fin k → InteractionSample p) :
    |fieldAverage (N := N) (mapModel M T g hT hg) (fun j => T (θ j))-fieldAverage (N := N) M θ|≤
      (∑ j,‖(T (θ j)).1-(θ j).1‖)+(N:ℝ)*(∫ h,|g h-h| ∂M.field.toMeasure) := by
  rw [indexAverage_mapModel]
  let C := ∑ j,‖(T (θ j)).1-(θ j).1‖
  have hfm : Measurable (fun h : Fin N → ℝ => indexAverage (fun j => T (θ j)) (fun i => g (h i))) :=
    ((continuous_indexAverage (p := p) (N := N) (k := k)).comp (continuous_const.prodMk continuous_id)).measurable.comp (Measurable.of_eval (fun index => hg.comp (measurable_pi_apply index)))
  have he := integrate_error (Measure.pi (fun _ : Fin N => M.field.toMeasure)) hfm.aestronglyMeasurable
    (indexAverage_integrable_and_fieldAverage_bound M hh hN θ).1
    ((integrable_const C).add (integrable_pi_sum M.field.toMeasure hd))
    (ae_of_all _ (fun h => indexAverage_stability hN (fun j => T (θ j)) θ (fun i => g (h i)) h))
  have heq : (∫ h : Fin N → ℝ,C+∑ i,|g (h i)-h i| ∂Measure.pi (fun _ : Fin N => M.field.toMeasure))=
      C+(N:ℝ)*(∫ h,|g h-h| ∂M.field.toMeasure) := by
    rw [integral_add (integrable_const C) (integrable_pi_sum M.field.toMeasure hd),integral_pi_sum M.field.toMeasure hd]
    simp
  simpa only [Pi.add_def,heq,fieldAverage] using he.2

lemma disorderAverage_map_eq {p : ℕ} (M : Model p)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g) (N k : ℕ) :
    disorderAverage (mapModel M T g hT hg) N k=
      ∫ θ : Fin k → InteractionSample p,fieldAverage (N := N) (mapModel M T g hT hg) (fun j => T (θ j))
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  change (∫ θ : Fin k → InteractionSample p,fieldAverage (N := N) (mapModel M T g hT hg) θ
    ∂Measure.pi (fun _ : Fin k => Measure.map T M.disorder.toMeasure))=_
  exact integral_pi_map _ T hT _ (stronglyMeasurable_fieldAverage (mapModel M T g hT hg) N k).measurable

lemma disorderAverage_map_stability {p N : ℕ} (M : Model p) (hN : 0<N)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hD : Integrable (fun z => ‖(T z).1-z.1‖) M.disorder.toMeasure)
    (hd : Integrable (fun h => |g h-h|) M.field.toMeasure) (k : ℕ) :
    |disorderAverage (mapModel M T g hT hg) N k-disorderAverage M N k|≤
      (k:ℝ)*(∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure)+(N:ℝ)*(∫ h,|g h-h| ∂M.field.toMeasure) := by
  rw [disorderAverage_map_eq]
  let d := (N:ℝ)*(∫ h,|g h-h| ∂M.field.toMeasure)
  have hfm : Measurable (fun θ : Fin k → InteractionSample p =>
      fieldAverage (N := N) (mapModel M T g hT hg) (fun j => T (θ j))) :=
    (stronglyMeasurable_fieldAverage (mapModel M T g hT hg) N k).measurable.comp
      (Measurable.of_eval (fun index => hT.comp (measurable_pi_apply index)))
  have he := integrate_error (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) hfm.aestronglyMeasurable
    (fieldAverage_integrable_and_disorderAverage_bound M hθ hh hN k).1
    ((integrable_pi_sum M.disorder.toMeasure hD).add (integrable_const d))
    (ae_of_all _ (fieldAverage_map_stability M hN hh T g hT hg hd))
  have heq : (∫ θ : Fin k → InteractionSample p,(∑ j,‖(T (θ j)).1-(θ j).1‖)+d
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure))=
      (k:ℝ)*(∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure)+d := by
    rw [integral_add (integrable_pi_sum M.disorder.toMeasure hD) (integrable_const d),integral_pi_sum M.disorder.toMeasure hD]
    simp
  simpa only [Pi.add_def,heq,disorderAverage] using he.2

/-- Uniform first-moment stability of the exact pinned physical pressure. -/
lemma pressure_map_stability {p N : ℕ} (M : Model p) (hN : 0<N)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hD : Integrable (fun z => ‖(T z).1-z.1‖) M.disorder.toMeasure)
    (hd : Integrable (fun h => |g h-h|) M.field.toMeasure) :
    |pressure (mapModel M T g hT hg) N-pressure M N|≤
      (M.alpha:ℝ)*(∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure)+(∫ h,|g h-h| ∂M.field.toMeasure) := by
  let D := ∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure
  let d := ∫ h,|g h-h| ∂M.field.toMeasure
  have he := integrate_error (poissonMeasure (M.alpha*N)) StronglyMeasurable.of_discrete.aestronglyMeasurable
    (disorderAverage_integrable_and_pressure_bound M hθ hh hN).1
    (((poisson_integrable_count _).mul_const D).add (integrable_const ((N:ℝ)*d)))
    (ae_of_all _ (disorderAverage_map_stability M hN hθ hh T g hT hg hD hd))
  have heq : (∫ k : ℕ,(k:ℝ)*D+(N:ℝ)*d ∂poissonMeasure (M.alpha*N))=(M.alpha:ℝ)*N*D+N*d := by
    rw [integral_add ((poisson_integrable_count _).mul_const D) (integrable_const _),integral_mul_const,poisson_mean]
    simp
  have hb : |(∫ k,disorderAverage (mapModel M T g hT hg) N k ∂poissonMeasure (M.alpha*N))-
      (∫ k,disorderAverage M N k ∂poissonMeasure (M.alpha*N))|≤(M.alpha:ℝ)*N*D+N*d := by
    simpa only [Pi.add_def,Pi.mul_def,heq] using he.2
  change |((∫ k,disorderAverage (mapModel M T g hT hg) N k ∂poissonMeasure (M.alpha*N))/N)-
      ((∫ k,disorderAverage M N k ∂poissonMeasure (M.alpha*N))/N)|≤_
  rw [← sub_div,abs_div,abs_of_pos (show (0:ℝ)<N from Nat.cast_pos.mpr hN),div_le_iff₀ (show (0:ℝ)<N from Nat.cast_pos.mpr hN)]
  dsimp [D,d] at hb
  nlinarith

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma trialSiteField_map_eq {p r k : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g) (θ : Fin k → InteractionSample p) :
    trialSiteField (mapModel M T g hT hg) m ζ θ =
      ∫ h,trialLog r ζ m (siteLog θ (g h)) ∂M.field.toMeasure := by
  change (∫ h,trialLog r ζ m (siteLog θ h) ∂Measure.map g M.field.toMeasure)=_
  exact integral_map hg.aemeasurable
    (((trial_site_lipschitz r m hm ζ).continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)

lemma trialSiteField_map_stability {p r k : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hd : Integrable (fun h => |g h-h|) M.field.toMeasure) (θ : Fin k → InteractionSample p) :
    |trialSiteField (mapModel M T g hT hg) m ζ (fun j => T (θ j))-trialSiteField M m ζ θ|≤
      (∫ h,|g h-h| ∂M.field.toMeasure)+∑ j,‖(T (θ j)).1-(θ j).1‖ := by
  rw [trialSiteField_map_eq M m hm]
  have hfm : Measurable (fun h => trialLog r ζ m (siteLog (fun j => T (θ j)) (g h))) :=
    ((trial_site_lipschitz r m hm ζ).continuous.comp (continuous_const.prodMk continuous_id)).measurable.comp hg
  have he := integrate_error M.field.toMeasure hfm.aestronglyMeasurable
    (integrable_trial_site_field M m hm hh ζ θ)
    (hd.add (integrable_const (∑ j,‖(T (θ j)).1-(θ j).1‖)))
    (ae_of_all _ (fun h => trial_site_stability r (fun j => T (θ j)) θ (g h) h m hm ζ))
  simpa only [trialSiteField,Pi.add_def,integral_add hd (integrable_const _),integral_const,
    probReal_univ,one_smul] using he.2

lemma trialSiteDisorder_map_eq {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g) (k : ℕ) :
    trialSiteDisorder (mapModel M T g hT hg) m ζ k =
      ∫ θ : Fin k → InteractionSample p,trialSiteField (mapModel M T g hT hg) m ζ (fun j => T (θ j))
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  change (∫ θ : Fin k → InteractionSample p,trialSiteField (mapModel M T g hT hg) m ζ θ
    ∂Measure.pi (fun _ : Fin k => Measure.map T M.disorder.toMeasure))=_
  exact integral_pi_map _ T hT _ (stronglyMeasurable_trialSiteField (mapModel M T g hT hg) m hm ζ k).measurable

lemma trialSiteDisorder_map_stability {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hD : Integrable (fun z => ‖(T z).1-z.1‖) M.disorder.toMeasure)
    (hd : Integrable (fun h => |g h-h|) M.field.toMeasure) (k : ℕ) :
    |trialSiteDisorder (mapModel M T g hT hg) m ζ k-trialSiteDisorder M m ζ k|≤
      (∫ h,|g h-h| ∂M.field.toMeasure)+(k:ℝ)*(∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure) := by
  rw [trialSiteDisorder_map_eq M m hm]
  let d := ∫ h,|g h-h| ∂M.field.toMeasure
  have hfm : Measurable (fun θ : Fin k → InteractionSample p =>
      trialSiteField (mapModel M T g hT hg) m ζ (fun j => T (θ j))) :=
    (stronglyMeasurable_trialSiteField (mapModel M T g hT hg) m hm ζ k).measurable.comp
      (Measurable.of_eval (fun index => hT.comp (measurable_pi_apply index)))
  have he := integrate_error (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) hfm.aestronglyMeasurable
    (integrable_trialSiteField M m hm hθ hh ζ k)
    ((integrable_const d).add (integrable_pi_sum M.disorder.toMeasure hD))
    (ae_of_all _ (trialSiteField_map_stability M m hm ζ hh T g hT hg hd))
  have heq : (∫ θ : Fin k → InteractionSample p,d+∑ j,‖(T (θ j)).1-(θ j).1‖
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure))=
      d+(k:ℝ)*(∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure) := by
    rw [integral_add (integrable_const d) (integrable_pi_sum M.disorder.toMeasure hD),integral_pi_sum M.disorder.toMeasure hD]
    simp
  simpa only [Pi.add_def,heq,trialSiteDisorder] using he.2

lemma functional_map_stability {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hD : Integrable (fun z => ‖(T z).1-z.1‖) M.disorder.toMeasure)
    (hd : Integrable (fun h => |g h-h|) M.field.toMeasure) :
    |functional (mapModel M T g hT hg) r ζ m-functional M r ζ m|≤
      (M.alpha:ℝ)*((p:ℝ)+((p-1:ℕ):ℝ))*(∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure)+
      (∫ h,|g h-h| ∂M.field.toMeasure) := by
  let D := ∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure
  let d := ∫ h,|g h-h| ∂M.field.toMeasure
  have hsi : Integrable (trialSiteDisorder M m ζ) (poissonMeasure (M.alpha*p)) := by
    apply ((integrable_const _).add ((poisson_integrable_count _).mul_const _)).mono'
      StronglyMeasurable.of_discrete.aestronglyMeasurable
    exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs,Pi.add_def,Pi.mul_def] using (trialSiteDisorder_bound M m hm hθ hh ζ k))
  have hs := integrate_error (poissonMeasure (M.alpha*p)) StronglyMeasurable.of_discrete.aestronglyMeasurable
    hsi ((integrable_const d).add ((poisson_integrable_count _).mul_const D))
    (ae_of_all _ (trialSiteDisorder_map_stability M m hm ζ hθ hh T g hT hg hD hd))
  have hsbound : |(∫ k,trialSiteDisorder (mapModel M T g hT hg) m ζ k ∂poissonMeasure (M.alpha*p))-
      (∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p))|≤d+(M.alpha:ℝ)*p*D := by
    simpa only [Pi.add_def,Pi.mul_def,integral_add (integrable_const d) ((poisson_integrable_count _).mul_const D),
      integral_const,probReal_univ,one_smul,integral_mul_const,poisson_mean,NNReal.coe_mul,NNReal.coe_natCast] using hs.2
  have hei : Integrable (fun z : InteractionSample p => trialLog r ζ m (fun x => Real.log (edge z.1 x))) M.disorder.toMeasure := by
    apply hθ.mono' (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Function.comp_apply] using trial_edge_bound r m hm ζ z.1)
  have he := integrate_error M.disorder.toMeasure
    (((trial_edge_lipschitz r m hm ζ).continuous.measurable.comp (measurable_fst.comp hT)).aestronglyMeasurable)
    hei hD (ae_of_all _ (fun z => trial_edge_stability r (T z).1 z.1 m hm ζ))
  have heq : (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x))
      ∂(mapModel M T g hT hg).disorder.toMeasure)=
      ∫ z,trialLog r ζ m (fun x => Real.log (edge (T z).1 x)) ∂M.disorder.toMeasure := by
    change (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂Measure.map T M.disorder.toMeasure)=_
    exact integral_map hT.aemeasurable (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
  unfold functional
  change |(Real.log 2 + (∫ k,trialSiteDisorder (mapModel M T g hT hg) m ζ k ∂poissonMeasure (M.alpha*p)) -
      (M.alpha:ℝ)*(p-1:ℕ)*(∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂(mapModel M T g hT hg).disorder.toMeasure)) -
      (Real.log 2 + (∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p)) -
      (M.alpha:ℝ)*(p-1:ℕ)*(∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂M.disorder.toMeasure))|≤_
  rw [heq]
  have hc : 0≤(M.alpha:ℝ)*(p-1:ℕ) := mul_nonneg M.alpha.coe_nonneg (Nat.cast_nonneg _)
  have h := he.2
  dsimp [D,d] at hsbound
  have hhbound := abs_sub
    ((∫ k,trialSiteDisorder (mapModel M T g hT hg) m ζ k ∂poissonMeasure (M.alpha*p))-
      (∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p)))
    ((M.alpha:ℝ)*(p-1:ℕ)*((∫ z,trialLog r ζ m (fun x => Real.log (edge (T z).1 x)) ∂M.disorder.toMeasure)-
      (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂M.disorder.toMeasure)))
  rw [abs_mul,abs_of_nonneg hc] at hhbound
  simp only [Function.comp_apply] at h
  convert hhbound.trans (add_le_add hsbound (mul_le_mul_of_nonneg_left h hc)) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try ring_nf

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ d,0 < m d) (ζ : Hierarchy (r+1))

include hm

lemma trialDisorderAt_measurable (k : ℕ) : Measurable (trialDisorderAt M m ζ k) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  exact (trial_site_lipschitz r m hm ζ).continuous.stronglyMeasurable.integral_prod_left.measurable

lemma trialDisorderAt_bound
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (k : ℕ) (h : ℝ) : |trialDisorderAt M m ζ k h|≤|h|+k*interactionMoment M := by
  have hb := norm_integral_le_of_norm_le (f := fun z : Fin k → InteractionSample p => trialLog r ζ m (siteLog z h))
    ((integrable_const |h|).add (interaction_sum_integrable M hθ k))
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using (trial_site_bound r m hm ζ z h)))
  simpa only [trialDisorderAt,Real.norm_eq_abs,Pi.add_apply,
    integral_add (integrable_const _) (interaction_sum_integrable M hθ k),
    integral_const,probReal_univ,one_smul,integral_interaction_sum M hθ k,interactionMoment] using hb

lemma trialSite_integrable_prod
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    Integrable (fun z : (Fin k → InteractionSample p)×ℝ => trialLog r ζ m (siteLog z.1 z.2))
      ((Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  apply ((hh.comp_snd _).add ((interaction_sum_integrable M hθ k).comp_fst _)).mono'
    (trial_site_lipschitz r m hm ζ).continuous.aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using (trial_site_bound r m hm ζ z.1 z.2))

lemma trialDisorderAt_integral
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    (∫ h,trialDisorderAt M m ζ k h ∂M.field.toMeasure)=trialSiteDisorder M m ζ k :=
  (integral_integral_swap (trialSite_integrable_prod M m hm ζ hθ hh k)).symm

lemma trialDisorderAt_joint_integrable
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (t : ℝ≥0) :
    Integrable (fun z : ℕ×ℝ => trialDisorderAt M m ζ z.1 z.2)
      ((poissonMeasure t).prod M.field.toMeasure) := by
  apply ((hh.comp_snd _).add (((poisson_integrable_count t).mul_const (interactionMoment M)).comp_fst _)).mono'
  · exact (measurable_from_prod_countable_right (fun k => trialDisorderAt_measurable M m hm ζ k)).aestronglyMeasurable
  · exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using (trialDisorderAt_bound M m hm ζ hθ z.1 z.2))

lemma trialPoisson_field_order
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (t : ℝ≥0) :
    (∫ h,∫ k,trialDisorderAt M m ζ k h ∂poissonMeasure t ∂M.field.toMeasure)=
      ∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure t := by
  rw [← integral_integral_swap (trialDisorderAt_joint_integrable M m hm ζ hθ hh t)]
  simp_rw [trialDisorderAt_integral M m hm ζ hθ hh]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SameInsertionAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma sameInsertionAverage_bound (hm : ∀ i, 0 < m i) (a : ℕ)
    (F : (Fin a → Spin) → ℝ) {C : ℝ} (hF : ∀ s, |F s|≤C) (z : FullRootState Y X I M) :
    |sameInsertionAverage T Q m base old V a F z|≤C := by
  apply FiniteLaw.abs_expect_le
  intro i
  exact backwardLog_bound (L+1) _ m hm (fun y => hF _)

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalInsertionComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators Topology
variable {p : ℕ}

lemma reservoirInsertion_bound (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (a : ℕ) (F : (Fin a → Spin) → ℝ) {D : ℝ} (hF : ∀ s, |F s|≤D) :
    |reservoirInsertion M C H N L u a F|≤D := by
  apply abs_integral_le_bound
  intro z
  exact sameInsertionAverage_bound _ _ _ _ _ _ (gridExponents_pos L) a F hF z


end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_NormalizationSymmetry
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma measurable_normalizedFactor (p : ℕ) : Measurable (normalizedFactor (p := p)) := by
  unfold normalizedFactor
  fun_prop

lemma centeredInteraction_factorization {p : ℕ} (M : Model p) (hM : Admissible M) :
    centeredInteraction =ᵐ[M.disorder.toMeasure] (fun z => normalizedFactor (z.2.2.1,z.2.2.2)) := by
  filter_upwards [hM.factorization] with z hz
  funext s
  have hp (s : Fin p → Spin) : 0<1+z.2.2.1*∏ l,z.2.2.2 l (s l) := by
    have hh := (abs_lt.mp (hz.2 s).2).1
    linarith
  have he (s : Fin p → Spin) : z.1 s = Real.log z.2.1 + Real.log (1+z.2.2.1*∏ l,z.2.2.2 l (s l)) := by
    rw [← Real.log_mul hz.1.ne' (hp s).ne',← (hz.2 s).1,Real.log_exp]
  simp only [centeredInteraction,normalizedFactor,he]
  ring

lemma normalizedFactor_permutation {p : ℕ} (e : Equiv.Perm (Fin p))
    (b : ℝ) (f : Fin p → Spin → ℝ) :
    normalizedFactor (b,fun l => f (e.symm l)) =
      (fun s => normalizedFactor (b,f) (fun l => s (e l))) := by
  funext s
  unfold normalizedFactor
  have h1 : (∏ l, f (e.symm l) (s l)) = ∏ l, f l (s (e l)) := by
    simpa only [Equiv.symm_apply_apply] using (Equiv.prod_comp e (fun l => f (e.symm l) (s l))).symm
  have h2 : (∏ l, f (e.symm l) true) = ∏ l, f l true := Equiv.prod_comp e.symm (fun l => f l true)
  rw [h1,h2]

/-- Exact symmetry of the centered physical interaction, derived from the
 original factorization, iid coordinates and independent b. The multiplier a
 need not be independent of anything, nor need log a be integrable. -/
theorem centeredInteraction_permutation {p : ℕ} (M : Model p) (hM : Admissible M)
    (e : Equiv.Perm (Fin p)) :
    IdentDistrib (centeredInteraction (p := p))
      (fun z s => centeredInteraction z (fun l => s (e l)))
      M.disorder.toMeasure M.disorder.toMeasure := by
  have hf := IdentDistrib.pi (fun l => hM.identically_distributed_f l (e.symm l))
    hM.independent_f (hM.independent_f.precomp e.symm.injective)
  have hb : IdentDistrib (fun z : InteractionSample p => z.2.2.1)
      (fun z : InteractionSample p => z.2.2.1) M.disorder.toMeasure M.disorder.toMeasure :=
    IdentDistrib.refl (by fun_prop)
  have hj := hb.prodMk hf hM.independent_b
    (hM.independent_b.comp measurable_id (show Measurable (fun f : Fin p → Spin → ℝ => fun l => f (e.symm l)) by fun_prop))
  have hn := hj.comp (measurable_normalizedFactor p)
  simp only [Function.comp_def] at hn
  simp_rw [normalizedFactor_permutation e] at hn
  have hc := IdentDistrib.of_ae_eq (measurable_centeredInteraction p).aemeasurable
    (centeredInteraction_factorization M hM)
  have hp := hc.comp (show Measurable (fun θ : Interaction p => fun s : Fin p → Spin => θ (fun l => s (e l))) by fun_prop)
  exact hc.trans (hn.trans hp.symm)

lemma centeredInteraction_norm_le {p : ℕ} (z : InteractionSample p) : ‖centeredInteraction z‖≤2*‖z.1‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro s
  exact (norm_sub_le _ _).trans ((add_le_add (norm_le_pi_norm z.1 s)
    (norm_le_pi_norm z.1 (fun _ => true))).trans_eq (by ring))

lemma centeredInteraction_integrable {p : ℕ} (M : Model p)
    (h : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) :
    Integrable (fun z => ‖centeredInteraction z‖) M.disorder.toMeasure := by
  apply (h.const_mul 2).mono' ((measurable_centeredInteraction p).norm.aestronglyMeasurable)
  exact ae_of_all _ (fun z => by simpa only [norm_norm] using centeredInteraction_norm_le z)
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_NormalizedCutoff
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

lemma clipReal_abs_le {K : ℝ} (hK : 0≤K) (x : ℝ) : |clipReal K x|≤|x| := by
  refine abs_le.mpr ⟨?_,?_⟩
  · apply le_max_of_le_right
    exact le_min (by linarith [abs_nonneg x]) (neg_abs_le x)
  · exact max_le (by linarith [abs_nonneg x]) ((min_le_right K x).trans (le_abs_self x))

lemma clipSample_norm_le {p : ℕ} {K : ℝ} (hK : 0≤K) (z : InteractionSample p) :
    ‖(clipSample K z).1‖≤‖z.1‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro s
  exact (clipReal_abs_le hK (z.1 s)).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z.1 s)

lemma clipSample_difference_bound {p : ℕ} {K : ℝ} (hK : 0≤K) (z : InteractionSample p) :
    ‖z.1-(clipSample K z).1‖≤2*‖z.1‖ := by
  have h1 := norm_sub_le z.1 (clipSample K z).1
  have h2 := clipSample_norm_le hK z
  linarith

lemma clipSample_eventually_eq {p : ℕ} (z : InteractionSample p) :
    ∀ᶠ K : ℕ in atTop,clipSample (K:ℝ) z=z := by
  obtain ⟨k,hk⟩ := exists_nat_ge ‖z.1‖
  filter_upwards [eventually_ge_atTop k] with K hK
  apply clipSample_eq
  intro s
  exact (show |z.1 s|≤‖z.1‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z.1 s).trans
    (hk.trans (by exact_mod_cast hK))

lemma clipReal_eventually_eq (x : ℝ) : ∀ᶠ K : ℕ in atTop,clipReal (K:ℝ) x=x := by
  obtain ⟨k,hk⟩ := exists_nat_ge |x|
  filter_upwards [eventually_ge_atTop k] with K hK
  exact clipReal_eq (hk.trans (by exact_mod_cast hK))

lemma clipping_interaction_error_tendsto {p : ℕ} (M : Model p)
    (hi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) :
    Tendsto (fun K : ℕ => ∫ z : InteractionSample p,‖z.1-(clipSample (K:ℝ) z).1‖ ∂M.disorder.toMeasure)
      atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (F := fun K (z : InteractionSample p) => ‖z.1-(clipSample (K:ℝ) z).1‖) (f := fun _ => 0) (fun z : InteractionSample p => 2*‖z.1‖)
    (fun K : ℕ => (measurable_fst.sub (measurable_fst.comp (measurable_clipSample (K:ℝ)))).norm.aestronglyMeasurable)
    (hi.const_mul 2)
    (fun K => ae_of_all _ (fun z => by simpa only [norm_norm] using clipSample_difference_bound (by positivity : 0≤(K:ℝ)) z))
    (ae_of_all _ (fun z => tendsto_const_nhds.congr' ((clipSample_eventually_eq z).mono (fun K hK => by dsimp only; rw [hK,sub_self,norm_zero]))))
  simpa only [integral_zero] using hh

lemma clipping_field_error_tendsto {p : ℕ} (M : Model p)
    (hi : Integrable (fun x : ℝ => |x|) M.field.toMeasure) :
    Tendsto (fun K : ℕ => ∫ x : ℝ,|x-clipReal (K:ℝ) x| ∂M.field.toMeasure) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (F := fun K (x : ℝ) => |x-clipReal (K:ℝ) x|) (f := fun _ => 0) (fun x : ℝ => 2*|x|)
    (fun K : ℕ => (measurable_id.sub (measurable_clipReal (K:ℝ))).abs.aestronglyMeasurable)
    (hi.const_mul 2)
    (fun K => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      have h1 := abs_sub x (clipReal (K:ℝ) x)
      have h2 := clipReal_abs_le (by positivity : 0≤(K:ℝ)) x
      linarith))
    (ae_of_all _ (fun x => tendsto_const_nhds.congr' ((clipReal_eventually_eq x).mono (fun K hK => by dsimp only; rw [hK,sub_self,abs_zero]))))
  simpa only [integral_zero] using hh

lemma centeredModel_symmetric {p : ℕ} (M : Model p) (hM : Admissible M) (e : Equiv.Perm (Fin p)) :
    IdentDistrib (fun z : InteractionSample p => z.1)
      (fun z : InteractionSample p => fun (s : Fin p → Spin) => z.1 (fun l => s (e l)))
      (centeredModel M).disorder.toMeasure (centeredModel M).disorder.toMeasure := by
  have hh := centeredInteraction_permutation M hM e
  constructor
  · exact measurable_fst.aemeasurable
  · exact (show Measurable (fun z : InteractionSample p => fun (s : Fin p → Spin) => z.1 (fun l => s (e l))) by fun_prop).aemeasurable
  · change Measure.map _ (Measure.map centerSample M.disorder.toMeasure)=Measure.map _ (Measure.map centerSample M.disorder.toMeasure)
    rw [Measure.map_map measurable_fst (measurable_centerSample p),
      Measure.map_map (show Measurable (fun z : InteractionSample p => fun (s : Fin p → Spin) => z.1 (fun l => s (e l))) by fun_prop) (measurable_centerSample p)]
    exact hh.map_eq

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory

lemma interaction_clip_symmetric {p : ℕ} (M : Model p) (C : ℝ)
    (hsym : ∀ e : Equiv.Perm (Fin p),IdentDistrib (fun z : InteractionSample p => z.1)
      (fun z : InteractionSample p => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    (e : Equiv.Perm (Fin p)) :
    IdentDistrib (fun z : InteractionSample p => (clipSample C z).1)
      (fun z : InteractionSample p => fun s => (clipSample C z).1 (fun i => s (e i)))
      M.disorder.toMeasure M.disorder.toMeasure := by
  exact (hsym e).comp (show Measurable (fun f : (Fin p → Spin) → ℝ => fun s => clipReal C (f s)) from
    Measurable.of_eval (fun spin => (measurable_clipReal C).comp (measurable_pi_apply spin)))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityRateLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter
open scoped Topology NNReal BigOperators

lemma oneNewRate_tendsto (α : ℝ≥0) (q : ℕ) :
    Tendsto (fun N => (oneNewRate α q N:ℝ)) atTop (𝓝 ((α:ℝ)*(q+1))) := by
  have hh := ((tendsto_natCast_div_add_atTop (1:ℝ)).pow q).const_mul ((α:ℝ)*(q+1))
  simpa only [oneNewRate,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,
    NNReal.coe_pow,NNReal.coe_div,one_pow,mul_one] using hh

lemma reservoir_deficit_identity (α : ℝ≥0) (q N : ℕ) :
    (α:ℝ)*N-(reservoirRate α q N:ℝ) =
      (α:ℝ)*((N:ℝ)/(N+1))*(∑ i∈Finset.range q,((N:ℝ)/(N+1))^i) := by
  have hh := geom_sum_mul ((N:ℝ)/(N+1)) q
  have hd : (N:ℝ)+1 ≠ 0 := by positivity
  change (α:ℝ)*N-(α:ℝ)*N*((N:ℝ)/(N+1))^q = _
  have hx : ((N:ℝ)/(N+1)-1) = -1/(N+1) := by field_simp; ring
  rw [hx] at hh
  have he : 1-((N:ℝ)/(N+1))^q = (∑ i∈Finset.range q,((N:ℝ)/(N+1))^i)/(N+1) := by
    simp only [div_eq_mul_inv,neg_mul,one_mul,mul_neg] at hh ⊢
    linarith
  rw [show (α:ℝ)*N-(α:ℝ)*N*((N:ℝ)/(N+1))^q = (α:ℝ)*N*(1-((N:ℝ)/(N+1))^q) by ring,he]
  ring

lemma reservoir_deficit_tendsto (α : ℝ≥0) (q : ℕ) :
    Tendsto (fun N => (α:ℝ)*N-(reservoirRate α q N:ℝ)) atTop (𝓝 ((α:ℝ)*q)) := by
  simp_rw [reservoir_deficit_identity]
  have hh := ((tendsto_natCast_div_add_atTop (1:ℝ)).const_mul (α:ℝ)).mul
    (tendsto_finsetSum (Finset.range q) (fun i _ => (tendsto_natCast_div_add_atTop (1:ℝ)).pow i))
  simpa only [one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,mul_one] using hh

lemma cavityBadRate_tendsto (α : ℝ≥0) (q : ℕ) :
    Tendsto (cavityBadRate α q) atTop (𝓝 0) := by
  have hh := ((tendsto_const_nhds (x := (α:ℝ))).add (reservoir_deficit_tendsto α q)).sub (oneNewRate_tendsto α q)
  have he : (α:ℝ)+(α:ℝ)*q-(α:ℝ)*(q+1)=0 := by ring
  rw [he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext N
  dsimp [cavityBadRate]
  ring

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ClippedModelFacts
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal

lemma clippedModel_interaction_bounded {p : ℕ} (M : Model p) {K : ℝ} (hK : 0 ≤ K) :
    ∀ᵐ z ∂(clippedModel M K).disorder.toMeasure, ‖z.1‖ ≤ K := by
  change ∀ᵐ z ∂Measure.map (clipSample K) M.disorder.toMeasure, ‖z.1‖ ≤ K
  apply (ae_map_iff (measurable_clipSample K).aemeasurable (measurableSet_le measurable_fst.norm measurable_const)).mpr
  exact ae_of_all _ (fun z => (pi_norm_le_iff_of_nonneg hK).mpr (fun s => by
    simpa only [Real.norm_eq_abs,clipSample] using clipReal_bound hK (z.1 s)))

lemma clippedModel_field_bounded {p : ℕ} (M : Model p) {K : ℝ} (hK : 0 ≤ K) :
    ∀ᵐ h ∂(clippedModel M K).field.toMeasure, |h| ≤ K := by
  change ∀ᵐ h ∂Measure.map (clipReal K) M.field.toMeasure, |h| ≤ K
  apply (ae_map_iff (measurable_clipReal K).aemeasurable (measurableSet_le measurable_id.abs measurable_const)).mpr
  exact ae_of_all _ (clipReal_bound hK)

lemma clippedModel_interaction_integrable {p : ℕ} (M : Model p) {K : ℝ} (hK : 0 ≤ K) :
    Integrable (fun z : InteractionSample p => ‖z.1‖) (clippedModel M K).disorder.toMeasure := by
  exact (integrable_const K).mono' (by fun_prop) ((clippedModel_interaction_bounded M hK).mono (fun z hz => by simpa only [norm_norm] using hz))

lemma clippedModel_field_integrable {p : ℕ} (M : Model p) {K : ℝ} (hK : 0 ≤ K) :
    Integrable (fun h : ℝ => |h|) (clippedModel M K).field.toMeasure := by
  exact (integrable_const K).mono' (by fun_prop) ((clippedModel_field_bounded M hK).mono (fun z hz => by simpa only [Real.norm_eq_abs,abs_abs] using hz))

lemma clippedModel_symmetric {p : ℕ} (M : Model p) (K : ℝ)
    (hsym : ∀ e : Equiv.Perm (Fin p),IdentDistrib (fun z : InteractionSample p => z.1)
      (fun z : InteractionSample p => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    (e : Equiv.Perm (Fin p)) :
    IdentDistrib (fun z : InteractionSample p => z.1)
      (fun z : InteractionSample p => fun s => z.1 (fun i => s (e i)))
      (clippedModel M K).disorder.toMeasure (clippedModel M K).disorder.toMeasure := by
  constructor
  · exact measurable_fst.aemeasurable
  · exact (show Measurable (fun z : InteractionSample p => fun (s : Fin p → Spin) => z.1 (fun l => s (e l))) by fun_prop).aemeasurable
  · change Measure.map _ (Measure.map (clipSample K) M.disorder.toMeasure)=Measure.map _ (Measure.map (clipSample K) M.disorder.toMeasure)
    rw [Measure.map_map measurable_fst (measurable_clipSample K),
      Measure.map_map (show Measurable (fun z : InteractionSample p => fun (s : Fin p → Spin) => z.1 (fun l => s (e l))) by fun_prop) (measurable_clipSample K)]
    exact (interaction_clip_symmetric M K hsym e).map_eq

lemma clip_interaction_difference_integrable {p : ℕ} (M : Model p) {K : ℝ} (hK : 0 ≤ K)
    (hi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) :
    Integrable (fun z => ‖(clipSample K z).1-z.1‖) M.disorder.toMeasure := by
  apply (hi.const_mul 2).mono' ((measurable_fst.comp (measurable_clipSample K)).sub measurable_fst).norm.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    simp only [norm_norm]
    change ‖(clipSample K z).1-z.1‖ ≤ 2*‖z.1‖
    rw [norm_sub_rev]
    exact clipSample_difference_bound hK z)

lemma clip_field_difference_integrable {p : ℕ} (M : Model p) {K : ℝ} (hK : 0 ≤ K)
    (hi : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    Integrable (fun h => |clipReal K h-h|) M.field.toMeasure := by
  apply (hi.const_mul 2).mono' ((measurable_clipReal K).sub measurable_id).abs.aestronglyMeasurable
  exact ae_of_all _ (fun h => by
    simp only [Real.norm_eq_abs,abs_abs]
    change |clipReal K h-h| ≤ 2*|h|
    have h1 := abs_sub (clipReal K h) h
    have h2 := clipReal_abs_le hK h
    linarith)
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityInsertionAlgebra
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
open _root_.MeasureTheory
namespace FiniteLaw

lemma spinLog_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : (ι → Spin) → ℝ) (x : ι → ℝ) :
    spinLog F x=Real.log (∑ s : ι → Spin,(∏ i,q (x i) (s i))*Real.exp (F s)) := by
  unfold spinLog
  rw [Subsingleton.elim (finiteMapDecEq ι) (inferInstance : DecidableEq ι)]

lemma spinLog_edge {p : ℕ} (θ : Interaction p) :
    spinLog θ = fun x => Real.log (edge θ x) := by
  funext x
  rw [spinLog_eq]
  apply congrArg Real.log
  unfold edge
  apply Finset.sum_congr rfl
  intro s _
  exact mul_comm _ _

lemma spinPartition_blocks {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (F : ι → (κ → Spin) → ℝ) (x : ι × κ → ℝ) :
    (∑ s : ι × κ → Spin, (∏ i, q (x i) (s i))*Real.exp (∑ j,F j (fun l => s (j,l)))) =
      ∏ j : ι, ∑ s : κ → Spin,(∏ l,q (x (j,l)) (s l))*Real.exp (F j s) := by
  classical
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (Equiv.curry ι κ Spin)
  intro s
  simp only [Equiv.curry_apply,Function.curry,Real.exp_sum,Fintype.prod_prod_type,← Finset.prod_mul_distrib]
  rfl

lemma spinLog_blocks {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (F : ι → (κ → Spin) → ℝ) (x : ι × κ → ℝ) :
    spinLog (fun s : ι × κ → Spin => ∑ j,F j (fun l => s (j,l))) x =
      ∑ j : ι,spinLog (F j) (fun l => x (j,l)) := by
  simp only [spinLog_eq]
  rw [spinPartition_blocks,Real.log_prod]
  intro j _
  apply ne_of_gt
  apply Finset.sum_pos
  · intro s _
    exact mul_pos (Finset.prod_pos (fun l _ => q_pos _ _)) (Real.exp_pos _)
  · exact Finset.univ_nonempty

end FiniteLaw

lemma cavitySiteEnergy_bound {p k : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (s : Fin k × Fin (p-1) → Spin) :
    |cavitySiteEnergy θ h s| ≤ |h|+∑ j,‖(θ j).1‖ := by
  change |Real.log ((∑ ε : Spin, Real.exp (h*spin ε+∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)))/2)| ≤ _
  have hh (ε : Spin) : |h*spin ε+∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)| ≤ |h|+∑ j,‖(θ j).1‖ := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul,abs_spin,mul_one]
    · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (θ j).1 (appendSpin (fun l => s (j,l)) ε)))
  -- This is the logarithm of the uniform two-spin exponential moment.
  have hb := (FiniteLaw.uniform : FiniteLaw Spin).logMean_stability (show (0:ℝ)<1 by norm_num)
    (g := fun _ => 0) (fun ε => by simpa only [sub_zero] using hh ε)
  simp only [FiniteLaw.logMean_const _ (one_ne_zero), sub_zero] at hb
  simpa only [FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one,FiniteLaw.expect,
    FiniteLaw.uniform,Fintype.card_bool,← Finset.mul_sum,inv_mul_eq_div,Nat.cast_ofNat,← Finset.sum_div] using hb

lemma spinLog_cavitySiteEnergy {p k : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (x : Fin k × Fin (p-1) → ℝ) :
    FiniteLaw.spinLog (cavitySiteEnergy θ h) x = siteLog θ h x := by
  classical
  have hp (s : Fin k × Fin (p-1) → Spin) :
      0 < (∑ ε : Spin,Real.exp (h*spin ε+∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)))/2 :=
    div_pos (Finset.sum_pos (fun ε _ => Real.exp_pos _) Finset.univ_nonempty) (by norm_num)
  rw [FiniteLaw.spinLog_eq]
  unfold cavitySiteEnergy
  simp only [Real.exp_log (hp _)]
  unfold siteLog
  apply congrArg Real.log
  simp only [← mul_div_assoc,← Finset.sum_div,Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro ε _
  simp_rw [Real.exp_add]
  rw [show (∑ s : Fin k × Fin (p-1) → Spin, (∏ i,q (x i) (s i))*
      (Real.exp (h*spin ε)*Real.exp (∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)))) =
      Real.exp (h*spin ε)*(∑ s : Fin k × Fin (p-1) → Spin,(∏ i,q (x i) (s i))*
        Real.exp (∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε))) by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring]
  congr 1
  rw [FiniteLaw.spinPartition_blocks (fun j (s : Fin (p-1) → Spin) => (θ j).1 (appendSpin s ε)) x,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  unfold message
  rw [Real.exp_log]
  · apply Finset.sum_congr rfl; intro s _; exact mul_comm _ _
  · exact Finset.sum_pos (fun s _ => mul_pos (Real.exp_pos _) (Finset.prod_pos (fun l _ => q_pos _ _))) Finset.univ_nonempty

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_AveragedEnergyRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter
open scoped BigOperators Topology

namespace UniversalDictionary
open ConcreteReservoir

lemma reservoirInsertionOn_bound {ι : Type} [Fintype ι] {p : ℕ}
    (M : Model p) (C H : ℝ) (N L : ℕ) (u : Spec L×ℕ → ℝ) (F : (ι → Spin) → ℝ)
    {D : ℝ} (hF : ∀ s,|F s|≤D) : |reservoirInsertionOn M C H N L u F|≤D :=
  reservoirInsertion_bound M C H N L u (Fintype.card ι) _ (fun _ => hF _)

end UniversalDictionary
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScoreIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter
open scoped Topology

lemma scoreScale_succ_sub_sharp {N : ℕ} (hN : 0 < N) :
    scoreScale (N+1)-scoreScale N ≤ scoreScale N/N := by
  have hx : (0:ℝ)<N := by exact_mod_cast hN
  have hy : (0:ℝ) ≤ 1+1/(N:ℝ) := by positivity
  have hxy : (N:ℝ)+1=(N:ℝ)*(1+1/(N:ℝ)) := by field_simp
  have h := mul_le_mul_of_nonneg_left
    (Real.rpow_le_self_of_one_le (show (1:ℝ)≤1+1/(N:ℝ) from le_add_of_nonneg_right (by positivity))
      (show (3:ℝ)/4≤1 by norm_num)) (Real.rpow_nonneg hx.le ((3:ℝ)/4))
  unfold scoreScale
  rw [Nat.cast_add,Nat.cast_one,hxy,Real.mul_rpow hx.le hy]
  calc
    _ ≤ (N:ℝ)^((3:ℝ)/4)*(1+1/(N:ℝ))-(N:ℝ)^((3:ℝ)/4) := sub_le_sub_right h _
    _ = _ := by ring

lemma scoreScale_succ_difference_tendsto :
    Tendsto (fun N => scoreScale (N+1)-scoreScale N) atTop (𝓝 0) := by
  have he := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp he
  apply squeeze_zero' (eventually_atTop.2 ⟨1,fun N _ => sub_nonneg.mpr (scoreScale_mono (Nat.le_succ N))⟩)
    (eventually_atTop.2 ⟨1,fun N hN => ?_⟩) ht
  change scoreScale (N+1)-scoreScale N ≤ (N:ℝ)^(-(1/4:ℝ))
  rw [← neg_div]
  rw [← SizeCoupling.scoreScale_div (show 0 < N by omega)]
  exact scoreScale_succ_sub_sharp (by omega)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityErrorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter
open scoped Topology

lemma scoreScale_div_succ_tendsto :
    Tendsto (fun N => scoreScale N/(N+1)) atTop (𝓝 0) := by
  have he := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp he
  apply squeeze_zero' (Eventually.of_forall (fun N => by unfold scoreScale; positivity))
    (eventually_atTop.2 ⟨1,fun N hN => ?_⟩) ht
  change scoreScale N/(N+1) ≤ (N:ℝ)^(-(1/4:ℝ))
  rw [← neg_div,← SizeCoupling.scoreScale_div (show 0 < N by omega)]
  apply div_le_div_of_nonneg_left
  · unfold scoreScale; positivity
  · exact_mod_cast (show 0 < N by omega)
  · linarith

namespace UniversalDictionary
lemma gridExponents_exponents (L : ℕ) :
    Exponents (fun i : Fin L => gridExponents L i.castSucc) := by
  constructor
  · intro i j hij
    simp only [gridExponents,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<L+1)).mpr
    exact_mod_cast (show i.val+1<j.val+1 by exact Nat.add_lt_add_right hij 1)
  · intro i
    refine ⟨gridExponents_pos L i.castSucc,?_⟩
    simp only [gridExponents,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    apply (div_lt_one (by positivity : (0:ℝ)<L+1)).mpr
    exact_mod_cast (show i.val+1<L+1 by omega)
end UniversalDictionary
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityTrialIdentity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

lemma cavityBondEnergy_bound {p k : ℕ} (θ : Fin k → InteractionSample p)
    (s : Fin k × Fin p → Spin) : |cavityBondEnergy θ s|≤∑ j,‖(θ j).1‖ :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (θ j).1 (fun i => s (j,i))))

lemma continuous_cavityBondEnergy {p k : ℕ} :
    Continuous (cavityBondEnergy : (Fin k → InteractionSample p) → (Fin k × Fin p → Spin) → ℝ) := by
  apply continuous_pi
  intro s
  exact continuous_finsetSum _ (fun j _ =>
    (continuous_apply (fun i => s (j,i))).comp (continuous_fst.comp (continuous_apply j)))

lemma continuous_cavitySiteEnergy {p k : ℕ} :
    Continuous (fun z : (Fin k → InteractionSample p) × ℝ => cavitySiteEnergy z.1 z.2) := by
  apply continuous_pi
  intro s
  apply Continuous.log
  · apply Continuous.div_const
    apply continuous_finsetSum
    intro ε _
    apply Real.continuous_exp.comp
    exact (continuous_snd.mul_const (spin ε)).add (continuous_finsetSum _ (fun j _ =>
      (continuous_apply (appendSpin (fun l => s (j,l)) ε)).comp
        (continuous_fst.comp ((continuous_apply j).comp continuous_fst))))
  · intro z
    exact ne_of_gt (div_pos (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty) (by norm_num))

lemma trialLog_cavityBondEnergy {p k r : ℕ} (ζ : Hierarchy (r+1))
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (θ : Fin k → InteractionSample p) :
    trialLog r ζ m (FiniteLaw.spinLog (cavityBondEnergy θ)) =
      ∑ j,trialLog r ζ m (fun x => Real.log (edge (θ j).1 x)) := by
  have he : FiniteLaw.spinLog (cavityBondEnergy θ) =
      fun x : Fin k × Fin p → ℝ => ∑ j,Real.log (edge (θ j).1 (fun i => x (j,i))) := by
    funext x
    change FiniteLaw.spinLog (fun s : Fin k × Fin p → Spin => ∑ j,(θ j).1 (fun i => s (j,i))) x = _
    rw [FiniteLaw.spinLog_blocks]
    simp only [FiniteLaw.spinLog_edge]
  rw [he]
  exact trialLog_blocks r k _ (fun j => continuous_log_edge (θ j).1)
    (fun j => ‖(θ j).1‖) (fun j => log_edge_bound (θ j).1) m hm ζ

lemma integral_trial_cavityBondEnergy {p k r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : ∀ i,0 < m i) :
    (∫ θ : Fin k → InteractionSample p,trialLog r ζ m (FiniteLaw.spinLog (cavityBondEnergy θ))
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) =
      k*(∫ θ : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge θ.1 x)) ∂M.disorder.toMeasure) := by
  have hi : Integrable (fun θ : InteractionSample p => trialLog r ζ m (fun x => Real.log (edge θ.1 x))) M.disorder.toMeasure := by
    apply hθ.mono' (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
    exact ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs,Function.comp_apply] using trial_edge_bound r m hm ζ θ.1)
  simp_rw [trialLog_cavityBondEnergy ζ m hm]
  rw [integral_finsetSum _ (fun j _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hi)]
  simp only [integral_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hi.aestronglyMeasurable,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

lemma integral_trial_cavitySiteEnergy {p k r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : ∀ i,0 < m i) :
    (∫ z : (Fin k → InteractionSample p) × ℝ,
      trialLog r ζ m (FiniteLaw.spinLog (cavitySiteEnergy z.1 z.2))
      ∂(Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure) =
      trialSiteDisorder M m ζ k := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  simp_rw [show ∀ θ h, FiniteLaw.spinLog (cavitySiteEnergy (p := p) (k := k) θ h)=siteLog θ h from
    fun θ h => funext (spinLog_cavitySiteEnergy θ h)]
  apply integral_prod
  apply ((hh.comp_snd _).add ((interaction_sum_integrable M hθ k).comp_fst _)).mono'
    (trial_site_lipschitz r m hm ζ).continuous.aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply,Function.comp_apply] using trial_site_bound r m hm ζ z.1 z.2)

lemma functional_cavity_trial {p r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : ∀ i,0 < m i) :
    functional M r ζ m = Real.log 2+
      (∫ k, ∫ z : (Fin k → InteractionSample p) × ℝ,
        trialLog r ζ m (FiniteLaw.spinLog (cavitySiteEnergy z.1 z.2))
        ∂(Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure
        ∂poissonMeasure (M.alpha*p))-
      (∫ k, ∫ θ : Fin k → InteractionSample p,
        trialLog r ζ m (FiniteLaw.spinLog (cavityBondEnergy θ))
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)
        ∂poissonMeasure (M.alpha*(p-1:ℕ))) := by
  simp_rw [integral_trial_cavitySiteEnergy M hθ hh ζ m hm,
    integral_trial_cavityBondEnergy M hθ ζ m hm,integral_mul_const,poisson_mean]
  unfold functional trialSiteDisorder trialSiteField
  simp only [NNReal.coe_mul,NNReal.coe_natCast]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators

lemma abs_integral_le_bound_ae {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} {B : ℝ}
    (h : ∀ᵐ x ∂μ, |f x|≤B) : |∫ x,f x ∂μ|≤B := by
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
      (h.mono (fun x hx => by simpa only [Real.norm_eq_abs] using hx))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionPoissonAlgebra
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

lemma poisson_average_bound (ρ : ℝ≥0) (f : ℕ → ℝ) {B D : ℝ}
    (h : ∀ k,|f k|≤B+D*k) : |∫ k,f k ∂poissonMeasure ρ|≤B+D*ρ := by
  have hg : Integrable (fun k : ℕ => B+D*k) (poissonMeasure ρ) :=
    (integrable_const _).add ((poisson_integrable_count ρ).const_mul D)
  have hh := norm_integral_le_of_norm_le (f := f) hg (ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs] using h k))
  simpa only [Real.norm_eq_abs,integral_add (integrable_const _) ((poisson_integrable_count ρ).const_mul D),
    integral_const,probReal_univ,smul_eq_mul,one_mul,integral_const_mul,poisson_mean] using hh

lemma poisson_average_integrable (ρ : ℝ≥0) (f : ℕ → ℝ) {B D : ℝ}
    (h : ∀ k,|f k|≤B+D*k) : Integrable f (poissonMeasure ρ) := by
  apply ((integrable_const B).add ((poisson_integrable_count ρ).const_mul D)).mono'
    (measurable_of_countable f).aestronglyMeasurable
  exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs,Pi.add_apply] using h k)

lemma double_limit_two (a f g : ℕ → ℕ → ℝ) {B C : ℝ}
    (ha : ∀ L n,0≤a L n) (hf0 : ∀ L n,0≤f L n) (hg0 : ∀ L n,0≤g L n)
    (hf : ∀ L n,f L n≤B) (hg : ∀ L n,g L n≤C)
    (h : ∀ L n,a L n≤f L n+g L n)
    (hflim : Tendsto (fun L => limsup (f L) atTop) atTop (𝓝 0))
    (hglim : Tendsto (fun L => limsup (g L) atTop) atTop (𝓝 0)) :
    Tendsto (fun L => limsup (a L) atTop) atTop (𝓝 0) := by
  have hfB L : IsBoundedUnder (·≤·) atTop (f L) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (hf L))
  have hgB L : IsBoundedUnder (·≤·) atTop (g L) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (hg L))
  have haB L : IsBoundedUnder (·≤·) atTop (a L) :=
    isBoundedUnder_of_eventually_le (a := B+C) (Eventually.of_forall (fun n => (h L n).trans (add_le_add (hf L n) (hg L n))))
  apply squeeze_zero (fun L => le_limsup_of_frequently_le ((Eventually.of_forall (ha L)).frequently) (haB L))
    (fun L => ?_) (by simpa using hflim.add hglim)
  have hfLower := isBoundedUnder_of_eventually_ge (f := atTop) (Eventually.of_forall (hf0 L))
  have hgLower := isBoundedUnder_of_eventually_ge (f := atTop) (Eventually.of_forall (hg0 L))
  refine (limsup_le_limsup (Eventually.of_forall (h L))
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall (ha L))).isCoboundedUnder_le
    (isBoundedUnder_of_eventually_le (a := B+C)
      (Eventually.of_forall (fun index => add_le_add (hf L index) (hg L index))))).trans ?_
  exact limsup_add_le hfLower (hfB L) hgLower.isCoboundedUnder_le (hgB L)

namespace UniversalDictionary
open ConcreteReservoir

lemma insertionPoisson_comparison_bound
    {ι X : ℕ → Type} [∀ k,Fintype (ι k)] [∀ k,MeasurableSpace (X k)]
    {p : ℕ} (M : Model p) (C H : ℝ) (N L : ℕ) (u : Spec L×ℕ → ℝ)
    (μ : (k : ℕ) → Measure (X k)) [∀ k,IsProbabilityMeasure (μ k)]
    (F : (k : ℕ) → X k → (ι k → Spin) → ℝ) {B D : ℝ}
    (hF : ∀ k,∀ᵐ x ∂μ k,∀ s,|F k x s|≤B+D*k) (ρ : ℝ≥0) :
    |insertionPoisson M C H N L u μ F ρ-
      trialPoisson L (reservoirTrialLaw M C H N L u) μ F ρ| ≤
      ∫ k,|(∫ x,reservoirInsertionOn M C H N L u (F k x) ∂μ k)-
        (∫ x,trialLog L (reservoirTrialLaw M C H N L u)
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F k x)) ∂μ k)| ∂poissonMeasure ρ := by
  have h1 k := abs_integral_le_bound_ae (μ k) ((hF k).mono (fun x hx =>
    reservoirInsertionOn_bound M C H N L u (F k x) hx))
  have h2 k := abs_integral_le_bound_ae (μ k) ((hF k).mono (fun x hx =>
    (trialLog_continuous_bound L (FiniteLaw.spinLog (F k x)) (FiniteLaw.spinLog_continuous (F k x))
      (FiniteLaw.spinLog_bound (F k x) hx) _ (fun i => gridExponents_pos L i.castSucc)).2
        (reservoirTrialLaw M C H N L u)))
  unfold insertionPoisson trialPoisson
  rw [← integral_sub (poisson_average_integrable ρ _ h1) (poisson_average_integrable ρ _ h2)]
  exact abs_integral_le_integral_abs

end UniversalDictionary
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityProxy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators

namespace UniversalDictionary
open ConcreteReservoir

lemma cavitySiteEnergy_ae_bound {p k : ℕ} (M : Model p) {C H : ℝ}
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure,|h|≤H) :
    ∀ᵐ z ∂(Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure,
      ∀ s,|cavitySiteEnergy z.1 z.2 s|≤H+C*k := by
  have ht : ∀ᵐ θ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure),∀ j,‖(θ j).1‖≤C :=
    Filter.eventually_all.mpr (fun j => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => M.disorder.toMeasure) (i := j)).eventually hθ)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ht,Measure.quasiMeasurePreserving_snd.ae hh] with z hz hh
  intro s
  apply (cavitySiteEnergy_bound z.1 z.2 s).trans
  have hs := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin k))) => hz j)
  simpa [mul_comm] using add_le_add hh hs

lemma cavityBondEnergy_ae_bound {p k : ℕ} (M : Model p) {C : ℝ}
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C) :
    ∀ᵐ θ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure),
      ∀ s,|cavityBondEnergy θ s|≤0+C*k := by
  have ht : ∀ᵐ θ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure),∀ j,‖(θ j).1‖≤C :=
    Filter.eventually_all.mpr (fun j => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => M.disorder.toMeasure) (i := j)).eventually hθ)
  filter_upwards [ht] with θ hθ
  intro s
  apply (cavityBondEnergy_bound θ s).trans
  simpa [mul_comm] using Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin k))) => hθ j)

lemma cavityProxy_comparison_tendsto {p : ℕ} (M : Model p) (hα : 0<M.alpha)
    {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure,|h|≤H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L,Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L,FullShapeControl M C H L (Ns L) (us L)) :
    Tendsto (fun L => limsup (fun n =>
      |cavityProxy M C H (Ns L n+1) L (us L n)-
        functional M L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc)|) atTop) atTop (𝓝 0) := by
  let μs := fun k => (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure
  let μb := fun k => Measure.pi (fun _ : Fin k => M.disorder.toMeasure)
  let Fs := fun (k : ℕ) (z : (Fin k → InteractionSample p)×ℝ) => cavitySiteEnergy z.1 z.2
  let Fb := fun (k : ℕ) (θ : Fin k → InteractionSample p) => cavityBondEnergy θ
  let es := fun L n => ∫ k,|(∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (Fs k x) ∂μs k)-
    (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
      (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (Fs k x)) ∂μs k)| ∂poissonMeasure (M.alpha*p)
  let eb := fun L n => ∫ k,|(∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (Fb k x) ∂μb k)-
    (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
      (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (Fb k x)) ∂μb k)| ∂poissonMeasure (M.alpha*(p-1:ℕ))
  let (k : ℕ) : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  have hFs k : Measurable (Fs k) := continuous_cavitySiteEnergy.measurable
  have hFb k : Measurable (Fb k) := continuous_cavityBondEnergy.measurable
  have hsb k := cavitySiteEnergy_ae_bound (k := k) M hθ hh
  have hbb k := cavityBondEnergy_ae_bound (k := k) M hθ
  have hs := poissonInsertionOn_comparison_tendsto_ae M hα C H Ns hNs us hcontrol μs Fs hFs hH hC hsb (M.alpha*p)
  have hb := poissonInsertionOn_comparison_tendsto_ae M hα C H Ns hNs us hcontrol μb Fb hFb (le_refl 0) hC hbb (M.alpha*(p-1:ℕ))
  have hsbound L n : es L n≤2*H+2*C*(M.alpha*p) := by
    apply (le_abs_self _).trans
    apply poisson_average_bound
    intro k
    rw [abs_abs]
    have h1 := abs_integral_le_bound_ae (μs k) ((hsb k).mono (fun x hx => reservoirInsertionOn_bound M C H (Ns L n+1) L (us L n) (Fs k x) hx))
    have h2 := abs_integral_le_bound_ae (μs k) ((hsb k).mono (fun x hx => (trialLog_continuous_bound L _ (FiniteLaw.spinLog_continuous (Fs k x)) (FiniteLaw.spinLog_bound (Fs k x) hx) _ (fun i => gridExponents_pos L i.castSucc)).2 (reservoirTrialLaw M C H (Ns L n+1) L (us L n))))
    exact (abs_sub _ _).trans (by linarith)
  have hbbound L n : eb L n≤0+2*C*(M.alpha*(p-1:ℕ)) := by
    apply (le_abs_self _).trans
    apply poisson_average_bound
    intro k
    rw [abs_abs]
    have h1 := abs_integral_le_bound_ae (μb k) ((hbb k).mono (fun x hx => reservoirInsertionOn_bound M C H (Ns L n+1) L (us L n) (Fb k x) hx))
    have h2 := abs_integral_le_bound_ae (μb k) ((hbb k).mono (fun x hx => (trialLog_continuous_bound L _ (FiniteLaw.spinLog_continuous (Fb k x)) (FiniteLaw.spinLog_bound (Fb k x) hx) _ (fun i => gridExponents_pos L i.castSucc)).2 (reservoirTrialLaw M C H (Ns L n+1) L (us L n))))
    exact (abs_sub _ _).trans (by linarith)
  apply double_limit_two _ es eb (fun _ _ => abs_nonneg _) (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
    (fun _ _ => integral_nonneg (fun _ => abs_nonneg _)) hsbound hbbound ?_ hs hb
  intro L n
  rw [functional_cavity_trial M hθi hhi _ _ (fun i => gridExponents_pos L i.castSucc)]
  have hs' := insertionPoisson_comparison_bound M C H (Ns L n+1) L (us L n) μs Fs hsb (M.alpha*p)
  have hb' := insertionPoisson_comparison_bound M C H (Ns L n+1) L (us L n) μb Fb hbb (M.alpha*(p-1:ℕ))
  have hh := (abs_sub (insertionPoisson M C H (Ns L n+1) L (us L n) μs Fs (M.alpha*p)-trialPoisson L (reservoirTrialLaw M C H (Ns L n+1) L (us L n)) μs Fs (M.alpha*p))
    (insertionPoisson M C H (Ns L n+1) L (us L n) μb Fb (M.alpha*(p-1:ℕ))-trialPoisson L (reservoirTrialLaw M C H (Ns L n+1) L (us L n)) μb Fb (M.alpha*(p-1:ℕ)))).trans (add_le_add hs' hb')
  have hlin (a b c d x : ℝ) : |(x+a-b)-(x+c-d)|=|(a-c)-(b-d)| := by congr 1; ring
  simpa only [cavityProxy,trialPoisson,Fs,Fb,μs,μb,es,eb,hlin] using hh

end UniversalDictionary
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators

lemma functional_envelope {p r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : ∀ i,0 < m i) :
    |functional M r ζ m-Real.log 2|≤functionalEnvelope M := by
  have hs := poisson_average_bound (M.alpha*p) (trialSiteDisorder M m ζ)
    (B := fieldMoment M) (D := interactionMoment M)
    (fun k => (trialSiteDisorder_bound M m hm hθ hh ζ k).trans_eq (by
      simp only [fieldMoment,interactionMoment]; ring))
  have he : |∫ θ : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge θ.1 x)) ∂M.disorder.toMeasure| ≤ interactionMoment M := by
    simpa only [Real.norm_eq_abs,interactionMoment] using
      norm_integral_le_of_norm_le (f := fun θ : InteractionSample p => trialLog r ζ m (fun x => Real.log (edge θ.1 x))) hθ (ae_of_all _ (fun θ => by
        simpa only [Real.norm_eq_abs] using trial_edge_bound r m hm ζ θ.1))
  have he' := mul_le_mul_of_nonneg_left he
    (show 0≤(M.alpha:ℝ)*(p-1:ℕ) by positivity)
  rw [← abs_of_nonneg (show 0≤(M.alpha:ℝ)*(p-1:ℕ) by positivity),← abs_mul] at he'
  rw [abs_of_nonneg (show 0≤(M.alpha:ℝ)*(p-1:ℕ) by positivity)] at he'
  have hx := (abs_sub (∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p))
    ((M.alpha:ℝ)*(p-1:ℕ)*(∫ θ : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge θ.1 x)) ∂M.disorder.toMeasure))).trans (add_le_add hs he')
  have hid : functional M r ζ m-Real.log 2 =
      (∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p))-
      (M.alpha:ℝ)*(p-1:ℕ)*(∫ θ : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge θ.1 x)) ∂M.disorder.toMeasure) := by
    simp only [functional,trialSiteDisorder,trialSiteField]
    ring
  rw [hid]
  apply hx.trans_eq
  simp only [functionalEnvelope,NNReal.coe_mul,NNReal.coe_natCast]
  ring

lemma variationalValue_le_functional_integrable {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : Exponents m) :
    variationalValue M≤functional M r ζ m := by
  have hl r ζ m (hm : Exponents m) : Real.log 2-functionalEnvelope M≤functional M r ζ m := by
    have hh := (abs_le.mp (functional_envelope M hθ hh ζ m (fun i => (hm.2 i).1))).1
    linarith
  have hphi r : Real.log 2-functionalEnvelope M≤phi M r := by
    obtain ⟨m,hm⟩ := exponents_nonempty r
    apply le_csInf
    · exact ⟨functional M r (zeroHierarchy (r+1)) m,zeroHierarchy (r+1),m,hm,rfl⟩
    · rintro v ⟨ζ,m,hm,rfl⟩
      exact hl r ζ m hm
  apply (ciInf_le (show BddBelow (Set.range (phi M)) from ⟨_,by rintro v ⟨t,rfl⟩; exact hphi t⟩) r).trans
  apply csInf_le
  · exact ⟨_,by rintro v ⟨ζ,m,hm,rfl⟩; exact hl r ζ m hm⟩
  · exact ⟨ζ,m,hm,rfl⟩

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CenteredPressure
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

lemma referenceEnergy_integrable {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) :
    Integrable referenceEnergy M.disorder.toMeasure := by
  apply hθ.mono' (show Measurable (referenceEnergy (p := p)) by unfold referenceEnergy; fun_prop).aestronglyMeasurable
  exact ae_of_all _ (fun z => norm_le_pi_norm z.1 (fun _ => true))

lemma logSumExp_add_constant {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (a : ℝ) :
    Real.log (∑ x,Real.exp (f x+a))=Real.log (∑ x,Real.exp (f x))+a := by
  simp_rw [Real.exp_add]
  rw [← Finset.sum_mul,Real.log_mul (ne_of_gt (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)) (Real.exp_ne_zero _),Real.log_exp]

lemma logPartition_center {p N k : ℕ} (θ : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) :
    logPartition (fun j => centerSample (θ j)) h indices=
      logPartition θ h indices-(∑ j,referenceEnergy (θ j)) := by
  have he σ : logWeight (fun j => centerSample (θ j)) h indices σ=
      logWeight θ h indices σ+(-(∑ j,referenceEnergy (θ j))) := by
    simp only [logWeight,centerSample,centeredInteraction,referenceEnergy,Finset.sum_sub_distrib]
    ring
  simp only [logPartition,he,logSumExp_add_constant,sub_eq_add_neg]

lemma indexAverage_center {p N k : ℕ} (hN : 0 < N) (θ : Fin k → InteractionSample p) (h : Fin N → ℝ) :
    indexAverage (fun j => centerSample (θ j)) h=indexAverage θ h-(∑ j,referenceEnergy (θ j)) := by
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have hc : (Fintype.card (Fin k → Fin p → Fin N):ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  simp only [indexAverage,logPartition_center,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [sub_div,mul_div_cancel_left₀ _ hc]

lemma fieldAverage_center {p N k : ℕ} (M : Model p) (hN : 0 < N)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (θ : Fin k → InteractionSample p) :
    fieldAverage (N := N) (centeredModel M) (fun j => centerSample (θ j))=
      fieldAverage (N := N) M θ-(∑ j,referenceEnergy (θ j)) := by
  rw [centeredModel,indexAverage_mapModel]
  simp only [id_eq,indexAverage_center hN]
  rw [integral_sub (indexAverage_integrable_and_fieldAverage_bound M hh hN θ).1 (integrable_const _)]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,fieldAverage]

lemma disorderAverage_center {p N : ℕ} (M : Model p) (hN : 0 < N)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    disorderAverage (centeredModel M) N k=disorderAverage M N k-
      (k:ℝ)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure) := by
  rw [centeredModel,disorderAverage_map_eq]
  change (∫ θ : Fin k → InteractionSample p,fieldAverage (N := N) (centeredModel M) (fun j => centerSample (θ j))
    ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure))=_
  simp_rw [fieldAverage_center M hN hh]
  rw [integral_sub (fieldAverage_integrable_and_disorderAverage_bound M hθ hh hN k).1
    (integrable_pi_sum M.disorder.toMeasure (referenceEnergy_integrable M hθ)),
    integral_pi_sum M.disorder.toMeasure (referenceEnergy_integrable M hθ)]
  simp only [Fintype.card_fin,disorderAverage]

lemma pressure_center {p N : ℕ} (M : Model p) (hN : 0 < N)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    pressure (centeredModel M) N=pressure M N-(M.alpha:ℝ)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure) := by
  change (∫ k,disorderAverage (centeredModel M) N k ∂poissonMeasure (M.alpha*N))/N=_
  simp_rw [disorderAverage_center M hN hθ hh]
  rw [integral_sub (disorderAverage_integrable_and_pressure_bound M hθ hh hN).1
    ((poisson_integrable_count _).mul_const _),integral_mul_const,poisson_mean]
  change ((∫ k,disorderAverage M N k ∂poissonMeasure (M.alpha*N))-(M.alpha*N:ℝ≥0)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure))/N=_
  simp only [NNReal.coe_mul,NNReal.coe_natCast,pressure,disorderAverage,fieldAverage,indexAverage]
  have hn : (N:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hN)
  field_simp
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PressureLiminf
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter

lemma pressure_bounded {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    IsBoundedUnder (· ≤ ·) atTop (pressure M) ∧ IsBoundedUnder (· ≥ ·) atTop (pressure M) := by
  have he : ∀ᶠ N in atTop, |pressure M N-Real.log 2| ≤ (M.alpha:ℝ)*interactionMoment M+fieldMoment M := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (disorderAverage_integrable_and_pressure_bound M hθ hh hN).2
  constructor
  · apply isBoundedUnder_of_eventually_le (a := Real.log 2+(M.alpha:ℝ)*interactionMoment M+fieldMoment M)
    filter_upwards [he] with N hN
    linarith [(abs_le.mp hN).2]
  · apply isBoundedUnder_of_eventually_ge (a := Real.log 2-((M.alpha:ℝ)*interactionMoment M+fieldMoment M))
    filter_upwards [he] with N hN
    linarith [(abs_le.mp hN).1]

lemma liminf_le_liminf_add_of_eventually_le {f g : ℕ → ℝ} {c : ℝ}
    (hf : IsBoundedUnder (· ≥ ·) atTop f)
    (hg : IsBoundedUnder (· ≤ ·) atTop g ∧ IsBoundedUnder (· ≥ ·) atTop g)
    (hle : ∀ᶠ n in atTop, f n ≤ g n+c) :
    liminf f atTop ≤ liminf g atTop+c := by
  rw [← liminf_add_const atTop g c hg.1.isCobounded_ge hg.2]
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => g n+c) := by
    obtain ⟨b,hb⟩ := hg.1.eventually_le
    exact isBoundedUnder_of_eventually_le (a := b+c) (hb.mono (fun n hn => by linarith))
  exact liminf_le_liminf hle hf hb.isCobounded_ge
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CenteredTrialLocal
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

lemma logWeightedExp_add_constant {ι : Type*} [Fintype ι] [Nonempty ι]
    (f w : ι → ℝ) (hw : ∀ i,0 < w i) (a : ℝ) :
    Real.log (∑ i,Real.exp (f i+a)*w i)=Real.log (∑ i,Real.exp (f i)*w i)+a := by
  have he : (∑ i,Real.exp (f i+a)*w i)=(∑ i,Real.exp (f i)*w i)*Real.exp a := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.exp_add]
    ring
  rw [he,Real.log_mul (ne_of_gt (Finset.sum_pos (fun i _ => mul_pos (Real.exp_pos _) (hw i)) Finset.univ_nonempty))
    (Real.exp_ne_zero _),Real.log_exp]

lemma log_edge_center {p : ℕ} (z : InteractionSample p) (x : Fin p → ℝ) :
    Real.log (edge (centerSample z).1 x)=Real.log (edge z.1 x)-referenceEnergy z := by
  simpa only [edge,centerSample,centeredInteraction,referenceEnergy,sub_eq_add_neg] using
    logWeightedExp_add_constant z.1 (fun s => ∏ l,q (x l) (s l))
      (fun s => Finset.prod_pos (fun l _ => q_pos _ _)) (-referenceEnergy z)

lemma message_center {p : ℕ} (z : InteractionSample p) (x : Fin (p-1) → ℝ) (ε : Spin) :
    message (centerSample z).1 x ε=message z.1 x ε-referenceEnergy z := by
  simpa only [message,centerSample,centeredInteraction,referenceEnergy,sub_eq_add_neg] using
    logWeightedExp_add_constant (fun s => z.1 (appendSpin s ε)) (fun s => ∏ l,q (x l) (s l))
      (fun s => Finset.prod_pos (fun l _ => q_pos _ _)) (-referenceEnergy z)

lemma siteLog_center {p k : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (x : Fin k×Fin (p-1) → ℝ) :
    siteLog (fun j => centerSample (θ j)) h x=siteLog θ h x-(∑ j,referenceEnergy (θ j)) := by
  have he ε : h*spin ε+∑ j,message (centerSample (θ j)).1 (fun l => x (j,l)) ε=
      (h*spin ε+∑ j,message (θ j).1 (fun l => x (j,l)) ε)+(-(∑ j,referenceEnergy (θ j))) := by
    simp only [message_center,Finset.sum_sub_distrib]
    ring
  simp only [siteLog,he]
  have hh := logWeightedExp_add_constant (fun ε => h*spin ε+∑ j,message (θ j).1 (fun l => x (j,l)) ε)
    (fun _ : Spin => (1:ℝ)/2) (fun _ => by norm_num) (-(∑ j,referenceEnergy (θ j)))
  simpa only [mul_one_div,← Finset.sum_div,sub_eq_add_neg] using hh

lemma trial_site_center {p k r : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (siteLog (fun j => centerSample (θ j)) h)=
      trialLog r ζ m (siteLog θ h)-(∑ j,referenceEnergy (θ j)) := by
  have he : siteLog (fun j => centerSample (θ j)) h=(fun x => siteLog θ h x+(-(∑ j,referenceEnergy (θ j)))) := by
    funext x
    simpa only [sub_eq_add_neg] using siteLog_center θ h x
  rw [he,trialLog_add_constant r _ (continuous_siteLog θ h) (siteLog_bound θ h) m hm]
  rfl

lemma trial_edge_center {p r : ℕ} (z : InteractionSample p)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun x => Real.log (edge (centerSample z).1 x))=
      trialLog r ζ m (fun x => Real.log (edge z.1 x))-referenceEnergy z := by
  simp_rw [log_edge_center,sub_eq_add_neg]
  rw [trialLog_add_constant r _ (continuous_log_edge z.1) (log_edge_bound z.1) m hm]
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter

lemma centeredModel_interaction_integrable {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) :
    Integrable (fun z : InteractionSample p => ‖z.1‖) (centeredModel M).disorder.toMeasure := by
  exact mapModel_interaction_integrable M centerSample id (measurable_centerSample p) measurable_id
    (centeredInteraction_integrable M hθ)

lemma centeredModel_field_integrable {p : ℕ} (M : Model p)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    Integrable (fun h : ℝ => |h|) (centeredModel M).field.toMeasure := by
  exact mapModel_field_integrable M centerSample id (measurable_centerSample p) measurable_id hh

lemma liminf_pressure_center {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    liminf (pressure (centeredModel M)) atTop=liminf (pressure M) atTop-
      (M.alpha:ℝ)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure) := by
  have he : pressure (centeredModel M)=ᶠ[atTop]
      (fun N => pressure M N-(M.alpha:ℝ)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact pressure_center M hN hθ hh
  rw [liminf_congr he]
  exact liminf_sub_const atTop (pressure M) _ (pressure_bounded M hθ hh).1.isCobounded_ge
    (pressure_bounded M hθ hh).2
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperTrial
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal

lemma cavityProxy_envelope {p : ℕ} (M : Model p) {C H : ℝ}
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C) (hh : ∀ᵐ h ∂M.field.toMeasure,|h|≤H)
    (N L : ℕ) (u : Spec L×ℕ → ℝ) :
    |cavityProxy M C H N L u-Real.log 2| ≤ H+C*(M.alpha*p:ℝ≥0)+C*(M.alpha*(p-1:ℕ):ℝ≥0) := by
  have hs : |insertionPoisson M C H N L u
      (fun k => (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)
      (fun _ z => cavitySiteEnergy z.1 z.2) (M.alpha*p)| ≤ H+C*(M.alpha*p:ℝ≥0) := by
    apply poisson_average_bound
    intro k
    exact abs_integral_le_bound_ae _ ((cavitySiteEnergy_ae_bound (k := k) M hθ hh).mono
      (fun z hz => reservoirInsertionOn_bound M C H N L u _ hz))
  have hb : |insertionPoisson M C H N L u
      (fun k => Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
      (fun _ θ => cavityBondEnergy θ) (M.alpha*(p-1:ℕ))| ≤ 0+C*(M.alpha*(p-1:ℕ):ℝ≥0) := by
    apply poisson_average_bound
    intro k
    exact abs_integral_le_bound_ae _ ((cavityBondEnergy_ae_bound (k := k) M hθ).mono
      (fun z hz => reservoirInsertionOn_bound M C H N L u _ hz))
  have hx := (abs_sub _ _).trans (add_le_add hs hb)
  convert hx using 1 <;> first | rfl | (dsimp [cavityProxy]; congr 1; ring)

lemma cavityProxy_functional_bound {p : ℕ} (M : Model p) {C H : ℝ}
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C) (hh : ∀ᵐ h ∂M.field.toMeasure,|h|≤H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (N L : ℕ) (u : Spec L×ℕ → ℝ) :
    |cavityProxy M C H N L u-functional M L (reservoirTrialLaw M C H N L u)
      (fun i => gridExponents L i.castSucc)| ≤
      (H+C*(M.alpha*p:ℝ≥0)+C*(M.alpha*(p-1:ℕ):ℝ≥0))+functionalEnvelope M := by
  simpa only [sub_sub_sub_cancel_right] using
    (abs_sub (cavityProxy M C H N L u-Real.log 2)
      (functional M L (reservoirTrialLaw M C H N L u) (fun i => gridExponents L i.castSucc)-Real.log 2)).trans
      (add_le_add (cavityProxy_envelope M hθ hh N L u)
        (functional_envelope M hθi hhi _ _ (fun i => gridExponents_pos L i.castSucc)))

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

lemma trialSiteField_center {p r k : ℕ} (M : Model p) (m : Fin r → ℝ)
    (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1))
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (θ : Fin k → InteractionSample p) :
    trialSiteField (centeredModel M) m ζ (fun j => centerSample (θ j))=
      trialSiteField M m ζ θ-∑ j,referenceEnergy (θ j) := by
  rw [centeredModel,trialSiteField_map_eq M m hm]
  simp only [id_eq,trial_site_center θ _ m hm]
  rw [integral_sub (integrable_trial_site_field M m hm hh ζ θ) (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul,trialSiteField]

lemma trialSiteDisorder_center {p r : ℕ} (M : Model p) (m : Fin r → ℝ)
    (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1))
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    trialSiteDisorder (centeredModel M) m ζ k= trialSiteDisorder M m ζ k-
      (k:ℝ)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure) := by
  rw [centeredModel,trialSiteDisorder_map_eq M m hm]
  change (∫ θ : Fin k → InteractionSample p,trialSiteField (centeredModel M) m ζ (fun j => centerSample (θ j))
    ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure))=_
  simp_rw [trialSiteField_center M m hm ζ hh]
  rw [integral_sub (integrable_trialSiteField M m hm hθ hh ζ k)
    (integrable_pi_sum M.disorder.toMeasure (referenceEnergy_integrable M hθ)),
    integral_pi_sum M.disorder.toMeasure (referenceEnergy_integrable M hθ)]
  simp only [Fintype.card_fin,trialSiteDisorder]

lemma trialEdge_center {p r : ℕ} (M : Model p) (m : Fin r → ℝ)
    (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1))
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) :
    (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂(centeredModel M).disorder.toMeasure)=
      (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂M.disorder.toMeasure)-
      ∫ z,referenceEnergy z ∂M.disorder.toMeasure := by
  change (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂Measure.map centerSample M.disorder.toMeasure)=_
  have heq : (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂Measure.map centerSample M.disorder.toMeasure)=
      ∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge (centerSample z).1 x)) ∂M.disorder.toMeasure :=
    integral_map (measurable_centerSample p).aemeasurable
      (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
  rw [heq]
  simp_rw [trial_edge_center _ m hm ζ]
  apply integral_sub _ (referenceEnergy_integrable M hθ)
  apply hθ.mono' (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Function.comp_apply] using trial_edge_bound r m hm ζ z.1)

lemma functional_center {p r : ℕ} (M : Model p) (hp : 1 ≤ p) (m : Fin r → ℝ)
    (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1))
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    functional (centeredModel M) r ζ m=functional M r ζ m-
      (M.alpha:ℝ)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure) := by
  have hsi : Integrable (trialSiteDisorder M m ζ) (poissonMeasure (M.alpha*p)) := by
    apply ((integrable_const _).add ((poisson_integrable_count _).mul_const _)).mono'
      StronglyMeasurable.of_discrete.aestronglyMeasurable
    exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs,Pi.add_def,Pi.mul_def] using trialSiteDisorder_bound M m hm hθ hh ζ k)
  change Real.log 2+(∫ k,trialSiteDisorder (centeredModel M) m ζ k ∂poissonMeasure (M.alpha*p))-
    (M.alpha:ℝ)*(p-1:ℕ)*(∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂(centeredModel M).disorder.toMeasure)=_
  simp_rw [trialSiteDisorder_center M m hm ζ hθ hh]
  rw [integral_sub hsi ((poisson_integrable_count _).mul_const _),integral_mul_const,poisson_mean,
    trialEdge_center M m hm ζ hθ]
  simp only [NNReal.coe_mul,NNReal.coe_natCast,Nat.cast_sub hp,Nat.cast_one,functional,trialSiteDisorder,trialSiteField]
  ring
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalFieldOrder
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {p N : ℕ} [NeZero N]

lemma centeredDisorderAt_bound (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (k : ℕ) (h : Fin N → ℝ) :
    |centeredDisorderAt M k h|≤k*interactionMoment M+∑ i,|h i| := by
  have hb := norm_integral_le_of_norm_le (f := fun z : Fin k → InteractionSample p =>
      indexAverage z h-(N:ℝ)*Real.log 2)
    ((interaction_sum_integrable M hθ k).add (integrable_const (∑ i,|h i|)))
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply,Pi.sub_apply] using (indexAverage_bound (NeZero.pos N) z h)))
  simpa only [centeredDisorderAt,Real.norm_eq_abs,Pi.add_apply,
    integral_add (interaction_sum_integrable M hθ k) (integrable_const _),
    integral_const,probReal_univ,one_smul,integral_interaction_sum M hθ k,interactionMoment] using hb

omit [NeZero N] in
lemma centeredDisorderAt_measurable (M : Model p) (k : ℕ) :
    Measurable (centeredDisorderAt (N := N) M k) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  exact ((continuous_indexAverage (p := p) (k := k) (N := N)).sub continuous_const).stronglyMeasurable.integral_prod_left.measurable

lemma centeredIndex_integrable_prod (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    Integrable (fun z : (Fin k → InteractionSample p)×(Fin N → ℝ) =>
      indexAverage z.1 z.2-(N:ℝ)*Real.log 2)
      ((Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod
        (Measure.pi (fun _ : Fin N => M.field.toMeasure))) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  apply (((interaction_sum_integrable M hθ k).comp_fst _).add
    ((integrable_pi_sum M.field.toMeasure hh).comp_snd _)).mono'
    ((continuous_indexAverage (p := p) (k := k) (N := N)).sub continuous_const).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply,Pi.sub_apply] using (indexAverage_bound (NeZero.pos N) z.1 z.2))

lemma centeredDisorderAt_integral (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    (∫ h : Fin N → ℝ,centeredDisorderAt M k h ∂Measure.pi (fun _ : Fin N => M.field.toMeasure))=
      disorderAverage M N k-(N:ℝ)*Real.log 2 := by
  simp only [centeredDisorderAt]
  rw [← integral_integral_swap (centeredIndex_integrable_prod M hθ hh k)]
  simp_rw [integral_sub (indexAverage_integrable_and_fieldAverage_bound M hh (NeZero.pos N) _).1
    (integrable_const _),integral_const,probReal_univ,one_smul]
  simpa only [fieldAverage,disorderAverage,integral_const,probReal_univ,one_smul] using
    (integral_sub (fieldAverage_integrable_and_disorderAverage_bound M hθ hh (NeZero.pos N) k).1
      (integrable_const ((N:ℝ)*Real.log 2)))

lemma centeredDisorderAt_joint_integrable (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (r : ℝ≥0) :
    Integrable (fun z : ℕ×(Fin N → ℝ) => centeredDisorderAt M z.1 z.2)
      ((poissonMeasure r).prod (Measure.pi (fun _ : Fin N => M.field.toMeasure))) := by
  apply ((((poisson_integrable_count r).mul_const (interactionMoment M)).comp_fst _).add
    ((integrable_pi_sum M.field.toMeasure hh).comp_snd _)).mono'
  · exact (measurable_from_prod_countable_right (fun k => centeredDisorderAt_measurable M k)).aestronglyMeasurable
  · exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using (centeredDisorderAt_bound M hθ z.1 z.2))

lemma centeredPressure_field_order (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    (∫ h : Fin N → ℝ,∫ k,centeredDisorderAt M k h ∂poissonMeasure (M.alpha*N)
      ∂Measure.pi (fun _ : Fin N => M.field.toMeasure))=
        (N:ℝ)*(pressure M N-Real.log 2) := by
  rw [← integral_integral_swap (centeredDisorderAt_joint_integrable M hθ hh (M.alpha*N))]
  simp_rw [centeredDisorderAt_integral M hθ hh]
  rw [integral_sub (disorderAverage_integrable_and_pressure_bound M hθ hh (NeZero.pos N)).1
    (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]
  change (∫ k,disorderAverage M N k ∂poissonMeasure (M.alpha*N))-(N:ℝ)*Real.log 2=
    (N:ℝ)*((∫ k,disorderAverage M N k ∂poissonMeasure (M.alpha*N))/(N:ℝ)-Real.log 2)
  have hN : (N:ℝ)≠0 := by exact_mod_cast NeZero.ne N
  field_simp

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_IntegratedFiniteUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory ProbabilityTheory KernelTower
open scoped NNReal BigOperators
variable {Λ R : Type} [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {N q : ℕ} [NeZero N]

lemma finiteTrial_pressure_le (M : Model (q+1)) (hM : Admissible M)
    (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin r → ℝ) (hm : Exponents m) :
    pressure M N ≤ functional M r (finiteTrialLaw r Q U x) m := by
  let ζ := finiteTrialLaw r Q U x
  let μ := Measure.pi (fun _ : Fin N => M.field.toMeasure)
  let S : ℝ → ℝ := fun h => ∫ k,trialDisorderAt M m ζ k h ∂poissonMeasure (M.alpha*(q+1))
  let E := ∫ z,trialLog r ζ m (fun y => Real.log (edge z.1 y)) ∂M.disorder.toMeasure
  have hp : ∀ d,0 < m d := fun d => (hm.2 d).1
  have hS : Integrable S M.field.toMeasure :=
    (trialDisorderAt_joint_integrable M m hp ζ hM.interaction_integrable hM.field_integrable _).integral_prod_right
  have hF := (centeredDisorderAt_joint_integrable (N := N) M hM.interaction_integrable
    hM.field_integrable (M.alpha*N)).integral_prod_right
  have hiS (s : Fin N) : Integrable (fun h : Fin N → ℝ => S (h s)) μ :=
    integrable_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) (i := s) hS
  have hb (h : Fin N → ℝ) :
      (∫ k,centeredDisorderAt M k h ∂poissonMeasure (M.alpha*N))+(M.alpha:ℝ)*N*q*E ≤ ∑ s,S (h s) := by
    have he := finiteTrial_upper_fixedField M hM a r Q U x m hm h
    simpa only [FiniteLaw.expect_sub,FiniteLaw.expect_const,FiniteLaw.expect_uniform,
      centeredDisorderAt,indexAverage,trialDisorderAt,S,E,ζ] using he
  have hi := integral_mono (hF.add (integrable_const ((M.alpha:ℝ)*N*q*E)))
    (integrable_finsetSum Finset.univ (fun s _ => hiS s)) hb
  simp only [Pi.add_apply] at hi
  rw [integral_add hF (integrable_const _),integral_const,probReal_univ,one_smul,
    centeredPressure_field_order M hM.interaction_integrable hM.field_integrable,
    integral_finsetSum _ (fun s _ => hiS s)] at hi
  dsimp only [μ] at hi
  simp only [integral_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) hS.aestronglyMeasurable,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hi
  dsimp only [S] at hi
  rw [trialPoisson_field_order M m hp ζ hM.interaction_integrable hM.field_integrable] at hi
  have hN : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
  unfold functional
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
  change pressure M N ≤ Real.log 2+(∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*(q+1)))-
    (M.alpha:ℝ)*q*E
  nlinarith

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_DenseUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory KernelTower PrescribedTree Set
open scoped NNReal BigOperators
variable {N q : ℕ} [NeZero N]

lemma finiteHierarchy_pressure_le (M : Model (q+1)) (hM : Admissible M)
    (r : ℕ) (ζ : Hierarchy (r+1)) (hζ : FiniteHierarchy (r+1) ζ)
    (m : Fin r → ℝ) (hm : Exponents m) : pressure M N ≤ functional M r ζ m := by
  obtain ⟨n,hn,T,V,hT⟩ := finiteHierarchy_realization (r+1) ζ hζ
  let a : Fin n := ⟨0,hn⟩
  have h := finiteTrial_pressure_le (N := N) M hM a r T.1 T.2 (fun b y => V (b,y)) m hm
  have he : finiteTrialLaw r T.1 T.2 (fun b y => V (b,y))=ζ := hT
  rwa [he] at h

lemma pressure_le_functional (M : Model (q+1)) (hM : Admissible M)
    (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : Exponents m) :
    pressure M N ≤ functional M r ζ m := by
  have hc : IsClosed {ζ : Hierarchy (r+1) | pressure M N ≤ functional M r ζ m} :=
    isClosed_le continuous_const (functional_continuous M m (fun d => (hm.2 d).1)
      hM.interaction_integrable hM.field_integrable)
  have hs : {ζ : Hierarchy (r+1) | FiniteHierarchy (r+1) ζ} ⊆
      {ζ : Hierarchy (r+1) | pressure M N ≤ functional M r ζ m} := by
    intro η hη
    exact finiteHierarchy_pressure_le M hM r η hη m hm
  exact closure_minimal hs hc ((finiteHierarchy_dense (r+1)) ζ)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_VariationalUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory KernelTower PrescribedTree Set Filter
open scoped NNReal BigOperators Topology
variable {N q : ℕ} [NeZero N]

lemma pressure_le_phi (M : Model (q+1)) (hM : Admissible M) (r : ℕ) :
    pressure M N ≤ phi M r := by
  obtain ⟨m,hm⟩ := exponents_nonempty r
  apply le_csInf
  · exact ⟨functional M r (zeroHierarchy (r+1)) m,zeroHierarchy (r+1),m,hm,rfl⟩
  · rintro v ⟨ζ,m,hm,rfl⟩
    exact pressure_le_functional M hM r ζ m hm

lemma pressure_le_variationalValue (M : Model (q+1)) (hM : Admissible M) :
    pressure M N ≤ variationalValue M := by
  apply le_ciInf
  intro r
  exact pressure_le_phi M hM r

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProxyRateIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter
open scoped Topology

/-- The upper comparison for the exact arity and first-moment hypotheses of
`main:theorem`; no bounded representative is assumed. -/
lemma pressure_le_variationalValue_exact {p N : ℕ} (M : Model p)
    (hM : Admissible M) (hN : 0<N) : pressure M N ≤ variationalValue M := by
  have hp : p=(p-1)+1 := by have := hM.arity; omega
  revert M
  rw [hp]
  intro M hM
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact pressure_le_variationalValue M hM

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_IncrementErrorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open Filter
open scoped Topology NNReal
lemma cavityIncrementError_tendsto (α : ℝ≥0) (q : ℕ) (C : ℝ) :
    Tendsto (cavityIncrementError α q C) atTop (𝓝 0) := by
  have h1 := (cavityBadRate_tendsto α q).const_mul C
  have h2 := scoreScale_div_succ_tendsto.const_mul 6
  have h3 := (((oneNewRate_tendsto α q).sub_const ((α:ℝ)*(q+1))).abs).const_mul C
  have h4 := (((reservoir_deficit_tendsto α q).sub_const ((α:ℝ)*q)).abs).const_mul C
  have hh := (((h1.add h2).add h3).add h4).add scoreScale_succ_difference_tendsto
  unfold cavityIncrementError
  simpa only [mul_div_assoc,sub_self,abs_zero,mul_zero,add_zero] using hh
end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_BoundedCavityLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory Filter Set ConcreteReservoir
open scoped NNReal Topology

lemma bounded_symmetric_trial_lower {q : ℕ} (M : Model (q+1)) (hα : 0 < M.alpha)
    {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure,|h|≤H)
    (hθi : Integrable (fun z : InteractionSample (q+1) => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun z : InteractionSample (q+1) => z.1)
      (fun z : InteractionSample (q+1) => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ),Exponents m ∧
      functional M r ζ m ≤ liminf (pressure M) atTop+ε := by
  have hθ' : ∀ᵐ z ∂M.disorder.toMeasure,∀ σ,|z.1 σ|≤C := hθ.mono (fun z hz σ =>
    (show |z.1 σ|≤‖z.1‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z.1 σ).trans hz)
  obtain ⟨Ns,us,hNs,hu,hinc,hcontrol,_⟩ := full_regular_covariance_selection M hC hH hθ' hh hθi hhi
    (show 0 < ε/4 by positivity)
  let gap := fun L n => |cavityProxy M C H (Ns L n+1) L (us L n)-
    functional M L (reservoirTrialLaw M C H (Ns L n+1) L (us L n)) (fun i => gridExponents L i.castSucc)|
  have hlim : Tendsto (fun L => limsup (gap L) atTop) atTop (𝓝 0) :=
    cavityProxy_comparison_tendsto M hα hC hH hθ hh hθi hhi Ns (fun L => (hNs L).tendsto_atTop) us hcontrol
  have hL := ((tendsto_order.1 hlim).2 (ε/4) (by positivity)).exists
  obtain ⟨L,hL⟩ := hL
  have hB : IsBoundedUnder (·≤·) atTop (gap L) := isBoundedUnder_of_eventually_le
    (Eventually.of_forall (fun n => cavityProxy_functional_bound M hθ hh hθi hhi (Ns L n+1) L (us L n)))
  have hsmall : ∀ᶠ n in atTop,gap L n<ε/4 := eventually_lt_of_limsup_lt hL hB
  have hNlim : Tendsto (fun n => Ns L n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp (hNs L).tendsto_atTop
  have herr := (cavityIncrementError_tendsto M.alpha q C).comp hNlim
  have hevent : ∀ᶠ n in atTop,cavityIncrementError M.alpha q C (Ns L n+1)<ε/4 :=
    (tendsto_order.1 herr).2 (ε/4) (by positivity)
  obtain ⟨n,hn,he⟩ := (hsmall.and hevent).exists
  refine ⟨L,reservoirTrialLaw M C H (Ns L n+1) L (us L n),
    (fun i => gridExponents L i.castSucc),gridExponents_exponents L,?_⟩
  have hp := increment_cavityProxy_bound M hC hH hθ' hh hsym (Ns L n) (us L n)
  have hg := (abs_lt.mp hn).1
  have hi := (abs_le.mp hp).1
  have hb := hinc L n
  linarith
end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SymmetricTrialLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

lemma symmetric_trial_lower {q : ℕ} (M : Model (q+1)) (hα : 0 < M.alpha)
    (hθ : Integrable (fun z : InteractionSample (q+1) => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun z : InteractionSample (q+1) => z.1)
      (fun z : InteractionSample (q+1) => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ),Exponents m ∧
      functional M r ζ m ≤ liminf (pressure M) atTop+ε := by
  let D := fun K : ℕ => ∫ z : InteractionSample (q+1),‖(clipSample (K:ℝ) z).1-z.1‖ ∂M.disorder.toMeasure
  let d := fun K : ℕ => ∫ h : ℝ,|clipReal (K:ℝ) h-h| ∂M.field.toMeasure
  have hD : Tendsto D atTop (𝓝 0) := by simpa only [D,norm_sub_rev] using clipping_interaction_error_tendsto M hθ
  have hd : Tendsto d atTop (𝓝 0) := by simpa only [d,abs_sub_comm] using clipping_field_error_tendsto M hh
  have he : Tendsto (fun K => (M.alpha:ℝ)*((q+1:ℕ)+(q:ℝ)+1)*D K+2*d K) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using (hD.const_mul ((M.alpha:ℝ)*((q+1:ℕ)+(q:ℝ)+1))).add (hd.const_mul 2)
  obtain ⟨K,hK⟩ := ((tendsto_order.1 he).2 (ε/2) (by positivity)).exists
  have hK0 : 0 ≤ (K:ℝ) := Nat.cast_nonneg K
  obtain ⟨r,ζ,m,hm,hl⟩ := UniversalDictionary.bounded_symmetric_trial_lower (clippedModel M (K:ℝ)) hα hK0 hK0
    (clippedModel_interaction_bounded M hK0) (clippedModel_field_bounded M hK0)
    (clippedModel_interaction_integrable M hK0) (clippedModel_field_integrable M hK0)
    (clippedModel_symmetric M (K:ℝ) hsym) (show 0 < ε/2 by positivity)
  have hDi := clip_interaction_difference_integrable M hK0 hθ
  have hdi := clip_field_difference_integrable M hK0 hh
  have hP : liminf (pressure (clippedModel M (K:ℝ))) atTop ≤ liminf (pressure M) atTop+(M.alpha:ℝ)*D K+d K := by
    have he' : ∀ᶠ N in atTop,pressure (clippedModel M (K:ℝ)) N ≤ pressure M N+((M.alpha:ℝ)*D K+d K) := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hb := (abs_le.mp (pressure_map_stability M hN hθ hh (clipSample (K:ℝ)) (clipReal (K:ℝ))
        (measurable_clipSample _) (measurable_clipReal _) hDi hdi)).2
      change pressure (clippedModel M (K:ℝ)) N-pressure M N ≤ (M.alpha:ℝ)*D K+d K at hb
      linarith
    have hb := liminf_le_liminf_add_of_eventually_le
      (pressure_bounded (clippedModel M (K:ℝ)) (clippedModel_interaction_integrable M hK0) (clippedModel_field_integrable M hK0)).2
      (pressure_bounded M hθ hh) he'
    linarith
  have hF := (abs_le.mp (functional_map_stability M m (fun i => (hm.2 i).1) ζ hθ hh
    (clipSample (K:ℝ)) (clipReal (K:ℝ)) (measurable_clipSample _) (measurable_clipReal _) hDi hdi)).1
  change -((M.alpha:ℝ)*(((q+1:ℕ):ℝ)+((q+1-1:ℕ):ℝ))*D K+d K) ≤
    functional (clippedModel M (K:ℝ)) r ζ m-functional M r ζ m at hF
  simp only [Nat.add_sub_cancel] at hF
  refine ⟨r,ζ,m,hm,?_⟩
  nlinarith
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ExactVariationalLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter

lemma admissible_trial_lower {q : ℕ} (M : Model (q+1)) (hM : Admissible M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ),Exponents m ∧
      functional M r ζ m ≤ liminf (pressure M) atTop+ε := by
  obtain ⟨r,ζ,m,hm,hl⟩ := symmetric_trial_lower (centeredModel M) hM.density
    (centeredModel_interaction_integrable M hM.interaction_integrable)
    (centeredModel_field_integrable M hM.field_integrable) (centeredModel_symmetric M hM) hε
  rw [functional_center M (by omega) m (fun i => (hm.2 i).1) ζ
    hM.interaction_integrable hM.field_integrable,
    liminf_pressure_center M hM.interaction_integrable hM.field_integrable] at hl
  exact ⟨r,ζ,m,hm,by linarith⟩

lemma variationalValue_le_liminf_pressure {p : ℕ} (M : Model p) (hM : Admissible M) :
    variationalValue M ≤ liminf (pressure M) atTop := by
  have hp : p=(p-1)+1 := by have := hM.arity; omega
  revert M
  rw [hp]
  intro M hM
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r,ζ,m,hm,hl⟩ := admissible_trial_lower M hM hε
  exact (variationalValue_le_functional_integrable M hM.interaction_integrable hM.field_integrable r ζ m hm).trans hl
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter
open scoped Topology

 
theorem mezard_parisi_oai {p : ℕ} (M : Model p) (hM : Admissible M) :
    Tendsto (pressure M) atTop (𝓝 (variationalValue M)) := by
  have hb := pressure_bounded M hM.interaction_integrable hM.field_integrable
  have hu : limsup (pressure M) atTop ≤ variationalValue M := by
    apply limsup_le_of_le hb.2.isCobounded_le
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact pressure_le_variationalValue_exact M hM hN
  exact tendsto_of_le_liminf_of_limsup_le (variationalValue_le_liminf_pressure M hM) hu hb.1 hb.2
end DilutedSpinGlass

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.mezard_parisi_oai := @OAI.DilutedSpinGlass.mezard_parisi_oai
