-- Prove2me | solution 1 for OAI.FixedClauseThreshold.Computability.deletion_increment_linear_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:47:03.001333+00:00
-- url     : https://prove2.me/submissions/93494429-0f2c-4f26-a1fc-9ab2c071cab3

import Mathlib
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A002
import Theorems.Thm_OAI_FixedClauseThreshold_Computability_restored_process_moment_sat

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CompoundPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma charFunDual_iid_sum (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (L : StrongDual ℝ E) :
    charFunDual (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) L =
      charFunDual μ L ^ n := by
  rw [charFunDual_apply,integral_map (by fun_prop) (by fun_prop)]
  simp_rw [map_sum,Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin n => fun x : E => Complex.exp ((L x : ℂ)*Complex.I))]
  simp only [charFunDual_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma charFunDual_compoundPoisson (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : StrongDual ℝ E) :
    charFunDual (compoundPoisson r μ) L = Complex.exp ((r:ℂ)*(charFunDual μ L-1)) := by
  have hi : Integrable (fun x : E => Complex.exp ((L x:ℂ)*Complex.I)) (compoundPoisson r μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  change (∫ x, Complex.exp ((L x:ℂ)*Complex.I) ∂compoundPoisson r μ) = _
  rw [compoundPoisson,integral_sum_measure hi]
  have hw (n : ℕ) : 0 ≤ Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial := by positivity
  simp_rw [integral_smul_measure,ENNReal.toReal_ofReal (hw _)]
  change (∑' n : ℕ, (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial) •
    charFunDual (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) L) = _
  simp_rw [charFunDual_iid_sum,Complex.real_smul]
  have hh := (NormedSpace.expSeries_div_hasSum_exp ((r:ℂ)*charFunDual μ L)).mul_left
    (Complex.exp (-(r:ℂ)))
  have he : (fun n : ℕ => ((Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial:ℝ):ℂ)*charFunDual μ L^n) =
      (fun n : ℕ => Complex.exp (-(r:ℂ))*(((r:ℂ)*charFunDual μ L)^n/n.factorial)) := by
    funext n
    simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,
      Complex.ofReal_exp,Complex.ofReal_neg,mul_pow]
    ring
  rw [he,hh.tsum_eq]
  rw [← Complex.exp_eq_exp_ℂ,← Complex.exp_add]
  congr 1
  ring
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonMoments
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_MarkedPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_FinitePoissonSplit
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma integral_finiteUniform {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : A → E) :
    (∫ x, f x ∂finiteUniform A) = ((Fintype.card A:ℝ)⁻¹) • ∑ x,f x := by
  rw [finiteUniform,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Finset.smul_sum]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootProductLaw
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma finiteUniform_pi {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] :
    Measure.pi (fun _ : ι => finiteUniform J) = finiteUniform (ι → J) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  simp [Measure.pi_singleton,finiteUniform,PMF.uniformOfFintype_apply,ENNReal.inv_pow]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateProcess
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

theorem candidateStep_mono {n : ℕ} [NeZero n] (k : ℕ) :
    Monotone (candidateStep (n := n) k) := by
  intro f g h U
  exact FiniteLaw.expect_mono _ (fun _ => h _)

theorem candidateKill_iterate {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) :
    batchKillProbability U k d = 1 - (candidateStep k)^[d] candidateAlive U := by
  rw [candidateStep_iterate]
  have he (cs : Fin d → Fin k → SignedLiteral n) :
      (if batchKills U cs then (1 : ℝ) else 0) =
        1 - candidateAlive (candidateResidual U cs) := by
    rw [candidateAlive, ← candidateResidual_empty_iff]
    by_cases h : candidateResidual U cs = ∅
    · simp [h]
    · simp [h, Finset.nonempty_iff_ne_empty]
  simp_rw [batchKillProbability, he, FiniteLaw.expect_sub, FiniteLaw.expect_const]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DeletionIncrement
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset
open DilutedSpinGlass
open scoped BigOperators

theorem bestDeletionTime_mono {n : ℕ} (t : Finset (Fin n) → ℝ) :
    Monotone (bestDeletionTime t) := by
  intro r s hrs
  apply Finset.sup'_le
  intro D hD
  apply Finset.le_sup'
  simp only [allowedDeletions, Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
  exact hD.trans hrs

theorem bestDeletionTime_le_free {n : ℕ} {t : Finset (Fin n) → ℝ}
    (ht : Monotone t) (r : ℕ) (v : Fin n) :
    bestDeletionTime t r ≤ freeDeletionTime t r v := by
  apply Finset.sup'_le
  intro D hD
  apply (ht (Finset.subset_insert v D)).trans
  exact Finset.le_sup' (fun E => t (insert v E)) hD

theorem freeDeletionTime_le_next {n : ℕ} (t : Finset (Fin n) → ℝ)
    (r : ℕ) (v : Fin n) :
    freeDeletionTime t r v ≤ bestDeletionTime t (r+1) := by
  apply Finset.sup'_le
  intro D hD
  apply Finset.le_sup'
  simp only [allowedDeletions, Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hD 1)

theorem freeDeletionTime_eq_at_max {n r : ℕ} (t : Finset (Fin n) → ℝ)
    (hr : 1 ≤ r) {D : Finset (Fin n)} (hD : D.card = r)
    (hmax : bestDeletionTime t r = t D) {v : Fin n} (hv : v ∈ D) :
    freeDeletionTime t (r-1) v = bestDeletionTime t r := by
  apply le_antisymm
  · simpa only [Nat.sub_add_cancel hr] using freeDeletionTime_le_next t (r-1) v
  · rw [hmax]
    have he : D.erase v ∈ allowedDeletions n (r-1) := by
      simp only [allowedDeletions, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.card_erase_of_mem hv, hD, le_refl]
    have h := Finset.le_sup' (fun E => t (insert v E)) he
    simpa only [freeDeletionTime, Finset.insert_erase hv] using h

theorem deletion_increment_rpow {n r : ℕ} {t : Finset (Fin n) → ℝ}
    (ht : Monotone t) (hr : 1 ≤ r) {p : ℝ} (hp : 0 < p) :
    (r : ℝ) * (bestDeletionTime t r - bestDeletionTime t (r-1))^p ≤
      ∑ v : Fin n, (freeDeletionTime t (r-1) v - bestDeletionTime t (r-1))^p := by
  obtain ⟨D, hD, hmax⟩ := Finset.exists_mem_eq_sup'
    (allowedDeletions_nonempty n r) t
  change bestDeletionTime t r = t D at hmax
  have hcard : D.card ≤ r := by simpa only [allowedDeletions, Finset.mem_filter,
    Finset.mem_univ, true_and] using hD
  have hnonneg (v : Fin n) :
      0 ≤ freeDeletionTime t (r-1) v - bestDeletionTime t (r-1) :=
    sub_nonneg.mpr (bestDeletionTime_le_free ht (r-1) v)
  by_cases hsmall : D.card < r
  · have he : D ∈ allowedDeletions n (r-1) := by
      simp only [allowedDeletions, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hle : bestDeletionTime t r ≤ bestDeletionTime t (r-1) := by
      rw [hmax]
      exact Finset.le_sup' t he
    have heq := le_antisymm hle (bestDeletionTime_mono t (Nat.sub_le r 1))
    rw [heq, sub_self, Real.zero_rpow hp.ne', mul_zero]
    exact Finset.sum_nonneg (fun v _ => Real.rpow_nonneg (hnonneg v) _)
  · have hcard' : D.card = r := by omega
    calc
      _ = ∑ v ∈ D, (bestDeletionTime t r - bestDeletionTime t (r-1))^p := by
        simp only [Finset.sum_const, nsmul_eq_mul, hcard']
      _ = ∑ v ∈ D, (freeDeletionTime t (r-1) v - bestDeletionTime t (r-1))^p := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [freeDeletionTime_eq_at_max t hr hcard' hmax hv]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
        (fun v _ _ => Real.rpow_nonneg (hnonneg v) _)

theorem mean_deletion_increment {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    {n r : ℕ} (t : Ω → Finset (Fin n) → ℝ) (ht : ∀ ω, Monotone (t ω))
    (hr : 1 ≤ r) {p C : ℝ} (hp : 1 ≤ p)
    (hmoment : ∀ v : Fin n, P.expect (fun ω =>
      (freeDeletionTime (t ω) (r-1) v - bestDeletionTime (t ω) (r-1))^p) ≤ C) :
    P.expect (fun ω => bestDeletionTime (t ω) r - bestDeletionTime (t ω) (r-1)) ≤
      ((n : ℝ) * C / r) ^ (1/p) := by
  let delta := fun ω => bestDeletionTime (t ω) r - bestDeletionTime (t ω) (r-1)
  have hd (ω : Ω) : 0 ≤ delta ω :=
    sub_nonneg.mpr (bestDeletionTime_mono (t ω) (Nat.sub_le r 1))
  have hpow : (r : ℝ) * P.expect (fun ω => (delta ω)^p) ≤ n*C := by
    have hi := P.expect_mono (fun ω => deletion_increment_rpow (ht ω) hr
      (show 0 < p by linarith))
    rw [FiniteLaw.expect_mul_left, FiniteLaw.expect_fintype_sum] at hi
    apply hi.trans
    have hs := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin n))) =>
      hmoment v)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hi : P.expect (fun ω => (delta ω)^p) ≤ (n : ℝ)*C/r :=
    (le_div_iff₀ hr0).mpr (by simpa only [mul_comm] using hpow)
  have hm := Real.arith_mean_le_rpow_mean Finset.univ P.weight delta
    (fun ω _ => P.nonneg ω) P.total (fun ω _ => hd ω) hp
  change P.expect delta ≤ _ at hm
  apply hm.trans
  exact Real.rpow_le_rpow (P.expect_nonneg (fun ω => Real.rpow_nonneg (hd ω) p)) hi
    (by positivity)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonKilling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem candidateAlive_le_one {n : ℕ} (U : Finset (DeletionCandidate n)) :
    candidateAlive U ≤ 1 := by unfold candidateAlive; split <;> norm_num

theorem candidateStep_alive_le {n : ℕ} [NeZero n] (k : ℕ) :
    candidateStep (n := n) k candidateAlive ≤ candidateAlive := by
  intro U
  by_cases hU : U.Nonempty
  · calc
      _ ≤ (FiniteLaw.uniform : FiniteLaw (Fin k → SignedLiteral n)).expect (fun _ => 1) :=
        FiniteLaw.expect_mono _ (fun _ => candidateAlive_le_one _)
      _ = candidateAlive U := by simp [candidateAlive, hU]
  · have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    simp [he, candidateStep, candidateAlive]

theorem batchKillProbability_mono {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) : Monotone (batchKillProbability U k) := by
  have hstep (d : ℕ) : (candidateStep k)^[d+1] candidateAlive ≤
      (candidateStep (n := n) k)^[d] candidateAlive := by
    rw [Function.iterate_succ_apply]
    exact (candidateStep_mono k).iterate d (candidateStep_alive_le k)
  have ha : Antitone (fun d => (candidateStep k)^[d] candidateAlive U) :=
    antitone_nat_of_succ_le (fun d => hstep d U)
  intro d e hde
  rw [candidateKill_iterate, candidateKill_iterate]
  linarith [ha hde]

theorem batchKillProbability_nonneg {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) : 0 ≤ batchKillProbability U k d := by
  apply FiniteLaw.expect_nonneg
  intro cs
  split <;> norm_num

theorem batchKillProbability_le_one {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) : batchKillProbability U k d ≤ 1 := by
  apply (FiniteLaw.expect_mono _ (g := fun _ => 1) ?_).trans_eq (FiniteLaw.expect_const _ _)
  intro cs
  split <;> norm_num

theorem poissonKillProbability_mono_rate {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) :
    Monotone (poissonKillProbability U k) := by
  have hi (r : ℝ≥0) : Integrable (fun d => batchKillProbability U k d)
      (poissonMeasure r) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun d => abs_le.mpr
      ⟨by linarith [batchKillProbability_nonneg U k d], batchKillProbability_le_one U k d⟩)
  intro r s hrs
  have hs : s = r + (s-r) := (add_tsub_cancel_of_le hrs).symm
  unfold poissonKillProbability
  rw [hs, ← poissonMeasure_conv_poissonMeasure, integral_conv (by
    simpa only [poissonMeasure_conv_poissonMeasure] using hi (r+(s-r)))]
  apply integral_mono (hi r)
  · apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun d => by
      simpa only [Real.norm_eq_abs] using
        (abs_integral_le_bound (μ := poissonMeasure (s-r)) (fun e => abs_le.mpr
          ⟨by linarith [batchKillProbability_nonneg U k (d+e)],
            batchKillProbability_le_one U k (d+e)⟩)))
  · intro d
    have hshift : Integrable (fun e => batchKillProbability U k (d+e))
        (poissonMeasure (s-r)) := by
      apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      exact Eventually.of_forall (fun e => abs_le.mpr
        ⟨by linarith [batchKillProbability_nonneg U k (d+e)], batchKillProbability_le_one U k (d+e)⟩)
    calc
      _ = ∫ _e : ℕ, batchKillProbability U k d ∂poissonMeasure (s-r) := by simp
      _ ≤ _ := integral_mono (integrable_const _) hshift
        (fun e => batchKillProbability_mono U k (Nat.le_add_right d e))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonKernel
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem candidateBlock_expect {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n))
    (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock r k U).expect f =
      ∫ d, (candidateStep k)^[d] f U ∂poissonMeasure r := by
  rw [candidateBlock, poissonMixture_expect]
  simp only [candidateFixedBlock_expect]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateSurvival
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem candidateAlive_mono {n : ℕ} :
    Monotone (candidateAlive (n := n)) := by
  intro U V h
  unfold candidateAlive
  split_ifs with hU hV
  · rfl
  · exact (hV (hU.mono h)).elim
  · norm_num
  · rfl

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateMasks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped NNReal Classical

theorem candidateResidual_inter {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (cs : Fin d → Fin k → SignedLiteral n) :
    candidateResidual U cs = U ∩ candidateResidual Finset.univ cs := by
  ext x
  simp only [candidateResidual, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]

theorem candidateFixedBlock_mask {n : ℕ} [NeZero n] (k d : ℕ)
    (U : Finset (DeletionCandidate n)) (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateFixedBlock k d Finset.univ).expect (fun V => f (U ∩ V)) =
      (candidateFixedBlock k d U).expect f := by
  simp only [candidateFixedBlock_expect, candidateStep_iterate]
  apply FiniteLaw.expect_congr
  intro cs
  rw [candidateResidual_inter U cs]

theorem candidateBlock_mask {n : ℕ} [NeZero n] (r : ℝ≥0) (k : ℕ)
    (U : Finset (DeletionCandidate n)) (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock r k Finset.univ).expect (fun V => f (U ∩ V)) =
      (candidateBlock r k U).expect f := by
  simp only [candidateBlock, poissonMixture_expect, candidateFixedBlock_mask]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DeletionMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory
open scoped BigOperators

theorem sum_inverse_five_sixths (r : ℕ) :
    (∑ j ∈ Finset.range r, ((j : ℝ)+1)^(-(5/6 : ℝ))) ≤
      6 * (r : ℝ)^(1/6 : ℝ) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, r = m+1 := ⟨r-1, by omega⟩
  have ha : AntitoneOn (fun x : ℝ => x^(-(5/6 : ℝ))) (Set.Icc 1 (1 + (m : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by norm_num)
  have hb := ha.sum_le_integral
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(5/6 : ℝ)))] at hb
  rw [Finset.sum_range_succ']
  have h1 : ∑ i ∈ Finset.range m, (((i+1 : ℕ) : ℝ)+1)^(-(5/6 : ℝ)) =
      ∑ i ∈ Finset.range m, (1 + ((i+1 : ℕ) : ℝ))^(-(5/6 : ℝ)) :=
    Finset.sum_congr rfl fun i _ => by rw [add_comm]
  rw [h1]
  have h2 : (-(5/6 : ℝ) + 1) = 1/6 := by norm_num
  rw [h2] at hb
  simp only [Nat.cast_add, Nat.cast_one] at hb ⊢
  have h3 : ((1:ℝ) + m)^(1/6 : ℝ) = ((m:ℝ)+1)^(1/6:ℝ) := by rw [add_comm]
  rw [h3] at hb
  simp only [Real.one_rpow, Nat.cast_zero, zero_add] at hb ⊢
  have : (1:ℝ)/(1/6) = 6 := by norm_num
  have hb' : _ := hb
  field_simp at hb'
  nlinarith [hb']

theorem finite_deletion_mean {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    {n r : ℕ} (t : Ω → Finset (Fin n) → ℝ) (ht : ∀ ω, Monotone (t ω))
    {C : ℝ} (hC : 0 ≤ C)
    (hmoment : ∀ j < r, ∀ v : Fin n, P.expect (fun ω =>
      (freeDeletionTime (t ω) j v - bestDeletionTime (t ω) j)^(6/5 : ℝ)) ≤ C) :
    P.expect (fun ω => bestDeletionTime (t ω) r) -
        P.expect (fun ω => bestDeletionTime (t ω) 0) ≤
      6 * ((n : ℝ)*C)^(5/6 : ℝ) * (r : ℝ)^(1/6 : ℝ) := by
  let A := fun j => P.expect (fun ω => bestDeletionTime (t ω) j)
  have hnc : 0 ≤ (n : ℝ)*C := mul_nonneg (Nat.cast_nonneg _) hC
  have hj (j : ℕ) (hj : j < r) :
      A (j+1) - A j ≤ ((n : ℝ)*C)^(5/6 : ℝ) *
        ((j : ℝ)+1)^(-(5/6 : ℝ)) := by
    have h := mean_deletion_increment P t ht (Nat.succ_pos j)
      (by norm_num : (1 : ℝ) ≤ 6/5) (by
        simpa only [Nat.succ_sub_one] using hmoment j hj)
    simp only [Nat.succ_sub_one, Nat.cast_succ, one_div, FiniteLaw.expect_sub] at h
    norm_num only [inv_div, div_one] at h
    apply h.trans_eq
    rw [Real.div_rpow hnc (by positivity), div_eq_mul_inv,
      ← Real.rpow_neg (by positivity)]
  change A r - A 0 ≤ _
  calc
    _ = ∑ j ∈ Finset.range r, (A (j+1)-A j) := (Finset.sum_range_sub A r).symm
    _ ≤ ∑ j ∈ Finset.range r, ((n : ℝ)*C)^(5/6 : ℝ) *
        ((j : ℝ)+1)^(-(5/6 : ℝ)) :=
      Finset.sum_le_sum (fun j hj' => hj j (Finset.mem_range.mp hj'))
    _ = ((n : ℝ)*C)^(5/6 : ℝ) *
        ∑ j ∈ Finset.range r, ((j : ℝ)+1)^(-(5/6 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ ((n : ℝ)*C)^(5/6 : ℝ) * (6*(r : ℝ)^(1/6 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_inverse_five_sixths r) (Real.rpow_nonneg hnc _)
    _ = _ := by ring

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DyadicBlocks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

theorem dyadicLevel_pos (j : ℕ) : 0 < dyadicLevel j := by
  unfold dyadicLevel
  positivity

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MaskLifetime
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators NNReal Classical

theorem maskLifetime_nonneg {n m : ℕ} (U : Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) : 0 ≤ maskLifetime m U xs := by
  induction m generalizing U with
  | zero => exact (le_rfl : (0 : ℝ) ≤ 0)
  | succ m ih => exact add_nonneg (candidateAlive_nonneg U) (ih _ _)

theorem maskLifetime_le {n m : ℕ} (U : Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) : maskLifetime m U xs ≤ m := by
  induction m generalizing U with
  | zero => simp [maskLifetime]
  | succ m ih =>
    simp only [maskLifetime, Nat.cast_add, Nat.cast_one]
    linarith [candidateAlive_le_one U, ih (U ∩ xs 0) (Fin.tail xs)]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MaskDelay
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory
open scoped BigOperators Classical NNReal

theorem maskLifetime_mono {n m : ℕ} {U V : Finset (DeletionCandidate n)}
    (hUV : U ⊆ V) (xs : Fin m → Finset (DeletionCandidate n)) :
    maskLifetime m U xs ≤ maskLifetime m V xs := by
  induction m generalizing U V with
  | zero => exact le_rfl
  | succ m ih =>
    exact add_le_add (candidateAlive_mono hUV)
      (ih (Finset.inter_subset_inter_right hUV) (Fin.tail xs))

theorem maskLifetime_empty {n m : ℕ}
    (xs : Fin m → Finset (DeletionCandidate n)) : maskLifetime m ∅ xs = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [maskLifetime, candidateAlive, ih]

theorem finite_expect_comm {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (P : FiniteLaw Ω) (Q : FiniteLaw Ξ) (f : Ω → Ξ → ℝ) :
    P.expect (fun x => Q.expect (f x)) = Q.expect (fun y => P.expect (fun x => f x y)) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DyadicMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Filter
open scoped BigOperators NNReal Topology

theorem dyadicMomentCoefficient_nonneg (j : ℕ) : 0 ≤ dyadicMomentCoefficient j := by
  unfold dyadicMomentCoefficient
  positivity [dyadicLevel_pos j]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_IncidentMasks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

theorem finiteMap_expect {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [DecidableEq Ξ] (P : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → ℝ) :
    (finiteMap P f).expect g = P.expect (fun x => g (f x)) := by
  simp only [FiniteLaw.expect, finiteMap, Finset.sum_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MaskDeletionTimes
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

theorem maskLifetime_union {n m : ℕ} (U V : Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) :
    maskLifetime m (U ∪ V) xs = max (maskLifetime m U xs) (maskLifetime m V xs) := by
  induction m generalizing U V with
  | zero => simp [maskLifetime]
  | succ m ih =>
    by_cases hU : U.Nonempty
    · by_cases hV : V.Nonempty
      · have hUV : (U ∪ V).Nonempty := hU.mono Finset.subset_union_left
        simp only [maskLifetime, candidateAlive, ite_eq_left hU, ite_eq_left hV,
          ite_eq_left hUV, Finset.union_inter_distrib_right, ih, max_add_add_left]
      · have hVe : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
        subst V
        simp only [Finset.union_empty, maskLifetime_empty, max_eq_left (maskLifetime_nonneg U xs)]
    · have hUe : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      subst U
      simp only [Finset.empty_union, maskLifetime_empty, max_eq_right (maskLifetime_nonneg V xs)]

theorem maskLifetime_biUnion {ι : Type*} [DecidableEq ι] {n m : ℕ}
    (S : Finset ι) (hS : S.Nonempty) (F : ι → Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) :
    maskLifetime m (S.biUnion F) xs = S.sup' hS (fun i => maskLifetime m (F i) xs) := by
  induction S using Finset.induction_on with
  | empty => simp at hS
  | @insert a S ha ih =>
    by_cases hne : S.Nonempty
    · rw [Finset.biUnion_insert, maskLifetime_union, ih hne, Finset.sup'_insert hne]
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst S
      simp

theorem deletionMask_mono {n : ℕ} : Monotone (deletionMask (n := n)) := by
  intro D E hDE x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.trans hDE⟩

theorem deletionBudgetMask_union (n r : ℕ) :
    (allowedDeletions n r).biUnion (deletionMask (n := n)) = deletionBudgetMask n r := by
  ext x
  simp only [Finset.mem_biUnion, deletionMask, deletionBudgetMask, allowedDeletions,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨D,hD,hx⟩
    exact (Finset.card_le_card hx).trans hD
  · intro hx
    exact ⟨deletedVariables x,hx,Finset.Subset.refl _⟩

theorem fixedMaskDeletionTime_mono {n m : ℕ}
    (xs : Fin m → Finset (DeletionCandidate n)) : Monotone (fixedMaskDeletionTime xs) := by
  intro D E hDE
  exact maskLifetime_mono (deletionMask_mono hDE) xs

theorem bestMaskDeletionTime_eq {n m : ℕ}
    (xs : Fin m → Finset (DeletionCandidate n)) (r : ℕ) :
    bestDeletionTime (fixedMaskDeletionTime xs) r = maskLifetime m (deletionBudgetMask n r) xs := by
  rw [← deletionBudgetMask_union, maskLifetime_biUnion _ (allowedDeletions_nonempty n r)]
  rfl

theorem freeMaskDeletionTime_eq {n m : ℕ}
    (xs : Fin m → Finset (DeletionCandidate n)) (r : ℕ) (v : Fin n) :
    freeDeletionTime (fixedMaskDeletionTime xs) r v = maskLifetime m (freeDeletionBudgetMask n r v) xs := by
  rw [freeDeletionBudgetMask, maskLifetime_biUnion _ (allowedDeletions_nonempty n r)]
  rfl

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RestoredCandidates
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical

theorem deletedVariables_tail_image {n : ℕ} (x : DeletionCandidate (n+1)) :
    (deletedVariables (Fin.tail x)).image Fin.succ = (deletedVariables x).erase 0 := by
  ext i
  rw [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨j,hj,rfl⟩
    refine ⟨Fin.succ_ne_zero _,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
  · rintro ⟨hi0,hi⟩
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩,rfl⟩

theorem mem_freeDeletionBudgetMask {n r : ℕ} (x : DeletionCandidate (n+1)) :
    x ∈ freeDeletionBudgetMask (n+1) r 0 ↔
      (deletedVariables (Fin.tail x)).card ≤ r := by
  simp only [freeDeletionBudgetMask, Finset.mem_biUnion, allowedDeletions, deletionMask,
    Finset.mem_filter, Finset.mem_univ, true_and]
  have hc : ((deletedVariables (Fin.tail x)).image Fin.succ).card =
      (deletedVariables (Fin.tail x)).card := Finset.card_image_of_injective _ (Fin.succ_injective n)
  constructor
  · rintro ⟨D,hD,hx⟩
    have hsub : (deletedVariables (Fin.tail x)).image Fin.succ ⊆ D := by
      rw [deletedVariables_tail_image]
      intro i hi
      obtain ⟨hi0,hi⟩ := Finset.mem_erase.mp hi
      exact (Finset.mem_insert.mp (hx hi)).resolve_left hi0
    rw [← hc]
    exact (Finset.card_le_card hsub).trans hD
  · intro hx
    refine ⟨(deletedVariables (Fin.tail x)).image Fin.succ, by simpa only [hc] using hx, ?_⟩
    intro i hi
    by_cases hi0 : i = 0
    · exact Finset.mem_insert.mpr (Or.inl hi0)
    · exact Finset.mem_insert.mpr (Or.inr (by
        rw [deletedVariables_tail_image]
        exact Finset.mem_erase.mpr ⟨hi0,hi⟩))

theorem maskLifetime_map_le {n N m : ℕ} (f : DeletionCandidate n → DeletionCandidate N)
    (U : Finset (DeletionCandidate n)) (V : Finset (DeletionCandidate N))
    (xs : Fin m → Finset (DeletionCandidate n)) (ys : Fin m → Finset (DeletionCandidate N))
    (hUV : ∀ x ∈ U, f x ∈ V)
    (hxy : ∀ j x, x ∈ xs j → f x ∈ ys j) :
    maskLifetime m U xs ≤ maskLifetime m V ys := by
  induction m generalizing U V with
  | zero => exact le_rfl
  | succ m ih =>
    apply add_le_add
    · unfold candidateAlive
      split_ifs with hU hV hV
      · exact le_rfl
      · obtain ⟨x,hx⟩ := hU
        exact False.elim (hV ⟨f x,hUV x hx⟩)
      · norm_num
      · exact le_rfl
    · exact ih (U ∩ xs 0) (V ∩ ys 0) (Fin.tail xs) (Fin.tail ys)
        (fun x hx => Finset.mem_inter.mpr
          ⟨hUV x (Finset.mem_inter.mp hx).1,hxy 0 x (Finset.mem_inter.mp hx).2⟩)
        (fun j x hx => hxy j.succ x hx)

theorem restoredMask_tail {n : ℕ} (B F T : Finset (DeletionCandidate n))
    {x : DeletionCandidate (n+1)} (hx : x ∈ restoredMask B F T) : Fin.tail x ∈ B :=
  (Finset.mem_filter.mp hx).2.1

theorem restore_none_mem {n : ℕ} (B F T : Finset (DeletionCandidate n))
    {x : DeletionCandidate n} (hx : x ∈ B) :
    restoreCandidate none x ∈ restoredMask B F T := by
  simpa [restoredMask, restoreCandidate] using hx

theorem free_restored_lifetime {n r m : ℕ}
    (base f t : Fin m → Finset (DeletionCandidate n)) :
    maskLifetime m (freeDeletionBudgetMask (n+1) r 0)
      (fun j => restoredMask (base j) (f j) (t j)) =
      maskLifetime m (deletionBudgetMask n r) base := by
  apply le_antisymm
  · apply maskLifetime_map_le (fun x => Fin.tail x)
    · intro x hx
      simpa only [deletionBudgetMask, Finset.mem_filter, Finset.mem_univ, true_and,
        mem_freeDeletionBudgetMask] using hx
    · intro j x hx
      exact restoredMask_tail _ _ _ hx
  · apply maskLifetime_map_le (restoreCandidate none)
    · intro x hx
      rw [mem_freeDeletionBudgetMask]
      simpa only [restoreCandidate, Fin.tail_cons, deletionBudgetMask,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    · intro j x hx
      exact restore_none_mem _ _ _ hx

theorem deletionBudgetMask_subset_free (n r : ℕ) (v : Fin n) :
    deletionBudgetMask n r ⊆ freeDeletionBudgetMask n r v := by
  intro x hx
  apply Finset.mem_biUnion.mpr
  refine ⟨deletedVariables x, ?_, ?_⟩
  · simpa only [allowedDeletions, deletionBudgetMask, Finset.mem_filter,
      Finset.mem_univ, true_and] using hx
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_insert _ _⟩

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ClauseRestoration
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical

theorem literalFalse_lift {n : ℕ} (x : DeletionCandidate (n+1)) (l : SignedLiteral n) :
    literalFalse x (liftLiteral l) ↔ literalFalse (Fin.tail x) l := Iff.rfl

theorem clauseMask_lift {n k : ℕ} (x : DeletionCandidate (n+1))
    (c : Fin k → SignedLiteral n) :
    x ∈ clauseMask (fun l => liftLiteral (c l)) ↔ Fin.tail x ∈ clauseMask c := by
  simp only [clauseMask, Finset.mem_filter, Finset.mem_univ, true_and, literalFalse_lift]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ClauseClasses
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open scoped Classical

theorem clauseClasses_base_card (n : ℕ) :
    Fintype.card (Triple (SignedLiteral n)) = 8*n^3 := by
  simp [Triple, SignedLiteral, Fintype.card_prod, Fintype.card_fin]
  ring

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ClassMasks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open scoped Classical

theorem classClause_base {n : ℕ} (c : Triple (SignedLiteral n)) :
    classClause (.inl c) = fun j => liftLiteral ((tripleVectorEquiv _).symm c j) := by
  funext j
  fin_cases j <;> rfl

theorem classClause_restored_base {n : ℕ} (c : Triple (SignedLiteral n)) :
    clauseMask (classClause (.inl c)) = restoredMask (classBaseMask (.inl c))
      (classIncidentMask false (.inl c)) (classIncidentMask true (.inl c)) := by
  rw [classClause_base]
  ext x
  simp only [clauseMask_lift, classBaseMask, classIncidentMask, restoredMask,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases x 0 with
  | none => simp
  | some b => cases b <;> simp

theorem classClause_restored_single {n : ℕ} (i : Fin 3) (b : Bool)
    (c d : SignedLiteral n) :
    clauseMask (classClause (.inr (.inl (i,b,c,d)))) =
      restoredMask (classBaseMask (.inr (.inl (i,b,c,d))))
        (classIncidentMask false (.inr (.inl (i,b,c,d))))
        (classIncidentMask true (.inr (.inl (i,b,c,d)))) := by
  ext x
  have hx : restoreCandidate (x 0) (Fin.tail x) = x := Fin.cons_self_tail x
  conv_lhs => rw [← hx]
  fin_cases i <;> cases b <;> rcases h0 : x 0 with _ | (_ | _)
  all_goals simp [classClause, clauseClassesEquiv, tripleClassesEquiv, joinTriple,
    tripleVectorEquiv, literalSplitEquiv, Equiv.arrowCongr, classBaseMask,
    classIncidentMask, restoredMask, clauseMask, literalFalse, restoreCandidate,
    Fin.forall_fin_succ, Fin.tail_def, h0, Bool.not_false, Bool.not_true]

theorem classClause_restored_double {n : ℕ} (i : Fin 3) (a b : Bool)
    (c : SignedLiteral n) :
    clauseMask (classClause (.inr (.inr (.inl (i,a,b,c))))) =
      restoredMask (classBaseMask (.inr (.inr (.inl (i,a,b,c)))))
        (classIncidentMask false (.inr (.inr (.inl (i,a,b,c)))))
        (classIncidentMask true (.inr (.inr (.inl (i,a,b,c))))) := by
  ext x
  have hx : restoreCandidate (x 0) (Fin.tail x) = x := Fin.cons_self_tail x
  conv_lhs => rw [← hx]
  fin_cases i <;> cases a <;> cases b <;> rcases h0 : x 0 with _ | (_ | _)
  all_goals simp [classClause, clauseClassesEquiv, tripleClassesEquiv, joinTriple,
    tripleVectorEquiv, literalSplitEquiv, Equiv.arrowCongr, classBaseMask,
    classIncidentMask, restoredMask, clauseMask, literalFalse, restoreCandidate,
    Fin.forall_fin_succ, Fin.tail_def, h0, Bool.not_false, Bool.not_true]

theorem classClause_restored_triple {n : ℕ} (a b c : Bool) :
    clauseMask (classClause (n := n) (.inr (.inr (.inr (a,b,c))))) =
      restoredMask (classBaseMask (.inr (.inr (.inr (a,b,c)))))
        (classIncidentMask false (.inr (.inr (.inr (a,b,c)))))
        (classIncidentMask true (.inr (.inr (.inr (a,b,c))))) := by
  ext x
  have hx : restoreCandidate (x 0) (Fin.tail x) = x := Fin.cons_self_tail x
  conv_lhs => rw [← hx]
  cases a <;> cases b <;> cases c <;> rcases h0 : x 0 with _ | (_ | _)
  all_goals simp [classClause, clauseClassesEquiv, tripleClassesEquiv, joinTriple,
    tripleVectorEquiv, literalSplitEquiv, Equiv.arrowCongr, classBaseMask,
    classIncidentMask, restoredMask, clauseMask, literalFalse, restoreCandidate,
    Fin.forall_fin_succ, Fin.tail_def, h0, Bool.not_false, Bool.not_true]

theorem classClause_restored {n : ℕ} (c : TripleClasses (SignedLiteral n)) :
    clauseMask (classClause c) = restoredMask (classBaseMask c)
      (classIncidentMask false c) (classIncidentMask true c) := by
  rcases c with c | (⟨i,b,c,d⟩ | (⟨i,a,b,c⟩ | ⟨a,b,c⟩))
  · exact classClause_restored_base c
  · exact classClause_restored_single i b c d
  · exact classClause_restored_double i a b c
  · exact classClause_restored_triple a b c

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ActiveClauses
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open scoped Classical

theorem activeClass_injective (n : ℕ) : Function.Injective (activeClass (n := n)) := by
  intro c d h
  rcases c with c | ⟨b,c | (c | c)⟩ <;>
    rcases d with d | ⟨a,d | (d | d)⟩ <;>
    simp_all [activeClass]
  all_goals exact Prod.ext h.1 h.2.2

theorem restoredMask_mono {n : ℕ}
    {B F T B' F' T' : Finset (DeletionCandidate n)}
    (hB : B ⊆ B') (hF : F ⊆ F') (hT : T ⊆ T') :
    restoredMask B F T ⊆ restoredMask B' F' T' := by
  intro x hx
  obtain ⟨hb,hx⟩ := (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,hB hb,?_⟩
  rcases h0 : x 0 with _ | (_ | _)
  · trivial
  · exact hF (by simpa only [h0] using hx)
  · exact hT (by simpa only [h0] using hx)

theorem strongerClassMask_subset {n : ℕ} (c : ActiveClause n) :
    strongerClassMask c ⊆ clauseMask (classClause (activeClass c)) := by
  rw [classClause_restored]
  rcases c with c | ⟨b,c | (⟨i,c⟩ | u)⟩
  · exact Finset.Subset.refl _
  · rcases c with ⟨i,c,d⟩
    cases b <;> exact Finset.Subset.refl _
  · cases b <;>
      simp only [strongerClassMask, activeClass, classBaseMask, classIncidentMask,
        Bool.false_eq_true, Bool.true_eq_false, or_self, ite_true, ite_false, incidentMask]
    all_goals apply restoredMask_mono <;> first | exact Finset.Subset.refl _ | exact Finset.empty_subset _
  · cases b <;> exact Finset.Subset.refl _

theorem inactiveClass_trivial {n : ℕ} (c : TripleClasses (SignedLiteral n))
    (hc : c ∉ Set.range (activeClass (n := n))) :
    clauseMask (classClause c) = Finset.univ := by
  rcases c with c | (⟨i,b,c,d⟩ | (⟨i,a,b,c⟩ | ⟨a,b,c⟩))
  · exact False.elim (hc ⟨.inl c,rfl⟩)
  · exact False.elim (hc ⟨.inr (b,.inl (i,c,d)),rfl⟩)
  · by_cases hab : a = b
    · subst b
      exact False.elim (hc ⟨.inr (a,.inr (.inl (i,c))),rfl⟩)
    · rw [classClause_restored_double]
      clear hc
      cases a <;> cases b <;> try contradiction
      all_goals
        ext x
        rcases h0 : x 0 with _ | (_ | _)
        all_goals simp [classBaseMask, classIncidentMask, restoredMask, h0]
  · by_cases habc : a = b ∧ b = c
    · rcases habc with ⟨hab,hbc⟩
      subst b
      subst c
      exact False.elim (hc ⟨.inr (a,.inr (.inr ())),rfl⟩)
    · rw [classClause_restored_triple]
      clear hc
      cases a <;> cases b <;> cases c <;> try simp_all
      all_goals
        ext x
        rcases h0 : x 0 with _ | (_ | _)
        all_goals simp [classBaseMask, classIncidentMask, restoredMask, h0]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonMarks
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem uniform_poisson_marks {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    (r : ℝ≥0) (V : A → E) :
    compoundPoisson r (Measure.map V (finiteUniform A)) =
      Measure.map (fun x : A → E => ∑ a, x a)
        (Measure.pi (fun a => compoundPoisson (r / Fintype.card A) (Measure.dirac (V a)))) := by
  have hV : Measurable V := measurable_of_countable V
  let : IsProbabilityMeasure (Measure.map V (finiteUniform A)) :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr inferInstance
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_compoundPoisson, charFunDual_map_sum_pi_eq_prod]
  simp only [Finset.prod_apply]
  simp_rw [charFunDual_compoundPoisson, charFunDual_apply, integral_dirac]
  rw [← Complex.exp_sum]
  congr 1
  rw [integral_map hV.aemeasurable (by fun_prop), integral_finiteUniform]
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [NNReal.coe_div, NNReal.coe_natCast, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.real_smul, Complex.ofReal_inv]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  simp only [mul_comm Complex.I]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonCounts
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

theorem compoundPoisson_dirac_nsmul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (r : ℝ≥0) (v : E) :
    compoundPoisson r (Measure.dirac v) =
      Measure.map (fun m : ℕ => m • v) (poissonMeasure r) := by
  rw [compoundPoisson, poissonMeasure,
    Measure.map_sum (measurable_of_countable _).aemeasurable]
  congr 1
  funext m
  rw [Measure.map_smul,
    Measure.map_dirac' (measurable_of_countable _)]
  congr 1
  have ha : ∀ᵐ x ∂Measure.pi (fun _ : Fin m => Measure.dirac v), ∀ i, x i = v :=
    Filter.eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin m => Measure.dirac v) (i := i)).eventually
        (show ∀ᵐ x ∂Measure.dirac v, x = v from by simp))
  rw [Measure.map_congr (ha.mono (fun x hx =>
    show (∑ i, x i) = m • v by simp only [hx, Finset.sum_const, Finset.card_univ, Fintype.card_fin]))]
  simp

theorem uniform_poisson_weighted_counts {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E] (r : ℝ≥0) (V : A → E) :
    compoundPoisson r (Measure.map V (finiteUniform A)) =
      Measure.map (fun counts : A → ℕ => ∑ a, counts a • V a)
        (Measure.pi (fun _ : A => poissonMeasure (r / Fintype.card A))) := by
  rw [uniform_poisson_marks]
  simp_rw [compoundPoisson_dirac_nsmul]
  rw [← Measure.pi_map_pi (μ := fun _ : A => poissonMeasure (r / Fintype.card A))
    (f := fun a (m : ℕ) => m • V a) (fun a =>
      (measurable_of_countable (fun m : ℕ => m • V a)).aemeasurable)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_FinitePushforward
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

theorem finitePushforward_expect {X Y : Type*} [MeasurableSpace X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → Y) (hg : Measurable g) (f : Y → ℝ) :
    (finitePushforward μ g hg).expect f = ∫ x, f (g x) ∂μ := by
  simp only [FiniteLaw.expect, finitePushforward]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun y _ => (finite_indicator_integrable μ g hg y).mul_const (f y))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp

theorem bounded_finite_observable {X Y : Type*} [MeasurableSpace X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → Y) (hg : Measurable g) (f : Y → ℝ) :
    Integrable (fun x => f (g x)) μ := by
  apply Integrable.of_bound ((measurable_of_countable f).comp hg).aestronglyMeasurable
    (∑ y, |f y|)
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun y _ => abs_nonneg (f y)) (Finset.mem_univ (g x))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonMaskCounts
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

theorem zeroMask_measurable {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] : Measurable (zeroMask (X := X)) := by
  apply measurable_finset_iff.mpr
  intro x
  simp only [zeroMask, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (measurable_pi_apply x).eq_const 0

theorem zeroMask_sum_defect {A X : Type*} [Fintype A] [Fintype X]
    (mask : A → Finset X) (counts : A → ℕ) :
    zeroMask (∑ a, counts a • maskDefect mask a) = countsMask mask counts := by
  ext x
  simp only [zeroMask, countsMask, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.sum_apply, nsmul_eq_mul]
  change (∑ a, (counts a : ℝ)*(if x ∈ mask a then 0 else 1)) = 0 ↔
    ∀ a, counts a = 0 ∨ x ∈ mask a
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by split_ifs <;> positivity)]
  simp only [Finset.mem_univ, true_implies]
  apply forall_congr'
  intro a
  by_cases hx : x ∈ mask a <;> simp [hx]

theorem zeroMask_sum_marks {A X : Type*} [Fintype X] (mask : A → Finset X)
    {d : ℕ} (as : Fin d → A) :
    zeroMask (∑ j, maskDefect mask (as j)) =
      Finset.univ.filter (fun x => ∀ j, x ∈ mask (as j)) := by
  ext x
  simp only [zeroMask, Finset.mem_filter, Finset.mem_univ, true_and, Finset.sum_apply,
    maskDefect]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)]
  simp

theorem compoundPoisson_uniform_integral {A E : Type} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    (r : ℝ≥0) (V : A → E) (f : E → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) :
    (∫ z, f z ∂compoundPoisson r (Measure.map V (finiteUniform A))) =
      ∫ d : ℕ, (FiniteLaw.uniform : FiniteLaw (Fin d → A)).expect
        (fun as => f (∑ j, V (as j))) ∂poissonMeasure r := by
  have hV : Measurable V := measurable_of_countable V
  let ν := Measure.map V (finiteUniform A)
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr inferInstance
  have hi : Integrable f (compoundPoisson r ν) :=
    Integrable.of_bound hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hb z))
  rw [compoundPoisson, integral_sum_measure hi, integral_poissonMeasure]
  apply tsum_congr
  intro d
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    integral_map (by fun_prop) hf.aestronglyMeasurable]
  change _ • (∫ z : Fin d → E, f (∑ j, z j)
    ∂Measure.pi (fun _ => Measure.map V (finiteUniform A))) = _
  rw [← Measure.pi_map_pi (μ := fun _ : Fin d => finiteUniform A)
    (f := fun _ a => V a) (fun _ => hV.aemeasurable),
    integral_map (φ := fun x : Fin d → A => fun i => V (x i))
      (f := fun z : Fin d → E => f (∑ j, z j))
      (Measurable.of_eval (fun i => hV.comp (measurable_pi_apply i))).aemeasurable
      (hf.comp (by fun_prop)).aestronglyMeasurable,
    finiteUniform_pi, integral_finiteUniform]
  simp only [FiniteLaw.expect, FiniteLaw.uniform, smul_eq_mul, ← Finset.mul_sum]

theorem markedMaskLaw_counts {A X : Type} [Fintype A] [Nonempty A] [Fintype X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (r : ℝ≥0) (mask : A → Finset X) (f : Finset X → ℝ) :
    (markedMaskLaw r mask).expect f =
      ∫ counts : A → ℕ, f (countsMask mask counts)
        ∂Measure.pi (fun _ : A => poissonMeasure (r / Fintype.card A)) := by
  have hg : Measurable (fun z : X → ℝ => f (zeroMask z)) :=
    (measurable_of_countable f).comp zeroMask_measurable
  have hb (z : X → ℝ) : |f (zeroMask z)| ≤ ∑ U : Finset X, |f U| :=
    Finset.single_le_sum (fun U _ => abs_nonneg (f U)) (Finset.mem_univ _)
  have he := compoundPoisson_uniform_integral r (maskDefect mask)
    (fun z => f (zeroMask z)) hg _ hb
  simp only [zeroMask_sum_marks] at he
  rw [uniform_poisson_weighted_counts, integral_map
    (measurable_of_countable (fun counts : A → ℕ => ∑ a, counts a • maskDefect mask a)).aemeasurable
    hg.aestronglyMeasurable] at he
  simp only [zeroMask_sum_defect] at he
  rw [markedMaskLaw, poissonMixture_expect]
  simp only [finiteMap_expect]
  exact he.symm

theorem candidateBlock_counts {n : ℕ} [NeZero n] (r : ℝ≥0) (k : ℕ)
    (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock r k (Finset.univ : Finset (DeletionCandidate n))).expect f =
      ∫ counts : (Fin k → SignedLiteral n) → ℕ,
        f (countsMask clauseMask counts)
        ∂Measure.pi (fun _ : Fin k → SignedLiteral n =>
          poissonMeasure (r / Fintype.card (Fin k → SignedLiteral n))) := by
  classical
  let : MeasurableSpace (DeletionCandidate n) := ⊤
  let : MeasurableSingletonClass (DeletionCandidate n) := ⟨fun _ => trivial⟩
  rw [← markedMaskLaw_counts r (clauseMask (n := n) (k := k)) f,
    markedMaskLaw, poissonMixture_expect, candidateBlock_expect]
  apply integral_congr_ae
  filter_upwards [] with d
  rw [candidateStep_iterate]
  simp only [finiteMap, FiniteLaw.expect, Finset.sum_mul, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cs _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 2
  ext x
  simp only [candidateResidual, clauseMask, Finset.mem_filter, Finset.mem_univ, true_and]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ActiveMaskCounts
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open scoped Classical

theorem countsMask_mono {A X : Type*} [Fintype A] [Fintype X]
    {f g : A → Finset X} (h : ∀ a, f a ⊆ g a) (c : A → ℕ) :
    countsMask f c ⊆ countsMask g c := by
  intro x hx
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro a
  exact ((Finset.mem_filter.mp hx).2 a).imp_right (fun hx => h a hx)

theorem countsMask_equiv {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
    (e : A ≃ B) (f : B → Finset X) (c : A → ℕ) :
    countsMask (f ∘ e) c = countsMask f (c ∘ e.symm) := by
  ext x
  simp only [countsMask, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_def]
  constructor
  · intro h b
    simpa only [Equiv.apply_symm_apply] using h (e.symm b)
  · intro h a
    simpa only [Equiv.symm_apply_apply] using h (e a)

theorem countsMask_active {n : ℕ} (c : TripleClasses (SignedLiteral n) → ℕ) :
    countsMask (fun a => clauseMask (classClause (activeClass a))) (c ∘ activeClass) =
      countsMask (fun a => clauseMask (classClause a)) c := by
  ext x
  simp only [countsMask, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_def]
  constructor
  · intro h a
    by_cases ha : a ∈ Set.range (activeClass (n := n))
    · obtain ⟨b,rfl⟩ := ha
      exact h b
    · exact Or.inr (by rw [inactiveClass_trivial a ha]; exact Finset.mem_univ _)
  · intro h a
    exact h (activeClass a)

theorem countsMask_stronger {n : ℕ} (c : ActiveClause n → ℕ) :
    countsMask strongerClassMask c =
      restoredMask
        (countsMask (fun a => clauseMask ((tripleVectorEquiv _).symm a)) (fun a => c (.inl a)))
        (countsMask incidentMask (fun a => c (.inr (true,a))))
        (countsMask incidentMask (fun a => c (.inr (false,a)))) := by
  ext x
  rcases h0 : x 0 with _ | (_ | _)
  all_goals
    simp [countsMask, strongerClassMask, restoredMask, Sum.forall, Prod.forall,
      Bool.forall_bool, h0]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_FiniteProductPushforward
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory
open scoped BigOperators Classical

theorem finitePushforward_pi {I : Type*} [Fintype I] [DecidableEq I]
    {X Y : I → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, Fintype (Y i)]
    [∀ i, MeasurableSpace (Y i)] [∀ i, MeasurableSingletonClass (Y i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (g : ∀ i, X i → Y i) (hg : ∀ i, Measurable (g i)) :
    finitePushforward (Measure.pi μ) (fun x i => g i (x i))
        (Measurable.of_eval (fun i => (hg i).comp (measurable_pi_apply i))) =
      FiniteLaw.pi (fun i => finitePushforward (μ i) (g i) (hg i)) := by
  classical
  let : DecidableEq ((i : I) → Y i) := Classical.decEq _
  apply FiniteLaw.weights_ext
  intro y
  simp only [finitePushforward, FiniteLaw.pi]
  have he (x : ∀ i, X i) :
      (if (fun i => g i (x i)) = y then (1 : ℝ) else 0) =
        ∏ i, if g i (x i) = y i then (1 : ℝ) else 0 := by
    by_cases h : (fun i => g i (x i)) = y
    · have hh (i : I) := congrFun h i
      simp [hh]
    · rw [ite_eq_right h]
      obtain ⟨i,hi⟩ := Function.ne_iff.mp h
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm
  exact (integral_congr_ae (ae_of_all (Measure.pi μ) he)).trans
    (integral_fintype_prod_eq_prod (μ := μ) (fun i x => if g i x = y i then (1 : ℝ) else 0))

theorem finiteLaw_eq_of_expect {Y : Type*} [Fintype Y] (P Q : FiniteLaw Y)
    (h : ∀ f, P.expect f = Q.expect f) : P = Q := by
  apply FiniteLaw.weights_ext
  intro y
  simpa only [FiniteLaw.expect, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using h (fun x => if x = y then 1 else 0)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonCountProducts
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

theorem poissonCountLaw_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (r : ℝ≥0) (f : (B → ℕ) → ℝ) :
    (∫ c, f (fun b => c (e.symm b)) ∂poissonCountLaw A r) =
      ∫ c, f c ∂poissonCountLaw B r := by
  have hp (c : A → ℕ) : (MeasurableEquiv.piCongrLeft (fun _ : B => ℕ) e) c =
      fun b => c (e.symm b) := by
    funext b
    change (Equiv.piCongrLeft (fun _ : B => ℕ) e) c b = _
    rw [Equiv.piCongrLeft_apply]
    simp
  simpa only [poissonCountLaw, hp] using
    (measurePreserving_piCongrLeft (fun _ : B => poissonMeasure r) e).integral_comp' f

theorem poissonCountLaw_sum {A B : Type*} [Fintype A] [Fintype B]
    (r : ℝ≥0) (f : (A ⊕ B → ℕ) → ℝ) (C : ℝ) (hC : ∀ c, |f c| ≤ C) :
    (∫ c, f c ∂poissonCountLaw (A ⊕ B) r) =
      ∫ a, ∫ b, f (Sum.elim a b) ∂poissonCountLaw B r ∂poissonCountLaw A r := by
  have he := (measurePreserving_sumPiEquivProdPi_symm
    (fun _ : A ⊕ B => poissonMeasure r)).integral_comp' f
  unfold poissonCountLaw
  rw [← he]
  change (∫ p : (A → ℕ) × (B → ℕ), f (Sum.elim p.1 p.2)
    ∂(poissonCountLaw A r).prod (poissonCountLaw B r)) = _
  apply integral_prod
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
  filter_upwards [] with p
  simpa only [Real.norm_eq_abs] using hC (Sum.elim p.1 p.2)

theorem poisson_zero_eq_dirac : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton]
  cases n <;> simp

theorem poissonCountLaw_hasLaw_sum {A : Type*} [Fintype A]
    (r : A → ℝ≥0) :
    HasLaw (fun c : A → ℕ => ∑ a, c a) (poissonMeasure (∑ a, r a))
      (Measure.pi (fun a => poissonMeasure (r a))) := by
  let μ := Measure.pi (fun a => poissonMeasure (r a))
  have hi : iIndepFun (fun a (c : A → ℕ) => c a) μ :=
    iIndepFun_pi (fun a => measurable_id.aemeasurable)
  have hcoord (a : A) : HasLaw (fun c : A → ℕ => c a) (poissonMeasure (r a)) μ :=
    ⟨(measurable_pi_apply a).aemeasurable, (measurePreserving_eval _ a).map_eq⟩
  have hs (S : Finset A) : HasLaw (fun c : A → ℕ => ∑ a ∈ S, c a)
      (poissonMeasure (∑ a ∈ S, r a)) μ := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, poisson_zero_eq_dirac]
      exact ⟨measurable_const.aemeasurable, by simp⟩
    | @insert a S ha ih =>
      have hind := (hi.indepFun_finsetSum_of_notMem (fun a => measurable_pi_apply a) ha).symm
      have he : (∑ j ∈ S, fun c : A → ℕ => c j) = (fun c => ∑ j ∈ S, c j) := by
        funext c
        simp only [Finset.sum_apply]
      rw [he] at hind
      have h := hind.hasLaw_add_poissonMeasure (hcoord a) ih
      have hf : ((fun c : A → ℕ => c a) + (fun c => ∑ j ∈ S, c j)) =
          (fun c => c a + ∑ j ∈ S, c j) := rfl
      rw [hf] at h
      simpa only [Finset.sum_insert ha] using h
  exact hs Finset.univ

theorem poissonCountLaw_embedding {A B : Type*} [Fintype A] [Fintype B]
    (e : B → A) (he : Function.Injective e) (r : ℝ≥0) :
    Measure.map (fun c : A → ℕ => c ∘ e) (poissonCountLaw A r) =
      poissonCountLaw B r := by
  have hi : iIndepFun (fun a (c : A → ℕ) => c a) (poissonCountLaw A r) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have h := (hi.precomp he).map_fun_eq_pi_map
    (fun b => (measurable_pi_apply (e b)).aemeasurable)
  simpa only [Function.comp_def, poissonCountLaw,
    (measurePreserving_eval (fun _ : A => poissonMeasure r) _).map_eq] using h

theorem poissonCountLaw_embedding_integral {A B : Type*} [Fintype A] [Fintype B]
    (e : B → A) (he : Function.Injective e) (r : ℝ≥0) (f : (B → ℕ) → ℝ) :
    (∫ c, f (c ∘ e) ∂poissonCountLaw A r) = ∫ c, f c ∂poissonCountLaw B r := by
  rw [← poissonCountLaw_embedding e he r]
  exact (integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable).symm

theorem poissonCountLaw_row_sums {A B : Type*} [Fintype A] [Fintype B]
    (r : ℝ≥0) :
    Measure.map (fun c : A → B → ℕ => fun a => ∑ b, c a b)
      (Measure.pi (fun _ : A => poissonCountLaw B r)) =
      poissonCountLaw A (Fintype.card B * r) := by
  rw [Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable)]
  congr 1
  funext a
  simpa only [poissonCountLaw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    (poissonCountLaw_hasLaw_sum (fun _ : B => r)).map_eq

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_UniformDelayConstant
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators NNReal

theorem deletionMomentConstant_nonneg : 0 ≤ deletionMomentConstant := by
  have hs : 0 ≤ ∑' j, dyadicMomentCoefficient j :=
    tsum_nonneg (fun j => dyadicMomentCoefficient_nonneg j)
  unfold deletionMomentConstant
  positivity

theorem capped_incident_error {n : ℕ} (hn : 0 < n) :
    ((60 : ℝ)/(n : ℝ))^2*((20*n : ℕ) : ℝ)^(6/5 : ℝ) ≤ (1200 : ℝ)^2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : (1 : ℝ) ≤ ((20*n : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 20*n by omega)
  have hp : ((20*n : ℕ) : ℝ)^(6/5 : ℝ) ≤ ((20*n : ℕ) : ℝ)^2 := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hM
      (by norm_num : (6/5 : ℝ) ≤ (2 : ℕ))
  calc
    _ ≤ ((60 : ℝ)/(n : ℝ))^2*((20*n : ℕ) : ℝ)^2 :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ = _ := by
      push_cast
      field_simp
      ring

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RestoredProcessMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical NNReal

theorem mem_maskRun {n m : ℕ} (U : Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) (x : DeletionCandidate n) :
    x ∈ maskRun m U xs ↔ x ∈ U ∧ ∀ j, x ∈ xs j := by
  induction m generalizing U with
  | zero => simp [maskRun]
  | succ m ih =>
    simp only [maskRun, ih, Finset.mem_inter, Fin.forall_fin_succ, Fin.tail_def, and_assoc]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonGrid
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

theorem poissonCountLaw_uncurry {A B : Type*} [Fintype A] [Fintype B] (r : ℝ≥0) :
    Measure.map (fun c : A → B → ℕ => fun p : A × B => c p.1 p.2)
      (Measure.pi (fun _ : A => poissonCountLaw B r)) = poissonCountLaw (A × B) r := by
  apply Measure.ext_of_singleton
  intro c
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton c)]
  have he : (fun x : A → B → ℕ => fun p : A × B => x p.1 p.2) ⁻¹' {c} =
      {fun a b => c (a,b)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Prod.forall]
  rw [he]
  simp only [poissonCountLaw, Measure.pi_singleton, Fintype.prod_prod_type]

theorem poissonCountLaw_uncurry_integral {A B : Type*} [Fintype A] [Fintype B]
    (r : ℝ≥0) (f : (A × B → ℕ) → ℝ) :
    (∫ c : A → B → ℕ, f (fun p => c p.1 p.2)
      ∂Measure.pi (fun _ : A => poissonCountLaw B r)) =
      ∫ c, f c ∂poissonCountLaw (A × B) r := by
  rw [← poissonCountLaw_uncurry r]
  exact (integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable).symm

theorem countsMask_sum {A I X : Type*} [Fintype A] [Fintype I] [Fintype X]
    (mask : A → Finset X) (c : I → A → ℕ) (x : X) :
    (∀ i, x ∈ countsMask mask (c i)) ↔
      x ∈ countsMask mask (fun a => ∑ i, c i a) := by
  simp only [countsMask, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h a
    by_cases hx : x ∈ mask a
    · exact Or.inr hx
    · left
      apply Finset.sum_eq_zero
      intro i _
      exact (h i a).resolve_right hx
  · intro h i a
    rcases h a with hz | hx
    · left
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le (c j a))).mp hz i
        (Finset.mem_univ i)
    · exact Or.inr hx

theorem frontload_countsMask {A : Type*} [Fintype A] {n M : ℕ}
    (mask : A → Finset (DeletionCandidate n)) (c : Fin M → A → ℕ) :
    frontloadMask (fun j => countsMask mask (c j)) =
      countsMask mask (fun a => ∑ j, c j a) := by
  ext x
  rw [frontloadMask, mem_maskRun]
  simp only [Finset.mem_univ, true_and]
  exact countsMask_sum mask c x

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ClauseProcess
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

theorem countsMask_restored {A : Type*} [Fintype A] {n : ℕ}
    (B F T : A → Finset (DeletionCandidate n)) (c : A → ℕ) :
    countsMask (fun a => restoredMask (B a) (F a) (T a)) c =
      restoredMask (countsMask B c) (countsMask F c) (countsMask T c) := by
  ext x
  simp only [countsMask, restoredMask, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases x 0 with _ | (_ | _)
  all_goals simp only [and_true, or_and_left, forall_and]

theorem gridMaskLaw_expect {A : Type*} [Fintype A] {n M : ℕ}
    (r : ℝ≥0) (mask : A → Finset (DeletionCandidate n))
    (f : (Fin M → Finset (DeletionCandidate n)) → ℝ) :
    (gridMaskLaw M r mask).expect f =
      ∫ c, f (maskGrid mask c) ∂poissonCountLaw (A × Fin M) r :=
  finitePushforward_expect _ _ _ _

theorem gridMaskLaw_frontload {A : Type*} [Fintype A] {n M : ℕ}
    (r : ℝ≥0) (mask : A → Finset (DeletionCandidate n))
    (f : Finset (DeletionCandidate n) → ℝ) :
    (gridMaskLaw M r mask).expect (fun xs => f (frontloadMask xs)) =
      ∫ c, f (countsMask mask c) ∂poissonCountLaw A (M*r) := by
  rw [gridMaskLaw_expect]
  have hfront (c : A × Fin M → ℕ) : frontloadMask (maskGrid mask c) =
      countsMask mask (fun a => ∑ j, c (a,j)) :=
    frontload_countsMask mask (fun j a => c (a,j))
  simp only [hfront]
  rw [← poissonCountLaw_uncurry_integral]
  have hh := poissonCountLaw_row_sums (A := A) (B := Fin M) r
  have h := integral_map (φ := fun c : A → Fin M → ℕ => fun a => ∑ j, c a j)
    (μ := Measure.pi (fun _ : A => poissonCountLaw (Fin M) r))
    (f := fun c => f (countsMask mask c))
    (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable
  rw [hh] at h
  simpa only [Fintype.card_fin] using h.symm

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_GridBlockLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

theorem gridMaskLaw_pi_of_expect {A : Type*} [Fintype A] {n M : ℕ}
    (r : ℝ≥0) (mask : A → Finset (DeletionCandidate n))
    (Q : FiniteLaw (Finset (DeletionCandidate n)))
    (hQ : ∀ f, Q.expect f = ∫ c, f (countsMask mask c) ∂poissonCountLaw A r) :
    gridMaskLaw M r mask = FiniteLaw.pi (fun _ : Fin M => Q) := by
  classical
  let μ := poissonCountLaw A r
  have hsingle : finitePushforward μ (countsMask mask) (measurable_of_countable _) = Q := by
    apply finiteLaw_eq_of_expect
    intro f
    rw [finitePushforward_expect]
    exact (hQ f).symm
  apply finiteLaw_eq_of_expect
  intro f
  rw [gridMaskLaw_expect]
  have htranspose := poissonCountLaw_equiv (Equiv.prodComm (Fin M) A) r
    (fun c => f (maskGrid mask c))
  rw [← htranspose, ← poissonCountLaw_uncurry_integral]
  change (∫ c : Fin M → A → ℕ, f (fun j => countsMask mask (c j))
    ∂Measure.pi (fun _ : Fin M => μ)) = _
  rw [← finitePushforward_expect (Measure.pi (fun _ : Fin M => μ))
    (fun c j => countsMask mask (c j))
    (Measurable.of_eval (fun j => (measurable_of_countable (countsMask mask)).comp
      (measurable_pi_apply j))) f,
    finitePushforward_pi _ _ (fun _ => measurable_of_countable _)]
  simp only [hsingle]

theorem gridMaskLaw_equiv {A B : Type} [Fintype A] [Fintype B] {n M : ℕ}
    (e : A ≃ B) (r : ℝ≥0) (mask : B → Finset (DeletionCandidate n)) :
    gridMaskLaw M r (mask ∘ e) = gridMaskLaw M r mask := by
  apply finiteLaw_eq_of_expect
  intro f
  simp only [gridMaskLaw_expect]
  have he (c : A × Fin M → ℕ) :
      maskGrid (mask ∘ e) c = maskGrid mask (c ∘ (e.prodCongr (Equiv.refl (Fin M))).symm) := by
    funext j
    exact countsMask_equiv e mask (fun a => c (a,j))
  simp only [he]
  simpa only [Function.comp_def] using
    poissonCountLaw_equiv (e.prodCongr (Equiv.refl (Fin M))) r (fun c => f (maskGrid mask c))

theorem gridMaskLaw_clauses {n : ℕ} [NeZero n] (M k : ℕ) (r : ℝ≥0) :
    gridMaskLaw M r (clauseMask (n := n) (k := k)) =
      FiniteLaw.pi (fun _ : Fin M => candidateBlock
        (r*Fintype.card (Fin k → SignedLiteral n)) k Finset.univ) := by
  apply gridMaskLaw_pi_of_expect
  intro f
  rw [candidateBlock_counts]
  simp only [mul_div_cancel_right₀ _ (show
    (Fintype.card (Fin k → SignedLiteral n) : ℝ≥0) ≠ 0 by
      exact_mod_cast Fintype.card_ne_zero)]
  rfl

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonMaskAggregation
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

theorem countsMask_product {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
    (mask : A → Finset X) (c : A × B → ℕ) :
    countsMask (fun p : A × B => mask p.1) c =
      countsMask mask (fun a => ∑ b, c (a,b)) := by
  ext x
  simp only [countsMask, Finset.mem_filter, Finset.mem_univ, true_and, Prod.forall]
  constructor
  · intro h a
    by_cases hx : x ∈ mask a
    · exact Or.inr hx
    · left
      exact Finset.sum_eq_zero (fun b _ => (h a b).resolve_right hx)
  · intro h a b
    rcases h a with hz | hx
    · left
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le (c (a,j)))).mp hz b
        (Finset.mem_univ b)
    · exact Or.inr hx

theorem poissonCountLaw_redundant_mask {A B X : Type*}
    [Fintype A] [Fintype B] [Fintype X] (r : ℝ≥0)
    (mask : A → Finset X) (f : Finset X → ℝ) :
    (∫ c, f (countsMask (fun p : A × B => mask p.1) c)
      ∂poissonCountLaw (A × B) r) =
      ∫ c, f (countsMask mask c) ∂poissonCountLaw A (Fintype.card B*r) := by
  rw [← poissonCountLaw_uncurry_integral]
  simp only [countsMask_product]
  rw [← poissonCountLaw_row_sums (A := A) (B := B) r,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_IncidentObstruction
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

theorem singleIncident_law {n : ℕ} [NeZero n] (r : ℝ≥0)
    (f : Finset (DeletionCandidate n) → ℝ) :
    (∫ c, f (countsMask singleIncidentMask c) ∂poissonCountLaw (SingleIncident n) r) =
      (candidateBlock (3*r*Fintype.card (Fin 2 → SignedLiteral n)) 2 Finset.univ).expect f := by
  have he : singleIncidentMask (n := n) =
      (fun p : (Fin 2 → SignedLiteral n) × Fin 3 => clauseMask p.1) ∘ singleIncidentEquiv n := rfl
  rw [he]
  simp_rw [countsMask_equiv]
  rw [show (∫ c, f (countsMask (fun p : (Fin 2 → SignedLiteral n) × Fin 3 => clauseMask p.1)
      (c ∘ (singleIncidentEquiv n).symm)) ∂poissonCountLaw (SingleIncident n) r) =
      ∫ c, f (countsMask (fun p : (Fin 2 → SignedLiteral n) × Fin 3 => clauseMask p.1) c)
        ∂poissonCountLaw ((Fin 2 → SignedLiteral n) × Fin 3) r from by
      simpa only [Function.comp_def] using poissonCountLaw_equiv (singleIncidentEquiv n) r
        (fun c => f (countsMask (fun p : (Fin 2 → SignedLiteral n) × Fin 3 => clauseMask p.1) c)),
    poissonCountLaw_redundant_mask]
  rw [candidateBlock_counts]
  congr 2
  simp only [Fintype.card_fin, mul_div_cancel_right₀ _ (show
    (Fintype.card (Fin 2 → SignedLiteral n) : ℝ≥0) ≠ 0 by
      exact_mod_cast Fintype.card_ne_zero)]
  norm_num

theorem incident_killing_pointwise {n : ℕ} (U : Finset (DeletionCandidate n))
    (c : IncidentClass n → ℕ) :
    (if U ∩ countsMask incidentMask c = ∅ then (1 : ℝ) else 0) ≤
      (if U ∩ countsMask singleIncidentMask (fun a => c (.inl a)) = ∅ then 1 else 0) +
      (∑ b : BadIncident n, c (.inr b) : ℕ) := by
  by_cases hz : ∑ b : BadIncident n, c (.inr b) = 0
  · have hb (b : BadIncident n) : c (.inr b) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le (c (.inr j)))).mp hz b
        (Finset.mem_univ b)
    have hm : countsMask incidentMask c =
        countsMask singleIncidentMask (fun a => c (.inl a)) := by
      ext x
      simp [countsMask, incidentMask, singleIncidentMask, Sum.forall, hb]
    rw [hm,hz,Nat.cast_zero,add_zero]
  · have hpos : (1 : ℝ) ≤ (∑ b : BadIncident n, c (.inr b) : ℕ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    split_ifs <;> linarith

theorem incident_killing_bound {n : ℕ} [NeZero n] (r : ℝ≥0)
    (U : Finset (DeletionCandidate n)) :
    (∫ c, if U ∩ countsMask incidentMask c = ∅ then (1 : ℝ) else 0
      ∂poissonCountLaw (IncidentClass n) r) ≤
      poissonKillProbability U 2 (3*r*Fintype.card (Fin 2 → SignedLiteral n)) +
      Fintype.card (BadIncident n)*(r : ℝ) := by
  let μ := poissonCountLaw (IncidentClass n) r
  let g := fun c : IncidentClass n → ℕ =>
    if U ∩ countsMask singleIncidentMask (fun a => c (.inl a)) = ∅ then (1 : ℝ) else 0
  let b := fun c : IncidentClass n → ℕ => ((∑ a : BadIncident n, c (.inr a) : ℕ) : ℝ)
  have hg : Integrable g μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    filter_upwards [] with c
    dsimp only [g]
    split_ifs <;> norm_num
  have hres : HasLaw (fun c : IncidentClass n → ℕ => fun a : BadIncident n => c (.inr a))
      (poissonCountLaw (BadIncident n) r) μ :=
    ⟨(measurable_of_countable _).aemeasurable,
      poissonCountLaw_embedding Sum.inr Sum.inr_injective r⟩
  have hsum := (poissonCountLaw_hasLaw_sum (fun _ : BadIncident n => r)).comp hres
  have hb : Integrable b μ := by
    have h0 : Integrable (fun k : ℕ => (k : ℝ)) (Measure.map ((fun c : BadIncident n → ℕ => ∑ a, c a) ∘ fun c a => c (Sum.inr a)) μ) := by
      rw [hsum.map_eq]; exact poisson_integrable_count _
    exact h0.comp_measurable (measurable_of_countable _)
  have hi : Integrable (fun c : IncidentClass n → ℕ =>
      if U ∩ countsMask incidentMask c = ∅ then (1 : ℝ) else 0) μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    filter_upwards [] with c
    split_ifs <;> norm_num
  have h := integral_mono hi (hg.add hb) (incident_killing_pointwise U)
  simp only [Pi.add_apply] at h
  rw [integral_add hg hb] at h
  have hbg : (∫ c, b c ∂μ) = Fintype.card (BadIncident n)*(r : ℝ) := by
    have he := hsum.integral_comp (f := fun k : ℕ => (k : ℝ))
      (measurable_of_countable _).aestronglyMeasurable
    rw [poisson_mean] at he
    simpa only [Function.comp_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      NNReal.coe_mul, NNReal.coe_natCast] using he
  have hgg : (∫ c, g c ∂μ) =
      poissonKillProbability U 2 (3*r*Fintype.card (Fin 2 → SignedLiteral n)) := by
    have he := poissonCountLaw_embedding_integral (A := IncidentClass n) (B := SingleIncident n)
      Sum.inl Sum.inl_injective r
      (fun c => if U ∩ countsMask singleIncidentMask c = ∅ then (1 : ℝ) else 0)
    change (∫ c, g c ∂μ) = _ at he
    rw [he, singleIncident_law r (fun I => if U ∩ I = ∅ then (1 : ℝ) else 0)]
    rw [candidateBlock_mask _ _ U (fun V => if V = ∅ then (1 : ℝ) else 0), candidateBlock_kill]
  rwa [hbg,hgg] at h

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_IncidentRates
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped NNReal

theorem clause_atom_normalization (n : ℕ) :
    clauseAtomRate n * Fintype.card (Fin 3 → SignedLiteral (n+1)) = 1 := by
  have hc : (Fintype.card (Fin 3 → SignedLiteral (n+1)) : ℝ≥0) =
      8*((n+1 : ℕ) : ℝ≥0)^3 := by
    simp only [Fintype.card_fun, SignedLiteral, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hc, clauseAtomRate, inv_mul_cancel₀ (by positivity)]

theorem incident_pair_card (n : ℕ) : Fintype.card (Fin 2 → SignedLiteral n) = 4*n^2 := by
  simp [SignedLiteral, Fintype.card_prod]
  ring

theorem incident_bad_card (n : ℕ) : Fintype.card (BadIncident n) = 6*n+1 := by
  simp [BadIncident, SignedLiteral, Fintype.card_sum, Fintype.card_prod]
  ring

theorem clause_base_rate {n : ℕ} (hn : 0 < n) :
    (1 : ℝ)/8 ≤ (clauseAtomRate n * Fintype.card (Triple (SignedLiteral n)) : ℝ≥0) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have hr : (1 : ℝ)/2 ≤ (n : ℝ)/((n : ℝ)+1) :=
    (le_div_iff₀ hpos).mpr (by linarith)
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hr 3
  rw [clauseClasses_base_card]
  change (1 : ℝ)/8 ≤ ((clauseAtomRate n : ℝ) * (8*n^3 : ℕ))
  simp only [clauseAtomRate, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_ofNat,
    NNReal.coe_pow, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_pow]
  push_cast
  convert hp using 1 <;> first | rfl | (solve | norm_num) | (solve | field_simp)

theorem incident_single_rate (n : ℕ) :
    3*(((20*(n+1) : ℕ) : ℝ≥0)*clauseAtomRate n)*
      Fintype.card (Fin 2 → SignedLiteral n) ≤ 60 := by
  apply NNReal.coe_le_coe.mp
  rw [incident_pair_card]
  simp only [clauseAtomRate, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_ofNat,
    NNReal.coe_pow, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_pow]
  push_cast
  have hp : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have he : (3 : ℝ)*(20*((n : ℝ)+1)*(8*((n : ℝ)+1)^3)⁻¹)*(4*(n : ℝ)^2) =
      30*(n : ℝ)^2/((n : ℝ)+1)^2 := by field_simp; ring
  rw [he, div_le_iff₀ (sq_pos_of_pos hp)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem incident_bad_rate (n : ℕ) :
    (Fintype.card (BadIncident n) : ℝ)*
      ((((20*(n+1) : ℕ) : ℝ≥0)*clauseAtomRate n) : ℝ) ≤ 60/((n : ℝ)+1) := by
  rw [incident_bad_card]
  simp only [clauseAtomRate, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_ofNat,
    NNReal.coe_pow, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
  push_cast
  have hp : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have he : (6*(n : ℝ)+1)*(20*((n : ℝ)+1)*(8*((n : ℝ)+1)^3)⁻¹) =
      (15*(n : ℝ)+(5/2 : ℝ))/((n : ℝ)+1)^2 := by field_simp; ring
  rw [he, div_le_div_iff₀ (sq_pos_of_pos hp) hp]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem incident_grid_obstruction {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) :
    (finiteMap (gridMaskLaw (20*(n+1)) (clauseAtomRate n) incidentMask) frontloadMask).expect
      (fun I => if U ∩ I = ∅ then 1 else 0) ≤
      poissonKillProbability U 2 60 + 60/((n : ℝ)+1) := by
  rw [finiteMap_expect, gridMaskLaw_frontload _ _
    (fun I => if U ∩ I = ∅ then 1 else 0)]
  exact (incident_killing_bound _ U).trans
    (add_le_add (poissonKillProbability_mono_rate U 2 (incident_single_rate n))
      (incident_bad_rate n))

theorem incident_restored_uniform_moment {n : ℕ} [NeZero n] (r : ℕ) :
    let M := 20*(n+1)
    let P := gridMaskLaw M (clauseAtomRate n) (incidentMask (n := n))
    let rate := clauseAtomRate n * Fintype.card (Triple (SignedLiteral n))
    P.expect (fun f => P.expect (fun t =>
      (FiniteLaw.pi (fun _ : Fin M => candidateBlock rate 3 Finset.univ)).expect (fun base =>
        (maskLifetime M (deletionBudgetMask n r) base -
          maskLifetime M (deletionBudgetMask (n+1) r)
            (fun j => restoredMask (base j) (f j) (t j)))^(6/5 : ℝ)))) ≤
      deletionMomentConstant := by
  dsimp only
  have h := restored_process_moment_sat (20*(n+1)) r
    (clauseAtomRate n * Fintype.card (Triple (SignedLiteral n)))
    (clause_base_rate (NeZero.pos n))
    (gridMaskLaw (20*(n+1)) (clauseAtomRate n) incidentMask)
    (60/((n : ℝ)+1)) incident_grid_obstruction
  apply h.trans
  unfold deletionMomentConstant
  apply add_le_add le_rfl
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 12/5)
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    capped_incident_error (Nat.succ_pos n)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ActiveProcess
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

theorem active_base_counts {n : ℕ} (c : ActiveClause n → ℕ) :
    countsMask (fun a => classBaseMask (activeClass a)) c =
      countsMask baseMask (fun a => c (.inl a)) := by
  ext x
  simp [countsMask, classBaseMask, activeClass, baseMask, Sum.forall, Prod.forall]

theorem active_mask_counts {n : ℕ} (c : ActiveClause n → ℕ) :
    countsMask activeMask c = restoredMask
      (countsMask baseMask (fun a => c (.inl a)))
      (countsMask (fun a => classIncidentMask false (activeClass a)) c)
      (countsMask (fun a => classIncidentMask true (activeClass a)) c) := by
  rw [← active_base_counts, ← countsMask_restored]
  congr 1
  funext a
  exact classClause_restored (activeClass a)

theorem active_free_lifetime {n M r : ℕ} (c : ActiveClause n × Fin M → ℕ) :
    maskLifetime M (freeDeletionBudgetMask (n+1) r 0) (maskGrid activeMask c) =
      maskLifetime M (deletionBudgetMask n r) (maskGrid baseMask (fun p => c (.inl p.1,p.2))) := by
  have he : maskGrid activeMask c = fun j => restoredMask
      (countsMask baseMask (fun a => c (.inl a,j)))
      (countsMask (fun a => classIncidentMask false (activeClass a)) (fun a => c (a,j)))
      (countsMask (fun a => classIncidentMask true (activeClass a)) (fun a => c (a,j))) := by
    funext j
    exact active_mask_counts _
  rw [he, free_restored_lifetime]
  rfl

theorem active_stronger_counts {n : ℕ} (c : ActiveClause n → ℕ) :
    countsMask strongerClassMask c = restoredMask
      (countsMask baseMask (fun a => c (.inl a)))
      (countsMask incidentMask (fun a => c (.inr (true,a))))
      (countsMask incidentMask (fun a => c (.inr (false,a)))) :=
  countsMask_stronger c

theorem active_gap_domination {n M r : ℕ} (c : ActiveClause n × Fin M → ℕ) :
    (maskLifetime M (freeDeletionBudgetMask (n+1) r 0) (maskGrid activeMask c) -
      maskLifetime M (deletionBudgetMask (n+1) r) (maskGrid activeMask c))^(6/5 : ℝ) ≤
    (maskLifetime M (deletionBudgetMask n r) (maskGrid baseMask (fun p => c (.inl p.1,p.2))) -
      maskLifetime M (deletionBudgetMask (n+1) r) (fun j => restoredMask
        (countsMask baseMask (fun a => c (.inl a,j)))
        (countsMask incidentMask (fun a => c (.inr (true,a),j)))
        (countsMask incidentMask (fun a => c (.inr (false,a),j)))))^(6/5 : ℝ) := by
  have hnon : 0 ≤ maskLifetime M (freeDeletionBudgetMask (n+1) r 0) (maskGrid activeMask c) -
      maskLifetime M (deletionBudgetMask (n+1) r) (maskGrid activeMask c) :=
    sub_nonneg.mpr (maskLifetime_mono (deletionBudgetMask_subset_free (n+1) r 0) _)
  rw [active_free_lifetime] at hnon ⊢
  apply Real.rpow_le_rpow hnon _ (by norm_num : (0 : ℝ) ≤ 6/5)
  apply sub_le_sub_left
  apply maskLifetime_map_le id _ _ _ _ (fun _ h => h)
  intro j x hx
  have he := active_stronger_counts (fun a => c (a,j))
  rw [← he] at hx
  exact countsMask_mono (fun a => strongerClassMask_subset a) _ hx

theorem poissonCountLaw_three {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (r : ℝ≥0) (f : (A → ℕ) → (B → ℕ) → (C → ℕ) → ℝ)
    (D : ℝ) (hD : ∀ a b c, |f a b c| ≤ D) :
    (∫ s : A ⊕ (B ⊕ C) → ℕ,
      f (fun a => s (.inl a)) (fun b => s (.inr (.inl b))) (fun c => s (.inr (.inr c)))
      ∂poissonCountLaw (A ⊕ (B ⊕ C)) r) =
      ∫ a, ∫ b, ∫ c, f a b c ∂poissonCountLaw C r
        ∂poissonCountLaw B r ∂poissonCountLaw A r := by
  rw [poissonCountLaw_sum r _ D (fun s => hD _ _ _)]
  apply integral_congr_ae
  filter_upwards [] with a
  exact poissonCountLaw_sum r _ D (fun _ => hD _ _ _)

theorem active_streams_expect {n M : ℕ} (r : ℝ≥0)
    (ψ : (Fin M → Finset (DeletionCandidate n)) →
      (Fin M → Finset (DeletionCandidate n)) → (Fin M → Finset (DeletionCandidate n)) → ℝ) :
    (∫ c : ActiveClause n × Fin M → ℕ,
      ψ (maskGrid baseMask (fun p => c (.inl p.1,p.2)))
        (maskGrid incidentMask (fun p => c (.inr (true,p.1),p.2)))
        (maskGrid incidentMask (fun p => c (.inr (false,p.1),p.2)))
      ∂poissonCountLaw (ActiveClause n × Fin M) r) =
      (gridMaskLaw M r baseMask).expect (fun b =>
        (gridMaskLaw M r incidentMask).expect (fun f =>
          (gridMaskLaw M r incidentMask).expect (fun t => ψ b f t))) := by
  let X := Fin M → Finset (DeletionCandidate n)
  let D := ∑ p : X × X × X, |ψ p.1 p.2.1 p.2.2|
  have hD (b f t : X) : |ψ b f t| ≤ D :=
    Finset.single_le_sum (fun p _ => abs_nonneg (ψ p.1 p.2.1 p.2.2))
      (Finset.mem_univ (b,f,t))
  have he := poissonCountLaw_equiv (splitActiveGrid n M) r
    (fun s => ψ (maskGrid baseMask (fun p => s (.inl p)))
      (maskGrid incidentMask (fun p => s (.inr (.inr p))))
      (maskGrid incidentMask (fun p => s (.inr (.inl p)))))
  change (∫ c : ActiveClause n × Fin M → ℕ,
      ψ (maskGrid baseMask (fun p => c (.inl p.1,p.2)))
        (maskGrid incidentMask (fun p => c (.inr (true,p.1),p.2)))
        (maskGrid incidentMask (fun p => c (.inr (false,p.1),p.2)))
      ∂poissonCountLaw (ActiveClause n × Fin M) r) = _ at he
  rw [he, poissonCountLaw_three r
    (fun (b : Triple (SignedLiteral n) × Fin M → ℕ)
      (f t : IncidentClass n × Fin M → ℕ) =>
        ψ (maskGrid baseMask b) (maskGrid incidentMask t) (maskGrid incidentMask f))
    D (fun a b c => hD _ _ _)]
  have hi (b : Triple (SignedLiteral n) × Fin M → ℕ)
      (f : IncidentClass n × Fin M → ℕ) :
      (∫ t, ψ (maskGrid baseMask b) (maskGrid incidentMask t) (maskGrid incidentMask f)
        ∂poissonCountLaw (IncidentClass n × Fin M) r) =
        (gridMaskLaw M r incidentMask).expect
          (fun t => ψ (maskGrid baseMask b) t (maskGrid incidentMask f)) :=
    (gridMaskLaw_expect r incidentMask
      (fun t => ψ (maskGrid baseMask b) t (maskGrid incidentMask f))).symm
  simp_rw [hi]
  have hm (b : Triple (SignedLiteral n) × Fin M → ℕ) :
      (∫ f, (gridMaskLaw M r incidentMask).expect
        (fun t => ψ (maskGrid baseMask b) t (maskGrid incidentMask f))
        ∂poissonCountLaw (IncidentClass n × Fin M) r) =
      (gridMaskLaw M r incidentMask).expect (fun f =>
        (gridMaskLaw M r incidentMask).expect (fun t => ψ (maskGrid baseMask b) t f)) :=
    (gridMaskLaw_expect r incidentMask (fun f =>
      (gridMaskLaw M r incidentMask).expect (fun t => ψ (maskGrid baseMask b) t f))).symm
  simp_rw [hm]
  rw [← gridMaskLaw_expect r baseMask (fun b =>
    (gridMaskLaw M r incidentMask).expect (fun f =>
      (gridMaskLaw M r incidentMask).expect (fun t => ψ b t f)))]
  apply FiniteLaw.expect_congr
  intro b
  exact finite_expect_comm _ _ _

theorem active_original_expect {n M : ℕ} (r : ℝ≥0)
    (ψ : (Fin M → Finset (DeletionCandidate (n+1))) → ℝ) :
    (∫ c : TripleClasses (SignedLiteral n) × Fin M → ℕ,
      ψ (maskGrid (fun a => clauseMask (classClause a)) c)
      ∂poissonCountLaw (TripleClasses (SignedLiteral n) × Fin M) r) =
    ∫ c : ActiveClause n × Fin M → ℕ, ψ (maskGrid activeMask c)
      ∂poissonCountLaw (ActiveClause n × Fin M) r := by
  let e : ActiveClause n × Fin M → TripleClasses (SignedLiteral n) × Fin M :=
    fun p => (activeClass p.1,p.2)
  have he : Function.Injective e := by
    intro p q h
    change (activeClass p.1,p.2) = (activeClass q.1,q.2) at h
    exact Prod.ext (activeClass_injective n (Prod.mk.inj h).1) (Prod.mk.inj h).2
  rw [← poissonCountLaw_embedding_integral e he r]
  apply integral_congr_ae
  filter_upwards [] with c
  congr 1
  funext j
  exact (countsMask_active (fun a => c (a,j))).symm

theorem base_grid_law {n : ℕ} [NeZero n] (M : ℕ) (r : ℝ≥0) :
    gridMaskLaw M r (baseMask (n := n)) = FiniteLaw.pi (fun _ : Fin M =>
      candidateBlock (r*Fintype.card (Triple (SignedLiteral n))) 3 Finset.univ) := by
  rw [← gridMaskLaw_equiv (tripleVectorEquiv (SignedLiteral n)) r baseMask]
  have hm : baseMask ∘ tripleVectorEquiv (SignedLiteral n) = clauseMask := by
    funext a
    simp only [baseMask, Function.comp_apply, Equiv.symm_apply_apply]
  rw [hm, gridMaskLaw_clauses]
  rw [Fintype.card_congr (tripleVectorEquiv (SignedLiteral n))]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ActualFreeMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

theorem actual_free_deletion_moment_zero {n : ℕ} [NeZero n] (r : ℕ) :
    (FiniteLaw.pi (fun _ : Fin (20*(n+1)) =>
      candidateBlock (n := n+1) 1 3 Finset.univ)).expect (freeGap n (20*(n+1)) r) ≤
      deletionMomentConstant := by
  let M := 20*(n+1)
  let rate := clauseAtomRate n
  let ψ := restoredGap n M r
  let B := gridMaskLaw M rate (baseMask (n := n))
  let P := gridMaskLaw M rate (incidentMask (n := n))
  have hgrid := gridMaskLaw_clauses (n := n+1) M 3 rate
  change gridMaskLaw M rate clauseMask = _ at hgrid
  have hn := clause_atom_normalization n
  change rate * Fintype.card (Fin 3 → SignedLiteral (n+1)) = 1 at hn
  rw [hn] at hgrid
  have hm : clauseMask (n := n+1) (k := 3) =
      (fun a => clauseMask (classClause a)) ∘ clauseClassesEquiv n := by
    funext a
    simp only [Function.comp_apply, classClause, Equiv.symm_apply_apply]
  have hleft : Integrable (fun c : ActiveClause n × Fin M → ℕ =>
      freeGap n M r (maskGrid activeMask c)) (poissonCountLaw (ActiveClause n × Fin M) rate) :=
    bounded_finite_observable _ (maskGrid activeMask) (measurable_of_countable _) (freeGap n M r)
  have hright : Integrable (fun c : ActiveClause n × Fin M → ℕ =>
      ψ (maskGrid baseMask (fun p => c (.inl p.1,p.2)))
        (maskGrid incidentMask (fun p => c (.inr (true,p.1),p.2)))
        (maskGrid incidentMask (fun p => c (.inr (false,p.1),p.2))))
      (poissonCountLaw (ActiveClause n × Fin M) rate) := by
    exact bounded_finite_observable _
      (fun c : ActiveClause n × Fin M → ℕ =>
        (maskGrid baseMask (fun p => c (.inl p.1,p.2)),
          maskGrid incidentMask (fun p => c (.inr (true,p.1),p.2)),
          maskGrid incidentMask (fun p => c (.inr (false,p.1),p.2))))
      (measurable_of_countable _) (fun p => ψ p.1 p.2.1 p.2.2)
  calc
    _ = (gridMaskLaw M rate clauseMask).expect (freeGap n M r) := by rw [hgrid]
    _ = (gridMaskLaw M rate (fun a => clauseMask (classClause a))).expect (freeGap n M r) := by
      exact congrArg (fun P => P.expect (freeGap n M r))
        ((congrArg (gridMaskLaw M rate) hm).trans
          (gridMaskLaw_equiv (clauseClassesEquiv n) rate (fun a => clauseMask (classClause a))))
    _ = ∫ c : ActiveClause n × Fin M → ℕ, freeGap n M r (maskGrid activeMask c)
        ∂poissonCountLaw (ActiveClause n × Fin M) rate := by
      rw [gridMaskLaw_expect, active_original_expect]
    _ ≤ ∫ c : ActiveClause n × Fin M → ℕ,
        ψ (maskGrid baseMask (fun p => c (.inl p.1,p.2)))
          (maskGrid incidentMask (fun p => c (.inr (true,p.1),p.2)))
          (maskGrid incidentMask (fun p => c (.inr (false,p.1),p.2)))
          ∂poissonCountLaw (ActiveClause n × Fin M) rate :=
      integral_mono hleft hright (fun c => active_gap_domination c)
    _ = B.expect (fun base => P.expect (fun f => P.expect (fun t => ψ base f t))) :=
      active_streams_expect rate ψ
    _ = P.expect (fun f => P.expect (fun t => B.expect (fun base => ψ base f t))) := by
      rw [finite_expect_comm B P]
      apply P.expect_congr
      intro f
      exact finite_expect_comm B P _
    _ ≤ deletionMomentConstant := by
      dsimp only [B]
      rw [base_grid_law]
      exact incident_restored_uniform_moment r

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MaskPermutations
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical

noncomputable section

attribute [local instance] OAI.FixedClauseThreshold.Computability.maskPermutationsDecidableEq
theorem deletedVariables_permutation {n : ℕ} (e : Equiv.Perm (Fin n)) (x : DeletionCandidate n) :
    deletedVariables (candidatePermutation e x) = (deletedVariables x).image e := by
  ext v
  constructor
  · intro h
    have hx : x (e.symm v) = none := (Finset.mem_filter.mp h).2
    exact Finset.mem_image.mpr ⟨e.symm v,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,e.apply_symm_apply v⟩
  · intro h
    obtain ⟨w,hw,hwe⟩ := Finset.mem_image.mp h
    have hx : x w = none := (Finset.mem_filter.mp hw).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change x (e.symm v) = none
    rw [← hwe,Equiv.symm_apply_apply]
    exact hx

theorem deletionBudget_permutation {n r : ℕ} (e : Equiv.Perm (Fin n)) (x : DeletionCandidate n) :
    candidatePermutation e x ∈ deletionBudgetMask n r ↔ x ∈ deletionBudgetMask n r := by
  simp only [deletionBudgetMask, Finset.mem_filter, Finset.mem_univ, true_and,
    deletedVariables_permutation, Finset.card_image_of_injective _ e.injective]

theorem mem_freeDeletionBudgetMask_erase {n r : ℕ} (v : Fin n) (x : DeletionCandidate n) :
    x ∈ freeDeletionBudgetMask n r v ↔ ((deletedVariables x).erase v).card ≤ r := by
  simp only [freeDeletionBudgetMask, Finset.mem_biUnion, allowedDeletions, deletionMask,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨D,hD,hx⟩
    have he : (deletedVariables x).erase v ⊆ D := by
      intro w hw
      exact (Finset.mem_insert.mp (hx (Finset.mem_of_mem_erase hw))).resolve_left
        (Finset.ne_of_mem_erase hw)
    exact (Finset.card_le_card he).trans hD
  · intro hx
    refine ⟨(deletedVariables x).erase v,hx,?_⟩
    intro w hw
    by_cases he : w = v
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨he,hw⟩))

theorem freeDeletionBudget_permutation {n r : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin n) (x : DeletionCandidate n) :
    candidatePermutation e x ∈ freeDeletionBudgetMask n r (e v) ↔
      x ∈ freeDeletionBudgetMask n r v := by
  rw [mem_freeDeletionBudgetMask_erase, mem_freeDeletionBudgetMask_erase,
    deletedVariables_permutation, ← Finset.image_erase e.injective,
    Finset.card_image_of_injective _ e.injective]

theorem maskLifetime_permutation {n M : ℕ} (e : Equiv.Perm (Fin n))
    (U V : Finset (DeletionCandidate n)) (xs : Fin M → Finset (DeletionCandidate n))
    (hUV : ∀ x, candidatePermutation e x ∈ V ↔ x ∈ U) :
    maskLifetime M V (fun j => renameMask e (xs j)) = maskLifetime M U xs := by
  apply le_antisymm
  · apply maskLifetime_map_le (candidatePermutation e).symm
    · intro x hx
      have h := (hUV ((candidatePermutation e).symm x)).mp
      exact h (by simpa only [Equiv.apply_symm_apply] using hx)
    · intro j x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      simpa only [Equiv.symm_apply_apply] using hy
  · apply maskLifetime_map_le (candidatePermutation e)
    · intro x hx
      exact (hUV x).mpr hx
    · intro j x hx
      exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem clauseMask_permutation_mem {n k : ℕ} (e : Equiv.Perm (Fin n))
    (cs : Fin k → SignedLiteral n) (x : DeletionCandidate n) :
    candidatePermutation e x ∈ clauseMask (fun j => literalPermutation e (cs j)) ↔
      x ∈ clauseMask cs := by
  simp only [clauseMask, Finset.mem_filter, Finset.mem_univ, true_and]
  change (¬∀ j, x (e.symm (e (cs j).1)) = some (!(cs j).2)) ↔
    (¬∀ j, x (cs j).1 = some (!(cs j).2))
  simp only [Equiv.symm_apply_apply]

private theorem mem_clauseCounts {n k : ℕ} (x : DeletionCandidate n)
    (c : (Fin k → SignedLiteral n) → ℕ) :
    x ∈ countsMask clauseMask c ↔ ∀ a, c a = 0 ∨ x ∈ clauseMask a := by
  simp only [countsMask, Finset.mem_filter, Finset.mem_univ, true_and]

theorem countsMask_permutation {n k : ℕ} (e : Equiv.Perm (Fin n))
    (c : (Fin k → SignedLiteral n) → ℕ) :
    renameMask e (countsMask clauseMask c) =
      countsMask clauseMask (fun a => c ((clausePermutation e k).symm a)) := by
  ext x
  rw [renameMask, Finset.mem_image]
  constructor
  · rintro ⟨y,hy,rfl⟩
    apply (mem_clauseCounts _ _).mpr
    intro a
    rcases (mem_clauseCounts y c).mp hy ((clausePermutation e k).symm a) with hz | hm
    · exact Or.inl hz
    · right
      have he : (fun j => literalPermutation e (((clausePermutation e k).symm a) j)) = a :=
        (clausePermutation e k).apply_symm_apply a
      rw [← he]
      exact (clauseMask_permutation_mem e _ y).mpr hm
  · intro hx
    refine ⟨(candidatePermutation e).symm x, ?_, (candidatePermutation e).apply_symm_apply x⟩
    apply (mem_clauseCounts _ _).mpr
    intro a
    have h := (mem_clauseCounts x _).mp hx ((clausePermutation e k) a)
    simp only [Equiv.symm_apply_apply] at h
    rcases h with hz | hm
    · exact Or.inl hz
    · right
      have hmem := (clauseMask_permutation_mem e a ((candidatePermutation e).symm x)).mp
      apply hmem
      change x ∈ clauseMask (fun j => literalPermutation e (a j)) at hm
      simpa only [Equiv.apply_symm_apply] using hm

end

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ExchangeableBlocks
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory
open scoped NNReal Classical

theorem maskGrid_permutation {n k M : ℕ} (e : Equiv.Perm (Fin n))
    (c : (Fin k → SignedLiteral n) × Fin M → ℕ) :
    (fun j => renameMask e (maskGrid clauseMask c j)) =
      maskGrid clauseMask (fun p => c ((clausePermutation e k).symm p.1,p.2)) := by
  funext j
  exact countsMask_permutation e (fun a => c (a,j))

theorem gridMaskLaw_permutation {n k M : ℕ} (e : Equiv.Perm (Fin n)) (r : ℝ≥0)
    (f : (Fin M → Finset (DeletionCandidate n)) → ℝ) :
    (gridMaskLaw M r (clauseMask (n := n) (k := k))).expect
      (fun xs => f (fun j => renameMask e (xs j))) =
      (gridMaskLaw M r (clauseMask (n := n) (k := k))).expect f := by
  simp only [gridMaskLaw_expect, maskGrid_permutation]
  have h := poissonCountLaw_equiv
    ((clausePermutation e k).prodCongr (Equiv.refl (Fin M))) r
    (fun c => f (maskGrid clauseMask c))
  exact h

theorem candidatePath_permutation {n : ℕ} [NeZero n] (M k : ℕ)
    (e : Equiv.Perm (Fin n)) (r : ℝ≥0)
    (f : (Fin M → Finset (DeletionCandidate n)) → ℝ) :
    (FiniteLaw.pi (fun _ : Fin M => candidateBlock r k Finset.univ)).expect
      (fun xs => f (fun j => renameMask e (xs j))) =
      (FiniteLaw.pi (fun _ : Fin M => candidateBlock r k Finset.univ)).expect f := by
  have hc : (Fintype.card (Fin k → SignedLiteral n) : ℝ≥0) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h := gridMaskLaw_permutation (k := k) (M := M) e
    (r/Fintype.card (Fin k → SignedLiteral n)) f
  rw [gridMaskLaw_clauses, div_mul_cancel₀ _ hc] at h
  exact h

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_UniformFreeMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped NNReal Classical

theorem uniformFreeConstant_nonneg : 0 ≤ uniformFreeConstant := by
  unfold uniformFreeConstant
  linarith [deletionMomentConstant_nonneg]

theorem free_gap_power_le {n M r : ℕ} (v : Fin n)
    (xs : Fin M → Finset (DeletionCandidate n)) :
    (maskLifetime M (freeDeletionBudgetMask n r v) xs -
      maskLifetime M (deletionBudgetMask n r) xs)^(6/5 : ℝ) ≤ (M : ℝ)^(6/5 : ℝ) := by
  apply Real.rpow_le_rpow
  · exact sub_nonneg.mpr (maskLifetime_mono (deletionBudgetMask_subset_free n r v) xs)
  · exact (sub_le_self _ (maskLifetime_nonneg _ xs)).trans (maskLifetime_le _ xs)
  · norm_num

theorem actual_free_deletion_moment (n r : ℕ) [NeZero n] (v : Fin n) :
    (FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)).expect
      (fun xs => (maskLifetime (20*n) (freeDeletionBudgetMask n r v) xs -
        maskLifetime (20*n) (deletionBudgetMask n r) xs)^(6/5 : ℝ)) ≤ uniformFreeConstant := by
  cases n with
  | zero => exact Fin.elim0 v
  | succ n =>
    cases n with
    | zero =>
      have h := (FiniteLaw.pi (fun _ : Fin (20*1) =>
        candidateBlock (n := 1) 1 3 Finset.univ)).expect_mono
          (fun xs => free_gap_power_le v xs (r := r))
      rw [FiniteLaw.expect_const] at h
      apply h.trans
      have hp : (20 : ℝ)^(6/5 : ℝ) ≤ 20^2 := by
        simpa only [Real.rpow_natCast] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 20)
            (by norm_num : (6/5 : ℝ) ≤ (2 : ℕ))
      norm_num only [Nat.mul_one, Nat.cast_ofNat] at *
      unfold uniformFreeConstant
      linarith [deletionMomentConstant_nonneg]
    | succ n =>
      let e : Equiv.Perm (Fin (n+1+1)) := Equiv.swap 0 v
      have hv : e 0 = v := Equiv.swap_apply_left _ _
      let φ := fun xs : Fin (20*(n+1+1)) → Finset (DeletionCandidate (n+1+1)) =>
        (maskLifetime (20*(n+1+1)) (freeDeletionBudgetMask (n+1+1) r v) xs -
          maskLifetime (20*(n+1+1)) (deletionBudgetMask (n+1+1) r) xs)^(6/5 : ℝ)
      have he := candidatePath_permutation (20*(n+1+1)) 3 e 1 φ
      have hφ (xs) : φ (fun j => renameMask e (xs j)) =
          freeGap (n+1) (20*(n+1+1)) r xs := by
        dsimp only [φ, freeGap]
        rw [maskLifetime_permutation e (freeDeletionBudgetMask (n+1+1) r 0)
          (freeDeletionBudgetMask (n+1+1) r v) xs (fun x => by
            simpa only [hv] using freeDeletionBudget_permutation e 0 x),
          maskLifetime_permutation e (deletionBudgetMask (n+1+1) r)
            (deletionBudgetMask (n+1+1) r) xs (deletionBudget_permutation e)]
      simp only [hφ] at he
      rw [← he]
      exact (actual_free_deletion_moment_zero r).trans
        (by unfold uniformFreeConstant; linarith)

theorem actual_deletion_mean (n r : ℕ) [NeZero n] :
    let P := FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)
    P.expect (maskLifetime (20*n) (deletionBudgetMask n r)) -
      P.expect (maskLifetime (20*n) (deletionBudgetMask n 0)) ≤
      6*((n : ℝ)*uniformFreeConstant)^(5/6 : ℝ)*(r : ℝ)^(1/6 : ℝ) := by
  dsimp only
  have h := finite_deletion_mean (r := r)
    (FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ))
    (fun xs => fixedMaskDeletionTime xs) (fun xs => fixedMaskDeletionTime_mono xs)
    uniformFreeConstant_nonneg
    (fun j _ v => by
      simpa only [freeMaskDeletionTime_eq, bestMaskDeletionTime_eq] using
        actual_free_deletion_moment n j v)
  simpa only [bestMaskDeletionTime_eq] using h

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DeletionScaling
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Filter
open scoped NNReal Topology

theorem deletion_increment_linear_sat_oai (n q : ℕ) [NeZero n] (hq : 0 < q) :
    let P := FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)
    P.expect (maskLifetime (20*n) (deletionBudgetMask n (n/q))) -
      P.expect (maskLifetime (20*n) (deletionBudgetMask n 0)) ≤ deletionSlope q*n := by
  dsimp only
  apply (actual_deletion_mean n (n/q)).trans
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hd : ((n/q : ℕ) : ℝ) ≤ (n : ℝ)*(q : ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hqR]
    exact_mod_cast Nat.div_mul_le_self n q
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (n/q)) hd
    (by norm_num : (0 : ℝ) ≤ 1/6)
  calc
    _ ≤ 6*((n : ℝ)*uniformFreeConstant)^(5/6 : ℝ)*
        ((n : ℝ)*(q : ℝ)⁻¹)^(1/6 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (mul_nonneg hn.le uniformFreeConstant_nonneg) _))
    _ = deletionSlope q*n := by
      rw [Real.mul_rpow hn.le uniformFreeConstant_nonneg,
        Real.mul_rpow hn.le (inv_nonneg.mpr hqR.le)]
      calc
        _ = deletionSlope q*((n : ℝ)^(5/6 : ℝ)*(n : ℝ)^(1/6 : ℝ)) := by
          unfold deletionSlope
          ring
        _ = _ := by rw [← Real.rpow_add hn]; norm_num

end FixedClauseThreshold.Computability

end OAI
end

theorem solution : type_of% @OAI.FixedClauseThreshold.Computability.deletion_increment_linear_sat_oai := @OAI.FixedClauseThreshold.Computability.deletion_increment_linear_sat_oai
