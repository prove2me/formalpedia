-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine_le_scalarBernoulliTail
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:58:31.682136+00:00
-- url     : https://prove2.me/submissions/aac59de6-c82a-4c7a-bd3c-e5bcc71d5141

-- Generated proof for MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine_le_scalarBernoulliTail.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/Scalar.lean. -/
/-!
# Scalar Bernoulli polynomial helpers for pasting

Purely scalar inequalities used by the matrix Chernoff comparison.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MeasureTheory ProbabilityTheory
open scoped BigOperators







/-- Hoeffding's lemma for a centered Bernoulli random variable. -/
private lemma bernoulli_centered_mgf_le {p t : Error}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * Real.exp (t * p) + p * Real.exp (t * (p - 1)) ≤
      Real.exp (t ^ (2 : ℕ) / 8) := by
  let pI : unitInterval := ⟨p, hp0, hp1⟩
  have hpI_coe : (pI : Error) = p := rfl
  let μ : Measure Bool := ProbabilityTheory.bernoulliMeasure true false pI
  have hm : AEMeasurable (fun b : Bool => cond b (1 : Error) 0) μ := by
    simpa using (measurable_of_finite (fun b : Bool => cond b (1 : Error) 0)).aemeasurable
  have hb : ∀ᵐ b ∂μ, (cond b (1 : Error) 0) ∈ Set.Icc (0 : Error) 1 := by
    filter_upwards with b
    cases b <;> simp
  have hsubG := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hm hb
  have hcentered :
      ProbabilityTheory.HasSubgaussianMGF
        (fun b : Bool => p - cond b (1 : Error) 0)
        ((‖(1 : Error) - 0‖₊ / 2) ^ (2 : ℕ)) μ := by
    refine hsubG.neg.congr ?_
    filter_upwards with b
    simp [μ, ProbabilityTheory.integral_bernoulliMeasure, hpI_coe]
  have hmgf := hcentered.mgf_le t
  have hmgf' :
      p * Real.exp (t * (p - 1)) +
          (1 - p) * Real.exp (p * t) ≤
        Real.exp (t ^ (2 : ℕ) * (2 ^ (2 : ℕ))⁻¹ / 2) := by
    simpa [μ, ProbabilityTheory.mgf, ProbabilityTheory.integral_bernoulliMeasure,
      smul_eq_mul, hpI_coe, mul_comm, add_comm]
      using hmgf
  have hexp :
      Real.exp (t ^ (2 : ℕ) * (2 ^ (2 : ℕ))⁻¹ / 2) = Real.exp (t ^ (2 : ℕ) / 8) := by
    congr 1
    ring_nf
  rw [hexp] at hmgf'
  simpa [mul_comm, add_comm] using hmgf'

/-- The centered moment-generating function of the binomial law is the binomial expansion of the
corresponding one-step Bernoulli moment-generating function. -/
private lemma binomial_centered_mgf_eq
    (k : ℕ) {p t : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ProbabilityTheory.mgf (fun i : ℕ => p * k - i)
      (ProbabilityTheory.binomial k (⟨p, hp0, hp1⟩ : unitInterval)) t =
        ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
            Real.exp (t * (p * k - r)) := by
  let pI : unitInterval := ⟨p, hp0, hp1⟩
  have hpI_coe : (pI : Error) = p := rfl
  calc
    ProbabilityTheory.mgf (fun i : ℕ => p * k - i) (ProbabilityTheory.binomial k pI) t
      = ∫ i, Real.exp (t * (p * k - i)) ∂ProbabilityTheory.binomial k pI := by
          rfl
    _ = ∑ r ∈ Finset.Iic k,
          (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
            Real.exp (t * (p * k - r)) := by
          rw [ProbabilityTheory.integral_binomial]
          refine Finset.sum_congr rfl ?_
          intro r hr
          simp [hpI_coe, smul_eq_mul]
          ring
    _ = ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
            Real.exp (t * (p * k - r)) := by
          rw [Nat.range_succ_eq_Iic]

/-- A Hoeffding bound for the centered binomial moment-generating function. -/
private lemma binomial_centered_mgf_le
    (k : ℕ) {p t : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ProbabilityTheory.mgf (fun i : ℕ => p * k - i)
      (ProbabilityTheory.binomial k (⟨p, hp0, hp1⟩ : unitInterval)) t ≤
        Real.exp ((k : Error) * t ^ (2 : ℕ) / 8) := by
  let a : Error := p * Real.exp (t * (p - 1))
  let b : Error := (1 - p) * Real.exp (t * p)
  have hrewrite :
      (∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
          Real.exp (t * (p * k - r))) =
        ∑ r ∈ Finset.range (k + 1), (Nat.choose k r : Error) * (a ^ r * b ^ (k - r)) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    dsimp [a, b]
    have hrle : r ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    have hexp :
        Real.exp (t * (p * k - r)) =
          Real.exp (((k : Error) - r) * (t * p)) * Real.exp ((r : Error) * (t * (p - 1))) := by
      rw [show t * (p * k - r) =
          ((k : Error) - r) * (t * p) + (r : Error) * (t * (p - 1)) by ring]
      rw [Real.exp_add]
    have hfirst :
        Real.exp (((k : Error) - r) * (t * p)) = Real.exp (t * p) ^ (k - r) := by
      rw [← Nat.cast_sub hrle]
      simpa using (Real.exp_nat_mul (t * p) (k - r))
    have hsecond :
        Real.exp ((r : Error) * (t * (p - 1))) = Real.exp (t * (p - 1)) ^ r := by
      simpa using (Real.exp_nat_mul (t * (p - 1)) r)
    rw [hexp, hfirst, hsecond]
    calc
      (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
          (Real.exp (t * p) ^ (k - r) * Real.exp (t * (p - 1)) ^ r)
        = (Nat.choose k r : Error) *
            ((p ^ r * Real.exp (t * (p - 1)) ^ r) *
              ((1 - p) ^ (k - r) * Real.exp (t * p) ^ (k - r))) := by
              ring
      _ = (Nat.choose k r : Error) *
            ((p * Real.exp (t * (p - 1))) ^ r * ((1 - p) * Real.exp (t * p)) ^ (k - r)) := by
              rw [← mul_pow, ← mul_pow]
      _ = (Nat.choose k r : Error) * (a ^ r * b ^ (k - r)) := by
              rfl
  have hpow :
      (∑ r ∈ Finset.range (k + 1), (Nat.choose k r : Error) * (a ^ r * b ^ (k - r))) =
        (a + b) ^ k := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (add_pow a b k).symm
  let pI : unitInterval := ⟨p, hp0, hp1⟩
  calc
    ProbabilityTheory.mgf (fun i : ℕ => p * k - i)
        (ProbabilityTheory.binomial k pI) t
      = ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
            Real.exp (t * (p * k - r)) :=
        binomial_centered_mgf_eq k hp0 hp1
    _ = ∑ r ∈ Finset.range (k + 1), (Nat.choose k r : Error) * (a ^ r * b ^ (k - r)) := hrewrite
    _ = (a + b) ^ k := hpow
    _ ≤ (Real.exp (t ^ (2 : ℕ) / 8)) ^ k := by
          have ha_nonneg : 0 ≤ a := by
            dsimp [a]
            positivity
          have hOneSub_nonneg : 0 ≤ 1 - p := by
            linarith
          have hb_nonneg : 0 ≤ b := by
            dsimp [b]
            exact mul_nonneg hOneSub_nonneg (by positivity)
          have hab_nonneg : 0 ≤ a + b := by
            linarith
          apply pow_le_pow_left₀ hab_nonneg
          simpa [a, b, add_comm] using bernoulli_centered_mgf_le hp0 hp1
    _ = Real.exp ((k : Error) * (t ^ (2 : ℕ) / 8)) := by
          symm
          simpa [mul_comm] using (Real.exp_nat_mul (t ^ (2 : ℕ) / 8) k)
    _ = Real.exp ((k : Error) * t ^ (2 : ℕ) / 8) := by
          congr 1
          ring

/-- The lower tail of the binomial law is the lower partial sum of the Bernoulli polynomial. -/
private lemma binomial_lowerTail_eq
    (k degree : ℕ) {p : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (ProbabilityTheory.binomial k (⟨p, hp0, hp1⟩ : unitInterval)).real
        {i : ℕ | (i : Error) ≤ degree} =
      scalarBernoulliLowerTail k degree p := by
  let pI : unitInterval := ⟨p, hp0, hp1⟩
  have hpI_coe : (pI : Error) = p := rfl
  let f : ℕ → Error := fun r =>
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))
  calc
    (ProbabilityTheory.binomial k pI).real {i : ℕ | (i : Error) ≤ degree}
      = ∑ r ∈ Finset.Iic k, if r ≤ degree then f r else 0 := by
          rw [measureReal_def, ProbabilityTheory.binomial_eq_sum_dirac,
            Measure.finsetSum_apply, ENNReal.toReal_sum]
          · refine Finset.sum_congr rfl ?_
            intro r hr
            by_cases hrd : r ≤ degree
            · have hcoeff_nonneg :
                  0 ≤ (Nat.choose k r : Error) * p ^ r * (1 - p) ^ (k - r) := by
                positivity
              have hmem : r ∈ {i : ℕ | i ≤ degree} := hrd
              have htoReal :
                  (ENNReal.ofReal ((Nat.choose k r : Error) * p ^ r *
                    (1 - p) ^ (k - r))).toReal =
                    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) := by
                rw [ENNReal.toReal_ofReal hcoeff_nonneg]
                ring
              simpa only [Nat.cast_le, Measure.smul_apply,
                MeasurableSpace.measurableSet_top, Measure.dirac_apply', smul_eq_mul,
                Set.indicator_of_mem hmem, Pi.one_apply, mul_one, hrd, ite_true, f, hpI_coe]
                using htoReal
            · simp [Measure.smul_apply, hrd, f, hpI_coe, smul_eq_mul]
          · intro r hr
            refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
            by_cases hrd : r ≤ degree <;> simp [Set.indicator, hrd]
    _ = ∑ r ∈ Finset.range (k + 1), if r ≤ degree then f r else 0 := by
          rw [Nat.range_succ_eq_Iic]
    _ = ∑ r ∈ Finset.range (degree + 1), f r := by
          by_cases hdk : degree ≤ k
          · have hRange :
                (∑ r ∈ Finset.range (degree + 1), if r ≤ degree then f r else 0) =
                  ∑ r ∈ Finset.range (degree + 1), f r := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                have hrle : r ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
                simp [hrle]
            have hIcoZero :
                (∑ r ∈ Finset.Ico (degree + 1) (k + 1), if r ≤ degree then f r else 0) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro r hr
                have hlt : degree < r := (Finset.mem_Ico.mp hr).1
                simp [Nat.not_le.mpr hlt]
            have hsplit :=
              Finset.sum_range_add_sum_Ico (f := fun r => if r ≤ degree then f r else 0)
                (h := Nat.succ_le_succ hdk)
            calc
              (∑ r ∈ Finset.range (k + 1), if r ≤ degree then f r else 0)
                =
                  ∑ r ∈ Finset.range (degree + 1), if r ≤ degree then f r else 0 := by
                      symm
                      rw [hIcoZero, add_zero] at hsplit
                      exact hsplit
              _ = ∑ r ∈ Finset.range (degree + 1), f r := hRange
          · have hdk' : k < degree := Nat.lt_of_not_ge hdk
            have hAll :
                (∑ r ∈ Finset.range (k + 1), if r ≤ degree then f r else 0) =
                  ∑ r ∈ Finset.range (k + 1), f r := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                have hrle : r ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
                have hrdeg : r ≤ degree := hrle.trans (Nat.le_of_lt hdk')
                simp [hrdeg]
            have hIcoZero : ∑ r ∈ Finset.Ico (k + 1) (degree + 1), f r = 0 := by
              refine Finset.sum_eq_zero ?_
              intro r hr
              have hklt : k < r := (Finset.mem_Ico.mp hr).1
              change (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) = 0
              rw [Nat.choose_eq_zero_of_lt hklt]
              simp
            have hsplit :=
              Finset.sum_range_add_sum_Ico (f := f) (h := Nat.succ_le_succ (Nat.le_of_lt hdk'))
            calc
              (∑ r ∈ Finset.range (k + 1), if r ≤ degree then f r else 0)
                = ∑ r ∈ Finset.range (k + 1), f r := hAll
              _ = ∑ r ∈ Finset.range (degree + 1), f r := by
                    rw [hIcoZero, add_zero] at hsplit
                    exact hsplit
    _ = scalarBernoulliLowerTail k degree p := by
          rfl

/-- The binomial lower tail obeys the additive Hoeffding bound. -/
private lemma scalarBernoulliLowerTail_le_exp
    (k degree : ℕ) {p : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hpd : (degree : Error) / (k : Error) ≤ p) :
    scalarBernoulliLowerTail k degree p ≤
      Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) * (k : Error))) := by
  by_cases hk0 : k = 0
  · subst hk0
    have htail : scalarBernoulliLowerTail 0 degree p = 1 := by
      unfold scalarBernoulliLowerTail
      rw [Finset.sum_eq_single 0]
      · simp
      · intro r hr hr0
        have hrpos : 0 < r := Nat.pos_iff_ne_zero.mpr hr0
        simp [Nat.choose_eq_zero_of_lt hrpos]
      · simp
    rw [htail]
    simp
  · have hkpos : 0 < (k : Error) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hk0
    let ε : Error := p * (k : Error) - degree
    let t : Error := 4 * (p - degree / (k : Error))
    let pI : unitInterval := ⟨p, hp0, hp1⟩
    let μ : Measure ℕ := ProbabilityTheory.binomial k pI
    have hε_nonneg : 0 ≤ ε := by
      dsimp [ε]
      have hpd' : (degree : Error) ≤ p * (k : Error) := by
        rw [div_le_iff₀ hkpos] at hpd
        simpa [mul_comm] using hpd
      linarith
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      nlinarith
    have hInt :
        Integrable (fun i : ℕ => Real.exp (t * (p * (k : Error) - i))) μ := by
      exact ProbabilityTheory.integrable_binomial _
    have hCher :=
      ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := μ) (X := fun i : ℕ => p * (k : Error) - i) (t := t) ε
        ht_nonneg hInt
    have hEvent :
        {i : ℕ | ε ≤ p * (k : Error) - i} =
          {i : ℕ | (i : Error) ≤ degree} := by
      ext i
      dsimp [ε]
      constructor <;> intro hi <;> linarith
    calc
      scalarBernoulliLowerTail k degree p
        = μ.real {i : ℕ | ε ≤ p * (k : Error) - i} := by
            rw [hEvent]
            symm
            exact binomial_lowerTail_eq k degree hp0 hp1
      _ ≤ Real.exp (-t * ε) *
            ProbabilityTheory.mgf (fun i : ℕ => p * (k : Error) - i) μ t := hCher
      _ ≤ Real.exp (-t * ε) * Real.exp ((k : Error) * t ^ (2 : ℕ) / 8) := by
            gcongr
            exact binomial_centered_mgf_le k hp0 hp1 (t := t)
      _ = Real.exp (-t * ε + (k : Error) * t ^ (2 : ℕ) / 8) := by
            rw [← Real.exp_add]
      _ = Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) * (k : Error))) := by
            have hε_eq : ε = (p - degree / (k : Error)) * (k : Error) := by
              dsimp [ε]
              field_simp [hkpos.ne']
            dsimp [t]
            rw [hε_eq]
            congr 1
            ring_nf

/-- The lower and upper binomial tails partition the full Bernoulli polynomial. -/
private lemma scalarBernoulliLowerTail_add_scalarBernoulliTail
    (k degree : ℕ) (p : Error) :
    scalarBernoulliLowerTail k degree p + scalarBernoulliTail k degree p = 1 := by
  let f : ℕ → Error := fun r =>
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))
  have hfull : ∑ r ∈ Finset.range (k + 1), f r = 1 := by
    calc
      ∑ r ∈ Finset.range (k + 1), f r
        = ∑ r ∈ Finset.range (k + 1), p ^ r * (1 - p) ^ (k - r) * Nat.choose k r := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              ring
      _ = (p + (1 - p)) ^ k := by
            simpa using (add_pow p (1 - p) k).symm
      _ = 1 := by
            ring
  by_cases hdk : degree ≤ k
  · have hTail :
        ∑ r ∈ Finset.Ico (degree + 1) (k + 1), f r = scalarBernoulliTail k degree p := by
      have hIco : Finset.Ico (degree + 1) (k + 1) = Finset.Icc (degree + 1) k := by
        ext r
        simp
      simp [scalarBernoulliTail, f, hIco]
    calc
      scalarBernoulliLowerTail k degree p + scalarBernoulliTail k degree p
        =
          (∑ r ∈ Finset.range (degree + 1), f r) +
            ∑ r ∈ Finset.Ico (degree + 1) (k + 1), f r := by
              rw [scalarBernoulliLowerTail, ← hTail]
      _ = ∑ r ∈ Finset.range (k + 1), f r := by
            exact Finset.sum_range_add_sum_Ico (f := f) (h := Nat.succ_le_succ hdk)
      _ = 1 := hfull
  · have hdk' : k < degree := Nat.lt_of_not_ge hdk
    have hTailZero : scalarBernoulliTail k degree p = 0 := by
      unfold scalarBernoulliTail
      refine Finset.sum_eq_zero ?_
      intro r hr
      have hr1 : degree + 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hr2 : r ≤ k := (Finset.mem_Icc.mp hr).2
      omega
    have hIcoZero : ∑ r ∈ Finset.Ico (k + 1) (degree + 1), f r = 0 := by
      refine Finset.sum_eq_zero ?_
      intro r hr
      have hklt : k < r := (Finset.mem_Ico.mp hr).1
      change (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) = 0
      rw [Nat.choose_eq_zero_of_lt hklt]
      simp
    have hsplit :=
      Finset.sum_range_add_sum_Ico (f := f) (h := Nat.succ_le_succ (Nat.le_of_lt hdk'))
    calc
      scalarBernoulliLowerTail k degree p + scalarBernoulliTail k degree p
        = ∑ r ∈ Finset.range (degree + 1), f r := by
            rw [scalarBernoulliLowerTail, hTailZero, add_zero]
      _ = ∑ r ∈ Finset.range (k + 1), f r := by
            rw [hIcoZero, add_zero] at hsplit
            exact hsplit.symm
      _ = 1 := hfull

/-- The scalar Bernoulli tail satisfies the additive Hoeffding lower bound used by
`lem:chernoff-bernoulli-matrix`. -/
theorem scalarBernoulliTail_hoeffding_lower_bound
    (k degree : ℕ) {p : Error}
    (hpd : (degree : Error) / (k : Error) ≤ p) (hp1 : p ≤ 1) :
    1 - Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) * (k : Error))) ≤
      scalarBernoulliTail k degree p := by
  have hp0 : 0 ≤ p := by
    have hdk_nonneg : 0 ≤ (degree : Error) / (k : Error) := by
      positivity
    linarith
  have hLower := scalarBernoulliLowerTail_le_exp k degree hp0 hp1 hpd
  have hsum := scalarBernoulliLowerTail_add_scalarBernoulliTail k degree p
  linarith

/-- The paper's size condition `k ≥ 2d/θ` implies `d/k ≤ θ/2`. -/
private lemma degree_div_le_theta_half
    (theta : Error) (k degree : ℕ)
    (hθ0 : 0 < theta) (hk : (2 * (degree : Error)) / theta ≤ (k : Error)) :
    (degree : Error) / (k : Error) ≤ theta / 2 := by
  by_cases hk0 : k = 0
  · subst hk0
    have hdeg : degree = 0 := by
      by_contra hdeg
      have hdegpos : 0 < (degree : Error) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr hdeg
      have hfracpos : 0 < (2 * (degree : Error)) / theta := by
        positivity
      linarith
    subst hdeg
    have hnonneg : 0 ≤ theta / 2 := by
      positivity
    simpa using hnonneg
  · have hkpos : 0 < (k : Error) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hk0
    have hk' := hk
    field_simp [hθ0.ne', hkpos.ne'] at hk'
    have h2 : (2 * (degree : Error)) / (k : Error) ≤ theta := by
      rw [div_le_iff₀ hkpos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hk'
    have h2' : 2 * ((degree : Error) / (k : Error)) ≤ theta := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h2
    linarith



end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Scalar Bernoulli polynomial helpers for pasting

Purely scalar inequalities used by the matrix Chernoff comparison.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem solution
    (theta : _root_.LIDT.MIPStarRE.LDT.Error) (k degree : ℕ)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : _root_.LIDT.MIPStarRE.LDT.Error)) / theta ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error))
    {p : _root_.LIDT.MIPStarRE.LDT.Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine theta
      (Real.exp (-((theta ^ (2 : ℕ)) * (k : _root_.LIDT.MIPStarRE.LDT.Error)) / 2)) p ≤
        _root_.LIDT.MIPStarRE.LDT.Pasting.scalarBernoulliTail k degree p := by
  by_cases hpθ : p < theta
  · have htail_nonneg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.scalarBernoulliTail k degree p :=
      by
        unfold _root_.LIDT.MIPStarRE.LDT.Pasting.scalarBernoulliTail
        refine Finset.sum_nonneg ?_
        intro r hr
        apply mul_nonneg
        · exact_mod_cast Nat.zero_le (Nat.choose k r)
        · apply mul_nonneg
          · exact pow_nonneg hp0 _
          · exact pow_nonneg (sub_nonneg.mpr hp1) _
    have hθden : 0 < 1 - theta := sub_pos.mpr hθ1
    have hfrac_ge_one : 1 ≤ (1 - p) / (1 - theta) := by
      rw [one_le_div₀ hθden]
      linarith
    have hbase : 1 - (1 - p) / (1 - theta) ≤ 0 := by
      linarith
    have hexp_nonneg : 0 ≤ Real.exp (-((theta ^ (2 : ℕ)) * (k : _root_.LIDT.MIPStarRE.LDT.Error)) / 2) := by
      positivity
    have hLower :
        _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine theta
            (Real.exp (-((theta ^ (2 : ℕ)) * (k : _root_.LIDT.MIPStarRE.LDT.Error)) / 2)) p ≤ 0 := by
      unfold _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine
      have hrew : (1 / (1 - theta)) * (1 - p) = (1 - p) / (1 - theta) := by
        ring
      rw [hrew]
      linarith
    exact hLower.trans htail_nonneg
  · have hpθ' : theta ≤ p := le_of_not_gt hpθ
    have hdk_half : (degree : _root_.LIDT.MIPStarRE.LDT.Error) / (k : _root_.LIDT.MIPStarRE.LDT.Error) ≤ theta / 2 :=
      degree_div_le_theta_half theta k degree hθ0 hk
    have hdk_le_p : (degree : _root_.LIDT.MIPStarRE.LDT.Error) / (k : _root_.LIDT.MIPStarRE.LDT.Error) ≤ p := by
      linarith
    have hScalar := _root_.LIDT.MIPStarRE.LDT.Pasting.scalarBernoulliTail_hoeffding_lower_bound k degree hdk_le_p hp1
    have hk_nonneg : 0 ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) := by positivity
    have hpd_half : theta / 2 ≤ p - (degree : _root_.LIDT.MIPStarRE.LDT.Error) / (k : _root_.LIDT.MIPStarRE.LDT.Error) := by
      linarith
    have hsq : theta ^ (2 : ℕ) / 4 ≤ (p - (degree : _root_.LIDT.MIPStarRE.LDT.Error) / (k : _root_.LIDT.MIPStarRE.LDT.Error)) ^ (2 : ℕ) := by
      nlinarith [hpd_half, hθ0.le,
        sq_nonneg (p - (degree : _root_.LIDT.MIPStarRE.LDT.Error) / (k : _root_.LIDT.MIPStarRE.LDT.Error) - theta / 2)]
    have hExpCompare :
        Real.exp (-(2 * ((p - (degree : _root_.LIDT.MIPStarRE.LDT.Error) / (k : _root_.LIDT.MIPStarRE.LDT.Error)) ^ (2 : ℕ)) * (k : _root_.LIDT.MIPStarRE.LDT.Error))) ≤
          Real.exp (-((theta ^ (2 : ℕ)) * (k : _root_.LIDT.MIPStarRE.LDT.Error)) / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hsq, hk_nonneg]
    have hConst :
        1 - Real.exp (-((theta ^ (2 : ℕ)) * (k : _root_.LIDT.MIPStarRE.LDT.Error)) / 2) ≤
          1 - Real.exp (-(2 * ((p - (degree : _root_.LIDT.MIPStarRE.LDT.Error) / (k : _root_.LIDT.MIPStarRE.LDT.Error)) ^ (2 : ℕ)) *
            (k : _root_.LIDT.MIPStarRE.LDT.Error))) := by
      linarith
    have hθden : 0 < 1 - theta := sub_pos.mpr hθ1
    have hθinv_nonneg : 0 ≤ 1 / (1 - theta) := one_div_nonneg.mpr hθden.le
    have hp_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1
    have hterm_nonneg : 0 ≤ (1 / (1 - theta)) * (1 - p) :=
      mul_nonneg hθinv_nonneg hp_nonneg
    have hLowerConst :
        _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine theta
            (Real.exp (-((theta ^ (2 : ℕ)) * (k : _root_.LIDT.MIPStarRE.LDT.Error)) / 2)) p ≤
          1 - Real.exp (-((theta ^ (2 : ℕ)) * (k : _root_.LIDT.MIPStarRE.LDT.Error)) / 2) := by
      unfold _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine
      linarith
    exact hLowerConst.trans (hConst.trans hScalar)
