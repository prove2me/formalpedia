-- Prove2me | solution 1 for OAI.Problem367.IsingCopyResponseRowPaths.exists_actual_spatial_endpoint_constant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:47:21.424469+00:00
-- url     : https://prove2.me/submissions/7343aa00-4725-4834-9290-9a16a5bc8d37

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_IsingCopyResponseRowPaths_integral_actual_density_le_path_sums
import Theorems.Thm_OAI_Problem367_IsingCopySpectral_forwardOperator_pow_bound
import Theorems.Thm_OAI_Problem367_IsingCopySpectral_norm_cavityLogDifference_sq_le

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CopyDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.CopyDifference

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

theorem pullback_ae {μ : Measure A} {ν : Measure B} {p : B → A}
    (hp : MeasurePreserving p ν μ) (f : Lp ℝ 2 μ) :
    pullback hp f =ᵐ[ν] fun z => f (p z) :=
  Lp.coeFn_compMeasurePreserving f hp

theorem operator_ae {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (f : Lp ℝ 2 μ) :
    operator hp hq f =ᵐ[ν] fun z => f (p z) - f (q z) := by
  have hd := Lp.coeFn_sub (pullback hp f) (pullback hq f)
  exact hd.trans ((pullback_ae hp f).sub (pullback_ae hq f))

end Problem367.CopyDifference

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_Attenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma lipschitzWith_tanh_response : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_tanh_response x).differentiableAt
  · intro x
    have h : |deriv Real.tanh x| ≤ 1 := by
      rw [(hasDerivAt_tanh_response x).deriv,
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt (Real.tanh_sq_lt_one x)))]
      nlinarith [sq_nonneg (Real.tanh x)]
    exact_mod_cast h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_AttenuationMoments
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

lemma log_responseAttenuation_sub_sq_le {theta x y : ℝ} (hθ : theta ^ 2 ≤ 1) :
    (Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)) ^ 2 ≤
      4 * (x - y) ^ 2 := by
  have h := (lipschitzWith_log_responseAttenuation hθ).dist_le_mul x y
  have ha : |Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)| ≤
      2 * |x - y| := by simpa [Real.dist_eq] using h
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (abs_nonneg (x - y)))).mpr ha
  norm_num [mul_pow, sq_abs] at hs ⊢
  exact hs

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {theta : ℝ} {Y Y' : Ω → ℝ}

lemma integrable_log_responseAttenuation_sub_sq
    (hθ : theta ^ 2 ≤ 1) (hY : Measurable Y) (hY' : Measurable Y')
    (hInt : Integrable (fun w => (Y w - Y' w) ^ 2) μ) :
    Integrable (fun w =>
      (Real.log (responseAttenuation theta (Y w)) -
        Real.log (responseAttenuation theta (Y' w))) ^ 2) μ := by
  have hm : Measurable (fun x => Real.log (responseAttenuation theta x)) :=
    (lipschitzWith_log_responseAttenuation hθ).continuous.measurable
  apply (hInt.const_mul 4).mono'
    (((hm.comp hY).sub (hm.comp hY')).pow_const 2).aestronglyMeasurable
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact log_responseAttenuation_sub_sq_le hθ

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_AttenuationProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem prod_responseAttenuation_pos {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    {theta : ℝ} (htheta : theta ^ 2 ≤ 1) :
    0 < ∏ i ∈ s, responseAttenuation theta (z i) := by
  exact Finset.prod_pos (fun i _ => responseAttenuation_pos htheta (z i))

theorem prod_attenuation_le_one {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    {theta : ℝ} (htheta : theta ^ 2 ≤ 1) :
    ∏ i ∈ s, responseAttenuation theta (z i) ≤ 1 := by
  exact Finset.prod_le_one (fun index _ => le_of_lt (responseAttenuation_pos htheta (z index)))
    (fun i _ => responseAttenuation_le_one htheta (z i))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem summable_path_attenuation (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-a * n)) :=
  Real.summable_pow_mul_exp_neg_nat_mul k ha

theorem pow_le_factorial_mul_choose (n k : ℕ) :
    (n : ℝ) ^ k ≤ (k.factorial : ℝ) * ((n + k).choose k : ℝ) := by
  have h := (Nat.pow_le_choose (α := ℝ) k (n + k))
  have hnk : n + k + 1 - k = n + 1 := by omega
  rw [hnk] at h
  have hk : (0 : ℝ) < k.factorial := by positivity
  have h' : ((n + 1 : ℕ) : ℝ) ^ k ≤
      ((n + k).choose k : ℝ) * (k.factorial : ℝ) := by
    exact (div_le_iff₀ hk).mp h
  calc
    (n : ℝ) ^ k ≤ ((n + 1 : ℕ) : ℝ) ^ k := by gcongr; exact_mod_cast Nat.le_succ n
    _ ≤ (k.factorial : ℝ) * ((n + k).choose k : ℝ) := by simpa [mul_comm] using h'

theorem tsum_path_attenuation_le (k : ℕ) {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-a * n)) ≤
      (k.factorial : ℝ) / (1 - Real.exp (-a)) ^ (k + 1) := by
  have he : ‖Real.exp (-a)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hsum := (summable_choose_mul_geometric_of_norm_lt_one k he).mul_left
    (k.factorial : ℝ)
  have hle : (∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-a * n)) ≤
      ∑' n : ℕ, (k.factorial : ℝ) * (((n + k).choose k : ℝ) * Real.exp (-a) ^ n) := by
    apply Summable.tsum_le_tsum _ (summable_path_attenuation k ha) hsum
    intro n
    rw [show -a * (n : ℝ) = (n : ℝ) * -a by ring, Real.exp_nat_mul]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right
      (pow_le_factorial_mul_choose n k) (pow_nonneg (Real.exp_nonneg _) n)
  calc
    _ ≤ _ := hle
    _ = (k.factorial : ℝ) / (1 - Real.exp (-a)) ^ (k + 1) := by
      rw [tsum_mul_left, tsum_choose_mul_geometric_of_norm_lt_one k he]
      ring

theorem half_le_one_sub_exp_neg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    a / 2 ≤ 1 - Real.exp (-a) := by
  have hmul := mul_le_mul_of_nonneg_right (Real.add_one_le_exp a)
    (Real.exp_nonneg (-a))
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
  by_cases h : Real.exp (-a) ≤ 1 / 2
  · linarith
  · have h' : 1 / 2 ≤ Real.exp (-a) := le_of_not_ge h
    have := mul_le_mul_of_nonneg_left h' ha
    nlinarith

theorem tsum_path_attenuation_small_le (k : ℕ) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-a * n)) ≤
      (k.factorial : ℝ) * (2 / a) ^ (k + 1) := by
  have hgap := half_le_one_sub_exp_neg ha.le ha1
  have ha2 : 0 < a / 2 := by positivity
  have hgap0 : 0 < 1 - Real.exp (-a) := ha2.trans_le hgap
  have hinv : (1 - Real.exp (-a))⁻¹ ≤ 2 / a := by
    calc
      (1 - Real.exp (-a))⁻¹ ≤ (a / 2)⁻¹ := inv_anti₀ ha2 hgap
      _ = 2 / a := by field_simp
  calc
    _ ≤ (k.factorial : ℝ) / (1 - Real.exp (-a)) ^ (k + 1) :=
      tsum_path_attenuation_le k ha
    _ = (k.factorial : ℝ) * ((1 - Real.exp (-a))⁻¹) ^ (k + 1) := by
      rw [div_eq_mul_inv, inv_pow]
    _ ≤ (k.factorial : ℝ) * (2 / a) ^ (k + 1) := by gcongr

theorem tsum_linear_path_attenuation_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑' n : ℕ, (n : ℝ) * Real.exp (-a * n)) ≤ 4 / a ^ 2 := by
  simpa only [Nat.factorial_one, Nat.cast_one, pow_one, Nat.reduceAdd, one_mul,
    div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      tsum_path_attenuation_small_le 1 ha ha1

theorem sqrt_le_path_affine {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    Real.sqrt x ≤ (a * x + 1) / (2 * Real.sqrt a) := by
  have ha' : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq : (Real.sqrt a * Real.sqrt x) ^ 2 = a * x := by
    rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hx]
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt a)).mpr
  nlinarith [sq_nonneg (Real.sqrt a * Real.sqrt x - 1)]

theorem summable_sqrt_path_attenuation {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => Real.sqrt n * Real.exp (-a * n)) := by
  have hn : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-a * n)) := by
    simpa using summable_path_attenuation 1 ha
  have hg : Summable (fun n : ℕ => Real.exp (-a * n)) := by
    simpa using summable_path_attenuation 0 ha
  apply (hn.add hg).of_nonneg_of_le (fun n => by positivity)
  intro n
  have hs : Real.sqrt (n : ℝ) ≤ (n : ℝ) + 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ ((n : ℝ) + 1) * Real.exp (-a * n) :=
      mul_le_mul_of_nonneg_right hs (Real.exp_nonneg _)
    _ = _ := by ring

theorem tsum_sqrt_path_attenuation_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑' n : ℕ, Real.sqrt n * Real.exp (-a * n)) ≤ 3 / (a * Real.sqrt a) := by
  have hn : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-a * n)) := by
    simpa using summable_path_attenuation 1 ha
  have hg : Summable (fun n : ℕ => Real.exp (-a * n)) := by
    simpa using summable_path_attenuation 0 ha
  have hsum := ((hn.mul_left a).add hg).div_const (2 * Real.sqrt a)
  have hle : (∑' n : ℕ, Real.sqrt n * Real.exp (-a * n)) ≤
      ∑' n : ℕ, (a * ((n : ℝ) * Real.exp (-a * n)) + Real.exp (-a * n)) /
        (2 * Real.sqrt a) := by
    apply Summable.tsum_le_tsum _ (summable_sqrt_path_attenuation ha) hsum
    intro n
    calc
      _ ≤ ((a * (n : ℝ) + 1) / (2 * Real.sqrt a)) * Real.exp (-a * n) :=
        mul_le_mul_of_nonneg_right (sqrt_le_path_affine ha (Nat.cast_nonneg n))
          (Real.exp_nonneg _)
      _ = _ := by ring
  have hzero : (∑' n : ℕ, Real.exp (-a * n)) ≤ 2 / a := by
    simpa using tsum_path_attenuation_small_le 0 ha ha1
  calc
    _ ≤ _ := hle
    _ = (a * (∑' n : ℕ, (n : ℝ) * Real.exp (-a * n)) +
        (∑' n : ℕ, Real.exp (-a * n))) / (2 * Real.sqrt a) := by
      rw [tsum_div_const, (hn.mul_left a).tsum_add hg, tsum_mul_left]
    _ ≤ (a * (4 / a ^ 2) + 2 / a) / (2 * Real.sqrt a) := by
      gcongr
      exact tsum_linear_path_attenuation_le ha ha1
    _ = 3 / (a * Real.sqrt a) := by
      field_simp
      ring

theorem summable_superexponential_path (k : ℕ) {a q : ℝ}
    (ha : 0 < a) (hq : 1 < q) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-a * q ^ n)) := by
  have hrate : 0 < a * (q - 1) := mul_pos ha (sub_pos.mpr hq)
  apply (summable_path_attenuation k hrate).of_nonneg_of_le (fun n => by positivity)
  intro n
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have h := one_add_mul_sub_le_pow (show -1 ≤ q by linarith) n
  have h' : (n : ℝ) * (q - 1) ≤ q ^ n := by linarith
  nlinarith

theorem exp_neg_le_sq_of_log_cutoff {V K A : ℝ} (hV : 0 < V) (hK : 1 ≤ K)
    (hA : 2 * (1 + Real.log (K / V)) ≤ A) :
    Real.exp (-A) ≤ V ^ 2 := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  rw [Real.log_div hK0.ne' hV.ne'] at hA
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  calc
    Real.exp (-A) ≤ Real.exp (2 * Real.log V) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = V ^ 2 := by rw [two_mul, Real.exp_add, Real.exp_log hV]; ring

theorem superexponential_path_absorption {V K a q : ℝ} {n : ℕ}
    (hV : 0 < V) (hK : 1 ≤ K)
    (hcut : 2 * (1 + Real.log (K / V)) ≤ (a / 2) * q ^ n) :
    Real.exp (-a * q ^ n) ≤ V ^ 2 * Real.exp (-(a / 2) * q ^ n) := by
  have h := exp_neg_le_sq_of_log_cutoff hV hK hcut
  calc
    Real.exp (-a * q ^ n) =
        Real.exp (-((a / 2) * q ^ n)) * Real.exp (-(a / 2) * q ^ n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ V ^ 2 * Real.exp (-(a / 2) * q ^ n) :=
      mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem exists_path_cutoff_constant {a q : ℝ} (ha : 0 < a) (hq : 1 < q) (C₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ C₀ ≤ C ∧ 1 ≤ Real.log q * C ∧
      2 ≤ (a / 2) * q ^ C := by
  have hl : 0 < Real.log q := Real.log_pos hq
  let C := max C₀ (max (1 / Real.log q) (Real.log (4 / a) / Real.log q))
  have hC₀ : C₀ ≤ C := le_max_left _ _
  have hC₁ : 1 / Real.log q ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC₂ : Real.log (4 / a) / Real.log q ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, (one_div_pos.mpr hl).trans_le hC₁, hC₀, ?_, ?_⟩
  · have := (div_le_iff₀ hl).mp hC₁
    nlinarith
  · have hpow : 4 / a ≤ q ^ C := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans hq)]
      calc
        4 / a = Real.exp (Real.log (4 / a)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (Real.log q * C) := by
          apply Real.exp_le_exp.mpr
          have := (div_le_iff₀ hl).mp hC₂
          nlinarith
    have := mul_le_mul_of_nonneg_left hpow (show 0 ≤ a / 2 by positivity)
    have heq : (a / 2) * (4 / a) = 2 := by field_simp <;> ring
    rwa [heq] at this

theorem path_log_cutoff_bound {a q C I : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (hq : 1 < q) (hI : 1 ≤ I)
    (hC : 1 ≤ Real.log q * C) (hbase : 2 ≤ (a / 2) * q ^ C)
    (hcut : C * (1 + Real.log I) ≤ (n : ℝ)) :
    2 * I ≤ (a / 2) * q ^ n := by
  have hlq : 0 < Real.log q := Real.log_pos hq
  have hI0 : 0 < I := zero_lt_one.trans_le hI
  have hlI : 0 ≤ Real.log I := Real.log_nonneg hI
  have hexp : Real.log q * C + Real.log I ≤ Real.log q * n := by
    have h₁ := mul_le_mul_of_nonneg_left hcut hlq.le
    have h₂ := mul_le_mul_of_nonneg_right hC hlI
    nlinarith
  have hpow : q ^ C * I ≤ q ^ n := by
    calc
      q ^ C * I = Real.exp (Real.log q * C + Real.log I) := by
        rw [Real.exp_add, Real.exp_log hI0, Real.rpow_def_of_pos (zero_lt_one.trans hq)]
      _ ≤ Real.exp (Real.log q * n) := Real.exp_le_exp.mpr hexp
      _ = q ^ n := by rw [← Real.rpow_natCast, Real.rpow_def_of_pos (zero_lt_one.trans hq)]
  calc
    2 * I ≤ ((a / 2) * q ^ C) * I := mul_le_mul_of_nonneg_right hbase hI0.le
    _ = (a / 2) * (q ^ C * I) := by ring
    _ ≤ (a / 2) * q ^ n := mul_le_mul_of_nonneg_left hpow (by positivity)

theorem pathCutoff_le {C ω I : ℝ} (hC : 0 ≤ C) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hI : 1 ≤ I) :
    (pathCutoff C ω I : ℝ) ≤ (C + 1) * (ω⁻¹ + Real.log I) := by
  have hωinv : 1 ≤ ω⁻¹ := (one_le_inv₀ hω).mpr hω1
  have hlI : 0 ≤ Real.log I := Real.log_nonneg hI
  have hscale : 1 ≤ ω⁻¹ + Real.log I := by linarith
  have hnonneg : 0 ≤ C * (ω⁻¹ + Real.log I) := mul_nonneg hC (by linarith)
  have hceil := Nat.ceil_lt_add_one hnonneg
  change (Nat.ceil (C * (ω⁻¹ + Real.log I)) : ℝ) ≤ _
  nlinarith

theorem pathCutoff_log_bound {C ω I : ℝ} {n : ℕ} (hC : 0 ≤ C)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hn : pathCutoff C ω I ≤ n) :
    C * (1 + Real.log I) ≤ (n : ℝ) := by
  have hωinv : 1 ≤ ω⁻¹ := (one_le_inv₀ hω).mpr hω1
  calc
    C * (1 + Real.log I) ≤ C * (ω⁻¹ + Real.log I) := by gcongr
    _ ≤ (pathCutoff C ω I : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn

theorem pathCutoff_absorption {V K a q C ω : ℝ} {n : ℕ}
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K) (ha : 0 ≤ a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C)
    (hbase : 2 ≤ (a / 2) * q ^ C) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : pathCutoff C ω (1 + Real.log (K / V)) ≤ n) :
    Real.exp (-a * q ^ n) ≤ V ^ 2 * Real.exp (-(a / 2) * q ^ n) := by
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    have hratio : 1 ≤ K / V := (one_le_div hV).mpr hVK
    have := Real.log_nonneg hratio
    linarith
  apply superexponential_path_absorption hV hK
  apply path_log_cutoff_bound ha hq hI hC hbase
  exact pathCutoff_log_bound hC0 hω hω1 hn

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_EndpointSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter

namespace Problem367

theorem tsum_le_prefix_add_majorant {f g : ℕ → ℝ} (R : ℕ)
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g)
    (htail : ∀ n, R ≤ n → f n ≤ g n) :
    (∑' n, f n) ≤ (∑ n ∈ Finset.range R, f n) + ∑' n, g n := by
  have hf : Summable f := hg.of_norm_bounded_eventually_nat <|
    eventually_atTop.mpr ⟨R, fun n hn => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 n)]
      exact htail n hn⟩
  have hft : Summable (fun n => f (n + R)) := (summable_nat_add_iff R).mpr hf
  have hgt : Summable (fun n => g (n + R)) := (summable_nat_add_iff R).mpr hg
  calc
    (∑' n, f n) = (∑ n ∈ Finset.range R, f n) + ∑' n, f (n + R) :=
      (hf.sum_add_tsum_nat_add R).symm
    _ ≤ (∑ n ∈ Finset.range R, f n) + ∑' n, g (n + R) := by
      exact add_le_add le_rfl (hft.tsum_le_tsum
        (fun n => htail (n + R) (Nat.le_add_left R n)) hgt)
    _ ≤ (∑ n ∈ Finset.range R, f n) + ∑' n, g n := by
      apply add_le_add le_rfl
      exact tsum_comp_le_tsum_of_inj (i := fun n : ℕ => n + R) hg hg0
        (fun m n h => Nat.add_right_cancel h)

theorem sum_range_nat_pow_le (R k : ℕ) :
    (∑ n ∈ Finset.range R, (n : ℝ) ^ k) ≤ (R : ℝ) ^ (k + 1) := by
  calc
    _ ≤ ∑ _n ∈ Finset.range R, (R : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro n hn
      have h : (n : ℝ) ≤ R := by exact_mod_cast (Finset.mem_range.mp hn).le
      exact pow_le_pow_left₀ (Nat.cast_nonneg n) h k
    _ = (R : ℝ) ^ (k + 1) := by simp [pow_succ, mul_comm]

theorem sum_range_sqrt_le (R : ℕ) :
    (∑ n ∈ Finset.range R, Real.sqrt n) ≤ (R : ℝ) * Real.sqrt R := by
  calc
    _ ≤ ∑ _n ∈ Finset.range R, Real.sqrt R := by
      apply Finset.sum_le_sum
      intro n hn
      apply Real.sqrt_le_sqrt
      exact_mod_cast (Finset.mem_range.mp hn).le
    _ = (R : ℝ) * Real.sqrt R := by simp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_EndpointScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem endpoint_two_term_le {A B u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    A * u + B * v ≤ max A B * (u + v) := by
  calc
    A * u + B * v ≤ max A B * u + max A B * v :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hu)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hv)
    _ = _ := by ring

theorem cutoff_square_le {R K x y : ℝ} (hR0 : 0 ≤ R) (hK : 0 ≤ K)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hR : R ≤ K * (x + y)) :
    R ^ 2 ≤ 2 * K ^ 2 * (x ^ 2 + y ^ 2) := by
  calc
    R ^ 2 ≤ (K * (x + y)) ^ 2 :=
      (sq_le_sq₀ hR0 (mul_nonneg hK (add_nonneg hx hy))).mpr hR
    _ = K ^ 2 * (x + y) ^ 2 := by ring
    _ ≤ K ^ 2 * (2 * (x ^ 2 + y ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg K)
      nlinarith [sq_nonneg (x - y)]
    _ = _ := by ring

theorem add_mul_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) * Real.sqrt (x + y) ≤ 4 * (x * Real.sqrt x + y * Real.sqrt y) := by
  have haux : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u ≤ v →
      (u + v) * Real.sqrt (u + v) ≤ 4 * (u * Real.sqrt u + v * Real.sqrt v) := by
    intro u v hu hv huv
    have hsum : u + v ≤ 2 * v := by linarith
    have hsqrt : Real.sqrt (u + v) ≤ 2 * Real.sqrt v := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · rw [mul_pow, Real.sq_sqrt hv]
        nlinarith
    calc
      (u + v) * Real.sqrt (u + v) ≤ (2 * v) * (2 * Real.sqrt v) :=
        mul_le_mul hsum hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ ≤ 4 * (u * Real.sqrt u + v * Real.sqrt v) := by
        nlinarith [mul_nonneg hu (Real.sqrt_nonneg u)]
  rcases le_total x y with h | h
  · exact haux x y hx hy h
  · simpa [add_comm] using haux y x hy hx h

theorem cutoff_mul_sqrt_le {R K x y : ℝ} (_hR0 : 0 ≤ R) (hK : 0 ≤ K)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hR : R ≤ K * (x + y)) :
    R * Real.sqrt R ≤
      4 * K * Real.sqrt K * (x * Real.sqrt x + y * Real.sqrt y) := by
  calc
    R * Real.sqrt R ≤ (K * (x + y)) * Real.sqrt (K * (x + y)) :=
      mul_le_mul hR (Real.sqrt_le_sqrt hR) (Real.sqrt_nonneg _) (by positivity)
    _ = (K * Real.sqrt K) * ((x + y) * Real.sqrt (x + y)) := by
      rw [Real.sqrt_mul hK]
      ring
    _ ≤ (K * Real.sqrt K) * (4 * (x * Real.sqrt x + y * Real.sqrt y)) :=
      mul_le_mul_of_nonneg_left (add_mul_sqrt_add_le hx hy) (by positivity)
    _ = _ := by ring

theorem quadratic_endpoint_scale {F A B E S V R K x y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hR0 : 0 ≤ R) (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hR : R ≤ K * (x + y))
    (hF : F ≤ A * S * R ^ 2 + B * S * x ^ 2 + E * V ^ 2) :
    F ≤ max (2 * A * K ^ 2 + B) E *
      (S * (x ^ 2 + y ^ 2) + V ^ 2) := by
  have hfirst := mul_le_mul_of_nonneg_left (cutoff_square_le hR0 hK hx hy hR)
    (mul_nonneg hA hS)
  have hsecond : B * S * x ^ 2 ≤ B * S * (x ^ 2 + y ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB hS)
    nlinarith [sq_nonneg y]
  calc
    F ≤ A * S * (2 * K ^ 2 * (x ^ 2 + y ^ 2)) +
        B * S * (x ^ 2 + y ^ 2) + E * V ^ 2 :=
      hF.trans (add_le_add (add_le_add hfirst hsecond) le_rfl)
    _ = (2 * A * K ^ 2 + B) * (S * (x ^ 2 + y ^ 2)) + E * V ^ 2 := by ring
    _ ≤ _ := endpoint_two_term_le (by positivity) (sq_nonneg V)

theorem linear_endpoint_scale {F A B E V R K x y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hR : R ≤ K * (x + y))
    (hF : F ≤ A * V * R + B * V * x + E * V ^ 2) :
    F ≤ max (A * K + B) E * (V * (x + y) + V ^ 2) := by
  have hfirst := mul_le_mul_of_nonneg_left hR (mul_nonneg hA hV)
  have hsecond : B * V * x ≤ B * V * (x + y) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB hV)
    linarith
  calc
    F ≤ A * V * (K * (x + y)) + B * V * (x + y) + E * V ^ 2 :=
      hF.trans (add_le_add (add_le_add hfirst hsecond) le_rfl)
    _ = (A * K + B) * (V * (x + y)) + E * V ^ 2 := by ring
    _ ≤ _ := endpoint_two_term_le (by positivity) (sq_nonneg V)

theorem sqrt_endpoint_scale {F A B E S V R K x y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hR0 : 0 ≤ R) (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hR : R ≤ K * (x + y))
    (hF : F ≤ A * Real.sqrt S * (R * Real.sqrt R) +
      B * Real.sqrt S * (x * Real.sqrt x) + E * V) :
    F ≤ max (4 * A * K * Real.sqrt K + B) E *
      (Real.sqrt S * (x * Real.sqrt x + y * Real.sqrt y) + V) := by
  have hfirst := mul_le_mul_of_nonneg_left (cutoff_mul_sqrt_le hR0 hK hx hy hR)
    (mul_nonneg hA (Real.sqrt_nonneg S))
  have hsecond : B * Real.sqrt S * (x * Real.sqrt x) ≤
      B * Real.sqrt S * (x * Real.sqrt x + y * Real.sqrt y) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB (Real.sqrt_nonneg S))
    nlinarith [mul_nonneg hy (Real.sqrt_nonneg y)]
  calc
    F ≤ A * Real.sqrt S *
        (4 * K * Real.sqrt K * (x * Real.sqrt x + y * Real.sqrt y)) +
        B * Real.sqrt S * (x * Real.sqrt x + y * Real.sqrt y) + E * V :=
      hF.trans (add_le_add (add_le_add hfirst hsecond) le_rfl)
    _ = (4 * A * K * Real.sqrt K + B) *
        (Real.sqrt S * (x * Real.sqrt x + y * Real.sqrt y)) + E * V := by ring
    _ ≤ _ := endpoint_two_term_le (by positivity) hV

theorem tsum_scaled_path_attenuation_le (k : ℕ) {c ω : ℝ}
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) :
    (∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-(c * ω) * n)) ≤
      (k.factorial : ℝ) * (2 / min c 1) ^ (k + 1) * (ω⁻¹) ^ (k + 1) := by
  have hm : 0 < min c 1 := lt_min hc zero_lt_one
  have hrate : 0 < min c 1 * ω := mul_pos hm hω
  have hrate1 : min c 1 * ω ≤ 1 :=
    (mul_le_mul_of_nonneg_right (min_le_right c 1) hω.le).trans (by simpa using hω1)
  calc
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-(min c 1 * ω) * n) := by
      apply Summable.tsum_le_tsum _ (summable_path_attenuation k (mul_pos hc hω))
        (summable_path_attenuation k hrate)
      intro n
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right (min_le_left c 1) hω.le
      have := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) n)
      linarith
    _ ≤ (k.factorial : ℝ) * (2 / (min c 1 * ω)) ^ (k + 1) :=
      tsum_path_attenuation_small_le k hrate hrate1
    _ = _ := by simp [div_eq_mul_inv, mul_inv_rev, mul_pow, mul_assoc, mul_comm, mul_left_comm]

theorem tsum_scaled_sqrt_path_attenuation_le {c ω : ℝ}
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) :
    (∑' n : ℕ, Real.sqrt n * Real.exp (-(c * ω) * n)) ≤
      (3 / (min c 1 * Real.sqrt (min c 1))) * (ω⁻¹ * Real.sqrt (ω⁻¹)) := by
  have hm : 0 < min c 1 := lt_min hc zero_lt_one
  have hrate : 0 < min c 1 * ω := mul_pos hm hω
  have hrate1 : min c 1 * ω ≤ 1 :=
    (mul_le_mul_of_nonneg_right (min_le_right c 1) hω.le).trans (by simpa using hω1)
  calc
    _ ≤ ∑' n : ℕ, Real.sqrt n * Real.exp (-(min c 1 * ω) * n) := by
      apply Summable.tsum_le_tsum _ (summable_sqrt_path_attenuation (mul_pos hc hω))
        (summable_sqrt_path_attenuation hrate)
      intro n
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right (min_le_left c 1) hω.le
      have := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) n)
      linarith
    _ ≤ 3 / ((min c 1 * ω) * Real.sqrt (min c 1 * ω)) :=
      tsum_sqrt_path_attenuation_le hrate hrate1
    _ = _ := by
      rw [Real.sqrt_mul hm.le, Real.sqrt_inv]
      field_simp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_EndpointTimeScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem mul_sqrt_eq_three_halves {x : ℝ} (hx : 0 ≤ x) :
    x * Real.sqrt x = x ^ ((3 : ℝ) / 2) := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · norm_num
  calc
    x * Real.sqrt x = x ^ (1 : ℝ) * x ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_one, Real.sqrt_eq_rpow]
    _ = x ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hx _ _).symm
    _ = x ^ ((3 : ℝ) / 2) := by norm_num

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LocalColorAutomorphisms
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

lemma prefixColorList_on_subtree {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) :
    prefixColorList stem p (stem ++ w) = stem ++ w.map p := by
  induction stem with
  | nil => rfl
  | cons a r ih => simp [prefixColorList, ih]

lemma prefixColorList_eq_of_length_le {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) (hw : w.length ≤ stem.length) :
    prefixColorList stem p w = w := by
  induction stem generalizing w with
  | nil =>
    have hw' : w = [] := List.length_eq_zero_iff.mp (by simpa using hw)
    simp [hw']
  | cons a r ih =>
    cases w with
    | nil => simp
    | cons b w =>
      have hw' : w.length ≤ r.length := by simpa using hw
      by_cases h : a = b <;> simp [prefixColorList, h, ih w hw']

theorem prefixColorAut_fixes_ball {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    (u : TreeVertex d) (hu : u.1.length ≤ stem.length) :
    (prefixColorAut stem p hp).toEquiv u = u := by
  apply Subtype.ext
  exact prefixColorList_eq_of_length_le stem p u.1 hu

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ThresholdArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma branching_pos {d : ℕ} (hd : 3 ≤ d) : 0 < (d : ℝ) - 1 := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma threshold_sqrt_pos {d : ℕ} (hd : 3 ≤ d) :
    0 < Real.sqrt ((d : ℝ) - 1) :=
  Real.sqrt_pos.2 (branching_pos hd)

lemma threshold_iff_branching_sq {d : ℕ} {theta : ℝ}
    (hd : 3 ≤ d) (htheta : 0 ≤ theta) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
      ((d : ℝ) - 1) * theta ^ 2 ≤ 1 := by
  have hb := (branching_pos hd).le
  have hs := threshold_sqrt_pos hd
  calc
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
        theta * Real.sqrt ((d : ℝ) - 1) ≤ 1 := le_div_iff₀ hs
    _ ↔ (theta * Real.sqrt ((d : ℝ) - 1)) ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg htheta hs.le) (by norm_num)).symm
    _ ↔ ((d : ℝ) - 1) * theta ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt hb, one_pow, mul_comm]

lemma tanh_threshold_iff_branching_sq {d : ℕ} {beta : ℝ}
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta) :
    Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
      ((d : ℝ) - 1) * Real.tanh beta ^ 2 ≤ 1 :=
  threshold_iff_branching_sq hd (tanh_nonneg_of_beta_nonneg hbeta)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Transitivity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem exists_treeAut_to_root {d : ℕ} (u : TreeVertex d) :
    ∃ g : TreeAut d, g.toEquiv u = ⟨[], List.IsChain.nil⟩ := by
  rcases u with ⟨w, hw⟩
  induction w with
  | nil => exact ⟨TreeAut.refl d, rfl⟩
  | cons a w ih =>
    have hw' : w.IsChain (· ≠ ·) := hw.tail
    obtain ⟨g, hg⟩ := ih hw'
    refine ⟨(prefixTreeAut a).trans g, ?_⟩
    change g.toEquiv (prefixFlip a ⟨a :: w, hw⟩) = _
    have hflip : prefixFlip a ⟨a :: w, hw⟩ = ⟨w, hw'⟩ := by
      apply Subtype.ext
      simp [prefixFlip, prefixFlipWord]
    rw [hflip]
    exact hg

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyStationarity
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyStationarity

open IsingObservationInnovation IsingObservationFactor

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem posterior_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun x => posterior beta v t (relabel g x)) =ᵐ[observationLaw μ]
      posterior beta (g.toEquiv.symm v) t := by
  have hm (w : TreeVertex d) : Measurable (posterior beta w t) :=
    (measurable_infiniteGibbsSpinMean beta w).comp
      (Measurable.of_eval (fun i => measurable_evaluation i t))
  apply (ae_map_iff measurable_uniformObservation.aemeasurable
    (measurableSet_eq_fun ((hm v).comp (measurable_relabel g))
      (hm (g.toEquiv.symm v)))).mpr
  have hmB (s : ℝ≥0) : Measurable (fun u => WienerSampler.sample u s) :=
    WienerSampler.measurable_sample_eval.comp (measurable_const.prodMk measurable_id)
  have h := ArrayPosteriorStationarity.posterior_version_relabel_ae hμ uniform01
    (fun s u => WienerSampler.sample u s) hmB
    (fun s w => IsingInnovation.posterior_eq_condExp hμ uniform01
      WienerSampler.sample_isBrownianReal.toIsPreBrownianReal hmB s w) g t v
  exact h

omit [IsProbabilityMeasure μ] in
theorem field_array_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d) (t : ℝ≥0) :
    (fun x v => field beta v t (relabel g x)) =ᵐ[observationLaw μ]
      (fun x => relabel g (fun v => field beta v t x)) := by
  filter_upwards [ae_all_iff.mpr (fun v => posterior_relabel_ae hμ g t v)] with x hx
  funext v
  exact congrArg Real.artanh (hx v)

end Problem367.IsingCopyStationarity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Parents
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem treeAdj_length {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    v.1.length = u.1.length + 1 ∨ u.1.length = v.1.length + 1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · left; simp [hc]
  · right; simp [hc]

theorem treeAdj_parent_of_length_lt {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) (hlt : u.1.length < v.1.length) : parentVertex v = u := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply Subtype.ext
    simp [parentVertex, hc]
  · have hlen : u.1.length = v.1.length + 1 := by simp [hc]
    omega

theorem treeAdj_lower_unique {d : ℕ} {u v w : TreeVertex d}
    (hu : treeAdj u w) (hv : treeAdj v w)
    (huw : u.1.length < w.1.length) (hvw : v.1.length < w.1.length) : u = v := by
  exact (treeAdj_parent_of_length_lt hu huw).symm.trans
    (treeAdj_parent_of_length_lt hv hvw)

theorem treeAdj_parentVertex {d : ℕ} {v : TreeVertex d} (hv : v.1 ≠ []) :
    treeAdj (parentVertex v) v := by
  exact Or.inl ⟨v.1.getLast hv, (List.dropLast_append_getLast hv).symm⟩

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_WordAction
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeKoopman

theorem wordAut_root {d : ℕ} (w : List (Fin d))
    (hw : w.IsChain (· ≠ ·)) :
    (wordAut w).toEquiv ⟨[], List.IsChain.nil⟩ = ⟨w, hw⟩ := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change prefixFlip c ((wordAut w).toEquiv ⟨[], List.IsChain.nil⟩) = _
    rw [ih hw.tail]
    apply Subtype.ext
    cases w with
    | nil => rfl
    | cons a w =>
      simp [prefixFlip, prefixFlipWord, (List.isChain_cons_cons.mp hw).1]

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredEdgeLifts
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.pathValue_succ _root_.OAI.Problem367.ColoredPathAverage.pathValue_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped InnerProductSpace
namespace Problem367.ColoredEdgeLifts
variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {d : ℕ}

section Adjoint
variable [CompleteSpace E]

theorem tailLift_adjoint_apply (hd : 0 < d) (y : EdgeSpace d E) :
    (tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint y =
      (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • ∑ i, y i := by
  apply ext_inner_left 𝕜
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap, tailLift_apply, inner_smul_left, inner_smul_right, inner_sum,
    RCLike.conj_ofReal, Finset.mul_sum]

theorem forwardOperator_apply (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (r : ℝ) (y : EdgeSpace d E) (i : Fin d) :
    forwardOperator hd S r y i = (r : 𝕜) • ∑ j ∈ Finset.univ.erase i, S i (y j) := by
  change (((d : ℝ) * r : ℝ) : 𝕜) •
    (headLift hd S ((tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint y) i) -
      (r : 𝕜) • reversal S y i = _
  rw [headLift_apply, tailLift_adjoint_apply, map_smul, reversal_apply]
  simp only [smul_smul]
  have hscalar : (((d : ℝ) * r : ℝ) : 𝕜) *
      ((((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) * (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜)) = (r : 𝕜) := by
    have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
    norm_cast
    rw [← pow_two, inv_pow, Real.sq_sqrt hdreal.le]
    field_simp
  rw [hscalar, ← smul_sub, map_sum]
  congr 1
  exact (Finset.sum_erase_eq_sub (f := fun j => S i (y j)) (Finset.mem_univ i)).symm

end Adjoint

end Problem367.ColoredEdgeLifts

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredEdgeDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.ColoredEdgeLifts
open NonbacktrackingComplement

lemma degree_decay_parameters {d : ℕ} (hd : 3 ≤ d) :
    let q := (Real.sqrt ((d : ℝ) - 1))⁻¹
    0 < q ∧ q < 1 ∧ q ^ 2 = ((d : ℝ) - 1)⁻¹ ∧
      1 + q ^ 2 = (d : ℝ) * ((d : ℝ) - 1)⁻¹ ∧
      vertexRate q = 2 * Real.sqrt ((d : ℝ) - 1) / d := by
  dsimp only
  have hb := branching_pos hd
  have hs := threshold_sqrt_pos hd
  have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs2 := Real.sq_sqrt hb.le
  have hs1 : 1 < Real.sqrt ((d : ℝ) - 1) := by nlinarith
  have hq2 : (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ 2 = ((d : ℝ) - 1)⁻¹ := by
    rw [inv_pow, hs2]
  refine ⟨inv_pos.mpr hs, (inv_lt_one₀ hs).mpr hs1, hq2, ?_, ?_⟩
  · rw [hq2]
    field_simp
    ring
  · unfold vertexRate
    rw [hq2]
    field_simp
    nlinarith

end Problem367.ColoredEdgeLifts

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyObservables
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity PlantedSymmetry

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem cavityObservable_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun x => cavityObservable hbeta t v w (relabel g x)) =ᵐ[observationLaw μ]
      cavityObservable hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  filter_upwards [field_array_relabel_ae hμ g t] with x hx
  unfold cavityObservable
  rw [hx]
  rfl

theorem observableDifference_ae {f : Paths d → ℝ} (hf : MemLp f 2 (observationLaw μ)) :
    (observableDifference (beta := beta) hf : Lp ℝ 2 (copies beta μ)) =ᵐ[copies beta μ]
      (fun q => f q.2.1 - f q.2.2) := by
  obtain ⟨hp, hq⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  have h := CopyDifference.operator_ae hp hq (hf.toLp f)
  filter_upwards [h, hp.quasiMeasurePreserving.ae hf.coeFn_toLp,
    hq.quasiMeasurePreserving.ae hf.coeFn_toLp] with q hq' hl hr
  exact hq'.trans (congrArg₂ (fun a b : ℝ => a - b) hl hr)

theorem norm_observableDifference_sq {f : Paths d → ℝ} (hf : MemLp f 2 (observationLaw μ)) :
    ‖observableDifference (beta := beta) hf‖ ^ 2 =
      ∫ q, (f q.2.1 - f q.2.2) ^ 2 ∂copies beta μ := by
  change ‖(observableDifference (beta := beta) hf : Lp ℝ 2 (copies beta μ))‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [observableDifference_ae (beta := beta) hf] with q hq
  simp [hq, pow_two]

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyGeodesicCorrelations
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem cavityLogObservable_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun x => cavityLogObservable hbeta t v w (relabel g x)) =ᵐ[observationLaw μ]
      cavityLogObservable hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  filter_upwards [cavityObservable_relabel_ae hμ hbeta g t v w] with x hx
  exact congrArg (fun z => Real.log (responseAttenuation (Real.tanh beta) z)) hx

theorem cavityLogDifference_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun q => cavityLogDifference hbeta t v w (copyRelabel g q)) =ᵐ[copies beta μ]
      cavityLogDifference hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  filter_upwards [hl.quasiMeasurePreserving.ae
    (cavityLogObservable_relabel_ae hμ hbeta g t v w),
    hr.quasiMeasurePreserving.ae
    (cavityLogObservable_relabel_ae hμ hbeta g t v w)] with q hq hq'
  exact congrArg₂ (fun x y : ℝ => x - y) hq hq'

theorem memLp_cavityLogDifference
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    MemLp (cavityLogDifference hbeta t v w) 2 (copies beta μ) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  exact ((memLp_cavityLogObservable hμ hbeta t v w).comp_measurePreserving hl).sub
    ((memLp_cavityLogObservable hμ hbeta t v w).comp_measurePreserving hr)

theorem cavityLogVector_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    (cavityLogVector hμ hbeta t v w : Lp ℝ 2 (copies beta μ)) =ᵐ[copies beta μ]
      cavityLogDifference hbeta t v w :=
  observableDifference_ae (beta := beta) (memLp_cavityLogObservable hμ hbeta t v w)

theorem inner_cavityLogVector_eq_integral
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w u z : TreeVertex d) :
    inner ℝ (cavityLogVector hμ hbeta t v w) (cavityLogVector hμ hbeta t u z) =
      ∫ q, cavityLogDifference hbeta t v w q * cavityLogDifference hbeta t u z q
        ∂copies beta μ := by
  change inner ℝ (cavityLogVector hμ hbeta t v w : Lp ℝ 2 (copies beta μ))
    (cavityLogVector hμ hbeta t u z : Lp ℝ 2 (copies beta μ)) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cavityLogVector_ae hμ hbeta t v w,
    cavityLogVector_ae hμ hbeta t u z] with q hq hq'
  simp [hq, hq', mul_comm]

theorem inner_cavityLogVector_map
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w u z : TreeVertex d) :
    inner ℝ (cavityLogVector hμ hbeta t (g.toEquiv v) (g.toEquiv w))
      (cavityLogVector hμ hbeta t (g.toEquiv u) (g.toEquiv z)) =
    inner ℝ (cavityLogVector hμ hbeta t v w) (cavityLogVector hμ hbeta t u z) := by
  rw [inner_cavityLogVector_eq_integral, inner_cavityLogVector_eq_integral]
  have hmem := (memLp_cavityLogDifference hμ hbeta t v w).integrable_mul
    (memLp_cavityLogDifference hμ hbeta t u z)
  calc
    _ = ∫ q, cavityLogDifference hbeta t v w (copyRelabel g.symm q) *
        cavityLogDifference hbeta t u z (copyRelabel g.symm q) ∂copies beta μ := by
      apply integral_congr_ae
      filter_upwards [cavityLogDifference_relabel_ae hμ hbeta g.symm t v w,
        cavityLogDifference_relabel_ae hμ hbeta g.symm t u z] with q hq hq'
      exact (congrArg₂ (fun x y : ℝ => x * y) hq hq').symm
    _ = _ := (measurePreserving_copies_relabel hμ g.symm).hasLaw.integral_comp
      hmem.aestronglyMeasurable

theorem differenceReflection_cavityLogVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (c : Fin d) (t : ℝ≥0) (v w : TreeVertex d) :
    differenceReflection hμ c (cavityLogVector hμ hbeta t v w) =
      cavityLogVector hμ hbeta t (prefixFlip c v) (prefixFlip c w) := by
  apply Subtype.ext
  change koopmanL2 (copyRelabel (prefixTreeAut c))
    (measurePreserving_copies_relabel hμ (prefixTreeAut c))
    (cavityLogVector hμ hbeta t v w : Lp ℝ 2 (copies beta μ)) = _
  apply Lp.ext
  have hp := measurePreserving_copies_relabel hμ (prefixTreeAut c)
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (cavityLogVector hμ hbeta t v w : Lp ℝ 2 (copies beta μ)) hp,
    hp.quasiMeasurePreserving.ae (cavityLogVector_ae hμ hbeta t v w),
    cavityLogDifference_relabel_ae hμ hbeta (prefixTreeAut c) t v w,
    cavityLogVector_ae hμ hbeta t (prefixFlip c v) (prefixFlip c w)]
    with q hq hq' hq'' hq'''
  exact hq.trans (hq'.trans (hq''.trans hq'''.symm))

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedTransitivity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem exists_treeAut_map_common_stem {d : ℕ} (n : ℕ) :
    ∀ (stem s t : List (Fin d)) (_ : s.length = n) (_ : t.length = n)
      (hs : (stem ++ s).IsChain (· ≠ ·)) (_ : (stem ++ t).IsChain (· ≠ ·)),
    ∃ g : TreeAut d,
      (g.toEquiv ⟨stem ++ s, hs⟩).1 = stem ++ t ∧
      ∀ u : TreeVertex d, u.1.length ≤ stem.length → g.toEquiv u = u := by
  induction n with
  | zero =>
    intro stem s t hslen htlen hs ht
    have hs0 : s = [] := List.length_eq_zero_iff.mp hslen
    have ht0 : t = [] := List.length_eq_zero_iff.mp htlen
    subst s
    subst t
    exact ⟨TreeAut.refl d, rfl, fun _ _ => rfl⟩
  | succ n ih =>
    intro stem s t hslen htlen hs ht
    cases s with
    | nil => simp at hslen
    | cons a s =>
      cases t with
      | nil => simp at htlen
      | cons b t =>
        have hslen' : s.length = n := by simpa using hslen
        have htlen' : t.length = n := by simpa using htlen
        let p : Equiv.Perm (Fin d) := Equiv.swap a b
        have hp : ∀ c ∈ stem.getLast?, p c = c := by
          intro c hc
          apply Equiv.swap_apply_of_ne_of_ne
          · exact (List.isChain_append.mp hs).2.2 c hc a (by simp)
          · exact (List.isChain_append.mp ht).2.2 c hc b (by simp)
        let g₁ := prefixColorAut stem p hp
        have hmid : ((stem ++ [b]) ++ s.map p).IsChain (· ≠ ·) := by
          have h := (g₁.toEquiv ⟨stem ++ a :: s, hs⟩).2
          change (prefixColorList stem p (stem ++ a :: s)).IsChain (· ≠ ·) at h
          simpa [prefixColorList_on_subtree, p, List.append_assoc] using h
        have htarget : ((stem ++ [b]) ++ t).IsChain (· ≠ ·) := by
          simpa only [List.append_assoc, List.singleton_append] using ht
        obtain ⟨g₂, hg₂, hfix₂⟩ := ih (stem ++ [b]) (s.map p) t
          (by simpa using hslen') htlen' hmid htarget
        refine ⟨g₁.trans g₂, ?_, ?_⟩
        · have hg₁ : g₁.toEquiv ⟨stem ++ a :: s, hs⟩ =
              ⟨(stem ++ [b]) ++ s.map p, hmid⟩ := by
            apply Subtype.ext
            simp [g₁, prefixColorList_on_subtree, p, List.append_assoc]
          change (g₂.toEquiv (g₁.toEquiv ⟨stem ++ a :: s, hs⟩)).1 = _
          rw [hg₁, hg₂]
          simp [List.append_assoc]
        · intro u hu
          change g₂.toEquiv (g₁.toEquiv u) = u
          have hfix₁ : g₁.toEquiv u = u := prefixColorAut_fixes_ball stem p hp u hu
          rw [hfix₁]
          apply hfix₂
          simp only [List.length_append, List.length_singleton]
          omega

theorem exists_rootFixing_treeAut_map {d : ℕ} (u v : TreeVertex d)
    (hlen : u.1.length = v.1.length) :
    ∃ g : TreeAut d, g.toEquiv u = v ∧
      g.toEquiv ⟨[], List.IsChain.nil⟩ = ⟨[], List.IsChain.nil⟩ := by
  obtain ⟨g, hmap, hfix⟩ := exists_treeAut_map_common_stem u.1.length
    [] u.1 v.1 rfl hlen.symm u.2 v.2
  refine ⟨g, ?_, hfix ⟨[], List.IsChain.nil⟩ (by simp)⟩
  apply Subtype.ext
  exact hmap

theorem exists_treeAut_map_adjacent_pair {d : ℕ} {u v x y : TreeVertex d}
    (huv : treeAdj u v) (hxy : treeAdj x y) :
    ∃ g : TreeAut d, g.toEquiv u = x ∧ g.toEquiv v = y := by
  let root : TreeVertex d := ⟨[], List.IsChain.nil⟩
  have root_neighbor_length : ∀ w : TreeVertex d, treeAdj root w → w.1.length = 1 := by
    intro w hw
    rcases hw with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hl := congrArg List.length hc
      simpa [root] using hl
    · have hl := congrArg List.length hc
      simp [root] at hl
  obtain ⟨g, hgu⟩ := exists_treeAut_to_root u
  obtain ⟨h, hhx⟩ := exists_treeAut_to_root x
  have hgv : (g.toEquiv v).1.length = 1 := by
    apply root_neighbor_length
    dsimp only [root]
    rw [← hgu]
    exact (g.map_adj u v).2 huv
  have hhy : (h.toEquiv y).1.length = 1 := by
    apply root_neighbor_length
    dsimp only [root]
    rw [← hhx]
    exact (h.map_adj x y).2 hxy
  obtain ⟨k, hkv, hkroot⟩ := exists_rootFixing_treeAut_map (g.toEquiv v) (h.toEquiv y)
    (hgv.trans hhy.symm)
  refine ⟨(g.trans k).trans h.symm, ?_, ?_⟩
  · change h.toEquiv.symm (k.toEquiv (g.toEquiv u)) = x
    rw [hgu, hkroot, ← hhx]
    exact h.toEquiv.symm_apply_apply x
  · change h.toEquiv.symm (k.toEquiv (g.toEquiv v)) = y
    rw [hkv]
    exact h.toEquiv.symm_apply_apply y

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyEdgeVariance
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.pathValue_succ _root_.OAI.Problem367.ColoredPathAverage.pathValue_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor ColoredEdgeLifts

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem norm_cavityLogVector_sq_eq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    ‖cavityLogVector hμ hbeta t v w‖ ^ 2 =
      ∫ q, (cavityLogDifference hbeta t v w q) ^ 2 ∂copies beta μ := by
  rw [← real_inner_self_eq_norm_sq, inner_cavityLogVector_eq_integral]
  simp only [pow_two]

theorem norm_cavityLogVector_sq_eq_of_adj
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {u v x y : TreeVertex d} (huv : treeAdj u v) (hxy : treeAdj x y) :
    ‖cavityLogVector hμ hbeta t u v‖ ^ 2 =
      ‖cavityLogVector hμ hbeta t x y‖ ^ 2 := by
  obtain ⟨g, hgu, hgv⟩ := exists_treeAut_map_adjacent_pair huv hxy
  have h := inner_cavityLogVector_map hμ hbeta g t u v u v
  rw [hgu, hgv] at h
  simpa only [real_inner_self_eq_norm_sq] using h.symm

theorem norm_cavityLogEdgeVector_sq_eq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {u v : TreeVertex d} (huv : treeAdj u v) :
    ‖cavityLogEdgeVector hμ hbeta t‖ ^ 2 = (d : ℝ) *
      ∫ q, (cavityLogDifference hbeta t u v q) ^ 2 ∂copies beta μ := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ = ∑ _c : Fin d, ‖cavityLogVector hμ hbeta t u v‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      change ‖cavityLogVector hμ hbeta t TreeEscape.root
        (prefixFlip c TreeEscape.root)‖ ^ 2 = _
      exact norm_cavityLogVector_sq_eq_of_adj hμ hbeta t (Or.inl ⟨c, rfl⟩) huv
    _ = (d : ℝ) * ‖cavityLogVector hμ hbeta t u v‖ ^ 2 := by simp
    _ = _ := by rw [norm_cavityLogVector_sq_eq]

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredPathAverage
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.card_path _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace

namespace Problem367.ColoredPathAverage

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {d : ℕ}

theorem forwardOperator_pow_apply [CompleteSpace E]
    (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) (r : ℝ)
    (n : ℕ) (y : ColoredEdgeLifts.EdgeSpace d E) (i : Fin d) :
    (ColoredEdgeLifts.forwardOperator hd S r ^ n) y i =
      (r : 𝕜) ^ n • ∑ p : Path d n i, pathValue S y p := by
  induction n generalizing i with
  | zero =>
      change y i = (r : 𝕜) ^ 0 • ∑ _ : PUnit, y i
      simp
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp,
        ColoredEdgeLifts.forwardOperator_apply]
      simp_rw [ih, map_smul, map_sum]
      rw [← Finset.smul_sum, smul_smul, ← pow_succ']
      congr 1
      rw [show (∑ p : Path d (n + 1) i, pathValue S y p) =
          ∑ j : {j : Fin d // j ≠ i}, ∑ p : Path d n j.1, S i (pathValue S y p) from
        Fintype.sum_sigma _]
      exact Finset.sum_subtype (Finset.univ.erase i) (by simp) _

end Problem367.ColoredPathAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredPathEndpoints
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.card_path _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem prefixFlip_reduced_cons {d : ℕ} (c : Fin d) (w : List (Fin d))
    (h : (c :: w).IsChain (· ≠ ·)) :
    prefixFlip c ⟨w, h.tail⟩ = ⟨c :: w, h⟩ := by
  apply Subtype.ext
  cases w with
  | nil => rfl
  | cons a w =>
    simp [prefixFlip, prefixFlipWord, (List.isChain_cons_cons.mp h).1]

theorem prefixFlip_reduced_dropLast {d : ℕ} (c : Fin d) (w : List (Fin d))
    (h : (c :: w).IsChain (· ≠ ·)) (hw : w ≠ []) :
    prefixFlip c ⟨w.dropLast, h.tail.dropLast⟩ =
      ⟨(c :: w).dropLast, h.dropLast⟩ := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w =>
    cases w with
    | nil => rfl
    | cons b w =>
      apply Subtype.ext
      simp [prefixFlip, prefixFlipWord,
        (List.isChain_cons_cons.mp h).1]

namespace ColoredPathAverage

@[simp] theorem headVertex_succ {d n : ℕ} {i : Fin d} (p : Path d (n + 1) i) :
    headVertex p = prefixFlip i (headVertex p.2) := by
  symm
  exact prefixFlip_reduced_cons i (colors p.2) (colors_isChain p)

@[simp] theorem tailVertex_succ {d n : ℕ} {i : Fin d} (p : Path d (n + 1) i) :
    tailVertex p = prefixFlip i (tailVertex p.2) := by
  symm
  apply prefixFlip_reduced_dropLast i (colors p.2) (colors_isChain p)
  intro h
  have := colors_length p.2
  simp [h] at this

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem pathValue_eq_edgeVector {d : ℕ}
    (S : Fin d → E ≃ₗᵢ[𝕜] E) (A : TreeVertex d → TreeVertex d → E)
    (y : ColoredEdgeLifts.EdgeSpace d E)
    (hy : ∀ i, y i = A ⟨[], List.IsChain.nil⟩
      ⟨[i], List.IsChain.singleton i⟩)
    (hS : ∀ c v w, S c (A v w) = A (prefixFlip c v) (prefixFlip c w))
    {n : ℕ} {i : Fin d} (p : Path d n i) :
    pathValue S y p = A (tailVertex p) (headVertex p) := by
  induction n generalizing i with
  | zero => exact hy i
  | succ n ih =>
    rw [pathValue_succ, ih p.2, hS, tailVertex_succ, headVertex_succ]

end ColoredPathAverage

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyPathVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open ColoredPathAverage IsingObservationInnovation IsingObservationFactor

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem pathValue_cavityLogEdgeVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {n : ℕ} {i : Fin d} (p : Path d n i) :
    pathValue (differenceReflection hμ) (cavityLogEdgeVector hμ hbeta t) p =
      cavityLogVector hμ hbeta t (tailVertex p) (headVertex p) := by
  apply pathValue_eq_edgeVector
  · intro i
    rfl
  · intro c v w
    exact differenceReflection_cavityLogVector hμ hbeta c t v w

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredPathCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace

namespace Problem367.ColoredPathAverage
open ColoredEdgeLifts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] {d : ℕ}

theorem inner_forwardOperator_pow_component_eq (hd : 2 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (n : ℕ) (f : EdgeSpace d E)
    (i : Fin d) (c : ℝ)
    (h : ∀ p : Path d n i, inner ℝ (f i) (pathValue S f p) = c) :
    inner ℝ (f i)
      ((forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n) f i) = c := by
  rw [forwardOperator_pow_apply, inner_smul_right, inner_sum]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_path]
  have hd1 : 1 ≤ d := by omega
  have hb : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [Nat.cast_pow, Nat.cast_sub hd1, Nat.cast_one, ← mul_assoc,
    ← mul_pow, inv_mul_cancel₀ hb, one_pow, one_mul]

theorem inner_forwardOperator_pow_eq_card_mul (hd : 2 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (n : ℕ) (f : EdgeSpace d E) (c : ℝ)
    (h : ∀ (i : Fin d) (p : Path d n i),
      inner ℝ (f i) (pathValue S f p) = c) :
    inner ℝ f
      ((forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n) f) =
        (d : ℝ) * c := by
  rw [PiLp.inner_apply]
  simp only [inner_forwardOperator_pow_component_eq hd S n f _ c (h _),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem abs_pathCoefficient_le (hd : 2 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (n : ℕ) (f : EdgeSpace d E) (c B : ℝ)
    (h : ∀ (i : Fin d) (p : Path d n i),
      inner ℝ (f i) (pathValue S f p) = c)
    (hB : |inner ℝ f
      ((forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n) f)| ≤
        (d : ℝ) * B) : |c| ≤ B := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rw [inner_forwardOperator_pow_eq_card_mul hd S n f c h,
    abs_mul, abs_of_pos hdreal] at hB
  exact (mul_le_mul_iff_right₀ hdreal).mp hB

theorem abs_pathCoefficient_le_norm_pow (hd : 2 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (n : ℕ) (f : EdgeSpace d E) (c V : ℝ)
    (h : ∀ (i : Fin d) (p : Path d n i),
      inner ℝ (f i) (pathValue S f p) = c)
    (hsize : ‖f‖ ^ 2 ≤ (d : ℝ) * V) :
    |c| ≤ ‖forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n‖ * V := by
  apply abs_pathCoefficient_le hd S n f c _ h
  let A := forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n
  change |inner ℝ f (A f)| ≤ (d : ℝ) * (‖A‖ * V)
  calc
    |inner ℝ f (A f)| ≤ ‖f‖ * ‖A f‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) f (A f)
    _ ≤ ‖f‖ * (‖A‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm f) (norm_nonneg f)
    _ = ‖A‖ * ‖f‖ ^ 2 := by ring
    _ ≤ ‖A‖ * ((d : ℝ) * V) :=
      mul_le_mul_of_nonneg_left hsize (norm_nonneg A)
    _ = _ := by ring

end Problem367.ColoredPathAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathPrefix
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.headVertex_succ _root_.OAI.Problem367.ColoredPathAverage.tailVertex_succ _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

namespace TreeAut

private theorem length_le_of_root_eq {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d)
    (v : TreeVertex d) : (g.toEquiv v).1.length ≤ v.1.length := by
  suffices h : ∀ n (v : TreeVertex d), v.1.length = n →
      (g.toEquiv v).1.length ≤ n from h _ v rfl
  intro n
  induction n with
  | zero =>
      intro v hv
      have heq : v = ConnectedHull.root d :=
        Subtype.ext (List.length_eq_zero_iff.mp hv)
      rw [heq, hg]
      exact Nat.zero_le _
  | succ n ih =>
      intro v hv
      have hne : v.1 ≠ [] := by
        intro heq
        simp [heq] at hv
      have hp : (parentVertex v).1.length = n := by
        rw [parentVertex_length, hv]
        omega
      have hbound := ih (parentVertex v) hp
      have hadj := treeAdj_length
        ((g.map_adj _ _).mpr (treeAdj_parentVertex hne))
      omega

theorem length_eq_of_root_eq {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d)
    (v : TreeVertex d) : (g.toEquiv v).1.length = v.1.length := by
  have hsymm : g.symm.toEquiv (ConnectedHull.root d) = ConnectedHull.root d := by
    change g.toEquiv.symm (ConnectedHull.root d) = ConnectedHull.root d
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact hg.symm
  apply Nat.le_antisymm (length_le_of_root_eq g hg v)
  simpa only [TreeAut.symm, Equiv.symm_apply_apply] using
    length_le_of_root_eq g.symm hsymm (g.toEquiv v)

theorem map_takeVertex_of_length_preserving {d : ℕ} (g : TreeAut d)
    (hg : ∀ v, (g.toEquiv v).1.length = v.1.length)
    (v : TreeVertex d) (n : ℕ) :
    g.toEquiv (ConnectedHull.takeVertex v n) =
      ConnectedHull.takeVertex (g.toEquiv v) n := by
  by_cases hn : n ≤ v.1.length
  · induction hn using Nat.decreasingInduction with
    | self =>
        rw [ConnectedHull.prefix_length, ← hg v, ConnectedHull.prefix_length]
    | of_succ k hk ih =>
        apply treeAdj_lower_unique
          ((g.map_adj _ _).mpr (ConnectedHull.prefix_adj v hk))
        · rw [ih]
          apply ConnectedHull.prefix_adj
          rw [hg]
          exact hk
        · rw [hg, hg]
          simp only [ConnectedHull.takeVertex, List.length_take]
          omega
        · rw [hg]
          simp only [ConnectedHull.takeVertex, List.length_take, hg]
          omega
  · have hv : ConnectedHull.takeVertex v n = v := by
      apply Subtype.ext
      exact (List.take_eq_self_iff v.1).mpr (by omega)
    have hgv : ConnectedHull.takeVertex (g.toEquiv v) n = g.toEquiv v := by
      apply Subtype.ext
      apply (List.take_eq_self_iff (g.toEquiv v).1).mpr
      rw [hg]
      omega
    rw [hv, hgv]

theorem map_takeVertex_of_root_eq {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d)
    (v : TreeVertex d) (n : ℕ) :
    g.toEquiv (ConnectedHull.takeVertex v n) =
      ConnectedHull.takeVertex (g.toEquiv v) n :=
  map_takeVertex_of_length_preserving g (length_eq_of_root_eq g hg) v n

end TreeAut

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyFixedPathBound
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor
open ColoredEdgeLifts ColoredPathAverage ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem inner_rooted_cavityLogVector_eq_of_length_eq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (a b : TreeVertex d) (hlen : a.1.length = b.1.length) (n : ℕ) :
    inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex a 1))
      (cavityLogVector hμ hbeta t (takeVertex a n) a) =
    inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex b 1))
      (cavityLogVector hμ hbeta t (takeVertex b n) b) := by
  obtain ⟨g, hga, hgroot⟩ := exists_rootFixing_treeAut_map a b hlen
  have hgroot' : g.toEquiv (root d) = root d := hgroot
  have hfirst := g.map_takeVertex_of_root_eq hgroot' a 1
  have hlast := g.map_takeVertex_of_root_eq hgroot' a n
  rw [hga] at hfirst hlast
  have h := inner_cavityLogVector_map hμ hbeta g t (root d) (takeVertex a 1)
    (takeVertex a n) a
  rw [hgroot', hfirst, hlast, hga] at h
  exact h.symm

theorem inner_pathValue_eq_rooted_cavityLogVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {n : ℕ} {i : Fin d} (p : Path d n i)
    (v : TreeVertex d) (hlen : v.1.length = n + 1) :
    inner ℝ (cavityLogEdgeVector hμ hbeta t i)
      (pathValue (differenceReflection hμ) (cavityLogEdgeVector hμ hbeta t) p) =
    inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex v 1))
      (cavityLogVector hμ hbeta t (takeVertex v n) v) := by
  rw [pathValue_cavityLogEdgeVector]
  change inner ℝ (cavityLogVector hμ hbeta t (root d) (prefixFlip i TreeEscape.root))
    (cavityLogVector hμ hbeta t (tailVertex p) (headVertex p)) = _
  have hfirst : takeVertex (headVertex p) 1 = prefixFlip i TreeEscape.root := by
    cases n <;> apply Subtype.ext <;> rfl
  have htail : tailVertex p = takeVertex (headVertex p) n := by
    apply Subtype.ext
    change (colors p).dropLast = (colors p).take n
    rw [List.dropLast_eq_take, colors_length]
    simp
  rw [← hfirst, htail]
  apply inner_rooted_cavityLogVector_eq_of_length_eq hμ hbeta t _ v _ n
  simpa only [headVertex, colors_length] using hlen.symm

theorem abs_inner_rooted_cavityLogVector_le_norm_pow
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 2 ≤ d) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (n : ℕ) (v : TreeVertex d) (hlen : v.1.length = n + 1)
    {u w : TreeVertex d} (huw : treeAdj u w) :
    |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex v 1))
      (cavityLogVector hμ hbeta t (takeVertex v n) v)| ≤
      ‖forwardOperator (by omega : 0 < d) (differenceReflection hμ)
        ((d : ℝ) - 1)⁻¹ ^ n‖ *
        ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ := by
  apply abs_pathCoefficient_le_norm_pow hd (differenceReflection hμ) n
    (cavityLogEdgeVector hμ hbeta t)
  · intro i p
    exact inner_pathValue_eq_rooted_cavityLogVector hμ hbeta t p v hlen
  · exact (norm_cavityLogEdgeVector_sq_eq hμ hbeta t huw).le

theorem exists_rooted_cavityLogVector_correlation_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ≥0) (n : ℕ) (v : TreeVertex d),
      v.1.length = n + 1 → ∀ (u w : TreeVertex d), treeAdj u w →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex v 1))
        (cavityLogVector hμ hbeta t (takeVertex v n) v)| ≤
        (K * ((n : ℝ) + 1) * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n) *
          ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ := by
  obtain ⟨K, hK, hpow⟩ := forwardOperator_pow_bound hμ hd hbeta hthreshold
  refine ⟨K, hK, ?_⟩
  intro t n v hlen u w huw
  exact (abs_inner_rooted_cavityLogVector_le_norm_pow hμ (by omega) hbeta t n v
    hlen huw).trans (mul_le_mul_of_nonneg_right (hpow n)
      (integral_nonneg (fun q => sq_nonneg _)))

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367

theorem pathCorrelationKernel_nonneg {q : ℝ} (hq : 0 ≤ q) (k : ℤ) :
    0 ≤ pathCorrelationKernel q k := by
  unfold pathCorrelationKernel
  positivity

theorem summable_pathCorrelationKernel {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (pathCorrelationKernel q) := by
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hlin : Summable (fun n : ℕ => (n : ℝ) * q ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have hgeom : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hnat : Summable (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) := by
    simpa [add_mul] using hlin.add hgeom
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor <;> simpa [pathCorrelationKernel] using hnat

theorem tsum_pathCorrelationKernel {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' k, pathCorrelationKernel q k) = 2 / (1 - q) ^ 2 - 1 := by
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hnat : HasSum (fun n : ℕ => ((n : ℝ) + 1) * q ^ n)
      (1 / (1 - q) ^ 2) := by
    simpa using hasSum_choose_mul_geometric_of_norm_lt_one 1 hn
  have hpos : HasSum (fun n : ℕ => pathCorrelationKernel q (n : ℤ))
      (1 / (1 - q) ^ 2) := by
    simpa [pathCorrelationKernel] using hnat
  have hneg : HasSum (fun n : ℕ => pathCorrelationKernel q (-(n : ℤ)))
      (1 / (1 - q) ^ 2) := by
    simpa [pathCorrelationKernel] using hnat
  have h := (hpos.of_nat_of_neg hneg).tsum_eq
  simpa [pathCorrelationKernel, ← two_mul, div_eq_mul_inv] using h

open MeasureTheory

theorem integral_sum_sq_eq_sum_pair_moments
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) =
      ∑ i ∈ s, ∑ j ∈ s, ∫ ω, f i ω * f j ω ∂μ := by
  have hp : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun ω => f i ω * f j ω) μ := by
    intro i hi j hj
    exact (hf i hi).integrable_mul (hf j hj)
  calc
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) =
        ∫ ω, ∑ i ∈ s, ∑ j ∈ s, f i ω * f j ω ∂μ := by
      congr 1
      funext ω
      rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ ω, f i ω * f j ω ∂μ := by
      rw [integral_finsetSum s (fun i hi => integrable_finsetSum s (hp i hi))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum s (hp i hi)

theorem integral_sum_sq_le_card_mul_of_pair_rows
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → Ω → ℝ) {a : ι → ι → ℝ} {K : ℝ}
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, (∫ ω, f i ω * f j ω ∂μ) ≤ a i j)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, a i j ≤ K) :
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) ≤ (s.card : ℝ) * K := by
  rw [integral_sum_sq_eq_sum_pair_moments s f hf]
  calc
    ∑ i ∈ s, ∑ j ∈ s, ∫ ω, f i ω * f j ω ∂μ
        ≤ ∑ i ∈ s, ∑ j ∈ s, a i j :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpair i hi j hj
    _ ≤ ∑ _i ∈ s, K := Finset.sum_le_sum hrow
    _ = (s.card : ℝ) * K := by simp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_IndexedPathVariance
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Problem367

theorem sum_indexed_translate_le_tsum {ι : Type*}
    (s : Finset ι) (z : ι → ℤ) (hz : Set.InjOn z (s : Set ι))
    (i : ℤ) {c : ℤ → ℝ} (hc : ∀ k, 0 ≤ c k) (hsum : Summable c) :
    ∑ j ∈ s, c (z j - i) ≤ ∑' k, c k := by
  classical
  calc
    ∑ j ∈ s, c (z j - i) = ∑ k ∈ s.image (fun j => z j - i), c k := by
      symm
      apply Finset.sum_image
      intro a ha b hb hab
      apply hz ha hb
      exact sub_left_injective hab
    _ ≤ ∑' k, c k := Summable.sum_le_tsum _ (fun k _ => hc k) hsum

theorem integral_sum_sq_le_geometric_bound_of_injective_index
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (z : ι → ℤ) (hz : Set.InjOn z (s : Set ι))
    (f : ι → Ω → ℝ) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      |∫ ω, f i ω * f j ω ∂μ| ≤ S * pathCorrelationKernel q (z j - z i)) :
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) ≤
      (s.card : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  have h := integral_sum_sq_le_card_mul_of_pair_rows s f hf
    (fun i hi j hj => (le_abs_self _).trans (hpair i hi j hj))
    (K := S * ∑' k, pathCorrelationKernel q k) (fun i _ => by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_indexed_translate_le_tsum s z hz (z i)
        (pathCorrelationKernel_nonneg hq0) (summable_pathCorrelationKernel hq0 hq1)) hS)
  simpa only [tsum_pathCorrelationKernel hq0 hq1, mul_assoc] using h

theorem integral_sum_fin_sq_le_geometric_pair_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} (f : Fin n → Ω → ℝ) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hf : ∀ i, MemLp (f i) 2 μ)
    (hpair : ∀ i j, |∫ ω, f i ω * f j ω ∂μ| ≤
      S * pathCorrelationKernel q ((j : ℤ) - (i : ℤ))) :
    (∫ ω, (∑ i, f i ω) ^ 2 ∂μ) ≤
      (n : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  have hinj : Function.Injective (fun i : Fin n => (i : ℤ)) := by
    intro i j hij
    exact Fin.ext (Int.ofNat.inj hij)
  simpa using integral_sum_sq_le_geometric_bound_of_injective_index
    Finset.univ (fun i : Fin n => (i : ℤ)) hinj.injOn f hq0 hq1 hS
    (fun i _ => hf i) (fun i _ j _ => hpair i j)

theorem integral_sum_fin_sq_le_ordered_geometric_pair_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} (f : Fin n → Ω → ℝ) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hf : ∀ i, MemLp (f i) 2 μ)
    (hpair : ∀ i j, i ≤ j → |∫ ω, f i ω * f j ω ∂μ| ≤
      S * (((j.val - i.val : ℕ) : ℝ) + 1) * q ^ (j.val - i.val)) :
    (∫ ω, (∑ i, f i ω) ^ 2 ∂μ) ≤
      (n : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  apply integral_sum_fin_sq_le_geometric_pair_bound f hq0 hq1 hS hf
  intro i j
  by_cases hij : i ≤ j
  · simpa only [pathCorrelationKernel,
      Int.natAbs_natCast_sub_natCast_of_ge hij, mul_assoc] using hpair i j hij
  · have hji : j ≤ i := le_of_not_ge hij
    have heq : (∫ ω, f i ω * f j ω ∂μ) = ∫ ω, f j ω * f i ω ∂μ := by
      congr 1
      funext ω
      exact mul_comm _ _
    rw [heq]
    simpa only [pathCorrelationKernel,
      Int.natAbs_natCast_sub_natCast_of_le hji, mul_assoc] using hpair j i hji

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathRerooting
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.headVertex_succ _root_.OAI.Problem367.ColoredPathAverage.tailVertex_succ _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem stripPrefixAut_of_append {d : ℕ} (stem : List (Fin d))
    (v : TreeVertex d) (s : List (Fin d)) (hv : v.1 = stem ++ s) :
    ((stripPrefixAut stem).toEquiv v).1 = s := by
  induction stem generalizing v with
  | nil =>
    change v.1 = s
    simpa only [List.nil_append] using hv
  | cons a stem ih =>
    change ((stripPrefixAut stem).toEquiv (prefixFlip a v)).1 = s
    apply ih
    simp [prefixFlip, prefixFlipWord, hv]

theorem stripPrefixAut_eq_drop {d : ℕ} (stem : List (Fin d))
    (v : TreeVertex d) (hpre : stem <+: v.1) :
    ((stripPrefixAut stem).toEquiv v).1 = v.1.drop stem.length := by
  obtain ⟨s, hs⟩ := hpre
  rw [stripPrefixAut_of_append stem v s hs.symm, ← hs]
  simp

theorem stripPrefixAut_takeVertex {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hi : i ≤ v.1.length) (hij : i ≤ j) :
    (stripPrefixAut (v.1.take i)).toEquiv (ConnectedHull.takeVertex v j) =
      ConnectedHull.takeVertex (dropVertex v i) (j - i) := by
  apply Subtype.ext
  have hpre : v.1.take i <+: (ConnectedHull.takeVertex v j).1 := by
    change v.1.take i <+: v.1.take j
    simpa only [List.take_take, Nat.min_eq_left hij] using
      List.take_prefix i (v.1.take j)
  rw [stripPrefixAut_eq_drop _ _ hpre]
  simp only [ConnectedHull.takeVertex, dropVertex, List.length_take,
    Nat.min_eq_left hi, List.drop_take]

theorem exists_treeAut_reroot_subsegment {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    ∃ (w : TreeVertex d) (g : TreeAut d),
      w.1.length = j - i + 1 ∧
      ∀ k : ℕ, i ≤ k → k ≤ j + 1 →
        g.toEquiv (ConnectedHull.takeVertex v k) =
          ConnectedHull.takeVertex w (k - i) := by
  let w := ConnectedHull.takeVertex (dropVertex v i) (j - i + 1)
  refine ⟨w, stripPrefixAut (v.1.take i), ?_, ?_⟩
  · have hle : j - i + 1 ≤ v.1.length - i := by omega
    simp only [w, ConnectedHull.takeVertex, dropVertex, List.length_take,
      List.length_drop, Nat.min_eq_left hle]
  · intro k hik hkj
    rw [stripPrefixAut_takeVertex v (by omega) hik]
    apply Subtype.ext
    change (v.1.drop i).take (k - i) =
      ((v.1.drop i).take (j - i + 1)).take (k - i)
    rw [List.take_take, Nat.min_eq_left (by omega : k - i ≤ j - i + 1)]

theorem exists_treeAut_reroot_edge_pair {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    ∃ (w : TreeVertex d) (g : TreeAut d),
      w.1.length = j - i + 1 ∧
      g.toEquiv (ConnectedHull.takeVertex v i) = ConnectedHull.root d ∧
      g.toEquiv (ConnectedHull.takeVertex v (i + 1)) = ConnectedHull.takeVertex w 1 ∧
      g.toEquiv (ConnectedHull.takeVertex v j) = ConnectedHull.takeVertex w (j - i) ∧
      g.toEquiv (ConnectedHull.takeVertex v (j + 1)) = w := by
  obtain ⟨w, g, hlen, hmap⟩ := exists_treeAut_reroot_subsegment v hij hj
  refine ⟨w, g, hlen, ?_, ?_, hmap j hij (by omega), ?_⟩
  · simpa using hmap i le_rfl (by omega)
  · simpa using hmap (i + 1) (by omega) (by omega)
  · have h := hmap (j + 1) (by omega) le_rfl
    have hk : j + 1 - i = w.1.length := by omega
    rw [hk, ConnectedHull.prefix_length] at h
    exact h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_WordCancellation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.TreeKoopman

theorem wordAut_append_apply {d : ℕ} (u w : List (Fin d)) (v : TreeVertex d) :
    (wordAut (u ++ w)).toEquiv v =
      (wordAut u).toEquiv ((wordAut w).toEquiv v) := by
  induction u with
  | nil => rfl
  | cons c u ih =>
    change prefixFlip c ((wordAut (u ++ w)).toEquiv v) =
      prefixFlip c ((wordAut u).toEquiv ((wordAut w).toEquiv v))
    rw [ih]

theorem wordAut_reverse_left_apply {d : ℕ} (w : List (Fin d)) (v : TreeVertex d) :
    (wordAut w.reverse).toEquiv ((wordAut w).toEquiv v) = v := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [List.reverse_cons, wordAut_append_apply]
    change (wordAut w.reverse).toEquiv
      (prefixFlip c (prefixFlip c ((wordAut w).toEquiv v))) = v
    rw [prefixFlip_twice, ih]

theorem wordAut_reverse_right_apply {d : ℕ} (w : List (Fin d)) (v : TreeVertex d) :
    (wordAut w).toEquiv ((wordAut w.reverse).toEquiv v) = v := by
  simpa only [List.reverse_reverse] using wordAut_reverse_left_apply w.reverse v

theorem wordAut_append_reverse_suffix {d : ℕ} (u w : TreeVertex d) :
    (wordAut (u.1 ++ w.1)).toEquiv (reverseVertex w) = u := by
  rw [wordAut_append_apply]
  have hw : reverseVertex w =
      (wordAut w.1.reverse).toEquiv ⟨[], List.IsChain.nil⟩ :=
    (wordAut_root w.1.reverse (reverseVertex w).2).symm
  rw [hw, wordAut_reverse_right_apply, wordAut_root u.1 u.2]

theorem wordAut_apply_reverse_prefix {d : ℕ} (v : TreeVertex d) (k : ℕ) :
    (wordAut v.1).toEquiv (ConnectedHull.takeVertex (reverseVertex v) k) =
      ConnectedHull.takeVertex v (v.1.length - k) := by
  let u : TreeVertex d := ConnectedHull.takeVertex v (v.1.length - k)
  let w : TreeVertex d := ⟨v.1.drop (v.1.length - k), v.2.drop _⟩
  have hsplit : u.1 ++ w.1 = v.1 := List.take_append_drop _ _
  have hrev : ConnectedHull.takeVertex (reverseVertex v) k = reverseVertex w := by
    apply Subtype.ext
    exact List.take_reverse
  calc
    (wordAut v.1).toEquiv (ConnectedHull.takeVertex (reverseVertex v) k) =
        (wordAut (u.1 ++ w.1)).toEquiv (reverseVertex w) := by rw [hsplit, hrev]
    _ = u := wordAut_append_reverse_suffix u w

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathReverseRerooting
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.headVertex_succ _root_.OAI.Problem367.ColoredPathAverage.tailVertex_succ _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

open ConnectedHull

namespace TreeKoopman

theorem wordAut_reverse_apply_prefix {d : ℕ} (v : TreeVertex d) (k : ℕ) :
    (wordAut v.1.reverse).toEquiv (takeVertex v k) =
      takeVertex (reverseVertex v) (v.1.length - k) := by
  have h := wordAut_apply_reverse_prefix (reverseVertex v) k
  rw [reverseVertex_twice] at h
  simpa only [reverseVertex, List.length_reverse] using h

end TreeKoopman

theorem exists_treeAut_reverse_subsegment {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    ∃ (w : TreeVertex d) (g : TreeAut d),
      w.1.length = j - i + 1 ∧
      ∀ k : ℕ, i ≤ k → k ≤ j + 1 →
        g.toEquiv (takeVertex v k) = takeVertex w (j + 1 - k) := by
  obtain ⟨u, g, hlen, hmap⟩ := exists_treeAut_reroot_subsegment v hij hj
  let w := TreeKoopman.reverseVertex u
  let h := TreeKoopman.wordAut u.1.reverse
  refine ⟨w, g.trans h, ?_, ?_⟩
  · simpa only [w, TreeKoopman.reverseVertex, List.length_reverse] using hlen
  · intro k hik hkj
    change h.toEquiv (g.toEquiv (takeVertex v k)) = _
    rw [hmap k hik hkj]
    change (TreeKoopman.wordAut u.1.reverse).toEquiv (takeVertex u (k - i)) = _
    rw [TreeKoopman.wordAut_reverse_apply_prefix]
    have hindex : u.1.length - (k - i) = j + 1 - k := by omega
    rw [hindex]

theorem exists_treeAut_reroot_reverse_edge_pair {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    ∃ (w : TreeVertex d) (g : TreeAut d),
      w.1.length = j - i + 1 ∧
      g.toEquiv (takeVertex v (j + 1)) = root d ∧
      g.toEquiv (takeVertex v j) = takeVertex w 1 ∧
      g.toEquiv (takeVertex v (i + 1)) = takeVertex w (j - i) ∧
      g.toEquiv (takeVertex v i) = w := by
  obtain ⟨w, g, hlen, hmap⟩ := exists_treeAut_reverse_subsegment v hij hj
  refine ⟨w, g, hlen, ?_, ?_, ?_, ?_⟩
  · simpa using hmap (j + 1) (by omega) le_rfl
  · simpa using hmap j hij (by omega)
  · have h := hmap (i + 1) (by omega) (by omega)
    have hindex : j + 1 - (i + 1) = j - i := by omega
    simpa only [hindex] using h
  · have h := hmap i le_rfl (by omega)
    have hindex : j + 1 - i = w.1.length := by omega
    rw [hindex, prefix_length] at h
    exact h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyPathVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor
open ConnectedHull
open scoped NNReal

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

private theorem inner_path_pair_bound_of_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {K q S : ℝ}
    (hroot : ∀ (n : ℕ) (w : TreeVertex d), w.1.length = n + 1 →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex w 1))
        (cavityLogVector hμ hbeta t (takeVertex w n) w)| ≤
          K * ((n : ℝ) + 1) * q ^ n * S)
    (v : TreeVertex d) {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    |inner ℝ (cavityLogVector hμ hbeta t (takeVertex v i) (takeVertex v (i + 1)))
      (cavityLogVector hμ hbeta t (takeVertex v j) (takeVertex v (j + 1)))| ≤
        (K * S) * pathCorrelationKernel q ((j : ℤ) - (i : ℤ)) := by
  obtain ⟨w, g, hlen, hi, hi1, hj0, hj1⟩ :=
    exists_treeAut_reroot_edge_pair v hij hj
  have hm := inner_cavityLogVector_map hμ hbeta g t
    (takeVertex v i) (takeVertex v (i + 1))
    (takeVertex v j) (takeVertex v (j + 1))
  rw [hi, hi1, hj0, hj1] at hm
  rw [← hm]
  have hlag : ((j : ℤ) - (i : ℤ)).natAbs = j - i := by
    rw [← Int.natCast_sub hij]
    rfl
  calc
    _ ≤ K * (((j - i : ℕ) : ℝ) + 1) * q ^ (j - i) * S := hroot _ w hlen
    _ = _ := by rw [pathCorrelationKernel, hlag]; ring

private theorem inner_reverse_path_pair_bound_of_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {K q S : ℝ}
    (hroot : ∀ (n : ℕ) (w : TreeVertex d), w.1.length = n + 1 →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex w 1))
        (cavityLogVector hμ hbeta t (takeVertex w n) w)| ≤
          K * ((n : ℝ) + 1) * q ^ n * S)
    (v : TreeVertex d) {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    |inner ℝ (cavityLogVector hμ hbeta t (takeVertex v (i + 1)) (takeVertex v i))
      (cavityLogVector hμ hbeta t (takeVertex v (j + 1)) (takeVertex v j))| ≤
        (K * S) * pathCorrelationKernel q ((j : ℤ) - (i : ℤ)) := by
  obtain ⟨w, g, hlen, hi, hi1, hj0, hj1⟩ :=
    exists_treeAut_reroot_reverse_edge_pair v hij hj
  have hm := inner_cavityLogVector_map hμ hbeta g t
    (takeVertex v (j + 1)) (takeVertex v j)
    (takeVertex v (i + 1)) (takeVertex v i)
  rw [hi, hi1, hj0, hj1] at hm
  rw [real_inner_comm, ← hm]
  have hlag : ((j : ℤ) - (i : ℤ)).natAbs = j - i := by
    rw [← Int.natCast_sub hij]
    rfl
  calc
    _ ≤ K * (((j - i : ℕ) : ℝ) + 1) * q ^ (j - i) * S := hroot _ w hlen
    _ = _ := by rw [pathCorrelationKernel, hlag]; ring

private theorem integral_image_path_sq_bound_of_root_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {K q S : ℝ} (hK : 0 ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hS : 0 ≤ S)
    (hroot : ∀ (n : ℕ) (w : TreeVertex d), w.1.length = n + 1 →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex w 1))
        (cavityLogVector hμ hbeta t (takeVertex w n) w)| ≤
          K * ((n : ℝ) + 1) * q ^ n * S)
    (g : TreeAut d) (v : TreeVertex d) :
    (∫ ω, (∑ i : Fin v.1.length, cavityLogDifference hbeta t
      (g.toEquiv (takeVertex v i)) (g.toEquiv (takeVertex v (i + 1))) ω) ^ 2
        ∂copies beta μ) ≤
      (K * (2 / (1 - q) ^ 2 - 1)) * (v.1.length : ℝ) * S := by
  have h := integral_sum_fin_sq_le_ordered_geometric_pair_bound
    (fun i => cavityLogDifference hbeta t
      (g.toEquiv (takeVertex v i)) (g.toEquiv (takeVertex v (i + 1))))
    hq0 hq1 (mul_nonneg hK hS)
    (fun i => memLp_cavityLogDifference hμ hbeta t _ _)
    (fun i j hij => by
      rw [← inner_cavityLogVector_eq_integral hμ hbeta t,
        inner_cavityLogVector_map]
      have hpair := inner_path_pair_bound_of_le hμ hbeta t hroot v hij j.isLt
      simpa only [pathCorrelationKernel,
        Int.natAbs_natCast_sub_natCast_of_ge hij, mul_assoc] using hpair)
  calc
    _ ≤ (v.1.length : ℝ) * (K * S) * (2 / (1 - q) ^ 2 - 1) := h
    _ = _ := by ring

private theorem integral_image_reverse_path_sq_bound_of_root_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {K q S : ℝ} (hK : 0 ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hS : 0 ≤ S)
    (hroot : ∀ (n : ℕ) (w : TreeVertex d), w.1.length = n + 1 →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex w 1))
        (cavityLogVector hμ hbeta t (takeVertex w n) w)| ≤
          K * ((n : ℝ) + 1) * q ^ n * S)
    (g : TreeAut d) (v : TreeVertex d) :
    (∫ ω, (∑ i : Fin v.1.length, cavityLogDifference hbeta t
      (g.toEquiv (takeVertex v (i + 1))) (g.toEquiv (takeVertex v i)) ω) ^ 2
        ∂copies beta μ) ≤
      (K * (2 / (1 - q) ^ 2 - 1)) * (v.1.length : ℝ) * S := by
  have h := integral_sum_fin_sq_le_ordered_geometric_pair_bound
    (fun i => cavityLogDifference hbeta t
      (g.toEquiv (takeVertex v (i + 1))) (g.toEquiv (takeVertex v i)))
    hq0 hq1 (mul_nonneg hK hS)
    (fun i => memLp_cavityLogDifference hμ hbeta t _ _)
    (fun i j hij => by
      rw [← inner_cavityLogVector_eq_integral hμ hbeta t,
        inner_cavityLogVector_map]
      have hpair := inner_reverse_path_pair_bound_of_le hμ hbeta t hroot v hij j.isLt
      simpa only [pathCorrelationKernel,
        Int.natAbs_natCast_sub_natCast_of_ge hij, mul_assoc] using hpair)
  calc
    _ ≤ (v.1.length : ℝ) * (K * S) * (2 / (1 - q) ^ 2 - 1) := h
    _ = _ := by ring

theorem exists_cavityLog_path_variance_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w →
      ∀ (g : TreeAut d) (v : TreeVertex d),
      ((∫ ω, (∑ i : Fin v.1.length, cavityLogDifference hbeta t
          (g.toEquiv (takeVertex v i)) (g.toEquiv (takeVertex v (i + 1))) ω) ^ 2
            ∂copies beta μ) ≤
        C * (v.1.length : ℝ) *
          ∫ ω, (cavityLogDifference hbeta t u w ω) ^ 2 ∂copies beta μ) ∧
      ((∫ ω, (∑ i : Fin v.1.length, cavityLogDifference hbeta t
          (g.toEquiv (takeVertex v (i + 1))) (g.toEquiv (takeVertex v i)) ω) ^ 2
            ∂copies beta μ) ≤
        C * (v.1.length : ℝ) *
          ∫ ω, (cavityLogDifference hbeta t u w ω) ^ 2 ∂copies beta μ) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_rooted_cavityLogVector_correlation_bound hμ hd hbeta hthreshold
  let q := (Real.sqrt ((d : ℝ) - 1))⁻¹
  have hq0 : 0 ≤ q := (ColoredEdgeLifts.degree_decay_parameters hd).1.le
  have hq1 : q < 1 := (ColoredEdgeLifts.degree_decay_parameters hd).2.1
  have hmass : 0 ≤ 2 / (1 - q) ^ 2 - 1 := by
    rw [← tsum_pathCorrelationKernel hq0 hq1]
    exact tsum_nonneg (pathCorrelationKernel_nonneg hq0)
  refine ⟨K * (2 / (1 - q) ^ 2 - 1), mul_nonneg hK hmass, ?_⟩
  intro t u w huw g v
  have hS : 0 ≤ ∫ ω, (cavityLogDifference hbeta t u w ω) ^ 2 ∂copies beta μ :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hroot := fun n x hx => hbound t n x hx u w huw
  exact ⟨integral_image_path_sq_bound_of_root_bound hμ hbeta t hK hq0 hq1 hS
      hroot g v,
    integral_image_reverse_path_sq_bound_of_root_bound hμ hbeta t hK hq0 hq1 hS
      hroot g v⟩

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CoupledPathProducts
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

private theorem sub_le_mul_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - b ≤ a * (Real.log a - Real.log b) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h ha.le
  have hcancel : a * (b / a) = b := by field_simp
  nlinarith

theorem abs_sub_le_max_mul_abs_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a - b| ≤ max a b * |Real.log a - Real.log b| := by
  rcases le_total b a with hba | hab
  · rw [max_eq_left hba, abs_of_nonneg (sub_nonneg.mpr hba),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb hba))]
    exact sub_le_mul_log_sub ha hb
  · rw [max_eq_right hab, abs_of_nonpos (sub_nonpos.mpr hab),
      abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ha hab))]
    have h := sub_le_mul_log_sub hb ha
    nlinarith

theorem positive_sub_sq_le_log_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) ^ 2 ≤ (a ^ 2 + b ^ 2) * (Real.log a - Real.log b) ^ 2 := by
  have h := abs_sub_le_max_mul_abs_log_sub ha hb
  have hmax : 0 ≤ max a b := le_trans ha.le (le_max_left _ _)
  have hs := (sq_le_sq₀ (abs_nonneg (a - b))
    (mul_nonneg hmax (abs_nonneg _))).2 h
  rw [sq_abs, mul_pow, sq_abs] at hs
  have hmaxsq : (max a b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases le_total b a with hba | hab
    · rw [max_eq_left hba]
      nlinarith [sq_nonneg b]
    · rw [max_eq_right hab]
      nlinarith [sq_nonneg a]
  exact hs.trans (mul_le_mul_of_nonneg_right hmaxsq (sq_nonneg _))

theorem log_prod_responseAttenuation_sub {ι : Type*} (s : Finset ι)
    (x y : ι → ℝ) {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    Real.log (∏ i ∈ s, responseAttenuation theta (x i)) -
        Real.log (∏ i ∈ s, responseAttenuation theta (y i)) =
      ∑ i ∈ s, (Real.log (responseAttenuation theta (x i)) -
        Real.log (responseAttenuation theta (y i))) := by
  rw [Real.log_prod (fun i _ => (responseAttenuation_pos hθ (x i)).ne'),
    Real.log_prod (fun i _ => (responseAttenuation_pos hθ (y i)).ne'),
    Finset.sum_sub_distrib]

theorem prod_responseAttenuation_sub_sq_le {ι : Type*} (s : Finset ι)
    (x y : ι → ℝ) {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    ((∏ i ∈ s, responseAttenuation theta (x i)) -
        (∏ i ∈ s, responseAttenuation theta (y i))) ^ 2 ≤
      ((∏ i ∈ s, responseAttenuation theta (x i)) ^ 2 +
        (∏ i ∈ s, responseAttenuation theta (y i)) ^ 2) *
      (∑ i ∈ s, (Real.log (responseAttenuation theta (x i)) -
        Real.log (responseAttenuation theta (y i)))) ^ 2 := by
  have h := positive_sub_sq_le_log_weight
    (prod_responseAttenuation_pos s x hθ) (prod_responseAttenuation_pos s y hθ)
  rwa [log_prod_responseAttenuation_sub s x y hθ] at h

section Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem measurable_responseAttenuation (theta : ℝ) : Measurable (responseAttenuation theta) := by
  have ht : Measurable Real.tanh := lipschitzWith_tanh_response.continuous.measurable
  exact (measurable_const.sub (ht.pow_const 2)).div
    (measurable_const.sub (measurable_const.mul (ht.pow_const 2)))

theorem measurable_prod_responseAttenuation (s : Finset ι) (theta : ℝ)
    {X : ι → Ω → ℝ} (hX : ∀ i ∈ s, Measurable (X i)) :
    Measurable (fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)) :=
  s.measurable_prod (fun i hi => (measurable_responseAttenuation theta).comp (hX i hi))

theorem memLp_sum_log_responseAttenuation_sub (s : Finset ι)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) {X Y : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ) :
    MemLp (fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))) 2 μ := by
  apply memLp_finsetSum s
  intro i hi
  have hm := (lipschitzWith_log_responseAttenuation hθ).continuous.measurable
  exact (memLp_two_iff_integrable_sq
    (((hm.comp (hX i hi)).sub (hm.comp (hY i hi))).aestronglyMeasurable)).2
      (integrable_log_responseAttenuation_sub_sq hθ (hX i hi) (hY i hi) (hInt i hi))

theorem integral_prod_responseAttenuation_sub_sq_le (s : Finset ι)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) {X Y : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ) :
    let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
    let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
    let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))
    Integrable (fun ω => (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2) μ ∧
      Integrable (fun ω => (P ω - P' ω) ^ 2) μ ∧
      (∫ ω, (P ω - P' ω) ^ 2 ∂μ) ≤
        ∫ ω, (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 ∂μ := by
  dsimp only
  let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
  let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
  let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))
  have hP : Measurable P := measurable_prod_responseAttenuation s theta hX
  have hP' : Measurable P' := measurable_prod_responseAttenuation s theta hY
  have hZ : MemLp Z 2 μ := memLp_sum_log_responseAttenuation_sub s hθ hX hY hInt
  have hweight (ω : Ω) : P ω ^ 2 + P' ω ^ 2 ≤ 2 := by
    have hp := prod_responseAttenuation_pos s (fun i => X i ω) hθ
    have hp' := prod_responseAttenuation_pos s (fun i => Y i ω) hθ
    have hl := prod_attenuation_le_one s (fun i => X i ω) hθ
    have hl' := prod_attenuation_le_one s (fun i => Y i ω) hθ
    change P ω > 0 at hp
    change P' ω > 0 at hp'
    change P ω ≤ 1 at hl
    change P' ω ≤ 1 at hl'
    nlinarith
  have hQ : Integrable (fun ω => (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2) μ := by
    apply (hZ.integrable_sq.const_mul 2).mono'
      (((hP.pow_const 2).add (hP'.pow_const 2)).aestronglyMeasurable.mul
        (hZ.aestronglyMeasurable.pow 2))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hweight ω) (sq_nonneg _)
  have hpoint (ω : Ω) : (P ω - P' ω) ^ 2 ≤ (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 :=
    prod_responseAttenuation_sub_sq_le s (fun i => X i ω) (fun i => Y i ω) hθ
  have hDiff : Integrable (fun ω => (P ω - P' ω) ^ 2) μ := by
    apply hQ.mono' (((hP.sub hP').pow_const 2).aestronglyMeasurable)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint ω
  exact ⟨hQ, hDiff, integral_mono hDiff hQ hpoint⟩

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CoupledPathVariance
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_weighted_path_log_sq_le_twice_unweighted
    {ι : Type*} (s : Finset ι) {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    {X Y : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ) :
    (∫ ω, ((∏ i ∈ s, responseAttenuation theta (X i ω)) ^ 2 +
      (∏ i ∈ s, responseAttenuation theta (Y i ω)) ^ 2) *
      (∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
        Real.log (responseAttenuation theta (Y i ω)))) ^ 2 ∂μ) ≤
      2 * ∫ ω, (∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
        Real.log (responseAttenuation theta (Y i ω)))) ^ 2 ∂μ := by
  have hQ := (integral_prod_responseAttenuation_sub_sq_le s hθ hX hY hInt).1
  have hZ := memLp_sum_log_responseAttenuation_sub s hθ hX hY hInt
  calc
    _ ≤ ∫ ω, 2 * (∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
        Real.log (responseAttenuation theta (Y i ω)))) ^ 2 ∂μ := by
      apply integral_mono hQ (hZ.integrable_sq.const_mul 2)
      intro ω
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hp := prod_responseAttenuation_pos s (fun i => X i ω) hθ
      have hp' := prod_responseAttenuation_pos s (fun i => Y i ω) hθ
      have hl := prod_attenuation_le_one s (fun i => X i ω) hθ
      have hl' := prod_attenuation_le_one s (fun i => Y i ω) hθ
      nlinarith
    _ = _ := integral_const_mul _ _

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyProductVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem memLp_cavityObservable_difference
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    MemLp (fun q => cavityObservable hbeta t v w q.2.1 -
      cavityObservable hbeta t v w q.2.2) 2 (copies beta μ) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  exact ((memLp_cavityObservable hμ hbeta t v w).comp_measurePreserving hl).sub
    ((memLp_cavityObservable hμ hbeta t v w).comp_measurePreserving hr)

theorem integral_cavityProduct_log_sq_le_twice_unweighted
    {ι : Type*} (s : Finset ι) (a b : ι → TreeVertex d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (t : ℝ≥0) :
    (∫ q, ((∏ i ∈ s, responseAttenuation (Real.tanh beta)
        (cavityObservable hbeta t (a i) (b i) q.2.1)) ^ 2 +
      (∏ i ∈ s, responseAttenuation (Real.tanh beta)
        (cavityObservable hbeta t (a i) (b i) q.2.2)) ^ 2) *
      (∑ i ∈ s, cavityLogDifference hbeta t (a i) (b i) q) ^ 2 ∂copies beta μ) ≤
      2 * ∫ q, (∑ i ∈ s, cavityLogDifference hbeta t (a i) (b i) q) ^ 2
        ∂copies beta μ := by
  have hθ : (Real.tanh beta) ^ 2 ≤ 1 := by
    have h0 := tanh_nonneg_of_beta_nonneg hbeta
    have h1 := Real.tanh_lt_one beta
    nlinarith
  exact integral_weighted_path_log_sq_le_twice_unweighted s hθ
    (fun i _ => (measurable_cavityObservable hbeta t (a i) (b i)).comp
      (measurable_fst.comp measurable_snd))
    (fun i _ => (measurable_cavityObservable hbeta t (a i) (b i)).comp
      (measurable_snd.comp measurable_snd))
    (fun i _ => (memLp_cavityObservable_difference hμ hbeta t (a i) (b i)).integrable_sq)

theorem integral_cavityProduct_sub_sq_le_twice_log_sum
    {ι : Type*} (s : Finset ι) (a b : ι → TreeVertex d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (t : ℝ≥0) :
    (∫ q, ((∏ i ∈ s, responseAttenuation (Real.tanh beta)
        (cavityObservable hbeta t (a i) (b i) q.2.1)) -
      (∏ i ∈ s, responseAttenuation (Real.tanh beta)
        (cavityObservable hbeta t (a i) (b i) q.2.2))) ^ 2 ∂copies beta μ) ≤
      2 * ∫ q, (∑ i ∈ s, cavityLogDifference hbeta t (a i) (b i) q) ^ 2
        ∂copies beta μ := by
  have hθ : (Real.tanh beta) ^ 2 ≤ 1 := by
    have h0 := tanh_nonneg_of_beta_nonneg hbeta
    have h1 := Real.tanh_lt_one beta
    nlinarith
  have h := integral_prod_responseAttenuation_sub_sq_le s hθ
    (fun i _ => (measurable_cavityObservable hbeta t (a i) (b i)).comp
      (measurable_fst.comp measurable_snd))
    (fun i _ => (measurable_cavityObservable hbeta t (a i) (b i)).comp
      (measurable_snd.comp measurable_snd))
    (fun i _ => (memLp_cavityObservable_difference hμ hbeta t (a i) (b i)).integrable_sq)
  exact h.2.2.trans (integral_cavityProduct_log_sq_le_twice_unweighted s a b hμ hbeta t)

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyProductPathBound
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_cavityProduct_path_variance_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w →
      ∀ (g : TreeAut d) (v : TreeVertex d) (reverse : Bool),
      (∫ q, (pathCavityProduct hbeta t g v reverse q.2.1 -
          pathCavityProduct hbeta t g v reverse q.2.2) ^ 2 ∂copies beta μ) ≤
        C * v.1.length * ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ ∧
      (∫ q, ((pathCavityProduct hbeta t g v reverse q.2.1) ^ 2 +
          (pathCavityProduct hbeta t g v reverse q.2.2) ^ 2) *
          (pathCavityLogSum hbeta t g v reverse q) ^ 2 ∂copies beta μ) ≤
        C * v.1.length * ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ := by
  obtain ⟨C, hC, hpath⟩ := exists_cavityLog_path_variance_bound hμ hd hbeta hthreshold
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro t u w huw g v reverse
  have hlog : (∫ q, (pathCavityLogSum hbeta t g v reverse q) ^ 2 ∂copies beta μ) ≤
      C * v.1.length * ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ := by
    cases reverse with
    | false => simpa only [pathCavityLogSum, Bool.false_eq_true, ↓reduceIte] using
        (hpath t u w huw g v).1
    | true => simpa only [pathCavityLogSum, ↓reduceIte] using
        (hpath t u w huw g v).2
  have hscale := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 2)
  have hscale' : 2 * (∫ q, (pathCavityLogSum hbeta t g v reverse q) ^ 2 ∂copies beta μ) ≤
      (2 * C) * v.1.length *
        ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ := by
    simpa only [mul_assoc] using hscale
  let a := fun i : Fin v.1.length =>
    g.toEquiv (takeVertex v (if reverse then i.1 + 1 else i.1))
  let b := fun i : Fin v.1.length =>
    g.toEquiv (takeVertex v (if reverse then i.1 else i.1 + 1))
  constructor
  · exact (integral_cavityProduct_sub_sq_le_twice_log_sum Finset.univ a b hμ hbeta t).trans hscale'
  · exact (integral_cavityProduct_log_sq_le_twice_unweighted Finset.univ a b hμ hbeta t).trans hscale'

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CoupledPathDrift
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_mul_prod_responseAttenuation_sq_le
    {ι : Type*} (s : Finset ι) {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    {X : ι → Ω → ℝ} {U : Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hU : MemLp U 2 μ) :
    Integrable (fun ω => U ω ^ 2 *
      (∏ i ∈ s, responseAttenuation theta (X i ω)) ^ 2) μ ∧
    (∫ ω, U ω ^ 2 * (∏ i ∈ s, responseAttenuation theta (X i ω)) ^ 2 ∂μ) ≤
      ∫ ω, U ω ^ 2 ∂μ := by
  let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
  have hP : Measurable P := measurable_prod_responseAttenuation s theta hX
  have hpoint (ω : Ω) : U ω ^ 2 * P ω ^ 2 ≤ U ω ^ 2 := by
    have hp := prod_responseAttenuation_pos s (fun i => X i ω) hθ
    have hl := prod_attenuation_le_one s (fun i => X i ω) hθ
    change 0 < P ω at hp
    change P ω ≤ 1 at hl
    have hsq : P ω ^ 2 ≤ 1 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left hsq (sq_nonneg (U ω))
  have hint : Integrable (fun ω => U ω ^ 2 * P ω ^ 2) μ := by
    apply hU.integrable_sq.mono'
      ((hU.aestronglyMeasurable.pow 2).mul ((hP.pow_const 2).aestronglyMeasurable))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hpoint ω
  exact ⟨hint, integral_mono hint hU.integrable_sq hpoint⟩

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_EndpointFromPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem pathCutoff_applicability {C₀ C ω I : ℝ} {n : ℕ}
    (hCC : C₀ ≤ C) (hC : 0 ≤ C) (hω : 0 < ω) (hI : 1 ≤ I)
    (hn : pathCutoff C ω I ≤ n) : C₀ / ω ≤ (n : ℝ) := by
  calc
    C₀ / ω = C₀ * ω⁻¹ := div_eq_mul_inv _ _
    _ ≤ C * ω⁻¹ := mul_le_mul_of_nonneg_right hCC (by positivity)
    _ ≤ C * (ω⁻¹ + Real.log I) := by
      apply mul_le_mul_of_nonneg_left _ hC
      linarith [Real.log_nonneg hI]
    _ ≤ (pathCutoff C ω I : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn

theorem tsum_endpoint_of_majorants {f g e : ℕ → ℝ} (R : ℕ)
    {P B E M : ℝ} (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n)
    (he0 : ∀ n, 0 ≤ e n) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hg : Summable g) (he : Summable e)
    (hprefix : (∑ n ∈ Finset.range R, f n) ≤ P)
    (htail : ∀ n, R ≤ n → f n ≤ B * g n + E * e n)
    (hM : (∑' n, g n) ≤ M) :
    (∑' n, f n) ≤ P + B * M + E * (∑' n, e n) := by
  have hmajorant := (hg.mul_left B).add (he.mul_left E)
  calc
    _ ≤ (∑ n ∈ Finset.range R, f n) + ∑' n, (B * g n + E * e n) :=
      tsum_le_prefix_add_majorant R hf0
        (fun n => add_nonneg (mul_nonneg hB (hg0 n)) (mul_nonneg hE (he0 n))) hmajorant htail
    _ = (∑ n ∈ Finset.range R, f n) +
        (B * (∑' n, g n) + E * (∑' n, e n)) := by
      rw [(hg.mul_left B).tsum_add (he.mul_left E), tsum_mul_left, tsum_mul_left]
    _ ≤ P + (B * M + E * (∑' n, e n)) :=
      add_le_add hprefix (add_le_add (mul_le_mul_of_nonneg_left hM hB) le_rfl)
    _ = _ := by ring

theorem tsum_scaled_integer_endpoint_le {f : ℕ → ℝ} (R k m : ℕ)
    {A B E c ω a q : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hshort : ∀ n, n < R → f n ≤ A * (n : ℝ) ^ k)
    (htail : ∀ n, R ≤ n → f n ≤
      B * ((n : ℝ) ^ k * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤ A * (R : ℝ) ^ (k + 1) +
      B * ((k.factorial : ℝ) * (2 / min c 1) ^ (k + 1) * (ω⁻¹) ^ (k + 1)) +
      E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-a * q ^ n)) := by
  apply tsum_endpoint_of_majorants R hf0 (fun n => by positivity)
    (fun n => by positivity) hB hE (summable_path_attenuation k (mul_pos hc hω))
    (summable_superexponential_path m ha hq) _ htail
    (tsum_scaled_path_attenuation_le k hc hω hω1)
  calc
    _ ≤ ∑ n ∈ Finset.range R, A * (n : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro n hn
      exact hshort n (Finset.mem_range.mp hn)
    _ = A * (∑ n ∈ Finset.range R, (n : ℝ) ^ k) := by rw [Finset.mul_sum]
    _ ≤ A * (R : ℝ) ^ (k + 1) :=
      mul_le_mul_of_nonneg_left (sum_range_nat_pow_le R k) hA

theorem tsum_scaled_sqrt_endpoint_le {f : ℕ → ℝ} (R m : ℕ)
    {A B E c ω a q : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hshort : ∀ n, n < R → f n ≤ A * Real.sqrt n)
    (htail : ∀ n, R ≤ n → f n ≤
      B * (Real.sqrt n * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤ A * ((R : ℝ) * Real.sqrt R) +
      B * ((3 / (min c 1 * Real.sqrt (min c 1))) * (ω⁻¹ * Real.sqrt (ω⁻¹))) +
      E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-a * q ^ n)) := by
  apply tsum_endpoint_of_majorants R hf0 (fun n => by positivity)
    (fun n => by positivity) hB hE (summable_sqrt_path_attenuation (mul_pos hc hω))
    (summable_superexponential_path m ha hq) _ htail
    (tsum_scaled_sqrt_path_attenuation_le hc hω hω1)
  calc
    _ ≤ ∑ n ∈ Finset.range R, A * Real.sqrt n := by
      apply Finset.sum_le_sum
      intro n hn
      exact hshort n (Finset.mem_range.mp hn)
    _ = A * (∑ n ∈ Finset.range R, Real.sqrt n) := by rw [Finset.mul_sum]
    _ ≤ A * ((R : ℝ) * Real.sqrt R) :=
      mul_le_mul_of_nonneg_left (sum_range_sqrt_le R) hA

theorem tsum_cutoff_integer_endpoint_le {f : ℕ → ℝ} (R k m : ℕ)
    {A B E U V K c ω a q C : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hU : 0 ≤ U)
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C) (hbase : 2 ≤ (a / 2) * q ^ C)
    (hR : R = pathCutoff C ω (1 + Real.log (K / V)))
    (hshort : ∀ n, n < R → f n ≤ A * U * (n : ℝ) ^ k)
    (htail : ∀ n, R ≤ n → f n ≤
      B * U * ((n : ℝ) ^ k * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤ A * U * (R : ℝ) ^ (k + 1) +
      (B * ((k.factorial : ℝ) * (2 / min c 1) ^ (k + 1))) * U * (ω⁻¹) ^ (k + 1) +
      (E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n))) * V ^ 2 := by
  have htail' : ∀ n, R ≤ n → f n ≤
      (B * U) * ((n : ℝ) ^ k * Real.exp (-(c * ω) * n)) +
      (E * V ^ 2) * ((n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n)) := by
    intro n hn
    have habs := pathCutoff_absorption hV hVK hK ha.le hq hC0 hC hbase hω hω1
      (show pathCutoff C ω (1 + Real.log (K / V)) ≤ n by simpa [← hR] using hn)
    calc
      f n ≤ _ := htail n hn
      _ ≤ B * U * ((n : ℝ) ^ k * Real.exp (-(c * ω) * n)) +
          E * ((n : ℝ) ^ m * (V ^ 2 * Real.exp (-(a / 2) * q ^ n))) := by
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left habs (by positivity)) hE
      _ = _ := by ring
  have hs := tsum_scaled_integer_endpoint_le R k m hf0
    (mul_nonneg hA hU) (mul_nonneg hB hU) (mul_nonneg hE (sq_nonneg V))
    hc hω hω1 (show 0 < a / 2 by positivity) hq hshort htail'
  convert hs using 1 <;> first | rfl | ring

theorem pathCutoff_linear_absorption {V K a q C ω : ℝ} {n : ℕ}
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K) (ha : 0 ≤ a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C)
    (hbase : 2 ≤ (a / 2) * q ^ C) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : pathCutoff C ω (1 + Real.log (K / V)) ≤ n) :
    Real.exp (-a * q ^ n) ≤ V * Real.exp (-(a / 2) * q ^ n) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hlogratio : 0 ≤ Real.log (K / V) := Real.log_nonneg ((one_le_div hV).2 hVK)
  have hI : 1 ≤ 1 + Real.log (K / V) := by linarith
  have hexponent := path_log_cutoff_bound ha hq hI hC hbase
    (pathCutoff_log_bound hC0 hω hω1 hn)
  have hlog : -(a / 2) * q ^ n ≤ Real.log V := by
    rw [Real.log_div (ne_of_gt hKpos) (ne_of_gt hV)] at hexponent hlogratio
    linarith
  calc
    Real.exp (-a * q ^ n) = Real.exp (-(a / 2) * q ^ n) *
        Real.exp (-(a / 2) * q ^ n) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (Real.log V) * Real.exp (-(a / 2) * q ^ n) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hlog) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_log hV]

theorem tsum_quadratic_endpoint_at_cutoff {f : ℕ → ℝ} (R m : ℕ)
    {A B E S V K c ω a q C : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hS : 0 ≤ S)
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C) (hbase : 2 ≤ (a / 2) * q ^ C)
    (hR : R = pathCutoff C ω (1 + Real.log (K / V)))
    (hshort : ∀ n, n < R → f n ≤ A * S * n)
    (htail : ∀ n, R ≤ n → f n ≤ B * S *
      ((n : ℝ) * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤
      max (2 * A * (C + 1) ^ 2 + B * (2 / min c 1) ^ 2)
        (E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n))) *
      (S * ((ω⁻¹) ^ 2 + (Real.log (1 + Real.log (K / V))) ^ 2) + V ^ 2) := by
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    have := Real.log_nonneg ((one_le_div hV).2 hVK)
    linarith
  have hscale : (R : ℝ) ≤ (C + 1) * (ω⁻¹ + Real.log (1 + Real.log (K / V))) := by
    rw [hR]
    exact pathCutoff_le hC0 hω hω1 hI
  apply quadratic_endpoint_scale hA (by positivity) hS (Nat.cast_nonneg R)
    (by positivity) (by positivity) (Real.log_nonneg hI) hscale
  have hs := tsum_cutoff_integer_endpoint_le R 1 m hf0 hA hB hE hS
    hV hVK hK hc hω hω1 ha hq hC0 hC hbase hR
    (by simpa only [pow_one] using hshort) (by simpa only [pow_one] using htail)
  simpa using hs

theorem tsum_linear_endpoint_at_cutoff {f : ℕ → ℝ} (R m : ℕ)
    {A B E V K c ω a q C : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C) (hbase : 2 ≤ (a / 2) * q ^ C)
    (hR : R = pathCutoff C ω (1 + Real.log (K / V)))
    (hshort : ∀ n, n < R → f n ≤ A * V)
    (htail : ∀ n, R ≤ n → f n ≤ B * V * Real.exp (-(c * ω) * n) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤
      max (A * (C + 1) + B * (2 / min c 1))
        (E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n))) *
      (V * (ω⁻¹ + Real.log (1 + Real.log (K / V))) + V ^ 2) := by
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    have := Real.log_nonneg ((one_le_div hV).2 hVK)
    linarith
  have hscale : (R : ℝ) ≤ (C + 1) * (ω⁻¹ + Real.log (1 + Real.log (K / V))) := by
    rw [hR]
    exact pathCutoff_le hC0 hω hω1 hI
  apply linear_endpoint_scale hA (by positivity) hV.le (by positivity)
    (Real.log_nonneg hI) hscale
  have hs := tsum_cutoff_integer_endpoint_le R 0 m hf0 hA hB hE hV.le
    hV hVK hK hc hω hω1 ha hq hC0 hC hbase hR
    (by simpa only [pow_zero, mul_one] using hshort)
    (by simpa only [pow_zero, one_mul] using htail)
  simpa using hs

theorem tsum_cutoff_sqrt_endpoint_le {f : ℕ → ℝ} (R m : ℕ)
    {A B E S V K c ω a q C : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C) (hbase : 2 ≤ (a / 2) * q ^ C)
    (hR : R = pathCutoff C ω (1 + Real.log (K / V)))
    (hshort : ∀ n, n < R → f n ≤ A * Real.sqrt S * Real.sqrt n)
    (htail : ∀ n, R ≤ n → f n ≤ B * Real.sqrt S *
      (Real.sqrt n * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤ A * Real.sqrt S * ((R : ℝ) * Real.sqrt R) +
      (B * (3 / (min c 1 * Real.sqrt (min c 1)))) * Real.sqrt S *
        (ω⁻¹ * Real.sqrt (ω⁻¹)) +
      (E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n))) * V := by
  have htail' : ∀ n, R ≤ n → f n ≤
      (B * Real.sqrt S) * (Real.sqrt n * Real.exp (-(c * ω) * n)) +
      (E * V) * ((n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n)) := by
    intro n hn
    have habs := pathCutoff_linear_absorption hV hVK hK ha.le hq hC0 hC hbase hω hω1
      (show pathCutoff C ω (1 + Real.log (K / V)) ≤ n by simpa [← hR] using hn)
    calc
      f n ≤ _ := htail n hn
      _ ≤ B * Real.sqrt S * (Real.sqrt n * Real.exp (-(c * ω) * n)) +
          E * ((n : ℝ) ^ m * (V * Real.exp (-(a / 2) * q ^ n))) := by
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left habs (by positivity)) hE
      _ = _ := by ring
  have hs := tsum_scaled_sqrt_endpoint_le R m hf0
    (mul_nonneg hA (Real.sqrt_nonneg S)) (mul_nonneg hB (Real.sqrt_nonneg S))
    (mul_nonneg hE hV.le) hc hω hω1 (show 0 < a / 2 by positivity) hq hshort htail'
  convert hs using 1 <;> first | rfl | ring

theorem tsum_sqrt_endpoint_at_cutoff {f : ℕ → ℝ} (R m : ℕ)
    {A B E S V K c ω a q C : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C) (hbase : 2 ≤ (a / 2) * q ^ C)
    (hR : R = pathCutoff C ω (1 + Real.log (K / V)))
    (hshort : ∀ n, n < R → f n ≤ A * Real.sqrt S * Real.sqrt n)
    (htail : ∀ n, R ≤ n → f n ≤ B * Real.sqrt S *
      (Real.sqrt n * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤
      max (4 * A * (C + 1) * Real.sqrt (C + 1) +
        B * (3 / (min c 1 * Real.sqrt (min c 1))))
        (E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n))) *
      (Real.sqrt S * (ω⁻¹ * Real.sqrt (ω⁻¹) +
        Real.log (1 + Real.log (K / V)) * Real.sqrt (Real.log (1 + Real.log (K / V)))) + V) := by
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    have := Real.log_nonneg ((one_le_div hV).2 hVK)
    linarith
  have hscale : (R : ℝ) ≤ (C + 1) * (ω⁻¹ + Real.log (1 + Real.log (K / V))) := by
    rw [hR]
    exact pathCutoff_le hC0 hω hω1 hI
  apply sqrt_endpoint_scale hA (by positivity) hV.le (Nat.cast_nonneg R)
    (by positivity) (by positivity) (Real.log_nonneg hI) hscale
  exact tsum_cutoff_sqrt_endpoint_le R m hf0 hA hB hE hV hVK hK
    hc hω hω1 ha hq hC0 hC hbase hR hshort htail

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_WeightedPathSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
namespace Problem367

theorem sqrt_le_path_majorant {x B S E c a q ω : ℝ} (n : ℕ)
    (hB : 0 ≤ B) (hS : 0 ≤ S) (hE : 0 ≤ E)
    (hx : x ≤ B * S * ((n : ℝ) * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ 2 * Real.exp (-a * q ^ n))) :
    Real.sqrt x ≤ Real.sqrt B * Real.sqrt S *
      (Real.sqrt n * Real.exp (-((c / 2) * ω) * n)) +
      Real.sqrt E * ((n : ℝ) * Real.exp (-(a / 2) * q ^ n)) := by
  let u := Real.sqrt B * Real.sqrt S *
    (Real.sqrt n * Real.exp (-((c / 2) * ω) * n))
  let v := Real.sqrt E * ((n : ℝ) * Real.exp (-(a / 2) * q ^ n))
  have hu : 0 ≤ u := by dsimp [u] <;> positivity
  have hv : 0 ≤ v := by dsimp [v] <;> positivity
  have hu2 : u ^ 2 = B * S * ((n : ℝ) * Real.exp (-(c * ω) * n)) := by
    dsimp [u]
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hS,
      Real.sq_sqrt (Nat.cast_nonneg n), ← Real.exp_nat_mul]
    congr 2
    ring_nf
  have hv2 : v ^ 2 = E * ((n : ℝ) ^ 2 * Real.exp (-a * q ^ n)) := by
    dsimp [v]
    rw [mul_pow, mul_pow, Real.sq_sqrt hE, ← Real.exp_nat_mul]
    congr 2
    ring_nf
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg hu hv, ?_⟩
  nlinarith [mul_nonneg hu hv]

theorem WeightedPathEstimates.summable
    {Q L : ℕ → ℝ} {A B E c a q C₀ S V ω : ℝ}
    (h : WeightedPathEstimates Q L A B E c a q C₀ S V ω)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hS : 0 ≤ S)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q) (hω : 0 < ω) :
    Summable Q ∧ Summable L ∧ Summable (fun n => Real.sqrt (Q n)) := by
  let R := Nat.ceil (C₀ / ω)
  have hR (n : ℕ) (hn : R ≤ n) : C₀ / ω ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hQsum := ((summable_path_attenuation 1 (mul_pos hc hω)).mul_left (B * S)).add
    ((summable_superexponential_path 2 ha hq).mul_left E)
  have hLsum := ((summable_path_attenuation 0 (mul_pos hc hω)).mul_left (B * V)).add
    ((summable_superexponential_path 0 ha hq).mul_left E)
  have hZsum := ((summable_sqrt_path_attenuation (mul_pos (half_pos hc) hω)).mul_left
    (Real.sqrt B * Real.sqrt S)).add
    ((summable_superexponential_path 1 (half_pos ha) hq).mul_left (Real.sqrt E))
  refine ⟨?_, ?_, ?_⟩
  · apply hQsum.of_norm_bounded_eventually_nat
    refine eventually_atTop.mpr ⟨R, fun n hn => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (h.noise_nonneg n)]
    simpa only [pow_one] using h.noise_long n (hR n hn)
  · apply hLsum.of_norm_bounded_eventually_nat
    refine eventually_atTop.mpr ⟨R, fun n hn => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (h.linear_nonneg n)]
    simpa only [pow_zero, one_mul] using h.linear_long n (hR n hn)
  · apply hZsum.of_norm_bounded_eventually_nat
    refine eventually_atTop.mpr ⟨R, fun n hn => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [pow_one] using sqrt_le_path_majorant n hB hS hE (h.noise_long n (hR n hn))

theorem WeightedPathEstimates.endpoint_bounds
    {Q L : ℕ → ℝ} {A B E c a q C₀ S V K ω C : ℝ}
    (h : WeightedPathEstimates Q L A B E c a q C₀ S V ω)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hS : 0 ≤ S)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q)
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K)
    (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hC0 : 0 ≤ C) (hCC : C₀ ≤ C) (hC : 1 ≤ Real.log q * C)
    (hbase : 2 ≤ ((a / 2) / 2) * q ^ C) :
    let M := weightedPathEndpointConstant A B E c a q C
    Summable Q ∧ Summable L ∧ Summable (fun n => Real.sqrt (Q n)) ∧
    (∑' n, Q n) ≤ M * (S * ((ω⁻¹) ^ 2 + (Real.log (1 + Real.log (K / V))) ^ 2) + V ^ 2) ∧
    (∑' n, L n) ≤ M * (V * (ω⁻¹ + Real.log (1 + Real.log (K / V))) + V ^ 2) ∧
    (∑' n, Real.sqrt (Q n)) ≤ M * (Real.sqrt S *
      (ω⁻¹ * Real.sqrt (ω⁻¹) + (Real.log (1 + Real.log (K / V))) ^ ((3 : ℝ) / 2)) + V) := by
  let R := pathCutoff C ω (1 + Real.log (K / V))
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    linarith [Real.log_nonneg ((one_le_div hV).mpr hVK)]
  have hlog : 0 ≤ Real.log (1 + Real.log (K / V)) := Real.log_nonneg hI
  have happ (n : ℕ) (hn : R ≤ n) : C₀ / ω ≤ (n : ℝ) :=
    pathCutoff_applicability hCC hC0 hω hI hn
  have hbase' : 2 ≤ (a / 2) * q ^ C := by
    have hp : 0 ≤ q ^ C := Real.rpow_nonneg (zero_lt_one.trans hq).le _
    nlinarith [mul_nonneg ha.le hp]
  have hQ := tsum_quadratic_endpoint_at_cutoff R 2 h.noise_nonneg hA hB hE hS
    hV hVK hK hc hω hω1 ha hq hC0 hC hbase' rfl
    (fun n _ => h.noise_short n) (fun n hn => h.noise_long n (happ n hn))
  have hL := tsum_linear_endpoint_at_cutoff R 0 h.linear_nonneg hA hB hE
    hV hVK hK hc hω hω1 ha hq hC0 hC hbase' rfl
    (fun n _ => h.linear_short n)
    (fun n hn => by simpa only [pow_zero, one_mul] using h.linear_long n (happ n hn))
  have hZ := tsum_sqrt_endpoint_at_cutoff (S := S) R 1 (fun n => Real.sqrt_nonneg (Q n))
    (Real.sqrt_nonneg A) (Real.sqrt_nonneg B) (Real.sqrt_nonneg E)
    hV hVK hK (half_pos hc) hω hω1 (half_pos ha) hq hC0 hC hbase rfl
    (fun n _ => by
      calc
        Real.sqrt (Q n) ≤ Real.sqrt (A * S * n) := Real.sqrt_le_sqrt (h.noise_short n)
        _ = Real.sqrt A * Real.sqrt S * Real.sqrt n := by
          rw [Real.sqrt_mul (mul_nonneg hA hS), Real.sqrt_mul hA])
    (fun n hn => by simpa only [pow_one] using
      sqrt_le_path_majorant n hB hS hE (h.noise_long n (happ n hn)))
  rw [mul_sqrt_eq_three_halves hlog] at hZ
  obtain ⟨hsQ, hsL, hsZ⟩ := h.summable hB hE hS hc ha hq hω
  refine ⟨hsQ, hsL, hsZ, ?_, ?_, ?_⟩
  · exact hQ.trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) (by positivity))
  · simp only [pow_zero, one_mul] at hL
    exact hL.trans (mul_le_mul_of_nonneg_right
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) (by positivity))
  · simp only [pow_one] at hZ
    exact hZ.trans (mul_le_mul_of_nonneg_right
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) (by positivity))

theorem exists_spatial_endpoint_constant_of_path_estimates
    {A B E c a q N C₀ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ {Q L : ℕ → ℝ} {S V K ω D : ℝ},
      WeightedPathEstimates Q L A B E c a q C₀ S V ω →
      0 ≤ S → S ≤ N * V → 0 < V → V ≤ K → 1 ≤ K → 0 < ω → ω ≤ 1 →
      D ≤ N * (V + (∑' n, Q n) + (∑' n, L n) +
        Real.sqrt V * (∑' n, Real.sqrt (Q n))) →
      CriticalSpatialEndpointBounds D (∑' n, Q n) (∑' n, L n)
        (∑' n, Real.sqrt (Q n)) S V M K ω := by
  obtain ⟨C, hC0, hCC, hC, hbase⟩ := exists_path_cutoff_constant (half_pos ha) hq C₀
  let W := weightedPathEndpointConstant A B E c a q C
  let M := max N W
  have hW1 : 1 ≤ W := le_max_left _ _
  have hWM : W ≤ M := le_max_right _ _
  have hNM : N ≤ M := le_max_left _ _
  refine ⟨M, hW1.trans hWM, ?_⟩
  intro Q L S V K ω D h hS hSV hV hVK hK hω hω1 hD
  obtain ⟨_, _, _, hQ, hL, hZ⟩ := h.endpoint_bounds hA hB hE hS hc ha hq
    hV hVK hK hω hω1 hC0.le hCC hC hbase
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    linarith [Real.log_nonneg ((one_le_div hV).mpr hVK)]
  have hlog : 0 ≤ Real.log (1 + Real.log (K / V)) := Real.log_nonneg hI
  refine ⟨hS, hSV.trans (mul_le_mul_of_nonneg_right hNM hV.le), ?_, ?_, ?_, ?_⟩
  · exact hQ.trans (mul_le_mul_of_nonneg_right hWM (by positivity))
  · exact hL.trans (mul_le_mul_of_nonneg_right hWM (by positivity))
  · exact hZ.trans (mul_le_mul_of_nonneg_right hWM (by positivity))
  · apply hD.trans
    apply mul_le_mul_of_nonneg_right hNM
    exact add_nonneg (add_nonneg (add_nonneg hV.le (tsum_nonneg h.noise_nonneg))
      (tsum_nonneg h.linear_nonneg))
      (mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg (fun _ => Real.sqrt_nonneg _)))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyShellEnergies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367

theorem nonnegativeShellSup_nonneg {d : ℕ} (F : TreeVertex d → ℝ) (n : ℕ) :
    0 ≤ nonnegativeShellSup F n := by
  classical
  exact Finset.le_sup' (fun v : Option (TreeShell d n) => v.elim 0 (fun v => F v))
    (Finset.mem_univ none)

theorem nonnegativeShellSup_le {d n : ℕ} {F : TreeVertex d → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hF : ∀ v, v.1.length = n → F v ≤ C) :
    nonnegativeShellSup F n ≤ C := by
  classical
  apply Finset.sup'_le
  intro v _
  cases v with
  | none => exact hC
  | some v => exact hF v v.property

namespace IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingConditionalCopyBounds ConnectedHull ResponseRows IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem pathCavityProduct_eq_pathProduct (hb : 0 ≤ beta) (t : ℝ≥0)
    (v : TreeVertex d) (x : Paths d) :
    pathCavityProduct hb t (TreeAut.refl d) v true x =
      pathProduct (Real.tanh beta) (Finset.range v.1.length) (pathCavity hb t v) x := by
  simp only [pathCavityProduct, TreeAut.refl, Equiv.refl_apply, ↓reduceIte,
    pathProduct, pathCavity]
  exact Fin.prod_univ_eq_prod_range (fun i : ℕ => responseAttenuation (Real.tanh beta)
    (cavityObservable hb t (takeVertex v (i + 1)) (takeVertex v i) x)) v.1.length

theorem pathCavityLogSum_eq_pathLogDiff (hb : 0 ≤ beta) (t : ℝ≥0)
    (v : TreeVertex d) (q : CopySpace d) :
    pathCavityLogSum hb t (TreeAut.refl d) v true q =
      pathLogDiff (Real.tanh beta) (Finset.range v.1.length)
        (fun i q => pathCavity hb t v i q.2.1)
        (fun i q => pathCavity hb t v i q.2.2) q := by
  simp only [pathCavityLogSum, TreeAut.refl, Equiv.refl_apply, ↓reduceIte,
    pathLogDiff, pathCavity, cavityLogDifference, cavityLogObservable]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    Real.log (responseAttenuation (Real.tanh beta)
      (cavityObservable hb t (takeVertex v (i + 1)) (takeVertex v i) q.2.1)) -
    Real.log (responseAttenuation (Real.tanh beta)
      (cavityObservable hb t (takeVertex v (i + 1)) (takeVertex v i) q.2.2))) v.1.length

theorem linearEnergy_le_siteVariance
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    linearEnergy (μ := μ) hb t v ≤
      ∫ q, (fieldDifference beta (root d) t q) ^ 2 ∂copies beta μ := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  have hU : MemLp (fieldDifference beta (root d) t) 2 (copies beta μ) :=
    ((memLp_field_at hμ hb t _).comp_measurePreserving hl).sub
      ((memLp_field_at hμ hb t _).comp_measurePreserving hr)
  exact (integral_mul_prod_responseAttenuation_sq_le (Finset.range v.1.length)
    (Real.tanh_sq_lt_one beta).le
    (fun i _ => (measurable_cavityObservable hb t _ _).comp hl.measurable) hU).2

theorem exists_short_shell_energy_bounds
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w → ∀ n : ℕ,
      noiseShellEnergy (μ := μ) hb t n ≤
        A * (∫ q, (cavityLogDifference hb t u w q) ^ 2 ∂copies beta μ) * n ∧
      linearShellEnergy (μ := μ) hb t n ≤
        A * (∫ q, (fieldDifference beta (root d) t q) ^ 2 ∂copies beta μ) := by
  obtain ⟨C, hC, hbound⟩ := exists_cavityProduct_path_variance_bound hμ hd hb hcrit
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro t u w huw n
  have hS : 0 ≤ ∫ q, (cavityLogDifference hb t u w q) ^ 2 ∂copies beta μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hV : 0 ≤ ∫ q, (fieldDifference beta (root d) t q) ^ 2 ∂copies beta μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  constructor
  · apply nonnegativeShellSup_le (by positivity)
    intro v hv
    have hpath := (hbound t u w huw (TreeAut.refl d) v true).2
    simp_rw [pathCavityProduct_eq_pathProduct, pathCavityLogSum_eq_pathLogDiff] at hpath
    change noiseEnergy (μ := μ) hb t v ≤ _ at hpath
    calc
      _ ≤ C * (v.1.length : ℝ) * (∫ q, (cavityLogDifference hb t u w q) ^ 2 ∂copies beta μ) := hpath
      _ = C * (∫ q, (cavityLogDifference hb t u w q) ^ 2 ∂copies beta μ) * n := by rw [hv]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right 1 C) hS) (Nat.cast_nonneg n)
  · apply nonnegativeShellSup_le (by positivity)
    intro v _
    exact (linearEnergy_le_siteVariance hμ hb t v).trans
      (le_mul_of_one_le_left hV (le_max_left _ _))

end IsingCopyResponseRowPaths
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopySpatialEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyStationarity IsingConditionalCopyBounds ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_actual_spatial_endpoint_constant_oai
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1))
    {B E c a q C₀ : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w → 0 < t →
      let S := ∫ z, (cavityLogDifference hb t u w z) ^ 2 ∂copies beta μ
      let V := ∫ z, (fieldDifference beta (root d) t z) ^ 2 ∂copies beta μ
      ∀ (K ω : ℝ), 0 < V → V ≤ K → 1 ≤ K → 0 < ω → ω ≤ 1 →
      (∀ v : TreeVertex d, C₀ / ω ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤ B * S *
          ((v.1.length : ℝ) * Real.exp (-(c * ω) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length))) →
      (∀ v : TreeVertex d, C₀ / ω ≤ (v.1.length : ℝ) →
        linearEnergy (μ := μ) hb t v ≤ B * V * Real.exp (-(c * ω) * v.1.length) +
          E * Real.exp (-a * q ^ v.1.length)) →
      CriticalSpatialEndpointBounds
        (∫ z, IsingCopyEnergy.density beta (root d) t z ∂copies beta μ)
        (∑' n, noiseShellEnergy (μ := μ) hb t n)
        (∑' n, linearShellEnergy (μ := μ) hb t n)
        (∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb t n)) S V M K ω := by
  obtain ⟨A, hA, hshort⟩ := exists_short_shell_energy_bounds hμ hd hb hcrit
  let N := max (cavityLogVarianceCoefficient (Real.tanh beta))
    (2 + 8 * ((d : ℝ) * Real.tanh beta ^ 2))
  obtain ⟨M, hM, hendpoint⟩ := exists_spatial_endpoint_constant_of_path_estimates
    (N := N) (C₀ := C₀) (zero_le_one.trans hA) hB hE hc ha hq
  refine ⟨M, hM, ?_⟩
  intro t u w huw ht
  dsimp only
  intro K ω hV hVK hK hω hω1 hlongQ hlongL
  let S := ∫ z, (cavityLogDifference hb t u w z) ^ 2 ∂copies beta μ
  let V := ∫ z, (fieldDifference beta (root d) t z) ^ 2 ∂copies beta μ
  have hS : 0 ≤ S := integral_nonneg (fun _ => sq_nonneg _)
  have hV0 : 0 ≤ V := integral_nonneg (fun _ => sq_nonneg _)
  have hpaths : WeightedPathEstimates (noiseShellEnergy (μ := μ) hb t)
      (linearShellEnergy (μ := μ) hb t) A B E c a q C₀ S V ω := by
    refine ⟨fun _ => nonnegativeShellSup_nonneg _ _, fun _ => nonnegativeShellSup_nonneg _ _,
      fun n => (hshort t u w huw n).1, fun n => (hshort t u w huw n).2, ?_, ?_⟩
    · intro n hn
      apply nonnegativeShellSup_le (by positivity)
      intro v hv
      simpa only [hv] using hlongQ v (by simpa only [hv] using hn)
    · intro n hn
      apply nonnegativeShellSup_le (by positivity)
      intro v hv
      simpa only [hv] using hlongL v (by simpa only [hv] using hn)
  have hSV : S ≤ N * V := by
    have h := norm_cavityLogDifference_sq_le hμ hb t (root d) u w
    rw [norm_observableDifference_sq] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hV0)
  obtain ⟨hsQ, hsL, hsZ⟩ := hpaths.summable hB hE hS hc ha hq hω
  have hbranch : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1 := by
    have h := (tanh_threshold_iff_branching_sq hd hb).mp hcrit
    simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] using h
  have hD := (integral_actual_density_le_path_sums hμ hb ht hbranch hsQ hsL hsZ).2
  apply hendpoint hpaths hS hSV hV hVK hK hω hω1
  apply hD.trans
  apply mul_le_mul_of_nonneg_right (le_max_right _ _)
  exact add_nonneg (add_nonneg (add_nonneg hV0
    (tsum_nonneg hpaths.noise_nonneg)) (tsum_nonneg hpaths.linear_nonneg))
    (mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg (fun _ => Real.sqrt_nonneg _)))

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingCopyResponseRowPaths.exists_actual_spatial_endpoint_constant_oai := @OAI.Problem367.IsingCopyResponseRowPaths.exists_actual_spatial_endpoint_constant_oai
