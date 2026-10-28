-- Prove2me | solution 1 for OAI.TraceReconstruction.source_level_overlap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:04:38.947848+00:00
-- url     : https://prove2.me/submissions/8d30a210-2275-43b5-9d3f-8849ab14b619

import Mathlib
import Definitions.Def_TraceReconstruction
import Definitions.Def_OAIQ9Tr002
import Theorems.Thm_OAI_TraceReconstruction_actual_one_window_oracle
import Theorems.Thm_OAI_TraceReconstruction_source_level_all_budgets
import Theorems.Thm_OAI_TraceReconstruction_source_level_warmup_second

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# FiniteLaw

Finite laws, common-reference total variation, Hellinger affinity, overlap, scalar moments, hypercontractivity, clipping, and leaf densities.
-/

open scoped ENNReal
noncomputable section

noncomputable section
namespace TraceReconstruction

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem tv_sq_le_hellingerSq (P Q : FiniteLaw α) :
    tv P Q ^ 2 ≤ hellingerSq P Q := by
  have hpoint (a : α) : |P.mass a - Q.mass a| ^ 2 ≤
      (Real.sqrt (P.mass a) - Real.sqrt (Q.mass a)) ^ 2 *
        (Real.sqrt (P.mass a) + Real.sqrt (Q.mass a)) ^ 2 := by
    rw [sq_abs]
    have hp := Real.sq_sqrt (P.nonneg a)
    have hq := Real.sq_sqrt (Q.nonneg a)
    nlinarith only [hp, hq, sq_nonneg (P.mass a - Q.mass a)]
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.univ)
    (r := fun a => |P.mass a - Q.mass a|)
    (f := fun a => (Real.sqrt (P.mass a) - Real.sqrt (Q.mass a)) ^ 2)
    (g := fun a => (Real.sqrt (P.mass a) + Real.sqrt (Q.mass a)) ^ 2)
    (fun a _ => sq_nonneg _) (fun a _ => sq_nonneg _) (fun a _ => hpoint a)
  have hplus : (∑ a, (Real.sqrt (P.mass a) + Real.sqrt (Q.mass a)) ^ 2) =
      2 + 2 * affinity P Q := by
    unfold affinity
    calc
      _ = (∑ a, P.mass a) + (∑ a, Q.mass a) + 2 * ∑ a,
          Real.sqrt (P.mass a) * Real.sqrt (Q.mass a) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        have hp := Real.sq_sqrt (P.nonneg a)
        have hq := Real.sq_sqrt (Q.nonneg a)
        nlinarith only [hp, hq]
      _ = _ := by rw [P.total, Q.total]; ring
  rw [hplus] at h
  change (∑ a, |P.mass a - Q.mass a|) ^ 2 ≤ hellingerSq P Q * (2 + 2 * affinity P Q) at h
  have hbound := mul_le_mul_of_nonneg_left (affinity_le_one P Q) (hellingerSq_nonneg P Q)
  unfold tv
  nlinarith only [h, hbound]

theorem tv_le_sqrt_hellingerSq (P Q : FiniteLaw α) :
    tv P Q ≤ Real.sqrt (hellingerSq P Q) := by
  have h := tv_sq_le_hellingerSq P Q
  have hs := Real.sq_sqrt (hellingerSq_nonneg P Q)
  have hn := Real.sqrt_nonneg (hellingerSq P Q)
  nlinarith only [h, hs, hn]

theorem affinity_product (P Q : FiniteLaw α) (m : ℕ) :
    affinity (P.product m) (Q.product m) = affinity P Q ^ m := by
  unfold affinity product
  simp only
  have hexp (a : Fin m → α) :
      Real.sqrt (∏ j, P.mass (a j)) * Real.sqrt (∏ j, Q.mass (a j)) =
        ∏ j, (Real.sqrt (P.mass (a j)) * Real.sqrt (Q.mass (a j))) := by
    rw [Real.sqrt_prod _ (fun j _ => P.nonneg (a j)),
      Real.sqrt_prod _ (fun j _ => Q.nonneg (a j)), Finset.prod_mul_distrib]
  simp_rw [hexp]
  rw [← Fintype.prod_sum (fun (_ : Fin m) a => Real.sqrt (P.mass a) * Real.sqrt (Q.mass a))]
  simp

theorem hellingerSq_product_le (P Q : FiniteLaw α) (m : ℕ) :
    hellingerSq (P.product m) (Q.product m) ≤ (m : ℝ) * hellingerSq P Q := by
  rw [hellingerSq_eq, affinity_product, hellingerSq_eq]
  have ha := affinity_nonneg P Q
  have hb := affinity_le_one P Q
  have hpow : 1 - affinity P Q ^ m ≤ (m : ℝ) * (1 - affinity P Q) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      have hmul := mul_le_mul_of_nonneg_right ih ha
      have hm : (0 : ℝ) ≤ (m : ℝ) * (1 - affinity P Q) := by positivity
      have hmon := mul_le_mul_of_nonneg_left hb hm
      nlinarith only [hmul, hmon]
  linarith


theorem tv_bind_le (P Q : FiniteLaw α) (K : α → FiniteLaw β) :
    tv (P.bind K) (Q.bind K) ≤ tv P Q := by
  unfold tv bind
  simp only
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ = ∑ b, |∑ a, (P.mass a - Q.mass a) * (K a).mass b| := by
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _; ring
    _ ≤ ∑ b, ∑ a, |(P.mass a - Q.mass a) * (K a).mass b| :=
      Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, |P.mass a - Q.mass a| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [abs_mul, abs_of_nonneg ((K a).nonneg _), ← Finset.mul_sum, (K a).total, mul_one]

theorem tv_triangle (P Q R : FiniteLaw α) : tv P R ≤ tv P Q + tv Q R := by
  unfold tv
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro a _
  exact abs_sub_le _ _ _

theorem common_part_decomposition (P Q : FiniteLaw α) {ω : ℝ}
    (hω : ω ∈ Set.Ioo 0 1) (hov : ω ≤ overlap P Q) :
    ∃ H P' Q' : FiniteLaw α,
      (∀ a, P.mass a = ω * H.mass a + (1 - ω) * P'.mass a) ∧
      (∀ a, Q.mass a = ω * H.mass a + (1 - ω) * Q'.mass a) := by
  have h : 0 < overlap P Q := lt_of_lt_of_le hω.1 hov
  let H := commonPart P Q h
  have hP : ∀ a, ω * H.mass a ≤ P.mass a := commonPart_le_left P Q h hov
  have hQ : ∀ a, ω * H.mass a ≤ Q.mass a := by
    intro a
    change ω * (min (P.mass a) (Q.mass a) / overlap P Q) ≤ _
    calc
      _ ≤ overlap P Q * (min (P.mass a) (Q.mass a) / overlap P Q) :=
        mul_le_mul_of_nonneg_right hov (div_nonneg (le_min (P.nonneg a) (Q.nonneg a)) h.le)
      _ = min (P.mass a) (Q.mass a) := by field_simp
      _ ≤ _ := min_le_right _ _
  refine ⟨H, remainderLaw P H ω hω.2 hP, remainderLaw Q H ω hω.2 hQ, ?_, ?_⟩
  · intro a
    change P.mass a = ω * H.mass a + (1 - ω) * ((P.mass a - ω * H.mass a) / (1 - ω))
    field_simp [(sub_pos.mpr hω.2).ne']
    ring
  · intro a
    change Q.mass a = ω * H.mass a + (1 - ω) * ((Q.mass a - ω * H.mass a) / (1 - ω))
    field_simp [(sub_pos.mpr hω.2).ne']
    ring

end FiniteLaw
end TraceReconstruction

end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Model

Independent deletion, complete trace observations, randomized estimators, ENNReal fixed-budget complexity, concatenation, and literal input words.
-/

open scoped ENNReal
noncomputable section

open scoped ENNReal
noncomputable section

noncomputable section

namespace TraceReconstruction
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem tv_map_le (P Q : FiniteLaw α) (f : α → β) :
    tv (P.map f) (Q.map f) ≤ tv P Q := tv_bind_le P Q _

end FiniteLaw

end TraceReconstruction

end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Binomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Binomial

Fair and biased binomial laws, generating series, differences, concentration, Gaussian overlap, hidden counts, and local lower bounds.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

/-! ## Quantitative fair-binomial anti-concentration

A direct inductive bound, avoiding an unformalized appeal to Stirling.
It is one of the estimates needed for signed binomial smoothing and
for the local/global anchor kernels.
-/

theorem centralBinom_square_bound (n : ℕ) :
    ((n : ℝ) + 1) * (n.centralBinom : ℝ) ^ 2 ≤ (16 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hr : ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) =
        2 * (2 * n + 1) * (n.centralBinom : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hc : 4 * (2 * (n : ℝ) + 1) ^ 2 * (n + 2) ≤
        16 * (n + 1) ^ 3 := by nlinarith [sq_nonneg (n : ℝ)]
    have hh : ((n : ℝ) + 1) ^ 2 *
        ((n + 2) * ((n + 1).centralBinom : ℝ) ^ 2) ≤
        ((n : ℝ) + 1) ^ 2 * (16 * 16 ^ n) := by
      calc
        _ = (n + 2) * (((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ)) ^ 2 := by ring
        _ = (4 * (2 * (n : ℝ) + 1) ^ 2 * (n + 2)) *
            (n.centralBinom : ℝ) ^ 2 := by rw [hr]; ring
        _ ≤ (16 * ((n : ℝ) + 1) ^ 3) * (n.centralBinom : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hc (sq_nonneg _)
        _ = (16 * ((n : ℝ) + 1) ^ 2) *
            (((n : ℝ) + 1) * (n.centralBinom : ℝ) ^ 2) := by ring
        _ ≤ (16 * ((n : ℝ) + 1) ^ 2) * 16 ^ n :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by ring
    have := (mul_le_mul_iff_right₀ (sq_pos_of_pos hn)).mp hh
    rw [pow_succ (16 : ℝ) n]
    convert this using 1 <;> push_cast <;> first | rfl | ring

theorem choose_odd_le_twice_central (n k : ℕ) :
    (2 * n + 1).choose k ≤ 2 * n.centralBinom := by
  cases k with
  | zero => simp only [Nat.choose_zero_right]; have := Nat.centralBinom_pos n; omega
  | succ k =>
    rw [Nat.choose_succ_succ]
    have h₁ := Nat.choose_le_centralBinom k n
    have h₂ := Nat.choose_le_centralBinom (k + 1) n
    simpa [Nat.succ_eq_add_one, two_mul] using Nat.add_le_add h₁ h₂

theorem fairBinomial_square_bound (n k : ℕ) :
    ((n : ℝ) + 1) * fairBinomial n k ^ 2 ≤ 2 := by
  have hcases : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  rcases hcases with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hc : ((2 * m).choose k : ℝ) ≤ (m.centralBinom : ℝ) :=
      by exact_mod_cast Nat.choose_le_centralBinom k m
    have hcs : ((2 * m).choose k : ℝ) ^ 2 ≤ (m.centralBinom : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hc 2
    have ht := centralBinom_square_bound m
    have hp : ((2 : ℝ) ^ (2 * m)) ^ 2 = 16 ^ m := by
      rw [← pow_mul, show 2 * m * 2 = 4 * m by omega, pow_mul]
      norm_num
    unfold fairBinomial
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ (2 * m)) ^ 2)]
    rw [hp]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hcs (show (0 : ℝ) ≤ m + 1 by positivity),
      sq_nonneg ((2 * m).choose k : ℝ)]
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have hc : ((2 * m + 1).choose k : ℝ) ≤ 2 * (m.centralBinom : ℝ) :=
      by exact_mod_cast choose_odd_le_twice_central m k
    have hcs : ((2 * m + 1).choose k : ℝ) ^ 2 ≤ 4 * (m.centralBinom : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((2 * m + 1).choose k : ℝ)) hc 2
      nlinarith
    have ht := centralBinom_square_bound m
    have hp : ((2 : ℝ) ^ (2 * m + 1)) ^ 2 = 4 * 16 ^ m := by
      rw [pow_add, mul_pow, ← pow_mul, show 2 * m * 2 = 4 * m by omega, pow_mul]
      norm_num
      ring
    unfold fairBinomial
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ (2 * m + 1)) ^ 2)]
    rw [hp]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hcs (show (0 : ℝ) ≤ m + 1 by positivity)]


/-! ## Discrete convolution estimates for the hidden displacement kernels -/

/-! The probability generating series of the fair binomial kernel. -/

theorem binomialBound_nonneg (n : ℕ) : 0 ≤ binomialBound n := Real.sqrt_nonneg _

theorem fairBinomial_le_bound (n k : ℕ) : fairBinomial n k ≤ binomialBound n := by
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  simpa only [mul_comm] using fairBinomial_square_bound n k

theorem fairSeries_coeff_bound (n : ℕ) (z : ℤ) :
    |(fairSeries n).coeff z| ≤ binomialBound n := by
  by_cases hz : 0 ≤ z
  · rw [← Int.toNat_of_nonneg hz, fairSeries_coeff_nat,
      abs_of_nonneg (fairBinomial_nonneg _ _)]
    exact fairBinomial_le_bound _ _
  · rw [fairSeries_coeff_neg n z (by omega), abs_zero]
    exact binomialBound_nonneg n


/-! ## Nonfair anti-concentration without an assumed Stirling estimate -/

theorem binomialMass_harmonic_step (n k : ℕ) (p : ℝ) :
    ((n : ℝ) + 1) * p * (binomialMass n p k / ((k : ℝ) + 1)) =
      binomialMass (n + 1) p (k + 1) := by
  have hc : ((n : ℝ) + 1) * (n.choose k : ℝ) =
      ((n + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  unfold binomialMass
  rw [Nat.add_sub_add_right, pow_succ]
  field_simp
  nlinarith [congrArg (fun x : ℝ => x * p ^ k * (1 - p) ^ (n - k) * p) hc]

theorem binomialMass_harmonic_identity (n : ℕ) (p : ℝ) :
    ((n : ℝ) + 1) * p *
      (∑ k ∈ Finset.range (n + 1), binomialMass n p k / ((k : ℝ) + 1)) =
    1 - (1 - p) ^ (n + 1) := by
  rw [Finset.mul_sum]
  simp_rw [binomialMass_harmonic_step]
  have h := sum_binomialMass (n + 1) p
  rw [Finset.sum_range_succ'] at h
  simp only [binomialMass, Nat.choose_zero_right, Nat.cast_one, pow_zero,
    mul_one, one_mul, Nat.sub_zero] at h ⊢
  linarith

theorem binomialMass_harmonic_le (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioc 0 1) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k / ((k : ℝ) + 1)) ≤
      1 / (((n : ℝ) + 1) * p) := by
  apply (le_div_iff₀ (mul_pos (by positivity) hp.1)).mpr
  rw [mul_comm, binomialMass_harmonic_identity]
  have h := pow_nonneg (sub_nonneg.mpr hp.2) (n + 1)
  linarith

/-- The weighted Cauchy--Schwarz step for mixing the fair estimates. -/
theorem weighted_sum_sq_le {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ i ∈ S, w i * f i) ^ 2 ≤ (∑ i ∈ S, w i) * ∑ i ∈ S, w i * f i ^ 2 := by
  have heq (i : ι) : w i * f i = Real.sqrt (w i) * (Real.sqrt (w i) * f i) := by
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hw i)]
  simp_rw [heq]
  apply (Finset.sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * f i)).trans_eq
  simp only [mul_pow, Real.sq_sqrt (hw _)]

theorem mixed_binomialBound_le (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioc 0 1) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k * binomialBound k) ≤
      Real.sqrt (2 / (((n : ℝ) + 1) * p)) := by
  have hw (k : ℕ) := binomialMass_nonneg n k (show p ∈ Set.Icc 0 1 from ⟨hp.1.le, hp.2⟩)
  have hs := weighted_sum_sq_le (Finset.range (n + 1)) (binomialMass n p)
    binomialBound hw
  rw [sum_binomialMass, one_mul] at hs
  have hb (k : ℕ) : binomialBound k ^ 2 = 2 / ((k : ℝ) + 1) :=
    Real.sq_sqrt (by positivity)
  simp_rw [hb] at hs
  have heq : (∑ k ∈ Finset.range (n + 1), binomialMass n p k * (2 / ((k : ℝ) + 1))) =
      2 * ∑ k ∈ Finset.range (n + 1), binomialMass n p k / ((k : ℝ) + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq] at hs
  have hh := binomialMass_harmonic_le n hp
  have hp0 := hp.1
  have hbound : (∑ k ∈ Finset.range (n + 1), binomialMass n p k * binomialBound k) ^ 2 ≤
      2 / (((n : ℝ) + 1) * p) := by
    calc
      _ ≤ 2 * ∑ k ∈ Finset.range (n + 1), binomialMass n p k / ((k : ℝ) + 1) := hs
      _ ≤ 2 * (1 / (((n : ℝ) + 1) * p)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  have hsr := Real.sq_sqrt (show (0 : ℝ) ≤ 2 / (((n : ℝ) + 1) * p) by positivity)
  have hpos := Real.sqrt_nonneg (2 / (((n : ℝ) + 1) * p))
  nlinarith only [hbound, hsr, hpos]


theorem mixedFairSeries_expansion (n : ℕ) (p : ℝ) :
    mixedFairSeries n p =
      ∑ k ∈ Finset.range (n + 1), binomialMass n p k • fairSeries k := by
  rw [mixedFairSeries, add_pow]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_pow, one_pow, smul_mul_smul, mul_one, fairSeries, pow_one]
  rw [mul_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  unfold binomialMass
  ring

theorem mixedFairSeries_eq_biased (n : ℕ) (p : ℝ) :
    mixedFairSeries n p = biasedSeries n (p / 2) := by
  unfold mixedFairSeries biasedSeries
  congr 1
  ext z
  simp only [fairSeries, pow_one, smul_add, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    smul_eq_mul, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> first | omega | ring

theorem mixedFairSeries_coeff_bound (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioc 0 1) (z : ℤ) :
    |(mixedFairSeries n p).coeff z| ≤ Real.sqrt (2 / (((n : ℝ) + 1) * p)) := by
  rw [mixedFairSeries_expansion, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), |binomialMass n p k * (fairSeries k).coeff z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), binomialMass n p k * binomialBound k := by
      apply Finset.sum_le_sum
      intro k _
      have hw := binomialMass_nonneg n k (show p ∈ Set.Icc 0 1 from ⟨hp.1.le, hp.2⟩)
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (fairSeries_coeff_bound k z) hw
    _ ≤ _ := mixed_binomialBound_le n hp

/-- At success probabilities at most 1/2, this gives the sharp variance
    scale up to an absolute constant, using only the fair-coin estimate. -/
theorem biasedSeries_coeff_bound_low (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioc 0 (1 / 2)) (z : ℤ) :
    |(biasedSeries n p).coeff z| ≤ Real.sqrt (1 / (((n : ℝ) + 1) * p)) := by
  have h2p : 2 * p ∈ Set.Ioc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have h := mixedFairSeries_coeff_bound n h2p z
  rw [mixedFairSeries_eq_biased, show 2 * p / 2 = p by ring] at h
  have heq : 2 / (((n : ℝ) + 1) * (2 * p)) = 1 / (((n : ℝ) + 1) * p) := by
    field_simp
  rwa [heq] at h


theorem biasedSeries_sum (n : ℕ) (p : ℝ) :
    biasedSeries n p = ∑ k ∈ Finset.range (n + 1),
      AddMonoidAlgebra.single (k : ℤ) (binomialMass n p k) := by
  rw [biasedSeries, add_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.single_mul_single]
  simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero]
  congr 1
  unfold binomialMass
  ring

theorem biasedSeries_coeff_nat (n k : ℕ) (p : ℝ) :
    (biasedSeries n p).coeff (k : ℤ) = binomialMass n p k := by
  rw [biasedSeries_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  by_cases hk : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_true]
    · intro b _ hb
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Nat.cast_inj, ite_eq_right hb]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  · rw [Finset.sum_eq_zero]
    · simp [binomialMass, Nat.choose_eq_zero_of_lt (by omega : n < k)]
    · intro b hb
      have hbk : b ≠ k := by simp only [Finset.mem_range] at hb; omega
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Nat.cast_inj, ite_eq_right hbk]

theorem biasedSeries_coeff_neg (n : ℕ) (p : ℝ) (z : ℤ) (hz : z < 0) :
    (biasedSeries n p).coeff z = 0 := by
  rw [biasedSeries_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  have h : (b : ℤ) ≠ z := by omega
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right h]

theorem biasedSeries_coeff_high (n : ℕ) (p : ℝ) (z : ℤ) (hz : (n : ℤ) < z) :
    (biasedSeries n p).coeff z = 0 := by
  rw [biasedSeries_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b hb
  have h : (b : ℤ) ≠ z := by simp only [Finset.mem_range] at hb; omega
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right h]

theorem binomialMass_symm (n k : ℕ) (p : ℝ) (hk : k ≤ n) :
    binomialMass n (1 - p) (n - k) = binomialMass n p k := by
  unfold binomialMass
  rw [Nat.choose_symm hk, Nat.sub_sub_self hk, show 1 - (1 - p) = p by ring]
  ring

theorem biasedSeries_coeff_reflect (n : ℕ) (p : ℝ) (z : ℤ) :
    (biasedSeries n (1 - p)).coeff ((n : ℤ) - z) = (biasedSeries n p).coeff z := by
  by_cases hz : z < 0
  · rw [biasedSeries_coeff_neg n p z hz,
      biasedSeries_coeff_high n (1 - p) _ (by omega)]
  by_cases hz' : (n : ℤ) < z
  · rw [biasedSeries_coeff_high n p z hz',
      biasedSeries_coeff_neg n (1 - p) _ (by omega)]
  have h0 : 0 ≤ z := by omega
  have hk : z.toNat ≤ n := by omega
  have hzN : (z.toNat : ℤ) = z := Int.toNat_of_nonneg h0
  have hsub : (n : ℤ) - z = ((n - z.toNat : ℕ) : ℤ) := by omega
  rw [hsub, ← hzN, biasedSeries_coeff_nat, biasedSeries_coeff_nat]
  exact binomialMass_symm n z.toNat p hk

/-- Uniform nonfair-binomial anti-concentration.  This is the absolute
    variance-scale upper bound used in the manuscript's rank kernels. -/
theorem biasedSeries_coeff_bound (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (z : ℤ) :
    |(biasedSeries n p).coeff z| ≤
      Real.sqrt (1 / (((n : ℝ) + 1) * p * (1 - p))) := by
  by_cases hlow : p ≤ 1 / 2
  · apply (biasedSeries_coeff_bound_low n ⟨hp.1, hlow⟩ z).trans
    apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · have hn : (0 : ℝ) ≤ n + 1 := by positivity
      nlinarith [mul_nonneg hn (sq_nonneg p)]
  · have hq : 1 - p ∈ Set.Ioc 0 (1 / 2) := ⟨by linarith [hp.2], by linarith⟩
    rw [← biasedSeries_coeff_reflect n p z]
    apply (biasedSeries_coeff_bound_low n hq ((n : ℤ) - z)).trans
    apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity)
        (mul_nonneg (sub_nonneg.mpr hp.2.le) (sub_nonneg.mpr hp.2.le))]


theorem binomialMass_mul_index (n k : ℕ) (p : ℝ) :
    binomialMass (n + 1) p (k + 1) * ((k : ℝ) + 1) =
      ((n : ℝ) + 1) * p * binomialMass n p k := by
  have h := binomialMass_harmonic_step n k p
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [← h]
  field_simp

theorem binomialMass_index_sum (n : ℕ) (p : ℝ) (F : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 2), binomialMass (n + 1) p k * (k : ℝ) * F k) =
      ((n : ℝ) + 1) * p *
        ∑ k ∈ Finset.range (n + 1), binomialMass n p k * F (k + 1) := by
  rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
  simp_rw [binomialMass_mul_index]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem binomialMass_mean (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n + 1), binomialMass n p k * (k : ℝ) = (n : ℝ) * p := by
  cases n with
  | zero => simp
  | succ n =>
    simpa only [mul_one, sum_binomialMass, Nat.cast_add, Nat.cast_one] using
      binomialMass_index_sum n p (fun _ => 1)

theorem binomialMass_second_moment (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n + 1), binomialMass n p k * (k : ℝ) ^ 2 =
      (n : ℝ) * ((n : ℝ) - 1) * p ^ 2 + (n : ℝ) * p := by
  cases n with
  | zero => simp
  | succ n =>
    have h := binomialMass_index_sum n p (fun k => k)
    simp only [Nat.cast_add, Nat.cast_one] at h ⊢
    simp_rw [mul_add, mul_one, Finset.sum_add_distrib, binomialMass_mean,
      sum_binomialMass] at h
    calc
      _ = ∑ k ∈ Finset.range (n + 2), binomialMass (n + 1) p k * (k : ℝ) * (k : ℝ) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [h]; ring

theorem binomialMass_variance (n : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k * ((k : ℝ) - (n : ℝ) * p) ^ 2) =
      (n : ℝ) * p * (1 - p) := by
  calc
    _ = (∑ k ∈ Finset.range (n + 1), binomialMass n p k * (k : ℝ) ^ 2) -
        2 * (n : ℝ) * p * (∑ k ∈ Finset.range (n + 1), binomialMass n p k * (k : ℝ)) +
        ((n : ℝ) * p) ^ 2 * (∑ k ∈ Finset.range (n + 1), binomialMass n p k) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [binomialMass_second_moment, binomialMass_mean, sum_binomialMass]; ring

theorem binomialMass_adjacent (n k : ℕ) (p : ℝ) (hk : k < n) :
    ((k : ℝ) + 1) * (1 - p) * binomialMass n p (k + 1) =
      ((n : ℝ) - k) * p * binomialMass n p k := by
  have hc : (n.choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
      (n.choose k : ℝ) * ((n : ℝ) - (k : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk.le] using
      congrArg (fun t : ℕ => (t : ℝ)) (Nat.choose_succ_right_eq n k)
  have hnk : n - k = (n - (k + 1)) + 1 := by omega
  unfold binomialMass
  rw [hnk, pow_succ, pow_succ]
  linear_combination p ^ k * p * (1 - p) ^ (n - (k + 1)) * (1 - p) * hc

theorem binomialMass_le_mode (n l k : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hl : l ≤ n) (hmean : (n : ℝ) * p = l) :
    binomialMass n p k ≤ binomialMass n p l := by
  have h0 (j : ℕ) := binomialMass_nonneg n j ⟨hp.1.le, hp.2.le⟩
  have hleft (j : ℕ) (hj : j < l) : binomialMass n p j ≤ binomialMass n p (j + 1) := by
    have hrec := binomialMass_adjacent n j p (by omega)
    have hjr : (j : ℝ) + 1 ≤ l := by exact_mod_cast hj
    have hcoef : (0 : ℝ) < ((j : ℝ) + 1) * (1 - p) := by
      exact mul_pos (by positivity) (sub_pos.mpr hp.2)
    have hdiff : ((j : ℝ) + 1) * (1 - p) ≤ ((n : ℝ) - j) * p := by
      nlinarith [hp.1]
    have := mul_le_mul_of_nonneg_right hdiff (h0 j)
    nlinarith only [hrec, this, hcoef]
  have hright (j : ℕ) (hj : l ≤ j) : binomialMass n p (j + 1) ≤ binomialMass n p j := by
    by_cases hjn : j < n
    · have hrec := binomialMass_adjacent n j p hjn
      have hjr : (l : ℝ) ≤ j := by exact_mod_cast hj
      have hcoef : (0 : ℝ) < ((j : ℝ) + 1) * (1 - p) := by
        exact mul_pos (by positivity) (sub_pos.mpr hp.2)
      have hdiff : ((n : ℝ) - j) * p ≤ ((j : ℝ) + 1) * (1 - p) := by
        nlinarith [hp.2]
      have := mul_le_mul_of_nonneg_right hdiff (h0 j)
      nlinarith only [hrec, this, hcoef]
    · have hjn' : n < j + 1 := by omega
      simp only [binomialMass, Nat.choose_eq_zero_of_lt hjn', Nat.cast_zero, zero_mul]
      exact h0 j
  rcases le_total k l with hk | hk
  · have haux : ∀ b : ℕ, k ≤ b → b ≤ l → binomialMass n p k ≤ binomialMass n p b := by
      intro b hkb
      induction b, hkb using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ b hb ih =>
        intro hbl
        exact (ih (by omega)).trans (hleft b (by omega))
    exact haux l hk le_rfl
  · induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih => exact (hright j hj).trans ih


/-- A discrete law cannot have a very small maximum when its variance is bounded.
The explicit constant is deliberately loose, avoiding any use of Stirling. -/
theorem discrete_mode_lower (n l : ℕ) (f : ℕ → ℝ) (M v : ℝ)
    (hf : ∀ k, 0 ≤ f k) (hsum : ∑ k ∈ Finset.range (n + 1), f k = 1)
    (hmax : ∀ k, f k ≤ M)
    (hvar : ∑ k ∈ Finset.range (n + 1), f k * ((k : ℝ) - l) ^ 2 = v)
    (hv : 1 ≤ v) : 1 / (12 * Real.sqrt v) ≤ M := by
  classical
  let r : ℕ := ⌈2 * Real.sqrt v⌉₊
  have hv0 : 0 ≤ v := by linarith
  have hs : 1 ≤ Real.sqrt v := Real.one_le_sqrt.mpr hv
  have hs2 := Real.sq_sqrt hv0
  have hrlo : 2 * Real.sqrt v ≤ (r : ℝ) := Nat.le_ceil _
  have hrhi : (r : ℝ) < 2 * Real.sqrt v + 1 := Nat.ceil_lt_add_one (by positivity)
  have hrpos : (0 : ℝ) < r := by linarith
  have hM : 0 ≤ M := (hf 0).trans (hmax 0)
  let S := (Finset.range (n + 1)).filter (fun k => l - r ≤ k ∧ k ≤ l + r)
  have hcard : S.card ≤ 2 * r + 1 := by
    have hsub : S ⊆ Finset.Icc (l - r) (l + r) := by
      intro k hk
      exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hk).2
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  have hout (k : ℕ) (hk : ¬(l - r ≤ k ∧ k ≤ l + r)) :
      (r : ℝ) ^ 2 ≤ ((k : ℝ) - l) ^ 2 := by
    by_cases hleft : k < l - r
    · have hnat : k + r < l := by omega
      have hreal : (k : ℝ) + r < l := by exact_mod_cast hnat
      nlinarith [sq_nonneg ((l : ℝ) - k - r)]
    · have hnat : l + r < k := by omega
      have hreal : (l : ℝ) + r < k := by exact_mod_cast hnat
      nlinarith [sq_nonneg ((k : ℝ) - l - r)]
  have hpoint (k : ℕ) : (r : ℝ) ^ 2 * f k ≤
      (if l - r ≤ k ∧ k ≤ l + r then (r : ℝ) ^ 2 * M else 0) +
        f k * ((k : ℝ) - l) ^ 2 := by
    split_ifs with hk
    · have := mul_le_mul_of_nonneg_left (hmax k) (sq_nonneg (r : ℝ))
      have := mul_nonneg (hf k) (sq_nonneg ((k : ℝ) - l))
      linarith
    · simpa only [zero_add, mul_comm] using mul_le_mul_of_nonneg_left (hout k hk) (hf k)
  have htotal := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (n + 1)) => hpoint k)
  rw [← Finset.mul_sum, hsum, mul_one, Finset.sum_add_distrib, hvar,
    ← Finset.sum_filter] at htotal
  change (r : ℝ) ^ 2 ≤ ∑ k ∈ S, (r : ℝ) ^ 2 * M + v at htotal
  rw [Finset.sum_const, nsmul_eq_mul] at htotal
  have hcardR : (S.card : ℝ) ≤ 2 * r + 1 := by exact_mod_cast hcard
  have hbound := mul_le_mul_of_nonneg_right hcardR (mul_nonneg (sq_nonneg (r : ℝ)) hM)
  have htotal' : (r : ℝ) ^ 2 ≤ (2 * r + 1) * ((r : ℝ) ^ 2 * M) + v := by
    linarith
  have hrv : 4 * v ≤ (r : ℝ) ^ 2 := by nlinarith [sq_nonneg ((r : ℝ) - 2 * Real.sqrt v)]
  have hcancel : (3 : ℝ) / 4 ≤ (2 * r + 1) * M := by
    have hrr : (0 : ℝ) < (r : ℝ) ^ 2 := sq_pos_of_pos hrpos
    nlinarith only [htotal', hrv, hrr]
  have hsize : 2 * (r : ℝ) + 1 ≤ 7 * Real.sqrt v := by linarith
  have hfinal := mul_le_mul_of_nonneg_right hsize hM
  apply (div_le_iff₀ (by positivity : 0 < 12 * Real.sqrt v)).mpr
  nlinarith only [hcancel, hfinal]

theorem binomialMass_mean_lower (n l : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hl : l ≤ n) (hmean : (n : ℝ) * p = l) (hv : 1 ≤ (n : ℝ) * p * (1 - p)) :
    1 / (12 * Real.sqrt ((n : ℝ) * p * (1 - p))) ≤ binomialMass n p l := by
  apply discrete_mode_lower n l (binomialMass n p)
    (binomialMass n p l) ((n : ℝ) * p * (1 - p))
  · intro k; exact binomialMass_nonneg n k ⟨hp.1.le, hp.2.le⟩
  · exact sum_binomialMass n p
  · intro k; exact binomialMass_le_mode n l k hp hl hmean
  · rw [← hmean]; exact binomialMass_variance n p
  · exact hv


theorem binomialMass_mean_inverse_sq (n l : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hl : l ≤ n) (hmean : (n : ℝ) * p = l) (hv : 1 ≤ (n : ℝ) * p * (1 - p)) :
    (binomialMass n p l)⁻¹ ^ 2 ≤ 144 * ((n : ℝ) * p * (1 - p)) := by
  have hs : 0 < Real.sqrt ((n : ℝ) * p * (1 - p)) :=
    Real.sqrt_pos.mpr (by linarith)
  have hlow := binomialMass_mean_lower n l hp hl hmean hv
  have hpos : 0 < binomialMass n p l := lt_of_lt_of_le (by positivity) hlow
  have hi : (binomialMass n p l)⁻¹ ≤ 12 * Real.sqrt ((n : ℝ) * p * (1 - p)) := by
    rw [← one_div]
    apply (div_le_iff₀ hpos).mpr
    have := (div_le_iff₀ (by positivity)).mp hlow
    nlinarith only [this]
  have his := sq_le_sq₀ (by positivity) (by positivity) |>.mpr hi
  have hs2 := Real.sq_sqrt (show 0 ≤ (n : ℝ) * p * (1 - p) by linarith)
  nlinarith only [his, hs2]

/-! ## Gaussian overlap by exponential tilting of the exact binomial law -/

end TraceReconstruction

namespace TraceReconstruction

theorem hypergeomMass_eq_binomial (V M m v : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (hm : m ≤ V+M) (hv : v ≤ m) :
    hypergeomMass V M m v = binomialMass V p v * binomialMass M p (m-v) /
      binomialMass (V+M) p m := by
  unfold hypergeomMass
  rw [ite_eq_left hv]
  by_cases hvV : v ≤ V
  · by_cases hkM : m-v ≤ M
    · unfold binomialMass
      have hc : (0 : ℝ) < (V+M).choose m := by exact_mod_cast Nat.choose_pos hm
      have hp1 := hp.1
      have hq1 := sub_pos.mpr hp.2
      have he : V-v+(M-(m-v)) = V+M-m := by omega
      have he' : v+(m-v) = m := by omega
      apply (div_eq_div_iff (ne_of_gt hc) (by positivity)).mpr
      calc
        _ = ((V.choose v : ℝ) * (M.choose (m-v) : ℝ) * ((V+M).choose m : ℝ)) *
            (p^m * (1-p)^(V+M-m)) := by ring
        _ = _ := by
          rw [show p^m = p^v * p^(m-v) by rw [← pow_add, he'],
            show (1-p)^(V+M-m) = (1-p)^(V-v)*(1-p)^(M-(m-v)) by rw [← pow_add, he]]
          ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : M < m-v)]
      simp [binomialMass, Nat.choose_eq_zero_of_lt (by omega : M < m-v)]
  · rw [Nat.choose_eq_zero_of_lt (by omega : V < v)]
    simp [binomialMass, Nat.choose_eq_zero_of_lt (by omega : V < v)]

theorem binomialMass_sq_upper (n k : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    binomialMass n p k ^ 2 ≤ 1 / (((n : ℝ)+1)*p*(1-p)) := by
  have hp1 := hp.1
  have hq1 := sub_pos.mpr hp.2
  have h := biasedSeries_coeff_bound n hp (k : ℤ)
  rw [biasedSeries_coeff_nat, abs_of_nonneg (binomialMass_nonneg n k ⟨hp.1.le,hp.2.le⟩)] at h
  have hs := sq_le_sq₀ (binomialMass_nonneg n k ⟨hp.1.le,hp.2.le⟩)
    (Real.sqrt_nonneg _) |>.mpr h
  rwa [Real.sq_sqrt (by positivity)] at hs

theorem hypergeomMass_sq_upper (V M m v : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (hm : m ≤ V+M) (hmean : (m : ℝ) = (V+M : ℕ)*p)
    (hvar : 1 ≤ (V+M : ℕ)*p*(1-p)) :
    hypergeomMass V M m v ^ 2 ≤
      144 * (V+M : ℕ) / (((V : ℝ)+1)*((M : ℝ)+1)*p*(1-p)) := by
  have hp1 := hp.1
  have hq1 := sub_pos.mpr hp.2
  by_cases hv : v ≤ m
  · rw [hypergeomMass_eq_binomial V M m v hp hm hv, div_eq_mul_inv, mul_pow, mul_pow]
    have hV := binomialMass_sq_upper V v hp
    have hM := binomialMass_sq_upper M (m-v) hp
    have hN := binomialMass_mean_inverse_sq (V+M) m hp hm hmean.symm hvar
    have hvm := mul_le_mul hV hM (sq_nonneg _) (by positivity)
    have h := mul_le_mul hvm hN (sq_nonneg _) (by positivity)
    apply h.trans
    have hp0 : p ≠ 0 := ne_of_gt hp.1
    have hq0 : 1-p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
    have hV0 : (V : ℝ)+1 ≠ 0 := by positivity
    have hM0 : (M : ℝ)+1 ≠ 0 := by positivity
    apply le_of_eq
    field_simp
  · simp only [hypergeomMass, ite_eq_right hv, zero_pow (by decide : 2 ≠ 0)]
    positivity

theorem hypergeomMass_high (V M m v : ℕ) (hv : V < v) : hypergeomMass V M m v = 0 := by
  unfold hypergeomMass
  rw [Nat.choose_eq_zero_of_lt hv]
  simp

/-- Adjacent-mass identity for the hidden count. The central regime has full support
on 0,...,M; this is exactly the regime used in adjacent-power lifting. -/
theorem hypergeom_hidden_adjacent (V M m k : ℕ) (hM : M ≤ m) (hV : m ≤ V) (hk : k < M) :
    (((k:ℝ)+1)*((V:ℝ)-m+k+1)) * hypergeomMass M V m (k+1) =
    (((M:ℝ)-k)*((m:ℝ)-k)) * hypergeomMass M V m k := by
  have hkM : k ≤ M := by omega
  have hkm : k ≤ m := by omega
  have hkm' : k+1 ≤ m := by omega
  have hv : m-(k+1) ≤ V := by omega
  have h1 := Nat.choose_succ_right_eq M k
  have h2 := Nat.choose_succ_right_eq V (m-(k+1))
  rw [show m-(k+1)+1=m-k by omega] at h2
  have h1' : (M.choose (k+1):ℝ)*((k:ℝ)+1) = (M.choose k:ℝ)*((M:ℝ)-k) := by
    exact_mod_cast h1
  have h2' : (V.choose (m-k):ℝ)*((m:ℝ)-k) =
      (V.choose (m-(k+1)):ℝ)*((V:ℝ)-m+k+1) := by
    have hvsub : V-(m-(k+1)) = V-m+k+1 := by omega
    rw [hvsub] at h2
    exact_mod_cast h2
  unfold hypergeomMass
  rw [ite_eq_left hkm', ite_eq_left hkm]
  have hmul := congrArg (fun z : ℝ => z*(V.choose (m-(k+1)) : ℝ)*((V:ℝ)-m+k+1)) h1'
  have hmul' := congrArg (fun z : ℝ => z*(M.choose k : ℝ)*((M:ℝ)-k)) h2'
  have he : (((k:ℝ)+1)*((V:ℝ)-m+k+1)) *
        ((M.choose (k+1):ℝ)*(V.choose (m-(k+1)):ℝ)) =
      (((M:ℝ)-k)*((m:ℝ)-k))*((M.choose k:ℝ)*(V.choose (m-k):ℝ)) := by
    nlinarith only [hmul, hmul']
  simpa only [mul_div_assoc] using congrArg (fun z : ℝ => z/((M+V).choose m:ℝ)) he

theorem hypergeomHiddenMode_le (V M m : ℕ) (hV : m ≤ V) :
    hypergeomHiddenMode V M m ≤ M := by
  unfold hypergeomHiddenMode
  have h1 : (M+1)*(m+1) < (M+1)*(V+M+2) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hh : (M+1)*(m+1)/(V+M+2) < M+1 := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    exact h1
  omega

theorem hypergeom_hidden_unimodal_left (V M m k : ℕ) (hM : M ≤ m) (hV : m ≤ V)
    (hk : k < hypergeomHiddenMode V M m) :
    hypergeomMass M V m k ≤ hypergeomMass M V m (k+1) := by
  have hl := hypergeomHiddenMode_le V M m hV
  have hkM : k < M := by omega
  have hrec := hypergeom_hidden_adjacent V M m k hM hV hkM
  have hc : (k+1)*(V+M+2) ≤ (M+1)*(m+1) := by
    have hh : k+1 ≤ (M+1)*(m+1)/(V+M+2) := hk
    exact (Nat.le_div_iff_mul_le (by omega)).mp hh
  have hc' : ((k:ℝ)+1)*((V:ℝ)+M+2) ≤ ((M:ℝ)+1)*((m:ℝ)+1) := by exact_mod_cast hc
  have hh : ((k:ℝ)+1)*((V:ℝ)-m+k+1) ≤ ((M:ℝ)-k)*((m:ℝ)-k) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hh (hypergeomMass_nonneg M V m k)
  have hV' : (m:ℝ) ≤ V := by exact_mod_cast hV
  have ha : 0 < ((k:ℝ)+1)*((V:ℝ)-m+k+1) := by positivity
  exact (mul_le_mul_iff_right₀ ha).mp (by nlinarith only [hm, hrec])

theorem hypergeom_hidden_unimodal_right (V M m k : ℕ) (hM : M ≤ m) (hV : m ≤ V)
    (hk : hypergeomHiddenMode V M m ≤ k) :
    hypergeomMass M V m (k+1) ≤ hypergeomMass M V m k := by
  by_cases hkM : k < M
  · have hrec := hypergeom_hidden_adjacent V M m k hM hV hkM
    have hc : (M+1)*(m+1) < (k+1)*(V+M+2) := by
      apply (Nat.div_lt_iff_lt_mul (by omega)).mp
      exact Nat.lt_succ_of_le hk
    have hc' : ((M:ℝ)+1)*((m:ℝ)+1) < ((k:ℝ)+1)*((V:ℝ)+M+2) := by exact_mod_cast hc
    have hh : ((M:ℝ)-k)*((m:ℝ)-k) ≤ ((k:ℝ)+1)*((V:ℝ)-m+k+1) := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hh (hypergeomMass_nonneg M V m k)
    have hV' : (m:ℝ) ≤ V := by exact_mod_cast hV
    have ha : 0 < ((k:ℝ)+1)*((V:ℝ)-m+k+1) := by positivity
    exact (mul_le_mul_iff_right₀ ha).mp (by nlinarith only [hm, hrec])
  · rw [hypergeomMass_high M V m (k+1) (by omega)]
    exact hypergeomMass_nonneg M V m k

/-- Exact total variation of a zero-extended unimodal sequence. -/
theorem unimodal_variation (f : ℕ → ℝ) (n l : ℕ) (hl : l ≤ n+1)
    (hleft : ∀ k < l, f k ≤ f (k+1))
    (hright : ∀ k, l ≤ k → f (k+1) ≤ f k) (hz : f (n+1)=0) :
    f 0 + ∑ k ∈ Finset.range (n+1), |f (k+1)-f k| = 2*f l := by
  rw [← Finset.sum_range_add_sum_Ico _ hl]
  have h1 : (∑ k ∈ Finset.range l, |f (k+1)-f k|) = f l-f 0 := by
    rw [← Finset.sum_range_sub f l]
    apply Finset.sum_congr rfl
    intro k hk
    exact abs_of_nonneg (sub_nonneg.mpr (hleft k (Finset.mem_range.mp hk)))
  have h2 : (∑ k ∈ Finset.Ico l (n+1), |f (k+1)-f k|) = f l-f (n+1) := by
    calc
      _ = ∑ k ∈ Finset.Ico l (n+1), -(f (k+1)-f k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact abs_of_nonpos (sub_nonpos.mpr (hright k (Finset.mem_Ico.mp hk).1))
      _ = _ := by rw [Finset.sum_neg_distrib, Finset.sum_Ico_sub _ hl]; ring
  rw [h1,h2,hz]
  ring

theorem hypergeom_hidden_variation (V M m : ℕ) (hM : M ≤ m) (hV : m ≤ V) :
    hypergeomMass M V m 0 +
      ∑ k ∈ Finset.range (M+1), |hypergeomMass M V m (k+1)-hypergeomMass M V m k| =
      2*hypergeomMass M V m (hypergeomHiddenMode V M m) := by
  apply unimodal_variation _ M (hypergeomHiddenMode V M m)
    ((hypergeomHiddenMode_le V M m hV).trans (by omega))
    (fun k hk => hypergeom_hidden_unimodal_left V M m k hM hV hk)
    (fun k hk => hypergeom_hidden_unimodal_right V M m k hM hV hk)
  exact hypergeomMass_high M V m (M+1) (by omega)
theorem choose_pred_weight (n r : ℕ) (hn : 0 < n) (hr : r ≤ n) :
    (n:ℝ)*((n-1).choose r : ℝ) = ((n:ℝ)-r)*(n.choose r : ℝ) := by
  have h := Nat.choose_mul_succ_eq (n-1) r
  rw [Nat.sub_add_cancel hn] at h
  have h' : ((n-1).choose r : ℝ)*(n:ℝ) = (n.choose r : ℝ)*((n:ℝ)-r) := by
    exact_mod_cast h
  nlinarith only [h']

theorem choose_pred_weight_succ (n r : ℕ) (hn : 0 < n) :
    (n:ℝ)*((n-1).choose r : ℝ) = ((r:ℝ)+1)*(n.choose (r+1) : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (n-1) r
  rw [Nat.sub_add_cancel hn] at h
  exact_mod_cast h.trans (Nat.mul_comm _ _)

theorem hypergeomHiddenFlux_formula (V M m k : ℕ) (hM : M ≤ m) (hV : m < V) (hk : k ≤ M) :
    hypergeomHiddenFlux V M m k =
      ((V:ℝ)-m+k)/((V:ℝ)+M-m)*hypergeomMass M V m k := by
  have hN : 0 < V+M := by omega
  have hk' : k ≤ m := by omega
  have hr : m-k ≤ V := by omega
  have hmN : m ≤ V+M := by omega
  have hpred : m ≤ V+M-1 := by omega
  have hVN : (0:ℝ) < V+M := by exact_mod_cast hN
  have hd : (0:ℝ) < (V:ℝ)+M-m := by
    have hr : (m:ℝ) < (V:ℝ)+M := by exact_mod_cast (show m < V+M by omega)
    linarith
  have hCN : (0:ℝ) < (V+M).choose m := by exact_mod_cast Nat.choose_pos hmN
  have hCP : (0:ℝ) < (V+M-1).choose m := by exact_mod_cast Nat.choose_pos hpred
  have hcw := choose_pred_weight (V+M) m hN hmN
  have hcv := choose_pred_weight V (m-k) (by omega) hr
  push_cast [Nat.cast_sub hk'] at hcv
  push_cast at hcw
  unfold hypergeomHiddenFlux hypergeomMass
  rw [ite_eq_left hk', ite_eq_left hk', show M+(V-1)=V+M-1 by omega]
  have hden : ((V:ℝ)+M)*((V+M-1).choose m:ℝ) =
      ((V:ℝ)+M-m)*((V+M).choose m:ℝ) := hcw
  rw [show M+V=V+M by omega]
  calc
    _ = (M.choose k:ℝ)*((V:ℝ)*((V-1).choose (m-k):ℝ)) /
        (((V:ℝ)+M)*((V+M-1).choose m:ℝ)) := by field_simp
    _ = _ := by rw [hden, hcv]; field_simp; ring

theorem hypergeomHiddenFlux_high (V M m k : ℕ) (hk : M < k) :
    hypergeomHiddenFlux V M m k = 0 := by
  simp only [hypergeomHiddenFlux, hypergeomMass_high M (V-1) m k hk, mul_zero]

theorem hypergeomHiddenFlux_boundary (V M m : ℕ) (hM : M ≤ m) (hV : m < V) :
    hypergeomHiddenFlux V M m M = hypergeomMass M V m M := by
  rw [hypergeomHiddenFlux_formula V M m M hM hV le_rfl]
  have hd : (0:ℝ) < (V:ℝ)+M-m := by
    have hr : (m:ℝ) < (V:ℝ)+M := by exact_mod_cast (show m < V+M by omega)
    linarith
  have he : (V:ℝ)-m+M = (V:ℝ)+M-m := by ring
  rw [he, div_self hd.ne', one_mul]

theorem hypergeom_adjacent_hidden_difference (V M m k : ℕ)
    (hM : M ≤ m) (hV : m < V) (hk : k ≤ M) :
    hypergeomMass M V (m+1) (k+1) - hypergeomMass M V m k =
      hypergeomHiddenFlux V M m (k+1) - hypergeomHiddenFlux V M m k := by
  by_cases hkM : k = M
  · subst k
    rw [hypergeomMass_high M V (m+1) (M+1) (by omega),
      hypergeomHiddenFlux_high V M m (M+1) (by omega), hypergeomHiddenFlux_boundary V M m hM hV]
  have hklt : k < M := by omega
  have hkm : k+1 ≤ m := by omega
  have hkm' : k ≤ m := by omega
  have hN : 0 < V+M := by omega
  have hmN : m ≤ V+M := by omega
  have hmN' : m+1 ≤ V+M := by omega
  have hpred : m ≤ V+M-1 := by omega
  have hN0 : (0:ℝ) < (V:ℝ)+M := by exact_mod_cast hN
  have hCN : (0:ℝ) < (V+M).choose m := by exact_mod_cast Nat.choose_pos hmN
  have hCN' : (0:ℝ) < (V+M).choose (m+1) := by exact_mod_cast Nat.choose_pos hmN'
  have hCP : (0:ℝ) < (V+M-1).choose m := by exact_mod_cast Nat.choose_pos hpred
  have hcw := choose_pred_weight (V+M) m hN hmN
  have hcws := choose_pred_weight_succ (V+M) m hN
  have hcv := choose_pred_weight V (m-k) (by omega) (by omega)
  have hcvs := choose_pred_weight_succ V (m-(k+1)) (by omega)
  rw [show m-(k+1)+1=m-k by omega] at hcvs
  have hMrec := Nat.choose_succ_right_eq M k
  have hMrec' : (M.choose (k+1):ℝ)*((k:ℝ)+1) = (M.choose k:ℝ)*((M:ℝ)-k) := by
    exact_mod_cast hMrec
  push_cast at hcw hcws
  push_cast [Nat.cast_sub hkm'] at hcv
  push_cast [Nat.cast_sub hkm] at hcvs
  unfold hypergeomHiddenFlux hypergeomMass
  rw [ite_eq_left (by omega : k+1 ≤ m+1), ite_eq_left hkm', ite_eq_left hkm, ite_eq_left hkm',
    show m+1-(k+1)=m-k by omega, show M+V=V+M by omega,
    show M+(V-1)=V+M-1 by omega]
  have hpold : (M.choose k:ℝ)*(V.choose (m-k):ℝ)/( (V+M).choose m:ℝ) =
      ((V:ℝ)+M-m)*(M.choose k:ℝ)*(V.choose (m-k):ℝ) /
      (((V:ℝ)+M)*((V+M-1).choose m:ℝ)) := by
    apply (div_eq_div_iff hCN.ne' (mul_pos hN0 hCP).ne').mpr
    rw [hcw]; ring
  have hpnew : (M.choose (k+1):ℝ)*(V.choose (m-k):ℝ)/( (V+M).choose (m+1):ℝ) =
      ((m:ℝ)+1)*(M.choose (k+1):ℝ)*(V.choose (m-k):ℝ) /
      (((V:ℝ)+M)*((V+M-1).choose m:ℝ)) := by
    apply (div_eq_div_iff hCN'.ne' (mul_pos hN0 hCP).ne').mpr
    rw [hcws]; ring
  rw [hpold,hpnew]
  have hF (j : ℕ) : (V:ℝ)/((V:ℝ)+M)*((M.choose j:ℝ)*((V-1).choose (m-j):ℝ)/
      ((V+M-1).choose m:ℝ)) = (M.choose j:ℝ)*((V:ℝ)*((V-1).choose (m-j):ℝ)) /
      (((V:ℝ)+M)*((V+M-1).choose m:ℝ)) := by field_simp
  rw [hF, hF, hcv, hcvs]
  rw [← sub_div, ← sub_div]
  congr 1
  have hh := congrArg (fun z : ℝ => z*(V.choose (m-k):ℝ)) hMrec'
  nlinarith only [hh]


theorem hypergeom_next_zero (V M m : ℕ) (hV : m < V) :
    hypergeomMass M V (m+1) 0 = hypergeomHiddenFlux V M m 0 := by
  have hN : 0 < V+M := by omega
  have hN0 : (0:ℝ) < (V:ℝ)+M := by exact_mod_cast hN
  have hCN : (0:ℝ) < (V+M).choose (m+1) := by exact_mod_cast Nat.choose_pos (show m+1 ≤ V+M by omega)
  have hCP : (0:ℝ) < (V+M-1).choose m := by exact_mod_cast Nat.choose_pos (show m ≤ V+M-1 by omega)
  have hcw := choose_pred_weight_succ (V+M) m hN
  have hcv := choose_pred_weight_succ V m (by omega)
  push_cast at hcw hcv
  unfold hypergeomHiddenFlux hypergeomMass
  simp only [Nat.zero_le, ite_true, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul]
  rw [show M+V=V+M by omega, show M+(V-1)=V+M-1 by omega]
  rw [div_mul_div_comm]
  apply (div_eq_div_iff hCN.ne' (mul_pos hN0 hCP).ne').mpr
  have hh := congrArg (fun z : ℝ => z*(V.choose (m+1):ℝ)) hcw
  have hh' := congrArg (fun z : ℝ => z*((V+M).choose (m+1):ℝ)) hcv
  nlinarith only [hh,hh']

theorem adjacentHypergeomTV_eq_flux (V M m : ℕ) (hM : M ≤ m) (hV : m < V) :
    adjacentHypergeomTV V M m =
      hypergeomHiddenFlux V M m (hypergeomHiddenMode (V-1) M m) := by
  unfold adjacentHypergeomTV
  rw [hypergeom_next_zero V M m hV]
  have he : (∑ k ∈ Finset.range (M+1),
      |hypergeomMass M V (m+1) (k+1)-hypergeomMass M V m k|) =
      ∑ k ∈ Finset.range (M+1), |hypergeomHiddenFlux V M m (k+1)-hypergeomHiddenFlux V M m k| := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hypergeom_adjacent_hidden_difference V M m k hM hV (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)]
  rw [he]
  unfold hypergeomHiddenFlux
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (V:ℝ)/(V+M))]
  rw [← Finset.mul_sum, ← mul_add, hypergeom_hidden_variation (V-1) M m hM (by omega)]
  ring

theorem adjacentHypergeomTV_le_mass (V M m : ℕ) (hM : M ≤ m) (hV : m < V) :
    adjacentHypergeomTV V M m ≤ hypergeomMass M V m (hypergeomHiddenMode (V-1) M m) := by
  rw [adjacentHypergeomTV_eq_flux V M m hM hV,
    hypergeomHiddenFlux_formula V M m _ hM hV (hypergeomHiddenMode_le (V-1) M m (by omega))]
  have hk := hypergeomHiddenMode_le (V-1) M m (by omega : m ≤ V-1)
  have hk' : (hypergeomHiddenMode (V-1) M m:ℝ) ≤ M := by exact_mod_cast hk
  have hm' : (m:ℝ) < V := by exact_mod_cast hV
  have hd : (0:ℝ) < (V:ℝ)+M-m := by linarith [Nat.cast_nonneg (α := ℝ) M]
  apply mul_le_of_le_one_left (hypergeomMass_nonneg _ _ _ _)
  apply (div_le_one hd).mpr
  linarith

end TraceReconstruction

end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Scales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scales

Exact block exponents, deletion reduction, induction depth, backward target scales, and uniform power absorption.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

theorem scaleA_top (b : ℕ) (ε : ℝ) : scaleA b b ε = 1 := by
  unfold scaleA
  field_simp
  ring

theorem scaleA_step (b j : ℕ) (ε : ℝ) : scaleA b (j+1) ε - 2*scaleA b j ε = ε := by
  unfold scaleA
  rw [pow_succ]
  ring

theorem nat_add_one_le_two_pow (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem sourceEpsilon_pos (B D : ℕ) : 0 < sourceEpsilon B D := by
  unfold sourceEpsilon
  positivity

theorem sourceEpsilon_loss (B D b : ℕ) (d : ℝ) (hb : b ≤ B)
    (hd0 : 0 ≤ d) (hd : d ≤ 3 + (B:ℝ)*D) :
    (((2:ℝ)^b-1)*d + 3*b*((2:ℝ)^b/2))*sourceEpsilon B D < 1/100 := by
  have hpow : (2:ℝ)^b ≤ (2:ℝ)^B := pow_le_pow_right₀ (by norm_num) hb
  have hB : (B:ℝ)+1 ≤ (2:ℝ)^B := by exact_mod_cast nat_add_one_le_two_pow B
  have hB0 : (0:ℝ) ≤ B := by positivity
  have hD0 : (0:ℝ) ≤ D := by positivity
  have hh : (((2:ℝ)^b-1)*d + 3*b*((2:ℝ)^b/2)) ≤
      4*((2:ℝ)^B)^2*((D:ℝ)+1) := by
    have hb' : (b:ℝ) ≤ B := by exact_mod_cast hb
    have h1 := mul_le_mul_of_nonneg_right (show (2:ℝ)^b-1 ≤ (2:ℝ)^B by linarith) hd0
    have h2 := mul_le_mul_of_nonneg_left hd (show 0 ≤ (2:ℝ)^B by positivity)
    have h3 := mul_le_mul hb' hpow (by positivity : (0:ℝ) ≤ (2:ℝ)^b) hB0
    have h4 := mul_le_mul_of_nonneg_left hB hD0
    have h5 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ (2:ℝ)^B by positivity)
    have h6 := mul_le_mul_of_nonneg_left hB (show 0 ≤ (2:ℝ)^B by positivity)
    nlinarith [sq_nonneg ((2:ℝ)^B)]
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right hh (sourceEpsilon_pos B D).le)
  unfold sourceEpsilon
  have hpos : 0 < (2:ℝ)^(4*B+100) := by positivity
  have hp2 : (2:ℝ)^(2*B) = ((2:ℝ)^B)^2 := by rw [mul_comm 2 B, pow_mul]
  have hp4 : (2:ℝ)^(4*B+100) = ((2:ℝ)^B)^2 * (2:ℝ)^(2*B+100) := by
    rw [show 4*B+100=2*B+(2*B+100) by omega, pow_add, hp2]
  have hh2 : (400:ℝ) < (2:ℝ)^(2*B+100) := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : 9 ≤ 2*B+100)
    norm_num at h ⊢
    linarith
  rw [mul_one_div]
  apply (div_lt_iff₀ (by positivity)).mpr
  rw [hp4]
  have := mul_lt_mul_of_pos_left hh2 (show 0 < ((2:ℝ)^B)^2*((D:ℝ)+1) by positivity)
  nlinarith

end TraceReconstruction

open Filter
open scoped Topology


open Filter
open scoped Topology
namespace TraceReconstruction

theorem blockGain_two : blockGain 2 = 1/5 := by norm_num [blockGain]
theorem blockGain_pos (B : ℕ) (hB : 2 ≤ B) : 0 < blockGain B := by
  have hB' : (2:ℝ) ≤ B := by exact_mod_cast hB
  unfold blockGain
  linarith

theorem totalScoreExponent_exact (B D : ℕ) (hD : warmupBlocks B ≤ D) :
    totalScoreExponent B D = 11/5 + (warmupBlocks B:ℝ)/5 +
      ((D:ℝ)-warmupBlocks B)*blockGain B := by
  unfold totalScoreExponent
  rw [← Nat.add_sub_of_le hD, Finset.sum_range_add]
  have hfirst : (∑ i ∈ Finset.range (warmupBlocks B),
      blockGain (if i<warmupBlocks B then 2 else B)) = (warmupBlocks B:ℝ)/5 := by
    simp only [Finset.sum_congr rfl (fun i hi => congrArg blockGain (ite_eq_left (Finset.mem_range.mp hi))), blockGain_two]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hfirst]
  have hlast : (∑ i ∈ Finset.range (D-warmupBlocks B),
      blockGain (if warmupBlocks B+i<warmupBlocks B then 2 else B)) =
      ((D:ℝ)-warmupBlocks B)*blockGain B := by
    simp only [show ∀ i, ¬warmupBlocks B+i<warmupBlocks B from fun i => by omega, ite_false,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub hD]
  rw [hlast]
  simp only [Nat.add_sub_of_le hD]
  ring

end TraceReconstruction

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open Filter

theorem sourceTargetScale_step (B D i : ℕ) (n : ℝ) (hn : 0 ≤ n) (hi : i < D) :
    sourceTargetScale B D n i =
      (sourceTargetScale B D n (i+1))^(scaleA (sourceDimension B i) 0 (sourceEpsilon B D)) := by
  unfold sourceTargetScale sourceScaleProduct
  rw [←Real.rpow_mul hn,Finset.prod_eq_prod_Ico_succ_bot hi]
  rw [mul_comm]

theorem sourceEpsilon_small (B D : ℕ) :
    ((D:ℝ)+1)*(2:ℝ)^B*sourceEpsilon B D ≤ 1/2 := by
  have hp : 2*(2:ℝ)^B ≤ (2:ℝ)^(4*B+100) := by
    rw [←pow_succ']
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  unfold sourceEpsilon
  have hD : 0 < (D:ℝ)+1 := by positivity
  have hpow : 0 < (2:ℝ)^(4*B+100) := by positivity
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  have he : ((D:ℝ)+1)*2^B*(1/(2^(4*B+100)*((D:ℝ)+1)))*2 =
      (2*2^B)/2^(4*B+100) := by field_simp
  rw [he]
  exact (div_le_one hpow).mpr hp

theorem scaleA_zero_lower (b B : ℕ) (ε : ℝ) (hb : b ≤ B) (he : 0 ≤ ε) :
    (1/((2:ℝ)^B))*(1-((2:ℝ)^B-1)*ε) ≤ scaleA b 0 ε := by
  have hp : (2:ℝ)^b ≤ 2^B := pow_le_pow_right₀ (by norm_num) hb
  have hpos : 0 < (2:ℝ)^b := by positivity
  have hposB : 0 < (2:ℝ)^B := by positivity
  have hd := div_le_div_of_nonneg_left (show 0 ≤ 1+ε by linarith) hpos hp
  have heq : (1/((2:ℝ)^B))*(1-((2:ℝ)^B-1)*ε) = (1+ε)/2^B-ε := by
    field_simp; ring
  rw [heq]
  unfold scaleA
  norm_num only [pow_zero,mul_one]
  linarith only [hd]

theorem sourceScaleProduct_lower (B D i : ℕ) (hB : 2 ≤ B) :
    1/(2*((2:ℝ)^(B*D))) ≤ sourceScaleProduct B D i := by
  let ε := sourceEpsilon B D
  let u := ((2:ℝ)^B-1)*ε
  let a := (1/(2:ℝ)^B)*(1-u)
  have hε : 0 < ε := sourceEpsilon_pos _ _
  have hp : (1:ℝ) ≤ 2^B := one_le_pow₀ (by norm_num)
  have hu : 0 ≤ u := mul_nonneg (sub_nonneg.mpr hp) hε.le
  have hsmall := sourceEpsilon_small B D
  have hu' : ((D:ℝ)+1)*u ≤ 1/2 := by
    dsimp [u]
    dsimp [ε] at *
    nlinarith only [mul_nonneg (show 0 ≤ (D:ℝ)+1 by positivity) hε.le,hsmall]
  have hu1 : u ≤ 1/2 := by nlinarith only [hu',mul_nonneg (Nat.cast_nonneg D) hu]
  have ha : 0 ≤ a := mul_nonneg (by positivity) (by linarith only [hu1])
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have h1 : 1/(2:ℝ)^B ≤ 1 := (div_le_one (by positivity)).mpr hp
    exact (mul_le_mul_of_nonneg_left (by linarith only [hu] : 1-u ≤ 1) (by positivity)).trans (by simpa using h1)
  have hb : 1/2 ≤ (1-u)^D := by
    have H := one_add_mul_le_pow (a := -u) (by linarith only [hu1]) D
    have hd : (D:ℝ)*u ≤ 1/2 := by nlinarith only [hu',hu]
    simpa only [sub_eq_add_neg] using (show (1:ℝ)/2 ≤ (1+-u)^D by nlinarith only [H,hd])
  have hc : (Finset.Ico i D).card ≤ D := by simp only [Nat.card_Ico]; omega
  calc
    _ = (1/(2:ℝ)^B)^D*(1/2) := by rw [div_pow,one_pow,←pow_mul]; field_simp
    _ ≤ (1/(2:ℝ)^B)^D*(1-u)^D := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = a^D := (mul_pow _ _ _).symm
    _ ≤ a^(Finset.Ico i D).card := pow_le_pow_of_le_one ha ha1 hc
    _ = ∏j∈Finset.Ico i D,a := by simp
    _ ≤ sourceScaleProduct B D i := by
      apply Finset.prod_le_prod (fun _ _ => ha)
      intro j _
      apply scaleA_zero_lower _ _ _ _ hε.le
      unfold sourceDimension
      split_ifs <;> omega

end TraceReconstruction


end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Patterns

Pattern serialization, motif norms, flag posteriors, signed rank coefficients, translated binomials, and support geometry.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


namespace TraceReconstruction

theorem pureAtomRun_add (w : List Bool) (n m : ℕ) :
    pureAtomRun w (n+m)=pureAtomRun w n ++ pureAtomRun w m := by
  simp only [pureAtomRun,List.replicate_add,List.flatten_append]

/-- Splitting or regrouping a pure region into reported chunks changes no
 unmarked string. In particular arbitrary fixed chunk IDs are harmless. -/
theorem pureAtomRun_partition (w : List Bool) (ns : List ℕ) :
    (ns.map (pureAtomRun w)).flatten=pureAtomRun w ns.sum := by
  induction ns with
  | nil => simp [pureAtomRun]
  | cons n ns ih => simp [ih,pureAtomRun_add]

end TraceReconstruction


end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialMoments

Initial coefficient tails, primitive conditioning, mark-list oracle densities, pure norm estimates, and moment energies.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
noncomputable section
noncomputable section


noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem maskWeight_card {n : ℕ} (q : ℝ) (a : Mask n) :
    maskWeight q a = (1-q)^(maskSubset a).card*q^(n-(maskSubset a).card) := by
  unfold maskWeight maskSubset
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  congr 1
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := fun i => a i)
  rw [Finset.card_univ,Fintype.card_fin] at h
  rw [show (Finset.univ.filter fun i : Fin n => ¬a i=true).card=
      n-(Finset.univ.filter fun i : Fin n => a i=true).card by omega]

end TraceReconstruction



end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Oracles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Oracles

TV kernels and trace simulation, anchor costs, counted primitives, common-part lifting, concrete oracle pairs, and paired-flag metadata.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem tv_self (P : FiniteLaw α) : P.tv P=0 := by simp [tv]

theorem expect_bind (P : FiniteLaw α) (K : α → FiniteLaw β) (f : β → ℝ) :
    (P.bind K).expect f=P.expect (fun a => (K a).expect f) := by
  unfold expect bind
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem bind_assoc (P : FiniteLaw α) (K : α → FiniteLaw β) (L : β → FiniteLaw γ) :
    (P.bind K).bind L=P.bind (fun a => (K a).bind L) := by
  apply law_ext
  intro c
  simp only [bind,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tv_bind_kernel_le (P : FiniteLaw α) (K L : α → FiniteLaw β) :
    (P.bind K).tv (P.bind L) ≤ P.expect (fun a => (K a).tv (L a)) := by
  unfold tv bind expect
  simp only
  calc
    _ = (1/2:ℝ)*∑b, |∑a,P.mass a*((K a).mass b-(L a).mass b)| := by
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ (1/2:ℝ)*∑b,∑a,P.mass a*|(K a).mass b-(L a).mass b| := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro b _
      simpa only [abs_mul,abs_of_nonneg (P.nonneg _)] using
        Finset.abs_sum_le_sum_abs (fun a => P.mass a*((K a).mass b-(L a).mass b)) Finset.univ
    _ = _ := by
      rw [Finset.sum_comm,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum]
      ring

end TraceReconstruction.FiniteLaw


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem SimulatesTrace.append {α β : Type*} [Fintype α] [Fintype β]
    {q : ℝ} {P : FiniteLaw α} {Q : FiniteLaw β} {f : α → List Bool} {g : β → List Bool}
    {x y : List Bool} (hP : SimulatesTrace q P f x) (hQ : SimulatesTrace q Q g y) :
    SimulatesTrace q (P.prod Q) (fun a => f a.1++g a.2) (x++y) := by
  intro F
  rw [FiniteLaw.expect_prod,listDeletionExpectation_append]
  change P.expect (fun a => Q.expect (fun b => F (f a++g b)))=_
  unfold SimulatesTrace at hP hQ
  calc
    _ = P.expect (fun a => listDeletionExpectation q y (fun t => F (f a++t))) :=
      congrArg P.expect (funext fun a => hQ (fun t => F (f a++t)))
    _ = _ := hP (fun t => listDeletionExpectation q y (fun u => F (t++u)))

/-- Any randomized partition into exactly the same literal word gives exactly
its usual trace after boundaries are forgotten. No fit conditioning occurs. -/
theorem SimulatesTrace.random_partition {α Ω : Type*} [Fintype α] [Fintype Ω]
    {q : ℝ} (P : FiniteLaw Ω) (K : Ω → FiniteLaw α) (decode : α → List Bool)
    (w : List Bool) (h : ∀ω,SimulatesTrace q (K ω) decode w) :
    SimulatesTrace q (P.bind K) decode w := by
  intro F
  rw [FiniteLaw.expect_bind]
  unfold SimulatesTrace at h
  simp_rw [h]
  exact FiniteLaw.expect_const _ _

end TraceReconstruction


noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem hypergeomMass_middle_sq (V M m v : ℕ) {p : ℝ}
    (hp : p∈Set.Icc (1/4:ℝ) (3/4:ℝ)) (hMV : M≤V)
    (hN : 16≤V+M) (hm : m≤V+M) (hmean : (m:ℝ)=(V+M:ℕ)*p) :
    hypergeomMass V M m v^2≤4096/((M:ℝ)+1) := by
  have hp' : p∈Set.Ioo (0:ℝ) 1 := by constructor <;> linarith [hp.1,hp.2]
  have hpp : (1/8:ℝ)≤p*(1-p) := by nlinarith [sq_nonneg (p-1/2),mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)]
  have hNr : (16:ℝ)≤(V:ℝ)+M := by exact_mod_cast hN
  have hVr : (M:ℝ)≤V := by exact_mod_cast hMV
  have hv : 1≤(V+M:ℕ)*p*(1-p) := by
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) V,Nat.cast_nonneg (α:=ℝ) M]
  have H := hypergeomMass_sq_upper V M m v hp' hm hmean hv
  apply H.trans
  have hd : 0<((V:ℝ)+1)*((M:ℝ)+1)*p*(1-p) := by positivity [hp'.1,sub_pos.mpr hp'.2]
  apply (div_le_iff₀ hd).2
  have hM : 0<(M:ℝ)+1 := by positivity
  have he : 4096/((M:ℝ)+1)*(((V:ℝ)+1)*((M:ℝ)+1)*p*(1-p))=
      4096*((V:ℝ)+1)*(p*(1-p)) := by field_simp
  rw [he]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hpp (show 0≤(V:ℝ)+1 by positivity)]

theorem hypergeomMass_middle_le (V M m v : ℕ) {p : ℝ}
    (hp : p∈Set.Icc (1/4:ℝ) (3/4:ℝ)) (hMV : M≤V)
    (hN : 16≤V+M) (hm : m≤V+M) (hmean : (m:ℝ)=(V+M:ℕ)*p) :
    hypergeomMass V M m v≤64/Real.sqrt ((M:ℝ)+1) := by
  have H := hypergeomMass_middle_sq V M m v hp hMV hN hm hmean
  have hs : 0<Real.sqrt ((M:ℝ)+1) := Real.sqrt_pos.2 (by positivity)
  have he : (64/Real.sqrt ((M:ℝ)+1))^2=4096/((M:ℝ)+1) := by
    rw [div_pow,Real.sq_sqrt (by positivity)]; norm_num
  rw [←he] at H
  exact (sq_le_sq₀ (hypergeomMass_nonneg _ _ _ _) (by positivity)).1 H

theorem hypergeomMass_complement (V M m v : ℕ) (hv : v≤ m) :
    hypergeomMass V M m v=hypergeomMass M V m (m-v) := by
  simp only [hypergeomMass,ite_eq_left hv,ite_eq_left (Nat.sub_le _ _),Nat.sub_sub_self hv]
  rw [Nat.add_comm M V,mul_comm]

theorem hypergeomLaw_adjacent_tv (V M m : ℕ) (hM : M≤ m) (hV : m<V) :
    (hypergeomLaw V M (m+1) (by omega)).tv (hypergeomLaw V M m (by omega))=
      adjacentHypergeomTV V M m := by
  unfold FiniteLaw.tv
  simp only [hypergeomLaw]
  rw [Fin.sum_univ_eq_sum_range (fun v => |hypergeomMass V M (m+1) v-
    hypergeomMass V M m v|)]
  rw [sum_range_extend_zero (show m+2≤V+M+1 by omega) (fun k hk => by
    rw [hypergeomMass_above_total V M (m+1) k (by omega),
      hypergeomMass_above_total V M m k (by omega),sub_self,abs_zero])]
  rw [←Finset.sum_range_reflect (fun v => |hypergeomMass V M (m+1) v-
    hypergeomMass V M m v|) (m+2)]
  rw [show m+2=(m+1)+1 by omega,Finset.sum_range_succ']
  have hzero : |hypergeomMass V M (m+1) (m+1)-hypergeomMass V M m (m+1)|=
      hypergeomMass M V (m+1) 0 := by
    rw [hypergeomMass_above_total V M m (m+1) (by omega),sub_zero,
      hypergeomMass_complement V M (m+1) (m+1) le_rfl,Nat.sub_self,
      abs_of_nonneg (hypergeomMass_nonneg _ _ _ _)]
  have he (k : ℕ) (hk : k∈Finset.range (m+1)) :
      |hypergeomMass V M (m+1) ((m+1+1)-1-(k+1))-
       hypergeomMass V M m ((m+1+1)-1-(k+1))|=
      |hypergeomMass M V (m+1) (k+1)-hypergeomMass M V m k| := by
    have hk' : k≤ m := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk
    rw [show (m+1+1)-1-(k+1)=m-k by omega,
      hypergeomMass_complement V M (m+1) (m-k) (by omega),
      hypergeomMass_complement V M m (m-k) (by omega)]
    rw [show m+1-(m-k)=k+1 by omega,show m-(m-k)=k by omega]
  rw [Finset.sum_congr rfl he]
  simp only [Nat.add_sub_cancel,Nat.sub_zero,hzero]
  rw [sum_range_extend_zero (Nat.add_le_add_right hM 1) (fun k hk => by
    rw [hypergeomMass_high M V (m+1) (k+1) (by omega),
      hypergeomMass_high M V m k (by omega),sub_self,abs_zero])]
  unfold adjacentHypergeomTV
  ring

theorem adjacentHypergeomTV_middle_le (V M m : ℕ) {p : ℝ}
    (hp : p∈Set.Icc (1/4:ℝ) (3/4:ℝ)) (hMV : M≤V)
    (hN : 16≤V+M) (hM : M≤ m) (hV : m<V) (hmean : (m:ℝ)=(V+M:ℕ)*p) :
    adjacentHypergeomTV V M m≤64/Real.sqrt ((M:ℝ)+1) := by
  apply (adjacentHypergeomTV_le_mass V M m hM hV).trans
  rw [hypergeomMass_complement M V m _ (by
    exact (hypergeomHiddenMode_le (V-1) M m (by omega)).trans hM)]
  exact hypergeomMass_middle_le V M m _ hp hMV hN (by omega) hmean

theorem hypergeomLaw_adjacent_middle (V M m : ℕ) (hN : 16≤V+M)
    (hM : M≤ m) (hV : m<V) (hlow : V+M≤4*m) (hhigh : 4*m≤3*(V+M)) :
    (hypergeomLaw V M m (by omega)).tv (hypergeomLaw V M (m+1) (by omega))≤
      64/Real.sqrt ((M:ℝ)+1) := by
  have hn : 0<(V+M:ℕ) := by omega
  have hnr : (0:ℝ)<(V+M:ℕ) := by exact_mod_cast hn
  have hL : ((V+M:ℕ):ℝ)≤4*(m:ℝ) := by exact_mod_cast hlow
  have hU : 4*(m:ℝ)≤3*((V+M:ℕ):ℝ) := by exact_mod_cast hhigh
  rw [FiniteLaw.tv_symm,hypergeomLaw_adjacent_tv V M m hM hV]
  have hp : (m:ℝ)/(V+M:ℕ)∈Set.Icc (1/4:ℝ) (3/4:ℝ) := by
    constructor
    · apply (le_div_iff₀ hnr).2; linarith
    · apply (div_le_iff₀ hnr).2; linarith
  exact adjacentHypergeomTV_middle_le V M m hp (by omega) hN hM hV
    (by field_simp)

theorem FiniteLaw.tv_chain {α : Type*} [Fintype α] (P : ℕ→FiniteLaw α) (n : ℕ) :
    (P 0).tv (P n)≤∑i∈Finset.range n,(P i).tv (P (i+1)) := by
  induction n with
  | zero => simp [FiniteLaw.tv_self]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith [FiniteLaw.tv_triangle (P 0) (P n) (P (n+1))]

theorem hypergeomLaw_steps (V M m P : ℕ) (hN : 16≤V+M)
    (hM : M≤ m) (hV : m+P<V) (hlow : V+M≤4*m) (hhigh : 4*(m+P)≤3*(V+M)) :
    (hypergeomLaw V M m (by omega)).tv (hypergeomLaw V M (m+P) (by omega))≤
      (P:ℝ)*64/Real.sqrt ((M:ℝ)+1) := by
  let Q : ℕ→FiniteLaw (Fin (V+M+1)) := fun j =>
    hypergeomLaw V M (m+min j P) (by omega)
  have H := FiniteLaw.tv_chain Q P
  have hQ0 : Q 0=hypergeomLaw V M m (by omega) := by simp [Q]
  have hQP : Q P=hypergeomLaw V M (m+P) (by omega) := by simp [Q]
  rw [hQ0,hQP] at H
  apply H.trans
  calc
    _≤∑j∈Finset.range P,64/Real.sqrt ((M:ℝ)+1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j<P := Finset.mem_range.mp hj
      simp only [Q,min_eq_left (by omega : j≤P),min_eq_left (by omega : j+1≤P)]
      exact hypergeomLaw_adjacent_middle V M (m+j) hN (by omega) (by omega)
        (by omega) (by omega)
    _=_ := by simp [mul_div_assoc]

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

variable {α β : Type*} [Fintype α] [Fintype β]

theorem visibleScheduleLaw_mass (m : ℕ) (hm : m≤Fintype.card α+Fintype.card β) (S : Finset α) :
    (visibleScheduleLaw (α:=α) (β:=β) m hm).mass S=
      if S.card≤ m then ((Fintype.card β).choose (m-S.card):ℝ)/
        ((Fintype.card α+Fintype.card β).choose m:ℝ) else 0 := by
  unfold visibleScheduleLaw
  rw [FiniteLaw.map_mass]
  by_cases hS : S.card≤ m
  · rw [ite_eq_left hS]
    simp only [uniformSubsetLaw,Fintype.card_sum]
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    have he : (Finset.univ.filter (fun T : FixedSubset (α⊕β) m => T.val.toLeft=S)).card=
        (Fintype.card β).choose (m-S.card) := by
      rw [←Fintype.card_subtype]
      exact (Fintype.card_congr (visibleFiberEquiv (β:=β) m S hS)).trans (card_fixedSubset _)
    rw [he]
    ring
  · rw [ite_eq_right hS]
    apply Finset.sum_eq_zero
    intro T _
    have hnot : T.val.toLeft≠S := by
      intro he
      apply hS
      simpa only [he,T.property] using (Finset.card_toLeft_le (u:=T.val))
    rw [ite_eq_right hnot]

theorem sum_finset_card (f : ℕ→ℝ) :
    (∑S : Finset α,f S.card)=∑v : Fin (Fintype.card α+1),
      ((Fintype.card α).choose v.val:ℝ)*f v.val := by
  let g : Finset α→Fin (Fintype.card α+1) := fun S =>
    ⟨S.card,by have H:=Finset.card_le_univ S; omega⟩
  rw [←Fintype.sum_fiberwise g (fun S => f S.card)]
  apply Finset.sum_congr rfl
  intro v _
  have hc : Fintype.card {S : Finset α // g S=v}=(Fintype.card α).choose v.val := by
    let e : {S : Finset α // g S=v} ≃ FixedSubset α v.val :=
      { toFun := fun S => ⟨S.val,by have H:=congrArg Fin.val S.property; exact H⟩
        invFun := fun S => ⟨S.val,by apply Fin.ext; exact S.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Fintype.card_congr e).trans (card_fixedSubset _)
  calc
    _=∑_S : {S : Finset α // g S=v},f v.val := by
      apply Finset.sum_congr rfl
      intro S _
      congr 1
      exact congrArg Fin.val S.property
    _=_ := by simp [hc]

end TraceReconstruction

namespace TraceReconstruction
open scoped Classical
variable {α β : Type*} [Fintype α] [Fintype β]

theorem visibleScheduleLaw_tv (m m' : ℕ)
    (hm : m≤Fintype.card α+Fintype.card β) (hm' : m'≤Fintype.card α+Fintype.card β) :
    (visibleScheduleLaw (α:=α) (β:=β) m hm).tv (visibleScheduleLaw m' hm')=
      (hypergeomLaw (Fintype.card α) (Fintype.card β) m hm).tv
        (hypergeomLaw (Fintype.card α) (Fintype.card β) m' hm') := by
  unfold FiniteLaw.tv
  simp_rw [visibleScheduleLaw_mass]
  rw [sum_finset_card (α:=α) (fun v =>
    |(if v≤ m then ((Fintype.card β).choose (m-v):ℝ)/
      ((Fintype.card α+Fintype.card β).choose m:ℝ) else 0)-
     (if v≤ m' then ((Fintype.card β).choose (m'-v):ℝ)/
      ((Fintype.card α+Fintype.card β).choose m':ℝ) else 0)|)]
  have he (v : ℕ) :
      ((Fintype.card α).choose v:ℝ)*
        |(if v≤ m then ((Fintype.card β).choose (m-v):ℝ)/
          ((Fintype.card α+Fintype.card β).choose m:ℝ) else 0)-
         (if v≤ m' then ((Fintype.card β).choose (m'-v):ℝ)/
          ((Fintype.card α+Fintype.card β).choose m':ℝ) else 0)|=
      |hypergeomMass (Fintype.card α) (Fintype.card β) m v-
       hypergeomMass (Fintype.card α) (Fintype.card β) m' v| := by
    rw [←abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) ((Fintype.card α).choose v)),←abs_mul,mul_sub]
    simp only [mul_ite,mul_zero,hypergeomMass,mul_div_assoc]
  simp_rw [he]
  simp only [hypergeomLaw]
  rw [Fin.sum_univ_eq_sum_range (fun v => |hypergeomMass (Fintype.card α) (Fintype.card β) m v-
       hypergeomMass (Fintype.card α) (Fintype.card β) m' v|)]
  rw [Fin.sum_univ_eq_sum_range (n:=Fintype.card α+Fintype.card β+1)
    (fun v => |hypergeomMass (Fintype.card α) (Fintype.card β) m v-
       hypergeomMass (Fintype.card α) (Fintype.card β) m' v|)]
  congr 1
  symm
  apply sum_range_extend_zero (by omega)
  intro k hk
  rw [hypergeomMass_high _ _ _ _ (by omega),hypergeomMass_high _ _ _ _ (by omega),sub_self,abs_zero]

theorem visibleScheduleLaw_steps (m P : ℕ)
    (hN : 16≤Fintype.card α+Fintype.card β) (hM : Fintype.card β≤ m)
    (hV : m+P<Fintype.card α) (hlow : Fintype.card α+Fintype.card β≤4*m)
    (hhigh : 4*(m+P)≤3*(Fintype.card α+Fintype.card β)) :
    (visibleScheduleLaw (α:=α) (β:=β) m (by omega)).tv
      (visibleScheduleLaw (β:=β) (m+P) (by omega))≤
      (P:ℝ)*64/Real.sqrt ((Fintype.card β:ℝ)+1) := by
  rw [visibleScheduleLaw_tv]
  exact hypergeomLaw_steps _ _ m P hN hM hV hlow hhigh

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem ext_expect {P Q : FiniteLaw α} (h : ∀f : α→ℝ,P.expect f=Q.expect f) : P=Q := by
  apply ext
  funext a
  have H:=h (fun b => if b=a then 1 else 0)
  simpa only [expect,mul_ite,mul_one,mul_zero,Fintype.sum_ite_eq'] using H

theorem map_map (P : FiniteLaw α) (f : α→β) (g : β→γ) :
    (P.map f).map g=P.map (g∘f) := by
  apply ext_expect
  intro G
  rw [expect_map,expect_map,expect_map]
  rfl

theorem map_equiv_mass (P : FiniteLaw α) (e : α≃β) (b : β) :
    (P.map e).mass b=P.mass (e.symm b) := by
  rw [map_mass]
  simp only [←e.eq_symm_apply,Fintype.sum_ite_eq']

end FiniteLaw

variable {α β : Type*} [Fintype α] [Fintype β]

theorem uniformSubsetLaw_map (e : α≃β) (m : ℕ) (hm : m≤Fintype.card α) :
    (uniformSubsetLaw m hm).map (fixedSubsetEquiv e m)=
      uniformSubsetLaw m (by simpa only [←Fintype.card_congr e] using hm) := by
  apply FiniteLaw.ext
  funext T
  rw [FiniteLaw.map_equiv_mass]
  simp only [uniformSubsetLaw,Fintype.card_congr e]

end TraceReconstruction

namespace TraceReconstruction
open scoped Classical
variable {α : Type*} [Fintype α]

omit [Fintype α] in
theorem card_hiddenIndex (H : Finset α) : Fintype.card (HiddenIndex H)=H.card := by
  exact Fintype.card_coe H

omit [Fintype α] in
theorem erase_splitIndex (H : Finset α) (S : Finset (VisibleIndex H⊕HiddenIndex H)) :
    (S.map (splitIndexEquiv H).toEmbedding)\H=
      S.toLeft.map ⟨Subtype.val,Subtype.val_injective⟩ := by
  ext a
  constructor
  · intro ha
    obtain ⟨ha,hn⟩:=Finset.mem_sdiff.mp ha
    obtain ⟨b,hb,rfl⟩:=Finset.mem_map.mp ha
    cases b with
    | inl b =>
      apply Finset.mem_map.mpr
      exact ⟨b,by simpa using hb,rfl⟩
    | inr b => exact False.elim (hn b.property)
  · intro ha
    obtain ⟨b,hb,rfl⟩:=Finset.mem_map.mp ha
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_map.mpr ⟨Sum.inl b,by simpa using hb,rfl⟩
    · exact b.property

end TraceReconstruction

namespace TraceReconstruction
open scoped Classical
variable {α : Type*} [Fintype α]

theorem eraseScheduleLaw_eq (H : Finset α) (m : ℕ) (hm : m≤Fintype.card α) :
    eraseScheduleLaw H m hm=
      (visibleScheduleLaw (α:=VisibleIndex H) (β:=HiddenIndex H) m
        (by simpa only [card_splitIndex] using hm)).map
        (fun S => S.map ⟨Subtype.val,Subtype.val_injective⟩) := by
  have h:=uniformSubsetLaw_map (splitIndexEquiv H) m
    (by simpa only [Fintype.card_sum,card_splitIndex] using hm)
  unfold eraseScheduleLaw visibleScheduleLaw
  rw [←h,FiniteLaw.map_map,FiniteLaw.map_map]
  congr 1
  funext S
  exact erase_splitIndex H S.val

theorem eraseScheduleLaw_steps (H : Finset α) (m P : ℕ)
    (hN : 16≤Fintype.card α) (hM : H.card≤ m)
    (hV : m+P+H.card<Fintype.card α) (hlow : Fintype.card α≤4*m)
    (hhigh : 4*(m+P)≤3*Fintype.card α) :
    (eraseScheduleLaw H m (by omega)).tv (eraseScheduleLaw H (m+P) (by omega))≤
    (P:ℝ)*64/Real.sqrt ((H.card:ℝ)+1) := by
  rw [eraseScheduleLaw_eq,eraseScheduleLaw_eq]
  refine (FiniteLaw.tv_map_le _ _ _).trans ?_
  have hc:=card_splitIndex H
  have hd:=card_hiddenIndex H
  have h:=visibleScheduleLaw_steps (α:=VisibleIndex H) (β:=HiddenIndex H) m P
    (by omega) (by omega) (by omega) (by omega) (by omega)
  simpa only [hd] using h

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical
variable {α : Type*} [Fintype α]

theorem subsetLaw_expect_card (p : ℝ) (hp : p∈Set.Icc 0 1) (f : ℕ→ℝ) :
    (subsetLaw (α:=α) p hp).expect (fun S => f S.card)=
      ∑k∈Finset.range (Fintype.card α+1),binomialMass (Fintype.card α) p k*f k := by
  change (∑S : Finset α,p^S.card*(1-p)^(Fintype.card α-S.card)*f S.card)=_
  rw [sum_finset_card (α:=α) (fun k => p^k*(1-p)^(Fintype.card α-k)*f k),
    Fin.sum_univ_eq_sum_range (fun k => ((Fintype.card α).choose k:ℝ)*(p^k*(1-p)^(Fintype.card α-k)*f k))]
  apply Finset.sum_congr rfl
  intro k _
  unfold binomialMass
  ring

theorem subsetLaw_variance (p : ℝ) (hp : p∈Set.Icc 0 1) :
    (subsetLaw (α:=α) p hp).expect (fun S => ((S.card:ℝ)-Fintype.card α*p)^2)=
      (Fintype.card α:ℝ)*p*(1-p) := by
  rw [subsetLaw_expect_card p hp (fun k => ((k:ℝ)-Fintype.card α*p)^2)]
  exact binomialMass_variance _ p

theorem hiddenScheduleLaw_tv (p : ℝ) (hp : p∈Set.Icc 0 1) (m m' : ℕ)
    (hm : m≤Fintype.card α) (hm' : m'≤Fintype.card α) :
    (hiddenScheduleLaw p hp m hm).tv (hiddenScheduleLaw p hp m' hm') ≤
      (subsetLaw (α:=α) p hp).expect (fun H =>
        (eraseScheduleLaw H m hm).tv (eraseScheduleLaw H m' hm')) := by
  unfold hiddenScheduleLaw
  refine (FiniteLaw.tv_bind_kernel_le _ _ _).trans ?_
  apply FiniteLaw.expect_mono
  intro H
  exact FiniteLaw.tv_map_le _ _ _

theorem good_hiddenSchedule_bound {G P : ℕ} {p : ℝ}
    (hG : 8≤G) (hP : 4*P≤G) (hp : p∈Set.Ioc 0 (1/8))
    (H : Finset (Fin (2*G)))
    (hlo : p*(2*G:ℝ)/2≤H.card) (hhi : (H.card:ℝ)≤2*p*(2*G:ℝ)) :
    (eraseScheduleLaw H G (by simp only [Fintype.card_fin]; omega)).tv
      (eraseScheduleLaw H (G+P) (by simp only [Fintype.card_fin]; omega))≤
      (P:ℝ)*64/Real.sqrt (p*(2*G:ℝ)/2) := by
  have hgr : (0:ℝ)<G := by exact_mod_cast (show 0<G by omega)
  have hhr : (H.card:ℝ)≤(G:ℝ)/2 := by nlinarith [mul_le_mul_of_nonneg_right hp.2 hgr.le]
  have hh : 2*H.card≤G := by exact_mod_cast (show 2*(H.card:ℝ)≤G by linarith)
  have h:=eraseScheduleLaw_steps H G P (by simp only [Fintype.card_fin]; omega)
    (by omega) (by simp only [Fintype.card_fin]; omega)
    (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega)
  apply h.trans
  apply div_le_div_of_nonneg_left (by positivity)
    (Real.sqrt_pos.2 (by positivity [hp.1]))
    (Real.sqrt_le_sqrt (by linarith))

theorem bad_hiddenSchedule_variance {μ x : ℝ} (hμ : 0<μ)
    (hbad : ¬(μ/2≤x ∧ x≤2*μ)) :
    1≤4*(x-μ)^2/μ^2 := by
  rw [le_div_iff₀ (sq_pos_of_pos hμ)]
  push Not at hbad
  by_cases h : μ/2≤x
  · have hx:=hbad h
    nlinarith [sq_nonneg (x-2*μ)]
  · have hx : x<μ/2 := lt_of_not_ge h
    nlinarith [sq_nonneg (x-μ/2)]

theorem hiddenScheduleLaw_steps {G P : ℕ} {p : ℝ}
    (hG : 8≤G) (hP : 4*P≤G) (hp : p∈Set.Ioc 0 (1/8)) :
    (hiddenScheduleLaw (α:=Fin (2*G)) p ⟨hp.1.le,by linarith [hp.2]⟩ G
      (by simp only [Fintype.card_fin]; omega)).tv
      (hiddenScheduleLaw p ⟨hp.1.le,by linarith [hp.2]⟩ (G+P)
        (by simp only [Fintype.card_fin]; omega))≤
      (P:ℝ)*64/Real.sqrt (p*(2*G:ℝ)/2)+4/(p*(2*G:ℝ)) := by
  let μ : ℝ := p*(2*G:ℝ)
  have hgr : (0:ℝ)<G := by exact_mod_cast (show 0<G by omega)
  have hμ : 0<μ := by dsimp [μ]; positivity [hp.1]
  have hμ0 : μ≠0 := ne_of_gt hμ
  let E : ℝ := (P:ℝ)*64/Real.sqrt (μ/2)
  have hE : 0≤E := by dsimp [E]; positivity
  apply (hiddenScheduleLaw_tv p ⟨hp.1.le,by linarith [hp.2]⟩ G (G+P) _ _).trans
  have he := (subsetLaw (α:=Fin (2*G)) p ⟨hp.1.le,by linarith [hp.2]⟩).expect_mono
    (g:=fun H => E+4*((H.card:ℝ)-μ)^2/μ^2) (fun H => by
      by_cases hg : μ/2≤(H.card:ℝ) ∧ (H.card:ℝ)≤2*μ
      · exact (good_hiddenSchedule_bound hG hP hp H hg.1 (by simpa only [μ,mul_assoc] using hg.2)).trans
          (le_add_of_nonneg_right (by positivity))
      · exact (FiniteLaw.tv_le_one _ _).trans
          ((bad_hiddenSchedule_variance hμ hg).trans (by linarith)))
  apply he.trans
  have hv:=subsetLaw_variance (α:=Fin (2*G)) p ⟨hp.1.le,by linarith [hp.2]⟩
  simp only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at hv
  change (∑H,(subsetLaw p _).mass H*(E+4*((H.card:ℝ)-μ)^2/μ^2))≤E+4/μ
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul,FiniteLaw.total,one_mul]
  have heq : (∑H : Finset (Fin (2*G)),(subsetLaw p ⟨hp.1.le,by linarith [hp.2]⟩).mass H*(4*((H.card:ℝ)-μ)^2/μ^2))=
      4/μ^2*(2*(G:ℝ)*p*(1-p)) := by
    rw [←hv,FiniteLaw.expect,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro H _
    dsimp [μ]
    ring
  rw [heq]
  have heq' : 4/μ^2*(2*(G:ℝ)*p*(1-p))=4/μ*(1-p) := by
    have h : 2*(G:ℝ)*p=μ := by dsimp [μ]; ring
    rw [h]
    field_simp
  rw [heq']
  have h:=mul_le_mul_of_nonneg_left (show 1-p≤1 by linarith [hp.1]) (show 0≤4/μ by positivity)
  linarith

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem expect_comm (P : FiniteLaw α) (Q : FiniteLaw β) (F : α→β→ℝ) :
    P.expect (fun a => Q.expect (F a))=Q.expect (fun b => P.expect (fun a => F a b)) := by
  simp only [expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem bind_map (P : FiniteLaw α) (f : α→β) (K : β→FiniteLaw γ) :
    (P.map f).bind K=P.bind (K∘f) := by
  apply ext_expect
  intro F
  rw [expect_bind,expect_map,expect_bind]
  rfl

theorem bind_comm (P : FiniteLaw α) (Q : FiniteLaw β) (K : α→β→FiniteLaw γ) :
    P.bind (fun a => Q.bind (K a))=Q.bind (fun b => P.bind (fun a => K a b)) := by
  apply ext_expect
  intro F
  simp only [expect_bind]
  exact expect_comm P Q (fun a b => (K a b).expect F)

end FiniteLaw
variable {α : Type*} [Fintype α]

theorem subsetWeight_mask {n : ℕ} (p : ℝ) (a : Mask n) :
    subsetWeight p (maskSubset a)=maskWeight (1-p) a := by
  rw [maskWeight_card]
  simp only [subsetWeight,Fintype.card_fin,sub_sub_cancel]

theorem coordinateProduct_common_flags {n : ℕ} (p : ℝ) (hp : p∈Set.Icc 0 1)
    (U : FiniteLaw α) (R P : Fin n→FiniteLaw α)
    (hP : ∀ i x,(P i).mass x=p*U.mass x+(1-p)*(R i).mass x) :
    (subsetLaw p hp).bind (fun H : Finset (Fin n) =>
      FiniteLaw.coordinateProduct (fun i => if i∈H then U else R i))=
      FiniteLaw.coordinateProduct P := by
  apply FiniteLaw.ext
  funext x
  change (∑H : Finset (Fin n),subsetWeight p H*(∏i,(if i∈H then U else R i).mass (x i)))=
    ∏i,(P i).mass (x i)
  rw [←(maskSubsetEquiv n).sum_comp]
  change (∑a : Mask n,subsetWeight p (maskSubset a)*(∏i,(if i∈maskSubset a then U else R i).mass (x i)))=_
  simp_rw [subsetWeight_mask,maskWeight,←Finset.prod_mul_distrib]
  have he (a : Mask n) (i : Fin n) :
      (if a i then 1-(1-p) else 1-p)*(if i∈maskSubset a then U else R i).mass (x i)=
      if a i then p*U.mass (x i) else (1-p)*(R i).mass (x i) := by
    cases ha : a i <;> simp [maskSubset,ha]
  simp_rw [he]
  rw [←Fintype.prod_sum (fun i (b : Bool) => if b then p*U.mass (x i) else (1-p)*(R i).mass (x i))]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool,ite_true,Bool.false_eq_true,ite_false]
  rw [hP]

end TraceReconstruction

namespace TraceReconstruction
open scoped Classical
variable {α : Type*} [Fintype α]

theorem hiddenSchedule_payload_exact {n : ℕ} (p : ℝ) (hp : p∈Set.Icc 0 1)
    (U P' Q' P Q : FiniteLaw α)
    (hP : ∀ x,P.mass x=p*U.mass x+(1-p)*P'.mass x)
    (hQ : ∀ x,Q.mass x=p*U.mass x+(1-p)*Q'.mass x)
    (m : ℕ) (hm : m≤n) :
    (hiddenScheduleLaw (α:=Fin n) p hp m (by simpa using hm)).bind (schedulePayload U P' Q')=
      uniformSchedulePayload P Q m hm := by
  unfold hiddenScheduleLaw eraseScheduleLaw
  rw [FiniteLaw.bind_assoc]
  simp_rw [FiniteLaw.bind_map]
  rw [FiniteLaw.bind_comm]
  unfold uniformSchedulePayload
  congr 1
  funext S
  trans (subsetLaw p hp).bind (fun H : Finset (Fin n) =>
    FiniteLaw.coordinateProduct (fun i => if i∈H then U else if i∈S.val then Q' else P'))
  · congr 1
    funext H
    dsimp only [Function.comp_def,schedulePayload]
    congr 1
    funext i
    by_cases h : i∈H <;> by_cases h' : i∈S.val <;> simp [h,h']
  apply coordinateProduct_common_flags
  intro i x
  by_cases h : i∈S.val
  · simpa [h] using hQ x
  · simpa [h] using hP x

theorem uniformSchedulePayload_steps {G R : ℕ} {p : ℝ}
    (hG : 8≤G) (hR : 4*R≤G) (hp : p∈Set.Ioc 0 (1/8))
    (P Q : FiniteLaw α) (hov : p≤FiniteLaw.overlap P Q) :
    (uniformSchedulePayload (n:=2*G) P Q G (by omega)).tv
      (uniformSchedulePayload P Q (G+R) (by omega))≤
      (R:ℝ)*64/Real.sqrt (p*(2*G:ℝ)/2)+4/(p*(2*G:ℝ)) := by
  have hp1 : p∈Set.Ioo 0 1 := ⟨hp.1,by linarith [hp.2]⟩
  obtain ⟨U,P',Q',hP,hQ⟩:=FiniteLaw.common_part_decomposition P Q hp1 hov
  rw [←hiddenSchedule_payload_exact p ⟨hp.1.le,hp1.2.le⟩ U P' Q' P Q hP hQ,
    ←hiddenSchedule_payload_exact p ⟨hp.1.le,hp1.2.le⟩ U P' Q' P Q hP hQ]
  exact (FiniteLaw.tv_bind_le _ _ _).trans (hiddenScheduleLaw_steps hG hR hp)

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem coordinateProduct_simulates {α : Type*} [Fintype α]
    {n : ℕ} {q : ℝ} (P : Fin n→FiniteLaw α) (f : α→List Bool) (w : Fin n→List Bool)
    (h : ∀i,SimulatesTrace q (P i) f (w i)) :
    SimulatesTrace q (FiniteLaw.coordinateProduct P) (fun a => coordinateWord (fun i => f (a i)))
      (coordinateWord w) := by
  induction n with
  | zero =>
    intro F
    change (FiniteLaw.coordinateProduct P).expect (fun _ => F [])=F []
    exact FiniteLaw.expect_const _ _
  | succ n ih =>
    intro F
    rw [FiniteLaw.expect_coordinateProduct_succ,coordinateWord_succ,listDeletionExpectation_append]
    have hj (a : α) (x : Fin n→α) :
        coordinateWord (fun i => f ((Fin.cons a x : Fin (n+1)→α) i))=f a++coordinateWord (fun i => f (x i)) := by
      rw [coordinateWord_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
    simp_rw [hj]
    have ht:=ih (fun i => P i.succ) (fun i => w i.succ) (fun i => h i.succ)
    calc
      _=(P 0).expect (fun a => listDeletionExpectation q (coordinateWord (fun i => w i.succ))
          (fun t => F (f a++t))) := by
        congr 1
        funext a
        exact ht (fun t => F (f a++t))
      _=_ := h 0 (fun t => listDeletionExpectation q (coordinateWord (fun i => w i.succ)) (fun u => F (t++u)))

theorem sum_subset_choices {n : ℕ} (S : Finset (Fin n)) (k : ℕ) :
    (∑i : Fin n,if i∈S then k+1 else k)=n*k+S.card := by
  have he (i : Fin n) : (if i∈S then k+1 else k)=k+(if i∈S then 1 else 0) := by
    split_ifs <;> omega
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter,Nat.cast_id]

theorem coordinateWord_pureAtomRun {n : ℕ} (w : List Bool) (k : Fin n→ℕ) :
    coordinateWord (fun i => pureAtomRun w (k i))=pureAtomRun w (∑i,k i) := by
  change (List.ofFn (pureAtomRun w ∘ k)).flatten=_
  rw [←List.map_ofFn,pureAtomRun_partition,List.sum_ofFn]

theorem uniform_schedule_word {n m : ℕ} (S : FixedSubset (Fin n) m) (w : List Bool) (k : ℕ) :
    coordinateWord (fun i => if i∈S.val then pureAtomRun w (k+1) else pureAtomRun w k)=
      pureAtomRun w (n*k+m) := by
  have he (i : Fin n) : (if i∈S.val then pureAtomRun w (k+1) else pureAtomRun w k)=
      pureAtomRun w (if i∈S.val then k+1 else k) := by split_ifs <;> rfl
  simp_rw [he]
  rw [coordinateWord_pureAtomRun,sum_subset_choices,S.property]

end TraceReconstruction
noncomputable section
namespace TraceReconstruction

theorem lifting_count_scale {F k P : ℕ} {C p : ℝ}
    (hk : 1≤k) (hP : 1≤P) (hp : p∈Set.Ioc 0 (1/8))
    (hC : 1073741824≤p*C) (hF : C*k*P≤F) :
    (1048576:ℝ)*(P:ℝ)^2≤p*((F*P/(2*k+1):ℕ):ℝ) := by
  let G := F*P/(2*k+1)
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk
  have hPr : (1:ℝ)≤P := by exact_mod_cast hP
  have hGr : (0:ℝ)≤G := Nat.cast_nonneg G
  have hnat:=Nat.lt_mul_div_succ (F*P) (show 0<2*k+1 by omega)
  have hupper : (F:ℝ)*P<(2*(k:ℝ)+1)*((G:ℝ)+1) := by exact_mod_cast hnat
  have hF' := mul_le_mul_of_nonneg_right hF (show (0:ℝ)≤P by positivity)
  have hupper' := mul_lt_mul_of_pos_left hupper hp.1
  have hlower:=mul_le_mul_of_nonneg_left hF' hp.1.le
  have hC' := mul_le_mul_of_nonneg_right hC (show (0:ℝ)≤(k:ℝ)*(P:ℝ)^2 by positivity)
  have hden : (2*(k:ℝ)+1)*(p*((G:ℝ)+1))≤3*(k:ℝ)*(p*((G:ℝ)+1)) := by
    apply mul_le_mul_of_nonneg_right (by linarith)
    positivity [hp.1.le]
  have hmain : (1073741824:ℝ)*(P:ℝ)^2<3*p*((G:ℝ)+1) := by
    have h : (k:ℝ)*(1073741824*(P:ℝ)^2)<(k:ℝ)*(3*p*((G:ℝ)+1)) := by
      nlinarith only [hlower,hupper',hC',hden]
    exact (mul_lt_mul_iff_of_pos_left (by linarith : (0:ℝ)<k)).mp h
  change (1048576:ℝ)*(P:ℝ)^2≤p*(G:ℝ)
  nlinarith [sq_nonneg ((P:ℝ)-1),hp.2]

theorem lifting_scale_valid {G P : ℕ} {p : ℝ}
    (hP : 1≤P) (hp : p∈Set.Ioc 0 (1/8))
    (hscale : (1048576:ℝ)*(P:ℝ)^2≤p*(G:ℝ)) : 8≤G ∧ 4*P≤G := by
  have hPr : (1:ℝ)≤P := by exact_mod_cast hP
  have hmul:=mul_le_mul_of_nonneg_right hp.2 (Nat.cast_nonneg (α:=ℝ) G)
  have hG : (8:ℝ)≤G := by nlinarith [sq_nonneg ((P:ℝ)-1)]
  have h4 : 4*(P:ℝ)≤G := by nlinarith [sq_nonneg ((P:ℝ)-1)]
  constructor
  · exact_mod_cast hG
  · exact_mod_cast h4

theorem lifting_numeric_bound {G P : ℕ} {p : ℝ}
    (hP : 1≤P) (_hp : p∈Set.Ioc 0 (1/8))
    (hscale : (1048576:ℝ)*(P:ℝ)^2≤p*(G:ℝ)) :
    (P:ℝ)*64/Real.sqrt (p*(2*G:ℝ)/2)+4/(p*(2*G:ℝ))≤1/3 := by
  have hPr : (1:ℝ)≤P := by exact_mod_cast hP
  have hs : 0<p*(G:ℝ) := by nlinarith [sq_nonneg ((P:ℝ)-1)]
  have hre : p*(2*G:ℝ)/2=p*G := by ring
  have hden : (0:ℝ)<p*(2*G:ℝ) := by nlinarith
  have hsq : 1024*(P:ℝ)≤Real.sqrt (p*(G:ℝ)) := by
    apply (Real.le_sqrt (by positivity) (le_of_lt hs)).2
    nlinarith only [hscale]
  have hspos:=Real.sqrt_pos.2 hs
  have hfirst : (P:ℝ)*64/Real.sqrt (p*(2*G:ℝ)/2)≤1/16 := by
    rw [hre,div_le_iff₀ hspos]
    nlinarith only [hsq]
  have hsecond : 4/(p*(2*G:ℝ))≤1/16 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg ((P:ℝ)-1)]
  linarith

end TraceReconstruction
universe u
namespace TraceReconstruction
open scoped Classical
variable {α : Type u} [Fintype α]

theorem maskLaw_simulates {q : ℝ} (hq : q∈Set.Icc 0 1) (w : List Bool) :
    SimulatesTrace q (maskLaw q hq) (traceOfMask w.get) w := by
  intro F
  have h:=listDeletionExpectation_ofFn q w.get F
  rw [List.ofFn_get] at h
  exact h.symm

theorem uniformSchedulePayload_simulates {n m k : ℕ} {q : ℝ} (hm : m≤n)
    (P Q : FiniteLaw α) (f : α→List Bool) (w : List Bool)
    (hP : SimulatesTrace q P f (pureAtomRun w k))
    (hQ : SimulatesTrace q Q f (pureAtomRun w (k+1))) :
    SimulatesTrace q (uniformSchedulePayload P Q m hm)
      (fun a => coordinateWord (fun i => f (a i))) (pureAtomRun w (n*k+m)) := by
  apply SimulatesTrace.random_partition
  intro S
  rw [←uniform_schedule_word S w k]
  apply coordinateProduct_simulates
  intro i
  by_cases h : i∈S.val
  · simpa only [h,ite_true] using hQ
  · simpa only [h,ite_false] using hP

/-- Explicit source common-part lifting, using finite auxiliary observations
that decode exactly to ordinary complete traces of the adjacent pure powers. -/
theorem adjacent_power_lift {F k R : ℕ} {C p q : ℝ}
    (hk : 1≤k) (hR : 1≤R) (hp : p∈Set.Ioc 0 (1/8)) (hq : q∈Set.Icc 0 1)
    (hC : 1073741824≤p*C) (hF : C*k*R≤F)
    (P Q : FiniteLaw α) (f : α→List Bool) (w : List Bool)
    (hP : SimulatesTrace q P f (pureAtomRun w k))
    (hQ : SimulatesTrace q Q f (pureAtomRun w (k+1)))
    (hov : p≤FiniteLaw.overlap P Q) :
    ∃ (β : Type u) (_ : Fintype β) (P' Q' : FiniteLaw β) (g : β→List Bool),
      SimulatesTrace q P' g (pureAtomRun w (F*R)) ∧
      SimulatesTrace q Q' g (pureAtomRun w (F*R+R)) ∧
      (2/3:ℝ)≤FiniteLaw.overlap P' Q' := by
  let G := F*R/(2*k+1)
  have hs : (1048576:ℝ)*(R:ℝ)^2≤p*(G:ℝ) := lifting_count_scale hk hR hp hC hF
  obtain ⟨hG,hr⟩:=lifting_scale_valid hR hp hs
  let A:=uniformSchedulePayload (n:=2*G) P Q G (by omega)
  let B:=uniformSchedulePayload (n:=2*G) P Q (G+R) (by omega)
  have htv : A.tv B≤1/3 :=
    (uniformSchedulePayload_steps hG hr hp P Q hov).trans (lifting_numeric_bound hR hp hs)
  let tail:=pureAtomRun w (F*R-G*(2*k+1))
  let S:=maskLaw (n:=tail.length) q hq
  let g : (Fin (2*G)→α)×Mask tail.length→List Bool :=
    fun a => coordinateWord (fun i => f (a.1 i))++traceOfMask tail.get a.2
  refine ⟨(Fin (2*G)→α)×Mask tail.length,inferInstance,A.prod S,B.prod S,g,?_,?_,?_⟩
  · have ha:=uniformSchedulePayload_simulates (n:=2*G) (by omega : G≤2*G) P Q f w hP hQ
    have ht:=(ha.append (maskLaw_simulates hq tail))
    have hh : G*(2*k+1)≤F*R := Nat.div_mul_le_self _ _
    have he : 2*G*k+G+(F*R-G*(2*k+1))=F*R := by
      have he0 : G*(2*k+1)=2*G*k+G := by ring
      omega
    simpa only [tail,←pureAtomRun_add,he] using ht
  · have hb:=uniformSchedulePayload_simulates (n:=2*G) (by omega : G+R≤2*G) P Q f w hP hQ
    have ht:=(hb.append (maskLaw_simulates hq tail))
    have hh : G*(2*k+1)≤F*R := Nat.div_mul_le_self _ _
    have he : 2*G*k+(G+R)+(F*R-G*(2*k+1))=F*R+R := by
      have he0 : G*(2*k+1)=2*G*k+G := by ring
      omega
    simpa only [tail,←pureAtomRun_add,he] using ht
  · rw [FiniteLaw.overlap_eq_one_sub_tv,FiniteLaw.tv_prod_eq_left]
    linarith

end TraceReconstruction



/-!
Concrete objects for the scale inequalities, Definition 3 (the level invariant).
The observable channel remains the complete deletion trace of a literal word.
-/
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialOverlap

Literal periods, count overlap, initial low/high energies, genuine densities, and centered moment bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem primitivePeriodConstant_nonneg : 0 ≤ primitivePeriodConstant := by
  unfold primitivePeriodConstant
  positivity

end TraceReconstruction



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem initialOverlapLower_pos (q : ℝ) : 0 < initialOverlapLower q := by
  unfold initialOverlapLower
  positivity

theorem initialOverlapLower_lt_eighth {q : ℝ} (hq : 0 < q) :
    initialOverlapLower q < 1/8 := by
  have hx : -(32+3*primitivePeriodConstant)/q^3 ≤ 0 := by
    have hc := primitivePeriodConstant_nonneg
    apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith [pow_pos hq 3]
  have he : Real.exp (-(32+3*primitivePeriodConstant)/q^3) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr hx
  unfold initialOverlapLower
  linarith

/-- Data processing for common exact simulators, stated as a common-mass
inequality and allowing unequal original lengths. -/
theorem simulations_overlap_le {α : Type*} [Fintype α] {q : ℝ}
    (hq : q ∈ Set.Icc 0 1) (P Q : FiniteLaw α) (decode : α → List Bool)
    (x y : List Bool) (hP : SimulatesTrace q P decode x)
    (hQ : SimulatesTrace q Q decode y) :
    P.overlap Q ≤ listTraceOverlap q hq x y := by
  have h := approximations_trace_tv hq P Q decode x y 0 0
    (max x.length y.length) (le_max_left _ _) (le_max_right _ _)
    hP.approximate hQ.approximate
  simp only [add_zero] at h
  unfold listTraceOverlap
  rw [FiniteLaw.overlap_eq_one_sub_tv, FiniteLaw.overlap_eq_one_sub_tv]
  linarith

end TraceReconstruction



/-! From the actual displaced period words to their conditional oracle
moments.  The coefficient bounds are the rank kernels,
not assumptions on an abstract pair. -/
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_SourceOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# SourceOracle

Actual source mechanisms and posteriors, typical metadata, sparse degrees, common-event clipping, approximate oracles, and mixed Hellinger bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem listTraceOverlap_ambient {q : ℝ} (hq : q∈Set.Icc 0 1)
    (x y : List Bool) (M : ℕ) (hx : x.length≤M) (hy : y.length≤M) :
    listTraceOverlap q hq x y=
      (listTraceLaw q hq x M hx).overlap (listTraceLaw q hq y M hy) := by
  apply le_antisymm (listTraceOverlap_le_ambient hq x y M hx hy)
  exact simulations_overlap_le hq _ _ Subtype.val x y
    (listTraceLaw_simulates q hq x M hx) (listTraceLaw_simulates q hq y M hy)

end TraceReconstruction


end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Amplification

Oracle products, mixed powers, padding, warmup and nested template Hellinger estimates, overlap, and block assembly.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Genuine lifting for complete traces, with no auxiliary overlap hypothesis. -/
theorem listTraceOverlap_lift {F k R : ℕ} {C p q : ℝ}
    (hk : 1≤k) (hR : 1≤R) (hp : p∈Set.Ioc 0 (1/8)) (hq : q∈Set.Icc 0 1)
    (hC : 1073741824≤p*C) (hF : C*k*R≤F) (w : List Bool)
    (hov : p≤listTraceOverlap q hq (pureAtomRun w k) (pureAtomRun w (k+1))) :
    (2/3:ℝ)≤listTraceOverlap q hq (pureAtomRun w (F*R)) (pureAtomRun w (F*R+R)) := by
  let M := max (pureAtomRun w k).length (pureAtomRun w (k+1)).length
  have H := adjacent_power_lift hk hR hp hq hC hF
    (listTraceLaw q hq (pureAtomRun w k) M (le_max_left _ _))
    (listTraceLaw q hq (pureAtomRun w (k+1)) M (le_max_right _ _)) Subtype.val w
    (listTraceLaw_simulates q hq _ M _) (listTraceLaw_simulates q hq _ M _) hov
  obtain ⟨β,fin,P,Q,g,hP,hQ,hO⟩ := H
  let := fin
  exact hO.trans (simulations_overlap_le hq P Q g _ _ hP hQ)

theorem pureAtomRun_mul (w : List Bool) (n m : ℕ) :
    pureAtomRun (pureAtomRun w n) m=pureAtomRun w (m*n) := by
  induction m with
  | zero => simp [pureAtomRun]
  | succ m ih =>
    have H : pureAtomRun (pureAtomRun w n) (m+1)=
        pureAtomRun w n++pureAtomRun (pureAtomRun w n) m := by
      simp [pureAtomRun,List.replicate_succ]
    rw [H,ih,←pureAtomRun_add]
    congr 1
    ring

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem ApproximatesTrace.power {α : Type*} [Fintype α] {q E : ℝ} {P : FiniteLaw α}
    {g : α → List Bool} {w : List Bool} (H : ApproximatesTrace q P g w E)
    (hq : q∈Set.Icc 0 1) (F : ℕ) :
    ApproximatesTrace q (P.product F) (fun z => coordinateWord (fun i => g (z i)))
      (pureAtomRun w F) ((F:ℝ)*E) := by
  have h := coordinateProduct_approximates hq (fun _ : Fin F => P) (fun _ => g)
    (fun _ => w) (fun _ => E) (fun _ => H)
  have he : FiniteLaw.coordinateProduct (fun _ : Fin F => P)=P.product F := rfl
  rw [he,coordinateWord_constant] at h
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

end TraceReconstruction



noncomputable section



noncomputable section



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem HellingerTracePair.power_tv {q E V : ℝ} {x y : List Bool}
    (C : HellingerTracePair q x y E V) (hq : q∈Set.Icc 0 1)
    (F M : ℕ) (hx : (pureAtomRun x F).length ≤ M) (hy : (pureAtomRun y F).length ≤ M) :
    (listTraceLaw q hq (pureAtomRun x F) M hx).tv
      (listTraceLaw q hq (pureAtomRun y F) M hy) ≤ Real.sqrt ((F:ℝ)*V)+2*(F:ℝ)*E := by
  let := C.finiteOutcome
  have htv := (FiniteLaw.tv_le_sqrt_hellingerSq (C.first.product F) (C.second.product F)).trans
    (Real.sqrt_le_sqrt ((FiniteLaw.hellingerSq_product_le C.first C.second F).trans
      (mul_le_mul_of_nonneg_left C.bound (Nat.cast_nonneg F))))
  have H := approximations_trace_tv hq _ _ _ _ _ _ _ M hx hy
    (C.first_simulation.power hq F) (C.second_simulation.power hq F)
  linarith only [H,htv]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem HellingerTracePair.lifted_power_overlap {q E V p C₀ : ℝ} {w z : List Bool}
    {h P F : ℕ} (O : HellingerTracePair q (pureAtomRun w P) z E V)
    (hq : q∈Set.Icc 0 1) (hh : 1 ≤ h) (hP : 1 ≤ P)
    (hp : p∈Set.Ioc 0 (1/8)) (hC : 1073741824 ≤ p*C₀) (hF : C₀*h*P ≤ F)
    (hov : p ≤ listTraceOverlap q hq (pureAtomRun w h) (pureAtomRun w (h+1))) :
    (2/3:ℝ)-(Real.sqrt ((F:ℝ)*V)+2*(F:ℝ)*E)-
      (Real.sqrt (((F+1:ℕ):ℝ)*V)+2*((F+1:ℕ):ℝ)*E) ≤
      listTraceOverlap q hq (pureAtomRun z F) (pureAtomRun z (F+1)) := by
  let a := pureAtomRun (pureAtomRun w P) F
  let b := pureAtomRun (pureAtomRun w P) (F+1)
  let x := pureAtomRun z F
  let y := pureAtomRun z (F+1)
  let M := max (max a.length b.length) (max x.length y.length)
  have ha : a.length ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hb : b.length ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hx : x.length ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hy : y.length ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have ht1 := O.power_tv hq F M ha hx
  have ht2 := O.power_tv hq (F+1) M hb hy
  have hol := listTraceOverlap_lift hh hP hp hq hC hF w hov
  have he : F*P+P=(F+1)*P := by ring
  have heA : pureAtomRun w (F*P)=a := (pureAtomRun_mul w P F).symm
  have heB : pureAtomRun w (F*P+P)=b := by
    rw [he]; exact (pureAtomRun_mul w P (F+1)).symm
  rw [heA,heB] at hol
  rw [listTraceOverlap_ambient hq _ _ M ha hb,FiniteLaw.overlap_eq_one_sub_tv] at hol
  rw [listTraceOverlap_ambient hq _ _ M hx hy,FiniteLaw.overlap_eq_one_sub_tv]
  have H := (FiniteLaw.tv_triangle (listTraceLaw q hq x M hx) (listTraceLaw q hq a M ha)
    (listTraceLaw q hq y M hy)).trans
    (add_le_add le_rfl (FiniteLaw.tv_triangle (listTraceLaw q hq a M ha)
      (listTraceLaw q hq b M hb) (listTraceLaw q hq y M hy)))
  rw [FiniteLaw.tv_symm (listTraceLaw q hq x M hx) (listTraceLaw q hq a M ha)] at H
  linarith only [H,ht1,ht2,hol]

theorem HellingerTracePair.lifted_overlap_quarter {q E V p C₀ : ℝ} {w z : List Bool}
    {h P F : ℕ} (O : HellingerTracePair q (pureAtomRun w P) z E V)
    (hq : q∈Set.Icc 0 1) (hE : 0 ≤ E) (hh : 1 ≤ h) (hP : 1 ≤ P)
    (hp : p∈Set.Ioc 0 (1/8)) (hC : 1073741824 ≤ p*C₀) (hF : C₀*h*P ≤ F)
    (hov : p ≤ listTraceOverlap q hq (pureAtomRun w h) (pureAtomRun w (h+1)))
    (hsmall : Real.sqrt (((F+1:ℕ):ℝ)*V)+2*((F+1:ℕ):ℝ)*E ≤ 1/4) :
    p ≤ listTraceOverlap q hq (pureAtomRun z F) (pureAtomRun z (F+1)) := by
  let := O.finiteOutcome
  have hV : 0 ≤ V := (FiniteLaw.hellingerSq_nonneg _ _).trans O.bound
  have ht := O.lifted_power_overlap hq hh hP hp hC hF hov
  have hm : Real.sqrt ((F:ℝ)*V)+2*(F:ℝ)*E ≤
      Real.sqrt (((F+1:ℕ):ℝ)*V)+2*((F+1:ℕ):ℝ)*E := by
    apply add_le_add
    · apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_right (by norm_num) hV
    · exact mul_le_mul_of_nonneg_right (by norm_num) hE
  linarith only [hm,hsmall,ht,hp.2]

/-- Finite nested overlap induction at the main (post-warmup) dimensions.
 Every closeness premise is an explicit scalar estimate on the old oracle;
 the repeated-word overlaps themselves are proved, not assumed. -/
theorem source_nested_overlap {q E V p C₀ : ℝ} (hq : q∈Set.Icc 0 1)
    (hE : 0 ≤ E) (s : ℕ) (P h : ℕ → ℕ) (atom : Bool → List Bool)
    (C : HellingerTracePair q (atom false) (atom true) E V) (b : ℕ)
    (hp : p∈Set.Ioc 0 (1/8)) (hC : 1073741824 ≤ p*C₀)
    (hcount : ∀j ≤ b,1 ≤ h j) (hP : ∀j < b,1 ≤ P j)
    (hlift : ∀j < b,C₀*h j*P j ≤ h (j+1))
    (hsmall : ∀j < b,
      Real.sqrt (((h (j+1)+1:ℕ):ℝ)*(((2^s:ℕ):ℝ)^(j+1)*V))+
        2*((h (j+1)+1:ℕ):ℝ)*((sourceBlockLength P 1 (j+1):ℝ)*E) ≤ 1/4)
    (hbase : p ≤ listTraceOverlap q hq (pureAtomRun (atom false) (h 0))
      (pureAtomRun (atom false) (h 0+1))) :
    ∀j ≤ b,p ≤ listTraceOverlap q hq (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1)) := by
  intro j hj
  induction j with
  | zero => exact hbase
  | succ j ih =>
    have hjb : j < b := by omega
    have D := (sourceDensePair hq s P atom C j).pure_template hq (P j) (P j/2-1) (2^s) (prouhetBool s) false
    rw [bool_word_eta] at D
    have H := D.lifted_overlap_quarter hq (by positivity) (hcount j (by omega)) (hP j hjb)
      hp hC (hlift j hjb) (ih (by omega)) ?_
    · exact H
    · simpa only [sourceBlockLength,Nat.cast_mul,pow_succ,mul_assoc,mul_left_comm,mul_comm]
        using hsmall j hjb

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical


theorem sourceFitTail_nonneg (T n : ℕ → ℕ) (b : ℕ) : 0 ≤ sourceFitTail T n b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    cases b with
    | zero => rfl
    | succ b => exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (by positivity) ih)

theorem sourceEffectiveHiddenTail_nonneg (T n : ℕ → ℕ) (b : ℕ) (ω : ℝ) :
    0 ≤ sourceEffectiveHiddenTail T n b ω := by
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> positivity

theorem sourceClippingCost_nonneg (T n : ℕ → ℕ) (s b k : ℕ) (ω a L : ℝ) (ha : 0 ≤ a) :
    0 ≤ sourceClippingCost T n s b k ω a L := by
  exact add_nonneg (add_nonneg (sourceEffectiveHiddenTail_nonneg _ _ _ _)
    (div_nonneg (sourceFitTail_nonneg _ _ _) ha)) (Real.sqrt_nonneg _)

/-- The two-dimensional warmup uses the actual one-window cancellation
 oracle at its second nested overlap step. No unproved side overlap is
 inserted into the recursive source observation. -/
theorem source_warmup_nested_overlap {q E V p C₀ : ℝ} (hq : q∈Set.Icc 0 1)
    (hE : 0 ≤ E) (s k : ℕ) (P h : ℕ → ℕ) (atom : Bool → List Bool)
    (C : OracleTracePair q (atom false) (atom true) k E V)
    (hp : p∈Set.Ioc 0 (1/8)) (hC : 1073741824 ≤ p*C₀)
    (hcount : ∀j ≤ 1,1 ≤ h j) (hP : ∀j < 2,1 ≤ P j)
    (hlift : ∀j < 2,C₀*h j*P j ≤ h (j+1))
    (hfirst : Real.sqrt (((h 1+1:ℕ):ℝ)*((2^s:ℕ):ℝ)*V)+
      2*((h 1+1:ℕ):ℝ)*((P 0:ℝ)*E) ≤ 1/4)
    (hbase : p ≤ listTraceOverlap q hq (pureAtomRun (atom false) (h 0))
      (pureAtomRun (atom false) (h 0+1)))
    (T t : ℕ) (hT : 24 ≤ T) (he : Even T) (hMotif : 24*2^s ≤ T)
    (hroot : 4*(t+1) ≤ T) (hfit : t*(2*h 0+1)+T ≤ P 0)
    (a η L : ℝ) (ha : 0 < a) (hL : 0 < L) (hk : 1 ≤ k) (hV : V ≤ L^2)
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount (fun _ => T) s 0 ≤ 1/2)
    (hη : hiddenSmoothingBound t s p ≤ η)
    (herror : sourceClippingCost (fun _ => T) (fun _ => t) s 0 k p a L ≤ 1/2)
    (hsecond :
      Real.sqrt (((h 2+1:ℕ):ℝ)*((2^s:ℕ):ℝ)*
        (64*sourceSharpEnergyBudget (fun _ => T) (fun _ => t) s 0 2 p η a ((6*(2*k:ℕ):ℝ)*L)))+
      2*((h 2+1:ℕ):ℝ)*((P 1:ℝ)*
        (sourceClippingCost (fun _ => T) (fun _ => t) s 0 k p a L+(T:ℝ)*E)) ≤ 1/4) :
    ∀j ≤ 2,p ≤ listTraceOverlap q hq (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1)) := by
  have hp' : p∈Set.Ioo 0 1 := ⟨hp.1,lt_of_le_of_lt hp.2 (by norm_num)⟩
  have D := (C.hellinger hk).pure_template hq (P 0) (P 0/2-1) (2^s) (prouhetBool s) false
  rw [bool_word_eta] at D
  have h1 := D.lifted_overlap_quarter hq (by positivity) (hcount 0 (by omega))
    (hP 0 (by omega)) hp hC (hlift 0 (by omega)) hbase ?_
  · obtain ⟨W⟩ := actual_one_window_oracle C hq hE s (P 0) T t (h 0) 2 hT he hMotif
      hroot hfit p a η L ha hL hp' hbase hk hV hscale hη herror
    rw [bool_word_eta] at W
    have W' := (W.hellinger hk).pure_template hq (P 1) (P 1/2-1) (2^s) (prouhetBool s) false
    have heword : (fun τ => if τ then
        complementaryWords (P 0) (P 0/2-1) (2^s) (prouhetBool s) atom true else
        complementaryWords (P 0) (P 0/2-1) (2^s) (prouhetBool s) atom false) =
        sourceBlockWord s P atom 1 := bool_word_eta _
    rw [heword] at W'
    have hE' : 0 ≤ sourceClippingCost (fun _ => T) (fun _ => t) s 0 k p a L+(T:ℝ)*E := by
      exact add_nonneg (sourceClippingCost_nonneg _ _ _ _ _ _ _ _ ha.le) (by positivity)
    have h2 := W'.lifted_overlap_quarter hq (mul_nonneg (Nat.cast_nonneg _) hE')
      (hcount 1 le_rfl) (hP 1 (by omega)) hp hC (hlift 1 (by omega)) h1 ?_
    · intro j hj
      interval_cases j
      · exact hbase
      · exact h1
      · exact h2
    · simpa only [mul_assoc] using hsecond
  · simpa only [mul_assoc] using hfirst

end TraceReconstruction


end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialRates

Initial geometric parameters, moment depths, error and overlap rates, and production of the base induction pair.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem totalScoreExponent_bounds (B D : ℕ) (hB : 2 ≤ B) :
    11/5 ≤ totalScoreExponent B D ∧ totalScoreExponent B D ≤ 3+(D:ℝ)*B := by
  have hdim (i : ℕ) : (2:ℝ) ≤ (if i<warmupBlocks B then (2:ℕ) else B) ∧
      (((if i<warmupBlocks B then (2:ℕ) else B):ℕ):ℝ) ≤ B := by
    split_ifs <;> norm_cast
  have hlo : 0 ≤ ∑i∈Finset.range D,blockGain (if i<warmupBlocks B then 2 else B) := by
    apply Finset.sum_nonneg
    intro i _
    unfold blockGain
    linarith [(hdim i).1]
  have hhi : (∑i∈Finset.range D,blockGain (if i<warmupBlocks B then 2 else B)) ≤ (D:ℝ)*B := by
    calc
      _ ≤ ∑_i∈Finset.range D,(B:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        unfold blockGain
        linarith [(hdim i).1,(hdim i).2]
      _ = _ := by simp
  unfold totalScoreExponent
  constructor <;> linarith

theorem sourceHalfMoment_bounds (B D i : ℕ) {n : ℝ} (hB : 2 ≤ B) (hn : 1<n) :
    1 ≤ sourceHalfMoment B D n i ∧
    (sourceHalfMoment B D n i:ℝ) ≤
      ((10^8:ℝ)*2^(10*B)*((B:ℝ)+4)*2+1)*((D:ℝ)+1)*2^(B*D) := by
  have hp := sourceScaleProduct_lower B D i hB
  have hp0 : 0 < sourceScaleProduct B D i := lt_of_lt_of_le (by positivity) hp
  have he : (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)*Real.log n/
      Real.log (sourceTargetScale B D n i)=
      (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)/sourceScaleProduct B D i := by
    rw [sourceTargetScale,Real.log_rpow (by linarith : 0<n)]
    field_simp [(Real.log_pos hn).ne']
  have hd := totalScoreExponent_bounds B D hB
  have hA : 0<(10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1) := by positivity [hd.1]
  unfold sourceHalfMoment
  rw [he]
  constructor
  · exact Nat.one_le_ceil_iff.mpr (div_pos hA hp0)
  have hc := Nat.ceil_lt_add_one (div_nonneg hA.le hp0.le)
  have hb := div_le_div_of_nonneg_left hA.le (by positivity) hp
  have he' : (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)/(1/(2*2^(B*D)))=
      (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)*2*2^(B*D) := by field_simp
  rw [he'] at hb
  have hdd : totalScoreExponent B D+B+1 ≤ ((B:ℝ)+4)*((D:ℝ)+1) := by nlinarith [hd.2]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdd (by positivity : (0:ℝ) ≤ 10^8*2^(10*B)))
    (by positivity : (0:ℝ) ≤ 2*2^(B*D))
  have hp1 : (1:ℝ) ≤ 2^(B*D) := one_le_pow₀ (by norm_num)
  nlinarith [show (0:ℝ) ≤ D by positivity]

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N f g : ℕ→ℝ} {α β : ℝ}

theorem sourceOverlapConstant_pos {q : ℝ} (hq : 0<q) : 0 < sourceOverlapConstant q := by
  unfold sourceOverlapConstant
  positivity [initialOverlapLower_pos q]

theorem sourceOverlapConstant_large {q : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) :
    1073741824 ≤ initialOverlapLower q*sourceOverlapConstant q := by
  have hω := initialOverlapLower_pos q
  have he : initialOverlapLower q*sourceOverlapConstant q=(2:ℝ)^40/q := by
    unfold sourceOverlapConstant
    field_simp
  rw [he]
  apply (le_div_iff₀ hq.1).mpr
  nlinarith [hq.2]

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- All backwards targets are no larger than n, with the source epsilon. -/
theorem sourceScaleProduct_le_one (B D i : ℕ) (hB : 2 ≤ B) : sourceScaleProduct B D i ≤ 1 := by
  apply Finset.prod_le_one
  · intro j _
    have hdim : sourceDimension B j ≤ B := by unfold sourceDimension; split_ifs <;> omega
    have he := sourceEpsilon_pos B D
    have hh := sourceEpsilon_small B D
    have hp : (1:ℝ) ≤ 2^B := one_le_pow₀ (by norm_num)
    have hd : 0 ≤ (D:ℝ) := Nat.cast_nonneg _
    have hu : (2:ℝ)^B*sourceEpsilon B D ≤ 1/2 := by
      nlinarith only [hh,mul_nonneg hd (mul_nonneg (le_trans zero_le_one hp) he.le)]
    have hx := scaleA_zero_lower (sourceDimension B j) B (sourceEpsilon B D) hdim he.le
    apply le_trans _ hx
    exact mul_nonneg (by positivity) (by nlinarith only [hu,he])
  · intro j _
    have he := sourceEpsilon_pos B D
    have hp : (1:ℝ) ≤ 2^(sourceDimension B j) := one_le_pow₀ (by norm_num)
    unfold scaleA
    norm_num only [pow_zero,mul_one]
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<2^(sourceDimension B j))).mpr
      (show 1+sourceEpsilon B D ≤ (1+sourceEpsilon B D)*2^(sourceDimension B j) from
        le_mul_of_one_le_right (by linarith only [he]) hp)
    linarith only [hh]

end TraceReconstruction


end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_LayoutRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# LayoutRates

Integer block schedules, rounding, length and trial margins, sparse gaps, and forced-anchor decay.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceLocalTrials_budget (P h : ℕ) :
    50*sourceLocalTrials P h*(2*h+1) ≤ P := by
  have H := Nat.mul_div_le P (100*(2*h+1))
  unfold sourceLocalTrials
  nlinarith only [H]

theorem sourceWindowSize_even (N : ℝ) (b : ℕ) (ε : ℝ) (j : ℕ) :
    Even (sourceWindowSize N b ε j) := by
  unfold sourceWindowSize
  exact ⟨2*⌊N^(scaleKappa b (j+1) ε)/4⌋₊,by ring⟩

theorem sourceArithmeticLength_step (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ) :
    sourceArithmeticLength C N b ε ell k (j+1)=
      sourceArithmeticLength C N b ε ell k j*sourceArithmeticP C N b ε ell k j := rfl

theorem sourceArithmeticCount_step (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ) :
    sourceArithmeticCount C N b ε ell k (j+1)=
      ⌈C*sourceArithmeticCount C N b ε ell k j*sourceArithmeticP C N b ε ell k j⌉₊ := rfl

theorem sourceArithmetic_inner_trials (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ)
    (hj : j+1≠b) : sourceArithmeticTrials C N b ε ell k j=
      sourceLocalTrials (sourceArithmeticP C N b ε ell k j) (sourceArithmeticCount C N b ε ell k j) := by
  simp only [sourceArithmeticTrials,sourceArithmeticP,sourceArithmeticCount,sourceArithmeticStages,ite_eq_right hj]

theorem sourceArithmetic_count_lift (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ) :
    C*sourceArithmeticCount C N b ε ell k j*sourceArithmeticP C N b ε ell k j ≤
      sourceArithmeticCount C N b ε ell k (j+1) := Nat.le_ceil _

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Rounding the source windows loses at most a factor two. -/
theorem sourceWindowSize_bounds {N ε : ℝ} {b j : ℕ}
    (h : 8 ≤ N^(scaleKappa b (j+1) ε)) :
    N^(scaleKappa b (j+1) ε)/2 ≤ (sourceWindowSize N b ε j:ℝ) ∧
      (sourceWindowSize N b ε j:ℝ) ≤ N^(scaleKappa b (j+1) ε) := by
  have hlo := Nat.lt_floor_add_one (N^(scaleKappa b (j+1) ε)/4)
  have hhi := Nat.floor_le (show 0 ≤ N^(scaleKappa b (j+1) ε)/4 by linarith)
  unfold sourceWindowSize
  push_cast
  constructor <;> linarith only [h,hlo,hhi]

/-- The nonroot even trial count is between one and two times its unrounded
 quotient once the quotient is at least two. -/
theorem sourceLocalTrials_bounds (P h : ℕ) (hlarge : (200:ℝ)*(2*h+1) ≤ P) :
    (P:ℝ)/(100*(2*h+1)) ≤ (sourceLocalTrials P h:ℝ) ∧
      (sourceLocalTrials P h:ℝ) ≤ (P:ℝ)/(50*(2*h+1)) := by
  have hd : 0 < (100:ℝ)*(2*h+1) := by positivity
  have hx : (2:ℝ) ≤ (P:ℝ)/(100*(2*h+1)) := (le_div_iff₀ hd).mpr (by linarith only [hlarge])
  have he : (sourceLocalTrials P h:ℝ)=2*(⌊(P:ℝ)/(100*(2*h+1))⌋₊:ℝ) := by
    unfold sourceLocalTrials
    rw [show (100:ℝ)*(2*h+1)=((100*(2*h+1):ℕ):ℝ) by push_cast; ring,Nat.floor_div_eq_div]
    norm_cast
  rw [he]
  have hlo := Nat.lt_floor_add_one ((P:ℝ)/(100*(2*h+1)))
  have hhi := Nat.floor_le (div_nonneg (Nat.cast_nonneg P) hd.le)
  constructor
  · linarith only [hx,hlo]
  · have heq : (P:ℝ)/(50*(2*h+1))=2*((P:ℝ)/(100*(2*h+1))) := by field_simp; ring
    rw [heq]
    linarith only [hhi]

theorem source_floor_length_bounds {X : ℝ} {S : ℕ} (hS : 0 < S) (hX : 2*(S:ℝ) ≤ X) :
    X/2 ≤ ((S*⌊X/(S:ℝ)⌋₊:ℕ):ℝ) ∧ ((S*⌊X/(S:ℝ)⌋₊:ℕ):ℝ) ≤ X := by
  have hs : (0:ℝ) < S := by exact_mod_cast hS
  have hlo := Nat.lt_floor_add_one (X/(S:ℝ))
  have hhi := Nat.floor_le (div_nonneg (show 0 ≤ X by linarith only [hX,hs]) hs.le)
  have hh := mul_lt_mul_of_pos_left hlo hs
  have hh' := mul_le_mul_of_nonneg_left hhi hs.le
  rw [mul_add,mul_div_cancel₀ _ hs.ne'] at hh
  rw [mul_div_cancel₀ _ hs.ne'] at hh'
  push_cast
  constructor <;> nlinarith only [hX,hh,hh']

theorem source_root_length_bounds {N : ℝ} {S T h : ℕ} (hS : 0 < S)
    (hT : T ≤ ⌊N/(S:ℝ)⌋₊) (hN : (2*h+2:ℝ)*S ≤ N/2) :
    N/2 ≤ (S:ℝ)*(sourceRootTrials N S T h*(2*h+1)+T) ∧
      (S:ℝ)*(sourceRootTrials N S T h*(2*h+1)+T) ≤ N := by
  have hs : (0:ℝ)<S := by exact_mod_cast hS
  have hd : 0 < 2*h+1 := by omega
  have hi := Nat.div_mul_le_self (⌊N/(S:ℝ)⌋₊-T) (2*h+1)
  have hj := Nat.lt_mul_div_succ (⌊N/(S:ℝ)⌋₊-T) hd
  rw [Nat.mul_comm (2*h+1)] at hj
  have hp : sourceRootTrials N S T h*(2*h+1)+T ≤ ⌊N/(S:ℝ)⌋₊ := by
    unfold sourceRootTrials
    omega
  have hp' : ⌊N/(S:ℝ)⌋₊ < (sourceRootTrials N S T h+1)*(2*h+1)+T := by
    unfold sourceRootTrials
    omega
  have hN0 : 0 ≤ N := by
    have hh : (0:ℝ) ≤ (2*h+2:ℝ)*S := by positivity
    linarith only [hN,hh]
  have hfloor := Nat.floor_le (div_nonneg hN0 hs.le)
  have hfloor' := Nat.lt_floor_add_one (N/(S:ℝ))
  have hpr : (sourceRootTrials N S T h:ℝ)*(2*h+1)+T ≤ (⌊N/(S:ℝ)⌋₊:ℝ) := by exact_mod_cast hp
  have hpr' : (⌊N/(S:ℝ)⌋₊:ℝ) < (sourceRootTrials N S T h+1:ℝ)*(2*h+1)+T := by exact_mod_cast hp'
  constructor
  · have hf : N/(S:ℝ) < (sourceRootTrials N S T h:ℝ)*(2*h+1)+T+(2*h+2) := by
      nlinarith only [hfloor',hpr']
    have hh := mul_lt_mul_of_pos_left hf hs
    rw [mul_div_cancel₀ _ hs.ne'] at hh
    nlinarith only [hh,hN]
  · have hh := mul_le_mul_of_nonneg_left (hpr.trans hfloor) hs.le
    simpa only [mul_div_cancel₀ _ hs.ne'] using hh

theorem source_ceil_count_bounds {C F : ℝ} {S h P : ℕ} (hC : 2 ≤ C) (hF : 1 ≤ F)
    (hS : 1 ≤ S) (hP : 1 ≤ P) (hlo : S ≤ h) (hhi : (h:ℝ) ≤ F*S) :
    S*P ≤ ⌈C*h*P⌉₊ ∧ (⌈C*h*P⌉₊:ℝ) ≤ C^2*F*(S*P) := by
  have hs : (1:ℝ) ≤ S := by exact_mod_cast hS
  have hp : (1:ℝ) ≤ P := by exact_mod_cast hP
  have hh : (S:ℝ) ≤ h := by exact_mod_cast hlo
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ C*(h:ℝ)*P by positivity)
  constructor
  · have hbound : (S:ℝ)*P ≤ C*h*P := by
      have hh' := mul_le_mul_of_nonneg_right hh (by positivity : (0:ℝ) ≤ P)
      have hc := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ C by linarith) (show 0 ≤ (h:ℝ)*P by positivity)
      nlinarith only [hh',hc]
    exact_mod_cast hbound.trans (Nat.le_ceil (C*(h:ℝ)*P))
  · have hmul := mul_le_mul_of_nonneg_left hhi (show 0 ≤ C*(P:ℝ) by positivity)
    have hbase : (1:ℝ) ≤ F*(S*P) := one_le_mul_of_one_le_of_one_le hF (one_le_mul_of_one_le_of_one_le hs hp)
    have hgain : 1 ≤ C*(C-1) := by nlinarith only [hC]
    have hgap := mul_le_mul hgain hbase (by norm_num) (by linarith only [hgain])
    nlinarith only [hceil,hmul,hgap]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_scale_target_step {N ε : ℝ} (b j : ℕ) (hN : 0 < N) :
    N^(scaleA b (j+1) ε)=(N^(scaleA b j ε))^2*N^ε := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_add hN]
  congr 1
  have hh := scaleA_step b j ε
  norm_num only [Nat.cast_ofNat]
  linarith only [hh]

theorem sourceWindowSize_le_previous {N ε : ℝ} {b j : ℕ}
    (hN : 1 ≤ N) (he : 0 ≤ ε) :
    (sourceWindowSize N b ε j:ℝ) ≤ N^(scaleA b j ε) := by
  have hf := Nat.floor_le (show 0 ≤ N^(scaleKappa b (j+1) ε)/4 by positivity)
  have hk : scaleKappa b (j+1) ε ≤ scaleA b j ε := by
    unfold scaleKappa
    simp only [Nat.add_sub_cancel]
    have hh : (1:ℝ) ≤ 2^(j+1) := one_le_pow₀ (by norm_num)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hh) he]
  apply le_trans _ (Real.rpow_le_rpow_of_exponent_le hN hk)
  unfold sourceWindowSize
  push_cast
  linarith only [hf]

/-- The root's subtraction and rounding margins follow from the one
 subpower comparison N^epsilon >= 8F. -/
theorem source_root_margins {N X u F : ℝ} {S h T : ℕ}
    (hS : 1 ≤ S) (hX : (S:ℝ) ≤ X) (hF : 1 ≤ F) (hu : 8*F ≤ u)
    (hh : (h:ℝ) ≤ F*S) (hT : (T:ℝ) ≤ X) (hrel : X^2*u=N) :
    T ≤ ⌊N/(S:ℝ)⌋₊ ∧ (2*(h:ℝ)+2)*S ≤ N/2 := by
  have hs : (1:ℝ) ≤ S := by exact_mod_cast hS
  have hx : 1 ≤ X := hs.trans hX
  have hx0 : 0 ≤ X := by linarith only [hx]
  have hs0 : (0:ℝ) < S := by linarith only [hs]
  have hfs : 1 ≤ F*S := by nlinarith only [hF,hs]
  have hsX : (S:ℝ)^2 ≤ X^2 := sq_le_sq₀ hs0.le hx0 |>.mpr hX
  have h8 : 8*F*X^2 ≤ N := by nlinarith only [mul_le_mul_of_nonneg_right hu (sq_nonneg X),hrel]
  constructor
  · apply Nat.le_floor
    apply (le_div_iff₀ hs0).mpr
    have htX := mul_le_mul hT hX hs0.le hx0
    nlinarith only [htX,h8,mul_le_mul_of_nonneg_right hF (sq_nonneg X)]
  · have hhS := mul_le_mul_of_nonneg_right hh hs0.le
    have hS2 := mul_le_mul_of_nonneg_right hfs hs0.le
    have hFsq := mul_le_mul_of_nonneg_left hsX (by linarith only [hF] : 0 ≤ F)
    nlinarith only [hhS,hS2,hFsq,h8]

theorem source_arithmetic_inner_copies (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ)
    (hj : j+1≠b) : sourceArithmeticP C N b ε ell k j=
      ⌊N^(scaleA b (j+1) ε)/(sourceArithmeticLength C N b ε ell k j:ℝ)⌋₊ := by
  simp only [sourceArithmeticP,sourceArithmeticLength,sourceArithmeticStages,ite_eq_right hj]

theorem source_arithmetic_root_copies (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ)
    (hj : j+1=b) : sourceArithmeticP C N b ε ell k j=
      sourceRootTrials N (sourceArithmeticLength C N b ε ell k j) (sourceWindowSize N b ε j)
        (sourceArithmeticCount C N b ε ell k j)*
          (2*sourceArithmeticCount C N b ε ell k j+1)+sourceWindowSize N b ε j := by
  simp only [sourceArithmeticP,sourceArithmeticLength,sourceArithmeticCount,sourceArithmeticStages,ite_eq_left hj]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- All nested lengths and overlap counts for the literal floors/ceilings.
 Only the scalar subpower margin is needed for every rounding step. -/
theorem source_arithmetic_lengths {C N F ε : ℝ} {b ell k : ℕ}
    (hC : 2 ≤ C) (hN : 1 ≤ N) (hF : 1 ≤ F) (he : 0 ≤ ε)
    (ha : ∀j ≤ b,0 ≤ scaleA b j ε)
    (hsmall : 8*C^(2*b)*F ≤ N^ε)
    (hell : N^(scaleA b 0 ε)/2 ≤ (ell:ℝ)) (hell' : (ell:ℝ) ≤ N^(scaleA b 0 ε))
    (hk : ell ≤ k) (hk' : (k:ℝ) ≤ F*ell) :
    ∀j ≤ b,
      N^(scaleA b j ε)/2 ≤ (sourceArithmeticLength C N b ε ell k j:ℝ) ∧
      (sourceArithmeticLength C N b ε ell k j:ℝ) ≤ N^(scaleA b j ε) ∧
      sourceArithmeticLength C N b ε ell k j ≤ sourceArithmeticCount C N b ε ell k j ∧
      (sourceArithmeticCount C N b ε ell k j:ℝ) ≤
        C^(2*j)*F*sourceArithmeticLength C N b ε ell k j := by
  have hN0 : 0 < N := by linarith only [hN]
  have hC1 : 1 ≤ C := by linarith only [hC]
  intro j
  induction j with
  | zero =>
    intro _
    simpa only [sourceArithmeticLength,sourceArithmeticCount,sourceArithmeticStages,
      Nat.mul_zero,pow_zero,one_mul] using And.intro hell (And.intro hell' (And.intro hk hk'))
  | succ j ih =>
    intro hj
    obtain ⟨hlo,hhi,hcount,hcount'⟩ := ih (by omega)
    let S := sourceArithmeticLength C N b ε ell k j
    let H := sourceArithmeticCount C N b ε ell k j
    let P := sourceArithmeticP C N b ε ell k j
    let Fj := C^(2*j)*F
    have hFj : 1 ≤ Fj := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) hF
    have hS0 : (0:ℝ)<S := lt_of_lt_of_le (by positivity) hlo
    have hS : 1 ≤ S := by exact_mod_cast (show 0 < S from Nat.cast_pos.mp hS0)
    have hfactor : Fj ≤ C^(2*b)*F := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hC1 (by omega)) (by linarith only [hF])
    have hu : 8*Fj ≤ N^ε := (mul_le_mul_of_nonneg_left hfactor (by norm_num)).trans (by simpa only [mul_assoc] using hsmall)
    have hx : 1 ≤ N^(scaleA b j ε) := Real.one_le_rpow hN (ha j (by omega))
    have hlength : N^(scaleA b (j+1) ε)/2 ≤ ((S*P:ℕ):ℝ) ∧
        ((S*P:ℕ):ℝ) ≤ N^(scaleA b (j+1) ε) := by
      by_cases hr : j+1=b
      · have hrel : (N^(scaleA b j ε))^2*N^ε=N := by
          rw [←source_scale_target_step b j hN0,hr,scaleA_top,Real.rpow_one]
        have hmargin := source_root_margins hS hhi hFj hu hcount'
          (sourceWindowSize_le_previous (b:=b) (j:=j) hN he) hrel
        have hlen := source_root_length_bounds (Nat.pos_of_ne_zero (by omega : S≠0)) hmargin.1 hmargin.2
        have hp : P=sourceRootTrials N S (sourceWindowSize N b ε j) H*(2*H+1)+sourceWindowSize N b ε j :=
          source_arithmetic_root_copies C N b ε ell k j hr
        rw [hp,hr,scaleA_top,Real.rpow_one]
        simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hlen
      · have hstep := source_scale_target_step (ε:=ε) b j hN0
        have hX : 2*(S:ℝ) ≤ N^(scaleA b (j+1) ε) := by
          rw [hstep]
          have hu' : 2 ≤ N^ε := by linarith only [hu,hFj]
          have hxx : N^(scaleA b j ε) ≤ (N^(scaleA b j ε))^2 := by nlinarith only [hx]
          nlinarith only [hhi,hxx,mul_le_mul_of_nonneg_left hu' (sq_nonneg (N^(scaleA b j ε)))]
        have hp : P=⌊N^(scaleA b (j+1) ε)/(S:ℝ)⌋₊ :=
          source_arithmetic_inner_copies C N b ε ell k j hr
        rw [hp]
        exact source_floor_length_bounds (by omega) hX
    have hP : 1 ≤ P := by
      have hp : (0:ℝ)<(S*P:ℕ) := lt_of_lt_of_le (by positivity) hlength.1
      have hp' : 0<S*P := Nat.cast_pos.mp hp
      by_contra hp0
      have he : P=0 := by omega
      simp only [he,Nat.mul_zero,lt_self_iff_false] at hp'
    have hceil := source_ceil_count_bounds hC hFj hS hP hcount hcount'
    rw [sourceArithmeticLength_step,sourceArithmeticCount_step]
    refine ⟨hlength.1,hlength.2,hceil.1,?_⟩
    have heq : C^2*Fj=C^(2*(j+1))*F := by
      dsimp [Fj]
      rw [show 2*(j+1)=2+2*j by omega,pow_add]
      ring
    simpa only [←Nat.cast_mul,heq] using hceil.2

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_copies_bounds {X u : ℝ} {S P : ℕ} (hX : 0 < X)
    (hSlo : X/2 ≤ S) (hShi : (S:ℝ) ≤ X)
    (hlo : X^2*u/2 ≤ ((S*P:ℕ):ℝ)) (hhi : ((S*P:ℕ):ℝ) ≤ X^2*u) :
    X*u/2 ≤ (P:ℝ) ∧ (P:ℝ) ≤ 2*X*u := by
  have hp := (Nat.cast_nonneg P : (0:ℝ) ≤ P)
  have hlo' := mul_le_mul_of_nonneg_right hShi hp
  have hhi' := mul_le_mul_of_nonneg_right hSlo hp
  push_cast at hlo hhi
  constructor <;> nlinarith only [hX,hlo,hhi,hlo',hhi']

theorem source_inner_trials_scale {X u F : ℝ} {S P h : ℕ}
    (hX : 1 ≤ X) (hF : 1 ≤ F) (hu : 1200*F ≤ u)
    (hSlo : X/2 ≤ S) (hShi : (S:ℝ) ≤ X) (hhlo : S ≤ h) (hhhi : (h:ℝ) ≤ F*S)
    (hPlo : X*u/2 ≤ (P:ℝ)) (hPhi : (P:ℝ) ≤ 2*X*u) :
    u/(600*F) ≤ (sourceLocalTrials P h:ℝ) ∧ (sourceLocalTrials P h:ℝ) ≤ 2*u := by
  have hx : 0<X := by linarith only [hX]
  have hf : 0<F := by linarith only [hF]
  have hfx : 1 ≤ F*X := one_le_mul_of_one_le_of_one_le hF hX
  have hhu : (h:ℝ) ≤ F*X := hhhi.trans (mul_le_mul_of_nonneg_left hShi hf.le)
  have hhl : X ≤ 2*(h:ℝ)+1 := by exact_mod_cast (show X ≤ 2*(h:ℝ)+1 by
    have hh : (S:ℝ) ≤ h := by exact_mod_cast hhlo
    linarith only [hh,hSlo])
  have hhh : 2*(h:ℝ)+1 ≤ 3*F*X := by linarith only [hhu,hfx]
  have hlarge : (200:ℝ)*(2*h+1) ≤ P := by
    have hum := mul_le_mul_of_nonneg_left hu hx.le
    nlinarith only [hhh,hPlo,hum]
  obtain ⟨hlo,hhi⟩ := sourceLocalTrials_bounds P h hlarge
  have hd : 0 < (100:ℝ)*(2*h+1) := by positivity
  constructor
  · apply le_trans _ hlo
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<600*F) hd).mpr
    have hum := mul_le_mul_of_nonneg_left hhh (by linarith only [hu,hF] : 0 ≤ u)
    have hpm := mul_le_mul_of_nonneg_left hPlo hf.le
    nlinarith only [hum,hpm]
  · apply hhi.trans
    apply (div_le_iff₀ (by positivity : (0:ℝ)<50*(2*h+1))).mpr
    have hmm := mul_le_mul_of_nonneg_left hhl (by linarith only [hu,hF] : 0 ≤ u)
    nlinarith only [hPhi,hmm]

theorem source_root_trials_scale {X u F : ℝ} {S P h J T : ℕ}
    (hX : 1 ≤ X) (hF : 1 ≤ F) (hu : 1200*F ≤ u)
    (hSlo : X/2 ≤ S) (hShi : (S:ℝ) ≤ X) (hhlo : S ≤ h) (hhhi : (h:ℝ) ≤ F*S)
    (hPlo : X*u/2 ≤ (P:ℝ)) (hPhi : (P:ℝ) ≤ 2*X*u)
    (hT : (T:ℝ) ≤ X) (hP : P=J*(2*h+1)+T) :
    u/(600*F) ≤ (J:ℝ) ∧ (J:ℝ) ≤ 2*u := by
  have hx : 0<X := by linarith only [hX]
  have hf : 0<F := by linarith only [hF]
  have hfx : 1 ≤ F*X := one_le_mul_of_one_le_of_one_le hF hX
  have hhu : (h:ℝ) ≤ F*X := hhhi.trans (mul_le_mul_of_nonneg_left hShi hf.le)
  have hhl : X ≤ 2*(h:ℝ)+1 := by
    have hh : (S:ℝ) ≤ h := by exact_mod_cast hhlo
    linarith only [hh,hSlo]
  have hhh : 2*(h:ℝ)+1 ≤ 3*F*X := by linarith only [hhu,hfx]
  have hp : (P:ℝ)=(J:ℝ)*(2*h+1)+T := by exact_mod_cast hP
  have hj : (0:ℝ) ≤ J := Nat.cast_nonneg _
  have hupper := mul_le_mul_of_nonneg_left hhl hj
  have hlower := mul_le_mul_of_nonneg_left hhh hj
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<600*F)).mpr
    have hu' : 4 ≤ u := by linarith only [hu,hF]
    nlinarith only [hp,hT,hPlo,hlower,mul_le_mul_of_nonneg_left hu' hx.le,hx]
  · nlinarith only [hupper,hp,hPhi,(Nat.cast_nonneg T : (0:ℝ) ≤ T),hx]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem sourceOverlapConstant_ge_two {q : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) :
    2 ≤ sourceOverlapConstant q := by
  have hC := sourceOverlapConstant_pos hq.1
  have hω := initialOverlapLower_lt_eighth hq.1
  have hlarge := sourceOverlapConstant_large hq
  nlinarith only [hC,hω,hlarge]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Tiny epsilon estimates are uniform in the varying block depth. -/
theorem sourceEpsilon_power_small (B D m : ℕ) (hm : m ≤ 4*B+100) :
    (2:ℝ)^m*sourceEpsilon B D ≤ 1 := by
  have hp : (2:ℝ)^m ≤ 2^(4*B+100) := pow_le_pow_right₀ (by norm_num) hm
  have hd : (1:ℝ) ≤ (D:ℝ)+1 := by linarith only [Nat.cast_nonneg D (α:=ℝ)]
  have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ (2:ℝ)^(4*B+100) by positivity)
  unfold sourceEpsilon
  rw [mul_one_div]
  exact (div_le_one (by positivity)).mpr (hp.trans (by simpa only [mul_one] using hmul))

theorem scaleA_mono_index (b j k : ℕ) (ε : ℝ) (he : 0 ≤ ε) (hjk : j ≤ k) :
    scaleA b j ε ≤ scaleA b k ε := by
  unfold scaleA
  exact sub_le_sub_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hjk) (by linarith only [he]))
      (by positivity)) _

theorem scaleA_le_geometric (b j : ℕ) (ε : ℝ) (he : 0 ≤ ε) (hj : j ≤ b) :
    scaleA b j ε ≤ (2:ℝ)^j/2^b := by
  have hp : (2:ℝ)^j ≤ 2^b := pow_le_pow_right₀ (by norm_num) hj
  have hh := mul_le_mul_of_nonneg_left hp he
  unfold scaleA
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ (by positivity)).mpr
  simp only [add_mul]
  rw [div_mul_cancel₀ _ (by positivity : (2:ℝ)^b ≠ 0)]
  nlinarith only [hh]

theorem sourceKappa_three_epsilon (B D b j : ℕ) (hb : b ≤ B) (_hj : 1 ≤ j) (hj' : j ≤ b) :
    3*sourceEpsilon B D ≤ scaleKappa b j (sourceEpsilon B D) := by
  let ε := sourceEpsilon B D
  let X := (2:ℝ)^B
  have he : 0 < ε := sourceEpsilon_pos _ _
  have hx : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hsmall := sourceEpsilon_power_small B D (2*B+4) (by omega)
  have hsmall' : 16*X^2*ε ≤ 1 := by
    rw [show 2*B+4=B*2+4 by omega,pow_add,pow_mul] at hsmall
    norm_num only [show (2:ℝ)^4=16 by norm_num] at hsmall
    dsimp [X,ε]
    nlinarith only [hsmall]
  have hgeom := scaleA_zero_lower b B ε hb he.le
  have hmono := scaleA_mono_index b 0 (j-1) ε he.le (Nat.zero_le _)
  have hp : (2:ℝ)^j ≤ X := pow_le_pow_right₀ (by norm_num) (hj'.trans hb)
  have hprod : (3*X+4)*X*ε ≤ 1 := by
    have hxx : 0 ≤ X*(X-1) := mul_nonneg (by linarith only [hx]) (by linarith only [hx])
    have hcmp : (3*X+4)*X ≤ 16*X^2 := by nlinarith only [hxx,sq_nonneg X]
    exact (mul_le_mul_of_nonneg_right hcmp he.le).trans hsmall'
  have hq : (3*X+4)*ε ≤ 1/X := (le_div_iff₀ (by linarith only [hx])).mpr (by nlinarith only [hprod])
  have hzero : 1/X-ε ≤ scaleA b 0 ε := by
    have hh : (1/X)*(1-(X-1)*ε)=1/X-ε+ε/X := by field_simp; ring
    dsimp [X] at hh
    rw [hh] at hgeom
    exact (le_add_of_nonneg_right (div_nonneg he.le (by positivity))).trans hgeom
  have hpk := mul_le_mul_of_nonneg_right hp he.le
  unfold scaleKappa
  change 3*ε ≤ scaleA b (j-1) ε-3*(2^j-1)*ε
  nlinarith only [hzero,hmono,hq,hpk,he]

theorem sourceA_nonneg (B D b j : ℕ) (hb : b ≤ B) (hb0 : 1 ≤ b) :
    0 ≤ scaleA b j (sourceEpsilon B D) := by
  have h := sourceKappa_three_epsilon B D b 1 hb (by omega) hb0
  unfold scaleKappa at h
  norm_num only [Nat.sub_self,pow_one] at h
  have hm := scaleA_mono_index b 0 j (sourceEpsilon B D) (sourceEpsilon_pos B D).le (Nat.zero_le _)
  linarith only [h,hm,sourceEpsilon_pos B D]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem scaleA_zero_simple_lower (b : ℕ) (ε : ℝ) (he : 0 ≤ ε) :
    1/(2:ℝ)^b-ε ≤ scaleA b 0 ε := by
  unfold scaleA
  norm_num only [pow_zero,mul_one]
  exact sub_le_sub_right (div_le_div_of_nonneg_right (by linarith only [he]) (by positivity)) _

theorem totalScoreExponent_step (B i : ℕ) :
    totalScoreExponent B (i+1)=totalScoreExponent B i+blockGain (sourceDimension B i) := by
  unfold totalScoreExponent sourceDimension
  rw [Finset.sum_range_succ]
  ring

theorem totalScoreExponent_after_warmup (B i : ℕ) (hB : 2 ≤ B) (hi : warmupBlocks B ≤ i) :
    (2:ℝ)^B+11/5 ≤ totalScoreExponent B i := by
  rw [totalScoreExponent_exact B i hi]
  have hm : (0:ℝ) ≤ ((i:ℝ)-warmupBlocks B)*blockGain B :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hi)) (blockGain_pos B hB).le
  unfold warmupBlocks at *
  push_cast at *
  linarith only [hm]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact layout inequalities for the literal recursive integer construction.
 The hypotheses are just two scalar subpower margins and the exact scale
 identities, not any probabilistic producer or new overlap premise. -/
theorem source_arithmetic_geometry {C N F ε : ℝ} {s b ell k : ℕ}
    (hC : 2 ≤ C) (hN : 1 ≤ N) (hF : 1 ≤ F) (he : 0 ≤ ε)
    (ha : ∀j ≤ b,0 ≤ scaleA b j ε) (hκ : ∀j<b,3*ε ≤ scaleKappa b (j+1) ε)
    (hsmall : 1200*C^(2*b)*F ≤ N^ε) (hmotif : 48*((2^s:ℕ):ℝ) ≤ N^ε)
    (hell : N^(scaleA b 0 ε)/2 ≤ (ell:ℝ)) (hell' : (ell:ℝ) ≤ N^(scaleA b 0 ε))
    (hk : ell ≤ k) (hk' : (k:ℝ) ≤ F*ell) :
    SourceArithmeticBounds C N F ε s b ell k := by
  let G := C^(2*b)*F
  let u := N^ε
  have hC1 : 1 ≤ C := by linarith only [hC]
  have hN0 : 0 < N := by linarith only [hN]
  have hG : 1 ≤ G := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) hF
  have hG0 : 0 < G := by linarith only [hG]
  have hu : 1200*G ≤ u := by simpa only [G,u,mul_assoc] using hsmall
  have hu8 : 8 ≤ u := by linarith only [hu,hG]
  have H := source_arithmetic_lengths hC hN hF he ha
    (show 8*C^(2*b)*F ≤ N^ε by
      have hh : 8*G ≤ u := by linarith only [hu,hG]
      simpa only [G,u,mul_assoc] using hh) hell hell' hk hk'
  have hcopies (j : ℕ) (hj : j<b) :
      N^(scaleA b j ε)*u/2 ≤ (sourceArithmeticP C N b ε ell k j:ℝ) ∧
      (sourceArithmeticP C N b ε ell k j:ℝ) ≤ 2*N^(scaleA b j ε)*u := by
    have hlen := H j (by omega)
    have hnext := H (j+1) (by omega)
    rw [source_scale_target_step b j hN0,sourceArithmeticLength_step] at hnext
    exact source_copies_bounds (Real.rpow_pos_of_pos hN0 _) hlen.1 hlen.2.1 hnext.1 hnext.2.1
  have htrials (j : ℕ) (hj : j<b) :
      u/(600*G) ≤ (sourceArithmeticTrials C N b ε ell k j:ℝ) ∧
      (sourceArithmeticTrials C N b ε ell k j:ℝ) ≤ 2*u := by
    have hlen := H j (by omega)
    have hcp := hcopies j hj
    have hX : 1 ≤ N^(scaleA b j ε) := Real.one_le_rpow hN (ha j (by omega))
    have hcount : (sourceArithmeticCount C N b ε ell k j:ℝ) ≤
        G*sourceArithmeticLength C N b ε ell k j := by
      apply hlen.2.2.2.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1 (by omega)) (by linarith only [hF])
    by_cases hjroot : j+1=b
    · have hp : sourceArithmeticP C N b ε ell k j=
          sourceArithmeticTrials C N b ε ell k j*(2*sourceArithmeticCount C N b ε ell k j+1)+
            sourceWindowSize N b ε j := by
        simp only [sourceArithmeticP,sourceArithmeticTrials,sourceArithmeticCount,sourceArithmeticStages,ite_eq_left hjroot]
      exact source_root_trials_scale hX hG hu hlen.1 hlen.2.1 hlen.2.2.1 hcount hcp.1 hcp.2
        (sourceWindowSize_le_previous hN he) hp
    · rw [sourceArithmetic_inner_trials C N b ε ell k j hjroot]
      exact source_inner_trials_scale hX hG hu hlen.1 hlen.2.1 hlen.2.2.1 hcount hcp.1 hcp.2
  refine ⟨fun j hj => ⟨(H j hj).1,(H j hj).2.1⟩,fun j hj => (H j hj).2.2,hcopies,htrials,?_⟩
  intro j hj
  rw [sourceBlockWindows,ite_eq_left hj]
  have hp := hcopies j hj
  have ht := htrials j hj
  have hu3 : u^3 ≤ N^(scaleKappa b (j+1) ε) := by
    dsimp [u]
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    norm_num only [Nat.cast_ofNat]
    apply Real.rpow_le_rpow_of_exponent_le hN
    linarith only [hκ j hj]
  have hu32 : 64*u ≤ u^3 := by
    have hu_sq : 64 ≤ u^2 := by nlinarith only [hu8,sq_nonneg (u-8)]
    nlinarith only [mul_le_mul_of_nonneg_right hu_sq (by linarith only [hu8] : 0 ≤ u)]
  have hw := sourceWindowSize_bounds (show 8 ≤ N^(scaleKappa b (j+1) ε) by linarith only [hu32,hu8,hu3])
  have hwbig : u^3/2 ≤ (sourceWindowSize N b ε j:ℝ) := le_trans (by linarith only [hu3] : u^3/2 ≤ N^(scaleKappa b (j+1) ε)/2) hw.1
  have hwp := sourceWindowSize_le_previous (b:=b) (j:=j) hN he
  have hX : 0 ≤ N^(scaleA b j ε) := (Real.rpow_pos_of_pos hN0 _).le
  have hambient : (2:ℝ)*(sourceWindowSize N b ε j:ℝ) ≤ sourceArithmeticP C N b ε ell k j := by
    have hh := mul_le_mul_of_nonneg_right hu8 hX
    nlinarith only [hp.1,hwp,hh]
  have h24 : (24:ℝ) ≤ sourceWindowSize N b ε j := by linarith only [hwbig,hu32,hu8]
  have hmot : (24:ℝ)*((2^s:ℕ):ℝ) ≤ sourceWindowSize N b ε j := by
    have hu' : 48*((2^s:ℕ):ℝ) ≤ u := hmotif
    linarith only [hwbig,hu32,hu']
  have hroot : (4:ℝ)*((sourceArithmeticTrials C N b ε ell k j:ℝ)+1) ≤ sourceWindowSize N b ε j := by
    linarith only [hwbig,hu32,hu8,ht.2]
  exact ⟨by exact_mod_cast h24,by exact_mod_cast hmot,by exact_mod_cast hambient,by exact_mod_cast hroot⟩

end TraceReconstruction


end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_ErrorRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# ErrorRates

Realization of block caps, sparse scales, sharp and smoothing budgets, tree tails, fit errors, and uniform polynomial/exponential bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceArithmeticLength_eq_block (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ) :
    sourceArithmeticLength C N b ε ell k j=
      sourceBlockLength (sourceArithmeticP C N b ε ell k) ell j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [sourceArithmeticLength_step,sourceBlockLength,ih,mul_comm]

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem sourceCapEnvelope_pos (B D : ℕ) {q : ℝ} (hq : 0<q) : 0 < sourceCapEnvelope B D q := by
  unfold sourceCapEnvelope
  positivity [sourceOverlapConstant_pos hq,initialOverlapLower_pos q]

end TraceReconstruction


end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Propagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Propagation

Moment restriction, scale margins, sharp budget closure, clipping and error propagation, and dense/warmup overlap.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceScaleProduct_step_le (B D i : ℕ) (hB : 2≤B) (hi : i<D) :
    sourceScaleProduct B D i ≤ sourceScaleProduct B D (i+1) := by
  have he := sourceEpsilon_pos B D
  have hp : (1:ℝ)≤2^(sourceDimension B i) := one_le_pow₀ (by norm_num)
  have ha : scaleA (sourceDimension B i) 0 (sourceEpsilon B D)≤1 := by
    unfold scaleA
    norm_num only [pow_zero,mul_one]
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<2^(sourceDimension B i))).mpr
      (le_mul_of_one_le_right (by linarith only [he] : 0≤1+sourceEpsilon B D) hp)
    linarith only [hh]
  have hs : 0 ≤ sourceScaleProduct B D (i+1) := (lt_of_lt_of_le (by positivity) (sourceScaleProduct_lower B D (i+1) hB)).le
  have hh := mul_le_mul_of_nonneg_right ha hs
  unfold sourceScaleProduct at *
  rw [Finset.prod_eq_prod_Ico_succ_bot hi]
  simpa only [one_mul] using hh

theorem sourceHalfMoment_step (B D i : ℕ) {n : ℝ} (hB : 2≤B) (hi : i<D) (hn : 1<n) :
    sourceHalfMoment B D n (i+1) ≤ sourceHalfMoment B D n i := by
  have hlog : 0<Real.log (sourceTargetScale B D n i) := by
    rw [sourceTargetScale,Real.log_rpow (by linarith only [hn] : 0<n)]
    exact mul_pos (lt_of_lt_of_le (by positivity) (sourceScaleProduct_lower B D i hB)) (Real.log_pos hn)
  have hlog' : Real.log (sourceTargetScale B D n i) ≤ Real.log (sourceTargetScale B D n (i+1)) := by
    rw [sourceTargetScale,sourceTargetScale,Real.log_rpow (by linarith only [hn] : 0<n),Real.log_rpow (by linarith only [hn] : 0<n)]
    exact mul_le_mul_of_nonneg_right (sourceScaleProduct_step_le B D i hB hi) (Real.log_pos hn).le
  unfold sourceHalfMoment
  apply Nat.ceil_mono
  have hd := (totalScoreExponent_bounds B D hB).1
  have hl := (Real.log_pos hn).le
  exact div_le_div_of_nonneg_left (by positivity) hlog hlog'

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceGapFloor_le_one (B : ℕ) : sourceGapFloor B≤1 := by
  unfold sourceGapFloor
  apply (div_le_one (by positivity)).mpr
  have hh : (1:ℝ)≤2^(2*B) := one_le_pow₀ (by norm_num)
  linarith only [hh]

theorem sourceEpsilon_gap_small (B D : ℕ) : 1000*sourceEpsilon B D ≤ sourceGapFloor B := by
  have hp : (1000:ℝ)*128*2^(2*B) ≤ 2^(4*B+100) := by
    have hpow : (2:ℝ)^(2*B+17) ≤ 2^(4*B+100) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_add] at hpow
    norm_num only [show (2:ℝ)^17=131072 by norm_num] at hpow
    have hpos : 0≤(2:ℝ)^(2*B) := by positivity
    linarith only [hpow,hpos]
  have hd : 1≤(D:ℝ)+1 := by linarith [Nat.cast_nonneg D (α:=ℝ)]
  have hh := mul_le_mul_of_nonneg_left hd (show 0≤(2:ℝ)^(4*B+100) by positivity)
  unfold sourceEpsilon sourceGapFloor
  rw [←mul_div_assoc, mul_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hp,hh]

end TraceReconstruction

noncomputable section

noncomputable section

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceDimension_bounds (B i : ℕ) (hB : 2≤ B) :
    2≤ sourceDimension B i ∧ sourceDimension B i≤ B := by
  unfold sourceDimension
  split_ifs <;> omega

theorem totalScoreExponent_mono (B : ℕ) (hB : 2≤ B) : Monotone (totalScoreExponent B) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [totalScoreExponent_step]
  exact le_add_of_nonneg_right (blockGain_pos _ (sourceDimension_bounds B i hB).1).le

theorem sourceTargetScale_bounds (B D i : ℕ) {n : ℝ} (hB : 2≤ B) (hn : 1≤ n) :
    1≤ sourceTargetScale B D n i ∧ sourceTargetScale B D n i≤ n := by
  have hp : 0≤ sourceScaleProduct B D i :=
    (show (0:ℝ)≤1/(2*2^(B*D)) by positivity).trans (sourceScaleProduct_lower B D i hB)
  refine ⟨Real.one_le_rpow hn hp,?_⟩
  simpa only [sourceTargetScale,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn (sourceScaleProduct_le_one B D i hB)

theorem source_warmup_score_margin (B D : ℕ) {d : ℝ} (hB : 2≤ B)
    (hd : 11/5≤ d) (hd' : d≤3+(B:ℝ)*D) :
    27/50≤ scaleA 2 0 (sourceEpsilon B D)*d ∧ scaleA 2 1 (sourceEpsilon B D)≤1/2 := by
  have he := sourceEpsilon_pos B D
  have hloss := sourceEpsilon_loss B D 2 d hB (by linarith only [hd]) hd'
  norm_num only [show (2:ℝ)^2=4 by norm_num,Nat.cast_ofNat] at hloss
  have hlo := mul_le_mul_of_nonneg_right (scaleA_zero_simple_lower 2 (sourceEpsilon B D) he.le)
    (show 0≤ d by linarith only [hd])
  norm_num only [show (2:ℝ)^2=4 by norm_num] at hlo
  constructor
  · nlinarith only [hloss,hlo,hd,he]
  · have hh := scaleA_le_geometric 2 1 (sourceEpsilon B D) he.le (by omega)
    norm_num at hh ⊢
    exact hh

theorem source_main_score_margin (B D : ℕ) {d : ℝ} (hB : 2≤ B)
    (hd : (2:ℝ)^B+2≤ d) (hd' : d≤3+(B:ℝ)*D) :
    1+1/(2:ℝ)^B ≤ scaleA B 0 (sourceEpsilon B D)*d := by
  let X := (2:ℝ)^B
  let ε := sourceEpsilon B D
  have hX : 4≤ X := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hB
    norm_num at hh
    exact hh
  have hX0 : 0< X := by linarith only [hX]
  have he : 0<ε := sourceEpsilon_pos _ _
  have hd0 : 0≤ d := by dsimp [X] at hX; linarith only [hd,hX]
  have hloss := sourceEpsilon_loss B D B d le_rfl hd0 hd'
  change ((X-1)*d+3*B*(X/2))*ε<1/100 at hloss
  have hnonneg : 0≤3*(B:ℝ)*(X/2)*ε := by positivity
  have hde : 0≤ d*ε := mul_nonneg hd0 he.le
  have hmul : X*d*ε≤1/50 := by
    have hxx : 0≤(X-2)*(d*ε) := mul_nonneg (by linarith only [hX]) hde
    nlinarith only [hloss,hnonneg,hxx]
  have hlo := mul_le_mul_of_nonneg_right (scaleA_zero_simple_lower B ε he.le) hd0
  change (1/X-ε)*d≤ scaleA B 0 ε*d at hlo
  have hgoal : 1+1/X≤(1/X-ε)*d := by
    apply (mul_le_mul_iff_left₀ hX0).mp
    field_simp
    change X+2 ≤ d at hd
    nlinarith only [hd,hmul]
  exact hgoal.trans hlo

end TraceReconstruction

noncomputable section

noncomputable section
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem sourceWeightEnvelope_nonneg (B D : ℕ) : 0 ≤ sourceWeightEnvelope B D := by
  unfold sourceWeightEnvelope
  exact mul_nonneg (by norm_num) (sq_nonneg _)

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_count_envelope (B D i b : ℕ) {q : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hi : i≤ D) (hb : b≤ B) :
    (sourceOverlapConstant q)^(2*b)*(sourceOverlapConstant q)^(2*B*i+2) ≤
      (sourceOverlapConstant q)^(2*B*(D+1)+2) := by
  rw [←pow_add]
  apply pow_le_pow_right₀ ((by norm_num : (1:ℝ)≤ 2).trans (sourceOverlapConstant_ge_two hq))
  have hh := Nat.mul_le_mul_left (2*B) hi
  nlinarith only [hh,hb]

theorem source_cap_envelope (B D i b : ℕ) {q : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hi : i≤ D) (hb : b≤ B) :
    200*((sourceOverlapConstant q)^(2*b)*(sourceOverlapConstant q)^(2*B*i+2))/initialOverlapLower q ≤
      sourceCapEnvelope B D q := by
  dsimp [sourceCapEnvelope]
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (source_count_envelope B D i b hq hi hb)
    (by norm_num)) (inv_pos.mpr (initialOverlapLower_pos q)).le

theorem source_local_envelope (B D i b : ℕ) {q : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hi : i≤ D) (hb : b≤ B) :
    (sourceOverlapConstant q)^(2*b)*(sourceOverlapConstant q)^(2*B*i+2) ≤
      sourceCapEnvelope B D q := by
  have hω := initialOverlapLower_lt_eighth hq.1
  have hω0 := initialOverlapLower_pos q
  have hG : 0 ≤ (sourceOverlapConstant q)^(2*b)*(sourceOverlapConstant q)^(2*B*i+2) := by
    positivity [sourceOverlapConstant_pos hq.1]
  apply le_trans _ (source_cap_envelope B D i b hq hi hb)
  apply (le_div_iff₀ hω0).mpr
  nlinarith only [hω,hG,mul_nonneg hG (show 0 ≤ 200-initialOverlapLower q by linarith only [hω])]

theorem SourceArithmeticBounds.count_bound {C N F ε : ℝ} {s b ell k j : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hC : 1≤ C) (hF : 0≤ F) (hN : 1≤ N)
    (hj : j≤ b) (ha : 0≤ scaleA b j ε) :
    ((sourceArithmeticCount C N b ε ell k j+1:ℕ):ℝ) ≤
      (C^(2*b)*F+1)*N^(scaleA b j ε) := by
  have hc := (H.counts j hj).2
  have hc' : (sourceArithmeticCount C N b ε ell k j:ℝ) ≤
      (C^(2*b)*F)*N^(scaleA b j ε) := by
    apply hc.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC (by omega)) hF)
      (H.lengths j hj).2 (by positivity) (by positivity)
  have ho := Real.one_le_rpow hN ha
  push_cast
  nlinarith only [hc',ho]

end TraceReconstruction
noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem rpow_constant_absorb {N ε e c M : ℝ} (hN : 1 ≤ N) (hM : 0<M)
    (hc : M*c ≤ N^ε) (he : ε+e ≤ 0) : c*N^e ≤ 1/M := by
  have hN0 : 0<N := by linarith only [hN]
  have hh := mul_le_mul_of_nonneg_right hc (Real.rpow_pos_of_pos hN0 e).le
  rw [←Real.rpow_add hN0] at hh
  have hr := Real.rpow_le_rpow_of_exponent_le hN he
  rw [Real.rpow_zero] at hr
  apply (le_div_iff₀ hM).mpr
  nlinarith only [hh,hr]

theorem overlap_sqrt_budget {v e : ℝ} (hv : v ≤ 1/4096) (he : e ≤ 1/8) :
    Real.sqrt v+e ≤ 1/4 := by
  have hh : Real.sqrt v ≤ 1/64 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num at hv ⊢; exact hv)
  linarith only [hh,he]

/-- Generic dense-template estimate, used for the first warmup step and
 every step of a post-warmup block. -/
theorem source_dense_variance_budget {N ε e a K L V h : ℝ} {j : ℕ}
    (hN : 1 ≤ N) (_hK : 0 ≤ K) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hcount : h ≤ (K+1)*N^a) (hV : V ≤ N^(-e))
    (hc : 4096*(K+1)*L^j ≤ N^ε) (he : ε+a ≤ e) :
    h*(L^j*V) ≤ 1/4096 := by
  have hN0 : 0<N := by linarith only [hN]
  have hv := mul_le_mul_of_nonneg_left hV (show 0 ≤ h*L^j by positivity)
  have ht := mul_le_mul_of_nonneg_right hcount (show 0 ≤ L^j*N^(-e) by positivity)
  have heq : ((K+1)*N^a)*(L^j*N^(-e))=((K+1)*L^j)*N^(a-e) := by
    rw [sub_eq_add_neg,Real.rpow_add hN0]
    ring
  rw [heq] at ht
  have hb := rpow_constant_absorb hN (M:=4096) (by norm_num)
    (c:=(K+1)*L^j) (by nlinarith only [hc]) (e:=a-e) (by linarith only [he])
  nlinarith only [hv,ht,hb]

theorem sourceBlockLength_factor (P : ℕ→ℕ) (ell j : ℕ) :
    sourceBlockLength P ell j=ell*sourceBlockLength P 1 j := by
  induction j with
  | zero => simp only [sourceBlockLength,mul_one]
  | succ j ih => rw [sourceBlockLength,sourceBlockLength,ih]; ring

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_delta_power_budget {B D : ℕ} {n N ε : ℝ} (hB : 2 ≤ B)
    (hn : 1 ≤ n) (hN : 1 ≤ N) (hNn : N ≤ n) (he : 0 ≤ ε) (he1 : ε ≤ 1) :
    n^(-100*(totalScoreExponent B D+B+1))*N^(2+ε) ≤ 1 := by
  have hn0 : 0<n := by linarith only [hn]
  have hN0 : 0<N := by linarith only [hN]
  have hA : 1 ≤ totalScoreExponent B D+B+1 := by
    linarith only [(totalScoreExponent_bounds B D hB).1,Nat.cast_nonneg B (α:=ℝ)]
  apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN0.le hNn (by linarith only [he]))
    (Real.rpow_pos_of_pos hn0 (-100*(totalScoreExponent B D+B+1))).le).trans
  rw [←Real.rpow_add hn0]
  simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hn
    (show -100*(totalScoreExponent B D+B+1)+(2+ε) ≤ 0 by linarith only [hA,he1])

/-- Uniform repeated old simulation error; this is the error term in every
 dense nested-overlap estimate. -/
theorem source_repeated_error_budget {n N ε K E t h : ℝ} {B D : ℕ}
    (hB : 2 ≤ B) (hn : 1 ≤ n) (hN : 1 ≤ N) (hNn : N ≤ n)
    (he : 0 ≤ ε) (he1 : ε ≤ 1) (hh : 0 ≤ h) (_hK : 0 ≤ K)
    (hcount : h ≤ (K+1)*N)
    (hcost : t*E ≤ ((D:ℝ)+1)*n^(-100*(totalScoreExponent B D+B+1))*N)
    (hmargin : 64*(K+1)*((D:ℝ)+1) ≤ N^ε) : 2*h*(t*E) ≤ 1/32 := by
  let Δ := n^(-100*(totalScoreExponent B D+B+1))
  have hn0 : 0<n := by linarith only [hn]
  have hΔ : 0 ≤ Δ := (Real.rpow_pos_of_pos hn0 _).le
  have hc := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 2*h by positivity)
  have ht := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 2*((D:ℝ)+1)*Δ*N by positivity)
  have hm := mul_le_mul_of_nonneg_right hmargin (show 0 ≤ Δ*N^2 by positivity)
  have hp := source_delta_power_budget (D:=D) hB hn hN hNn he he1
  have hl : N^ε*N^2=N^(2+ε) := by
    rw [←Real.rpow_natCast,←Real.rpow_add (by linarith only [hN] : 0<N)]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hm' : 64*(K+1)*((D:ℝ)+1)*Δ*N^2 ≤ Δ*N^(2+ε) := by
    calc
      _ = (64*(K+1)*((D:ℝ)+1))*(Δ*N^2) := by ring
      _ ≤ N^ε*(Δ*N^2) := hm
      _ = _ := by rw [show N^ε*(Δ*N^2)=Δ*(N^ε*N^2) by ring,hl]
  change Δ*N^(2+ε) ≤ 1 at hp
  nlinarith only [hc,ht,hm',hp]

theorem source_old_error_cost {C N F ε E Δ : ℝ} {s b ell k j i D : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 1 ≤ N)
    (hE : E ≤ ((i:ℝ)+1)*Δ*ell) (hΔ : 0 ≤ Δ) (hi : i ≤ D) (hj : j ≤ b)
    (ha : scaleA b j ε ≤ 1) :
    (sourceBlockLength (sourceArithmeticP C N b ε ell k) 1 j:ℝ)*E ≤
      ((D:ℝ)+1)*Δ*N := by
  let t := sourceBlockLength (sourceArithmeticP C N b ε ell k) 1 j
  have hh := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg t (α:=ℝ))
  have hl : (ell:ℝ)*t ≤ N := by
    have hl' := (H.lengths j hj).2
    rw [sourceArithmeticLength_eq_block,sourceBlockLength_factor] at hl'
    push_cast at hl'
    exact hl'.trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN ha)
  have hi' : (i:ℝ) ≤ D := by exact_mod_cast hi
  have hh' := mul_le_mul_of_nonneg_left hl (show 0 ≤ ((D:ℝ)+1)*Δ by positivity)
  have hcoef := mul_le_mul_of_nonneg_right hi' (show 0 ≤ Δ*(ell:ℝ)*t by positivity)
  dsimp [t] at *
  nlinarith only [hh,hh',hcoef]

end TraceReconstruction
noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_overlap_prefactors {K W L X : ℝ} {B j : ℕ}
    (hK : 0 ≤ K) (hW : 0 ≤ W) (hL : 1 ≤ L) (hB : 2 ≤ B) (hj : j ≤ B+2)
    (hX : 1099511627776*(K+1)*(W+1)^2*L^(B+2) ≤ X) :
    4096*(K+1)*L^j ≤ X ∧
    8192*(4608*(K+1)*L*W) ≤ X ∧
    8192*(512*(K+1)*W^2*L^3) ≤ X := by
  have hK1 : 0 ≤ K+1 := by linarith only [hK]
  have hw1 : 1 ≤ (W+1)^2 := by nlinarith only [hW,sq_nonneg W]
  have hww : W ≤ (W+1)^2 := by nlinarith only [hW,sq_nonneg W]
  have hw2 : W^2 ≤ (W+1)^2 := by nlinarith only [hW]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hjpow := pow_le_pow_right₀ hL hj
  have hlpow : L ≤ L^(B+2) := by simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ B+2 by omega)
  have h3pow := pow_le_pow_right₀ hL (show 3 ≤ B+2 by omega)
  have hb0 : 0 ≤ (K+1)*(W+1)^2*L^(B+2) := by positivity
  have hfirst : (K+1)*L^j ≤ (K+1)*(W+1)^2*L^(B+2) := by
    have hp := mul_le_mul_of_nonneg_left hjpow hK1
    have hp' := mul_le_mul_of_nonneg_right hw1 (show 0 ≤ (K+1)*L^(B+2) by positivity)
    nlinarith only [hp,hp']
  have hsecond : (K+1)*L*W ≤ (K+1)*(W+1)^2*L^(B+2) := by
    have hp := mul_le_mul_of_nonneg_left (mul_le_mul hlpow hww hW (by positivity)) hK1
    nlinarith only [hp]
  have hthird : (K+1)*W^2*L^3 ≤ (K+1)*(W+1)^2*L^(B+2) := by
    have hp := mul_le_mul_of_nonneg_left (mul_le_mul hw2 h3pow (by positivity) (by positivity)) hK1
    nlinarith only [hp]
  constructor
  · nlinarith only [hfirst,hX,hb0]
  constructor <;> nlinarith only [hsecond,hthird,hX,hb0]

/-- Complete dense-overlap numerical criterion for the literal schedules,
 including the error carried by the old exact simulator. -/
theorem source_literal_dense_overlap {C N F ε E Δ V K W L n e : ℝ}
    {s b ell k j i D B : ℕ} (H : SourceArithmeticBounds C N F ε s b ell k)
    (hB : 2 ≤ B) (hb : b ≤ B) (hC : 1 ≤ C) (hF : 0 ≤ F)
    (hn : 1 ≤ n) (hN : 1 ≤ N) (hNn : N ≤ n) (he : 0 ≤ ε) (he1 : ε ≤ 1)
    (hK : 0 ≤ K) (hW : 0 ≤ W) (hL : 1 ≤ L) (hLdef : L=(2:ℝ)^s)
    (hG : C^(2*b)*F ≤ K) (hi : i ≤ D) (hj : j ≤ b)
    (ha : 0 ≤ scaleA b j ε) (ha1 : scaleA b j ε ≤ 1)
    (hE : E ≤ ((i:ℝ)+1)*Δ*ell) (hΔ : Δ=n^(-100*(totalScoreExponent B D+B+1)))
    (hV : V ≤ N^(-e)) (hgap : ε+scaleA b j ε ≤ e)
    (hmargin : 64*(K+1)*((D:ℝ)+1) ≤ N^ε)
    (hoverlap : 1099511627776*(K+1)*(W+1)^2*L^(B+2) ≤ N^ε) :
    Real.sqrt (((sourceArithmeticCount C N b ε ell k j+1:ℕ):ℝ)*
      (((2^s:ℕ):ℝ)^j*V))+
      2*((sourceArithmeticCount C N b ε ell k j+1:ℕ):ℝ)*
      ((sourceBlockLength (sourceArithmeticP C N b ε ell k) 1 j:ℝ)*E) ≤ 1/4 := by
  let h := ((sourceArithmeticCount C N b ε ell k j+1:ℕ):ℝ)
  have hn0 : 0<n := by linarith only [hn]
  have hN0 : 0<N := by linarith only [hN]
  have hh0 : 0 ≤ h := Nat.cast_nonneg _
  have hc : h ≤ (K+1)*N^(scaleA b j ε) := by
    exact (H.count_bound hC hF hN hj ha).trans
      (mul_le_mul_of_nonneg_right (add_le_add hG le_rfl) (Real.rpow_pos_of_pos hN0 _).le)
  have hc' : h ≤ (K+1)*N := hc.trans (mul_le_mul_of_nonneg_left
    (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN ha1)
    (by linarith only [hK]))
  have hpref := (source_overlap_prefactors hK hW hL hB (show j ≤ B+2 by omega) hoverlap).1
  have hv := source_dense_variance_budget hN hK (show 0 ≤ L by linarith only [hL]) hh0 hc hV hpref hgap
  have hcost := source_old_error_cost H hN hE (by rw [hΔ]; exact (Real.rpow_pos_of_pos hn0 _).le) hi hj ha1
  rw [hΔ] at hcost
  have herr := source_repeated_error_budget hB hn hN hNn he he1 hh0 hK hc' hcost hmargin
  have hres := overlap_sqrt_budget hv (show 2*h*((sourceBlockLength (sourceArithmeticP C N b ε ell k) 1 j:ℝ)*E) ≤ 1/8 by linarith only [herr])
  simpa only [hLdef,Nat.cast_pow,Nat.cast_ofNat] using hres

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem SourceArithmeticBounds.length_positive {C N F ε : ℝ} {s b ell k j : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0<N) (hj : j ≤ b) :
    1 ≤ sourceArithmeticLength C N b ε ell k j := by
  have hp : (0:ℝ) < sourceArithmeticLength C N b ε ell k j :=
    (show 0<N^(scaleA b j ε)/2 by positivity).trans_le (H.lengths j hj).1
  have hh : 0 < sourceArithmeticLength C N b ε ell k j := by exact_mod_cast hp
  omega

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Induction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Induction

Concrete level invariants, metadata prefixes, score/error budgets, overlap, the induction step, and the complete construction.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_level_geometry {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D)
    (hn : 1 ≤ n) (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1))) :
    SourceArithmeticBounds (sourceOverlapConstant q) (sourceTargetScale B D n (i+1))
      ((sourceOverlapConstant q)^(2*B*i+2)) (sourceEpsilon B D)
      (sourceCancellationOrder B D) (sourceDimension B i) U.left.length U.overlapCount := by
  let N := sourceTargetScale B D n (i+1)
  let b := sourceDimension B i
  let C := sourceOverlapConstant q
  have hC : 2 ≤ C := sourceOverlapConstant_ge_two hq'
  have hb := sourceDimension_bounds B i hB
  have hN := (sourceTargetScale_bounds B D (i+1) hB hn).1
  have he := sourceEpsilon_pos B D
  have hG := source_local_envelope B D i b hq' (Nat.le_of_lt hi) hb.2
  apply source_arithmetic_geometry hC hN (one_le_pow₀ (by linarith only [hC])) he.le
    (fun j _=>sourceA_nonneg B D b j hb.2 (by omega))
    (fun j hj=>sourceKappa_three_epsilon B D b (j+1) hb.2 (by omega) (by omega))
  · have hh := mul_le_mul_of_nonneg_left hG (show (0:ℝ) ≤ 1200 by norm_num)
    exact (by nlinarith only [hh] : 1200*C^(2*b)*C^(2*B*i+2) ≤ 1200*sourceCapEnvelope B D q).trans H.geometry
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using H.motif
  · simpa only [sourceTargetScale_step B D i n (by linarith only [hn]) hi] using U.length_lower
  · simpa only [sourceTargetScale_step B D i n (by linarith only [hn]) hi] using U.length_upper
  · exact U.overlapCount_lower
  · exact U.overlapCount_upper

theorem SourceArithmeticBounds.copies_positive {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0<N) {j : ℕ} (hj : j<b) :
    1 ≤ sourceArithmeticP C N b ε ell k j := by
  have hh := (H.copies j hj).1
  have hp : (0:ℝ)<N^(scaleA b j ε)*N^ε/2 := by positivity
  have hp' : (0:ℝ) < sourceArithmeticP C N b ε ell k j := hp.trans_le hh
  have hp'' : 0 < sourceArithmeticP C N b ε ell k j := by exact_mod_cast hp'
  omega

theorem source_level_exponent_margins (B D i : ℕ) (hB : 2 ≤ B) (hi : i ≤ D) :
    let ε := sourceEpsilon B D
    let b := sourceDimension B i
    let e := scaleA b 0 ε*totalScoreExponent B i
    (i<warmupBlocks B → b=2 ∧ 27/50 ≤ e ∧ ε+scaleA b 1 ε ≤ e ∧ ε+1-2*e ≤ 0) ∧
    (warmupBlocks B ≤ i → ∀j ≤ b,ε+scaleA b j ε ≤ e) := by
  let ε := sourceEpsilon B D
  have he := sourceEpsilon_pos B D
  have he1 : ε ≤ 1/100 := by
    have hh := sourceEpsilon_gap_small B D
    have hg := sourceGapFloor_le_one B
    dsimp [ε]
    linarith only [hh,hg]
  have hd := (totalScoreExponent_bounds B i hB).1
  have hd' : totalScoreExponent B i ≤ 3+(B:ℝ)*D := by
    simpa only [mul_comm] using (totalScoreExponent_mono B hB hi).trans (totalScoreExponent_bounds B D hB).2
  constructor
  · intro hw
    have hb : sourceDimension B i=2 := ite_eq_left hw
    have hh := source_warmup_score_margin B D hB hd hd'
    simp only [hb]
    exact ⟨True.intro,hh.1,by linarith only [hh.1,hh.2,he1],by linarith only [hh.1,he1]⟩
  · intro hw j hj
    have hb : sourceDimension B i=B := ite_eq_right (by omega)
    rw [hb] at hj ⊢
    have hlarge := totalScoreExponent_after_warmup B i hB hw
    have hh := source_main_score_margin B D hB (by linarith only [hlarge]) hd'
    have ha : scaleA B j ε ≤ 1 := by
      exact (scaleA_mono_index B j B ε he.le hj).trans (by rw [scaleA_top])
    have heps : ε ≤ 1/(2:ℝ)^B := by
      have hs := sourceEpsilon_small B D
      have hm := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ D+1 by have : 0 ≤ (D:ℝ) := Nat.cast_nonneg D; linarith only [this]) (show 0 ≤ (2:ℝ)^B*ε by positivity)
      apply (le_div_iff₀ (by positivity)).mpr
      dsimp [ε] at *
      nlinarith only [hs,hm]
    linarith only [hh,ha,heps]

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_old_variance_scale (B D i : ℕ) {n : ℝ} (hn : 0<n) (hi : i<D) :
    (sourceTargetScale B D n i)^(-totalScoreExponent B i)=
      (sourceTargetScale B D n (i+1))^(-scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i) := by
  rw [sourceTargetScale_step B D i n hn.le hi,←Real.rpow_mul (show 0 ≤ sourceTargetScale B D n (i+1) from (Real.rpow_pos_of_pos hn _).le)]
  congr 1
  ring

theorem source_old_variance_square (B D i : ℕ) {n : ℝ} (hn : 0<n) (hi : i<D) :
    (sourceTargetScale B D n i)^(-totalScoreExponent B i)=
      ((sourceTargetScale B D n (i+1))^(-scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i/2))^2 := by
  rw [source_old_variance_scale B D i hn hi,←Real.rpow_natCast,←Real.rpow_mul (show 0 ≤ sourceTargetScale B D n (i+1) from (Real.rpow_pos_of_pos hn _).le)]
  congr 1
  norm_num

theorem source_level_dense_overlap {B D i j : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
    (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
    (hj : j ≤ sourceDimension B i)
    (hgap : sourceEpsilon B D+scaleA (sourceDimension B i) j (sourceEpsilon B D) ≤
      scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i) :
    let N := sourceTargetScale B D n (i+1)
    let b := sourceDimension B i
    let ε := sourceEpsilon B D
    let s := sourceCancellationOrder B D
    let P := sourceArithmeticP (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    let h := sourceArithmeticCount (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    Real.sqrt (((h j+1:ℕ):ℝ)*(((2^s:ℕ):ℝ)^j*(sourceTargetScale B D n i)^(-totalScoreExponent B i)))+
      2*((h j+1:ℕ):ℝ)*((sourceBlockLength P 1 j:ℝ)*U.error) ≤ 1/4 := by
  have hn1 : 1 ≤ n := by linarith only [hn]
  have hn0 : 0<n := by linarith only [hn]
  have H' := source_level_geometry U hB hi hn1 hq' H
  have hb := sourceDimension_bounds B i hB
  have he := sourceEpsilon_pos B D
  have he1 : sourceEpsilon B D ≤ 1 := by
    linarith only [sourceEpsilon_gap_small B D,sourceGapFloor_le_one B]
  have hN := sourceTargetScale_bounds B D (i+1) hB hn1
  have hC : 1 ≤ sourceOverlapConstant q := (by norm_num : (1:ℝ) ≤ 2).trans (sourceOverlapConstant_ge_two hq')
  have hE : U.error ≤ ((i:ℝ)+1)*n^(-100*(totalScoreExponent B D+B+1))*U.left.length := by
    apply (div_le_iff₀ ?_).mp U.normalized_error
    exact (show 0 < sourceTargetScale B D n i/2 by positivity [Real.rpow_pos_of_pos hn0 (sourceScaleProduct B D i)]).trans_le U.length_lower
  apply source_literal_dense_overlap (V:=(sourceTargetScale B D n i)^(-totalScoreExponent B i)) (e:=scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i) (W:=sourceWeightEnvelope B D) (L:=(2:ℝ)^(sourceCancellationOrder B D))
    H' hB hb.2 hC (pow_nonneg (by linarith only [hC]) _) hn1 hN.1 hN.2 he.le he1
    (sourceCapEnvelope_pos B D hq'.1).le (sourceWeightEnvelope_nonneg B D) (one_le_pow₀ (by norm_num)) rfl
    (source_local_envelope B D i (sourceDimension B i) hq' (Nat.le_of_lt hi) hb.2) (Nat.le_of_lt hi) hj
    (sourceA_nonneg B D _ j hb.2 (by omega))
    ((scaleA_mono_index _ j _ _ he.le hj).trans (by rw [scaleA_top])) hE rfl
    (by simpa only [neg_mul] using (source_old_variance_scale B D i hn0 hi).le) hgap H.error H.overlap

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_level_overlap_oai {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
    (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
    (htail : 2*(B:ℝ)*Real.exp
      (-(sourceTargetScale B D n (i+1))^(sourceEpsilon B D)/sourceTailDenominator B D q) ≤
        n^(-sourceTailExponent B D)) :
    let N := sourceTargetScale B D n (i+1)
    let b := sourceDimension B i
    let ε := sourceEpsilon B D
    let s := sourceCancellationOrder B D
    let P := sourceArithmeticP (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    let h := sourceArithmeticCount (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    let atom := fun (τ : Bool)=>if τ then U.right else U.left
    ∀j ≤ b, initialOverlapLower q ≤ listTraceOverlap q hq
      (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1)) := by
  let N := sourceTargetScale B D n (i+1)
  let b := sourceDimension B i
  let ε := sourceEpsilon B D
  let s := sourceCancellationOrder B D
  let P := sourceArithmeticP (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
  let h := sourceArithmeticCount (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
  let T := sourceBlockWindows N b ε
  let t := sourceArithmeticTrials (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
  let atom := fun (τ : Bool)=>if τ then U.right else U.left
  let k := sourceHalfMoment B D n (i+1)
  let L := N^(-scaleA b 0 ε*totalScoreExponent B i/2)
  let a := N^(-20*sourceWorkSize B D)
  have hn1 : 1 ≤ n := by linarith only [hn]
  have hn2 : 1 < n := by linarith only [hn]
  have hN : 0<N := (by norm_num : (0:ℝ)<1).trans_le (sourceTargetScale_bounds B D (i+1) hB hn1).1
  have H' := source_level_geometry U hB hi hn1 hq' H
  have hb := sourceDimension_bounds B i hB
  have hk : 1 ≤ k := (sourceHalfMoment_bounds B D (i+1) hB hn2).1
  let O := U.oracle.restrict hk (sourceHalfMoment_step B D i hB hi hn2)
  have hC := sourceOverlapConstant_large hq'
  have hp : initialOverlapLower q∈Set.Ioc 0 (1/8:ℝ) :=
    ⟨initialOverlapLower_pos q,(initialOverlapLower_lt_eighth hq'.1).le⟩
  have hc (j : ℕ) (hj : j ≤ b) : 1 ≤ h j :=
    (H'.length_positive hN hj).trans (H'.counts j hj).1
  have hP (j : ℕ) (hj : j<b) : 1 ≤ P j := H'.copies_positive hN hj
  have hlift (j : ℕ) (_hj : j<b) : sourceOverlapConstant q*h j*P j ≤ h (j+1) :=
    sourceArithmetic_count_lift _ _ _ _ _ _ _
  have hbase : initialOverlapLower q ≤ listTraceOverlap q hq
      (pureAtomRun (atom false) (h 0)) (pureAtomRun (atom false) (h 0+1)) := U.power_overlap
  by_cases hiw : i<warmupBlocks B
  · have hb2 : sourceDimension B i=2 := ite_eq_left hiw
    have hb' : b=2 := hb2
    have hw := source_level_warmup_second U hB hi hn hq' hiw H htail
    have hnum := source_level_all_budgets U hB hi hn hq' H htail
    have hexp := (source_level_exponent_margins B D i hB (Nat.le_of_lt hi)).1 hiw
    have hfirst := source_level_dense_overlap U hB hi hn hq' H (j:=1) (by omega) hexp.2.2.1
    have hfirst' : Real.sqrt (((h 1+1:ℕ):ℝ)*((2^s:ℕ):ℝ)*(sourceTargetScale B D n i)^(-totalScoreExponent B i))+
        2*((h 1+1:ℕ):ℝ)*((P 0:ℝ)*U.error) ≤ 1/4 := by
      simpa only [pow_one,sourceBlockLength,mul_one,mul_assoc] using hfirst
    have hev : Even (T 0) := by
      change Even (sourceBlockWindows N b ε 0)
      rw [sourceBlockWindows,ite_eq_left (by omega : 0<b)]
      exact sourceWindowSize_even _ _ _ _
    have hfit : t 0*(2*h 0+1)+T 0 ≤ P 0 := by
      dsimp only [t]
      rw [sourceArithmetic_inner_trials (sourceOverlapConstant q) N b ε U.left.length U.overlapCount 0 (by omega : 0+1≠b)]
      have hh := sourceLocalTrials_budget (P 0) (h 0)
      have ht := (H'.windows 0 (by omega)).2.2.1
      change 2*T 0 ≤ P 0 at ht
      rw [mul_assoc] at hh
      change sourceLocalTrials (P 0) (h 0)*(2*h 0+1)+T 0 ≤ P 0
      omega
    have hs : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount (fun _=>T 0) s 0 ≤ 1/2 := by
      simpa only [L,N,b,ε,k,s,T,t,a,hb2,sourceSparseCount,Finset.range_zero,Finset.prod_empty,Nat.mul_one,Nat.cast_pow,Nat.cast_ofNat] using hw.1
    have hclip : sourceClippingCost (fun _=>T 0) (fun _=>t 0) s 0 k (initialOverlapLower q) a L ≤ 1/2 := by
      simpa only [L,N,b,ε,k,s,T,t,a,P,h,hb2] using hw.2.1
    have hv : (sourceTargetScale B D n i)^(-totalScoreExponent B i) ≤ L^2 := by
      rw [source_old_variance_square B D i (by linarith only [hn]) hi]
    have hh := source_warmup_nested_overlap hq U.error_nonneg s k P h atom O hp hC
      (fun j hj=>hc j (by omega)) (fun j hj=>hP j (by omega)) (fun j hj=>hlift j (by omega))
      hfirst' hbase (T 0) (t 0) (H'.windows 0 (by omega)).1 hev (H'.windows 0 (by omega)).2.1
      (H'.windows 0 (by omega)).2.2.2 hfit a a L (by positivity) (by positivity) hk hv hs
      (hnum.2.2.2.1 0 (by omega)) hclip (by simpa only [L,N,b,ε,k,s,T,t,a,P,h,hb2] using hw.2.2)
    change ∀j : ℕ,j≤b → initialOverlapLower q ≤ listTraceOverlap q hq
      (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1))
    intro j hj
    exact hh j (by change j≤b at hj; omega)
  · apply source_nested_overlap hq U.error_nonneg s P h atom (O.hellinger hk) b hp hC hc hP hlift _ hbase
    intro j hj
    exact source_level_dense_overlap U hB hi hn hq' H (by omega)
      ((source_level_exponent_margins B D i hB (Nat.le_of_lt hi)).2 (by omega) (j+1) (by omega))

end TraceReconstruction


end
end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.TraceReconstruction.source_level_overlap_oai := @OAI.TraceReconstruction.source_level_overlap_oai
