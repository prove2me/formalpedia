-- Prove2me | solution 1 for OAI.Erdos3.replacement_selected_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:14:17.976783+00:00
-- url     : https://prove2.me/submissions/07b40d11-6c8b-4b02-84f6-ec7e4a04d929

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090
import Theorems.Thm_OAI_Erdos3_replacementCommonInputLog_bounds
import Theorems.Thm_OAI_Erdos3_weightedReplacementTolerance_pos

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.NativeModelingNumerics

end Erdos3.NativeModelingNumerics

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem replacementAccuracy_spec {B epsilon : ℝ} (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    0 < replacementAccuracy B epsilon ∧ replacementAccuracy B epsilon ≤ 1 ∧
      B * replacementAccuracy B epsilon ≤ epsilon := by
  have hden : 0 < 1 + B := by positivity
  refine ⟨lt_min zero_lt_one (div_pos hepsilon hden), min_le_left _ _, ?_⟩
  calc
    _ ≤ B * (epsilon / (1 + B)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hB
    _ ≤ epsilon := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

theorem replacementAccuracy_inverse_le_exp {B epsilon P : ℝ}
    (hB0 : 0 ≤ B) (hepsilon : 0 < epsilon) (hP : 0 ≤ P)
    (hB : B ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (replacementAccuracy B epsilon)⁻¹ ≤ Real.exp (2 * P + 2) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold replacementAccuracy
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by linarith : 0 ≤ 2 * P + 2)
  · rw [inv_div, div_eq_mul_inv]
    calc
      (1 + B) * epsilon⁻¹ ≤ (1 + Real.exp P) * Real.exp P :=
        mul_le_mul (by linarith) heps (inv_nonneg.mpr hepsilon.le) (by positivity)
      _ ≤ 2 * (Real.exp P) ^ 2 := by nlinarith
      _ ≤ Real.exp 2 * (Real.exp P) ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCutoffLogBounds
namespace OAI

section

namespace Erdos3

theorem integerBoxNearRatio_spec (d : ℕ) {epsilon : ℝ} (heps : 0 < epsilon) :
    0 < integerBoxNearRatio d epsilon ∧ integerBoxNearRatio d epsilon ≤ 1 ∧
      (3 : ℝ) ^ d * integerBoxNearRatio d epsilon ≤ epsilon / 2 := by
  have h := replacementAccuracy_spec (by positivity : 0 ≤ 2 * (3 : ℝ) ^ d) heps
  change 0 < integerBoxNearRatio d epsilon ∧ integerBoxNearRatio d epsilon ≤ 1 ∧
    2 * (3 : ℝ) ^ d * integerBoxNearRatio d epsilon ≤ epsilon at h
  exact ⟨h.1, h.2.1, by linarith [h.2.2]⟩

end Erdos3

end

section

namespace Erdos3

theorem integerBoxGcdCutoff_le_exp (d : ℕ) {C epsilon P : ℝ}
    (hC0 : 0 ≤ C) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow : (2 : ℝ) ^ (d - 1) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (integerBoxGcdCutoff d C epsilon : ℝ) ≤ Real.exp (3 * P + 6) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hsum := one_add_le_exp_succ hP hC
  have hx : 2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon ≤ Real.exp (3 * P + 3) := by
    calc
      _ = 2 * (2 : ℝ) ^ (d - 1) * (1 + C) * epsilon⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ Real.exp 2 * Real.exp P * Real.exp (P + 1) * Real.exp P := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hceil := (Nat.ceil_lt_add_one
    (by positivity : 0 ≤ 2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon)).le
  have hbase : 1 ≤ Real.exp (3 * P + 3) := Real.one_le_exp_iff.mpr (by linarith)
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    (integerBoxGcdCutoff d C epsilon : ℝ) ≤ Real.exp (3 * P + 3) + 2 := by
      unfold integerBoxGcdCutoff
      push_cast
      linarith
    _ ≤ 3 * Real.exp (3 * P + 3) := by linarith
    _ ≤ Real.exp 3 * Real.exp (3 * P + 3) :=
      mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem integerBoxNearRatio_inverse_le_exp (d : ℕ) {epsilon P : ℝ}
    (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow : 2 * (3 : ℝ) ^ d ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (integerBoxNearRatio d epsilon)⁻¹ ≤ Real.exp (2 * P + 2) :=
  replacementAccuracy_inverse_le_exp (by positivity) heps0 hP hpow heps

theorem integerBoxPairScale_le_exp (d : ℕ) {C epsilon P : ℝ}
    (hC0 : 0 ≤ C) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow2 : (2 : ℝ) ^ (d - 1) ≤ Real.exp P)
    (hpow3 : 2 * (3 : ℝ) ^ d ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    integerBoxPairScale d C epsilon ≤ Real.exp (3 * P + 6) := by
  apply max_le (integerBoxGcdCutoff_le_exp d hC0 heps0 hP hpow2 hC heps)
  rw [one_div]
  exact (integerBoxNearRatio_inverse_le_exp d heps0 hP hpow3 heps).trans
    (Real.exp_le_exp.mpr (by linarith))

theorem integerBoxRetainedGap_inverse_le_exp (d D : ℕ) {c epsilon P : ℝ}
    (hD : 0 < D) (hc0 : 0 < c) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow : 2 * (3 : ℝ) ^ d ≤ Real.exp P)
    (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (integerBoxRetainedGap d D c epsilon)⁻¹ ≤ Real.exp (3 * P + 2) := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDinv : (D : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hD1
  have hnu0 := (integerBoxNearRatio_spec d heps0).1
  have hnu := integerBoxNearRatio_inverse_le_exp d heps0 hP hpow heps
  calc
    _ = (D : ℝ)⁻¹ * (integerBoxNearRatio d epsilon)⁻¹ * c⁻¹ := by
      simp only [integerBoxRetainedGap, mul_inv_rev]
      ring
    _ ≤ 1 * Real.exp (2 * P + 2) * Real.exp P := by gcongr
    _ = _ := by rw [one_mul, ← Real.exp_add]; congr 1; ring

theorem integerBoxGcdModulus_le_exp (d D : ℕ) {C epsilon P : ℝ}
    (hC0 : 0 ≤ C) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow : (2 : ℝ) ^ (d - 1) ≤ Real.exp P)
    (hD : (D : ℝ) ≤ Real.exp P) (hC : C ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    ((D * integerBoxGcdCutoff d C epsilon : ℕ) : ℝ) ≤ Real.exp (4 * P + 6) := by
  rw [Nat.cast_mul]
  calc
    _ ≤ Real.exp P * Real.exp (3 * P + 6) :=
      mul_le_mul hD (integerBoxGcdCutoff_le_exp d hC0 heps0 hP hpow hC heps)
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallWeightedPhysicalReplacement
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem weightedReplacementTolerance_inverse_le_exp {F E epsilon P : ℝ}
    (hF0 : 0 ≤ F) (hE0 : 0 ≤ E) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hF : F ≤ Real.exp P) (hE : E ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (weightedReplacementTolerance F E epsilon)⁻¹ ≤ Real.exp (6 * P + 6) := by
  have hcoef : F ^ 2 * (1 + E) ≤ Real.exp (3 * P + 2) := by
    calc
      _ ≤ (Real.exp P) ^ 2 * Real.exp (P + 1) :=
        mul_le_mul (pow_le_pow_left₀ hF0 hF 2) (one_add_le_exp_succ hP hE)
          (by linarith) (by positivity)
      _ = Real.exp (3 * P + 1) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have heps2 : (epsilon ^ 2)⁻¹ ≤ Real.exp (3 * P + 2) := by
    calc
      _ = (epsilon⁻¹) ^ 2 := by rw [inv_pow]
      _ ≤ (Real.exp P) ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr heps0.le) heps 2
      _ = Real.exp (2 * P) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ Real.exp (2 * (3 * P + 2) + 2) :=
      replacementAccuracy_inverse_le_exp (by positivity) (sq_pos_of_pos heps0)
        (by linarith) hcoef heps2
    _ = _ := by congr 1; ring

theorem replacementWindowFactor_le_exp (m : ℕ) {K P : ℝ}
    (hK0 : 0 ≤ K) (hK : K ≤ Real.exp P) :
    (3 * K) ^ m ≤ Real.exp ((m : ℝ) * (P + 3)) := by
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hbase : 3 * K ≤ Real.exp (P + 3) := by
    calc
      _ ≤ Real.exp 3 * Real.exp P := mul_le_mul h3 hK hK0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity : 0 ≤ 3 * K) hbase m

theorem replacementSampledEnergy_le_exp (n : ℕ) {A P : ℝ}
    (hA0 : 0 ≤ A) (hA : A ≤ Real.exp P) :
    (2 : ℝ) ^ (n + 1) * A ^ n ≤ Real.exp ((n : ℝ) * P + 2 * (n + 1)) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ (Real.exp 2) ^ (n + 1) * (Real.exp P) ^ n :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) h2 _) (pow_le_pow_left₀ hA0 hA _)
        (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; congr 1; ring

theorem physicalReplacementInputLog_nonneg (m n : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ physicalReplacementInputLog m n P := by
  unfold physicalReplacementInputLog
  positivity

theorem physicalReplacementTolerance_inverse_le_exp (m n : ℕ) {K A epsilon P : ℝ}
    (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon)⁻¹ ≤
      Real.exp (6 * physicalReplacementInputLog m n P + 6) := by
  apply weightedReplacementTolerance_inverse_le_exp (by positivity) (by positivity) heps0
    (physicalReplacementInputLog_nonneg m n hP)
  · apply (replacementWindowFactor_le_exp m hK0 hK).trans
    apply Real.exp_le_exp.mpr
    unfold physicalReplacementInputLog
    nlinarith [mul_nonneg (Nat.cast_nonneg n (α := ℝ)) hP]
  · apply (replacementSampledEnergy_le_exp n hA0 hA).trans
    apply Real.exp_le_exp.mpr
    unfold physicalReplacementInputLog
    nlinarith [mul_nonneg (Nat.cast_nonneg m (α := ℝ)) (by linarith : 0 ≤ P + 3)]
  · apply heps.trans
    apply Real.exp_le_exp.mpr
    unfold physicalReplacementInputLog
    nlinarith [mul_nonneg (Nat.cast_nonneg m (α := ℝ)) (by linarith : 0 ≤ P + 3),
      mul_nonneg (Nat.cast_nonneg n (α := ℝ)) hP]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InitialBudgetJointReplacement
namespace OAI

section

namespace Erdos3

theorem replacementCutoffInputLog_bounds (m n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ replacementCutoffInputLog m n d P ∧
    P ≤ replacementCutoffInputLog m n d P ∧
    6 * physicalReplacementInputLog m n P + 6 ≤ replacementCutoffInputLog m n d P ∧
    3 * (d : ℝ) + 2 ≤ replacementCutoffInputLog m n d P ∧
    2 * (d : ℝ) ≤ replacementCutoffInputLog m n d P := by
  have hW := physicalReplacementInputLog_nonneg m n hP
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  unfold replacementCutoffInputLog
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem replacement_binary_power_le_exp (d : ℕ) : (2 : ℝ) ^ d ≤ Real.exp (2 * d) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  apply (pow_le_pow_left₀ (by norm_num) h2 d).trans_eq
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem replacement_ternary_power_le_exp (d : ℕ) : 2 * (3 : ℝ) ^ d ≤ Real.exp (3 * d + 2) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    _ ≤ Real.exp 2 * (Real.exp 3) ^ d := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

theorem replacementCutoffInputLog_power_bounds (m n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (2 : ℝ) ^ (d - 1) ≤ Real.exp (replacementCutoffInputLog m n d P) ∧
    2 * (3 : ℝ) ^ d ≤ Real.exp (replacementCutoffInputLog m n d P) := by
  have hb := replacementCutoffInputLog_bounds m n d hP
  constructor
  · apply (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le d 1)).trans
    exact (replacement_binary_power_le_exp d).trans (Real.exp_le_exp.mpr hb.2.2.2.2)
  · exact (replacement_ternary_power_le_exp d).trans (Real.exp_le_exp.mpr hb.2.2.2.1)

end Erdos3

end

section

namespace Erdos3

theorem replacement_selected_parameter_bounds (m n d D : ℕ) {K A Cwidth c epsilon P : ℝ}
    (hP : 0 ≤ P) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hCwidth0 : 0 ≤ Cwidth)
    (hc0 : 0 < c) (heps0 : 0 < epsilon) (hD : 0 < D)
    (hDlog : (D : ℝ) ≤ Real.exp P) (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hCwidth : Cwidth ≤ Real.exp P) (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    let tol := weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon
    let Z := replacementCommonInputLog m n d P
    0 < tol ∧ tol⁻¹ ≤ Real.exp Z ∧
    0 < integerBoxRetainedGap d D c tol ∧ (integerBoxRetainedGap d D c tol)⁻¹ ≤ Real.exp Z ∧
    ((D * integerBoxGcdCutoff d Cwidth tol : ℕ) : ℝ) ≤ Real.exp Z ∧
    integerBoxPairScale d Cwidth tol ≤ Real.exp Z := by
  intro tol Z
  let T := replacementCutoffInputLog m n d P
  have hb := replacementCutoffInputLog_bounds m n d hP
  have hz := replacementCommonInputLog_bounds m n d hP
  have hpows := replacementCutoffInputLog_power_bounds m n d hP
  have ht : 0 < tol := weightedReplacementTolerance_pos (by positivity) heps0
  have hti : tol⁻¹ ≤ Real.exp T :=
    (physicalReplacementTolerance_inverse_le_exp m n hK0 hA0 heps0 hP hK hA heps).trans
      (Real.exp_le_exp.mpr hb.2.2.1)
  have hexp : Real.exp P ≤ Real.exp T := Real.exp_le_exp.mpr hb.2.1
  have hq := integerBoxGcdModulus_le_exp d D hCwidth0 ht hb.1 hpows.1
    (hDlog.trans hexp) (hCwidth.trans hexp) hti
  have hk := integerBoxRetainedGap_inverse_le_exp d D hD hc0 ht hb.1 hpows.2 (hc.trans hexp) hti
  have hs := integerBoxPairScale_le_exp d hCwidth0 ht hb.1 hpows.1 hpows.2 (hCwidth.trans hexp) hti
  refine ⟨ht, hti.trans (Real.exp_le_exp.mpr hz.2.2.1), ?_, ?_, ?_, ?_⟩
  · unfold integerBoxRetainedGap
    exact mul_pos (mul_pos (by exact_mod_cast hD) (integerBoxNearRatio_spec d ht).1) hc0
  · exact hk.trans (Real.exp_le_exp.mpr (by linarith [hz.2.2.2.2.1]))
  · exact hq.trans (Real.exp_le_exp.mpr hz.2.2.2.1)
  · exact hs.trans (Real.exp_le_exp.mpr hz.2.2.2.2.1)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.replacement_selected_parameter_bounds := @OAI.Erdos3.replacement_selected_parameter_bounds
