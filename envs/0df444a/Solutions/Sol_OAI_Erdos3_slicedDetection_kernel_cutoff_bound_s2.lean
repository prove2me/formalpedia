-- Prove2me | solution 1 for OAI.Erdos3.slicedDetection_kernel_cutoff_bound_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:33:16.643283+00:00
-- url     : https://prove2.me/submissions/8703cdd5-83e0-4623-b523-2f2897db2c43

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B065

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateDeterminant
namespace OAI

section

namespace Erdos3

theorem coordinateDeterminantVariation_nonneg (I X : Type*) [Fintype I] [Fintype X] :
    0 ≤ coordinateDeterminantVariation I X := by
  unfold coordinateDeterminantVariation
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

theorem integerScalarCubeDensityCap_pos (I : Type*) [Fintype I] :
    0 < integerScalarCubeDensityCap I := by
  unfold integerScalarCubeDensityCap
  positivity


open scoped BigOperators Classical

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSublevelThresholdBudget
namespace OAI


namespace Erdos3

theorem polynomialSublevelThreshold_log_inv (n m : ℕ) {C scale η : ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) :
    Real.log (polynomialSublevelThreshold n m C scale η)⁻¹ =
      Real.log 2 + Real.log (1 + scale) +
        (n : ℝ) * Real.log (1 + 2 * C * (m + 1 : ℝ) / η) := by
  have hscale : 0 < 1 + scale := by linarith
  have hL : 0 < 1 + 2 * C * (m + 1 : ℝ) / η := by positivity
  rw [polynomialSublevelThreshold, inv_inv,
    Real.log_mul (mul_pos (by norm_num) hscale).ne' (pow_pos hL n).ne',
    Real.log_mul (by norm_num) hscale.ne', Real.log_pow]


theorem polynomialSublevelThreshold_log_budget (n m : ℕ) {C scale η P : ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) (hP : 0 ≤ P)
    (hCP : C ≤ Real.exp P) (hsP : scale ≤ Real.exp P)
    (hmP : (m + 1 : ℝ) ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P) :
    Real.log (polynomialSublevelThreshold n m C scale η)⁻¹ ≤
      (1 + 3 * (n : ℝ)) * P + 2 * Real.log 2 + (n : ℝ) * Real.log 3 := by
  have hE : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hE3 : 1 ≤ Real.exp (3 * P) := Real.one_le_exp_iff.mpr (by positivity)
  have hscale : 1 + scale ≤ 2 * Real.exp P := by linarith
  have hprod : C * (m + 1 : ℝ) * η⁻¹ ≤ Real.exp P * Real.exp P * Real.exp P :=
    mul_le_mul (mul_le_mul hCP hmP (by positivity) (Real.exp_pos P).le) hηP
      (inv_nonneg.mpr hη.le) (by positivity)
  have heq : Real.exp P * Real.exp P * Real.exp P = Real.exp (3 * P) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hprod
  have hquot : 2 * C * (m + 1 : ℝ) / η ≤ 2 * Real.exp (3 * P) := by
    have ht := mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 2 by norm_num)
    simpa only [div_eq_mul_inv, mul_assoc] using ht
  have hinner : 1 + 2 * C * (m + 1 : ℝ) / η ≤ 3 * Real.exp (3 * P) := by linarith
  have hlogs := Real.log_le_log (show 0 < 1 + scale by positivity) hscale
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero P), Real.log_exp] at hlogs
  have hlogL := Real.log_le_log (show 0 < 1 + 2 * C * (m + 1 : ℝ) / η by positivity) hinner
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero (3 * P)), Real.log_exp] at hlogL
  rw [polynomialSublevelThreshold_log_inv n m hC hs hη]
  calc
    _ ≤ Real.log 2 + (Real.log 2 + P) + (n : ℝ) * (Real.log 3 + 3 * P) :=
      add_le_add (add_le_add le_rfl hlogs) (mul_le_mul_of_nonneg_left hlogL (Nat.cast_nonneg n))
    _ = _ := by ring

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.JointKernelCutoffBudget
namespace OAI


namespace Erdos3

theorem jointKernelCutoff_le (n b : ℕ) {K T ε κ : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hε : 0 < ε) (hκ : 0 < κ) :
    (jointKernelCutoff n b K T ε κ : ℝ) ≤
      2 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε := by
  unfold jointKernelCutoff
  have h := Nat.ceil_lt_add_one
    (show 0 ≤ 1 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε by positivity)
  linarith


theorem jointKernelCutoff_le_exp (n b : ℕ) {K T ε κ P : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hε : 0 < ε) (hκ : 0 < κ) (hP : 0 ≤ P)
    (hnP : (n : ℝ) ≤ Real.exp P) (hbP : (b : ℝ) ≤ Real.exp P)
    (hKP : K ≤ Real.exp P) (hTP : T ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) (hκP : κ⁻¹ ≤ Real.exp P) :
    (jointKernelCutoff n b K T ε κ : ℝ) ≤ Real.exp (2 * P + 8) := by
  have hE : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  calc
    _ ≤ 2 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε := jointKernelCutoff_le n b hK hT hε hκ
    _ ≤ 2 + Real.exp P + Real.exp P + (1 + Real.exp P) * Real.exp P +
        2 * Real.exp P * Real.exp P := by
      simp only [div_eq_mul_inv]
      gcongr
    _ ≤ 8 * (Real.exp P) ^ 2 := by nlinarith [sq_nonneg (Real.exp P - 1)]
    _ ≤ Real.exp 8 * (Real.exp P) ^ 2 := mul_le_mul_of_nonneg_right h8 (sq_nonneg _)
    _ = Real.exp (2 * P + 8) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num
      ring

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelBudgetEnvelope
namespace OAI

section

namespace Erdos3

theorem scalarKernel_polynomial_envelope {q j N R Q : ℝ}
    (hq : 0 ≤ q) (_hj : 0 ≤ j) (_hN : 0 ≤ N) (hR : 0 ≤ R)
    (hQ : 10 ≤ Q) (hqQ : q + 1 ≤ Q) (hjQ : j ≤ Q) (hNQ : N ≤ Q) (hRQ : R ≤ Q) :
    1 ≤ 16 * Q^3 ∧ q + 1 ≤ 16 * Q^3 ∧ 2 * R + (q + 1) ≤ 16 * Q^3 ∧
    N + q^2 + q ≤ 16 * Q^3 ∧
    j * ((q + 1) * (4 + (q + 1)) + q^2 + 1) ≤ 16 * Q^3 ∧
    j * (q + 1) * (4 + (q + 1) + 2 * R) + R ≤ 16 * Q^3 ∧
    j * ((q + 1) * (4 + (q + 1))) + 3 * N + (q + 1) + q * (8 + (q + 1)) ≤ 16 * Q^3 ∧
    N * (q + 1) ≤ 16 * Q^3 := by
  have hQ0 : 0 ≤ Q := by linarith
  have hqQ' : q ≤ Q := by linarith
  have h4 : (4 : ℝ) ≤ Q := by linarith
  have h8 : (8 : ℝ) ≤ Q := by linarith
  have hQ2 : Q ≤ Q^2 := by nlinarith
  have hQ3 : Q^2 ≤ Q^3 := by nlinarith
  have ha : (q + 1) * (4 + (q + 1)) ≤ 2 * Q^2 := by
    calc
      _ ≤ Q * (Q + Q) := by gcongr
      _ = _ := by ring
  have hu : (q + 1) + q * (8 + (q + 1)) ≤ Q + 2 * Q^2 := by
    calc
      _ ≤ Q + Q * (Q + Q) := by gcongr
      _ = _ := by ring
  have hv : N + q^2 + q ≤ 2 * Q + Q^2 := by
    calc
      _ ≤ Q + Q^2 + Q := by gcongr
      _ = _ := by ring
  have ht : j * ((q + 1) * (4 + (q + 1)) + q^2 + 1) ≤ 4 * Q^3 := by
    calc
      _ ≤ Q * (2 * Q^2 + Q^2 + 1) := by gcongr
      _ ≤ _ := by nlinarith
  have he : j * (q + 1) * (4 + (q + 1) + 2 * R) + R ≤ 4 * Q^3 + Q := by
    calc
      _ ≤ Q * Q * (Q + Q + 2 * Q) + Q := by gcongr
      _ = _ := by ring
  have hc : j * ((q + 1) * (4 + (q + 1))) + 3 * N + (q + 1) + q * (8 + (q + 1)) ≤
      2 * Q^3 + 4 * Q + 2 * Q^2 := by
    calc
      _ = j * ((q + 1) * (4 + (q + 1))) + 3 * N + ((q + 1) + q * (8 + (q + 1))) := by ring
      _ ≤ Q * (2 * Q^2) + 3 * Q + (Q + 2 * Q^2) := by gcongr
      _ = _ := by ring
  have hs : N * (q + 1) ≤ Q^2 := by nlinarith [mul_le_mul hNQ hqQ (by linarith : 0 ≤ q + 1) hQ0]
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI


namespace Erdos3

theorem scalarKernelConditioningConstant_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} (hM : 0 < M) (hD : 0 < D) : 0 < scalarKernelConditioningConstant I J M D :=
  pow_pos (scalarCubeResidueDensityCap_pos I (M * D) (Nat.mul_pos hM hD)) _

theorem scalarKernelTailConstant_pos (I J : Type*) [Fintype I] [Fintype J] :
    0 < scalarKernelTailConstant I J := by
  unfold scalarKernelTailConstant
  exact pow_pos (mul_pos (integerScalarCubeDensityCap_pos I) (by positivity)) _

theorem scalarKernelAdjustedAccuracy_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelAdjustedAccuracy I J M D η :=
  div_pos hη (scalarKernelConditioningConstant_pos I J hM hD)

theorem scalarKernelThreshold_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelThreshold I J M D η := by
  unfold scalarKernelThreshold discreteScalarMinorThreshold
  apply polynomialSublevelThreshold_pos
  · apply mul_nonneg (pow_nonneg (integerScalarCubeDensityCap_pos I).le _)
    unfold multivariateSublevelConstant
    exact mul_nonneg (by positivity) (univariateSublevelConstant_pos _).le
  · positivity
  · exact scalarKernelAdjustedAccuracy_pos I J hM hD hη

theorem scalarKernelCutoff_le_exp_of_bounds (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η P : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) (hP : 1 ≤ P)
    (hnP : (Fintype.card I + 1 : ℝ) ≤ Real.exp P)
    (hbP : (D * ((Fintype.card I + 1) * M) : ℕ) ≤ Real.exp P)
    (hKP : coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))) ≤ Real.exp P)
    (hTP : scalarKernelTailConstant I J ≤ Real.exp P)
    (hεP : (scalarKernelAdjustedAccuracy I J M D η)⁻¹ ≤ Real.exp P)
    (hCP : (integerScalarCubeDensityCap I) ^ Fintype.card J *
      multivariateSublevelConstant (Fintype.card (J × Option I)) (Fintype.card I) ≤ Real.exp P)
    (hSP : (Fintype.card I + 1 : ℝ) ^ Fintype.card (J × Option I) ≤ Real.exp P) :
    (scalarKernelCutoff I J M D η : ℝ) ≤ Real.exp (scalarKernelCutoffLogBudget I J P) := by
  let a : ℝ := ((Fintype.card (J × Option I) * Fintype.card I : ℕ) : ℝ)
  let Q := (4 + 3 * a) * (P + 2)
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hPQ : P ≤ Q := by dsimp [Q]; nlinarith
  have hQ : 0 ≤ Q := hP0.trans hPQ
  have hκ := scalarKernelThreshold_pos I J hM hD hη
  have hε := scalarKernelAdjustedAccuracy_pos I J hM hD hη
  have hC : 0 ≤ (integerScalarCubeDensityCap I) ^ Fintype.card J *
      multivariateSublevelConstant (Fintype.card (J × Option I)) (Fintype.card I) := by
    apply mul_nonneg (pow_nonneg (integerScalarCubeDensityCap_pos I).le _)
    unfold multivariateSublevelConstant
    exact mul_nonneg (by positivity) (univariateSublevelConstant_pos _).le
  have hS : 0 ≤ (Fintype.card I + 1 : ℝ) ^ Fintype.card (J × Option I) := by positivity
  have h2 : (1 + 1 : ℝ) ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  have ht := polynomialSublevelThreshold_log_budget
    (Fintype.card (J × Option I) * Fintype.card I) 1 hC hS hε hP0 hCP hSP
    (by simpa only [Nat.cast_one] using h2) hεP
  have hlog : Real.log (scalarKernelThreshold I J M D η)⁻¹ ≤
      (1 + 3 * a) * P + 2 * Real.log 2 + a * Real.log 3 := ht
  have hlog2 : Real.log 2 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog3 : Real.log 3 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hκQ : (scalarKernelThreshold I J M D η)⁻¹ ≤ Real.exp Q := by
    apply (Real.log_le_iff_le_exp (inv_pos.mpr hκ)).mp
    apply hlog.trans
    have h3 := mul_le_mul_of_nonneg_left hlog3 ha
    dsimp [Q]
    nlinarith
  have hexp : Real.exp P ≤ Real.exp Q := Real.exp_le_exp.mpr hPQ
  exact jointKernelCutoff_le_exp _ _ (coordinateDeterminantVariation_nonneg _ _)
    (scalarKernelTailConstant_pos I J).le hε hκ hQ
    (by simpa only [Nat.cast_add, Nat.cast_one] using hnP.trans hexp)
    (hbP.trans hexp) (hKP.trans hexp) (hTP.trans hexp) (hεP.trans hexp) hκQ


theorem integerScalarCubeDensityCap_le_exp (I : Type*) [Fintype I] :
    integerScalarCubeDensityCap I ≤
      Real.exp ((Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ))) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hn : (Fintype.card I + 1 : ℝ) ≤ Real.exp (Fintype.card I + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I + 1 : ℝ)]
  unfold integerScalarCubeDensityCap
  push_cast
  calc
    _ ≤ (Real.exp 4 * Real.exp (Fintype.card I + 1 : ℝ)) ^ (Fintype.card I + 1) := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; push_cast; rfl

theorem scalarKernelTailConstant_le_exp (I J : Type*) [Fintype I] [Fintype J] :
    scalarKernelTailConstant I J ≤ Real.exp ((Fintype.card J : ℝ) *
      ((Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ)) + (Fintype.card I : ℝ)^2 + 1)) := by
  have hf := factorial_le_exp_sq (Fintype.card I)
  have hA0 := (integerScalarCubeDensityCap_pos I).le
  have hA := integerScalarCubeDensityCap_le_exp I
  have hE : 1 ≤ Real.exp ((Fintype.card I : ℝ)^2) := Real.one_le_exp_iff.mpr (sq_nonneg _)
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hs : 1 + ((Fintype.card I).factorial : ℝ) ≤ Real.exp ((Fintype.card I : ℝ)^2 + 1) := by
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos ((Fintype.card I : ℝ)^2)).le]
  unfold scalarKernelTailConstant
  calc
    _ ≤ (Real.exp ((Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ))) *
        Real.exp ((Fintype.card I : ℝ)^2 + 1)) ^ Fintype.card J := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; ring

theorem coordinateDeterminantVariation_le_exp (I : Type*) [Fintype I] (N : ℕ) :
    coordinateDeterminantVariation I (Fin N) ≤
      Real.exp ((N : ℝ) + (Fintype.card I : ℝ)^2 + Fintype.card I) := by
  have hN : (N : ℝ) ≤ Real.exp N := by linarith [Real.add_one_le_exp (N : ℝ)]
  have hq : (Fintype.card I : ℝ) ≤ Real.exp (Fintype.card I : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I : ℝ)]
  simp only [coordinateDeterminantVariation, Fintype.card_fin]
  calc
    _ ≤ Real.exp N * (Real.exp ((Fintype.card I : ℝ)^2) * Real.exp (Fintype.card I : ℝ)) := by
      gcongr
      exact factorial_le_exp_sq _
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring


theorem scalarKernelConditioningConstant_le_exp (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) {R : ℝ} (hM : (M : ℝ) ≤ Real.exp R) (hD : (D : ℝ) ≤ Real.exp R) :
    scalarKernelConditioningConstant I J M D ≤ Real.exp ((Fintype.card J : ℝ) *
      (Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ) + 2 * R)) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hn : (Fintype.card I + 1 : ℝ) ≤ Real.exp (Fintype.card I + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I + 1 : ℝ)]
  have hbase : 4 * (Fintype.card I + 1 : ℝ) * ((M : ℝ) * D) ≤
      Real.exp (4 + (Fintype.card I + 1 : ℝ) + 2 * R) := by
    calc
      _ ≤ Real.exp 4 * Real.exp (Fintype.card I + 1 : ℝ) * (Real.exp R * Real.exp R) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  unfold scalarKernelConditioningConstant scalarCubeResidueDensityCap
  push_cast
  calc
    _ ≤ (Real.exp (4 + (Fintype.card I + 1 : ℝ) + 2 * R) ^ (Fintype.card I + 1)) ^ Fintype.card J := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

theorem scalarKernelAdjustedAccuracy_inv_le_exp (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) {R η : ℝ} (hη : 0 < η) (hM : (M : ℝ) ≤ Real.exp R)
    (hD : (D : ℝ) ≤ Real.exp R) (hηR : η⁻¹ ≤ Real.exp R) :
    (scalarKernelAdjustedAccuracy I J M D η)⁻¹ ≤ Real.exp ((Fintype.card J : ℝ) *
      (Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ) + 2 * R) + R) := by
  rw [scalarKernelAdjustedAccuracy, inv_div, div_eq_mul_inv, Real.exp_add]
  exact mul_le_mul (scalarKernelConditioningConstant_le_exp I J M D hM hD) hηR
    (inv_nonneg.mpr hη.le) (Real.exp_pos _).le

theorem scalarKernelMinorConstant_le_exp (I J : Type*) [Fintype I] [Nonempty I] [Fintype J] (N : ℕ) :
    (integerScalarCubeDensityCap I) ^ Fintype.card J * multivariateSublevelConstant N (Fintype.card I) ≤
      Real.exp ((Fintype.card J : ℝ) * ((Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ))) +
        3 * (N : ℝ) + (Fintype.card I + 1 : ℝ) + Fintype.card I * (8 + (Fintype.card I + 1 : ℝ))) := by
  have hA := integerScalarCubeDensityCap_le_exp I
  have hA0 := (integerScalarCubeDensityCap_pos I).le
  have hC := multivariateSublevelConstant_le_exp N (Fintype.card I) Fintype.card_pos
  have hC0 : 0 ≤ multivariateSublevelConstant N (Fintype.card I) := by
    unfold multivariateSublevelConstant
    exact mul_nonneg (by positivity) (univariateSublevelConstant_pos _).le
  calc
    _ ≤ Real.exp ((Fintype.card I + 1 : ℝ) * (4 + (Fintype.card I + 1 : ℝ))) ^ Fintype.card J *
        Real.exp (3 * (N : ℝ) + (Fintype.card I + 1 : ℝ) + Fintype.card I * (8 + (Fintype.card I + 1 : ℝ))) := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

theorem scalarKernelMinorScale_le_exp (I : Type*) [Fintype I] (N : ℕ) :
    (Fintype.card I + 1 : ℝ) ^ N ≤ Real.exp ((N : ℝ) * (Fintype.card I + 1 : ℝ)) := by
  have hn : (Fintype.card I + 1 : ℝ) ≤ Real.exp (Fintype.card I + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I + 1 : ℝ)]
  calc
    _ ≤ Real.exp (Fintype.card I + 1 : ℝ) ^ N := by gcongr
    _ = _ := (Real.exp_nat_mul _ _).symm


theorem scalarKernelInputBudget_bounds (I J : Type*)
    [Fintype I] [Nonempty I] [Fintype J] (M D : ℕ) {R η : ℝ}
    (hR : 0 ≤ R) (hη : 0 < η) (hM : (M : ℝ) ≤ Real.exp R)
    (hD : (D : ℝ) ≤ Real.exp R) (hηR : η⁻¹ ≤ Real.exp R) :
    1 ≤ scalarKernelInputBudget I J R ∧
    (Fintype.card I + 1 : ℝ) ≤ Real.exp (scalarKernelInputBudget I J R) ∧
    (D * ((Fintype.card I + 1) * M) : ℕ) ≤ Real.exp (scalarKernelInputBudget I J R) ∧
    coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))) ≤ Real.exp (scalarKernelInputBudget I J R) ∧
    scalarKernelTailConstant I J ≤ Real.exp (scalarKernelInputBudget I J R) ∧
    (scalarKernelAdjustedAccuracy I J M D η)⁻¹ ≤ Real.exp (scalarKernelInputBudget I J R) ∧
    (integerScalarCubeDensityCap I)^Fintype.card J *
      multivariateSublevelConstant (Fintype.card (J × Option I)) (Fintype.card I) ≤
        Real.exp (scalarKernelInputBudget I J R) ∧
    (Fintype.card I + 1 : ℝ)^Fintype.card (J × Option I) ≤ Real.exp (scalarKernelInputBudget I J R) := by
  let Q : ℝ := 10 + (Fintype.card I : ℝ) + Fintype.card J + Fintype.card (J × Option I) + R
  have hq0 : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ Fintype.card J := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ Fintype.card (J × Option I) := Nat.cast_nonneg _
  obtain ⟨hP, hn, hb, hK, hT, hε, hC, hS⟩ := scalarKernel_polynomial_envelope (Q := Q)
    hq0 hj0 hN0 hR (by dsimp [Q]; linarith) (by dsimp [Q]; linarith)
    (by dsimp [Q]; linarith) (by dsimp [Q]; linarith) (by dsimp [Q]; linarith)
  have hPE : 16 * Q^3 ≤ Real.exp (16 * Q^3) := by linarith [Real.add_one_le_exp (16 * Q^3)]
  have hnE : (Fintype.card I + 1 : ℝ) ≤ Real.exp (Fintype.card I + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I + 1 : ℝ)]
  have hbE : ((D * ((Fintype.card I + 1) * M) : ℕ) : ℝ) ≤
      Real.exp (2 * R + (Fintype.card I + 1 : ℝ)) := by
    push_cast
    calc
      _ ≤ Real.exp R * (Real.exp (Fintype.card I + 1 : ℝ) * Real.exp R) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  refine ⟨hP, hn.trans hPE, hbE.trans (Real.exp_le_exp.mpr hb), ?_, ?_, ?_, ?_, ?_⟩
  · exact (coordinateDeterminantVariation_le_exp I _).trans (Real.exp_le_exp.mpr hK)
  · exact (scalarKernelTailConstant_le_exp I J).trans (Real.exp_le_exp.mpr hT)
  · exact (scalarKernelAdjustedAccuracy_inv_le_exp I J M D hη hM hD hηR).trans (Real.exp_le_exp.mpr hε)
  · exact (scalarKernelMinorConstant_le_exp I J _).trans (Real.exp_le_exp.mpr hC)
  · exact (scalarKernelMinorScale_le_exp I _).trans (Real.exp_le_exp.mpr hS)


theorem scalarKernelCutoff_le_exp (I J : Type*) [Fintype I] [Nonempty I] [Fintype J]
    {M D : ℕ} {R η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) (hR : 0 ≤ R)
    (hMR : (M : ℝ) ≤ Real.exp R) (hDR : (D : ℝ) ≤ Real.exp R) (hηR : η⁻¹ ≤ Real.exp R) :
    (scalarKernelCutoff I J M D η : ℝ) ≤ Real.exp (scalarKernelLogarithmicBudget I J R) := by
  obtain ⟨hP, hn, hb, hK, hT, hε, hC, hS⟩ := scalarKernelInputBudget_bounds I J M D hR hη hMR hDR hηR
  exact scalarKernelCutoff_le_exp_of_bounds I J hM hD hη hP hn hb hK hT hε hC hS

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalDetectedScaleInputBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem natCeil_le_exp_succ_of_le {x p : ℝ} (hp : 0 ≤ p) (hx : x ≤ Real.exp p) :
    (⌈x⌉₊ : ℝ) ≤ Real.exp (p+1) := by
  calc
    _ ≤ (⌈Real.exp p⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hx
    _ ≤ Real.exp p+1 := (Nat.ceil_lt_add_one (Real.exp_pos p).le).le
    _ = 1+Real.exp p := add_comm _ _
    _ ≤ _ := one_add_le_exp_succ hp le_rfl

end Erdos3

end

section

namespace Erdos3

theorem slicedDetectionGain_lower (s C count : ℕ) {p q a α : ℝ}
    (hα : Real.exp (-a) ≤ α) :
    Real.exp (-slicedDetectionGainLog s C count p q a) ≤
      (Real.exp (-((5 * p + 20) * count + p + 2)) * (α / 2)) *
        Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) := by
  have hhalf : Real.exp (-(a + 1)) ≤ α / 2 := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hh : 2 * Real.exp (-(a + 1)) ≤ Real.exp (-a) := by
      calc
        _ ≤ Real.exp 1 * Real.exp (-(a + 1)) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    linarith
  calc
    _ = (Real.exp (-((5 * p + 20) * count + p + 2)) * Real.exp (-(a + 1))) *
          Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold slicedDetectionGainLog
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hhalf (Real.exp_nonneg _)) (by positivity)

theorem slicedDetection_kernel_cutoff_bound_s2_oai (s C count : ℕ) (G : Type*) [Fintype G]
    {p q a α : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a)
    (hα : Real.exp (-a) ≤ α) :
    let gain := (Real.exp (-((5 * p + 20) * count + p + 2)) * (α / 2)) *
      Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1))
    let gainLog := slicedDetectionGainLog s C count p q a
    let R := gainLog + p + 4
    (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊ (gain / 2) : ℝ) ≤
      Real.exp (scalarKernelLogarithmicBudget (Fin (s + 1)) G R) := by
  intro gain gainLog R
  have hgain := slicedDetectionGain_lower s C count (p := p) (q := q) hα
  have hg : 0 < gain := (Real.exp_pos _).trans_le hgain
  have hlog : 0 ≤ gainLog := slicedDetectionGainLog_nonneg s C count hp hq ha
  have hR : 0 ≤ R := by dsimp only [R]; linarith
  have hD : (⌈Real.exp (p + 1)⌉₊ : ℝ) ≤ Real.exp (p + 2) := by
    simpa only [add_assoc, one_add_one_eq_two] using
      natCeil_le_exp_succ_of_le (show 0 ≤ p + 1 by linarith) (le_refl (Real.exp (p + 1)))
  have hη : (gain / 2)⁻¹ ≤ Real.exp R := by
    have hgi : gain⁻¹ ≤ Real.exp gainLog := by
      simpa only [← Real.exp_neg, neg_neg] using (inv_le_inv₀ hg (Real.exp_pos _)).mpr hgain
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * gain⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1 * Real.exp gainLog := mul_le_mul htwo hgi (inv_nonneg.mpr hg.le) (Real.exp_nonneg _)
      _ = Real.exp (1 + gainLog) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [R]; linarith)
  exact scalarKernelCutoff_le_exp (Fin (s + 1)) G (by decide)
    (Nat.ceil_pos.mpr (Real.exp_pos _)) (half_pos hg) hR
    (by simpa only [Nat.cast_one] using Real.one_le_exp hR)
    (hD.trans (Real.exp_le_exp.mpr (by dsimp only [R]; linarith))) hη

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.slicedDetection_kernel_cutoff_bound_s2_oai.{u_1} := @OAI.Erdos3.slicedDetection_kernel_cutoff_bound_s2_oai.{u_1}
