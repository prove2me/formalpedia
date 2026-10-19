-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineSourceRadius_uniform_floor_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:12:44.326556+00:00
-- url     : https://prove2.me/submissions/acd871b5-6dd6-42c6-b912-f01c9e471963

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B112
import Definitions.Def_OAIE3v2B162

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem productMinorEntryBound_nonneg (q h : ℕ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorEntryBound q h C R := by
  unfold productMinorEntryBound
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productMinorPartialBound_nonneg (q h : ℕ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorPartialBound q h C R := by
  unfold productMinorPartialBound
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

theorem productMinorDeterminantDerivativeBound_nonneg (n j q h : ℕ) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorDeterminantDerivativeBound n j q h C R := by
  have he := productMinorEntryBound_nonneg q h hC hR
  have hd := productMinorPartialBound_nonneg q h hC hR
  unfold productMinorDeterminantDerivativeBound
  positivity

end Erdos3

end

section

namespace Erdos3

theorem boolean_minor_parameter_count_pos (O α : Type*) [Fintype O] [Nonempty O]
    [Fintype α] {h : ℕ} (hh : 0 < h) :
    0 < Fintype.card O * (h * (Fintype.card α + 1)) :=
  Nat.mul_pos Fintype.card_pos (Nat.mul_pos hh (Nat.succ_pos _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeBoundaryConstant_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < scalarCubeBoundaryConstant α := by
  have h := scalarCubeDomainDensity_pos α
  unfold scalarCubeBoundaryConstant
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

theorem regularizationRadius_inverse_le_exp {L ε P : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) (hP : 0 ≤ P)
    (hLP : L ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (regularizationRadius L ε)⁻¹ ≤ Real.exp (2*P+2) := by
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 2*P+2)
  · have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      (ε/(2*(1+L)))⁻¹ = 2*(1+L)*ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1*Real.exp (P+1)*Real.exp P := by
        gcongr
        exact one_add_le_exp_succ hP hLP
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeBoundaryLogBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem scalarCubeProductBoundaryRadius_pos (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] {η : ℝ} (hη : 0 < η) : 0 < scalarCubeProductBoundaryRadius ι α η :=
  div_pos hη (mul_pos (scalarCubeBoundaryConstant_pos α) (by positivity))

theorem scalarCubeProductBoundaryRadius_derivative (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] (A : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    (∑ _i : ι, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * A /
      scalarCubeProductBoundaryRadius ι α η) ≤
      scalarCubeProductDerivativeConstant α A * ((Fintype.card ι : ℝ) + 1) ^ 2 / η := by
  have hC := scalarCubeBoundaryConstant_pos α
  have hm : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have he : (∑ _i : ι, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * A /
      scalarCubeProductBoundaryRadius ι α η) =
      scalarCubeProductDerivativeConstant α A * (Fintype.card ι : ℝ) *
        ((Fintype.card ι : ℝ) + 1) / η := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      scalarCubeProductBoundaryRadius, scalarCubeProductDerivativeConstant]
    field_simp
  rw [he]
  have hB : 0 ≤ scalarCubeProductDerivativeConstant α A := by
    unfold scalarCubeProductDerivativeConstant
    positivity
  apply div_le_div_of_nonneg_right _ hη.le
  have h := mul_le_mul_of_nonneg_left
    (show (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1) ≤
      ((Fintype.card ι : ℝ) + 1) ^ 2 by nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]) hB
  simpa only [mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem scalarCubeBoundaryConstant_le_exp (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeBoundaryConstant I ≤ Real.exp (scalarCubeBoundaryLog (Fintype.card I)) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ)^2 := by norm_num
      _ ≤ (Real.exp 1)^2 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hd := scalarCubeDomainDensity_le_exp I
  have hd0 := (scalarCubeDomainDensity_pos I).le
  unfold scalarCubeBoundaryConstant
  calc
    _ ≤ Real.exp 2*Real.exp (((Fintype.card I : ℝ)+1)^2)*((Real.exp 1)^Fintype.card I)^2 := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold scalarCubeBoundaryLog
      ring

theorem scalarCubeProductDerivativeConstant_le_exp (I : Type*) [Fintype I] [DecidableEq I]
    (A : ℝ≥0) {P : ℝ} (hA : (A : ℝ) ≤ Real.exp P) :
    scalarCubeProductDerivativeConstant I A ≤ Real.exp (scalarCubeDerivativeLog (Fintype.card I) P) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq : (Fintype.card I : ℝ)+1 ≤ Real.exp (Fintype.card I) := Real.add_one_le_exp _
  have hC := scalarCubeBoundaryConstant_le_exp I
  have hC0 := (scalarCubeBoundaryConstant_pos I).le
  unfold scalarCubeProductDerivativeConstant
  push_cast
  calc
    _ ≤ (Real.exp 1*(Real.exp 1)^Fintype.card I)*(Real.exp (Fintype.card I))^2*
        Real.exp P*Real.exp (scalarCubeBoundaryLog (Fintype.card I)) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold scalarCubeDerivativeLog
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanSelectedDerivativeBound
namespace OAI

section

namespace Erdos3

theorem productMinorInverseBound_nonneg (j q h : ℕ) {C R κ : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hκ : 0 ≤ κ) :
    0 ≤ productMinorInverseBound j q h C R κ := by
  have hH := productMinorEntryBound_nonneg q h hC hR
  unfold productMinorInverseBound
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointBooleanPolynomialPerturbation
namespace OAI

section

namespace Erdos3

theorem polynomialC2BoxBudget_nonneg (N d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ polynomialC2BoxBudget N d C := by unfold polynomialC2BoxBudget; positivity

end Erdos3

end

section

namespace Erdos3

theorem polynomialC2BoxBudget_le_exp (N d : ℕ) {C p : ℝ} (hC : 0 ≤ C) (hCp : C ≤ Real.exp p) :
    polynomialC2BoxBudget N d C ≤ Real.exp (3 * (N : ℝ) * d + p) := by
  have hbase : 1 + (N : ℝ) * d ≤ Real.exp ((N : ℝ) * d) := by
    simpa only [add_comm] using Real.add_one_le_exp ((N : ℝ) * d)
  have hdegree : (d + 1 : ℝ) ≤ Real.exp (d : ℝ) := Real.add_one_le_exp _
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + (N : ℝ) * d) hbase 2
  have hterms := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (d + 1 : ℝ)) hdegree N
  calc
    _ ≤ (Real.exp ((N : ℝ) * d)) ^ 2 * (Real.exp (d : ℝ)) ^ N * Real.exp p :=
      mul_le_mul (mul_le_mul hpow hterms (by positivity) (by positivity)) hCp hC (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      norm_num
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BooleanJetMassBudget
namespace OAI

section

namespace Erdos3

theorem booleanJetMassBudget_nonneg (q h : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    0 ≤ booleanJetMassBudget q h W := by unfold booleanJetMassBudget; positivity

end Erdos3

end

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


end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalCubeMinorThreshold
namespace OAI

section

namespace Erdos3

theorem cubeMinorProbabilityConstant_pos (O α : Type*) [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ) :
    0 < cubeMinorProbabilityConstant O α h N d :=
  mul_pos (pow_pos (scalarCubeDomainDensity_pos α) _) (multivariateSublevelConstant_pos hN d)

theorem cubeMinorProbabilityScale_pos (O : Type*) [Fintype O] (N d : ℕ)
    {c₀ : ℝ} (hc₀ : 0 < c₀) : 0 < cubeMinorProbabilityScale O N d c₀ := by
  unfold cubeMinorProbabilityScale
  positivity

theorem cubeMinorThreshold_pos (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ η : ℝ} (hc₀ : 0 < c₀) (hη : 0 < η) :
    0 < cubeMinorThreshold J O α h N d c₀ η :=
  polynomialSublevelThreshold_pos _ _ (cubeMinorProbabilityConstant_pos O α h hN d).le
    (cubeMinorProbabilityScale_pos O N d hc₀).le hη

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem canonicalCubeMinorThreshold_pos (J O α : Type*)
    [Fintype J] [Fintype O] [Nonempty O] [Fintype α] [DecidableEq α]
    {h : ℕ} (hh : 0 < h) {c₀ η : ℝ} (hc₀ : 0 < c₀) (hη : 0 < η) :
    0 < canonicalCubeMinorThreshold J O α h c₀ η :=
  cubeMinorThreshold_pos J O α h (boolean_minor_parameter_count_pos O α hh) _ hc₀ hη

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.BooleanCanonicalLogBudget
namespace OAI

section

namespace Erdos3

theorem productMinorEntryBound_le_exp (q h : ℕ) {C P : ℝ}
    (hC : 0 ≤ C) (hCP : C ≤ Real.exp P) :
    productMinorEntryBound q h C 1 ≤ Real.exp (productMinorEntryLog q h P) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq : (q : ℝ)+1 ≤ Real.exp q := Real.add_one_le_exp _
  have hp : ((q : ℝ)+1)^(h-1) ≤ ((q : ℝ)+1)^h :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) q]) (Nat.sub_le _ _)
  unfold productMinorEntryBound
  rw [mul_one]
  calc
    _ ≤ C*((2 : ℝ)^h*((q : ℝ)+1)^h) := by gcongr
    _ ≤ Real.exp P*((Real.exp 1)^h*(Real.exp q)^h) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [productMinorEntryLog, mul_one]
      ring

theorem productMinorPartialBound_le_exp (q h : ℕ) {C P : ℝ}
    (_hC : 0 ≤ C) (hCP : C ≤ Real.exp P) :
    productMinorPartialBound q h C 1 ≤ Real.exp (productMinorPartialLog q h P) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq : (q : ℝ)+1 ≤ Real.exp q := Real.add_one_le_exp _
  have hh : (h : ℝ) ≤ Real.exp h := by linarith [Real.add_one_le_exp (h : ℝ)]
  unfold productMinorPartialBound
  rw [mul_one]
  calc
    _ ≤ Real.exp P*((Real.exp 1)^h*(Real.exp h*(Real.exp q)^h)) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [productMinorPartialLog, mul_one]
      ring

theorem productMinorInverseBound_le_exp (j q h : ℕ) {C κ P E : ℝ}
    (hC : 0 ≤ C) (hκ : 0 < κ) (hCP : C ≤ Real.exp P) (hκE : κ⁻¹ ≤ Real.exp E) :
    productMinorInverseBound j q h C 1 κ ≤ Real.exp (productMinorInverseLog j q h P E) := by
  have hj : (j : ℝ) ≤ Real.exp j := by linarith [Real.add_one_le_exp (j : ℝ)]
  have hf := factorial_le_exp_sq j
  have he := productMinorEntryBound_le_exp q h hC hCP
  have he0 := productMinorEntryBound_nonneg q h hC zero_le_one
  unfold productMinorInverseBound
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp j*(Real.exp ((j : ℝ)^2)*(Real.exp (productMinorEntryLog q h P))^(j-1)*Real.exp E) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold productMinorInverseLog
      ring

theorem productMinorDerivativeBound_le_exp (n j q h : ℕ) {C P : ℝ}
    (hC : 0 ≤ C) (hCP : C ≤ Real.exp P) :
    productMinorDerivativeBound n j q h C 1 ≤ Real.exp (productMinorDerivativeLog n j q h P) := by
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hj : (j : ℝ) ≤ Real.exp j := by linarith [Real.add_one_le_exp (j : ℝ)]
  have hb := productMinorPartialBound_le_exp q h hC hCP
  have hb0 := productMinorPartialBound_nonneg q h hC zero_le_one
  calc
    _ ≤ Real.exp n*(Real.exp j*Real.exp (productMinorPartialLog q h P)) := by
      unfold productMinorDerivativeBound
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; unfold productMinorDerivativeLog; ring

theorem productMinorDeterminantDerivativeBound_le_exp (n j q h : ℕ) {C P : ℝ}
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hCP : C ≤ Real.exp P) :
    productMinorDeterminantDerivativeBound n j q h C 1 ≤ Real.exp (productMinorDeterminantLog n j q h P) := by
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hj : (j : ℝ) ≤ Real.exp j := by linarith [Real.add_one_le_exp (j : ℝ)]
  have hf := factorial_le_exp_sq j
  have hb := productMinorPartialBound_le_exp q h hC hCP
  have hb0 := productMinorPartialBound_nonneg q h hC zero_le_one
  have he := one_add_le_exp_succ (show 0 ≤ productMinorEntryLog q h P by unfold productMinorEntryLog; positivity)
    (productMinorEntryBound_le_exp q h hC hCP)
  have he0 := productMinorEntryBound_nonneg q h hC zero_le_one
  calc
    _ ≤ Real.exp n*(Real.exp ((j : ℝ)^2)*(Real.exp j*Real.exp (productMinorPartialLog q h P)*
        (Real.exp (productMinorEntryLog q h P+1))^j)) := by
      unfold productMinorDeterminantDerivativeBound
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold productMinorDeterminantLog
      ring

end Erdos3

end

section

namespace Erdos3

theorem cubeMinorProbabilityConstant_le_exp (O α : Type*) [Fintype O] [Fintype α] [DecidableEq α]
    (h N d : ℕ) (hN : 0 < N) (hd : 0 < d) :
    cubeMinorProbabilityConstant O α h N d ≤
      Real.exp (cubeMinorConstantLog (Fintype.card O) (Fintype.card α) h N d) := by
  have hden := scalarCubeDomainDensity_le_exp α
  have hden0 := (scalarCubeDomainDensity_pos α).le
  have hc := multivariateSublevelConstant_le_exp N d hd
  have hc0 := (multivariateSublevelConstant_pos hN d).le
  unfold cubeMinorProbabilityConstant
  calc
    _ ≤ (Real.exp (((Fintype.card α : ℝ)+1)^2))^Fintype.card (O × Fin h)*
        Real.exp (3*(N : ℝ)+(d+1 : ℝ)+d*(8+(d+1 : ℝ))) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, cubeMinorConstantLog]
      ring

theorem cubeMinorProbabilityScale_le_exp (O : Type*) [Fintype O] (N d : ℕ)
    {c₀ P : ℝ} (hc₀ : 0 < c₀) (hcP : c₀⁻¹ ≤ Real.exp P) :
    cubeMinorProbabilityScale O N d c₀ ≤ Real.exp (cubeMinorScaleLog (Fintype.card O) N d P) := by
  have hd : (d : ℝ)+1 ≤ Real.exp d := Real.add_one_le_exp _
  unfold cubeMinorProbabilityScale
  rw [div_eq_mul_inv, ← inv_pow]
  calc
    _ ≤ (Real.exp d)^N*(Real.exp P)^Fintype.card O := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; rfl

theorem cubeMinorThreshold_inverse_le_exp (J O α : Type*)
    [Fintype J] [Fintype O] [Fintype α] [DecidableEq α]
    (h N d : ℕ) (hN : 0 < N) (hd : 0 < d) {c₀ η P E : ℝ}
    (hc₀ : 0 < c₀) (hη : 0 < η) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcP : c₀⁻¹ ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E) :
    (cubeMinorThreshold J O α h N d c₀ η)⁻¹ ≤
      Real.exp (cubeMinorThresholdLog (Fintype.card J) (Fintype.card O) (Fintype.card α) h N d P E) := by
  exact polynomialSublevelThreshold_inverse_le_exp (N*d) (Fintype.card J)
    (cubeMinorProbabilityConstant_pos O α h hN d).le (cubeMinorProbabilityScale_pos O N d hc₀).le hη
    (by unfold cubeMinorConstantLog; positivity) (by unfold cubeMinorScaleLog; positivity) hE
    (cubeMinorProbabilityConstant_le_exp O α h N d hN hd)
    (cubeMinorProbabilityScale_le_exp O N d hc₀ hcP) hηE

theorem canonicalCubeMinorThreshold_inverse_le_exp (J O α : Type*)
    [Fintype J] [Fintype O] [Nonempty O] [Fintype α] [DecidableEq α]
    (h : ℕ) (hh : 0 < h) {c₀ η P E : ℝ}
    (hc₀ : 0 < c₀) (hη : 0 < η) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcP : c₀⁻¹ ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E) :
    (canonicalCubeMinorThreshold J O α h c₀ η)⁻¹ ≤
      Real.exp (cubeMinorThresholdLog (Fintype.card J) (Fintype.card O) (Fintype.card α) h
        (cubeMinorVariableCount O α h) (cubeMinorDegree O h) P E) :=
  cubeMinorThreshold_inverse_le_exp J O α h (cubeMinorVariableCount O α h) (cubeMinorDegree O h)
    (boolean_minor_parameter_count_pos O α hh)
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) hc₀ hη hP hE hcP hηE

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem canonicalBooleanMinorLog_nonneg (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ canonicalBooleanMinorLog O α h P E := by
  unfold canonicalBooleanMinorLog cubeMinorThresholdLog cubeMinorScaleLog cubeMinorConstantLog
  positivity

theorem jointBooleanDerivativeLog_nonneg {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P := by
  apply add_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro d _
  unfold productMinorDerivativeLog productMinorPartialLog
  positivity

theorem jointBooleanDerivativeBudget_le_exp {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) {P : ℝ} (hP : 0 ≤ P)
    (hCP : ∀ d, C d ≤ Real.exp P) :
    (jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C : ℝ) ≤
      Real.exp (jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P) := by
  unfold jointBooleanDerivativeBudget jointBooleanDerivativeLog
  rw [NNReal.coe_sum]
  apply sum_le_exp_card_add_sum
  · intro d
    unfold productMinorDerivativeLog productMinorPartialLog
    positivity
  · intro d
    exact coe_toNNReal_le_exp (productMinorDerivativeBound_le_exp _ _ _ _ (hC d) (hCP d))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointBooleanWeightBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

theorem jointBooleanWeightBudget_nonneg (h : D → ℕ) (C : D → ℝ) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 ≤ r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 ≤ κ d) :
    0 ≤ jointBooleanWeightBudget (O := O) (α := α) h C A T r κ := by
  apply Finset.sum_nonneg
  intro d _
  exact add_nonneg (Finset.sum_nonneg (fun i _ => div_nonneg (by positivity) (hr d i)))
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (div_nonneg A.coe_nonneg (hκ d))
      (productMinorDeterminantDerivativeBound_nonneg _ _ _ _ (hC d) zero_le_one)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleBudget
namespace OAI

section

namespace Erdos3

theorem polynomialPerturbationScale_spec {K M Q τ : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (m : ℕ) :
    let t := polynomialPerturbationScale K M Q τ m
    0 < t ∧ t ≤ 1 ∧ K * (t * M) ≤ 1 / 2 ∧ t * M ≤ 1 ∧
      4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M))) ≤ τ := by
  let t := polynomialPerturbationScale K M Q τ m
  have ht : 0 < t := by dsimp [t, polynomialPerturbationScale]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htK : t ≤ 1 / (2 * (1 + K) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htQ : t ≤ τ ^ 2 / (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hden : t * (2 * (1 + K) * (1 + M)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp htK
  have h2KM : 2 * K * M ≤ 2 * (1 + K) * (1 + M) := by nlinarith
  have hMden : M ≤ 2 * (1 + K) * (1 + M) := by nlinarith [mul_nonneg hK hM]
  have hsmall : K * (t * M) ≤ 1 / 2 := by
    have hh := (mul_le_mul_of_nonneg_left h2KM ht.le).trans hden
    nlinarith
  have hsecond : t * M ≤ 1 := (mul_le_mul_of_nonneg_left hMden ht.le).trans hden
  refine ⟨ht, ht1, hsmall, hsecond, ?_⟩
  have hdenQ : t * (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) ≤ τ ^ 2 :=
    (le_div_iff₀ (by positivity)).mp htQ
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hm2 : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have hpoly : 16 * (m : ℝ) ^ 2 * Q * (1 + M) ≤
      16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M) := by
    gcongr
    linarith
  have hb := (mul_le_mul_of_nonneg_left hpoly ht.le).trans hdenQ
  have hroot := Real.sq_sqrt (show 0 ≤ Q * (t * (1 + M)) by positivity)
  have hroot0 := Real.sqrt_nonneg (Q * (t * (1 + M)))
  have hsquare : (4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M)))) ^ 2 ≤ τ ^ 2 := by
    calc
      _ = t * (16 * (m : ℝ) ^ 2 * Q * (1 + M)) := by
        rw [mul_pow, mul_pow, hroot]
        ring
      _ ≤ _ := hb
  nlinarith [mul_nonneg (show 0 ≤ 4 * (m : ℝ) by positivity) hroot0]

end Erdos3

end

section

namespace Erdos3

theorem polynomialPerturbationScale_inv_le {K M Q τ P : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (hP : 0 ≤ P)
    (m : ℕ) (hKP : 1 + K ≤ Real.exp P) (hMP : 1 + M ≤ Real.exp P)
    (hQP : 1 + Q ≤ Real.exp P) (hmP : (m : ℝ) + 1 ≤ Real.exp P)
    (hτP : τ⁻¹ ≤ Real.exp P) :
    (polynomialPerturbationScale K M Q τ m)⁻¹ ≤ 16 * Real.exp (6 * P) := by
  let E := 16 * Real.exp (6 * P)
  have hE : 0 < E := by dsimp [E]; positivity
  have hE1 : 1 ≤ E := by
    have he : 1 ≤ Real.exp (6 * P) := Real.one_le_exp_iff.mpr (by positivity)
    dsimp [E]
    linarith
  have hD1 : 2 * (1 + K) * (1 + M) ≤ E := by
    calc
      _ ≤ 2 * Real.exp P * Real.exp P := by gcongr
      _ = 2 * Real.exp (2 * P) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ 16 * Real.exp (6 * P) := by
        have he : Real.exp (2 * P) ≤ Real.exp (6 * P) := Real.exp_le_exp.mpr (by linarith)
        nlinarith [Real.exp_pos (6 * P)]
  have hD2 : (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) / τ ^ 2 ≤ E := by
    calc
      _ = 16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M) * (τ⁻¹) ^ 2 := by
        rw [div_eq_mul_inv, inv_pow]
      _ ≤ 16 * (Real.exp P) ^ 2 * Real.exp P * Real.exp P * (Real.exp P) ^ 2 := by gcongr
      _ = E := by
        rw [← Real.exp_nat_mul]
        simp only [mul_assoc, ← Real.exp_add]
        dsimp [E]
        congr 2
        ring
  have hsmall : 1 / E ≤ polynomialPerturbationScale K M Q τ m := by
    unfold polynomialPerturbationScale
    refine le_min ?_ (le_min ?_ ?_)
    · exact (div_le_iff₀ hE).mpr (by simpa using hE1)
    · exact one_div_le_one_div_of_le (by positivity) hD1
    · have he := one_div_le_one_div_of_le
        (by positivity : 0 < (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) / τ ^ 2) hD2
      simpa only [one_div_div] using he
  have hi := one_div_le_one_div_of_le (div_pos zero_lt_one hE) hsmall
  simpa only [one_div, inv_inv] using hi

theorem polynomialPerturbationScale_log_inv_le {K M Q τ P : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (hP : 0 ≤ P)
    (m : ℕ) (hKP : 1 + K ≤ Real.exp P) (hMP : 1 + M ≤ Real.exp P)
    (hQP : 1 + Q ≤ Real.exp P) (hmP : (m : ℝ) + 1 ≤ Real.exp P)
    (hτP : τ⁻¹ ≤ Real.exp P) :
    Real.log (polynomialPerturbationScale K M Q τ m)⁻¹ ≤ Real.log 16 + 6 * P := by
  have ht := (polynomialPerturbationScale_spec hK hM hQ hτ m).1
  have hi := polynomialPerturbationScale_inv_le hK hM hQ hτ hP m hKP hMP hQP hmP hτP
  have he := Real.log_le_log (inv_pos.mpr ht) hi
  simpa only [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] using he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanPolynomialLogBudget
namespace OAI

section

namespace Erdos3

theorem booleanJetMassBudget_le_exp (q h : ℕ) {W P : ℝ}
    (hW : 0 ≤ W) (hWP : W ≤ Real.exp P) :
    booleanJetMassBudget q h W ≤ Real.exp (booleanJetMassLog q h P) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq : (q : ℝ)+1 ≤ Real.exp q := Real.add_one_le_exp _
  unfold booleanJetMassBudget
  calc
    _ ≤ (Real.exp 1)^q*(Real.exp P*(Real.exp q)^h) := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; unfold booleanJetMassLog; ring

theorem booleanToleranceC2Log_nonneg {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ booleanToleranceC2Log (B := B) (α := α) Z h degree P := by
  unfold booleanToleranceC2Log booleanJetMassLog
  positivity

theorem booleanToleranceC2_le_exp {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) {Csum Wsum P : ℝ}
    (hC : 0 ≤ Csum) (hW : 0 ≤ Wsum) (hP : 0 ≤ P)
    (hCP : Csum ≤ Real.exp P) (hWP : Wsum ≤ Real.exp P) :
    booleanToleranceC2 (B := B) (α := α) Z h degree Csum Wsum ≤
      Real.exp (booleanToleranceC2Log (B := B) (α := α) Z h degree P) := by
  have hb : 0 ≤ booleanJetMassLog (Fintype.card α) degree P := by unfold booleanJetMassLog; positivity
  have hs := add_le_exp_add_one hb hb (booleanJetMassBudget_le_exp _ _ hC hCP) (booleanJetMassBudget_le_exp _ _ hW hWP)
  have hs' : booleanJetMassBudget (Fintype.card α) degree Csum+booleanJetMassBudget (Fintype.card α) degree Wsum ≤
      Real.exp (2*booleanJetMassLog (Fintype.card α) degree P+1) := by
    have he : booleanJetMassLog (Fintype.card α) degree P+
        booleanJetMassLog (Fintype.card α) degree P+1 =
        2*booleanJetMassLog (Fintype.card α) degree P+1 := by ring
    simpa only [he] using hs
  exact polynomialC2BoxBudget_le_exp _ _
    (add_nonneg (booleanJetMassBudget_nonneg _ _ hC) (booleanJetMassBudget_nonneg _ _ hW)) hs'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

omit [Fintype D] in
theorem unitProfilePrincipalSize_pos (d : D) : 0 < unitProfilePrincipalSize (B := B) d :=
  principalProfileSize_pos zero_lt_one _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DivergenceExponentialBounds
namespace OAI

section

namespace Erdos3

theorem translationDivergence_le_exp (m n : ℕ) {K H S a b c : ℝ}
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hKa : K ≤ Real.exp a) (hHb : H ≤ Real.exp b) (hSc : S ≤ Real.exp c) :
    (m : ℝ)*(K*S+n*(K^2*H)) ≤ Real.exp (m+n+3*a+b+c+1) := by
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hm : (m : ℝ) ≤ Real.exp m := by linarith [Real.add_one_le_exp (m : ℝ)]
  have hks : K*S ≤ Real.exp (a+c) := by rw [Real.exp_add]; gcongr
  have hnk : (n : ℝ)*(K^2*H) ≤ Real.exp (n+2*a+b) := by
    calc
      _ ≤ Real.exp n*((Real.exp a)^2*Real.exp b) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hs := add_le_exp_add_one (show 0 ≤ a+c by positivity) (show 0 ≤ (n : ℝ)+2*a+b by positivity) hks hnk
  calc
    _ ≤ Real.exp m*Real.exp (a+c+(n+2*a+b)+1) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem perturbationDivergence_le_exp (n : ℕ) {K H S a b c : ℝ}
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hKa : K ≤ Real.exp a) (hHb : H ≤ Real.exp b) (hSc : S ≤ Real.exp c) :
    1+2*K*S+(n : ℝ)*((2*K)^2*(H+1)) ≤ Real.exp (n+3*a+b+c+6) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have h2k : 2*K ≤ Real.exp (a+1) := by
    calc
      _ ≤ Real.exp 1*Real.exp a := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hh1 : H+1 ≤ Real.exp (b+1) := by simpa only [add_comm] using one_add_le_exp_succ hb hHb
  have hks : 2*K*S ≤ Real.exp (a+c+1) := by
    calc
      _ ≤ Real.exp (a+1)*Real.exp c := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hnk : (n : ℝ)*((2*K)^2*(H+1)) ≤ Real.exp (n+2*a+b+3) := by
    calc
      _ ≤ Real.exp n*((Real.exp (a+1))^2*Real.exp (b+1)) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hs := add_le_exp_add_one (show 0 ≤ a+c+1 by positivity) (show 0 ≤ (n : ℝ)+2*a+b+3 by positivity) hks hnk
  have hsum := one_add_le_exp_succ (show 0 ≤ a+c+1+(n+2*a+b+3)+1 by positivity) hs
  calc
    _ = 1+(2*K*S+(n : ℝ)*((2*K)^2*(H+1))) := by ring
    _ ≤ Real.exp (a+c+1+(n+2*a+b+3)+1+1) := hsum
    _ = _ := by congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProfileRadiusLog
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {B : D → Type*} [∀ d, Fintype (B d)]

theorem unitProfileCoefficientLog_nonneg (A T : ℝ≥0) :
    0 ≤ unitProfileCoefficientLog (B := B) A T := by
  unfold unitProfileCoefficientLog
  positivity

theorem unitProfileCoefficientLog_bounds (A T : ℝ≥0) :
    let P := unitProfileCoefficientLog (B := B) A T
    (∀ d, (unitProfilePrincipalSize (B := B) d)⁻¹ ≤ Real.exp P) ∧
    (∀ d, 2 * unitProfilePrincipalSize (B := B) d ≤ Real.exp P) ∧
    (A : ℝ) ≤ Real.exp P ∧ (T : ℝ) ≤ Real.exp P := by
  classical
  let P := unitProfileCoefficientLog (B := B) A T
  have hP : 0 ≤ P := unitProfileCoefficientLog_nonneg A T
  have hsum : 0 ≤ ∑ d, (Fintype.card (B d) : ℝ) := by positivity
  have hB (d : D) : (Fintype.card (B d) : ℝ) ≤ ∑ e, (Fintype.card (B e) : ℝ) :=
    Finset.single_le_sum (f := fun e => (Fintype.card (B e) : ℝ))
      (fun e _ => Nat.cast_nonneg _) (Finset.mem_univ d)
  have hPE : P ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d
    change (1 / (8 * ((Fintype.card (B d) : ℝ) + 1)))⁻¹ ≤ Real.exp P
    rw [one_div, inv_inv]
    calc
      _ ≤ Real.exp 7 * Real.exp (Fintype.card (B d)) := by
        gcongr
        · linarith [Real.add_one_le_exp (7 : ℝ)]
        · exact Real.add_one_le_exp _
      _ = Real.exp (7 + (Fintype.card (B d) : ℝ)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp P := by
        apply Real.exp_le_exp.mpr
        dsimp [P, unitProfileCoefficientLog]
        linarith [hB d, A.coe_nonneg, T.coe_nonneg]
  · intro d
    apply le_trans (b := 1) _ (Real.one_le_exp hP)
    change 2 * (1 / (8 * ((Fintype.card (B d) : ℝ) + 1))) ≤ 1
    rw [← mul_div_assoc, mul_one]
    apply (div_le_one (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (B d))]
  · apply le_trans (b := P) _ hPE
    dsimp [P, unitProfileCoefficientLog]
    linarith [T.coe_nonneg]
  · apply le_trans (b := P) _ hPE
    dsimp [P, unitProfileCoefficientLog]
    linarith [A.coe_nonneg]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubeMinorGoodMass
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem affineCubeMinorThreshold_pos (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ δ η : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ) (hη : 0 < η) :
    0 < affineCubeMinorThreshold J O α h N d c₀ δ η :=
  polynomialSublevelThreshold_pos _ _
    (mul_nonneg (cubeMinorProbabilityConstant_pos O α h hN d).le (pow_nonneg (inv_nonneg.mpr hδ.le) _))
    (cubeMinorProbabilityScale_pos O N d hc₀).le hη

theorem affineCubeMinorThreshold_log_inv (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ δ η : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ) (hη : 0 < η) :
    Real.log (affineCubeMinorThreshold J O α h N d c₀ δ η)⁻¹ =
      Real.log 2 + Real.log (1 + cubeMinorProbabilityScale O N d c₀) +
        (N * d : ℕ) * Real.log (1 + 2 * (cubeMinorProbabilityConstant O α h N d * δ⁻¹ ^ N) *
          (Fintype.card J + 1 : ℝ) / η) :=
  polynomialSublevelThreshold_log_inv _ _
    (mul_nonneg (cubeMinorProbabilityConstant_pos O α h hN d).le (pow_nonneg (inv_nonneg.mpr hδ.le) _))
    (cubeMinorProbabilityScale_pos O N d hc₀).le hη

end Erdos3

end

section

namespace Erdos3

lemma log_one_add_inverse_width_pow {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (N : ℕ) :
    Real.log (1 + A * δ⁻¹ ^ N) ≤ Real.log (1 + A) + (N : ℝ) * Real.log δ⁻¹ := by
  have hi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδone
  have hp : 1 ≤ δ⁻¹ ^ N := one_le_pow₀ hi
  have hmul : 1 + A * δ⁻¹ ^ N ≤ (1 + A) * δ⁻¹ ^ N := by nlinarith
  have hlog := Real.log_le_log (show 0 < 1 + A * δ⁻¹ ^ N by positivity) hmul
  rw [Real.log_mul (by positivity : (1 + A : ℝ) ≠ 0) (by positivity : δ⁻¹ ^ N ≠ 0),
    Real.log_pow] at hlog
  exact hlog

theorem affineCubeMinorThreshold_log_inv_slice_bound (J O α : Type*) [Fintype J] [Fintype O]
    [Fintype α] [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ δ η : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    Real.log (affineCubeMinorThreshold J O α h N d c₀ δ η)⁻¹ ≤
      Real.log 2 + Real.log (1 + cubeMinorProbabilityScale O N d c₀) +
        (N * d : ℕ) * (Real.log (1 + 2 * cubeMinorProbabilityConstant O α h N d *
          (Fintype.card J + 1 : ℝ) / η) + (N : ℝ) * Real.log δ⁻¹) := by
  rw [affineCubeMinorThreshold_log_inv J O α h hN d hc₀ hδ hη]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (N * d))
  have hA : 0 ≤ 2 * cubeMinorProbabilityConstant O α h N d * (Fintype.card J + 1 : ℝ) / η :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (cubeMinorProbabilityConstant_pos O α h hN d).le)
      (by positivity)) hη.le
  have hb := log_one_add_inverse_width_pow hA hδ hδone N
  convert hb using 1
  congr 1
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineBooleanSource
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem canonicalAffineCubeMinorThreshold_pos (O α : Type*) [Fintype O] [Nonempty O]
    [Fintype α] [DecidableEq α] {h : ℕ} (hh : 0 < h) {c₀ δ η : ℝ}
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hη : 0 < η) :
    0 < canonicalAffineCubeMinorThreshold O α h c₀ δ η :=
  affineCubeMinorThreshold_pos Unit O α h (boolean_minor_parameter_count_pos O α hh) _ hc₀ hδ hη

end Erdos3

end

section

namespace Erdos3

 theorem affineCubeMinorThreshold_log_inv_relative (J O α : Type*) [Fintype J] [Fintype O]
    [Fintype α] [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ δ η : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    Real.log (affineCubeMinorThreshold J O α h N d c₀ δ η)⁻¹ ≤
      Real.log (affineCubeMinorThreshold J O α h N d c₀ 1 η)⁻¹ +
        (N * d : ℕ) * (N : ℝ) * Real.log δ⁻¹ := by
  have he := affineCubeMinorThreshold_log_inv_slice_bound J O α h hN d hc₀ hδ hδone hη
  have hb := affineCubeMinorThreshold_log_inv J O α h hN d hc₀ zero_lt_one hη
  simp only [inv_one, one_pow, mul_one] at hb
  rw [hb]
  calc
    _ ≤ _ := he
    _ = _ := by ring

 theorem canonicalAffineCubeMinorThreshold_log_inv_relative (O α : Type*) [Fintype O]
    [Nonempty O] [Fintype α] [DecidableEq α] {h : ℕ} (hh : 0 < h)
    {c₀ δ η : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    Real.log (canonicalAffineCubeMinorThreshold O α h c₀ δ η)⁻¹ ≤
      Real.log (canonicalAffineCubeMinorThreshold O α h c₀ 1 η)⁻¹ +
        (cubeMinorVariableCount O α h * cubeMinorDegree O h : ℕ) *
          (cubeMinorVariableCount O α h : ℝ) * Real.log δ⁻¹ :=
  affineCubeMinorThreshold_log_inv_relative Unit O α h
    (boolean_minor_parameter_count_pos O α hh) (cubeMinorDegree O h) hc₀ hδ hδone hη

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

 theorem canonicalAffineMinorLog_nonneg (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) {P E F : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ canonicalAffineMinorLog O α h P E F :=
  add_nonneg (canonicalBooleanMinorLog_nonneg O α h hP hE) (by positivity)

 theorem canonicalAffineCubeMinorThreshold_inverse_le_exp (O α : Type*)
    [Fintype O] [Nonempty O] [Fintype α] [DecidableEq α]
    (h : ℕ) (hh : 0 < h) {c₀ δ η P E F : ℝ}
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcP : c₀⁻¹ ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) :
    (canonicalAffineCubeMinorThreshold O α h c₀ δ η)⁻¹ ≤ Real.exp (canonicalAffineMinorLog O α h P E F) := by
  have hkpos := canonicalAffineCubeMinorThreshold_pos O α hh hc₀ hδ hη
  have hbasepos := canonicalCubeMinorThreshold_pos Unit O α hh hc₀ hη
  have hbase : (canonicalCubeMinorThreshold Unit O α h c₀ η)⁻¹ ≤
      Real.exp (canonicalBooleanMinorLog O α h P E) := by
    simpa only [Fintype.card_unique, canonicalBooleanMinorLog] using
      canonicalCubeMinorThreshold_inverse_le_exp Unit O α h hh hc₀ hη hP hE hcP hηE
  have hsame : canonicalAffineCubeMinorThreshold O α h c₀ 1 η =
      canonicalCubeMinorThreshold Unit O α h c₀ η := by
    simp only [canonicalAffineCubeMinorThreshold, canonicalCubeMinorThreshold,
      affineCubeMinorThreshold, cubeMinorThreshold, inv_one, one_pow, mul_one]
  have hlbase := Real.log_le_log (inv_pos.mpr hbasepos) hbase
  rw [Real.log_exp] at hlbase
  have hlδ := Real.log_le_log (inv_pos.mpr hδ) hδF
  rw [Real.log_exp] at hlδ
  have he := canonicalAffineCubeMinorThreshold_log_inv_relative O α hh hc₀ hδ hδone hη
  rw [hsame] at he
  have hb : Real.log (canonicalAffineCubeMinorThreshold O α h c₀ δ η)⁻¹ ≤
      canonicalAffineMinorLog O α h P E F := by
    apply he.trans
    exact add_le_add hlbase (mul_le_mul_of_nonneg_left hlδ (by positivity))
  simpa only [Real.exp_log (inv_pos.mpr hkpos)] using Real.exp_le_exp.mpr hb

 theorem jointAffineInverseLog_nonneg {D α : Type*} [Fintype D] [Fintype α]
    {O : D → Type*} [∀ d, Fintype (O d)] (h : D → ℕ) {P E F : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ jointAffineInverseLog (O := O) (α := α) h P E F := by
  apply add_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro d _
  have hk := canonicalAffineMinorLog_nonneg (O d) α (h d) hP hE hF
  unfold productMinorInverseLog productMinorEntryLog
  positivity

 theorem jointAffineBooleanInverseBudget_le_exp {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {O : D → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (c₀ C η : D → ℝ)
    (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d) (hη : ∀ d, 0 < η d)
    {δ P E F : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hηE : ∀ d, (η d)⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) :
    (jointAffineBooleanInverseBudget (O := O) (α := α) h C
      (fun d => canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)) δ : ℝ) ≤
      Real.exp (jointAffineInverseLog (O := O) (α := α) h P E F) := by
  unfold jointAffineBooleanInverseBudget jointAffineInverseLog
  rw [NNReal.coe_sum]
  apply sum_le_exp_card_add_sum
  · intro d
    have hk := canonicalAffineMinorLog_nonneg (O d) α (h d) hP hE hF
    unfold productMinorInverseLog productMinorEntryLog
    positivity
  · intro d
    apply coe_toNNReal_le_exp
    have hb := productMinorInverseBound_le_exp (Fintype.card (O d)) (Fintype.card α) (h d) (hC d)
      (canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)) (hCP d)
      (canonicalAffineCubeMinorThreshold_inverse_le_exp (O d) α (h d) (hh d)
        (hc₀ d) hδ hδone (hη d) hP hE (hcP d) (hηE d) hδF)
    calc
      _ ≤ Real.exp F * Real.exp _ := mul_le_mul hδF hb
        (productMinorInverseBound_nonneg _ _ _ (hC d) zero_le_one
          (canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)).le)
        (Real.exp_pos F).le
      _ = _ := (Real.exp_add _ _).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem affineBooleanAxisWeightLog_nonneg (B O α : Type*) [Fintype B] [Fintype O] [Fintype α]
    (h : ℕ) {P E F : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) : 0 ≤ affineBooleanAxisWeightLog B O α h P E F := by
  have hk := canonicalAffineMinorLog_nonneg O α h hP hE hF
  unfold affineBooleanAxisWeightLog scalarCubeDerivativeLog scalarCubeBoundaryLog
    productMinorDeterminantLog productMinorPartialLog productMinorEntryLog
  positivity

theorem affineBooleanAxisWeightCost_le_exp (B O α : Type*) [Fintype B] [Fintype O] [Nonempty O]
    [Fintype α] [DecidableEq α] (h : ℕ) (hh : 0 < h) {C c₀ δ η P E F : ℝ}
    (hC : 0 ≤ C) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hCP : C ≤ Real.exp P) (hcP : c₀⁻¹ ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F)
    (A T : ℝ≥0) (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P) :
    affineBooleanAxisWeightCost B O α h C A T c₀ δ η ≤ Real.exp (affineBooleanAxisWeightLog B O α h P E F) := by
  let n := Fintype.card (BlockParameter B (Fin h) α)
  let k := Fintype.card (B × Fin h)
  let b := scalarCubeDerivativeLog (Fintype.card α) P+2*k+E+1
  let m := (n : ℝ)+P+canonicalAffineMinorLog O α h P E F+
    productMinorDeterminantLog n (Fintype.card O) (Fintype.card α) h P
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hhη : (η/2)⁻¹ ≤ Real.exp (E+1) := by
    calc
      _ = 2*η⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1*Real.exp E := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hk : (k : ℝ)+1 ≤ Real.exp k := Real.add_one_le_exp _
  have hd := scalarCubeProductDerivativeConstant_le_exp α T hTP
  have hd0 : 0 ≤ scalarCubeProductDerivativeConstant α T := by
    unfold scalarCubeProductDerivativeConstant
    have := (scalarCubeBoundaryConstant_pos α).le
    positivity
  have hb : (∑ _i : B × Fin h, ((2*2^Fintype.card α : ℕ) : ℝ)*((Fintype.card α : ℝ)+1)^2*T/
      scalarCubeProductBoundaryRadius (B × Fin h) α (η/2)) ≤ Real.exp b := by
    apply (scalarCubeProductBoundaryRadius_derivative (B × Fin h) α T (half_pos hη)).trans
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp (scalarCubeDerivativeLog (Fintype.card α) P)*(Real.exp k)^2*Real.exp (E+1) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [b]; ring
  have hκ : (canonicalAffineCubeMinorThreshold O α h c₀ δ η)⁻¹ ≤
      Real.exp (canonicalAffineMinorLog O α h P E F) := by
    simpa using
      canonicalAffineCubeMinorThreshold_inverse_le_exp O α h hh hc₀ hδ hδone hη hP hE hcP hηE hδF
  have hκ0 := canonicalAffineCubeMinorThreshold_pos O α hh hc₀ hδ hη
  have hdet := productMinorDeterminantDerivativeBound_le_exp n (Fintype.card O) (Fintype.card α) h hC hP hCP
  have hdet0 := productMinorDeterminantDerivativeBound_nonneg n (Fintype.card O) (Fintype.card α) h hC zero_le_one
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hm : (n : ℝ)*((A : ℝ)/canonicalAffineCubeMinorThreshold O α h c₀ δ η*
      productMinorDeterminantDerivativeBound n (Fintype.card O) (Fintype.card α) h C 1) ≤ Real.exp m := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp n*(Real.exp P*Real.exp (canonicalAffineMinorLog O α h P E F)*
          Real.exp (productMinorDeterminantLog n (Fintype.card O) (Fintype.card α) h P)) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [m]; ring
  have hb0 : 0 ≤ b := by dsimp [b, scalarCubeDerivativeLog, scalarCubeBoundaryLog]; positivity
  have hm0 : 0 ≤ m := by
    have := canonicalAffineMinorLog_nonneg O α h hP hE hF
    dsimp [m, productMinorDeterminantLog, productMinorPartialLog, productMinorEntryLog]
    positivity
  exact add_le_exp_add_one hb0 hm0 hb hm

theorem jointAffineBooleanWeightLog_nonneg {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) {P E F : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ jointAffineBooleanWeightLog (B := B) (O := O) (α := α) h P E F :=
  add_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun d _ => affineBooleanAxisWeightLog_nonneg (B d) (O d) α (h d) hP hE hF))

theorem jointAffineBooleanWeightBudget_canonical_le_exp {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (c₀ C η : D → ℝ)
    (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d) (hη : ∀ d, 0 < η d)
    {δ P E F : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hηE : ∀ d, (η d)⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) (A T : ℝ≥0)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P) :
    jointBooleanWeightBudget (B := B) (O := O) (α := α) h C A T
      (fun d _ => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d/2))
      (fun d => canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)) ≤
      Real.exp (jointAffineBooleanWeightLog (B := B) (O := O) (α := α) h P E F) := by
  change (∑ d, affineBooleanAxisWeightCost (B d) (O d) α (h d) (C d) A T (c₀ d) δ (η d)) ≤
    Real.exp ((Fintype.card D : ℝ)+∑ d, affineBooleanAxisWeightLog (B d) (O d) α (h d) P E F)
  exact sum_le_exp_card_add_sum
    (fun d => affineBooleanAxisWeightCost (B d) (O d) α (h d) (C d) A T (c₀ d) δ (η d))
    (fun d => affineBooleanAxisWeightLog (B d) (O d) α (h d) P E F)
    (fun d => affineBooleanAxisWeightLog_nonneg (B d) (O d) α (h d) hP hE hF)
    (fun d => affineBooleanAxisWeightCost_le_exp (B d) (O d) α (h d) (hh d)
      (hC d) (hc₀ d) hδ hδone (hη d) hP hE hF (hCP d) (hcP d) (hηE d) hδF A T hAP hTP)

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

 theorem jointAffineDivergence_le_exp [DecidableEq D] [DecidableEq α]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (c₀ C η : D → ℝ)
    (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d) (hη : ∀ d, 0 < η d)
    {δ P E F : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hηE : ∀ d, (η d)⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) (A T : ℝ≥0)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P) :
    let r := fun d (_ : B d × Fin (h d)) => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
    let κ := fun d => canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)
    let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
    let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
    (jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H : ℝ) ≤
      Real.exp (jointAffineTranslationLog (B := B) (O := O) (α := α) h P E F) ∧
    jointAffineBooleanErrorBudget (O := O) (α := α) h C κ A T r δ ≤
      Real.exp (jointAffinePerturbationLog (B := B) (O := O) (α := α) h P E F) := by
  intro r κ K H
  have hK := jointAffineBooleanInverseBudget_le_exp (O := O) (α := α)
    h hh c₀ C η hc₀ hC hη hδ hδone hP hE hF hcP hCP hηE hδF
  have hH := jointBooleanDerivativeBudget_le_exp (B := B) (O := O) (α := α) h C hC hP hCP
  have hS := jointAffineBooleanWeightBudget_canonical_le_exp (B := B) (O := O) (α := α)
    h hh c₀ C η hc₀ hC hη hδ hδone hP hE hF hcP hCP hηE hδF A T hAP hTP
  have hS0 := jointBooleanWeightBudget_nonneg (B := B) (O := O) (α := α) h C hC A T r
    (fun d _ => (scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (half_pos (hη d))).le)
    κ (fun d => (canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)).le)
  have hKL := jointAffineInverseLog_nonneg (O := O) (α := α) h hP hE hF
  have hHL := jointBooleanDerivativeLog_nonneg (B := B) (O := O) (α := α) h hP
  have hSL := jointAffineBooleanWeightLog_nonneg (B := B) (O := O) (α := α) h hP hE hF
  constructor
  · have he := translationDivergence_le_exp (Fintype.card (Σ d, O d))
      (Fintype.card (JointBlockParameter B h α)) K.coe_nonneg H.coe_nonneg hS0
      hKL hHL hSL hK hH hS
    simpa only [jointAffineTranslationLog, Nat.cast_add, jointAffineBooleanTranslationBudget, NNReal.coe_mul, NNReal.coe_add,
      NNReal.coe_natCast, NNReal.coe_pow, Real.coe_toNNReal _ hS0] using he
  · exact perturbationDivergence_le_exp (Fintype.card (JointBlockParameter B h α))
      K.coe_nonneg H.coe_nonneg hS0 hKL hHL hSL hK hH hS

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

 theorem jointAffineSourceScales_log_bounds (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) {δ ε P E F : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P)
    (hηE : (ε / (12 * ((Fintype.card D : ℝ) + 1)))⁻¹ ≤ Real.exp E)
    (hεE : (ε / 3)⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) :
    let Qlog := jointAffineSourceInputLog (B := B) (O := O) (α := α) h P E F
    0 ≤ Qlog ∧
    (jointAffineSourceRadius (B := B) (O := O) (α := α) h c₀ C A T δ ε)⁻¹ ≤ Real.exp (2 * Qlog + 2) ∧
    Real.log (jointAffineSourceTolerance (B := B) (O := O) (α := α) h c₀ C A T δ ε)⁻¹ ≤
      Real.log 16 + 6 * Qlog := by
  intro Qlog
  let η : D → ℝ := fun _ => ε / (12 * ((Fintype.card D : ℝ) + 1))
  have hη : ∀ d, 0 < η d := fun _ => div_pos hε (by positivity)
  let r := jointAffineSourceBoundaryRadius (B := B) (α := α) h ε
  let κ := jointAffineSourceMinorThreshold (O := O) (α := α) h c₀ δ ε
  let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
  let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  let Q := jointAffineBooleanErrorBudget (O := O) (α := α) h C κ A T r δ
  let L := jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H
  have hdiv := jointAffineDivergence_le_exp (B := B) (O := O) (α := α) h hh c₀ C η hc₀ hC hη
    hδ hδone hP hE hF hcP hCP (fun _ => hηE) hδF A T hAP hTP
  have hk := jointAffineBooleanInverseBudget_le_exp (O := O) (α := α) h hh c₀ C η hc₀ hC hη
    hδ hδone hP hE hF hcP hCP (fun _ => hηE) hδF
  have hKL := jointAffineInverseLog_nonneg (O := O) (α := α) h hP hE hF
  have hHL := jointBooleanDerivativeLog_nonneg (B := B) (O := O) (α := α) h hP
  have hSL := jointAffineBooleanWeightLog_nonneg (B := B) (O := O) (α := α) h hP hE hF
  have hLL : 0 ≤ jointAffineTranslationLog (B := B) (O := O) (α := α) h P E F := by
    unfold jointAffineTranslationLog
    positivity
  have hQL : 0 ≤ jointAffinePerturbationLog (B := B) (O := O) (α := α) h P E F := by
    unfold jointAffinePerturbationLog
    positivity
  have hQlog : 0 ≤ Qlog := by dsimp [Qlog, jointAffineSourceInputLog]; positivity
  have hLlog : jointAffineTranslationLog (B := B) (O := O) (α := α) h P E F ≤ Qlog := by
    dsimp [Qlog, jointAffineSourceInputLog]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]
  have hKlog : jointAffineInverseLog (O := O) (α := α) h P E F + 1 ≤ Qlog := by
    dsimp [Qlog, jointAffineSourceInputLog]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]
  have hQlog' : jointAffinePerturbationLog (B := B) (O := O) (α := α) h P E F + 1 ≤ Qlog := by
    dsimp [Qlog, jointAffineSourceInputLog]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]
  have hElog : E ≤ Qlog := by
    dsimp [Qlog, jointAffineSourceInputLog]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]
  have hnlog : (Fintype.card (Σ d, O d) : ℝ) ≤ Qlog := by
    dsimp [Qlog, jointAffineSourceInputLog]; linarith
  have honeLog : 1 ≤ Qlog := by
    dsimp [Qlog, jointAffineSourceInputLog]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]
  have hLexp : (L : ℝ) ≤ Real.exp Qlog := hdiv.1.trans (Real.exp_le_exp.mpr hLlog)
  have hKexp : 1 + (K : ℝ) ≤ Real.exp Qlog :=
    (one_add_le_exp_succ hKL hk).trans (Real.exp_le_exp.mpr hKlog)
  have hQexp : 1 + Q ≤ Real.exp Qlog :=
    (one_add_le_exp_succ hQL hdiv.2).trans (Real.exp_le_exp.mpr hQlog')
  have hτexp : (ε / 3)⁻¹ ≤ Real.exp Qlog := hεE.trans (Real.exp_le_exp.mpr hElog)
  have hS0 := jointBooleanWeightBudget_nonneg (B := B) (O := O) (α := α) h C hC A T r
    (fun d _ => (scalarCubeProductBoundaryRadius_pos _ _ (half_pos (hη d))).le)
    κ (fun d => (canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)).le)
  have hQ : 0 ≤ Q := by dsimp [Q, jointAffineBooleanErrorBudget]; positivity
  refine ⟨hQlog, ?_, ?_⟩
  · have hε' : 0 < 2 * ε / 3 := by positivity
    have hε'exp : (2 * ε / 3)⁻¹ ≤ Real.exp Qlog :=
      (inv_anti₀ (by positivity : 0 < ε / 3) (by linarith : ε / 3 ≤ 2 * ε / 3)).trans hτexp
    have he := regularizationRadius_inverse_le_exp L.coe_nonneg hε' hQlog hLexp hε'exp
    have heq : jointAffineSourceRadius (B := B) (O := O) (α := α) h c₀ C A T δ ε =
        regularizationRadius L (2 * ε / 3) := by
      change min 1 (ε / (3 * (1 + (L : ℝ)))) = min 1 ((2 * ε / 3) / (2 * (1 + (L : ℝ))))
      congr 1
      field_simp
    rwa [heq]
  · exact polynomialPerturbationScale_log_inv_le K.coe_nonneg zero_le_one hQ
      (by positivity : 0 < ε / 3) hQlog (Fintype.card (Σ d, O d)) hKexp
      ((by linarith [Real.add_one_le_exp (1 : ℝ)] : (1 : ℝ) + 1 ≤ Real.exp 1).trans
        (Real.exp_le_exp.mpr honeLog)) hQexp
      ((Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr hnlog)) hτexp

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D α Z : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  [Fintype Z] [DecidableEq Z]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

omit [DecidableEq D] [∀ index, DecidableEq (B index)] [∀ index, DecidableEq (O index)] in
 theorem jointAffineSourceTolerance_pos (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    0 < jointAffineSourceTolerance (B := B) (O := O) (α := α) h c₀ C A T δ ε := by
  let η : D → ℝ := fun _ => ε / (12 * ((Fintype.card D : ℝ) + 1))
  have hη : ∀ d, 0 < η d := fun _ => div_pos hε (by positivity)
  let r := jointAffineSourceBoundaryRadius (B := B) (α := α) h ε
  let κ := jointAffineSourceMinorThreshold (O := O) (α := α) h c₀ δ ε
  have hS0 := jointBooleanWeightBudget_nonneg (B := B) (O := O) (α := α) h C hC A T r
    (fun d _ => (scalarCubeProductBoundaryRadius_pos _ _ (half_pos (hη d))).le)
    κ (fun d => (canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)).le)
  have hQ : 0 ≤ jointAffineBooleanErrorBudget (O := O) (α := α) h C κ A T r δ := by
    unfold jointAffineBooleanErrorBudget
    positivity
  exact (polynomialPerturbationScale_spec (NNReal.coe_nonneg _) zero_le_one hQ
    (by positivity : 0 < ε / 3) (Fintype.card (Σ d, O d))).1

omit [DecidableEq Z] in
 theorem jointAffineCoefficientTolerance_log_bound (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) (degree : ℕ) {Csum Wsum δ ε P E F : ℝ}
    (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum) (hCsumP : Csum ≤ Real.exp P) (hWsumP : Wsum ≤ Real.exp P)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P)
    (hηE : (ε / (12 * ((Fintype.card D : ℝ) + 1)))⁻¹ ≤ Real.exp E)
    (hεE : (ε / 3)⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) :
    Real.log (jointAffineCoefficientTolerance (Z := Z) (B := B) (O := O) (α := α)
      h c₀ C A T degree Csum Wsum δ ε)⁻¹ ≤
      Real.log 16 + 6 * jointAffineSourceInputLog (B := B) (O := O) (α := α) h P E F +
        booleanToleranceC2Log (B := B) (α := α) Z h degree P + 1 := by
  let t := jointAffineSourceTolerance (B := B) (O := O) (α := α) h c₀ C A T δ ε
  let M := booleanToleranceC2 (B := B) (α := α) Z h degree Csum Wsum
  have ht : 0 < t := jointAffineSourceTolerance_pos h hh c₀ C hc₀ hC A T hδ hε
  have hM : 0 ≤ M := polynomialC2BoxBudget_nonneg _ _
    (add_nonneg (booleanJetMassBudget_nonneg _ _ hCsum) (booleanJetMassBudget_nonneg _ _ hWsum))
  have hraw := (jointAffineSourceScales_log_bounds (B := B) (O := O) (α := α) h hh c₀ C hc₀ hC A T hδ hδone hε hP hE hF
    hcP hCP hAP hTP hηE hεE hδF).2.2
  have hMexp := booleanToleranceC2_le_exp (B := B) (α := α) Z h degree hCsum hWsum hP hCsumP hWsumP
  have hMlog := Real.log_le_log (by positivity : 0 < 1 + M)
    (one_add_le_exp_succ (booleanToleranceC2Log_nonneg (B := B) (α := α) Z h degree hP) hMexp)
  rw [Real.log_exp] at hMlog
  change Real.log (t / (1 + M))⁻¹ ≤ _
  rw [inv_div, div_eq_mul_inv, Real.log_mul (by positivity : (1 + M : ℝ) ≠ 0) (inv_ne_zero ht.ne')]
  linarith

end Erdos3

end

section

namespace Erdos3
open scoped NNReal BigOperators Classical

 theorem affineDividedAccuracy_bounds (d : ℕ) {ε E : ℝ} (hε : 0 < ε)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    (ε / (12 * ((d : ℝ) + 1)))⁻¹ ≤ Real.exp (E + d + 4) ∧
    (ε / 3)⁻¹ ≤ Real.exp (E + d + 4) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h12 : (12 : ℝ) ≤ Real.exp 4 := by
    calc
      _ ≤ (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  constructor
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ (Real.exp 4 * Real.exp d) * Real.exp E := by
        gcongr
        exact Real.add_one_le_exp _
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp 2 * Real.exp E := by
        gcongr
        linarith [Real.add_one_le_exp (2 : ℝ)]
      _ = Real.exp (2 + E) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) d])

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]

 theorem partitionedAffineSource_scales_log_bounds (hh : ∀ d, 0 < h d)
    (A T : ℝ≥0) (degree : ℕ) {δ ε E F : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hεE : ε⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) :
    let Clog := unitProfileCoefficientLog (B := B) A T
    let Elog := E + Fintype.card {d // ¬P d} + 4
    let Qlog := jointAffineSourceInputLog (B := fun d : {d // ¬P d} => B d.val)
      (O := O) (α := α) (fun d => h d.val) Clog Elog F
    (partitionedAffineSourceRadius (B := B) (O := O) (α := α) h P A T δ ε)⁻¹ ≤ Real.exp (2 * Qlog + 2) ∧
    Real.log (partitionedAffineSourceTolerance (G := G) (Z := Z) (B := B) (O := O) (α := α)
      h P A T degree δ ε)⁻¹ ≤ Real.log 16 + 6 * Qlog +
        booleanToleranceC2Log (B := fun d : {d // ¬P d} => B d.val) (α := α)
          (PartitionedProfileNoiseIndex G Z α B h P) (fun d => h d.val) degree Clog + 1 := by
  intro Clog Elog Qlog
  have hC := unitProfileCoefficientLog_bounds (B := B) A T
  have hClog : 0 ≤ Clog := unitProfileCoefficientLog_nonneg (B := B) A T
  have hElog : 0 ≤ Elog := by dsimp [Elog]; positivity
  have hacc := affineDividedAccuracy_bounds (Fintype.card {d // ¬P d}) hε hεE
  have hlow (d : {d // ¬P d}) := unitProfilePrincipalSize_pos (B := B) d.val
  have hupp (d : {d // ¬P d}) : 0 ≤ 2 * unitProfilePrincipalSize (B := B) d.val :=
    mul_nonneg (by norm_num) (hlow d).le
  have hraw := jointAffineSourceScales_log_bounds (B := fun d : {d // ¬P d} => B d.val)
    (O := O) (α := α) (fun d => h d.val) (fun d => hh d.val)
    (fun d => unitProfilePrincipalSize (B := B) d.val) (fun d => 2 * unitProfilePrincipalSize (B := B) d.val)
    hlow hupp A T hδ hδone hε hClog hElog hF
    (fun d => hC.1 d.val) (fun d => hC.2.1 d.val) hC.2.2.1 hC.2.2.2 hacc.1 hacc.2 hδF
  refine ⟨hraw.2.1, ?_⟩
  exact jointAffineCoefficientTolerance_log_bound (Z := PartitionedProfileNoiseIndex G Z α B h P)
    (B := fun d : {d // ¬P d} => B d.val) (O := O) (α := α)
    (fun d => h d.val) (fun d => hh d.val)
    (fun d => unitProfilePrincipalSize (B := B) d.val) (fun d => 2 * unitProfilePrincipalSize (B := B) d.val)
    hlow hupp A T degree zero_le_one zero_le_one (Real.one_le_exp hClog) (Real.one_le_exp hClog)
    hδ hδone hε hClog hElog hF (fun d => hC.1 d.val) (fun d => hC.2.1 d.val)
    hC.2.2.1 hC.2.2.2 hacc.1 hacc.2 hδF

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineRadiusLog
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] [DecidableEq α]
  {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]

 theorem allocatedAffineSourceRadius_inverse_bound (A T : ℝ≥0) {δ ε E F : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hεE : ε⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F)
    (P : LayerSamplerAxis I n → Prop) :
    (partitionedAffineSourceRadius (B := B) (O := fun a : {a // ¬P a} => O a.val.1)
      (α := α) (layerSamplerDegree I n) P A T δ ε)⁻¹ ≤
        Real.exp (allocatedAffineRadiusLog (O := O) (α := α) B A T E F) := by
  have h := (partitionedAffineSource_scales_log_bounds (G := Unit) (Z := Unit)
    (B := B) (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P
    (fun _ => Nat.zero_lt_succ _) A T m hδ hδone hε hE hF hεE hδF).1
  apply h.trans
  apply Real.exp_le_exp.mpr
  exact Finset.le_sup' (allocatedAffinePartitionRadiusLog (O := O) (α := α) B A T E F)
    (Finset.mem_univ P)

 theorem allocatedAffineSourceRadius_uniform_floor_s2_oai (A T : ℝ≥0) {δ ε E F : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hεE : ε⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F)
    (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (hρ : ∀ P, 0 < ρ P)
    (hρeq : ∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
      (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T δ ε) :
    ∀ P, Real.exp (-allocatedAffineRadiusLog (O := O) (α := α) B A T E F) ≤ ρ P := by
  intro P
  have hi := allocatedAffineSourceRadius_inverse_bound (O := O) (α := α)
    B A T hδ hδone hε hE hF hεE hδF P
  rw [← hρeq P] at hi
  rw [Real.exp_neg]
  exact (inv_le_comm₀ (Real.exp_pos _) (show 0 < (ρ P : ℝ) from hρ P)).mpr hi

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineSourceRadius_uniform_floor_s2_oai.{u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedAffineSourceRadius_uniform_floor_s2_oai.{u_2, u_3, u_4, u_5}
