-- Prove2me | solution 1 for OAI.Erdos3.selectedPhysicalGrid_inverse_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T18:02:27.544915+00:00
-- url     : https://prove2.me/submissions/e9b03a77-0ff1-47c4-8938-6e4774149c78

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090
import Theorems.Thm_OAI_Erdos3_fullSmoothPairError_nonneg
import Theorems.Thm_OAI_Erdos3_physicalPairCoefficientLog_bounds
import Theorems.Thm_OAI_Erdos3_replacementCommonInputLog_bounds
import Theorems.Thm_OAI_Erdos3_replacement_selected_parameter_bounds

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem normalizedFiberErrorConstant_le_exp (j d : ℕ) {G U V R H b : ℝ} (K : ℝ≥0)
    (hb : 0 ≤ b) (_hG0 : 0 ≤ G) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hR0 : 0 ≤ R) (hH0 : 0 ≤ H)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hV : V ≤ Real.exp b)
    (hR : R ≤ Real.exp b) (hH : H ≤ Real.exp b) (hK : (K : ℝ) ≤ Real.exp b) :
    normalizedFiberErrorConstant j d G U V R H K ≤
      Real.exp ((j : ℝ)^2 + (j + 4) * b + (j + 2*d) * (b + 4) + 4) := by
  have hone : 1 ≤ Real.exp b := Real.one_le_exp_iff.mpr hb
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbox : 2 * R + 2 ≤ Real.exp (b + 4) := by
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left hfour (Real.exp_pos b).le]
  have htwor : 2 * R ≤ Real.exp (b + 4) := by linarith
  have hmax : max 1 (U * V) ≤ Real.exp (2*b) := by
    apply max_le
    · exact Real.one_le_exp_iff.mpr (by positivity)
    · calc
        _ ≤ Real.exp b * Real.exp b := mul_le_mul hU hV hV0 (Real.exp_pos b).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
  let F := (j : ℝ)^2 + (j + 4) * b + (j + 2*d) * (b + 4)
  have hfirst : integerFiberErrorConstant j d G U V R K ≤ Real.exp F := by
    unfold integerFiberErrorConstant
    calc
      _ ≤ Real.exp b * (Real.exp ((j : ℝ)^2) * (Real.exp b)^j) *
          (Real.exp (b + 4))^d * Real.exp b * Real.exp (2*b) := by
        gcongr
        exact factorial_le_exp_sq j
      _ = Real.exp ((j : ℝ)^2 + (j + 4)*b + d*(b+4)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        simp only [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp F := Real.exp_le_exp.mpr (by dsimp [F]; nlinarith [Nat.cast_nonneg j (α := ℝ), Nat.cast_nonneg d (α := ℝ)])
  have hsecond : (G * (j.factorial * U ^ j) * H * (2*R)^d) *
      ((2*R+2)^(j+d) * K) ≤ Real.exp F := by
    calc
      _ ≤ (Real.exp b * (Real.exp ((j : ℝ)^2) * (Real.exp b)^j) * Real.exp b *
          (Real.exp (b+4))^d) * ((Real.exp (b+4))^(j+d) * Real.exp b) := by
        gcongr
        exact factorial_le_exp_sq j
      _ = Real.exp ((j : ℝ)^2 + (j+3)*b + (j+2*d)*(b+4)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        simp only [← Real.exp_add]
        push_cast
        congr 1
        ring
      _ ≤ Real.exp F := Real.exp_le_exp.mpr (by dsimp [F]; nlinarith)
  change 2 * integerFiberErrorConstant j d G U V R K +
    2 * (G * (j.factorial * U ^ j) * H * (2*R)^d) * ((2*R+2)^(j+d) * K) ≤ _
  calc
    _ ≤ 4 * Real.exp F := by linarith
    _ ≤ Real.exp F * Real.exp 4 := by nlinarith [Real.exp_pos F]
    _ = _ := by rw [← Real.exp_add]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {O J : D → Type*}
  [∀ d, Fintype (O d)] [∀ d, Fintype (J d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSmoothPairLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

theorem smoothPairProbabilityError_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ smoothPairProbabilityError k Q C κ δ := by
  unfold smoothPairProbabilityError normalizedFiberErrorConstant integerFiberErrorConstant
  positivity

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothPairErrorLogBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem smoothPairErrorCoefficient_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) : 0 ≤ smoothPairErrorCoefficient n k Q C κ :=
  fullSmoothPairError_nonneg n k Q C κ 1 zero_le_one

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem smoothPairRowLipschitz_le_exp (k : J) {P : ℝ} (hP : 0 ≤ P)
    (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    (smoothPairRowLipschitz k : ℝ) ≤ Real.exp (2 * P + 3) := by
  have hd : (Fintype.card {j : J // j ≠ k} : ℝ) ≤ Fintype.card J := by
    exact_mod_cast Fintype.card_subtype_le (fun j : J => j ≠ k)
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hsum : (Fintype.card {j : J // j ≠ k} : ℝ) + 2 ≤ Real.exp (P + 3) := by
    rw [Real.exp_add]
    nlinarith
  simp only [smoothPairRowLipschitz, NNReal.coe_mul, Nat.cast_add, Nat.cast_ofNat]
  calc
    _ ≤ Real.exp (P + 3) * Real.exp P := mul_le_mul hsum hprofile (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem smoothPairScaleRatio_le_exp {C κ P : ℝ}
    (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P) :
    4 * C / κ ≤ Real.exp (2 * P + 4) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp 4 * Real.exp P * Real.exp P := by gcongr
    _ = _ := by simp only [← Real.exp_add]; congr 1; ring

theorem smoothPairQuadraticFactor_le_exp (k : J) {C κ P : ℝ}
    (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp (5 * P + 10) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hU := smoothPairScaleRatio_le_exp hC0 hκ0 hC hκ
  calc
    _ ≤ Real.exp 2 * (Real.exp (2 * P + 4)) ^ 2 * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; simp only [← Real.exp_add]; congr 1; ring

theorem smoothPairProbabilityCap_le_exp (k : J) (Q : ℕ) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hQ : (Q : ℝ) ≤ Real.exp P) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    smoothPairProbabilityCap k Q C κ ≤ Real.exp (6 * P + 11) := by
  have hfactor := smoothPairQuadraticFactor_le_exp k hC0 hκ0 hC hκ hpow
  have hproduct : (Q : ℝ) * (2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k}) ≤
      Real.exp (6 * P + 10) := by
    calc
      _ ≤ Real.exp P * Real.exp (5 * P + 10) := mul_le_mul hQ hfactor (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp ((6 * P + 10) + 1) := one_add_le_exp_succ (by linarith) hproduct
    _ = _ := by congr 1; ring

theorem smoothPairKernelBaseCap_le_exp (k : J) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (smoothPairKernelBaseCap k C κ : ℝ) ≤ Real.exp (5 * P + 11) := by
  apply coe_toNNReal_le_exp
  calc
    _ ≤ Real.exp ((5 * P + 10) + 1) := one_add_le_exp_succ (by linarith)
      (smoothPairQuadraticFactor_le_exp k hC0 hκ0 hC hκ hpow)
    _ = _ := by congr 1; ring

theorem smoothPairKernelBaseLip_le_exp (k : J) {C κ P : ℝ}
    (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (smoothPairKernelBaseLip k C κ : ℝ) ≤ Real.exp (8 * P + 14) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hU := smoothPairScaleRatio_le_exp hC0 hκ0 hC hκ
  apply coe_toNNReal_le_exp
  calc
    _ ≤ Real.exp 2 * (Real.exp (2 * P + 4)) ^ 3 * Real.exp P * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; simp only [← Real.exp_add]; congr 1; ring

theorem smoothPairKernelCap_le_exp (n : ℕ) (k : J) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (smoothPairKernelCap n k C κ : ℝ) ≤ Real.exp ((n : ℝ) * (5 * P + 11)) := by
  simpa only [smoothPairKernelCap, NNReal.coe_pow, Real.exp_nat_mul] using
    pow_le_pow_left₀ (NNReal.coe_nonneg (smoothPairKernelBaseCap k C κ))
      (smoothPairKernelBaseCap_le_exp k hP hC0 hκ0 hC hκ hpow) n

theorem smoothPairKernelLip_le_exp (n : ℕ) (k : J) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hn : (n : ℝ) ≤ Real.exp P) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (smoothPairKernelLip n k C κ : ℝ) ≤ Real.exp ((n : ℝ) * (5 * P + 11) + 9 * P + 14) := by
  have hbase := smoothPairKernelBaseLip_le_exp k hC0 hκ0 hC hκ hrow hpow
  have hcap := smoothPairKernelCap_le_exp n k hP hC0 hκ0 hC hκ hpow
  simp only [smoothPairKernelLip, NNReal.coe_mul, NNReal.coe_natCast]
  calc
    _ ≤ Real.exp P * Real.exp (8 * P + 14) * Real.exp ((n : ℝ) * (5 * P + 11)) := by gcongr
    _ = _ := by simp only [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem smoothPairRowErrorLog_nonneg (d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ smoothPairRowErrorLog d P := by
  unfold smoothPairRowErrorLog
  positivity

theorem smoothPairProbabilityError_one_le_exp (k : J) (Q : ℕ) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hQ : (Q : ℝ) ≤ Real.exp P) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P) :
    smoothPairProbabilityError k Q C κ 1 ≤
      Real.exp (smoothPairRowErrorLog (Fintype.card {j : J // j ≠ k}) P) := by
  have hlift : Real.exp P ≤ Real.exp (2 * P + 4) := Real.exp_le_exp.mpr (by linarith)
  have hV : (Fintype.card J : ℝ) * C ≤ Real.exp (2 * P + 4) := by
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hcard hC hC0 (Real.exp_nonneg _)
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have h1 : (1 : ℝ) ≤ Real.exp (2 * P + 4) := Real.one_le_exp_iff.mpr (by linarith)
  have h := normalizedFiberErrorConstant_le_exp 2 (Fintype.card {j : J // j ≠ k})
    (smoothPairRowLipschitz k) (by linarith : 0 ≤ 2 * P + 4)
    (Nat.cast_nonneg Q) (by positivity) (by positivity) (by norm_num) (by norm_num)
    (hQ.trans hlift) (smoothPairScaleRatio_le_exp hC0 hκ0 hC hκ) hV h1 h1 (hrow.trans hlift)
  simp only [smoothPairProbabilityError, mul_one]
  apply h.trans_eq
  congr 1
  unfold smoothPairRowErrorLog
  ring

theorem smoothPairErrorCoefficient_le_exp (n : ℕ) (k : J) (Q : ℕ) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hn : (n : ℝ) ≤ Real.exp P) (hQ : (Q : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    smoothPairErrorCoefficient n k Q C κ ≤
      Real.exp (smoothPairErrorLog n (Fintype.card {j : J // j ≠ k}) P) := by
  let d := Fintype.card {j : J // j ≠ k}
  have hr := smoothPairProbabilityError_one_le_exp k Q hP hC0 hκ0 hQ hC hκ hcard hrow
  have hc := smoothPairProbabilityCap_le_exp k Q hP hC0 hκ0 hQ hC hκ hpow
  have hsum : smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ 1 ≤
      Real.exp (smoothPairRowErrorLog d P + 6 * P + 12) := by
    have hh := add_le_exp_add_one (by linarith : 0 ≤ 6 * P + 11)
      (smoothPairRowErrorLog_nonneg d hP) hc hr
    apply hh.trans_eq
    congr 1
    ring
  have hr0 := smoothPairProbabilityError_nonneg k Q C κ 1 zero_le_one
  have hc0 : 0 ≤ smoothPairProbabilityCap k Q C κ := by unfold smoothPairProbabilityCap; positivity
  unfold smoothPairErrorCoefficient fullSmoothPairError
  calc
    _ ≤ Real.exp P * Real.exp (smoothPairRowErrorLog d P) *
        (Real.exp (smoothPairRowErrorLog d P + 6 * P + 12)) ^ n := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1

theorem smoothPairMeshCoefficient_le_exp (k : J) {P : ℝ}
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P) :
    (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k ≤
      Real.exp (4 * (2 + (Fintype.card {j : J // j ≠ k} : ℝ)) + P) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ (Real.exp 4) ^ (2 + Fintype.card {j : J // j ≠ k}) * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

theorem residualPointAccuracy_inverse_le_exp {M S F mesh epsilon P : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hF : 0 ≤ F) (hmesh : 0 ≤ mesh)
    (heps : 0 < epsilon) (hP : 0 ≤ P)
    (hcoef : 6 * M * S * F ≤ Real.exp P) (hmeshcoef : 2 * mesh ≤ Real.exp P)
    (hepsinv : epsilon⁻¹ ≤ Real.exp P) :
    (residualPointAccuracy M S F mesh epsilon)⁻¹ ≤ Real.exp (2 * P + 2) := by
  unfold residualPointAccuracy
  apply inv_min_le_of_inv_le
  · exact replacementAccuracy_inverse_le_exp (by positivity) heps hP hcoef hepsinv
  · exact replacementAccuracy_inverse_le_exp (by positivity) (by norm_num) hP hmeshcoef
      (by simpa only [inv_one] using Real.one_le_exp_iff.mpr hP)

theorem residualGridAccuracy_inverse_le_exp {M S K epsilon P : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hK : 0 ≤ K) (heps : 0 < epsilon) (hP : 0 ≤ P)
    (hcoef : 6 * M * S * K ≤ Real.exp P) (hepsinv : epsilon⁻¹ ≤ Real.exp P) :
    (residualGridAccuracy M S K epsilon)⁻¹ ≤ Real.exp (2 * P + 2) :=
  replacementAccuracy_inverse_le_exp (by positivity) heps hP hcoef hepsinv

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

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

theorem physicalPairPowerBounds (n : ℕ) {A P : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ Real.exp P) :
    A ^ (2 * n) ≤ Real.exp (2 * n * P) ∧ (2 : ℝ) ^ n ≤ Real.exp (2 * n) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  constructor
  · apply (pow_le_pow_left₀ hA0 hA (2 * n)).trans_eq
    rw [← Real.exp_nat_mul]
    push_cast
    rfl
  · apply (pow_le_pow_left₀ (by norm_num) h2 n).trans_eq
    rw [← Real.exp_nat_mul]
    congr 1
    ring

theorem physicalPairPointGridAccuracy_inverse_le_exp (n : ℕ) (k : J) (Q : ℕ)
    {C κ A epsilon P : ℝ} (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hA0 : 0 ≤ A) (heps0 : 0 < epsilon)
    (hn : (n : ℝ) ≤ Real.exp P) (hQ : (Q : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (heps : epsilon⁻¹ ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (physicalPairPointAccuracy n k Q C κ A epsilon)⁻¹ ≤
      Real.exp (2 * physicalPairCoefficientLog n (Fintype.card {j : J // j ≠ k}) P + 2) ∧
    (physicalPairGridAccuracy n k C κ A epsilon)⁻¹ ≤
      Real.exp (2 * physicalPairCoefficientLog n (Fintype.card {j : J // j ≠ k}) P + 2) := by
  let d := Fintype.card {j : J // j ≠ k}
  have hlogs := physicalPairCoefficientLog_bounds n d hP
  obtain ⟨hM, hS⟩ := physicalPairPowerBounds n hA0 hA
  have hF := smoothPairErrorCoefficient_le_exp n k Q hP hC0 hκ0 hn hQ hC hκ hcard hrow hpow
  have hK := smoothPairKernelLip_le_exp n k hP hC0 hκ0 hn hC hκ hrow hpow
  have hm := smoothPairMeshCoefficient_le_exp k hrow
  have h6 : (6 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hF0 := smoothPairErrorCoefficient_nonneg n k Q C κ
  have heps' : epsilon⁻¹ ≤ Real.exp (physicalPairCoefficientLog n d P) :=
    heps.trans (Real.exp_le_exp.mpr hlogs.2.1)
  constructor
  · apply residualPointAccuracy_inverse_le_exp (by positivity) (by positivity) hF0 (by positivity)
      heps0 hlogs.1
    · calc
        _ ≤ Real.exp 6 * Real.exp (2 * n * P) * Real.exp (2 * n) *
            Real.exp (smoothPairErrorLog n d P) := by gcongr
        _ = Real.exp (6 + 2 * n * P + 2 * n + smoothPairErrorLog n d P) := by
          simp only [← Real.exp_add]
        _ ≤ _ := Real.exp_le_exp.mpr hlogs.2.2.1
    · calc
        _ ≤ Real.exp 2 * Real.exp (4 * (2 + (d : ℝ)) + P) := by gcongr
        _ = Real.exp (2 + 4 * (2 + (d : ℝ)) + P) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr hlogs.2.2.2.1
    · exact heps'
  · apply residualGridAccuracy_inverse_le_exp (by positivity) (by positivity) (by positivity)
      heps0 hlogs.1
    · calc
        _ ≤ Real.exp 6 * Real.exp (2 * n * P) * Real.exp (2 * n) *
            Real.exp ((n : ℝ) * (5 * P + 11) + 9 * P + 14) := by gcongr
        _ = Real.exp (20 + 2 * n * P + 2 * n + n * (5 * P + 11) + 9 * P) := by
          simp only [← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := Real.exp_le_exp.mpr hlogs.2.2.2.2
    · exact heps'

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

theorem physicalReplacementInputLog_nonneg (m n : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ physicalReplacementInputLog m n P := by
  unfold physicalReplacementInputLog
  positivity

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

end Erdos3

end

section

namespace Erdos3

theorem replacement_common_geometric_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (m n : ℕ) (k : J) {C A P : ℝ} (hP : 0 ≤ P)
    (hn : (n : ℝ) ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    let Z := replacementCommonInputLog m n (Fintype.card J) P
    (n : ℝ) ≤ Real.exp Z ∧ (Fintype.card J : ℝ) ≤ Real.exp Z ∧
    C ≤ Real.exp Z ∧ A ≤ Real.exp Z ∧ (probabilityProfileLipschitz : ℝ) ≤ Real.exp Z ∧
    (smoothPairRowLipschitz k : ℝ) ≤ Real.exp Z ∧
    (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp Z := by
  intro Z
  have hz := replacementCommonInputLog_bounds m n (Fintype.card J) hP
  have ht := replacementCutoffInputLog_bounds m n (Fintype.card J) hP
  have hexp : Real.exp P ≤ Real.exp Z := Real.exp_le_exp.mpr hz.2.1
  refine ⟨hn.trans hexp, hcard.trans hexp, hC.trans hexp, hA.trans hexp, hprofile.trans hexp, ?_, ?_⟩
  · exact (smoothPairRowLipschitz_le_exp k hP hcard hprofile).trans (Real.exp_le_exp.mpr hz.2.2.2.2.2)
  · apply (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Fintype.card_subtype_le (fun j : J => j ≠ k))).trans
    apply (replacement_binary_power_le_exp (Fintype.card J)).trans
    exact Real.exp_le_exp.mpr (ht.2.2.2.2.trans hz.2.2.1)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SelectedPhysicalGridBudget
namespace OAI

section

namespace Erdos3

theorem selectedPhysicalGrid_inverse_le_exp {J : Type*} [Fintype J] [DecidableEq J]
    (m n : ℕ) (k : J) (D : ℕ) {K A C Cwidth c epsilon P : ℝ}
    (hP : 0 ≤ P) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) (hCwidth0 : 0 ≤ Cwidth)
    (hc0 : 0 < c) (heps0 : 0 < epsilon) (hD : 0 < D)
    (hn : (n : ℝ) ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hDlog : (D : ℝ) ≤ Real.exp P) (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hCwidth : Cwidth ≤ Real.exp P)
    (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    let tol := weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon
    let _Q := D * integerBoxGcdCutoff (Fintype.card J) Cwidth tol
    let κ := integerBoxRetainedGap (Fintype.card J) D c tol
    let Z := replacementCommonInputLog m n (Fintype.card J) P
    (physicalPairGridAccuracy n k C κ A tol)⁻¹ ≤
      Real.exp (2 * physicalPairCoefficientLog n (Fintype.card {j : J // j ≠ k}) Z + 2) := by
  intro tol Q κ Z
  obtain ⟨ht, hti, hk, hki, hq, _⟩ := replacement_selected_parameter_bounds m n (Fintype.card J) D
    hP hK0 hA0 hCwidth0 hc0 heps0 hD hDlog hK hA hCwidth hc heps
  obtain ⟨hn', hcard', hC', hA', _, hrow', hpow'⟩ :=
    replacement_common_geometric_bounds m n k hP hn hcard hC hA hprofile
  exact (physicalPairPointGridAccuracy_inverse_le_exp n k Q
    (replacementCommonInputLog_bounds m n (Fintype.card J) hP).1 hC0 hk hA0 ht
    hn' hq hC' hki hA' hti hcard' hrow' hpow').2

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.selectedPhysicalGrid_inverse_le_exp.{u_1} := @OAI.Erdos3.selectedPhysicalGrid_inverse_le_exp.{u_1}
