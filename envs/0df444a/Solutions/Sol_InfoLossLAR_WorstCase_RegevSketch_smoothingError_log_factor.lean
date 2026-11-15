-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.smoothingError_log_factor
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:34:23.447194+00:00
-- url     : https://prove2.me/submissions/23dddb7b-3745-4362-98b3-2a3857434323

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.RegevSketch
noncomputable section
private def shortSmoothingFactor (dimension : ℕ) (error : ℝ) : ℝ :=
  Real.sqrt (Real.log (4*(dimension : ℝ)*(1+1/error))/Real.pi)
private theorem smoothingError_pos (dimension : ℕ) : 0 < smoothingError dimension := by
  unfold smoothingError
  positivity

private theorem fixedSmoothingFactor_le_size (dimension : ℕ) (hdimension : 0 < dimension) :
    shortSmoothingFactor dimension (smoothingError dimension) ≤ (Nat.size (dimension+2) : ℝ)+2 := by
  let bits := Nat.size (dimension+2)
  have hbitsNonnegative : (0 : ℝ) ≤ bits := Nat.cast_nonneg _
  have hd : (dimension : ℝ) ≤ (2 : ℝ)^bits := by
    exact_mod_cast (le_trans (by omega : dimension ≤ dimension+2) (Nat.lt_size_self (dimension+2)).le)
  have herrorPositive := smoothingError_pos dimension
  have hpowerOne : (1 : ℝ) ≤ (2 : ℝ)^(bits^2) := one_le_pow₀ (by norm_num)
  have hinverse : 1/smoothingError dimension=(2 : ℝ)^(bits^2) := by
    change 1/(1/(2 : ℝ)^(bits^2))=(2 : ℝ)^(bits^2)
    simp
  have hone : 1+1/smoothingError dimension ≤ (2 : ℝ)^(bits^2+1) := by
    rw [hinverse,show (2 : ℝ)^(bits^2+1)=(2 : ℝ)^(bits^2)*2 from pow_succ _ _]
    linarith
  have hargument : 4*(dimension : ℝ)*(1+1/smoothingError dimension) ≤
      (2 : ℝ)^(bits^2+bits+3) := by
    calc
      _ ≤ 4*((2 : ℝ)^bits)*(2 : ℝ)^(bits^2+1) := by
        gcongr
      _ = _ := by simp only [pow_add,pow_one];ring
  have hargumentPos : 0 < 4*(dimension : ℝ)*(1+1/smoothingError dimension) := by
    have hdpositive : (0 : ℝ) < dimension := by exact_mod_cast hdimension
    have hepositive := smoothingError_pos dimension
    positivity
  have hlog := Real.log_le_log hargumentPos hargument
  rw [Real.log_pow] at hlog
  have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hexponent : ((bits^2+bits+3 : ℕ) : ℝ) ≤ ((bits : ℝ)+2)^2 := by
    push_cast
    nlinarith
  have hlogBound : Real.log (4*(dimension : ℝ)*(1+1/smoothingError dimension)) ≤ ((bits : ℝ)+2)^2*Real.pi := by
    have hlinear := mul_le_mul_of_nonneg_left hlogTwo (by positivity : (0 : ℝ) ≤ ((bits^2+bits+3 : ℕ) : ℝ))
    have hpi := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Real.pi from by linarith [Real.pi_gt_three])
      (sq_nonneg ((bits : ℝ)+2))
    nlinarith
  unfold shortSmoothingFactor
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  exact (div_le_iff₀ Real.pi_pos).mpr hlogBound

/-- The exact binary-length bound is logarithmic with an absolute constant. -/
private theorem dimension_size_le_log (dimension : ℕ) :
    (Nat.size (dimension+2) : ℝ)+2 ≤ (4/Real.log 2)*Real.log (dimension+2) := by
  let bits := Nat.size (dimension+2)
  have hbits : 0 < bits := Nat.size_pos.mpr (by omega)
  have hbitsOne : 1 ≤ bits := hbits
  have hpower : (2 : ℝ)^(bits-1) ≤ (dimension+2 : ℝ) := by
    exact_mod_cast (Nat.lt_size.mp (by dsimp only [bits];omega : bits-1 < Nat.size (dimension+2)))
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ)^(bits-1)) hpower
  rw [Real.log_pow,Nat.cast_sub hbitsOne,Nat.cast_one] at hlog
  have hlogDimension : Real.log 2 ≤ Real.log (dimension+2 : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ dimension+2 by omega))
  have hlarge : ((bits : ℝ)+2)*Real.log 2 ≤ 4*Real.log (dimension+2 : ℝ) := by nlinarith
  change (bits : ℝ)+2 ≤ _
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hlogTwo).mpr hlarge

end
end InfoLossLAR.WorstCase.RegevSketch
open InfoLossLAR.WorstCase.RegevSketch

/-- A single fixed negligible schedule has an absolute logarithmic factor,
so the final lattice approximation constant is independent of every
adversary-dependent sample or precision exponent. -/
theorem solution (dimension : ℕ) (hdimension : 0 < dimension) :
    Real.sqrt (Real.log (4*(dimension : ℝ)*(1+1/smoothingError dimension))/Real.pi) ≤
      (4/Real.log 2)*Real.log (dimension+2) :=
  (fixedSmoothingFactor_le_size dimension hdimension).trans (dimension_size_le_log dimension)

