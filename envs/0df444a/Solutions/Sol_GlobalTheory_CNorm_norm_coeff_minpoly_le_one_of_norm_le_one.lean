-- Prove2me | solution 1 for GlobalTheory.CNorm.norm_coeff_minpoly_le_one_of_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:06:55.74283+00:00
-- url     : https://prove2.me/submissions/29a78c3d-4056-4264-958f-0f1c74146b96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormCoeffMinpolyLeOneOfNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution (K : Type) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (L : Type) [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) (h : ‖Algebra.norm K x‖ ≤ 1) (n : ℕ) :
    ‖(minpoly K x).coeff n‖ ≤ 1 := by
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖(minpoly K x).coeff 0‖ ≤ 1 := by
    rw [Algebra.norm_eq_norm_adjoin K x, ← IntermediateField.adjoin.powerBasis_gen hx,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, IntermediateField.adjoin.powerBasis_gen hx,
      IntermediateField.minpoly_gen, norm_pow, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul] at h
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (Module.finrank_pos).ne').1 h
  have h1 : spectralNorm K L x ≤ 1 := by
    rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K L x]
    exact Real.rpow_le_one (norm_nonneg _) h0 (by positivity)
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h1
  exact h1 n
end GlobalTheory.CNorm
