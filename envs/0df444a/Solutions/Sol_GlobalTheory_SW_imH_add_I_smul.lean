-- Prove2me | solution 1 for GlobalTheory.SW.imH_add_I_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:32.304529+00:00
-- url     : https://prove2.me/submissions/8df62aaf-a449-40e6-a12a-b25635351e93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
variable {N : ℕ}
namespace GlobalTheory.SW
theorem _root_.solution (Z P : Matrix (Fin N) (Fin N) ℂ) (hP : P.IsHermitian) :
    imH (Z + I • P) = imH Z + P := by
  unfold imH
  rw [conjTranspose_add, conjTranspose_smul, hP.eq]
  have e : Z + I • P - (Zᴴ + star I • P) = (Z - Zᴴ) + (2 * I) • P := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.star_def,
      Complex.conj_I]
    ring
  rw [e, smul_add, smul_smul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero), one_smul]
end GlobalTheory.SW
