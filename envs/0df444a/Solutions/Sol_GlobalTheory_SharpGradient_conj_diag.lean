-- Prove2me | solution 1 for GlobalTheory.SharpGradient.conj_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:43:52.661806+00:00
-- url     : https://prove2.me/submissions/610f6b56-0477-406e-83bb-58ff3d41ff50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
namespace GlobalTheory.SharpGradient
theorem _root_.solution {p q : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (hU : Uᴴ * U = 1)
    (Z : Matrix (Fin p) (Fin q) ℂ) (a : Fin p) :
    ((Uᴴ * (1 - Z * Zᴴ) * U : Matrix (Fin p) (Fin p) ℂ) a a).re = 1 - ∑ b, Complex.normSq ((Uᴴ * Z) a b) := by
  have e : Uᴴ * (1 - Z * Zᴴ) * U = 1 - (Uᴴ * Z) * (Uᴴ * Z)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hU]
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.sub_apply, Matrix.mul_apply]
  simp only [Matrix.one_apply_eq, Complex.sub_re, Complex.one_re, conjTranspose_apply,
    Complex.star_def, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]
end GlobalTheory.SharpGradient
