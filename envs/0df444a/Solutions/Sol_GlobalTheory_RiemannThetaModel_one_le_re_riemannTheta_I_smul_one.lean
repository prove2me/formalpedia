-- Prove2me | solution 1 for GlobalTheory.RiemannThetaModel.one_le_re_riemannTheta_I_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:18:59.079492+00:00
-- url     : https://prove2.me/submissions/c2bfe1d3-169e-469b-9b08-570c51f5d7e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic
import Theorems.Thm_GlobalTheory_IsSiegel_hasSum_riemannTheta
import Theorems.Thm_GlobalTheory_isSiegel_I_smul_one
import Theorems.Thm_GlobalTheory_riemannThetaTerm_zero_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.RiemannThetaModel
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.RiemannThetaModel
theorem _root_.solution [DecidableEq ι] :
    1 ≤ (riemannTheta (0 : ι → ℝ) 0 (I • (1 : Matrix ι ι ℂ)) 0).re := by
  have hs := (isSiegel_I_smul_one (ι := ι)).hasSum_riemannTheta 0 0 0
  have hr := Complex.hasSum_re hs
  have ht (n : ι → ℤ) : riemannThetaTerm (0 : ι → ℝ) 0 (I • (1 : Matrix ι ι ℂ)) 0 n =
      (Real.exp (-π * ∑ i, (n i : ℝ) ^ 2) : ℝ) := by
    rw [riemannThetaTerm_zero_zero, Complex.ofReal_exp]
    congr 1
    simp only [smul_mulVec, one_mulVec, dotProduct_smul, dotProduct_zero, smul_eq_mul]
    simp only [dotProduct]
    push_cast
    simp only [sq]
    linear_combination (π * ∑ i, (n i : ℂ) * n i) * I_mul_I
  have := le_hasSum hr 0 (fun n _ => by rw [ht, ofReal_re]; exact (Real.exp_pos _).le)
  rw [ht] at this
  simpa using this
end GlobalTheory.RiemannThetaModel
