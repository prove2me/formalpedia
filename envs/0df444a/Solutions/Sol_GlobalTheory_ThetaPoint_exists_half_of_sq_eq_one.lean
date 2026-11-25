-- Prove2me | solution 1 for GlobalTheory.ThetaPoint.exists_half_of_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:46.15184+00:00
-- url     : https://prove2.me/submissions/c836f217-420a-4c92-9161-c7fbcd4385fb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfThetaTranslateEqUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHalfOfSqEqOne
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.ThetaPoint
open CanTh
variable {g : ℕ}
namespace GlobalTheory.ThetaPoint
theorem _root_.solution {c : ℂ} (hc : c ^ 2 = 1) :
    ∃ a : ℝ, (a = 0 ∨ a = 1 / 2) ∧ cexp (2 * π * I * a) = c ∧ cexp (-(2 * π * I * a)) = c := by
  rcases sq_eq_one_iff.1 hc with rfl | rfl
  · exact ⟨0, Or.inl rfl, by simp, by simp⟩
  · refine ⟨1 / 2, Or.inr rfl, ?_, ?_⟩
    · rw [← Complex.exp_pi_mul_I]; congr 1; push_cast; ring
    · rw [← Complex.exp_neg_pi_mul_I]; congr 1; push_cast; ring
end GlobalTheory.ThetaPoint
