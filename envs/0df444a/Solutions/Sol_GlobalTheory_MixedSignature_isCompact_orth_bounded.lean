-- Prove2me | solution 1 for GlobalTheory.MixedSignature.isCompact_orth_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:40:53.250862+00:00
-- url     : https://prove2.me/submissions/f452413f-3a61-4453-a6de-49fd2f0c53e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FinMuOfFiniteCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsStabiliserImageSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OrthonormalFramesBoundedOfDefinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsOrthUpdateMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FrameStepOfRightMulRealUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_OrthonormalFramesBoundedOfDefinite
import Theorems.Thm_GlobalTheory_FiniteCovolume_embGL_val
import Theorems.Thm_GlobalTheory_FiniteCovolume_hermC_eq_dotProduct
import Theorems.Thm_GlobalTheory_FiniteCovolume_inv_keeps_gram
import Theorems.Thm_GlobalTheory_FlagMahler_finite_bounded
import Theorems.Thm_GlobalTheory_IntegralMultiples_exists_int_smul_mem
import Theorems.Thm_GlobalTheory_LatFin_exists_common_den
import Theorems.Thm_GlobalTheory_LatFin_exists_int_smul_mem
import Theorems.Thm_GlobalTheory_LatFin_finite_bounded
import Theorems.Thm_GlobalTheory_UnitaryFrames_hermC_eq_dot
import Theorems.Thm_GlobalTheory_UnitaryFrames_hermC_mulVec
import Theorems.Thm_GlobalTheory_UnitaryFrames_locallyCompact_GL
import Theorems.Thm_GlobalTheory_UnitaryFrames_secondCountable_GL
import Theorems.Thm_GlobalTheory_UnitaryLift_det_ne_zero_of_diag
import Theorems.Thm_P2M_GlobalTheory_UnitaryFrames_col_mul__08ccc1f94cd1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.MixedSignature
open GlobalTheory.UnitaryFrames (hermC_eq_dot gram_eq_mul hermC_mulVec col_mul' locallyCompact_GL secondCountable_GL)
open GlobalTheory.FiniteCovolume (inv_keeps_gram embGL embGL_val hermC_eq_dotProduct uStabSubgroup)
open GlobalTheory.UnitaryLift (det_ne_zero_of_diag)
open GlobalTheory.LatFin (exists_common_den exists_int_smul_mem finite_bounded)
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.MixedSignature
theorem _root_.solution :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (R : ℝ),
      IsCompact {x : Frame X.Ψ r | Orth X G p x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R}) := by
  intro r X G p R
  have h1 : IsClosed {x : Frame X.Ψ r | Orth X G p x} := by
    simp only [Orth, Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    refine continuous_matrix fun a b => ?_
    simp only [gram, hermC, col, mat, Matrix.of_apply]
    fun_prop
  have h2 : IsClosed {x : Frame X.Ψ r | ∀ τ a b, ‖x τ a b‖ ≤ R} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le ?_ continuous_const
    fun_prop
  refine Metric.isCompact_of_isClosed_isBounded (h1.inter h2) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ r)) (r := |R|)).subset ?_
  rintro x ⟨-, hx⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro τ
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro a
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro b
  exact (hx τ a b).trans (le_abs_self R)
end GlobalTheory.MixedSignature
