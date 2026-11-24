-- Prove2me | solution 1 for GlobalTheory.FrameNet.norm_det_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:08:50.823084+00:00
-- url     : https://prove2.me/submissions/b75d31ca-8725-443a-af15-3514b5d3b4b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres
import Theorems.Thm_GlobalTheory_FrameNet_norm_emb_det_gramMat
import Theorems.Thm_GlobalTheory_FrameNet_norm_det_sq_of_ortho
import Theorems.Thm_GlobalTheory_FrameNet_det_ne_zero_of_ortho

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FrameNet
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace GlobalTheory.FrameNet
theorem _root_.solution {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (v : Fin r → Fin r → E) :
    ‖((mat x τ)⁻¹ * basisMat τ.1 v).det‖ = Real.sqrt ‖τ.1 (gramMat X.Gm v).det‖ := by
  have h1 := norm_det_sq_of_ortho X hx τ
  have hd := det_ne_zero_of_ortho X hx τ
  have hdn : 0 < ‖(mat x τ).det‖ := norm_pos_iff.mpr hd
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, norm_mul, norm_inv,
    norm_emb_det_gramMat]
  have hG : ‖τ.1 X.Gm.det‖ = (‖(mat x τ).det‖⁻¹) ^ 2 := by
    rw [inv_pow]
    field_simp
    linarith [h1]
  rw [hG, ← mul_pow, Real.sqrt_sq (by positivity)]
  ring
end GlobalTheory.FrameNet
