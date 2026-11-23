-- Prove2me | solution 1 for GlobalTheory.FrameNet.det_basisMat_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:06.972335+00:00
-- url     : https://prove2.me/submissions/6674eebc-3dfc-4e60-a765-55245d17062a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres

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
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.FrameNet
theorem _root_.solution (τ : E →+* ℂ) {v : Fin r → Fin r → E} (hv : LinearIndependent E v) :
    (basisMat τ v).det ≠ 0 := by
  have hu : IsUnit (Matrix.of v) := Matrix.linearIndependent_rows_iff_isUnit.mp hv
  have hd : (Matrix.of v).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  have e : (basisMat τ v).det = τ ((Matrix.of v)ᵀ).det := by
    unfold basisMat; rw [RingHom.map_det]; rfl
  rw [e, Matrix.det_transpose]
  exact (map_ne_zero τ).mpr hd
end GlobalTheory.FrameNet
