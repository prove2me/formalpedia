-- Prove2me | solution 1 for GlobalTheory.FrameNet.det_gramMat_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:08:49.085158+00:00
-- url     : https://prove2.me/submissions/f98a577b-6a4e-45b5-bf12-6b45ad54c387

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres
import Theorems.Thm_GlobalTheory_FrameNet_det_basisMat_ne_zero
import Theorems.Thm_GlobalTheory_FrameNet_norm_emb_det_gramMat

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
theorem _root_.solution {v : Fin r → Fin r → E} (hv : LinearIndependent E v) :
    (gramMat X.Gm v).det ≠ 0 := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  intro h0
  have h1 := norm_emb_det_gramMat τ X.Gm v
  rw [h0, map_zero, norm_zero] at h1
  have h2 : (basisMat τ v).det ≠ 0 := det_basisMat_ne_zero τ hv
  have h3 : τ X.Gm.det ≠ 0 := (map_ne_zero τ).mpr X.Gm_det
  exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr h2)) (norm_ne_zero_iff.mpr h3) h1.symm
end GlobalTheory.FrameNet
