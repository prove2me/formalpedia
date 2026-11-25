-- Prove2me | solution 1 for GlobalTheory.FrameNet.shortFrames_subset_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:48:23.670274+00:00
-- url     : https://prove2.me/submissions/eb974cd1-beba-4707-bfe8-673b23458016

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres
import Theorems.Thm_GlobalTheory_FrameNet_det_ne_zero_of_ortho
import Theorems.Thm_PIW_FdPA_mem_dom_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mem_dom_iff


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
theorem _root_.solution (v : Fin r → Fin r → E) (B : ℝ) : shortFrames X v B ⊆ X.dom := by
  intro x hx
  have ho : X.IsOrtho x := hx.1
  rw [PIW.FdPA.mem_dom_iff]
  intro τ
  refine ⟨det_ne_zero_of_ortho X ho τ, fun i => ?_⟩
  have hm : dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    rw [Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range]
    rfl
  rw [hm, Complex.ofReal_re]
  have hne : psgn X.p0 i ≠ 0 := by
    unfold psgn
    rw [Finset.prod_ne_zero_iff]
    intro a _
    unfold sgn
    split_ifs <;> norm_num
  exact mul_self_pos.mpr hne
end GlobalTheory.FrameNet
