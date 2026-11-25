-- Prove2me | solution 1 for GlobalTheory.LaurentFJ.flow_mem_dom_of_im_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:47.970142+00:00
-- url     : https://prove2.me/submissions/9fffd4b5-f490-46e1-bbed-60e1abf920aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bExpHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CoeffEqZeroOfHasSumZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_flowDomainCriterion_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFJ
open Complex ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
namespace GlobalTheory.LaurentFJ
theorem _root_.solution (X : Data E r) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : ∀ τ, 0 ≤ (s τ).im) :
    X.flow ξ s x ∈ X.dom := by
  have hiv : X.IsIsoV fun τ => Data.emb τ.1 ξ := by
    intro τ
    refine ⟨?_, ?_⟩
    · have key : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm ξ ξ) := by
        simp only [hermC, herm, Data.emb, map_sum, map_mul, cc,
          NumberField.IsCMField.complexEmbedding_complexConj]
      change hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0
      rw [key, hξ.2.1, map_zero]
    · intro h0
      apply hξ.2.2
      funext a
      have := congrFun h0 a
      simpa [Data.emb] using this
  refine (flowDomainCriterion_holds r X _ hiv x hx s).1.2 fun τ => ?_
  have ht : 0 < X.ttV (fun τ => Data.emb τ.1 ξ) x τ :=
    one_div_pos.mpr (mul_pos (MajorantFamilyNorms.c_pos X τ) (X.maj_pos hx τ (hiv τ).2))
  have := div_nonneg (hs τ) ht.le
  linarith
end GlobalTheory.LaurentFJ
