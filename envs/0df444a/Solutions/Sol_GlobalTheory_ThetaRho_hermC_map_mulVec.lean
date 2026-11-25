-- Prove2me | solution 1 for GlobalTheory.ThetaRho.hermC_map_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:38:00.975137+00:00
-- url     : https://prove2.me/submissions/3cd0d29e-30e4-430d-a8d5-02eca530ad82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormalisedThetaNormInvariant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaRho
open MeasureTheory
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.ThetaRho
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm G (γ.mulVec x) (γ.mulVec y) = herm G x y) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ G ((γ.map τ).mulVec u) ((γ.map τ).mulVec w) = hermC τ G u w := by
  have hx : ∀ (P : Matrix (Fin r) (Fin r) E) (u : Fin r → ℂ), (P.map τ).mulVec u =
      ∑ k, u k • Data.emb τ (P.mulVec (Pi.single k 1)) := by
    intro P u
    funext j
    simp [Data.emb, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm, apply_ite τ]
  have hexp : ∀ P : Matrix (Fin r) (Fin r) E,
      hermC τ G ((P.map τ).mulVec u) ((P.map τ).mulVec w) = ∑ k, ∑ l, u k * (conj (w l) *
        τ (herm G (P.mulVec (Pi.single k 1)) (P.mulVec (Pi.single l 1)))) := by
    intro P
    rw [hx, hx, hermC_sum_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hermC_smul_right, hermC_emb]
  have h1 : ((1 : Matrix (Fin r) (Fin r) E).map τ) = 1 := Matrix.map_one τ τ.map_zero τ.map_one
  conv_rhs => rw [← Matrix.one_mulVec u, ← Matrix.one_mulVec w, ← h1]
  rw [hexp, hexp]
  simp only [hγ, Matrix.one_mulVec]
end GlobalTheory.ThetaRho
