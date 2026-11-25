-- Prove2me | solution 1 for GlobalTheory.ThetaRho.exists_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:36.93959+00:00
-- url     : https://prove2.me/submissions/e2059938-b377-4256-acd6-7590a8bd0222

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
import Theorems.Thm_GlobalTheory_ThetaBound_col_mem_Sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaRho
open MeasureTheory
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.ThetaRho
theorem _root_.solution (T : PT E) {s t : (Fin 1 → Vsp T.dim) → ℂ} (hs : s ∈ T.Sec 1 1)
    (ht : t ∈ T.Sec 1 1) (hs0 : s ≠ 0) : ∃ c : ℂ, t = c • s := by
  obtain ⟨hfin, hle⟩ := dim (Idx T.dim) (gtOf T 1) 1 le_rfl
  rw [one_pow] at hle
  have hcol : ∀ w : Fin 1 → Vsp T.dim, w = fun _ => w 0 := fun w =>
    funext fun j => by rw [Subsingleton.elim j 0]
  let S : (gtOf T 1).Sec 1 := ⟨_, ThetaBound.col_mem_Sec T hs⟩
  let S' : (gtOf T 1).Sec 1 := ⟨_, ThetaBound.col_mem_Sec T ht⟩
  have hS : S ≠ 0 := by
    intro h
    apply hs0
    funext w
    rw [hcol w]
    exact congrFun (congrArg Subtype.val h) (w 0)
  obtain ⟨g, hg⟩ := (finrank_le_one_iff).1 hle
  obtain ⟨a, ha⟩ := hg S
  obtain ⟨a', ha'⟩ := hg S'
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hS (by rw [← ha, zero_smul])
  have h : S' = (a' * a⁻¹) • S := by
    rw [← ha, ← ha', smul_smul, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  refine ⟨a' * a⁻¹, funext fun w => ?_⟩
  rw [hcol w]
  exact congrFun (congrArg Subtype.val h) (w 0)
end GlobalTheory.ThetaRho
