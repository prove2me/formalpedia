-- Prove2me | solution 1 for GlobalTheory.ThetaRho.exists_unit_of_flag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:53:46.76887+00:00
-- url     : https://prove2.me/submissions/b74e0078-2d4f-496a-bbd1-8527048795d9

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
import Theorems.Thm_GlobalTheory_ThetaRho_hermC_eq_zero_of_mem_span
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_e_linInd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_sgn_sq
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
theorem _root_.solution (X : Data E r) (τ : X.Ψ) (e e' : Fin r → Fin r → ℂ)
    (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)
    (he' : ∀ a b, hermC τ.1 X.Gm (e' a) (e' b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)
    (hfl : ∀ (i : ℕ) (hi : i ≤ r),
      Submodule.span ℂ (Set.range fun a : Fin i => e' (Fin.castLE hi a)) ≤
        Submodule.span ℂ (Set.range fun a : Fin i => e (Fin.castLE hi a))) (a : Fin r) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ e' a = u • e a := by
  have heq : ∀ (i : ℕ) (hi : i ≤ r),
      Submodule.span ℂ (Set.range fun a : Fin i => e' (Fin.castLE hi a)) =
        Submodule.span ℂ (Set.range fun a : Fin i => e (Fin.castLE hi a)) := by
    intro i hi
    refine Submodule.eq_of_le_of_finrank_eq (hfl i hi) ?_
    have h1 := finrank_span_eq_card
      ((TorusAtDataPf.e_linInd X τ e he).comp _ (Fin.castLE_injective hi))
    have h2 := finrank_span_eq_card
      ((TorusAtDataPf.e_linInd X τ e' he').comp _ (Fin.castLE_injective hi))
    exact h2.trans h1.symm
  have h0 : ∀ c, c ≠ a → hermC τ.1 X.Gm (e' a) (e c) = 0 := by
    intro c hc
    rcases lt_or_gt_of_ne hc with h | h
    · have hm : e c ∈ Submodule.span ℂ
          (Set.range fun k : Fin (c + 1) => e' (Fin.castLE c.2 k)) := by
        rw [heq]
        exact Submodule.subset_span ⟨Fin.last c, rfl⟩
      have := hermC_eq_zero_of_mem_span X τ e' he' _ hm a h
      rw [← hermC_conj τ.1 X.Gm_herm, this, map_zero]
    · exact hermC_eq_zero_of_mem_span X τ e he a.2
        (hfl _ _ (Submodule.subset_span ⟨Fin.last a, rfl⟩)) c h
  have h1 : e' a = (((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm (e' a) (e a)) • e a := by
    conv_lhs => rw [TorusAtDataPf.expand X τ e he (e' a)]
    refine Finset.sum_eq_single a (fun c _ hc => ?_) (by simp)
    rw [h0 c hc, mul_zero, zero_smul]
  refine ⟨_, ?_, h1⟩
  generalize ((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm (e' a) (e a) = u at h1
  have h2 := he' a a
  rw [h1, hermC_smul_left, hermC_smul_right, he, if_pos rfl] at h2
  have h3 : u * conj u = 1 := by
    have := TorusAtDataPf.sgn_sq X a
    linear_combination ((sgn X.p0 a : ℝ) : ℂ) * h2 + (1 - u * conj u) * this
  rw [Complex.mul_conj'] at h3
  have h4 : ‖u‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg u) two_ne_zero).1 h4
end GlobalTheory.ThetaRho
