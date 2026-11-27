-- Prove2me | solution 1 for GlobalTheory.ThetaRho.exists_unit_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:21.271836+00:00
-- url     : https://prove2.me/submissions/f03ca28f-56b5-4be4-9b5c-ddec0154ec02

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
import Theorems.Thm_GlobalTheory_ThetaRho_hermC_map_mulVec
import Theorems.Thm_GlobalTheory_ThetaRho_exists_unit_of_flag
import Theorems.Thm_GlobalTheory_SemicharIndep_smul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
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
theorem _root_.solution (X : Data E r) {x b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) (A : TorusAt X x)
    (A' : TorusAt X (lact γ (rmul x b))) (τ : X.Ψ) (a : Fin r) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ v : Fin r → E,
      hermC τ.1 X.Gm (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E).mulVec v)) (A'.e τ a) =
        u * hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ a) := by
  set g := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hg
  have hst : ∀ u w, hermC τ.1 X.Gm (g.mulVec u) (g.mulVec w) = hermC τ.1 X.Gm u w :=
    hermC_map_mulVec X.Gm hγ.1 τ.1
  obtain ⟨u, hu, h⟩ := exists_unit_of_flag X τ (fun a => g.mulVec (A.e τ a)) (A'.e τ)
    (fun a b => by rw [hst, A.e_orth]) (A'.e_orth τ) (fun i hi => by
      rw [A'.e_flag τ i hi]
      have hmap : Submodule.span ℂ (Set.range fun a : Fin i => g.mulVec (A.e τ (Fin.castLE hi a))) =
          (Submodule.span ℂ (Set.range fun a : Fin i => A.e τ (Fin.castLE hi a))).map
            g.mulVecLin := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      rw [hmap, A.e_flag τ i hi, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine ⟨∑ c, b τ c (Fin.castLE hi k) • col (mat x τ) c, ?_, ?_⟩
      · refine Submodule.sum_mem _ fun c _ => ?_
        by_cases hc : (c : ℕ) < i
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hc⟩, rfl⟩)
        · rw [(hb τ).2 c (Fin.castLE hi k) (by
            have := k.2
            rw [Fin.lt_def]
            simp only [Fin.val_castLE]
            omega), zero_smul]
          exact Submodule.zero_mem _
      · funext j
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, col, mat, lact, rmul,
          Matrix.of_apply, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hg,
          mul_comm]
        rfl) a
  refine ⟨conj u, by rw [Complex.norm_conj, hu], fun v => ?_⟩
  have hemb : Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E).mulVec v) =
      g.mulVec (Data.emb τ.1 v) := by
    funext j
    simp [Data.emb, hg, Matrix.mulVec, dotProduct]
  rw [h, hermC_smul_right, hemb, hst]
end GlobalTheory.ThetaRho
