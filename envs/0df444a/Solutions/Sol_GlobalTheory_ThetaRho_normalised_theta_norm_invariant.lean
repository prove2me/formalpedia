-- Prove2me | solution 1 for GlobalTheory.ThetaRho.normalised_theta_norm_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:49:38.656545+00:00
-- url     : https://prove2.me/submissions/e9524bb9-ae44-4ce9-a9d0-7d3b9e5a20c0

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
import Theorems.Thm_GlobalTheory_ThetaRho_ratio_eq
import Theorems.Thm_GlobalTheory_ThetaRho_exists_isometry
import Theorems.Thm_GlobalTheory_torusAt_eps_indep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pointwiseNormSq_add_period


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
namespace GlobalTheory.ThetaRho
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ (A : TorusAt X.toData x) (A' : TorusAt X.toData (lact γ (rmul x b))) (v : Fin r → E), A'.T.ptN2 1 A'.s (fun _ => A'.φ ((γ : Matrix (Fin r) (Fin r) E).mulVec v)) / A'.T.l2 1 A'.s = A.T.ptN2 1 A.s (fun _ => A.φ v) / A.T.l2 1 A.s ∧ ∀ u ∈ X.Λ, A.T.ptN2 1 A.s (fun _ => A.φ (v + u)) / A.T.l2 1 A.s = A.T.ptN2 1 A.s (fun _ => A.φ v) / A.T.l2 1 A.s := by
  intro E _ _ _ r X hw x _ b hb γ hγ A A' v
  refine ⟨?_, fun u hu => ?_⟩
  · obtain ⟨U, hU⟩ := exists_isometry X.toData hb hγ A A'
    have hL : ∀ y, y ∈ A.T.L ↔ U y ∈ A'.T.L := by
      intro y
      rw [A.lat, A'.lat]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨_, (hγ.2 w).1 hw, (hU w).symm⟩
      · rintro ⟨w, hw, h⟩
        have e : (γ : Matrix (Fin r) (Fin r) E).mulVec
            (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec w) = w := by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.one_mulVec]
        refine ⟨_, (hγ.2 _).2 (e.symm ▸ hw), U.injective ?_⟩
        rw [hU, e, h]
    have he : ∀ y ∈ A.T.L, A'.T.eps (U y) = A.T.eps y := by
      intro y hy
      obtain ⟨w, hw', rfl⟩ := (A.lat y).1 hy
      rw [hU]
      exact GlobalTheory.torusAt_eps_indep E r X hw x _ A A' γ hγ w hw'
    rw [← hU]
    exact ratio_eq A.T A'.T U hL he A.s_mem A.s_ne A'.s_mem A'.s_ne _
  · rw [map_add]
    congr 1
    exact pointwiseNormSq_add_period A.T A.s_mem (γ := fun _ => A.φ u)
      (fun _ => (A.lat _).2 ⟨u, hu, rfl⟩) (fun _ => A.φ v)
end GlobalTheory.ThetaRho
