-- Prove2me | solution 1 for GlobalTheory.ThetaRho.exists_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:43:22.272133+00:00
-- url     : https://prove2.me/submissions/2bc51f4b-8a03-49f5-91be-aeb596d16d4a

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
import Theorems.Thm_GlobalTheory_ThetaRho_exists_diag_isometry
import Theorems.Thm_GlobalTheory_ThetaRho_exists_unit_frame
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_conj_conj_X
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.ThetaRho
theorem _root_.solution (X : Data E r) {x b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) (A : TorusAt X x)
    (A' : TorusAt X (lact γ (rmul x b))) :
    ∃ U : Vsp A.T.dim ≃ₗᵢ[ℂ] Vsp A'.T.dim,
      ∀ v, U (A.φ v) = A'.φ ((γ : Matrix (Fin r) (Fin r) E).mulVec v) := by
  have hcase : ∀ σ : E →+* ℂ, (∃ τ : X.Ψ, σ = τ.1) ∨
      ∃ τ : X.Ψ, σ = ComplexEmbedding.conjugate τ.1 := by
    intro σ
    by_cases h : σ ∈ X.Ψ
    · exact Or.inl ⟨⟨σ, h⟩, rfl⟩
    · refine Or.inr ⟨⟨ComplexEmbedding.conjugate σ, ?_⟩, (TorusAtDataPf.conj_conj_X σ).symm⟩
      rw [X.cmType, TorusAtDataPf.conj_conj_X]
      exact h
  have hdim : ∀ σ, A'.T.dim σ = A.T.dim σ := by
    intro σ
    rcases hcase σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · rw [A.dim_pos, A'.dim_pos]
    · rw [A.dim_neg, A'.dim_neg]
  let ε : Idx A'.T.dim ≃ Idx A.T.dim := Equiv.sigmaCongrRight fun σ => finCongr (hdim σ)
  have key : ∀ i : Idx A'.T.dim, ∃ w : ℂ, ‖w‖ = 1 ∧ ∀ v,
      A'.φ ((γ : Matrix (Fin r) (Fin r) E).mulVec v) i = w * A.φ v (ε i) := by
    rintro ⟨σ, a⟩
    rcases hcase σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · obtain ⟨u, hu, h⟩ := exists_unit_frame X hb hγ A A' τ
        (Fin.castLE (by rw [A'.dim_pos τ]; exact X.p0_le) a)
      refine ⟨u, hu, fun v => ?_⟩
      change _ = u * A.φ v ⟨τ.1, Fin.cast (hdim _) a⟩
      rw [A'.coord_pos, A.coord_pos, h, mul_left_comm]
      rfl
    · obtain ⟨u, hu, h⟩ := exists_unit_frame X hb hγ A A' τ
        ⟨X.p0 + a.1, by
          have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (A'.dim_neg τ)
          have := X.p0_le
          omega⟩
      refine ⟨conj u, by rw [Complex.norm_conj, hu], fun v => ?_⟩
      change _ = conj u * A.φ v ⟨ComplexEmbedding.conjugate τ.1, Fin.cast (hdim _) a⟩
      rw [A'.coord_neg, A.coord_neg, h, ← mul_neg, map_mul, mul_left_comm]
      rfl
  choose w hw hkey using key
  obtain ⟨U, hU⟩ := exists_diag_isometry ε w hw
  refine ⟨U, fun v => ?_⟩
  ext i
  rw [hU, hkey]
end GlobalTheory.ThetaRho
