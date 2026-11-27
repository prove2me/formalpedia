-- Prove2me | solution 1 for GlobalTheory.TwoLines.mem_SSgt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:34:51.149575+00:00
-- url     : https://prove2.me/submissions/05d3afe8-100e-43dc-9648-f6b3dbc64c47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
import Theorems.Thm_P2M_GlobalTheory_TwoLines_lact_one__d9ee5c0b5a07
import Theorems.Thm_GlobalTheory_TwoLines_colSq_pos
import Theorems.Thm_GlobalTheory_TwoLines_pnorm_sq
import Theorems.Thm_GlobalTheory_TwoLines_not_isIso
import Theorems.Thm_GlobalTheory_TwoLines_chi_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
open GlobalTheory GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.TwoLines
theorem _root_.solution {X : Data E 2} (hG : X.Gm = 1) (hΓ : X.Γ = ⊥) {la : Wt X.Ψ 2}
    {m : ℕ} (h0 : ∀ τ, la τ 0 = m) (h1 : ∀ τ, la τ 1 = 0) {P : Frame X.Ψ 2 → ℂ}
    (hd : Differentiable ℂ P)
    (he : ∀ x, ∀ b ∈ Bor X.Ψ 2, P (rmul x b) = (∏ τ, b τ 0 0) ^ m * P x)
    {C : ℝ} (hb : ∀ x, ‖P x‖ ^ 2 ≤ C * (∏ τ, colSq x τ) ^ m) (c : ℝ) : P ∈ X.SSgt la c := by
  refine ⟨⟨⟨⟨hd.differentiableOn, fun x _ b hb => ?_, fun γ hγ x _ => ?_⟩, ⟨√C, fun x hx => ?_⟩⟩,
    fun ξ h => (not_isIso hG ξ h).elim⟩, fun ξ h => (not_isIso hG ξ h).elim⟩
  · rw [he x b hb, bchar, ← Finset.prod_pow]
    simp [Fin.prod_univ_two, h0, h1]
  · rw [hΓ, Subgroup.mem_bot] at hγ
    rw [hγ, chi_one, lact_one', one_mul]
  · apply Real.le_sqrt_of_sq_le
    rw [pnorm_sq hG hx h0 h1, div_le_iff₀ (pow_pos (Finset.prod_pos fun τ _ => colSq_pos (hx τ).1) _)]
    exact hb x
end GlobalTheory.TwoLines
