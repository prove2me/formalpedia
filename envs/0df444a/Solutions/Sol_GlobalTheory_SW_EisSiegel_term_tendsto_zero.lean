-- Prove2me | solution 1 for GlobalTheory.SW.EisSiegel.term_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:16:08.320973+00:00
-- url     : https://prove2.me/submissions/d293b813-f6d3-4acc-8196-f0209e5e285e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelOperatorHermitianEisensteinSeries
import Theorems.Thm_GlobalTheory_SW_EisSiegel_hDen_growth
import Theorems.Thm_GlobalTheory_SW_EisTrans_hFac_zero
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisSiegel
variable {N : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n : ℕ}
namespace GlobalTheory.SW.EisSiegel
theorem _root_.solution (hΨ : IsType Ψ) (hn : n ≠ 0) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) (hv : γ.toBlocks₂₁ *ᵥ v ≠ 0)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    Tendsto (fun t : ℝ => eisTerm Ψ γ φ (pushZ Ψ Z v t) 0 0) atTop (𝓝 0) := by
  have hne : Nonempty Ψ := by
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : σ ∈ Ψ
    · exact ⟨⟨σ, h⟩⟩
    · exact ⟨⟨_, not_not.1 ((hΨ σ).not.1 h)⟩⟩
  simp only [eisTerm, EisTrans.hFac_zero, ← Finset.prod_inv_distrib]
  have h1 : ∀ τ : Ψ, Tendsto (fun t : ℝ => ((hDen Ψ γ (pushZ Ψ Z v t) τ).det ^ n)⁻¹) atTop
      (𝓝 0) := by
    intro τ
    obtain ⟨h0, c, -, h2, h3⟩ := hDen_growth Ψ hγ hZ v τ
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv, norm_pow]
    refine Tendsto.inv_tendsto_atTop ((tendsto_pow_atTop hn).comp (tendsto_atTop_mono h3 ?_))
    exact Tendsto.const_mul_atTop (norm_pos_iff.2 h0)
      (tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const (h2 hv)))
  have h2 := (tendsto_finset_prod Finset.univ fun τ _ => h1 τ).const_mul (weil Ψ γ φ 0)
  rwa [Finset.prod_const, zero_pow (Finset.card_univ.trans_ne Fintype.card_ne_zero), mul_zero] at h2
end GlobalTheory.SW.EisSiegel
