-- Prove2me | solution 1 for GlobalTheory.SW.Decay.coef_psd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:58:19.110632+00:00
-- url     : https://prove2.me/submissions/d6f6684d-4588-428b-bc3a-2840ab1230f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsFourierExpansionHolomorphicTubeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDualStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TracePairingGeDetImPowHermitianHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DecayOfVanishingAtCusps
import Theorems.Thm_GlobalTheory_SW_Decay_herm_map
import Theorems.Thm_GlobalTheory_SW_Decay_coef_bound
import Theorems.Thm_GlobalTheory_SW_Decay_trace_vecMulVec
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_quad_im


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Decay
open MeasureTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {N : ℕ}
variable {m : ℕ} {X : (Fin m → ℝ) → CM Ψ N N} {f : CM Ψ N N → ℂ} {T : Matrix (Fin N) (Fin N) E}
  {a : ℂ} {η B : ℝ}
namespace GlobalTheory.SW.Decay
theorem _root_.solution (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T) (hη : 0 < η)
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) (ha : IsCoef X f T a) (h0 : a ≠ 0) (τ : Ψ) :
    (T.map τ.1).PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨herm_map hT _, fun u => ?_⟩
  rw [Complex.le_def]
  refine ⟨?_, (ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.quad_im (herm_map hT _) u).symm⟩
  by_contra hneg
  simp only [zero_re, not_le] at hneg
  set q := (star u ⬝ᵥ T.map τ.1 *ᵥ u).re with hq
  set c := ∑ σ : Ψ, (T.map σ.1 * ((η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))).trace.re with hc
  have key : ∀ t : ℝ, 0 ≤ t → ‖a‖ ≤ B * Real.exp (2 * π * (c + q * t)) := by
    intro t ht
    have := coef_bound hX hT hη hB ha (Y := fun σ => (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) +
      if σ = τ then (t : ℂ) • vecMulVec u (star u) else 0) (fun σ => by
        rw [add_sub_cancel_left]
        split_ifs
        · exact (posSemidef_vecMulVec_self_star u).smul (by exact_mod_cast ht)
        · exact PosSemidef.zero)
    convert this using 4
    simp only [Matrix.mul_add, trace_add, add_re, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single τ]
    · rw [if_pos rfl, Matrix.mul_smul, trace_smul, trace_vecMulVec, smul_eq_mul, re_ofReal_mul,
        mul_comm]
    · intro σ _ h; simp [h]
    · simp
  have lim : Tendsto (fun t : ℝ => B * Real.exp (2 * π * (c + q * t))) atTop (𝓝 (B * 0)) := by
    refine Tendsto.const_mul _ (Real.tendsto_exp_atBot.comp ?_)
    exact Tendsto.const_mul_atBot (by positivity)
      (tendsto_atBot_add_const_left _ _ (tendsto_id.const_mul_atTop_of_neg hneg))
  have := ge_of_tendsto lim ((eventually_ge_atTop 0).mono key)
  exact h0 (norm_le_zero_iff.1 (by simpa using this))
end GlobalTheory.SW.Decay
