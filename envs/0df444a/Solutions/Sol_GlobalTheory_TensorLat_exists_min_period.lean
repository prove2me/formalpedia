-- Prove2me | solution 1 for GlobalTheory.TensorLat.exists_min_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:55:45.28838+00:00
-- url     : https://prove2.me/submissions/1fbee013-6b1e-414e-ad6e-8a37e0712eaa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LeMulNormFlatOfSelfDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormalisedThetaValueBound
import Theorems.Thm_GlobalTheory_ShortVectors_finrank_eq
import Theorems.Thm_GlobalTheory_TensorLat_le_mul_norm_flat_of_selfDual
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution (T : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ T.L, x ≠ 0 → lam ≤ ‖x‖) :
    ∃ lam' : ℝ, 0 < lam' ∧ (∀ γ ∈ tensorLat T Λ', γ ≠ 0 → lam' ≤ ‖flat γ‖) ∧
      (1 + 4 * Real.sqrt (2 * Fintype.card (Fin n × Idx T.dim)) / (Real.sqrt Real.pi * lam')) ^
          Fintype.card (Fin n × Idx T.dim) =
        (1 + 4 * Real.sqrt (2 * Fintype.card (Idx T.dim) * n) *
          (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^
          (Fintype.card (Idx T.dim) * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pos, fun γ _ h => absurd (Subsingleton.elim γ 0) h, by simp⟩
  have hf : (0 : ℝ) < fdeg E := by
    have h1 := ShortVectors.finrank_eq (E := E)
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact_mod_cast (by omega : 0 < fdeg E)
  have hr : 0 < rdE E := Real.rpow_pos_of_pos
    (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero E)) _
  have hρ : 0 < 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E := by positivity
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  set ρ := 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E with hρdef
  refine ⟨lam / ρ, by positivity, fun γ hγ h0 => ?_, ?_⟩
  · rw [div_le_iff₀' hρ]
    exact le_mul_norm_flat_of_selfDual T Λ' hfg hint hdual hmin hγ h0
  · rw [Fintype.card_prod, Fintype.card_fin, mul_comm n, Nat.cast_mul, ← mul_assoc]
    congr 2
    field_simp
end GlobalTheory.TensorLat
