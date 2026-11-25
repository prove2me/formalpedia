-- Prove2me | solution 1 for GlobalTheory.SW.EisTrans.hFac_inv_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:01:09.698827+00:00
-- url     : https://prove2.me/submissions/d2285bb7-9467-4c4f-9a09-3666e795ab8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubSmulOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Theorems.Thm_GlobalTheory_SW_EisTrans_exists_mem_HnGe
import Theorems.Thm_GlobalTheory_SW_EisTrans_entry_bound
import Theorems.Thm_GlobalTheory_SW_EisTrans_hFac_zero
import Theorems.Thm_GlobalTheory_SW_HAct_map_mem
import Theorems.Thm_GlobalTheory_SW_HermComp_row_rel
import Theorems.Thm_GlobalTheory_SW_unitary_act_halfSpace


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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisTrans
variable {N : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n : ℕ}
namespace GlobalTheory.SW.EisTrans
theorem _root_.solution {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (z z' : CM Ψ n N) :
    ∃ K : ℝ, ∀ γ ∈ UU E N,
      ‖(hFac Ψ γ Z z z')⁻¹‖ ≤ K * ‖(hFac Ψ γ Z (0 : CM Ψ n N) 0)⁻¹‖ := by
  obtain ⟨δ, hδ, hZ'⟩ := exists_mem_HnGe Ψ hZ
  refine ⟨∏ τ : Ψ, Real.exp (‖2 * (π : ℂ) * I‖ * ∑ k, ∑ a, ‖z' τ k a‖ * ∑ b, δ⁻¹ * ‖z τ k b‖),
    fun γ hγ => ?_⟩
  rw [hFac_zero, hFac, Finset.prod_mul_distrib, mul_inv, norm_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [← Finset.prod_inv_distrib, norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
  rw [← Complex.exp_neg]
  refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
  rw [norm_neg, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hb := entry_bound hδ (HermComp.row_rel _ (HAct.map_mem τ.1 hγ)).2
    (((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).1 τ).1 (hZ' τ)
  refine norm_sum_le_of_le _ fun k _ => norm_sum_le_of_le _ fun a _ => ?_
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [Matrix.mulVec, dotProduct]
  refine norm_sum_le_of_le _ fun b _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hb a b) (norm_nonneg _)
end GlobalTheory.SW.EisTrans
