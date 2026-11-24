-- Prove2me | solution 1 for GlobalTheory.SW.HeisH.thH_heisH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:58:44.674834+00:00
-- url     : https://prove2.me/submissions/2840c9bb-185a-49ae-9206-e527f4c25f1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Theorems.Thm_GlobalTheory_SW_HeisH_shift_transpose
import Theorems.Thm_GlobalTheory_SW_HeisH_pairT_eq
import Theorems.Thm_GlobalTheory_SW_HeisH_pairT_add
import Theorems.Thm_GlobalTheory_SW_HeisH_heisH_apply
import Theorems.Thm_GlobalTheory_SW_Base_expo_eq_trace


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeisH
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.HeisH
theorem _root_.solution (hΨ : IsType Ψ) (d b : Matrix (Fin n) (Fin N) E)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    thH Ψ (heisH d b φ) Z z z' = cexp (2 * π * I * expo Ψ d Z z z' + π * I * (pairT b d : ℂ)) *
      thH Ψ φ Z (fun τ => z τ + (b.map τ.1).map conj + (d.map τ.1).map conj * (Z τ)ᵀ)
        (fun τ => z' τ + b.map τ.1 + d.map τ.1 * Z τ) := by
  unfold thH
  rw [← tsum_mul_left, ← (Equiv.addRight d).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [Equiv.coe_addRight, heisH_apply, add_sub_cancel_right, mul_assoc, mul_left_comm _ (φ x),
    ← Complex.exp_add, ← Complex.exp_add, pairT_add]
  congr 2
  have : expo Ψ (x + d) Z z z' + pairT b x = expo Ψ d Z z z' + expo Ψ x Z
      (fun τ => z τ + (b.map τ.1).map conj + (d.map τ.1).map conj * (Z τ)ᵀ)
      (fun τ => z' τ + b.map τ.1 + d.map τ.1 * Z τ) := by
    simp only [Base.expo_eq_trace, pairT_eq hΨ, ← Finset.sum_add_distrib, shift_transpose]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Matrix.map_add _ (map_add τ.1)]
    simp only [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, trace_add, Matrix.mul_assoc]
    ring
  push_cast
  linear_combination 2 * π * I * this
end GlobalTheory.SW.HeisH
