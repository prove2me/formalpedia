-- Prove2me | solution 1 for GlobalTheory.SW.UnitaryLeft.expo_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:55:44.077235+00:00
-- url     : https://prove2.me/submissions/ddc8b16e-089f-4061-82b8-988396a2eb91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_sum_rows_unitary
import Theorems.Thm_P2M_GlobalTheory_SW_UnitaryLeft_sum_rows_unitary__05b53fb98137
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_unit_map

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UnitaryLeft
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
namespace GlobalTheory.SW.UnitaryLeft
theorem _root_.solution {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1)
    (x : Matrix (Fin n) (Fin N) E) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    expo Ψ (h * x) Z (mv Ψ h z) (mv' Ψ h z') = expo Ψ x Z z z' := by
  unfold expo
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e1 : ∀ (y : Matrix (Fin n) (Fin N) E) k, (fun a => τ.1 (y k a)) = (y.map τ.1) k :=
    fun _ _ => rfl
  have e2 : ∀ (y : Matrix (Fin n) (Fin N) E) k,
      (fun a => conj (τ.1 (y k a))) = ((y.map τ.1).map conj) k := fun _ _ => rfl
  simp only [e1, e2, Finset.sum_add_distrib, mv, mv']
  rw [Matrix.map_mul, Matrix.map_mul, sum_rows_unitary _ _ (unit_map hh τ.1),
    sum_rows_unitary' _ _ (unit_map hh τ.1), sum_rows_unitary' _ _ (unit_map hh τ.1)]
end GlobalTheory.SW.UnitaryLeft
