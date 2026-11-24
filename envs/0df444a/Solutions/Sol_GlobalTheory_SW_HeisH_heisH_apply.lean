-- Prove2me | solution 1 for GlobalTheory.SW.HeisH.heisH_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:09.630548+00:00
-- url     : https://prove2.me/submissions/9cd4feea-0f2a-41d3-808d-c8d4c119fa7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws

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
theorem _root_.solution (d b : Matrix (Fin n) (Fin N) E) (φ : Matrix (Fin n) (Fin N) E → ℂ)
    (x : Matrix (Fin n) (Fin N) E) :
    heisH d b φ x = φ (x - d) * cexp (π * I * (2 * (pairT b x : ℂ) - pairT b d)) := by
  have : (∑ k, ∑ a, b k a * (2 * cc (x k a) - cc (d k a))) =
      (2 : ℚ) • (∑ k, ∑ a, b k a * cc (x k a)) - ∑ k, ∑ a, b k a * cc (d k a) := by
    rw [two_smul]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring
  rw [heisH, this, map_sub, map_smul, smul_eq_mul]
  simp [pairT]
end GlobalTheory.SW.HeisH
