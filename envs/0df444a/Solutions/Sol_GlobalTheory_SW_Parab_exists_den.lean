-- Prove2me | solution 1 for GlobalTheory.SW.Parab.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:00.270022+00:00
-- url     : https://prove2.me/submissions/8cfbb585-e638-4228-8e57-79130f69b30b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicit
import Theorems.Thm_GlobalTheory_SW_Dict_exists_den
import Theorems.Thm_GlobalTheory_SW_FourierJ_exists_den
import Theorems.Thm_GlobalTheory_SW_LinChange_exists_den


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Parab
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
omit [IsCMField E]
namespace GlobalTheory.SW.Parab
theorem _root_.solution {α β : Type} [Finite α] [Finite β] (x : Matrix α β E) :
    ∃ D : ℕ, 0 < D ∧ IntM (D • x) := by
  obtain ⟨D, hD, h⟩ := Dict.exists_den fun p : α × β => x p.1 p.2
  exact ⟨D, hD, fun i j => h (i, j)⟩
end GlobalTheory.SW.Parab
