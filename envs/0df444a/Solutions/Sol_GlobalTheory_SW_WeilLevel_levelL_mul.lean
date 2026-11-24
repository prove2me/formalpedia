-- Prove2me | solution 1 for GlobalTheory.SW.WeilLevel.levelL_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:25.335436+00:00
-- url     : https://prove2.me/submissions/76b11807-1849-4de4-902c-a0f90ec56494

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Theorems.Thm_GlobalTheory_SW_WeilLevel_colsIn_smul

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilLevel
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ : Lt E n}
omit [IsCMField E]
namespace GlobalTheory.SW.WeilLevel
theorem _root_.solution {R : ℕ} {φ : Matrix (Fin n) (Fin N) E → ℂ} (h : LevelL Λ R φ) (m : ℕ) :
    LevelL Λ (m * R) φ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_smul]; exact colsIn_smul m (h.1 x hx)
  · rw [Nat.cast_mul, mul_comm, mul_smul]; exact h.2 x _ (colsIn_smul m hy)
end GlobalTheory.SW.WeilLevel
