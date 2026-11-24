-- Prove2me | solution 1 for GlobalTheory.SW.WeilLevel.hasLevel_of_levelL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:32:52.687263+00:00
-- url     : https://prove2.me/submissions/6fd19b33-4b0a-4800-a5e2-edfc6e0fef57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Theorems.Thm_GlobalTheory_SW_Base_mem_stdL
import Theorems.Thm_GlobalTheory_SW_Model_mem_stdL


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
theorem _root_.solution {s R : ℕ} (h1 : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n)
    (h2 : ∀ v ∈ stdL E n, (s : E) • v ∈ Λ) {φ : Matrix (Fin n) (Fin N) E → ℂ}
    (h : LevelL Λ R φ) : HasLevel (s * R) φ := by
  refine ⟨fun x hx k a => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_smul]
    exact (Model.mem_stdL _).1 (h1 _ (h.1 x hx a)) k
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact h.2 x _ fun a => h2 _ ((Model.mem_stdL _).2 fun k => hy k a)
end GlobalTheory.SW.WeilLevel
