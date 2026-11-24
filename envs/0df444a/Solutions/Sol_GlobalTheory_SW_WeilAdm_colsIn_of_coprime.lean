-- Prove2me | solution 1 for GlobalTheory.SW.WeilAdm.colsIn_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:25.032813+00:00
-- url     : https://prove2.me/submissions/c5419193-a77a-445e-9b0a-43e7fcb9f2dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction
import Theorems.Thm_GlobalTheory_SW_Base_mem_of_coprime
import Theorems.Thm_GlobalTheory_SW_Model_mem_of_coprime


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilAdm
open WeilLevel Base
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ Λ' : Lt E n}
omit [IsCMField E]
namespace GlobalTheory.SW.WeilAdm
theorem _root_.solution {s t : ℕ} (h : s.Coprime t) {x : Matrix (Fin n) (Fin N) E}
    (h1 : ColsIn Λ ((s : E) • x)) (h2 : ColsIn Λ ((t : E) • x)) : ColsIn Λ x :=
  fun a => mem_of_coprime Λ h (h1 a) (h2 a)
end GlobalTheory.SW.WeilAdm
