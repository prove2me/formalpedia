-- Prove2me | solution 1 for GlobalTheory.SW.WeilAdm.mem_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:17.525848+00:00
-- url     : https://prove2.me/submissions/2c29ea3a-ca93-47b4-964d-f5a670582d21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction

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
theorem _root_.solution {s : ℕ} (x : cols Λ N) :
    x ∈ ((cols Λ N).map (nsmulAddMonoidHom s)).addSubgroupOf (cols Λ N) ↔
      ∃ y ∈ cols Λ N, (s : E) • y = x.1 := by
  simp [AddSubgroup.mem_addSubgroupOf, Nat.cast_smul_eq_nsmul]
end GlobalTheory.SW.WeilAdm
