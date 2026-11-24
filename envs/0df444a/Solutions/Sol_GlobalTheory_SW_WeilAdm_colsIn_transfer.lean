-- Prove2me | solution 1 for GlobalTheory.SW.WeilAdm.colsIn_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:28.348235+00:00
-- url     : https://prove2.me/submissions/3d19fde0-ad5a-4cbf-805a-78e0d27b178b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction
import Theorems.Thm_GlobalTheory_SW_WeilAdm_colsIn_of_coprime

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
theorem _root_.solution {s R m : ℕ} (hs : s.Coprime (m * R)) (h1 : ∀ v ∈ Λ, (s : E) • v ∈ Λ')
    {x : Matrix (Fin n) (Fin N) E} (hx : ColsIn Λ ((R : E) • x))
    (hx' : ColsIn Λ' (((m * R : ℕ) : E) • x)) : ColsIn Λ' ((R : E) • x) := by
  refine colsIn_of_coprime (Nat.Coprime.coprime_mul_right_right hs) (fun a => h1 _ (hx a)) ?_
  rwa [Nat.cast_mul, mul_smul] at hx'
end GlobalTheory.SW.WeilAdm
