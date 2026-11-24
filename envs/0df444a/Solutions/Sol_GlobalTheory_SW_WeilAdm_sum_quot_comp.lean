-- Prove2me | solution 1 for GlobalTheory.SW.WeilAdm.sum_quot_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:25.077003+00:00
-- url     : https://prove2.me/submissions/1200c52a-345e-40a4-804e-269372188bbc

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
namespace GlobalTheory.SW.WeilAdm
theorem _root_.solution {A V : Type} [AddCommGroup A] [AddCommMonoid V] (B : AddSubgroup A)
    [Fintype (A ⧸ B)] (f : A → V) (hf : ∀ x y, x - y ∈ B → f x = f y) (α : A → A)
    (hα : ∀ x y, α x - α y ∈ B → x - y ∈ B) :
    ∑ q : A ⧸ B, f (α q.out) = ∑ q : A ⧸ B, f q.out := by
  have hinj : Function.Injective fun q : A ⧸ B => ((α q.out : A) : A ⧸ B) := by
    intro q q' h
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq_iff_sub_mem]
    exact hα _ _ (QuotientAddGroup.eq_iff_sub_mem.1 h)
  refine Fintype.sum_bijective _ (Finite.injective_iff_bijective.1 hinj) _ _ fun q => ?_
  exact hf _ _ (QuotientAddGroup.eq_iff_sub_mem.1 (QuotientAddGroup.out_eq' _).symm)
end GlobalTheory.SW.WeilAdm
