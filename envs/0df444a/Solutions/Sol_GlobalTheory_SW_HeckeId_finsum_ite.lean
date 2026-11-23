-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.finsum_ite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:59.54589+00:00
-- url     : https://prove2.me/submissions/431b5008-f4af-4e75-a67f-9303e553e648

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise

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
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {ι : Type} {S : Set ι} (hS : S.Finite) (p : ι → Prop) [DecidablePred p] (c : ℂ) (f : ι → ℂ)
    (hf : ∀ i ∈ S, f i = if p i then c else 0) :
    ∑ᶠ i ∈ S, f i = ({i ∈ S | p i}.ncard : ℂ) * c := by
  rw [finsum_mem_congr rfl hf, finsum_mem_eq_finite_toFinset_sum _ hS, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, ← Set.ncard_coe_finset]
  congr 3
  ext i
  simp
end GlobalTheory.SW.HeckeId
