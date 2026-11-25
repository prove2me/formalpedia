-- Prove2me | solution 1 for GlobalTheory.CoeffRings.mem_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:39:06.031686+00:00
-- url     : https://prove2.me/submissions/eecfd944-ebee-48c0-b963-1dc480784880

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoefficientFieldIntegersDedekindFractionField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory GlobalTheory.CoeffRings
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.CoeffRings
theorem _root_.solution {L : Type} [Field L] (W : ValuationSubring L) {x : L} (hx : IsIntegral ℤ x) : x ∈ W := by
  have h : IsIntegral W x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := L)).mp h
  exact hy ▸ y.2
end GlobalTheory.CoeffRings
