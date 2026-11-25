-- Prove2me | solution 1 for GlobalTheory.CoeffRings.isUnit_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:47.900043+00:00
-- url     : https://prove2.me/submissions/72b79476-7406-4e85-8ea5-024ad388dfcc

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
theorem _root_.solution {L : Type} [Field L] (V : ValuationSubring L) {p n : ℕ} (hp : (p : L) ∈ V.nonunits)
    (h : n.Coprime p) : IsUnit (n : V) := by
  have hpV : (p : V) ∈ IsLocalRing.maximalIdeal V :=
    ValuationSubring.coe_mem_nonunits_iff.mp (by simpa using hp)
  obtain ⟨a, b, hab⟩ : IsCoprime (n : V) (p : V) := Nat.Coprime.cast h
  by_contra hn
  have hnV : (n : V) ∈ IsLocalRing.maximalIdeal V := hn
  have h1 : (1 : V) ∈ IsLocalRing.maximalIdeal V :=
    hab ▸ add_mem (Ideal.mul_mem_left _ a hnV) (Ideal.mul_mem_left _ b hpV)
  exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
end GlobalTheory.CoeffRings
