-- Prove2me | solution 1 for GlobalTheory.CoeffRings.isIntegral_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:38.204565+00:00
-- url     : https://prove2.me/submissions/7c430ee1-bd7d-469c-a3ce-08e627bfe2fd

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
theorem _root_.solution (H : Host E) : IsIntegral ℤ ((1 + H.rt0) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d + 1 = 4 * k := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have hk' : (H.d : ℂ) + 1 = 4 * k := by exact_mod_cast hk
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k : ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C]
  simp only [eq_intCast, Int.cast_natCast]
  linear_combination (1 / 4 : ℂ) * H.sqrt_neg_disc_sq - (1 / 4 : ℂ) * hk'
end GlobalTheory.CoeffRings
