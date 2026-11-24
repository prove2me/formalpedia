-- Prove2me | solution 1 for GlobalTheory.BaseRing.isIntegral_half_one_add_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:22.733795+00:00
-- url     : https://prove2.me/submissions/ec6e7410-6c9b-4c07-bcee-564116b5bea9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IntOfPrimeMulSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmModelCoefficientSubringDedekindCompatibleEmbed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BaseRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.BaseRing
theorem _root_.solution (H : Host E) : IsIntegral ℤ ((1 + H.rt0) / 2) := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, H.d + 1 = 4 * c := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have hc' : (H.d : ℂ) + 1 = 4 * c := by exact_mod_cast hc
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩
  simp
  linear_combination (1 / 4 : ℂ) * H.sqrt_neg_disc_sq - (1 / 4 : ℂ) * hc'
end GlobalTheory.BaseRing
