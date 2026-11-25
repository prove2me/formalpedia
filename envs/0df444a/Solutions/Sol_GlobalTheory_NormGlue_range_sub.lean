-- Prove2me | solution 1 for GlobalTheory.NormGlue.range_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:19:40.653801+00:00
-- url     : https://prove2.me/submissions/ae155cd8-99e5-470d-a93e-120f0afaa22c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_CompanionTheory
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_RegularOfBoundedAtPadicAlgClPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleOfNormOneGenerators
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory
open GlobalTheory.NormGlue
namespace GlobalTheory.NormGlue
theorem _root_.solution {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : Set X} (z : Sp F)
    (h : x z ∈ U) : Set.range x ⊆ U := by
  have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  rintro _ ⟨y, rfl⟩
  rwa [Subsingleton.elim y z]
end GlobalTheory.NormGlue
