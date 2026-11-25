-- Prove2me | solution 1 for GlobalTheory.SS.exists_monic_of_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:06:36.461709+00:00
-- url     : https://prove2.me/submissions/5025fe69-6705-4932-bbaa-142ab2b1e838

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPositiveDefiniteQuadraticFormEndomorphismsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyTorsionFiniteEndomorphismDivisibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVectorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPolyNormSqRoots
import Theorems.Thm_GlobalTheory_SS_aeval_intertwine
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
open Polynomial
namespace GlobalTheory.SS
theorem _root_.solution {N : Type} [AddCommGroup N] (c : ℕ) (π : (Fin c → ℤ) →ₗ[ℤ] N)
    (hπ : Function.Surjective π) (T : Module.End ℤ N) :
    ∃ χ : ℤ[X], χ.Monic ∧ χ.natDegree = c ∧ aeval T χ = 0 := by
  obtain ⟨S, hS⟩ := Module.projective_lifting_property π (T ∘ₗ π) hπ
  have h := aeval_intertwine π S T fun x => (LinearMap.congr_fun hS x).symm
  refine ⟨S.charpoly, S.charpoly_monic, by simp [LinearMap.charpoly_natDegree], ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hπ x
  rw [h, LinearMap.aeval_self_charpoly]
  simp
end GlobalTheory.SS
