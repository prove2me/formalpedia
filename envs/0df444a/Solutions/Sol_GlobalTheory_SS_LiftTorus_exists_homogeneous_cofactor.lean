-- Prove2me | solution 1 for GlobalTheory.SS.LiftTorus.exists_homogeneous_cofactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:59:05.414447+00:00
-- url     : https://prove2.me/submissions/cc359327-283c-49e5-9008-4ec247ddf8bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftOneParameterQuotientTorus
import Theorems.Thm_GlobalTheory_SS_LiftTorus_coaction_base
import Theorems.Thm_GlobalTheory_TorsorUnit_coaction_coeff


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
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LiftTorus
open GlobalTheory.TorsorUnit
variable {X : Type} [AddCommGroup X] {A C : Type} [CommRing A] [CommRing C]
  {α : A →+* C} {ρ : C →+* AddMonoidAlgebra C X}
namespace GlobalTheory.SS.LiftTorus
theorem _root_.solution (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) {χ : X}
    {c c' : C} {a : A} (hcc : c * c' = α a) (hc : ρ c = AddMonoidAlgebra.single χ c) :
    ∃ d, c * d = α a ∧ ρ d = AddMonoidAlgebra.single (-χ) d := by
  refine ⟨(ρ c').coeff (-χ), ?_, coaction_coeff (h _) _ _⟩
  have h1 := congrArg (fun z => (ρ z).coeff 0) hcc
  simp only [map_mul, hc, coaction_base h] at h1
  simpa using h1
end GlobalTheory.SS.LiftTorus
