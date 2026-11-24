-- Prove2me | solution 1 for GlobalTheory.SS.LiftTorus.exists_eq_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.476643+00:00
-- url     : https://prove2.me/submissions/59a25149-3b1a-4e10-8904-201357f8d1df

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftOneParameterQuotientTorus
import Theorems.Thm_GlobalTheory_TorsorUnit_ev_single


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
theorem _root_.solution (hα : α.FaithfullyFlat)
    (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) (c : C)
    (hc : ρ c = AddMonoidAlgebra.single 0 c) : ∃ a, α a = c := by
  letI : Algebra A C := α.toAlgebra
  haveI : Module.FaithfullyFlat A C := hα
  obtain ⟨φ, hφ⟩ := (h (TensorProduct A C C)).2.2.2
    (Algebra.TensorProduct.includeRight : C →ₐ[A] TensorProduct A C C).toRingHom
    Algebra.TensorProduct.includeLeftRingHom
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := A) (A := C) (B := C)).symm
  have h1 := RingHom.congr_fun hφ c
  rw [RingHom.comp_apply, hc, ev_single] at h1
  refine (Algebra.IsEffective.of_faithfullyFlat A C c).1 ?_
  rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
  simpa using h1
end GlobalTheory.SS.LiftTorus
