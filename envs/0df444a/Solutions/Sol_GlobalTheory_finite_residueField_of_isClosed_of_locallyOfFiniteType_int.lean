-- Prove2me | solution 1 for GlobalTheory.finite_residueField_of_isClosed_of_locallyOfFiniteType_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:49:44.516803+00:00
-- url     : https://prove2.me/submissions/2f53c5bf-41f7-436c-addd-eea9a1d5b5e2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Theorems.Thm_GlobalTheory_finite_field_of_finiteType_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Scheme.{0}}
    (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (x : X) (hx : IsClosed ({x} : Set X)) :
    Finite (X.residueField x) := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have h : LocallyOfFiniteType (X.fromSpecResidueField x ≫ π) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ π)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  have e : φ.hom = algebraMap ℤ (X.residueField x) := RingHom.ext_int _ _
  have h' : (algebraMap ℤ (X.residueField x)).FiniteType := e ▸ h
  have : Algebra.FiniteType ℤ (X.residueField x) := RingHom.finiteType_algebraMap.mp h'
  exact finite_field_of_finiteType_int _
end GlobalTheory
