-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.packet_surjective_actualRows_coefficients_e43f5331
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:47:29.828898+00:00
-- url     : https://prove2.me/submissions/80ca42e1-ad23-4e64-9369-ccdc8afcebff

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_linearFunctional_extension_of_independent_family_e43f5331
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_linearMap_finitePi_coordinate_representation_e43f5331
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (hrows : LinearIndependent Complex (fun rho : Row d H => actualMatrix d H rho))
    (values : Row d H → Complex) :
    ∃ a : Column d H → Complex, ∀ rho : Row d H,
      ∑ c : Column d H, a c * actualMatrix d H rho c = values rho := by
  obtain ⟨L, hL⟩ :=
    OAI.PiExponent.DeterminantContradiction.linearFunctional_extension_of_independent_family_e43f5331
      (v := fun rho : Row d H => actualMatrix d H rho) hrows values
  obtain ⟨a, ha⟩ :=
    OAI.PiExponent.DeterminantContradiction.linearMap_finitePi_coordinate_representation_e43f5331 L
  refine ⟨a, ?_⟩
  intro rho
  calc
    ∑ c : Column d H, a c * actualMatrix d H rho c =
        L (actualMatrix d H rho) := (ha (actualMatrix d H rho)).symm
    _ = values rho := hL rho