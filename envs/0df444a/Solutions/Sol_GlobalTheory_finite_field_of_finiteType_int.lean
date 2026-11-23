-- Prove2me | solution 1 for GlobalTheory.finite_field_of_finiteType_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:28.436228+00:00
-- url     : https://prove2.me/submissions/aedbfa82-b3c2-419f-a760-89b21089a32f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_isJacobsonRing_int


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
theorem _root_.solution (K : Type*) [Field K] [Algebra.FiniteType ℤ K] :
    Finite K := by
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have : Module.Finite ℤ K := finite_of_finite_type_of_isJacobsonRing ℤ _
  obtain ⟨p, hp⟩ := CharP.exists K
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := CharP.charP_to_charZero K
    exact Int.not_isField (isField_of_isIntegral_of_isField
      (algebraMap ℤ K).injective_int (Field.toIsField _))
  have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero K p).resolve_right hp0⟩
  let := ZMod.algebra K p
  have : Module.Finite (ZMod p) K := Module.Finite.of_restrictScalars_finite ℤ _ _
  exact Module.finite_of_finite (ZMod p)
end GlobalTheory
