-- Prove2me | solution 1 for GlobalTheory.ZM.IntegersAway.exists_tBase_fractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:11.77627+00:00
-- url     : https://prove2.me/submissions/eac52049-084c-40e7-9225-528d713deb40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsPrimitiveRootMapOfNatCastNeZero
import Theorems.Thm_GlobalTheory_ZM_IntegersAway_exists_tBase_of_numberField

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.IntegersAway
namespace GlobalTheory.ZM.IntegersAway
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ (o : Type) (_ : CommRing o) (b : TBase o l.A) (em : o →+* ℂ) (ρ : o) (_ : Algebra o (KA l)), ArBase em ∧ IsFractionRing o (KA l) ∧ (∀ x, ((algebraMap o (KA l) x : KA l) : ℂ) = em x) ∧ algebraMap o (KA l) ρ = (baseKA l).ρ ∧ algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ := by
  intro E _ _ _ H l
  have : FiniteDimensional ℚ (KA l) := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    rcases hx with rfl | rfl
    · refine IsIntegral.of_pow two_pos ?_
      rw [H.sqrt_neg_disc_sq]
      exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
    · refine IsIntegral.of_pow l.A_pos ?_
      rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
      exact isIntegral_one
  have : NumberField (KA l) := {}
  have hr : IsIntegral ℤ (baseKA l).ρ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [(baseKA l).ρ_sq]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := KA l) (x := (H.d : ℤ))).neg
  exact exists_tBase_of_numberField (KA l).val.toRingHom l.A_pos (baseKA l).ζ_prim hr
end GlobalTheory.ZM.IntegersAway
