-- Prove2me | solution 1 for GlobalTheory.NormCurve.finite_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:51:16.007749+00:00
-- url     : https://prove2.me/submissions/9e32f495-2847-4a33-ad40-2962f3322b26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsPrimeLeNotMemRingKrullDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteIntegralClosureOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsProperCurveThroughPoint
import Theorems.Thm_GlobalTheory_NormCurve_exists_eq_div
import Theorems.Thm_GlobalTheory_integralClosure_restrictScalars_of_isIntegral
import Theorems.Thm_ReciprocityTheory_CA_exists_dim_trdeg_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.NormCurve
namespace GlobalTheory.NormCurve
theorem _root_.solution (k : Type) {B R : Type} [Field k] [PerfectField k] [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) :
    Module.Finite B (integralClosure B R) ∧ ∀ [Algebra k R] [IsScalarTower k B R],
      ringKrullDim (B ⧸ RingHom.ker (algebraMap B R)) ≤ 1 → Algebra.trdeg k R ≤ 1 := by
  let A := B ⧸ RingHom.ker (algebraMap B R)
  haveI : (RingHom.ker (algebraMap B R)).IsPrime := RingHom.ker_isPrime _
  letI : Algebra A R := (RingHom.kerLift (algebraMap B R)).toAlgebra
  haveI : IsScalarTower B A R := .of_algebraMap_eq fun x => (RingHom.kerLift_mk _ x).symm
  haveI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (RingHom.kerLift_injective _)
  haveI : IsFractionRing A R := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, e⟩ := exists_eq_div h z
    exact ⟨algebraMap B _ x, algebraMap B _ y, by
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]⟩
  constructor
  · haveI := NormFin.finite_integralClosure_of_perfectField k A R R
    haveI : Module.Finite B (integralClosure A R) := Module.Finite.trans A _
    have h' : Module.Finite B ((integralClosure A R).restrictScalars B) := this
    rwa [integralClosure_restrictScalars_of_isIntegral] at h'
  · intro _ _ hd
    haveI : IsScalarTower k A R := .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k B R, IsScalarTower.algebraMap_apply k B A,
        ← IsScalarTower.algebraMap_apply B A R]
    obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
    haveI : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap k A).injective
    haveI : Algebra.IsAlgebraic A R := IsLocalization.isAlgebraic R (nonZeroDivisors A)
    rw [← trdeg_add_eq k A (A := R), trdeg_eq_zero (R := A) (A := R), add_zero, hs2]
    rw [hs1] at hd
    exact_mod_cast hd
end GlobalTheory.NormCurve
