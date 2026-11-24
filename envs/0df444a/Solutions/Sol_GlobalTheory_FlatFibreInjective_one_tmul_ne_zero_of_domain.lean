-- Prove2me | solution 1 for GlobalTheory.FlatFibreInjective.one_tmul_ne_zero_of_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:15:49.069539+00:00
-- url     : https://prove2.me/submissions/e9b2152a-8a82-49b7-830d-d05a77618942

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain

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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FlatFibreInjective
open TensorProduct
namespace GlobalTheory.FlatFibreInjective
theorem _root_.solution {A P k : Type} [CommRing A] [IsDomain A] [AddCommGroup P]
    [Module A P] [Field k] [Algebra A k] (hinj : Function.Injective (algebraMap A k)) (y : P)
    (hy : ∀ a : A, a • y = 0 → a = 0) : (1 : k) ⊗ₜ[A] y ≠ 0 := by
  intro h1
  letI : Algebra (FractionRing A) k := (IsFractionRing.lift hinj).toAlgebra
  haveI : IsScalarTower A (FractionRing A) k :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsFractionRing.lift_algebraMap hinj a).symm)
  haveI : Module.Flat A (FractionRing A) := IsLocalization.flat _ (nonZeroDivisors A)
  haveI : Module.Free (FractionRing A) k := Module.Free.of_divisionRing _ _
  haveI : Module.Flat (FractionRing A) k := Module.Flat.of_free
  haveI : Module.Flat A k := Module.Flat.trans _ (FractionRing A) _
  have hi : Function.Injective (LinearMap.toSpanSingleton A P y) := by
    rw [injective_iff_map_eq_zero]
    exact hy
  have h2 : (1 : k) ⊗ₜ[A] (1 : A) = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := k) _ hi
    rw [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, one_smul, map_zero, h1]
  have h3 := congrArg (TensorProduct.rid A k) h2
  rw [TensorProduct.rid_tmul, one_smul, map_zero] at h3
  exact one_ne_zero h3
end GlobalTheory.FlatFibreInjective
