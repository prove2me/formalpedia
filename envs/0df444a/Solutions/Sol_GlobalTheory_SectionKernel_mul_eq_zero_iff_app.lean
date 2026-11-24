-- Prove2me | solution 1 for GlobalTheory.SectionKernel.mul_eq_zero_iff_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:54:57.091532+00:00
-- url     : https://prove2.me/submissions/05b23f65-0eab-4915-980f-879fa6f259c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSectionEqMulOfVanishingModElement
import Theorems.Thm_GlobalTheory_SectionKernel_mem_map_of_flat
import Theorems.Thm_GlobalTheory_SectionKernel_cst_eq
import Theorems.Thm_GlobalTheory_SmallExtLift_app_cst
import Theorems.Thm_GlobalTheory_SmallExtLift_cst_flat
import Theorems.Thm_GlobalTheory_SmallExtLift_mem_of_app_eq_zero
import Theorems.Thm_GlobalTheory_SmallExtLift_mul_eq_zero_of_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SectionKernel
variable {X Y : Scheme.{0}}
variable {A A₀ : Type} [CommRing A] [CommRing A₀] {g₀ : A →+* A₀} {a : A}
  {f : X ⟶ Spec (CommRingCat.of A)} {f₀ : Y ⟶ Spec (CommRingCat.of A₀)} {j : Y ⟶ X}
namespace GlobalTheory.SectionKernel
theorem _root_.solution (hg : Function.Surjective g₀)
    (ha : ∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) [Flat f]
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g₀))) {V : X.Opens} (hV : IsAffineOpen V)
    (u : Γ(X, V)) : cst f V a * u = 0 ↔ (j.app V).hom u = 0 := by
  rw [← cst_eq]
  constructor
  · intro h
    have h := mem_map_of_flat _ (SmallExtLift.cst_flat f hV) (fun x hx => (ha x).1 hx) u h
    refine (show _ ≤ RingHom.ker (j.app V).hom from Ideal.map_le_iff_le_comap.2 fun r hr => ?_) h
    rw [Ideal.mem_comap, RingHom.mem_ker, SmallExtLift.app_cst P.w, RingHom.mem_ker.1 hr, map_zero]
  · intro h
    exact SmallExtLift.mul_eq_zero_of_mem _ (fun x hx => (mul_comm _ _).trans ((ha x).2 hx))
      (SmallExtLift.mem_of_app_eq_zero hg P hV u h)
end GlobalTheory.SectionKernel
