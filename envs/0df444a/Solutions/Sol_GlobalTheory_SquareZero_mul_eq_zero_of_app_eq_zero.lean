-- Prove2me | solution 1 for GlobalTheory.SquareZero.mul_eq_zero_of_app_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:19:01.604026+00:00
-- url     : https://prove2.me/submissions/2ccdeb65-b84a-48f4-90f2-d9ad46d075fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSectionEqMulOfVanishingModElement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulEqZeroOfAppEqZero
import Theorems.Thm_GlobalTheory_SectionKernel_app_rs
import Theorems.Thm_GlobalTheory_SmallExtLift_mem_of_app_eq_zero


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
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace
open GlobalTheory GlobalTheory.SquareZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SquareZero
namespace _root_.GlobalTheory.SquareZero
theorem _root_.solution : ∀ (A A' : Type) [CommRing A] [CommRing A']
    (g : A →+* A'), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ → ∀ (X X' : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (β : X' ⟶ X),
    IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (W : X.Opens) (x y : Γ(X, W)),
    (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0 := by
  intro A A' _ _ g hg hsq X X' f f' β hpb W x y hx hy
  apply TopCat.Presheaf.section_ext X.sheaf W (x * y) 0
  intro p hp
  obtain ⟨V, hVaff, hpV, hVW⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hp
  have hres : ∀ z : Γ(X, W), (β.app W).hom z = 0 →
      _root_.GlobalTheory.AbLaw.rs X hVW z ∈
        Ideal.map (_root_.GlobalTheory.SmallExtLift.cst f V) (RingHom.ker g) := fun z hz =>
    _root_.GlobalTheory.SmallExtLift.mem_of_app_eq_zero hg hpb hVaff _
      (by rw [_root_.GlobalTheory.SectionKernel.app_rs, hz, map_zero])
  have hzero : _root_.GlobalTheory.AbLaw.rs X hVW (x * y) = 0 := by
    rw [map_mul]
    have hmem := Ideal.mul_mem_mul (hres x hx) (hres y hy)
    rw [← Ideal.map_mul, ← pow_two, hsq, Ideal.map_bot, Ideal.mem_bot] at hmem
    exact hmem
  have h1 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVW) p hpV (x * y)
  have h2 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVW) p hpV 0
  change X.presheaf.germ W p hp (x * y) = X.presheaf.germ W p hp 0
  rw [← h1, ← h2, map_zero]
  exact congrArg _ hzero
end _root_.GlobalTheory.SquareZero
end GlobalTheory.SquareZero
