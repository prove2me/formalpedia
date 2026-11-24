-- Prove2me | solution 1 for GlobalTheory.SectionKernel.surjective_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:37:33.491541+00:00
-- url     : https://prove2.me/submissions/0e0e2900-1557-42c7-a2ac-74b30a3681a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSectionEqMulOfVanishingModElement

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
    (hn : IsNilpotent (RingHom.ker g₀))
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g₀))) : Function.Surjective j := by
  have h2 : Surjective (Spec.map (CommRingCat.ofHom g₀)) := ⟨fun x => by
    obtain ⟨n, hn⟩ := hn
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker g₀ : Set A) := fun a ha =>
      x.isPrime.mem_of_pow_mem n (by
        have := Ideal.pow_mem_pow ha n
        rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
        rw [this]
        exact zero_mem _)
    rw [← range_comap_of_surjective _ g₀ hg] at hx
    exact hx⟩
  have : Surjective j := MorphismProperty.of_isPullback P.flip h2
  exact j.surjective
end GlobalTheory.SectionKernel
