-- Prove2me | solution 1 for GlobalTheory.SecLift.surj_of_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:24.787803+00:00
-- url     : https://prove2.me/submissions/fd716197-75a6-45d0-8ac5-7cdd1e9db171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]
namespace GlobalTheory.SecLift
theorem _root_.solution {A₀ : Type} [CommRing A₀] {g : A →+* A₀} (hg : Function.Surjective g)
    (hn : ∀ x ∈ RingHom.ker g, IsNilpotent x) {f : X ⟶ Spec (CommRingCat.of A)} {j : Y ⟶ X}
    {f₀ : Y ⟶ Spec (CommRingCat.of A₀)} (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g))) :
    Function.Surjective j := by
  have h : Surjective (Spec.map (CommRingCat.ofHom g)) := ⟨fun p => by
    have : p ∈ Set.range (PrimeSpectrum.comap g) := by
      rw [range_comap_of_surjective _ g hg]
      intro x hx
      obtain ⟨n, hx⟩ := hn x hx
      exact p.isPrime.mem_of_pow_mem n (by rw [hx]; exact Ideal.zero_mem _)
    exact this⟩
  exact (MorphismProperty.of_isPullback (P := @Surjective) P.flip h).1
end GlobalTheory.SecLift
