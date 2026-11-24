-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeGen.mem_range_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:52:59.531696+00:00
-- url     : https://prove2.me/submissions/a7efcffc-eb8a-4b7d-88f9-7c69d044bde6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
variable {X Y T W : Scheme.{0}} {K : Type} [Fintype K] (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
namespace GlobalTheory.AbLaw.CubeGen
theorem _root_.solution {R F : Type} [CommRing R] [Field F] (g : R →+* F) (x : PrimeSpectrum R) :
    x ∈ Set.range (Spec.map (CommRingCat.ofHom g)) ↔ RingHom.ker g = x.asIdeal := by
  have key : ∀ y : PrimeSpectrum F, (PrimeSpectrum.comap g y).asIdeal = RingHom.ker g := fun y => by
    rw [PrimeSpectrum.comap_asIdeal, Ideal.eq_bot_of_prime y.asIdeal]; rfl
  constructor
  · rintro ⟨y, rfl⟩
    exact (key y).symm
  · intro h
    exact ⟨(default : PrimeSpectrum F), PrimeSpectrum.ext ((key _).trans h)⟩
end GlobalTheory.AbLaw.CubeGen
