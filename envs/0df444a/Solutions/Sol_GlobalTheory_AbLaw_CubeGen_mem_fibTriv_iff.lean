-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeGen.mem_fibTriv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:22:56.025934+00:00
-- url     : https://prove2.me/submissions/4ca2643b-ce42-46d9-adc0-d08f0a289ad1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_triv_pull_comp_iff
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_mem_range_spec

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
theorem _root_.solution {p : Y ⟶ T} {R : Type} [CommRing R] {j : Spec (CommRingCat.of R) ⟶ T} [IsOpenImmersion j]
    {q : W ⟶ Y} {f : W ⟶ Spec (CommRingCat.of R)} (H : IsPullback q f p j) (x : PrimeSpectrum R) :
    j x ∈ fibTriv L φ ε p ↔ ∃ (F : Type) (_ : Field F) (g : R →+* F) (Z : Scheme.{0}) (π : Z ⟶ W)
      (f' : Z ⟶ Spec (CommRingCat.of F)), RingHom.ker g = x.asIdeal ∧
      IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧
      Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull π) := by
  constructor
  · rintro ⟨F, _, g, Z, π, f', ⟨y, hy⟩, hp, ht⟩
    have hsub : Subsingleton (Spec (CommRingCat.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    obtain ⟨g', hg'⟩ : ∃ g' : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R), g' ≫ j = g :=
      ⟨IsOpenImmersion.lift j g (by
        rintro _ ⟨y', rfl⟩
        rw [Subsingleton.elim y' y, hy]
        exact ⟨x, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨g₀, rfl⟩ := Spec.map_surjective g'
    subst hg'
    have w : π ≫ p = (f' ≫ Spec.map g₀) ≫ j := by rw [hp.w, Category.assoc]
    have e : H.lift π _ w ≫ q = π := H.lift_fst _ _ _
    refine ⟨F, inferInstance, g₀.hom, Z, H.lift π _ w, f', ?_, ?_, ?_⟩
    · exact (mem_range_spec g₀.hom x).1 ⟨y, j.isOpenEmbedding.injective hy⟩
    · exact IsPullback.of_right (by rw [e]; exact hp) (H.lift_snd _ _ _) H
    · rw [triv_pull_comp_iff, e]; exact ht
  · rintro ⟨F, _, g, Z, π, f', hk, hp, ht⟩
    obtain ⟨y, hy⟩ := (mem_range_spec g x).2 hk
    exact ⟨F, inferInstance, Spec.map (CommRingCat.ofHom g) ≫ j, Z, π ≫ q, f', ⟨y, congrArg j hy⟩,
      hp.paste_horiz H, (triv_pull_comp_iff L φ ε q π).1 ht⟩
end GlobalTheory.AbLaw.CubeGen
