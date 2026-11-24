-- Prove2me | solution 1 for GlobalTheory.NearFibreIso.near_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:38.623319+00:00
-- url     : https://prove2.me/submissions/5595cb18-9afd-49f8-8761-2c8fd03855f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoFibreOfPullback
import Theorems.Thm_GlobalTheory_DenseFibreIso_exists_away_bijective
import Theorems.Thm_GlobalTheory_DenseFibreIso_local_of_ring


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
open GlobalTheory GlobalTheory.NearFibreIso
open GlobalTheory.DenseFibreIso
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)
variable (K : Type) [Field K] [Algebra R K]
set_option backward.isDefEq.respectTransparency.types false
namespace GlobalTheory.NearFibreIso
theorem _root_.solution [hcl : IsClosedImmersion f] [IsLocallyNoetherian X] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  refine DenseFibreIso.local_of_ring s f (MorphismProperty.isomorphisms _) K ?_ x hx
  intro A B _ _ _ _ _ _ j j' hj H hjs hbij m
  have : IsOpenImmersion j' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H hj
  have hci : IsClosedImmersion (spMap (algebraMap A B)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) H.flip hcl
  have hs : Function.Surjective (algebraMap A B) := by
    have h1 := (spMap (algebraMap A B)).app_surjective ⊤ (isAffineOpen_top _)
    have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
    intro b
    obtain ⟨c, hc⟩ := h1 ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom c, ?_⟩
    have h3 := congr_arg (fun k => (ConcreteCategory.hom k) c) h2
    simp only [CategoryTheory.comp_apply, CommRingCat.hom_ofHom] at h3
    rw [← h3]
    change (Scheme.ΓSpecIso (CommRingCat.of B)).hom ((spMap (algebraMap A B)).app ⊤ c) = b
    rw [hc]
    simp
  have : IsLocallyNoetherian (Sp A) := isLocallyNoetherian_of_isOpenImmersion j
  have : IsNoetherian (Sp A) := {}
  have : IsNoetherianRing A := isNoetherian_Spec.mp this
  have hflat : Flat (spMap (algebraMap R B)) := by
    have e : spMap (algebraMap R B) = spMap (algebraMap A B) ≫ spMap (algebraMap R A) := by
      change Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    rw [e, ← hjs, reassoc_of% H.w]
    infer_instance
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hflat)
  obtain ⟨a, ha, hb⟩ := DenseFibreIso.exists_away_bijective R K hs hbij.1 m
  exact ⟨a, ha, isIso_SpecMap_iff.mpr hb⟩
end GlobalTheory.NearFibreIso
