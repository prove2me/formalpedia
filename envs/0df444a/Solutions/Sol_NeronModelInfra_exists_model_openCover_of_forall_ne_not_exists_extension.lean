-- Prove2me | solution 1 for NeronModelInfra.exists_model_openCover_of_forall_ne_not_exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/899ad0af-f063-5f35-8722-264b1f061920

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_NeronModelInfra_exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension
import Theorems.Thm_NeronModelInfra_exists_model_openCover_of_forall_isClosedImmersion_pullback_lift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_model_openCover_of_forall_ne_not_exists_extension
p2m_attr_erase "instance" "NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {ι : Type u} [Finite ι] [Nonempty ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
    (hf : ∀ i, Smooth (f i) ∧ IsSeparated (f i) ∧ LocallyOfFiniteType (f i) ∧ QuasiCompact (f i))
    (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i, IsIso (e i).1)
    (ξ : ∀ i, ↥(Y i)) (hξ : ∀ i, (f i).base (ξ i) = IsLocalRing.closedPoint R)
    (hξgen : ∀ i (y : ↥(Y i)), (f i).base y = IsLocalRing.closedPoint R → ξ i ⤳ y)
    (hne : ∀ i j, i ≠ j → ∀ (U : (Y i).Opens), ξ i ∈ U → ∀ u : SchemeHomOver (U.ι ≫ f i) (f j),
      (genericFibreRestrict R K (f j) (U.ι ≫ f i) u).1 ≫ (e j).1 ≠
        (genericFibreRestrict R K (f i) (U.ι ≫ f i) ⟨U.ι, rfl⟩).1 ≫ (e i).1) :
    ∃ (X : Scheme.{u}) (g : X ⟶ Spec (CommRingCat.of R))
      (eX : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK)
      (V : ∀ i, (Y i).Opens) (j : ∀ i, SchemeHomOver ((V i).ι ≫ f i) g),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧ IsIso eX.1 ∧
      (∀ i, ξ i ∈ V i) ∧
      (∀ i (y : ↥(Y i)), (f i).base y ≠ IsLocalRing.closedPoint R → y ∈ V i) ∧
      (∀ i, IsOpenImmersion (j i).1) ∧
      (∀ i, (genericFibreRestrict R K g ((V i).ι ≫ f i) (j i)).1 ≫ eX.1 =
        (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1 ≫ (e i).1) ∧
      (∀ x : ↥X, ∃ i, x ∈ Set.range (j i).1.base) := by
  obtain ⟨V, hξV, hgen, hiso, hdiag⟩ :=
    NeronModelInfra.exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension
      K gK Y f hf e he ξ hξ hξgen hne

  have hf' : ∀ i, Smooth ((V i).ι ≫ f i) ∧ IsSeparated ((V i).ι ≫ f i) ∧
      LocallyOfFiniteType ((V i).ι ≫ f i) ∧ QuasiCompact ((V i).ι ≫ f i) := by
    intro i
    obtain ⟨h1, h2, h3, h4⟩ := hf i
    haveI : IsLocallyNoetherian (Y i) := LocallyOfFiniteType.isLocallyNoetherian (f i)
    haveI : CompactSpace ↥(Y i) := QuasiCompact.compactSpace_of_compactSpace (f i)
    haveI : IsNoetherian (Y i) := {}
    haveI : TopologicalSpace.NoetherianSpace ↥(V i : Scheme.{u}) :=
      (inferInstance : TopologicalSpace.NoetherianSpace (V i : Set ↥(Y i)))
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have he' : ∀ i, IsIso (schemeHomOverComp
      (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩) (e i)).1 := by
    intro i
    haveI := hiso i
    haveI := he i
    show IsIso ((genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1 ≫ (e i).1)
    infer_instance
  obtain ⟨X, g, eX, j, hsm, hsep, hlft, hqc, hiX, hopen, hcomp, hcov⟩ :=
    NeronModelInfra.exists_model_openCover_of_forall_isClosedImmersion_pullback_lift
      K gK (fun i => (V i : Scheme.{u})) (fun i => (V i).ι ≫ f i) hf'
      (fun i => schemeHomOverComp (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩) (e i))
      he' hdiag
  exact ⟨X, g, eX, V, j, hsm, hsep, hlft, hqc, hiX, hξV, hgen, hopen, hcomp, hcov⟩

end S_NeronModelInfra_exists_model_openCover_of_forall_ne_not_exists_extension
end P2MW
export P2MW.S_NeronModelInfra_exists_model_openCover_of_forall_ne_not_exists_extension (solution)
