-- Prove2me | solution 1 for NeronModelInfra.exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f349773f-6d69-5d1f-898c-91e3fcdaef87

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_NeronModelInfra_SmoothnessDefect
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

namespace ChartDict29

theorem ΓSpecIso_inv_hom_apply (R : Type u) [CommRing R] (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom r = r
  rw [Iso.inv_hom_id]; rfl

theorem ΓSpecIso_nat_apply {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) (r : Γ(Spec (CommRingCat.of R), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((Spec.map (CommRingCat.ofHom g)).appTop.hom r) =
      g ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
  have := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)
  have h := congrArg (fun k : Γ(Spec (CommRingCat.of R), ⊤) ⟶ CommRingCat.of S => k.hom r) this
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using h

theorem topIso_inv_map {X : Scheme.{u}} (U : X.Opens) (s : Γ(X, ⊤)) :
    U.topIso.inv.hom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) = U.ι.appTop.hom s := by
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, ← CommRingCat.comp_apply]
  erw [← X.presheaf.map_comp]
  rfl

end ChartDict29

open ChartDict29

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra R R']
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f)
    (U : X.Opens) (hU : IsAffineOpen U) (hxU : x.1 (IsLocalRing.closedPoint R') ∈ U) :
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    ∃ c : Γ(X, U) →ₐ[R] R',
      (IsLocalRing.maximalIdeal R').comap c = (hU.primeIdealOf ⟨x.1 (IsLocalRing.closedPoint R'), hxU⟩).asIdeal := by
  letI : Algebra R Γ(X, U) :=
    ((X.presheaf.map (homOfLE le_top).op).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra

  have hpre : x.1 ⁻¹ᵁ U = ⊤ := (IsLocalRing.closedPoint_mem_iff _).mp hxU
  have hrange : Set.range x.1.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    have : p ∈ x.1 ⁻¹ᵁ U := by rw [hpre]; trivial
    exact this
  let φU : Spec (CommRingCat.of R') ⟶ (U : Scheme.{u}) := IsOpenImmersion.lift U.ι x.1 hrange
  have hφU : φU ≫ U.ι = x.1 := IsOpenImmersion.lift_fac U.ι x.1 hrange

  let c₀ : Γ(X, U) →+* R' :=
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom.comp (φU.appTop.hom.comp U.topIso.inv.hom)
  have hc₀ : ∀ r : R, c₀ (algebraMap R Γ(X, U) r) = algebraMap R R' r := by
    intro r
    show (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (φU.appTop.hom (U.topIso.inv.hom
      ((X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))))) = _
    rw [topIso_inv_map]
    have h1 : ∀ t, φU.appTop.hom (U.ι.appTop.hom (f.appTop.hom t)) = ((φU ≫ U.ι) ≫ f).appTop.hom t := fun t => by
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    rw [h1, hφU, x.2, ΓSpecIso_nat_apply, ΓSpecIso_inv_hom_apply]
  let c : Γ(X, U) →ₐ[R] R' := AlgHom.mk c₀ hc₀
  refine ⟨c, ?_⟩

  have hSpec : Spec.map (CommRingCat.ofHom c₀) = φU ≫ U.toSpecΓ := by
    show Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom.comp (φU.appTop.hom.comp U.topIso.inv.hom))) = _
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom,
      Spec.map_comp, Spec.map_comp, SpecMap_ΓSpecIso_hom, Scheme.Opens.toSpecΓ, ← Category.assoc, ← Category.assoc,
      ← Scheme.toSpecΓ_naturality]
  have hpt : φU.base (IsLocalRing.closedPoint R') = ⟨x.1.base (IsLocalRing.closedPoint R'), hxU⟩ := by
    apply Subtype.ext
    change (φU ≫ U.ι).base (IsLocalRing.closedPoint R') = _
    rw [hφU]
  show Ideal.comap c₀ (IsLocalRing.maximalIdeal R') = (hU.isoSpec.hom.base ⟨x.1.base (IsLocalRing.closedPoint R'), hxU⟩).asIdeal
  rw [IsAffineOpen.isoSpec_hom, ← hpt]
  change _ = ((φU ≫ U.toSpecΓ).base (IsLocalRing.closedPoint R')).asIdeal
  rw [← hSpec]
  rfl

end S_NeronModelInfra_exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem
end P2MW
export P2MW.S_NeronModelInfra_exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem (solution)
