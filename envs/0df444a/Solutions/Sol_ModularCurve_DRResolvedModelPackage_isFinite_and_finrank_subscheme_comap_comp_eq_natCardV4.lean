-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackage.isFinite_and_finrank_subscheme_comap_comp_eq_natCardV4
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a11e6389-3c78-5f3b-850e-411afc1a72e6

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackage_isFinite_and_finrank_subscheme_comap_comp_eq_natCardV4

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_isFinite_and_finrank_subscheme_comap_comp_eq_natCardV4.AlgebraicGeometry ModularCurve"

set_option autoImplicit false
set_option maxHeartbeats 800000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_isFinite_and_finrank_subscheme_comap_comp_eq_natCardV4.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.IdealSheafData.support_comap Scheme.Hom Scheme.Hom.germ_stalkMap_apply IsFinite Spec Scheme.IdealSheafData.range_subschemeι Scheme Scheme.Hom.app_eq_appLE Scheme.IdealSheafData.ker_subschemeι_app Scheme.IdealSheafData Scheme.IdealSheafData.ideal_comap_of_le Scheme.IdealSheafData.isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal"
namespace PL2S17
p2m_open "AlgebraicGeometry"

theorem map_maximalIdeal_of_surjective {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ] (hφ : Function.Surjective φ) :
    Ideal.map φ (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B := by
  refine le_antisymm ?_ ?_
  · exact ((IsLocalRing.local_hom_TFAE φ).out 0 2).mp ‹IsLocalHom φ›
  · intro b hb
    obtain ⟨a, rfl⟩ := hφ b
    refine Ideal.mem_map_of_mem _ ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
    exact fun ha => hb (ha.map φ)

theorem map_germ_comap_eq_maximalIdeal {X : Scheme.{u}} (I J : X.IdealSheafData) (z : J.subscheme)
    (U : X.affineOpens) (hU : J.subschemeι z ∈ (U : X.Opens))
    (h : Ideal.map (X.presheaf.germ (U : X.Opens) (J.subschemeι z) hU).hom (I.ideal U ⊔ J.ideal U) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (J.subschemeι z))) :
    Ideal.map ((J.subscheme).presheaf.germ (J.subschemeι ⁻¹ᵁ (U : X.Opens)) z hU).hom
        ((I.comap J.subschemeι).ideal ⟨J.subschemeι ⁻¹ᵁ (U : X.Opens), U.2.preimage J.subschemeι⟩) =
      IsLocalRing.maximalIdeal ((J.subscheme).presheaf.stalk z) := by
  set E : (J.subscheme).affineOpens := ⟨J.subschemeι ⁻¹ᵁ (U : X.Opens), U.2.preimage J.subschemeι⟩ with hEdef

  have hsurj : Function.Surjective (J.subschemeι.stalkMap z).hom := J.subschemeι.stalkMap_surjective z
  rw [← map_maximalIdeal_of_surjective (J.subschemeι.stalkMap z).hom hsurj, ← h, Ideal.map_map, Ideal.map_sup]

  have hcomp : (J.subschemeι.stalkMap z).hom.comp (X.presheaf.germ (U : X.Opens) (J.subschemeι z) hU).hom =
      ((J.subscheme).presheaf.germ (J.subschemeι ⁻¹ᵁ (U : X.Opens)) z hU).hom.comp
        (J.subschemeι.app (U : X.Opens)).hom := by
    ext a
    exact Scheme.Hom.germ_stalkMap_apply J.subschemeι (U : X.Opens) z hU a
  rw [hcomp, ← Ideal.map_map, ← Ideal.map_map, Scheme.IdealSheafData.ideal_comap_of_le I J.subschemeι U E le_rfl,
    ← Scheme.Hom.app_eq_appLE]

  have hJ : Ideal.map (J.subschemeι.app (U : X.Opens)).hom (J.ideal U) = ⊥ := by
    rw [← le_bot_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_bot, ← RingHom.mem_ker, Scheme.IdealSheafData.ker_subschemeι_app]
    exact ha
  rw [hJ, Ideal.map_bot, sup_bot_eq]

theorem mem_support_comap_iff {X : Scheme.{u}} (I J : X.IdealSheafData) (z : J.subscheme) :
    z ∈ (I.comap J.subschemeι).support ↔ J.subschemeι z ∈ I.support := by
  rw [Scheme.IdealSheafData.support_comap]
  rfl

end AlgebraicGeometry.PL2S17

open _root_.AlgebraicGeometry _root_.P2MW.S_ModularCurve_DRResolvedModelPackage_isFinite_and_finrank_subscheme_comap_comp_eq_natCardV4.AlgebraicGeometry ModularCurve in

theorem solution
    (p : ℕ) [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ} (R : DRResolvedModelPackage p 𝔛 O κ toκ)
    (v w : X0MqComponents R.width) (hvw : v ≠ w)
    {k : Type} [Field k] (y : (R.comp w).subscheme ⟶ Spec (CommRingCat.of k))
    (hrat : ∀ (n : R.node) (d : Fin (R.width n)),
      (v = DRResolvedModelPackage.chainPos R.width n d ∧ w = DRResolvedModelPackage.chainPos R.width n (d + 1)) ∨
          (w = DRResolvedModelPackage.chainPos R.width n d ∧ v = DRResolvedModelPackage.chainPos R.width n (d + 1)) →
      ∃ s : Spec (CommRingCat.of k) ⟶ (R.comp w).subscheme,
        s ≫ y = 𝟙 _ ∧ R.edgePt n d ∈ Set.range (s ≫ (R.comp w).subschemeι).base) :
    IsFinite (((R.comp v).comap (R.comp w).subschemeι).subschemeι ≫ y) ∧
      ∀ t : Spec (CommRingCat.of k), (((R.comp v).comap (R.comp w).subschemeι).subschemeι ≫ y).finrank t =
        Nat.card {e : Σ n : R.node, Fin (R.width n) //
          (v = DRResolvedModelPackage.chainPos R.width e.1 e.2 ∧ w = DRResolvedModelPackage.chainPos R.width e.1 (e.2 + 1)) ∨
            (w = DRResolvedModelPackage.chainPos R.width e.1 e.2 ∧ v = DRResolvedModelPackage.chainPos R.width e.1 (e.2 + 1))} := by
  classical

  let P : (Σ n : R.node, Fin (R.width n)) → Prop := fun e =>
    (v = DRResolvedModelPackage.chainPos R.width e.1 e.2 ∧ w = DRResolvedModelPackage.chainPos R.width e.1 (e.2 + 1)) ∨
      (w = DRResolvedModelPackage.chainPos R.width e.1 e.2 ∧ v = DRResolvedModelPackage.chainPos R.width e.1 (e.2 + 1))
  let eqv := Fintype.equivFin {e // P e}
  set N := Fintype.card {e // P e} with hNdef

  have hsec : ∀ e : {e // P e}, ∃ (s : Spec (CommRingCat.of k) ⟶ (R.comp w).subscheme) (z : (R.comp w).subscheme),
      s ≫ y = 𝟙 _ ∧ z ∈ Set.range s.base ∧ (R.comp w).subschemeι z = R.edgePt e.1.1 e.1.2 := by
    intro e
    obtain ⟨s, hs, pt, hpt⟩ := hrat e.1.1 e.1.2 e.2
    exact ⟨s, s pt, hs, ⟨pt, rfl⟩, hpt⟩
  choose s z hs hzs hz using hsec
  let x : Fin N → (R.comp w).subscheme := fun i => z (eqv.symm i)
  have hιx : ∀ i, (R.comp w).subschemeι (x i) = R.edgePt (eqv.symm i).1.1 (eqv.symm i).1.2 := fun i => hz _

  have hx : Function.Injective x := by
    intro i j hij
    have h1 : (R.comp w).subschemeι (x i) = (R.comp w).subschemeι (x j) := by rw [hij]
    rw [hιx, hιx] at h1
    have h2 : (eqv.symm i).1 = (eqv.symm j).1 := R.edgePt_injective h1
    exact eqv.symm.injective (Subtype.ext h2)

  have hsupp : ((((R.comp v).comap (R.comp w).subschemeι).support : Set (R.comp w).subscheme)) = Set.range x := by
    ext z'
    rw [SetLike.mem_coe, AlgebraicGeometry.PL2S17.mem_support_comap_iff]
    constructor
    · intro hv
      have hw : (R.comp w).subschemeι z' ∈ ((R.comp w).support : Set R.Y) := by
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z', rfl⟩
      obtain ⟨n, d, hnd, hor⟩ := R.edgePt_exhaust v w hvw _ ⟨hv, hw⟩
      refine ⟨eqv ⟨⟨n, d⟩, hor⟩, ?_⟩
      apply (R.comp w).subschemeι.isClosedEmbedding.injective
      change (R.comp w).subschemeι (z (eqv.symm (eqv ⟨⟨n, d⟩, hor⟩))) = (R.comp w).subschemeι z'
      rw [Equiv.symm_apply_apply, hz, hnd]
    · rintro ⟨i, rfl⟩
      show (R.comp w).subschemeι (x i) ∈ (((R.comp v).support) : Set R.Y)
      rw [hιx]
      rcases (eqv.symm i).2 with ⟨hv', -⟩ | ⟨-, hv'⟩
      · have hm := (R.edgePt_mem (eqv.symm i).1.1 (eqv.symm i).1.2).1
        rw [← hv'] at hm
        exact hm
      · have hm := (R.edgePt_mem (eqv.symm i).1.1 (eqv.symm i).1.2).2
        rw [← hv'] at hm
        exact hm

  have hmax : ∀ i, ∃ (U : ((R.comp w).subscheme).affineOpens) (hU : x i ∈ (U : ((R.comp w).subscheme).Opens)),
      Ideal.map (((R.comp w).subscheme).presheaf.germ (U : ((R.comp w).subscheme).Opens) (x i) hU).hom
          (((R.comp v).comap (R.comp w).subschemeι).ideal U) =
        IsLocalRing.maximalIdeal (((R.comp w).subscheme).presheaf.stalk (x i)) := by
    intro i
    obtain ⟨U, hU, htr⟩ := R.edgePt_transversal (eqv.symm i).1.1 (eqv.symm i).1.2
    have hU' : (R.comp w).subschemeι (x i) ∈ (U : R.Y.Opens) := by rw [hιx]; exact hU
    refine ⟨⟨(R.comp w).subschemeι ⁻¹ᵁ (U : R.Y.Opens), U.2.preimage _⟩, hU', ?_⟩
    apply AlgebraicGeometry.PL2S17.map_germ_comap_eq_maximalIdeal (R.comp v) (R.comp w) (x i) U hU'
    have key : ∀ (pt : R.Y) (hpt : pt ∈ (U : R.Y.Opens)), pt = R.edgePt (eqv.symm i).1.1 (eqv.symm i).1.2 →
        Ideal.map (R.Y.presheaf.germ (U : R.Y.Opens) pt hpt).hom
            ((R.comp (DRResolvedModelPackage.chainPos R.width (eqv.symm i).1.1 (eqv.symm i).1.2)).ideal U ⊔
              (R.comp (DRResolvedModelPackage.chainPos R.width (eqv.symm i).1.1 ((eqv.symm i).1.2 + 1))).ideal U) =
          IsLocalRing.maximalIdeal (R.Y.presheaf.stalk pt) := by
      rintro pt hpt rfl
      exact htr
    have hk := key _ hU' (hιx i)
    rcases (eqv.symm i).2 with ⟨hv', hw'⟩ | ⟨hw', hv'⟩
    · rw [← hv', ← hw'] at hk
      exact hk
    · rw [← hw', ← hv', sup_comm] at hk
      exact hk

  have hrat' : ∀ i, ∃ s' : Spec (CommRingCat.of k) ⟶ (R.comp w).subscheme, s' ≫ y = 𝟙 _ ∧ x i ∈ Set.range s'.base :=
    fun i => ⟨s (eqv.symm i), hs _, hzs _⟩
  obtain ⟨hfin, hdeg⟩ :=
    Scheme.IdealSheafData.isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal
      y ((R.comp v).comap (R.comp w).subschemeι) x hx hsupp hmax hrat'
  refine ⟨hfin, fun t => ?_⟩
  rw [hdeg t, hNdef]
  exact Nat.card_eq_fintype_card.symm

end S_ModularCurve_DRResolvedModelPackage_isFinite_and_finrank_subscheme_comap_comp_eq_natCardV4
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackage_isFinite_and_finrank_subscheme_comap_comp_eq_natCardV4 (solution)
