-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_and_forall_exists_comp_eq_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/715aabf4-10a0-5767-84dc-ed448a3737ad

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_and_forall_exists_comp_eq_of_isClosedImmersion

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open NeronModelInfra (SchemeHomOver schemeHomOverId)

namespace SUBGROUPCLOSED

universe u

variable {R : Type} [CommRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
    {𝒜 : Scheme.{0}} {a : 𝒜 ⟶ Spec (CommRingCat.of R)} (ι : SchemeHomOver a f) [Mono ι.1]

theorem ext_of_comp_eq {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of R)} {z z' : SchemeHomOver s a}
    (h : NeronModelInfra.schemeHomOverComp z ι = NeronModelInfra.schemeHomOverComp z' ι) : z = z' := by
  apply Subtype.ext
  have h1 := congrArg Subtype.val h
  rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe] at h1
  exact (cancel_mono ι.1).mp h1

theorem comp_testComp {T T' : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of R)} {s' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ s = s') (z : SchemeHomOver s a) :
    NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp ψ hψ z) ι =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp z ι) := by
  apply Subtype.ext
  simp only [NeronModelInfra.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]

section Law

variable (L : GoodReductionJacobian.RelativeGroupLaw R f)
  (hgrp : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)),
      (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι = L.one s) ∧
      (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
        L.mul s (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
      (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
        L.inv s (NeronModelInfra.schemeHomOverComp x ι)))

noncomputable def mulc {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s a) : SchemeHomOver s a :=
  Classical.choose ((hgrp s).2.1 x y)

noncomputable def onec {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver s a :=
  Classical.choose (hgrp s).1

noncomputable def invc {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s a) : SchemeHomOver s a :=
  Classical.choose ((hgrp s).2.2 x)

theorem mulc_spec {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s a) :
    NeronModelInfra.schemeHomOverComp (mulc ι L hgrp s x y) ι =
      L.mul s (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι) :=
  Classical.choose_spec ((hgrp s).2.1 x y)

theorem onec_spec {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (onec ι L hgrp s) ι = L.one s :=
  Classical.choose_spec (hgrp s).1

theorem invc_spec {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s a) :
    NeronModelInfra.schemeHomOverComp (invc ι L hgrp s x) ι = L.inv s (NeronModelInfra.schemeHomOverComp x ι) :=
  Classical.choose_spec ((hgrp s).2.2 x)

noncomputable def law : GoodReductionJacobian.RelativeGroupLaw R a where
  mul s x y := mulc ι L hgrp s x y
  one s := onec ι L hgrp s
  inv s x := invc ι L hgrp s x
  mul_assoc s x y z := by
    apply ext_of_comp_eq ι
    simp only [mulc_spec, L.mul_assoc]
  one_mul s x := by
    apply ext_of_comp_eq ι
    rw [mulc_spec, onec_spec, L.one_mul]
  mul_one s x := by
    apply ext_of_comp_eq ι
    rw [mulc_spec, onec_spec, L.mul_one]
  inv_mul_cancel s x := by
    apply ext_of_comp_eq ι
    rw [mulc_spec, invc_spec, onec_spec, L.inv_mul_cancel]
  mul_natural s s' ψ hψ x y := by
    apply ext_of_comp_eq ι
    rw [comp_testComp ι, mulc_spec, mulc_spec, L.mul_natural, comp_testComp ι, comp_testComp ι]

theorem law_mul_comp {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s a) :
    NeronModelInfra.schemeHomOverComp ((law ι L hgrp).mul s x y) ι =
      L.mul s (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι) :=
  mulc_spec ι L hgrp s x y

theorem law_isCommutative (hc : L.IsCommutative) : (law ι L hgrp).IsCommutative := by
  intro T s x y
  apply ext_of_comp_eq ι
  rw [law_mul_comp, law_mul_comp, hc]

theorem exists_restrict (E : SchemeHomOver f f)
    (hE : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) E =
        L.mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E))
    (hstab : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s a),
      ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) E) :
    ∃ E' : SchemeHomOver a a,
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s a),
        NeronModelInfra.schemeHomOverComp ((law ι L hgrp).mul s x y) E' =
          (law ι L hgrp).mul s (NeronModelInfra.schemeHomOverComp x E') (NeronModelInfra.schemeHomOverComp y E')) ∧
      E'.1 ≫ ι.1 = ι.1 ≫ E.1 := by
  obtain ⟨E', hE'⟩ := hstab a (schemeHomOverId a)
  have hsq : NeronModelInfra.schemeHomOverComp E' ι = NeronModelInfra.schemeHomOverComp ι E := by
    rw [hE', NeronModelInfra.schemeHomOverComp_id_left]
  have hsq1 : E'.1 ≫ ι.1 = ι.1 ≫ E.1 := by
    have := congrArg Subtype.val hsq
    simpa only [NeronModelInfra.schemeHomOverComp_coe] using this
  refine ⟨E', fun s x y => ?_, hsq1⟩
  apply ext_of_comp_eq ι
  rw [NeronModelInfra.schemeHomOverComp_assoc, hsq, ← NeronModelInfra.schemeHomOverComp_assoc, law_mul_comp, hE,
    law_mul_comp, NeronModelInfra.schemeHomOverComp_assoc x E' ι, NeronModelInfra.schemeHomOverComp_assoc y E' ι, hsq,
    ← NeronModelInfra.schemeHomOverComp_assoc, ← NeronModelInfra.schemeHomOverComp_assoc]

end Law

end SUBGROUPCLOSED

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {R : Type} [CommRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : GoodReductionJacobian.RelativeGroupLaw R f) (hc : L.IsCommutative)
    {𝒜 : Scheme.{0}} (a : 𝒜 ⟶ Spec (CommRingCat.of R)) (ι : SchemeHomOver a f) [IsClosedImmersion ι.1]
    (hgrp : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)),
      (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι = L.one s) ∧
      (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
        L.mul s (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
      (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
        L.inv s (NeronModelInfra.schemeHomOverComp x ι))) :
    ∃ L𝒜 : GoodReductionJacobian.RelativeGroupLaw R a, L𝒜.IsCommutative ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s a),
        NeronModelInfra.schemeHomOverComp (L𝒜.mul s x y) ι =
          L.mul s (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
      ∀ E : SchemeHomOver f f,
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) E = L.mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E)) →
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s a),
          ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι = NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) E) →
        ∃ E' : SchemeHomOver a a,
          (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s a),
            NeronModelInfra.schemeHomOverComp (L𝒜.mul s x y) E' = L𝒜.mul s (NeronModelInfra.schemeHomOverComp x E') (NeronModelInfra.schemeHomOverComp y E')) ∧
          E'.1 ≫ ι.1 = ι.1 ≫ E.1 := by
  haveI : Mono ι.1 := inferInstance
  refine ⟨SUBGROUPCLOSED.law ι L hgrp, SUBGROUPCLOSED.law_isCommutative ι L hgrp hc,
    fun s x y => SUBGROUPCLOSED.law_mul_comp ι L hgrp s x y, fun E hE hstab => ?_⟩
  exact SUBGROUPCLOSED.exists_restrict ι L hgrp E hE hstab

end S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_and_forall_exists_comp_eq_of_isClosedImmersion
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_and_forall_exists_comp_eq_of_isClosedImmersion (solution)
