-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_schemeKer_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1a42a23c-2d06-5e1d-b7d1-4c8fdd0ea4dd

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison.GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing"

open scoped Quaternion TensorProduct NumberField

universe u
namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp_coe RelativeGroupLaw BareDeformation RelativeGroupLaw.nsmul_zero RelativeGroupLaw.nsmul_succ RelativeGroupLaw.idPoint RelativeGroupLaw.schemeNsmul_over RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul"
namespace BareDeformation
p2m_export "GoodReductionJacobian.BareDeformation" "hom cart L g f"
p2m_open "GoodReductionJacobian.BareDeformation GoodReductionJacobian"

section Lift

variable {S B : Type} [CommRing S] [CommRing B] [Algebra B S]
  {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
  (D : BareDeformation fₛ Lₛ B)

private theorem _root_.GoodReductionJacobian.BareDeformation.ext_g {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (Q Q' : SchemeHomOver t fₛ)
    (h : Q.1 ≫ D.g = Q'.1 ≫ D.g) : Q = Q' := by
  apply Subtype.ext
  exact D.cart.hom_ext h (by rw [Q.2, Q'.2])

p2m_export "GoodReductionJacobian.BareDeformation" "ext_g"

private def _root_.GoodReductionJacobian.BareDeformation.pushG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T ⟶ Spec (CommRingCat.of B))
    (ht : t' = t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) (Q : SchemeHomOver t fₛ) :
    SchemeHomOver t' D.f :=
  ⟨Q.1 ≫ D.g, by rw [Category.assoc, D.cart.w, ← Category.assoc, Q.2, ht]⟩

p2m_export "GoodReductionJacobian.BareDeformation" "pushG"
@[scoped simp] theorem pushG_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht) (Q : SchemeHomOver t fₛ) :
    (D.pushG t t' ht Q).1 = Q.1 ≫ D.g := rfl

private noncomputable def _root_.GoodReductionJacobian.BareDeformation.liftG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B))
    (ht : t' = t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) (P : SchemeHomOver t' D.f) :
    SchemeHomOver t fₛ :=
  ⟨D.cart.lift P.1 t (by rw [P.2, ht]), D.cart.lift_snd _ _ _⟩

p2m_export "GoodReductionJacobian.BareDeformation" "liftG"
@[scoped simp] private theorem _root_.GoodReductionJacobian.BareDeformation.liftG_g {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht) (P : SchemeHomOver t' D.f) :
    (D.liftG t t' ht P).1 ≫ D.g = P.1 :=
  D.cart.lift_fst _ _ _

p2m_export "GoodReductionJacobian.BareDeformation" "liftG_g"
theorem pushG_liftG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht) (P : SchemeHomOver t' D.f) :
    D.pushG t t' ht (D.liftG t t' ht P) = P :=
  Subtype.ext (D.liftG_g t t' ht P)

theorem liftG_pushG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht) (Q : SchemeHomOver t fₛ) :
    D.liftG t t' ht (D.pushG t t' ht Q) = Q :=
  D.ext_g _ _ (by rw [liftG_g, pushG_coe])

private theorem _root_.GoodReductionJacobian.BareDeformation.mul_pushG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht : t' = t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S)))
    (P Q : SchemeHomOver t fₛ) :
    (D.L.mul t' (D.pushG t t' ht P) (D.pushG t t' ht Q)).1 = (Lₛ.mul t P Q).1 ≫ D.g := by
  subst ht
  rw [D.hom t P Q]
  rfl

p2m_export "GoodReductionJacobian.BareDeformation" "mul_pushG"

private theorem _root_.GoodReductionJacobian.BareDeformation.one_g {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht : t' = t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) :
    (Lₛ.one t).1 ≫ D.g = (D.L.one t').1 := by
  set u := D.pushG t t' ht (Lₛ.one t) with hu
  have h1 : D.L.mul t' u u = u := by
    apply Subtype.ext
    rw [hu, D.mul_pushG t t' ht, Lₛ.one_mul, pushG_coe]
  letI := D.L.pointGroup t'
  have h2 : u = 1 := mul_eq_left.mp h1
  have h3 : u.1 = (D.L.one t').1 := congrArg Subtype.val h2
  rw [← h3, hu, pushG_coe]

p2m_export "GoodReductionJacobian.BareDeformation" "one_g"
end Lift

end GoodReductionJacobian.BareDeformation
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison.GoodReductionJacobian.BareDeformation"
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp_coe RelativeGroupLaw BareDeformation RelativeGroupLaw.nsmul_zero RelativeGroupLaw.nsmul_succ RelativeGroupLaw.idPoint RelativeGroupLaw.schemeNsmul_over RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul"
namespace BareDeformation
p2m_export "GoodReductionJacobian.BareDeformation" "hom cart L g f"
p2m_open "GoodReductionJacobian.BareDeformation GoodReductionJacobian"

variable {S B : Type} [CommRing S] [CommRing B] [Algebra B S]
  {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
  (D : BareDeformation fₛ Lₛ B)

private theorem _root_.GoodReductionJacobian.BareDeformation.nsmul_pushG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht : t' = t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S)))
    (n : ℕ) (P : SchemeHomOver t fₛ) :
    D.pushG t t' ht (Lₛ.nsmul t n P) = D.L.nsmul t' n (D.pushG t t' ht P) := by
  induction n with
  | zero =>
    apply Subtype.ext
    rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero, pushG_coe, D.one_g t t' ht]
  | succ n ih =>
    rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, ← ih]
    apply Subtype.ext
    rw [pushG_coe, D.mul_pushG t t' ht]

p2m_export "GoodReductionJacobian.BareDeformation" "nsmul_pushG"

private theorem _root_.GoodReductionJacobian.BareDeformation.schemeNsmul_comp_g (n : ℕ) :
    Lₛ.schemeNsmul n ≫ D.g = D.g ≫ D.L.schemeNsmul n := by
  have h := D.nsmul_pushG fₛ (fₛ ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) rfl n
    RelativeGroupLaw.idPoint
  have h1 := congrArg Subtype.val h
  simp only [pushG_coe, RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul, Category.id_comp] at h1
  simpa [Category.assoc] using h1

p2m_export "GoodReductionJacobian.BareDeformation" "schemeNsmul_comp_g"

private theorem _root_.GoodReductionJacobian.BareDeformation.oneSection_comp_g :
    (Lₛ.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ D.g =
      Spec.map (CommRingCat.ofHom (algebraMap B S)) ≫ (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1 := by
  rw [D.one_g (𝟙 _) (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) rfl]
  have h := D.L.one_natural (𝟙 (Spec (CommRingCat.of B)))
    (Spec.map (CommRingCat.ofHom (algebraMap B S)))
    (Spec.map (CommRingCat.ofHom (algebraMap B S))) (Category.comp_id _)
  have h1 := congrArg Subtype.val h
  rw [schemeHomOverComp_coe] at h1
  rw [Category.id_comp, ← h1]

p2m_export "GoodReductionJacobian.BareDeformation" "oneSection_comp_g"
end GoodReductionJacobian.BareDeformation
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison.GoodReductionJacobian.BareDeformation"
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison.GoodReductionJacobian.BareDeformation"

theorem solution
    {S B : Type} [CommRing S] [CommRing B] [Algebra B S]
    {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
    (D : BareDeformation fₛ Lₛ B) (n : ℕ) :
    ∃ gK : Lₛ.schemeKer n ⟶ D.L.schemeKer n,
      gK ≫ pullback.fst (D.L.schemeNsmul n) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1 =
        pullback.fst (Lₛ.schemeNsmul n) (Lₛ.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ D.g ∧
      IsPullback gK (Lₛ.schemeKerStr n) (D.L.schemeKerStr n)
        (Spec.map (CommRingCat.ofHom (algebraMap B S))) := by

  have hF1 := D.schemeNsmul_comp_g n
  have hF2 := D.oneSection_comp_g

  have w : (pullback.fst (Lₛ.schemeNsmul n) (Lₛ.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ D.g) ≫
      D.L.schemeNsmul n =
      (Lₛ.schemeKerStr n ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) ≫
        (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1 := by
    rw [Category.assoc, ← hF1, ← Category.assoc, pullback.condition, Category.assoc, hF2,
      Category.assoc]
  refine ⟨pullback.lift _ _ w, pullback.lift_fst _ _ _, ?_⟩

  have hI : IsPullback D.g fₛ D.f (Spec.map (CommRingCat.ofHom (algebraMap B S))) := D.cart
  have hIV : IsPullback D.g (Lₛ.schemeNsmul n) (D.L.schemeNsmul n) D.g := by
    have s : IsPullback D.g (Lₛ.schemeNsmul n ≫ fₛ) (D.L.schemeNsmul n ≫ D.f)
        (Spec.map (CommRingCat.ofHom (algebraMap B S))) := by
      rw [RelativeGroupLaw.schemeNsmul_over, RelativeGroupLaw.schemeNsmul_over]; exact hI
    exact IsPullback.of_bot s hF1.symm hI
  have hKs : IsPullback (pullback.fst (Lₛ.schemeNsmul n) (Lₛ.one (𝟙 (Spec (CommRingCat.of S)))).1)
      (Lₛ.schemeKerStr n) (Lₛ.schemeNsmul n) (Lₛ.one (𝟙 (Spec (CommRingCat.of S)))).1 :=
    IsPullback.of_hasPullback _ _
  have hK : IsPullback (pullback.fst (D.L.schemeNsmul n) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1)
      (D.L.schemeKerStr n) (D.L.schemeNsmul n) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1 :=
    IsPullback.of_hasPullback _ _
  have outer := hKs.paste_horiz hIV
  rw [← pullback.lift_fst _ _ w, hF2] at outer
  exact IsPullback.of_right outer (pullback.lift_snd _ _ w) hK

end S_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison (solution)
