-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.existsUnique_schemeKer_comp_fst_eq_fst_comp_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b8b01643-633d-5a93-9b54-c7da93d2ea41

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeKer_comp_fst_eq_fst_comp_of_hom

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeKer_comp_fst_eq_fst_comp_of_hom.GoodReductionJacobian"

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul nsmul_succ nsmul_natural idPoint schemeNsmul schemeNsmul_over schemeKer mul_assoc one inv one_mul inv_mul_cancel mul"
namespace LiftEK
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) (n : ℕ)

set_option hygiene false in

local notation "Kfst" => pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1

set_option hygiene false in

local notation "Ksnd" => pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1

theorem snd_eq_fst_comp : Ksnd = Kfst ≫ f := by
  have h1 : Kfst ≫ L.schemeNsmul n = Ksnd ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
    pullback.condition
  have h2 : (Kfst ≫ L.schemeNsmul n) ≫ f = Kfst ≫ f := by
    rw [Category.assoc, L.schemeNsmul_over]
  rw [h1, Category.assoc, (L.one (𝟙 _)).2, Category.comp_id] at h2
  exact h2

theorem nsmul_coe_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have hid : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (idPoint : SchemeHomOver f f) = x := by
    apply Subtype.ext
    simp [GoodReductionJacobian.schemeHomOverComp]
  have h := L.nsmul_natural f t x.1 x.2 n idPoint
  rw [hid] at h
  rw [← h]
  rfl

variable (φ : SchemeHomOver f f)
  (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
      L.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))

include hφ in

theorem one_comp_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (L.one t) φ = L.one t := by
  have h : L.mul t (NeronModelInfra.schemeHomOverComp (L.one t) φ)
      (NeronModelInfra.schemeHomOverComp (L.one t) φ) =
      NeronModelInfra.schemeHomOverComp (L.one t) φ := by
    rw [← hφ t, L.one_mul]
  calc NeronModelInfra.schemeHomOverComp (L.one t) φ
      = L.mul t (L.one t) (NeronModelInfra.schemeHomOverComp (L.one t) φ) := (L.one_mul t _).symm
    _ = L.mul t (L.mul t (L.inv t (NeronModelInfra.schemeHomOverComp (L.one t) φ))
          (NeronModelInfra.schemeHomOverComp (L.one t) φ))
          (NeronModelInfra.schemeHomOverComp (L.one t) φ) := by
        rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t (NeronModelInfra.schemeHomOverComp (L.one t) φ))
          (L.mul t (NeronModelInfra.schemeHomOverComp (L.one t) φ)
            (NeronModelInfra.schemeHomOverComp (L.one t) φ)) := by
        rw [L.mul_assoc]
    _ = L.mul t (L.inv t (NeronModelInfra.schemeHomOverComp (L.one t) φ))
          (NeronModelInfra.schemeHomOverComp (L.one t) φ) := by rw [h]
    _ = L.one t := L.inv_mul_cancel t _

include hφ in

theorem nsmul_comp_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (m : ℕ)
    (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (L.nsmul t m x) φ =
      L.nsmul t m (NeronModelInfra.schemeHomOverComp x φ) := by
  induction m with
  | zero => exact one_comp_hom L φ hφ t
  | succ m ih => rw [nsmul_succ, hφ, ih, nsmul_succ]

include hφ in

theorem hom_comp_schemeNsmul : φ.1 ≫ L.schemeNsmul n = L.schemeNsmul n ≫ φ.1 := by
  have h1 : (L.nsmul f n φ).1 = φ.1 ≫ L.schemeNsmul n := nsmul_coe_eq L n f φ
  have h2 : NeronModelInfra.schemeHomOverComp (idPoint : SchemeHomOver f f) φ = φ :=
    Subtype.ext (Category.id_comp _)
  have h3 := congrArg Subtype.val (nsmul_comp_hom L φ hφ f n idPoint)
  rw [h2, h1] at h3
  exact h3.symm

include hφ in

theorem unitSection_comp_hom :
    (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ φ.1 = (L.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
  congrArg Subtype.val (one_comp_hom L φ hφ (𝟙 _))

def eKMor : L.schemeKer n ⟶ L.schemeKer n :=
  pullback.lift (Kfst ≫ φ.1) Ksnd (by
    rw [Category.assoc, hom_comp_schemeNsmul L n φ hφ, ← Category.assoc, pullback.condition,
      Category.assoc, unitSection_comp_hom L φ hφ])

theorem eKMor_fst : eKMor L n φ hφ ≫ Kfst = Kfst ≫ φ.1 :=
  pullback.lift_fst _ _ _

def eK : SchemeHomOver (Kfst ≫ f) (Kfst ≫ f) :=
  ⟨eKMor L n φ hφ, by rw [← Category.assoc, eKMor_fst, Category.assoc, φ.2]⟩

theorem eK_fst : (eK L n φ hφ).1 ≫ Kfst = Kfst ≫ φ.1 :=
  eKMor_fst L n φ hφ

theorem ext_of_comp_fst {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)}
    (a b : SchemeHomOver s (Kfst ≫ f)) (h : a.1 ≫ Kfst = b.1 ≫ Kfst) : a = b := by
  apply Subtype.ext
  apply pullback.hom_ext h
  rw [snd_eq_fst_comp L n, a.2, b.2]

theorem eK_unique (eK' : SchemeHomOver (Kfst ≫ f) (Kfst ≫ f)) (h : eK'.1 ≫ Kfst = Kfst ≫ φ.1) :
    eK' = eK L n φ hφ :=
  ext_of_comp_fst L n _ _ (h.trans (eK_fst L n φ hφ).symm)

def fstOver : SchemeHomOver (Kfst ≫ f) f :=
  ⟨Kfst, rfl⟩

theorem eK_comp_fstOver :
    NeronModelInfra.schemeHomOverComp (eK L n φ hφ) (fstOver L n) =
      NeronModelInfra.schemeHomOverComp (fstOver L n) φ :=
  Subtype.ext (eK_fst L n φ hφ)

include hφ in

theorem eK_hom (LK : RelativeGroupLaw R (Kfst ≫ f))
    (hLK : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s (Kfst ≫ f)),
      NeronModelInfra.schemeHomOverComp (LK.mul s x y) (fstOver L n) =
        L.mul s (NeronModelInfra.schemeHomOverComp x (fstOver L n))
          (NeronModelInfra.schemeHomOverComp y (fstOver L n)))
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s (Kfst ≫ f)) :
    NeronModelInfra.schemeHomOverComp (LK.mul s x y) (eK L n φ hφ) =
      LK.mul s (NeronModelInfra.schemeHomOverComp x (eK L n φ hφ))
        (NeronModelInfra.schemeHomOverComp y (eK L n φ hφ)) := by
  apply ext_of_comp_fst L n
  change (NeronModelInfra.schemeHomOverComp
      (NeronModelInfra.schemeHomOverComp (LK.mul s x y) (eK L n φ hφ)) (fstOver L n)).1 =
    (NeronModelInfra.schemeHomOverComp
      (LK.mul s (NeronModelInfra.schemeHomOverComp x (eK L n φ hφ))
        (NeronModelInfra.schemeHomOverComp y (eK L n φ hφ))) (fstOver L n)).1
  congr 1
  rw [NeronModelInfra.schemeHomOverComp_assoc, eK_comp_fstOver, ← NeronModelInfra.schemeHomOverComp_assoc,
    hLK, hφ, NeronModelInfra.schemeHomOverComp_assoc, NeronModelInfra.schemeHomOverComp_assoc,
    ← eK_comp_fstOver, ← NeronModelInfra.schemeHomOverComp_assoc,
    ← NeronModelInfra.schemeHomOverComp_assoc, ← hLK]

end GoodReductionJacobian.RelativeGroupLaw.LiftEK

end

open _root_.GoodReductionJacobian.RelativeGroupLaw _root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeKer_comp_fst_eq_fst_comp_of_hom.GoodReductionJacobian.RelativeGroupLaw in
theorem solution
    {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (φ : SchemeHomOver f f)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
        L.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) :
    ∃ eK : SchemeHomOver (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f),
      eK.1 ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ φ.1 ∧
      (∀ eK' : SchemeHomOver (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f),
        eK'.1 ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ φ.1 → eK' = eK) ∧
      (∀ (LK : RelativeGroupLaw R (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
        (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
          NeronModelInfra.schemeHomOverComp (LK.mul s x y)
              (⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f) =
            L.mul s (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)
              (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)) →
        ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
          NeronModelInfra.schemeHomOverComp (LK.mul s x y) eK =
            LK.mul s (NeronModelInfra.schemeHomOverComp x eK) (NeronModelInfra.schemeHomOverComp y eK)) := by
  refine ⟨LiftEK.eK L n φ hφ, LiftEK.eK_fst L n φ hφ, fun eK' h => LiftEK.eK_unique L n φ hφ eK' h, ?_⟩
  intro LK hLK T s x y
  exact LiftEK.eK_hom L n φ hφ LK hLK s x y

end S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeKer_comp_fst_eq_fst_comp_of_hom
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeKer_comp_fst_eq_fst_comp_of_hom (solution)
