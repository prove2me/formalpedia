-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translate_of_comp_schemeNsmul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ceab9b50-fffd-5f3d-a21c-08f6f04a5ac1

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_GoodReductionJacobian_NsmulEigenSubdatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_flat_etale_schemeKerStr_of_isUnit
import Theorems.Thm_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_isFinite_of_etale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translate_of_comp_schemeNsmul_eq
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

namespace Ws23TS2

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} (L : RelativeGroupLaw K f)

theorem nsmul_coe {Z : Scheme.{u}} (t : Z ⟶ Spec (CommRingCat.of K)) (n : ℕ) (P : SchemeHomOver t f) :
    (L.nsmul t n P).1 = P.1 ≫ L.schemeNsmul n := by
  have hid : GoodReductionJacobian.schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint) = P :=
    Subtype.ext (Category.comp_id _)
  have hn := L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint
  rw [hid] at hn
  rw [← hn, GoodReductionJacobian.schemeHomOverComp_coe]
  rfl

theorem one_coe {Z : Scheme.{u}} (t : Z ⟶ Spec (CommRingCat.of K)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  have := L.one_natural (𝟙 (Spec (CommRingCat.of K))) t t (Category.comp_id _)
  rw [← this, GoodReductionJacobian.schemeHomOverComp_coe]

theorem mul_coe_comp {Z Z' : Scheme.{u}} (t : Z ⟶ Spec (CommRingCat.of K)) (ψ : Z' ⟶ Z)
    (P Q : SchemeHomOver t f) :
    ψ ≫ (L.mul t P Q).1 =
      (L.mul (ψ ≫ t) ⟨ψ ≫ P.1, by rw [Category.assoc, P.2]⟩ ⟨ψ ≫ Q.1, by rw [Category.assoc, Q.2]⟩).1 := by
  have := L.mul_natural t (ψ ≫ t) ψ rfl P Q
  have h := congrArg Subtype.val this
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  rw [h]
  rfl

theorem mul_coe_congr {Z : Scheme.{u}} {b₁ b₂ : Z ⟶ Spec (CommRingCat.of K)} (hb : b₁ = b₂)
    (P Q : SchemeHomOver b₁ f) (P' Q' : SchemeHomOver b₂ f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul b₁ P Q).1 = (L.mul b₂ P' Q').1 := by
  subst hb
  obtain ⟨p, hp⟩ := P; obtain ⟨p', hp'⟩ := P'; obtain ⟨q, hq⟩ := Q; obtain ⟨q', hq'⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ
  rfl

end Ws23TS2

open Ws23TS2 in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ A) (h : g₁ ≫ L.schemeNsmul n = g₂ ≫ L.schemeNsmul n) :
    ∃ U : L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n → Z.Opens, ⨆ P, U P = ⊤ ∧
      ∀ P, (U P).ι ≫ g₂ = (U P).ι ≫ g₁ ≫ L.translate P.1 := by
  classical

  have hnf : L.schemeNsmul n ≫ f = f := L.schemeNsmul_over n
  set t : Z ⟶ Spec (CommRingCat.of K) := g₁ ≫ f with ht
  have hg₂ : g₂ ≫ f = t := by
    rw [ht, ← hnf, ← Category.assoc, ← h, Category.assoc, hnf]
  let G₁ : SchemeHomOver t f := ⟨g₁, rfl⟩
  let G₂ : SchemeHomOver t f := ⟨g₂, hg₂⟩
  letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := fun x y => hc t x y }

  have hmul : ∀ P Q : SchemeHomOver t f, P * Q = L.mul t P Q := fun _ _ => rfl
  have hone : (1 : SchemeHomOver t f) = L.one t := rfl
  have hpow : ∀ (m : ℕ) (P : SchemeHomOver t f), P ^ m = L.nsmul t m P := by
    intro m P
    induction m with
    | zero => rw [pow_zero, RelativeGroupLaw.nsmul_zero]; rfl
    | succ m ih => rw [pow_succ, RelativeGroupLaw.nsmul_succ, hmul, ih]

  let d : SchemeHomOver t f := G₂ * G₁⁻¹
  have hG : G₁ ^ n = G₂ ^ n := by
    apply Subtype.ext
    rw [hpow, hpow, nsmul_coe, nsmul_coe]
    exact h
  have hd : d ^ n = 1 := by
    show (G₂ * G₁⁻¹) ^ n = 1
    rw [mul_pow, inv_pow, ← hG, mul_inv_cancel]
  have hd1 : d.1 ≫ L.schemeNsmul n = t ≫ (L.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
    rw [← nsmul_coe, ← hpow, hd, hone, one_coe]

  let δ : Z ⟶ L.schemeKer n := pullback.lift d.1 t hd1
  have hδ₁ : δ ≫ pullback.fst _ _ = d.1 := pullback.lift_fst _ _ _
  have hδ₂ : δ ≫ L.schemeKerStr n = t := pullback.lift_snd _ _ _
  have hfst_f : pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f = L.schemeKerStr n := by
    have h1 : pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ L.schemeNsmul n ≫ f =
        pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ (L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f := by
      rw [← Category.assoc, pullback.condition, Category.assoc]
    rw [hnf] at h1
    rw [h1, (L.one (𝟙 (Spec (CommRingCat.of K)))).2, Category.comp_id]

  haveI : Smooth f := hA.smooth
  have hunit : IsUnit (n : K) := isUnit_iff_ne_zero.2 hn
  obtain ⟨hfin, -, het, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.isFinite_flat_etale_schemeKerStr_of_isUnit L hA hc g n hunit
  haveI := hfin
  haveI := het

  have hsplit := fun x : ↥(L.schemeKer n) =>
    AlgebraicGeometry.exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_isFinite_of_etale (L.schemeKerStr n) x
  choose V hV hViso using hsplit

  let px : ↥(L.schemeKer n) → (Spec (CommRingCat.of K) ⟶ A) := fun x =>
    inv ((V x).ι ≫ L.schemeKerStr n) ≫ (V x).ι ≫ pullback.fst _ _
  have hpx : ∀ x, px x ≫ f = 𝟙 (Spec (CommRingCat.of K)) := by
    intro x
    show (inv ((V x).ι ≫ L.schemeKerStr n) ≫ (V x).ι ≫ pullback.fst _ _) ≫ f = 𝟙 _
    rw [Category.assoc, Category.assoc, hfst_f, IsIso.inv_hom_id]
  let Px : ↥(L.schemeKer n) → SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f := fun x => ⟨px x, hpx x⟩

  have hPx : ∀ x, Px x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n := by
    intro x
    rw [RelativeGroupLaw.mem_torsionSubset, RelativeGroupLaw.isTorsionPoint_def]
    apply Subtype.ext
    rw [nsmul_coe]
    show (inv ((V x).ι ≫ L.schemeKerStr n) ≫ (V x).ι ≫ pullback.fst _ _) ≫ L.schemeNsmul n =
      (L.one (𝟙 (Spec (CommRingCat.of K)))).1
    have hinv : inv ((V x).ι ≫ L.schemeKerStr n) ≫ (V x).ι ≫
        pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of K)))).1 = 𝟙 _ :=
      IsIso.inv_hom_id ((V x).ι ≫ L.schemeKerStr n)
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% hinv]

  have hqP : ∀ P : L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n,
      P.1.1 ≫ L.schemeNsmul n = 𝟙 _ ≫ (L.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
    intro P
    have hT : L.IsTorsionPoint _ n P.1 := P.2
    rw [RelativeGroupLaw.isTorsionPoint_def] at hT
    have := congrArg Subtype.val hT
    rw [nsmul_coe] at this
    rw [this, Category.id_comp]
  let qP : L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n → (Spec (CommRingCat.of K) ⟶ L.schemeKer n) := fun P =>
    pullback.lift P.1.1 (𝟙 _) (hqP P)
  let xP : L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n → ↥(L.schemeKer n) := fun P =>
    (qP P).base (IsLocalRing.closedPoint K)

  have hpxP : ∀ P : L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n, px (xP P) = P.1.1 := by
    intro P
    have hrange : Set.range (qP P).base ⊆ Set.range (V (xP P)).ι.base := by
      rintro _ ⟨y, rfl⟩
      obtain rfl : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      rw [Scheme.Opens.range_ι, hV]
      rfl
    let q' := IsOpenImmersion.lift (V (xP P)).ι (qP P) hrange
    have hq' : q' ≫ (V (xP P)).ι = qP P := IsOpenImmersion.lift_fac _ _ _
    have hq'iso : q' ≫ ((V (xP P)).ι ≫ L.schemeKerStr n) = 𝟙 _ := by
      rw [← Category.assoc, hq']
      exact pullback.lift_snd _ _ _
    have hq'inv : q' = inv ((V (xP P)).ι ≫ L.schemeKerStr n) :=
      IsIso.eq_inv_of_inv_hom_id hq'iso
    show inv ((V (xP P)).ι ≫ L.schemeKerStr n) ≫ (V (xP P)).ι ≫ pullback.fst _ _ = _
    rw [← hq'inv, ← Category.assoc, hq']
    exact pullback.lift_fst _ _ _

  have hxPx : ∀ x : ↥(L.schemeKer n), xP ⟨Px x, hPx x⟩ = x := by
    intro x
    have hq : qP ⟨Px x, hPx x⟩ = inv ((V x).ι ≫ L.schemeKerStr n) ≫ (V x).ι := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc]
      · rw [pullback.lift_snd, Category.assoc]
        exact (IsIso.inv_hom_id ((V x).ι ≫ L.schemeKerStr n)).symm
    show (qP ⟨Px x, hPx x⟩).base (IsLocalRing.closedPoint K) = x
    have hmem : (qP ⟨Px x, hPx x⟩).base (IsLocalRing.closedPoint K) ∈ ((V x : Set ↥(L.schemeKer n))) := by
      rw [hq, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    rw [hV x] at hmem
    exact hmem

  refine ⟨fun P => δ ⁻¹ᵁ (V (xP P)), ?_, ?_⟩
  ·
    apply le_antisymm le_top
    intro z _
    apply TopologicalSpace.Opens.mem_iSup.2
    refine ⟨⟨Px (δ.base z), hPx _⟩, ?_⟩
    show δ.base z ∈ (V (xP ⟨Px (δ.base z), hPx _⟩) : Set _)
    rw [hxPx, hV]
    rfl
  · intro P
    set W : Z.Opens := δ ⁻¹ᵁ (V (xP P)) with hW

    have hdW : W.ι ≫ d.1 = (W.ι ≫ t) ≫ P.1.1 := by
      have h1 : W.ι ≫ δ = (δ ∣_ V (xP P)) ≫ (V (xP P)).ι := (morphismRestrict_ι δ (V (xP P))).symm
      have h2 : (V (xP P)).ι ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of K)))).1 =
          ((V (xP P)).ι ≫ L.schemeKerStr n) ≫ px (xP P) := by
        show _ = ((V (xP P)).ι ≫ L.schemeKerStr n) ≫ inv ((V (xP P)).ι ≫ L.schemeKerStr n) ≫ (V (xP P)).ι ≫ pullback.fst _ _
        rw [IsIso.hom_inv_id_assoc]
      calc W.ι ≫ d.1 = W.ι ≫ δ ≫ pullback.fst _ _ := by rw [hδ₁]
        _ = (δ ∣_ V (xP P)) ≫ (V (xP P)).ι ≫ pullback.fst _ _ := by rw [← Category.assoc, h1, Category.assoc]
        _ = (δ ∣_ V (xP P)) ≫ ((V (xP P)).ι ≫ L.schemeKerStr n) ≫ px (xP P) := by rw [h2]
        _ = ((W.ι ≫ δ) ≫ L.schemeKerStr n) ≫ px (xP P) := by rw [h1]; simp only [Category.assoc]
        _ = (W.ι ≫ t) ≫ P.1.1 := by rw [Category.assoc W.ι δ, hδ₂, hpxP]

    have hG₂ : G₂ = d * G₁ := by show G₂ = G₂ * G₁⁻¹ * G₁; rw [inv_mul_cancel_right]
    have e1 : W.ι ≫ g₂ = (L.mul (W.ι ≫ t) ⟨W.ι ≫ d.1, by rw [Category.assoc, d.2]⟩ ⟨W.ι ≫ g₁, by rw [Category.assoc]⟩).1 := by
      have := mul_coe_comp L t W.ι d G₁
      rw [← hmul, ← hG₂] at this
      exact this

    have e2 : (W.ι ≫ g₁) ≫ L.translate P.1 =
        (L.mul ((W.ι ≫ g₁) ≫ f) ⟨(W.ι ≫ g₁) ≫ (RelativeGroupLaw.idPoint (f := f)).1, by rw [Category.assoc, (RelativeGroupLaw.idPoint (f := f)).2]⟩
          ⟨(W.ι ≫ g₁) ≫ (f ≫ P.1.1), by simp only [Category.assoc, P.1.2, Category.comp_id]⟩).1 :=
      mul_coe_comp L f (W.ι ≫ g₁) RelativeGroupLaw.idPoint ⟨f ≫ P.1.1, by rw [Category.assoc, P.1.2, Category.comp_id]⟩
    rw [Category.assoc] at e2
    show W.ι ≫ g₂ = W.ι ≫ g₁ ≫ L.translate P.1
    rw [e1, hc (W.ι ≫ t), e2]

    apply mul_coe_congr L
    · rw [ht, Category.assoc]
    · show W.ι ≫ g₁ = W.ι ≫ g₁ ≫ 𝟙 A
      rw [Category.comp_id]
    · show W.ι ≫ d.1 = (W.ι ≫ g₁) ≫ f ≫ P.1.1
      rw [hdW, ht]
      simp only [Category.assoc]

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translate_of_comp_schemeNsmul_eq
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translate_of_comp_schemeNsmul_eq (solution)
