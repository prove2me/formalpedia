-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c7bae88c-e34a-5451-833b-6acb5b72e500

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel

open scoped MatrixGroups

namespace A3w

theorem base_apply_eq {X Y : Scheme} {f g : X ⟶ Y} (h : f = g) (x : X) : f.base x = g.base x := by rw [h]

variable {p : ℕ} [Fact p.Prime] {Γ Γ' : Subgroup SL(2, ℤ)} {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

theorem fibreMap_fst (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    XHDRLevel.fibreMap (Γ := Γ) (Γ' := Γ') φ toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φ.1 := by
  rw [XHDRLevel.fibreMap, pullback.lift_fst]

theorem fibreMap_snd (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    XHDRLevel.fibreMap (Γ := Γ) (Γ' := Γ') φ toκ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [XHDRLevel.fibreMap, pullback.lift_snd, Category.comp_id]

end A3w

namespace A3w

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)

theorem w_inv_over : 𝔛.w.inv ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj := by
  rw [Iso.inv_comp_eq, 𝔛.w_over]

theorem image_w_inv_le_smoothLocus : 𝔛.w.inv ''ᵁ 𝔛.smoothLocus ≤ 𝔛.smoothLocus := by
  have hsmU : Smooth (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) := SmoothOfRelativeDimension.smooth 1 _
  have hV : Smooth ((𝔛.w.inv ''ᵁ 𝔛.smoothLocus).ι ≫ toBase p (ΓM M H) hj) := by
    have e : (𝔛.w.inv ''ᵁ 𝔛.smoothLocus).ι ≫ toBase p (ΓM M H) hj =
        (𝔛.w.inv.isoImage 𝔛.smoothLocus).inv ≫ (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) := by
      rw [← Scheme.Hom.isoImage_inv_ι, Category.assoc, Category.assoc, w_inv_over]
    rw [e, MorphismProperty.cancel_left_of_respectsIso @Smooth]
    exact hsmU
  exact 𝔛.smoothLocus_maximal _ hV

theorem fibreMap_w_symm_comp_w {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w.symm (w_inv_over 𝔛)) toκ ≫
      XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w 𝔛.w_over) toκ = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, fibreMap_fst, ← Category.assoc, fibreMap_fst, Category.assoc, Category.id_comp]
    change pullback.fst _ _ ≫ 𝔛.w.inv ≫ 𝔛.w.hom = _
    rw [Iso.inv_hom_id, Category.comp_id]
  · rw [Category.assoc, fibreMap_snd, fibreMap_snd, Category.id_comp]

theorem fibreMap_w_comp_w_symm {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w 𝔛.w_over) toκ ≫
      XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w.symm (w_inv_over 𝔛)) toκ = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, fibreMap_fst, ← Category.assoc, fibreMap_fst, Category.assoc, Category.id_comp]
    change pullback.fst _ _ ≫ 𝔛.w.hom ≫ 𝔛.w.inv = _
    rw [Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, fibreMap_snd, fibreMap_snd, Category.id_comp]

theorem w_inv_eq (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (d : (ZMod M)ˣ) (hd : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d = pb⁻¹) :
    𝔛.w.inv = 𝔛.w.hom ≫ (𝔛.dia d⁻¹).hom ∧ ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d⁻¹ = pb := by
  have hdp : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 := by
    rw [hd, ← hpb, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hwsq := 𝔛.w_sq d hdp
  have hdia1 : (𝔛.dia d).hom ≫ (𝔛.dia d⁻¹).hom = 𝟙 _ := by
    rw [← 𝔛.dia_mul, mul_inv_cancel, 𝔛.dia_mem 1 (one_mem H)]
    rfl
  refine ⟨?_, by rw [map_inv, hd, inv_inv]⟩
  rw [← cancel_epi 𝔛.w.hom, Iso.hom_inv_id, ← Category.assoc, hwsq, hdia1]

end A3w

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((XHDRLevel.fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)
    (i : Fin 2)
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (husm : Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) :
    ∃ (y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ u'.1 = y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
      u'.1 = u.1 ≫ 𝔛.w.inv ∧
      Set.range u'.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) ∧
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y ∧
      ∃ uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1 ∧
        uκ' ≫ pullback.snd _ _ = 𝟙 _ ∧
        uκ' ≫ XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w 𝔛.w_over)
          ((IsLocalRing.residue ↥A).comp ρ) = uκ ∧
        ∃ P' : closedPoints (𝔛.Mfib A hA ρ hρ).C,
          (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ (if i = 0 then 1 else 0)).base P'.1 =
            uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
          (𝔛.Mfib A hA ρ hρ).placeOfPoint P' =
            (if i = 0 then (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
              (CuspForm.gammaLift (M / p) pb))) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P
              else (𝔛.Mfib A hA ρ hρ).placeOfPoint P) := by

  have hwinvB : 𝔛.w.inv ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj := A3w.w_inv_over 𝔛
  have hVle : 𝔛.w.inv ''ᵁ 𝔛.smoothLocus ≤ 𝔛.smoothLocus := A3w.image_w_inv_le_smoothLocus 𝔛

  have hyT : (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.inv) ≫ toBase p (ΓM M H) hj =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    simp only [Category.assoc]
    rw [hwinvB, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, y.2]
  have hinvB : inv 𝔛.eeta ≫ 𝔛.Meta.toBase = pullback.snd _ _ := by
    rw [← 𝔛.heeta, IsIso.inv_hom_id_assoc]
  have hy'sec : (pullback.lift _ _ hyT ≫ inv 𝔛.eeta) ≫ 𝔛.Meta.toBase = 𝟙 _ := by
    rw [Category.assoc, hinvB, pullback.lift_snd]
  have hy'gen : (pullback.lift _ _ hyT ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ pullback.fst _ _ =
      y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.inv := by
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  have hy'w : (pullback.lift _ _ hyT ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom =
      y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ := by
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst_assoc, Iso.inv_hom_id, Category.comp_id]

  have hfst' : XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w.symm hwinvB)
      ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔛.w.inv :=
    A3w.fibreMap_fst _ _
  have hsnd' : XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w.symm hwinvB)
      ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.snd _ _ = pullback.snd _ _ :=
    A3w.fibreMap_snd _ _
  have hfstw : XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w 𝔛.w_over)
      ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔛.w.hom :=
    A3w.fibreMap_fst _ _
  have hsndw : XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w 𝔛.w_over)
      ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.snd _ _ = pullback.snd _ _ :=
    A3w.fibreMap_snd _ _
  have hinvw := A3w.fibreMap_w_symm_comp_w 𝔛 ((IsLocalRing.residue ↥A).comp ρ)
  have hwinv' := A3w.fibreMap_w_comp_w_symm 𝔛 ((IsLocalRing.residue ↥A).comp ρ)
  have hback : (uκ ≫ XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w.symm hwinvB)
        ((IsLocalRing.residue ↥A).comp ρ)) ≫ XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w 𝔛.w_over)
      ((IsLocalRing.residue ↥A).comp ρ) = uκ := by
    rw [Category.assoc, hinvw, Category.comp_id]
  have hinvE : ∀ z, (𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hPpt : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) =
      (𝔛.comp A hA ρ hρ i).base ((𝔛.efib A hA ρ hρ).base P.1) := by
    rw [← hP, Scheme.Hom.comp_apply]

  refine ⟨⟨pullback.lift _ _ hyT ≫ inv 𝔛.eeta, hy'sec⟩,
    ⟨u.1 ≫ 𝔛.w.inv, by rw [Category.assoc, hwinvB]; exact u.2⟩, ?_, rfl, ?_, hwgen y _ hy'w,
    (uκ ≫ XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w.symm hwinvB)
        ((IsLocalRing.residue ↥A).comp ρ)), ?_, ?_, hback, ?_⟩
  ·
    show Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 ≫ 𝔛.w.inv = _
    rw [hy'gen, ← Category.assoc, hu, Category.assoc, Category.assoc]
  ·
    rintro _ ⟨z, rfl⟩
    show (u.1 ≫ 𝔛.w.inv).base z ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))
    rw [Scheme.Hom.comp_apply]
    exact hVle ((Scheme.Hom.apply_mem_image_iff 𝔛.w.inv).mpr (husm ⟨z, rfl⟩))
  ·
    rw [Category.assoc, hfst', ← Category.assoc, huκ₁, Category.assoc]
  ·
    rw [Category.assoc, hsnd', huκ₂]

  have huκ'pt : (uκ ≫ XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w.symm hwinvB)
        ((IsLocalRing.residue ↥A).comp ρ)).base (IsLocalRing.closedPoint (ResidueField ↥A)) =
      (XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w.symm hwinvB) ((IsLocalRing.residue ↥A).comp ρ)).base
        ((𝔛.comp A hA ρ hρ i).base ((𝔛.efib A hA ρ hρ).base P.1)) := by
    rw [Scheme.Hom.comp_apply, hPpt]
  obtain (hi | hi) : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  ·
    subst hi
    have hd := (ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM) pb⁻¹).choose_spec
    have hwd := A3w.w_inv_eq 𝔛 pb hpb _ hd
    have hwinv := hwd.1
    have hdbar := hwd.2

    have hfmap : XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w.symm hwinvB)
        ((IsLocalRing.residue ↥A).comp ρ) =
        XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ) ≫
          XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso (𝔛.dia (ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM) pb⁻¹).choose⁻¹) (𝔛.dia_over _))
            ((IsLocalRing.residue ↥A).comp ρ) := by
      apply pullback.hom_ext
      · rw [hfst', Category.assoc, A3w.fibreMap_fst, ← Category.assoc, hfstw, Category.assoc, hwinv]
        rfl
      · rw [hsnd', Category.assoc, A3w.fibreMap_snd, hsndw]

    have hcwz : ∀ z, (XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w 𝔛.w_over)
        ((IsLocalRing.residue ↥A).comp ρ)).base ((𝔛.comp A hA ρ hρ 0).base z) = (𝔛.comp A hA ρ hρ 1).base z := fun z => by
      have := A3w.base_apply_eq (𝔛.comp_w A hA ρ hρ) z
      rwa [Scheme.Hom.comp_apply] at this
    have hcdz : ∀ z, (XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso (𝔛.dia (ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM) pb⁻¹).choose⁻¹) (𝔛.dia_over _))
        ((IsLocalRing.residue ↥A).comp ρ)).base ((𝔛.comp A hA ρ hρ 1).base z) =
        (𝔛.comp A hA ρ hρ 1).base ((XHDRLevel.fibreMap (overOfIso (𝔛.dia0 pb) (𝔛.dia0_over pb))
          ((IsLocalRing.residue ↥A).comp ρ)).base z) := fun z => by
      have hcd := 𝔛.comp_dia A hA ρ hρ 1 (ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM) pb⁻¹).choose⁻¹
      rw [hdbar] at hcd
      have := A3w.base_apply_eq hcd z
      rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
    refine ⟨⟨_, (hdia0 pb P).fst⟩, ?_, ?_⟩
    · show (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base ((inv (𝔛.efib A hA ρ hρ)).base _) = _
      rw [Scheme.Hom.comp_apply, hinvE, huκ'pt, A3w.base_apply_eq hfmap, Scheme.Hom.comp_apply, hcwz, hcdz]
    · exact (hdia0 pb P).snd
  ·
    subst hi
    have hcwz' : ∀ z, (XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso 𝔛.w.symm hwinvB)
        ((IsLocalRing.residue ↥A).comp ρ)).base ((𝔛.comp A hA ρ hρ 1).base z) = (𝔛.comp A hA ρ hρ 0).base z := fun z => by
      have h1 := A3w.base_apply_eq (𝔛.comp_w A hA ρ hρ) z
      rw [Scheme.Hom.comp_apply] at h1
      have h2 := A3w.base_apply_eq hwinv' ((𝔛.comp A hA ρ hρ 0).base z)
      rw [Scheme.Hom.comp_apply, h1] at h2
      exact h2
    refine ⟨P, ?_, rfl⟩
    show (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P.1 = _
    rw [huκ'pt, Scheme.Hom.comp_apply, hcwz']

end S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq (solution)
