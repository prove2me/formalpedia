-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_dia_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/360c28b2-adce-5e9c-a3e2-bc3fb9cf7f31

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_dia_pointEquivPlace_eq_smul_placeOfPoint_eq_smul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel

open scoped MatrixGroups

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
    (d : (ZMod M)ˣ) (i : Fin 2)
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
      u'.1 = u.1 ≫ (𝔛.dia d).hom ∧
      Set.range u'.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) ∧
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut (diamondAutHBar M H d) • 𝔛.Meta.pointEquivPlace y ∧
      ∃ uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1 ∧
        uκ' ≫ pullback.snd _ _ = 𝟙 _ ∧
        uκ' = uκ ≫ XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso (𝔛.dia d) (𝔛.dia_over d))
          ((IsLocalRing.residue ↥A).comp ρ) ∧
        ∃ P' : closedPoints (𝔛.Mfib A hA ρ hρ).C,
          (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P'.1 = uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
          (𝔛.Mfib A hA ρ hρ).placeOfPoint P' =
            SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d))) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P := by

  have hsmU : Smooth (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) := SmoothOfRelativeDimension.smooth 1 _
  have hV : Smooth (((𝔛.dia d).hom ''ᵁ 𝔛.smoothLocus).ι ≫ toBase p (ΓM M H) hj) := by
    have e : ((𝔛.dia d).hom ''ᵁ 𝔛.smoothLocus).ι ≫ toBase p (ΓM M H) hj =
        ((𝔛.dia d).hom.isoImage 𝔛.smoothLocus).inv ≫ (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) := by
      rw [← Scheme.Hom.isoImage_inv_ι, Category.assoc, Category.assoc, 𝔛.dia_over d]
    rw [e, MorphismProperty.cancel_left_of_respectsIso @Smooth]
    exact hsmU
  have hVle : (𝔛.dia d).hom ''ᵁ 𝔛.smoothLocus ≤ 𝔛.smoothLocus := 𝔛.smoothLocus_maximal _ hV

  have hyT : (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ (𝔛.dia d).hom) ≫ toBase p (ΓM M H) hj =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    simp only [Category.assoc]
    rw [𝔛.dia_over d, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, y.2]
  have hinvB : inv 𝔛.eeta ≫ 𝔛.Meta.toBase = pullback.snd _ _ := by
    rw [← 𝔛.heeta, IsIso.inv_hom_id_assoc]
  have hy'sec : (pullback.lift _ _ hyT ≫ inv 𝔛.eeta) ≫ 𝔛.Meta.toBase = 𝟙 _ := by
    rw [Category.assoc, hinvB, pullback.lift_snd]
  have hy'gen : (pullback.lift _ _ hyT ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ pullback.fst _ _ =
      y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ (𝔛.dia d).hom := by
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

  have hd := hdia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) P
  obtain ⟨hmem, hpl⟩ := hd
  have hkey := 𝔛.comp_dia A hA ρ hρ i d
  have hkeyP : (XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso (𝔛.dia d) (𝔛.dia_over d))
        ((IsLocalRing.residue ↥A).comp ρ)).base ((𝔛.comp A hA ρ hρ i).base ((𝔛.efib A hA ρ hρ).base P.1)) =
      (𝔛.comp A hA ρ hρ i).base ((XHDRLevel.fibreMap (overOfIso (𝔛.dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d))
        (𝔛.dia0_over _)) ((IsLocalRing.residue ↥A).comp ρ)).base ((𝔛.efib A hA ρ hρ).base P.1)) := by
    rw [← Scheme.Hom.comp_apply, hkey, Scheme.Hom.comp_apply]
  have hinv : ∀ z, (𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hPpt : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) =
      (𝔛.comp A hA ρ hρ i).base ((𝔛.efib A hA ρ hρ).base P.1) := by
    rw [← hP, Scheme.Hom.comp_apply]

  refine ⟨⟨pullback.lift _ _ hyT ≫ inv 𝔛.eeta, hy'sec⟩,
    ⟨u.1 ≫ (𝔛.dia d).hom, by rw [Category.assoc, 𝔛.dia_over d]; exact u.2⟩, ?_, rfl, ?_,
    𝔛.dia_generic d y _ hy'gen,
    uκ ≫ XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso (𝔛.dia d) (𝔛.dia_over d))
      ((IsLocalRing.residue ↥A).comp ρ), ?_, ?_, rfl, ⟨_, hmem⟩, ?_, hpl⟩
  ·
    show Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 ≫ (𝔛.dia d).hom = _
    rw [hy'gen, ← Category.assoc, hu, Category.assoc, Category.assoc]
  ·
    rintro _ ⟨z, rfl⟩
    show (u.1 ≫ (𝔛.dia d).hom).base z ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))
    rw [Scheme.Hom.comp_apply]
    exact hVle ((Scheme.Hom.apply_mem_image_iff (𝔛.dia d).hom).mpr (husm ⟨z, rfl⟩))
  ·
    rw [Category.assoc, XHDRLevel.fibreMap, pullback.lift_fst, ← Category.assoc, huκ₁, Category.assoc]
    rfl
  ·
    rw [Category.assoc, XHDRLevel.fibreMap, pullback.lift_snd, ← Category.assoc, huκ₂]
    rfl
  ·
    show (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base ((inv (𝔛.efib A hA ρ hρ)).base _) =
      (uκ ≫ XHDRLevel.fibreMap (overOfIso (𝔛.dia d) (𝔛.dia_over d)) ((IsLocalRing.residue ↥A).comp ρ)).base _
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hinv, hPpt, hkeyP]

#print axioms solution

end S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_dia_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_dia_pointEquivPlace_eq_smul_placeOfPoint_eq_smul (solution)
