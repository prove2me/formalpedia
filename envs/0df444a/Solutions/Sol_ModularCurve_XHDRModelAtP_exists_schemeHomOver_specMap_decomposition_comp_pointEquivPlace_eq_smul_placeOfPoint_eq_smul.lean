-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_schemeHomOver_specMap_decomposition_comp_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/905a36f4-bcd9-5c5b-b5e2-c5a34884f5c2

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_specMap_decomposition_comp_pointEquivPlace_eq_smul_placeOfPoint_eq_smul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_specMap_decomposition_comp_pointEquivPlace_eq_smul_placeOfPoint_eq_smul.AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel"

open scoped MatrixGroups

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom Spec Spec.map Scheme Scheme.Hom.comp_apply Scheme.ΓSpecIso powCharRingHom_apply Scheme.frobenius_comp Scheme.frobenius_Spec" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.galconj_natCast_eq_zero_of_hom_Spec {κ : Type} [CommRing κ] (p : ℕ) [CharP κ p]
    {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of κ)) : (p : Γ(Y, ⊤)) = 0 := by
  have h : f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom (p : κ)) = (p : Γ(Y, ⊤)) := by
    rw [map_natCast, map_natCast]
  rw [← h, CharP.cast_eq_zero, map_zero, map_zero]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (frob : SemilinearAut (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM)))
    (hfrob : ∀ (x : ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM))) (n : ℤ),
      ((frob • x : ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM))) :
          LaurentSeries (ResidueField ↥A)).coeff n =
        ((x : LaurentSeries (ResidueField ↥A)).coeff n) ^ p)

    (hN : (p : Γ((fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), ⊤)) = 0)
    (θN : (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶ (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hθN₁ : θN ≫ pullback.fst _ _ = (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).frobenius p 1 Fact.out hN ≫ pullback.fst _ _)
    (hθN₂ : θN ≫ pullback.snd _ _ = pullback.snd _ _)

    (hM : (p : Γ((fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), ⊤)) = 0)
    (θM : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hθM₁ : θM ≫ pullback.fst _ _ = (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).frobenius p 1 Fact.out hM ≫ pullback.fst _ _)
    (hθM₂ : θM ≫ pullback.snd _ _ = pullback.snd _ _)

    (hfrobpl : ∀ P : closedPoints (𝔛.Mfib A hA ρ hρ).C,
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base ((𝔛.efib A hA ρ hρ ≫ θN).base P.1) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ = frob • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)

    (Fr : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hFr : Fr ∈ A.decompositionSubgroup ℚ)
    (φκ : ResidueField ↥A →+* ResidueField ↥A) (hφκ : ∀ a : ResidueField ↥A, φκ a = a ^ p)
    (hFrφ : ∀ a : ↥A, IsLocalRing.residue ↥A ((⟨Fr, hFr⟩ : ↥(A.decompositionSubgroup ℚ)) • a) = φκ (IsLocalRing.residue ↥A a))

    (i : Fin 2)
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (husm : Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))

    (hcompP : (𝔛.comp A hA ρ hρ i).base (θN.base ((𝔛.efib A hA ρ hρ).base P.1)) =
      θM.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1)) :
    ∃ (y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ u'.1 = y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
      u'.1 = Spec.map (CommRingCat.ofHom
        (MulSemiringAction.toRingHom (↥(A.decompositionSubgroup ℚ)) (↥A) ⟨Fr, hFr⟩)) ≫ u.1 ∧
      Set.range u'.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) ∧
      𝔛.Meta.pointEquivPlace y' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) Fr • 𝔛.Meta.pointEquivPlace y ∧
      ∃ uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
        uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1 ∧
        uκ' ≫ pullback.snd _ _ = 𝟙 _ ∧
        uκ' = uκ ≫ θM ∧
        ∃ P' : closedPoints (𝔛.Mfib A hA ρ hρ).C,
          (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P'.1 = uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
          (𝔛.Mfib A hA ρ hρ).placeOfPoint P' = frob • (𝔛.Mfib A hA ρ hρ).placeOfPoint P := by

  have hσρ : (MulSemiringAction.toRingHom (↥(A.decompositionSubgroup ℚ)) (↥A) ⟨Fr, hFr⟩).comp ρ = ρ := by
    refine RingHom.ext fun r => Subtype.val_injective ?_
    show Fr ((ρ r : ↥A) : AlgebraicClosure ℚ) = ((ρ r : ↥A) : AlgebraicClosure ℚ)
    have h1 : ((ρ r : ↥A) : AlgebraicClosure ℚ) = algebraMap (R p) (AlgebraicClosure ℚ) r := by
      rw [← hρ]; rfl
    rw [h1, IsScalarTower.algebraMap_apply (R p) ℚ (AlgebraicClosure ℚ), AlgEquiv.commutes]
  have hσsub : A.subtype.comp (MulSemiringAction.toRingHom (↥(A.decompositionSubgroup ℚ)) (↥A) ⟨Fr, hFr⟩) =
      (Fr : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype := RingHom.ext fun _ => rfl
  have hσres : (IsLocalRing.residue ↥A).comp (MulSemiringAction.toRingHom (↥(A.decompositionSubgroup ℚ)) (↥A) ⟨Fr, hFr⟩) =
      φκ.comp (IsLocalRing.residue ↥A) := RingHom.ext fun a => hFrφ a
  have hSρ : Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (↥(A.decompositionSubgroup ℚ)) (↥A) ⟨Fr, hFr⟩)) ≫
      Spec.map (CommRingCat.ofHom ρ) = Spec.map (CommRingCat.ofHom ρ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσρ]
  have hSsub : Spec.map (CommRingCat.ofHom A.subtype) ≫
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (↥(A.decompositionSubgroup ℚ)) (↥A) ⟨Fr, hFr⟩)) =
      Spec.map (CommRingCat.ofHom (Fr : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ Spec.map (CommRingCat.ofHom A.subtype) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hσsub]
  have hSres : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (↥(A.decompositionSubgroup ℚ)) (↥A) ⟨Fr, hFr⟩)) =
      Spec.map (CommRingCat.ofHom φκ) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hσres]

  have hκ0 : (p : Γ(Spec (CommRingCat.of (ResidueField ↥A)), ⊤)) = 0 :=
    AlgebraicGeometry.galconj_natCast_eq_zero_of_hom_Spec p (𝟙 _)
  have hFrobSpec : (Spec (CommRingCat.of (ResidueField ↥A))).frobenius p 1 Fact.out hκ0 = Spec.map (CommRingCat.ofHom φκ) := by
    refine (Scheme.frobenius_Spec p 1 Fact.out (CharP.cast_eq_zero (ResidueField ↥A) p)).trans ?_
    congr 2
    exact RingHom.ext fun a => by rw [AlgebraicGeometry.powCharRingHom_apply, pow_one, hφκ]

  have halg : Spec.map (CommRingCat.ofHom (Fr : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun s => ?_
    show Fr (algebraMap (R p) (AlgebraicClosure ℚ) s) = algebraMap (R p) (AlgebraicClosure ℚ) s
    rw [IsScalarTower.algebraMap_apply (R p) ℚ (AlgebraicClosure ℚ), AlgEquiv.commutes]
  have hw : (Spec.map (CommRingCat.ofHom (Fr : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ y.1 ≫ 𝔛.eeta ≫
      pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ≫ toBase p (ΓM M H) hj =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc y.1, y.2, Category.id_comp]
    simpa only [Category.id_comp] using halg
  have hinv : inv 𝔛.eeta ≫ 𝔛.Meta.toBase =
      pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) := by
    rw [← 𝔛.heeta, IsIso.inv_hom_id_assoc]
  have hy'E : ∃ y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _},
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Fr : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ := by
    refine ⟨⟨pullback.lift _ _ hw ≫ inv 𝔛.eeta, ?_⟩, ?_⟩
    · show (pullback.lift _ _ hw ≫ inv 𝔛.eeta) ≫ 𝔛.Meta.toBase = 𝟙 _
      rw [Category.assoc, hinv, pullback.lift_snd]
    · show (pullback.lift _ _ hw ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ pullback.fst _ _ = _
      rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  obtain ⟨y', hy'⟩ := hy'E

  obtain ⟨hP'mem, hP'pl⟩ := hfrobpl P
  have h1 : ∀ w, (𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base w) = w := fun w => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl

  refine ⟨y', ⟨Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (↥(A.decompositionSubgroup ℚ)) (↥A) ⟨Fr, hFr⟩)) ≫ u.1,
    by rw [Category.assoc, u.2, hSρ]⟩, ?_, rfl, ?_, 𝔛.hgal Fr y y' hy', uκ ≫ θM, ?_, ?_, rfl, ⟨_, hP'mem⟩, ?_, hP'pl⟩
  ·
    show Spec.map (CommRingCat.ofHom A.subtype) ≫
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (↥(A.decompositionSubgroup ℚ)) (↥A) ⟨Fr, hFr⟩)) ≫ u.1 = _
    rw [← Category.assoc, hSsub, Category.assoc, hu, hy']
  ·
    rintro _ ⟨t, rfl⟩
    exact husm ⟨_, rfl⟩
  ·
    rw [Category.assoc, hθM₁, ← Category.assoc, ← Scheme.frobenius_comp uκ p 1 Fact.out hκ0 hM, Category.assoc, huκ₁,
      hFrobSpec, ← Category.assoc, ← hSres, Category.assoc]
  ·
    rw [Category.assoc, hθM₂, huκ₂]
  ·
    show (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base ((inv (𝔛.efib A hA ρ hρ)).base ((𝔛.efib A hA ρ hρ ≫ θN).base P.1)) =
      (uκ ≫ θM).base (IsLocalRing.closedPoint (ResidueField ↥A))
    rw [Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply, hcompP, hP, Scheme.Hom.comp_apply]

#print axioms solution

end S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_specMap_decomposition_comp_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_specMap_decomposition_comp_pointEquivPlace_eq_smul_placeOfPoint_eq_smul (solution)
