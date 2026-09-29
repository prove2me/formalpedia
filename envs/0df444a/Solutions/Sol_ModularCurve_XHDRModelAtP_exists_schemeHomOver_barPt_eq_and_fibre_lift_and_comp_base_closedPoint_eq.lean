-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9d89d24f-072b-53af-b35b-3ce9c8f702da

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Theorems.Thm_AlgebraicGeometry_existsUnique_hom_comp_eq_specMap_and_specMap_comp_eq_of_isProper_of_valuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) :
    ∃ (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (i : Fin 2) (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) := by
  classical
  haveI := 𝔛.isProper

  let xg : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X p (ΓM M H) hj :=
    y.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  have hxg : xg ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
    simp only [xg, Category.assoc]
    rw [pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, y.2, Category.id_comp]

  obtain ⟨s, ⟨hs₁, hs₂⟩, -⟩ :=
    AlgebraicGeometry.existsUnique_hom_comp_eq_specMap_and_specMap_comp_eq_of_isProper_of_valuationSubring (toBase p (ΓM M H) hj) A ρ xg hxg

  have hκ : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s) ≫ toBase p (ΓM M H) hj =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [Category.assoc, hs₁, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) :=
    pullback.lift (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s) (𝟙 _) hκ
  have huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s := pullback.lift_fst _ _ _
  have huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _

  haveI : IsClosedImmersion (uκ ≫ pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) := by
    rw [huκ₂]; infer_instance
  haveI : IsClosedImmersion uκ := IsClosedImmersion.of_comp uκ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
  let pt := uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))
  have hpt : IsClosed ({pt} : Set (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
    have h := uκ.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint (ResidueField ↥A)} (IsLocalRing.isClosed_singleton_closedPoint _)
    have himg : ((fun a => uκ.base a) '' {IsLocalRing.closedPoint (ResidueField ↥A)}) = {pt} := Set.image_singleton
    convert h using 1
    exact himg.symm

  obtain ⟨i, z, hz⟩ : ∃ (i : Fin 2) (z : fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), (𝔛.comp A hA ρ hρ i).base z = pt := by
    rcases 𝔛.comp_jointly_surjective A hA ρ hρ pt with ⟨z, hz⟩ | ⟨z, hz⟩
    · exact ⟨0, z, hz⟩
    · exact ⟨1, z, hz⟩
  have hzcl : IsClosed ({z} : Set (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
    haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ i
    have hinj := (𝔛.comp A hA ρ hρ i).isClosedEmbedding.injective
    have : ({z} : Set _) = (𝔛.comp A hA ρ hρ i).base ⁻¹' {pt} := by
      ext w; simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ hz, fun h => hinj (h.trans hz.symm)⟩
    rw [this]
    exact hpt.preimage (𝔛.comp A hA ρ hρ i).base.hom.continuous

  haveI := 𝔛.efib_iso A hA ρ hρ
  let P0 : (𝔛.Mfib A hA ρ hρ).C := (inv (𝔛.efib A hA ρ hρ)).base z
  have hP0 : (𝔛.efib A hA ρ hρ).base P0 = z := by
    show ((inv (𝔛.efib A hA ρ hρ)) ≫ 𝔛.efib A hA ρ hρ).base z = z
    rw [IsIso.inv_hom_id]; rfl
  have hP0cl : IsClosed ({P0} : Set (𝔛.Mfib A hA ρ hρ).C) := by
    have hinj : Function.Injective (𝔛.efib A hA ρ hρ).base := by
      intro a b hab
      have := congrArg (inv (𝔛.efib A hA ρ hρ)).base hab
      change ((𝔛.efib A hA ρ hρ) ≫ inv (𝔛.efib A hA ρ hρ)).base a = ((𝔛.efib A hA ρ hρ) ≫ inv (𝔛.efib A hA ρ hρ)).base b at this
      rwa [IsIso.hom_inv_id] at this
    have : ({P0} : Set _) = (𝔛.efib A hA ρ hρ).base ⁻¹' {z} := by
      ext w; simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ hP0, fun h => hinj (h.trans hP0.symm)⟩
    rw [this]
    exact hzcl.preimage (𝔛.efib A hA ρ hρ).base.hom.continuous
  refine ⟨⟨s, hs₁⟩, hs₂, uκ, huκ₁, huκ₂, i, ⟨P0, (mem_closedPoints_iff).mpr hP0cl⟩, ?_⟩
  show (𝔛.comp A hA ρ hρ i).base ((𝔛.efib A hA ρ hρ).base P0) = pt
  rw [hP0, hz]

end S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq (solution)
