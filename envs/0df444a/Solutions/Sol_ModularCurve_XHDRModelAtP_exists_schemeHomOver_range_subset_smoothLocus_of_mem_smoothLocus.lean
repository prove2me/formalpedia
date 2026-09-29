-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/88c39120-7c0c-5556-aa78-aef7b9e4d4ae

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel

open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (i : Fin 2) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) :
    ∃ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
      Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) ∧
      ∃ uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1 ∧
        uκ ≫ pullback.snd _ _ = 𝟙 _ ∧
        (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) := by

  haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
  have hsmU : Smooth (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) :=
    SmoothOfRelativeDimension.smooth 1 _
  haveI : Smooth (pullback.snd (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) :=
    MorphismProperty.pullback_snd _ _ hsmU

  have hπκ : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hbar : Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρ) =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]

  have hsP : ∃ sP : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔛.Mfib A hA ρ hρ).C,
      sP ≫ (𝔛.Mfib A hA ρ hρ).toBase = 𝟙 _ ∧ sP.base (IsLocalRing.closedPoint (ResidueField ↥A)) = P.1 :=
    ⟨pointOfClosedPoint (𝔛.Mfib A hA ρ hρ).toBase P.1 P.2, pointOfClosedPoint_comp _ _ _,
      pointOfClosedPoint_apply _ _ _ _⟩
  obtain ⟨sP, hsP₁, hsP₂⟩ := hsP

  obtain ⟨uκ, huκ⟩ : ∃ uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶
      fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
      uκ = sP ≫ 𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i := ⟨_, rfl⟩
  have huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _ := by
    rw [huκ, Category.assoc, Category.assoc, 𝔛.comp_over A hA ρ hρ i, 𝔛.hefib A hA ρ hρ, hsP₁]
  have hPu : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 =
      uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) := by
    simp only [huκ, Scheme.Hom.comp_apply, hsP₂]

  obtain ⟨xκ, hxκ⟩ : ∃ xκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ X p (ΓM M H) hj,
      xκ = uκ ≫ pullback.fst _ _ := ⟨_, rfl⟩
  have hxκT : xκ ≫ toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [hxκ, Category.assoc, pullback.condition, ← Category.assoc, huκ₂, Category.id_comp, hπκ]
  have hrange : Set.range xκ.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint (ResidueField ↥A)), hxκ, Scheme.Hom.comp_apply, ← hPu]
    exact hP

  obtain ⟨a, ha⟩ : ∃ a : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ 𝔛.smoothLocus, a ≫ 𝔛.smoothLocus.ι = xκ :=
    ⟨IsOpenImmersion.lift 𝔛.smoothLocus.ι xκ (by rwa [Scheme.Opens.range_ι]), IsOpenImmersion.lift_fac _ _ _⟩
  have hax : a ≫ (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [← Category.assoc, ha, hxκT]
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶
      pullback (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)),
      x₀ = pullback.lift a (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) hax := ⟨_, rfl⟩
  have hx₀snd : x₀ ≫ pullback.snd (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥A (ResidueField ↥A))) := by
    rw [hx₀, pullback.lift_snd]
    rfl
  have hH := AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
    (pullback.snd (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) x₀ hx₀snd
  obtain ⟨s, hs₁, hs₂⟩ := hH

  have huT : (s ≫ pullback.fst _ _ ≫ 𝔛.smoothLocus.ι) ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom ρ) := by
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc, hs₁, Category.id_comp]
  have hyT : (Spec.map (CommRingCat.ofHom A.subtype) ≫ s ≫ pullback.fst _ _ ≫ 𝔛.smoothLocus.ι) ≫ toBase p (ΓM M H) hj =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    rw [Category.id_comp, Category.assoc, huT, hbar]
  refine ⟨⟨pullback.lift _ _ hyT ≫ inv 𝔛.eeta, ?_⟩, ⟨s ≫ pullback.fst _ _ ≫ 𝔛.smoothLocus.ι, huT⟩, ?_, ?_, uκ, ?_, huκ₂, hPu⟩
  ·
    rw [← 𝔛.heeta, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_snd]
  ·
    show Spec.map (CommRingCat.ofHom A.subtype) ≫ s ≫ pullback.fst _ _ ≫ 𝔛.smoothLocus.ι =
      (pullback.lift _ _ hyT ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ pullback.fst _ _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  ·
    rintro _ ⟨z, rfl⟩
    show (s ≫ pullback.fst _ _ ≫ 𝔛.smoothLocus.ι).base z ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))
    rw [← Scheme.Opens.range_ι 𝔛.smoothLocus, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  ·
    show uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s ≫ pullback.fst _ _ ≫ 𝔛.smoothLocus.ι
    rw [← hxκ, ← ha]
    have h1 : a = x₀ ≫ pullback.fst _ _ := by rw [hx₀, pullback.lift_fst]
    have h2 : x₀ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s := hs₂.symm
    rw [h1, h2, Category.assoc, Category.assoc]

#print axioms solution

end S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus (solution)
