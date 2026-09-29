-- Prove2me | solution 1 for ModularCurve.DRModelPackage.baseChangeMap_genericPoint_specializes_or
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b529b3c6-c246-588f-9a6f-5f43d68a4e61

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_or

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_or.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "DRModel.baseChangeMap DRModel DRModel.toBase DRModelPackage"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "comp_jointly_surjective flat compZero ratModel compInf"
namespace SpecialFibreMax
p2m_open "ModularCurve.DRModelPackage ModularCurve"

section Local
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] (toκ : O →+* κ)

include hϖ in

theorem toκ_maximalIdeal (a : O) (ha : a ∈ IsLocalRing.maximalIdeal O) : toκ a = 0 := by
  rw [hϖ, Ideal.mem_span_singleton] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

def ι : IsLocalRing.ResidueField O →+* κ :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) toκ (toκ_maximalIdeal p O hϖ κ toκ)

theorem ι_comp_residue : (ι p O hϖ κ toκ).comp (IsLocalRing.residue O) = toκ :=
  RingHom.ext fun _ => rfl

theorem baseChangeMap_eq_comp :
    DRModel.baseChangeMap (p := p) toκ =
      DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ) ≫ DRModel.baseChangeMap (IsLocalRing.residue O) := by
  apply pullback.hom_ext
  · simp only [DRModel.baseChangeMap, Category.assoc, pullback.lift_fst, Category.comp_id]
  · simp only [DRModel.baseChangeMap, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ι_comp_residue]

theorem isPullback_baseChangeMap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    IsPullback (DRModel.baseChangeMap (p := p) φ)
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ B))))
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))))
      (Spec.map (CommRingCat.ofHom φ)) := by
  have hρι : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ B)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show φ.comp (algebraMap ℤ A) = algebraMap ℤ B from RingHom.ext_int _ _]
  have h2 : DRModel.baseChangeMap (p := p) φ ≫ pullback.snd (DRModel.toBase p) _ =
      pullback.snd (DRModel.toBase p) _ ≫ Spec.map (CommRingCat.ofHom φ) := pullback.lift_snd _ _ _
  refine IsPullback.of_right ?_ h2
    (IsPullback.of_hasPullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))))
  have h1 : DRModel.baseChangeMap (p := p) φ ≫ pullback.fst (DRModel.toBase p) _ =
      pullback.fst (DRModel.toBase p) _ := by
    rw [DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]
  convert IsPullback.of_hasPullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ B))) using 1

theorem isClosedImmersion_baseChangeMap_residue :
    IsClosedImmersion (DRModel.baseChangeMap (p := p) (IsLocalRing.residue O)) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  exact MorphismProperty.of_isPullback (isPullback_baseChangeMap p (IsLocalRing.residue O)).flip inferInstance

include hϖ in

theorem exists_baseChangeMap_residue_eq
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hy : y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ∃ y₀, (DRModel.baseChangeMap (p := p) (IsLocalRing.residue O)).base y₀ = y := by

  set s := (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base y with hs
  have hps : ((p : ℕ) : O) ∈ s.asIdeal := by
    by_contra h
    exact hy h
  have hsm : s = IsLocalRing.closedPoint O := by
    apply PrimeSpectrum.ext
    have hle : IsLocalRing.maximalIdeal O ≤ s.asIdeal := by
      rw [hϖ, Ideal.span_singleton_le_iff_mem]
      exact hps
    exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le s.isPrime.ne_top hle).symm

  have hpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = s := by
    rw [hsm]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  obtain ⟨y₀, hy₀, -⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_baseChangeMap p (IsLocalRing.residue O)) y (IsLocalRing.closedPoint _) (by rw [hpt])
  exact ⟨y₀, hy₀⟩

theorem flat_baseChangeMap_ι :
    Flat (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)) := by
  haveI : Flat (Spec.map (CommRingCat.ofHom (ι p O hϖ κ toκ))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := (ι p O hϖ κ toκ).toAlgebra
    show RingHom.Flat (algebraMap (IsLocalRing.ResidueField O) κ)
    rw [RingHom.Flat]
    convert (inferInstance : Module.Flat (IsLocalRing.ResidueField O) κ)
  exact MorphismProperty.of_isPullback (isPullback_baseChangeMap p (ι p O hϖ κ toκ)).flip inferInstance

end Local

section Coverage
variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)

include hϖ in
omit [IsAlgClosed κ] in

theorem exists_baseChangeMap_eq
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hy : y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ∃ z, (DRModel.baseChangeMap (p := p) toκ).base z = y := by
  obtain ⟨y₀, rfl⟩ := exists_baseChangeMap_residue_eq p O hϖ y hy

  haveI : Surjective (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)) :=
    MorphismProperty.of_isPullback (isPullback_baseChangeMap p (ι p O hϖ κ toκ)).flip inferInstance
  obtain ⟨z, rfl⟩ := (Surjective.surj (f := DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ))) y₀
  refine ⟨z, ?_⟩
  rw [baseChangeMap_eq_comp p O hϖ κ toκ]
  rfl

include hϖ in

theorem specializes_or_specializes
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hy : y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳ y ∨
    (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳ y := by
  obtain ⟨z, rfl⟩ := exists_baseChangeMap_eq p O hϖ κ toκ y hy
  rcases 𝔛.comp_jointly_surjective κ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · left
    exact ((genericPoint_specializes c).map (𝔛.compInf κ).base.hom.continuous).map
      (DRModel.baseChangeMap toκ).base.hom.continuous
  · right
    exact ((genericPoint_specializes c).map (𝔛.compZero κ).base.hom.continuous).map
      (DRModel.baseChangeMap toκ).base.hom.continuous

end Coverage

end ModularCurve.DRModelPackage.SpecialFibreMax

open ModularCurve.DRModelPackage.SpecialFibreMax in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hy : y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳ y ∨
    (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳ y :=
  specializes_or_specializes p 𝔛 O hϖ κ toκ y hy

end S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_or
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_or (solution)
