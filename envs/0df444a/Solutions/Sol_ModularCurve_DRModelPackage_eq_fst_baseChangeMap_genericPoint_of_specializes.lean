-- Prove2me | solution 1 for ModularCurve.DRModelPackage.eq_fst_baseChangeMap_genericPoint_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c614d23f-49ca-5d75-9683-29184bde3a17

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_ModularCurve_DRModelPackage_eq_baseChangeMap_genericPoint_of_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_eq_fst_baseChangeMap_genericPoint_of_specializes
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_eq_fst_baseChangeMap_genericPoint_of_specializes.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "DRModel.baseChangeMap DRModel DRModel.toBase DRModelPackage DRModelPackage.eq_baseChangeMap_genericPoint_of_specializes"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "flat compZero ratModel compInf eq_baseChangeMap_genericPoint_of_specializes"
namespace FstMax
p2m_open "ModularCurve.DRModelPackage ModularCurve"

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})

include hϖ in

theorem charZero : CharZero O := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra h0
  have hp : (p : O) ≠ 0 := fun h => IsDiscreteValuationRing.not_a_field O (by rw [hϖ, h, Ideal.span_singleton_eq_bot.mpr rfl])

  obtain ⟨c, hc⟩ := CharP.exists O
  have hcn : c ∣ n := (CharP.cast_eq_zero_iff O c n).mp hn
  have hc0 : c ≠ 0 := fun h => h0 (Nat.eq_zero_of_zero_dvd (h ▸ hcn))
  haveI : Fact c.Prime := ⟨(CharP.char_is_prime_or_zero O c).resolve_right hc0⟩
  have hcp : c = p := by
    by_contra hne
    have hcop : Nat.Coprime c p := (Nat.coprime_primes (Fact.out) (Fact.out)).mpr hne

    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have := Nat.Coprime.isCoprime hcop
      obtain ⟨a, b, hab⟩ := this
      have hO : (a : O) * (c : O) + (b : O) * (p : O) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → O) hab
      rw [← hO, (CharP.cast_eq_zero O c), mul_zero, zero_add, hϖ]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  subst hcp
  exact hp (CharP.cast_eq_zero O c)

include hϖ in

theorem flat_fst : Flat (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := by
  haveI := charZero p O hϖ
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    show (algebraMap ℤ O).Flat
    rw [RingHom.Flat]
    convert (inferInstance : Module.Flat ℤ O)
    all_goals first | rfl | apply Subsingleton.elim
  infer_instance

end ModularCurve.DRModelPackage.FstMax

open ModularCurve.DRModelPackage.FstMax in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) :
    (∀ y : ↥(DRModel p), y ∉ (DRModel.toBase p) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : ℤ) : (Spec (CommRingCat.of ℤ)).Opens) →
      y ⤳ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base
        ((𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C)) →
      y = (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base
        ((𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C))) ∧
    (∀ y : ↥(DRModel p), y ∉ (DRModel.toBase p) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : ℤ) : (Spec (CommRingCat.of ℤ)).Opens) →
      y ⤳ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base
        ((𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C)) →
      y = (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base
        ((𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C))) := by
  haveI := flat_fst p O hϖ
  have hmax := ModularCurve.DRModelPackage.eq_baseChangeMap_genericPoint_of_specializes p 𝔛 O hϖ κ toκ

  have key : ∀ ξ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))),
      (∀ y', y' ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
          (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) → y' ⤳ ξ → y' = ξ) →
      ∀ y : ↥(DRModel p), y ∉ (DRModel.toBase p) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : ℤ) : (Spec (CommRingCat.of ℤ)).Opens) →
        y ⤳ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base ξ →
        y = (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base ξ := by
    intro ξ hm y hy hyξ
    obtain ⟨y', hy'ξ, rfl⟩ := Flat.generalizingMap
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) hyξ
    congr 1
    refine hm y' ?_ hy'ξ

    intro hy'
    apply hy
    have hsq : (DRModel.toBase p).base ((pullback.fst (DRModel.toBase p)
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base y') =
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))).base ((pullback.snd (DRModel.toBase p)
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base y') :=
      congr($(pullback.condition (f := DRModel.toBase p) (g := Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base y')
    change (DRModel.toBase p).base ((pullback.fst (DRModel.toBase p)
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base y') ∈ PrimeSpectrum.basicOpen ((p : ℕ) : ℤ)
    rw [hsq]
    change ((p : ℕ) : ℤ) ∉ (PrimeSpectrum.comap (algebraMap ℤ O) ((pullback.snd (DRModel.toBase p)
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base y')).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast]
    exact hy'
  exact ⟨key _ hmax.1, key _ hmax.2⟩

end S_ModularCurve_DRModelPackage_eq_fst_baseChangeMap_genericPoint_of_specializes
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_eq_fst_baseChangeMap_genericPoint_of_specializes (solution)
