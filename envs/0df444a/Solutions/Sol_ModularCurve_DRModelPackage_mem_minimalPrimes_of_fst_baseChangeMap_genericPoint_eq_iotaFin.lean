-- Prove2me | solution 1 for ModularCurve.DRModelPackage.mem_minimalPrimes_of_fst_baseChangeMap_genericPoint_eq_iotaFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/fa360e68-2bd3-565b-b6b0-4006ccc01849

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_ModularCurve_DRModelPackage_eq_fst_baseChangeMap_genericPoint_of_specializes
import Theorems.Thm_ModularCurve_DRModel_baseChangeMap_apply_notMem_preimage_basicOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_mem_minimalPrimes_of_fst_baseChangeMap_genericPoint_eq_iotaFin
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    (∀ P : PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base
          ((𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C)) =
        (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).base P →
      P.asIdeal ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p)
        (IgusaScheme.jFull p)))}).minimalPrimes) ∧
    (∀ P : PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base
          ((𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C)) =
        (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).base P →
      P.asIdeal ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p)
        (IgusaScheme.jFull p)))}).minimalPrimes) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hmax := ModularCurve.DRModelPackage.eq_fst_baseChangeMap_genericPoint_of_specializes p 𝔛 O hϖ κ toκ
  set A := ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) with hA
  set ιF := TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) with hιF
  set fst := pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) with hfst

  have hfib : ∀ Q : PrimeSpectrum A, ((p : ℕ) : A) ∈ Q.asIdeal ↔
      ιF.base Q ∉ (DRModel.toBase p) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : ℤ) : (Spec (CommRingCat.of ℤ)).Opens) := by
    intro Q
    have hsq : (DRModel.toBase p).base (ιF.base Q) = (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))).base Q :=
      congr($(TwoChartIntegralModel.ιFin_toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).base Q)
    change _ ↔ ¬ ((DRModel.toBase p).base (ιF.base Q) ∈ PrimeSpectrum.basicOpen ((p : ℕ) : ℤ))
    rw [hsq]
    change _ ↔ ¬ (((p : ℕ) : ℤ) ∉ Ideal.comap (algebraMap ℤ A) Q.asIdeal)
    rw [not_not, Ideal.mem_comap, map_natCast]

  have key : ∀ ξ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))),
      ξ ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
          (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
      (∀ y : ↥(DRModel p), y ∉ (DRModel.toBase p) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : ℤ) : (Spec (CommRingCat.of ℤ)).Opens) →
        y ⤳ fst.base ξ → y = fst.base ξ) →
      ∀ P : PrimeSpectrum A, fst.base ξ = ιF.base P → P.asIdeal ∈ (Ideal.span {((p : ℕ) : A)}).minimalPrimes := by
    intro ξ hξ hm P hP

    have hpP : ((p : ℕ) : A) ∈ P.asIdeal := by
      rw [hfib, ← hP]
      intro h
      apply hξ
      have hsq : (DRModel.toBase p).base (fst.base ξ) = (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))).base
          ((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base ξ) :=
        congr($(pullback.condition (f := DRModel.toBase p) (g := Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base ξ)
      have h' : (DRModel.toBase p).base (fst.base ξ) ∈ PrimeSpectrum.basicOpen ((p : ℕ) : ℤ) := h
      rw [hsq] at h'
      change ((p : ℕ) : ℤ) ∉ Ideal.comap (algebraMap ℤ O) ((pullback.snd (DRModel.toBase p)
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base ξ).asIdeal at h'
      rw [Ideal.mem_comap, map_natCast] at h'
      exact h'
    refine ⟨⟨P.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hpP⟩, ?_⟩
    rintro Q ⟨hQ, hpQ⟩ hQP

    let Q' : PrimeSpectrum A := ⟨Q, hQ⟩
    have hsp : ιF.base Q' ⤳ fst.base ξ := by
      rw [hP]
      exact ((PrimeSpectrum.le_iff_specializes Q' P).mp hQP).map ιF.base.hom.continuous
    have hQfib : ιF.base Q' ∉ (DRModel.toBase p) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((p : ℕ) : ℤ) : (Spec (CommRingCat.of ℤ)).Opens) :=
      (hfib Q').mp ((Ideal.span_singleton_le_iff_mem _).mp hpQ)
    have heq := hm _ hQfib hsp
    rw [hP] at heq
    have hQP' : Q' = P := ιF.isOpenEmbedding.injective heq
    exact le_of_eq (congrArg PrimeSpectrum.asIdeal hQP').symm
  exact ⟨key _ (ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O κ toκ _) hmax.1,
    key _ (ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O κ toκ _) hmax.2⟩

end S_ModularCurve_DRModelPackage_mem_minimalPrimes_of_fst_baseChangeMap_genericPoint_eq_iotaFin
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_mem_minimalPrimes_of_fst_baseChangeMap_genericPoint_eq_iotaFin (solution)
