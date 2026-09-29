-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_algHom_modularFunctionFieldFullC_of_ringHom_admissible_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/4c9b4da2-20a8-5ee7-9901-d47aea0766af

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_ModularCurve_FullLevel_sum_algebraMap_mul_apply_eq_zero_of_sum_smul_residue_eq_zero_of_prime
import Theorems.Thm_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_sum_smul_eq_zero_of_algebra
import Theorems.Thm_ModularCurve_FullLevel_isIntegral_adjoin_residue_jq_residue_of_mem_admissible_of_prime
import Theorems.Thm_ModularCurve_FullLevel_mem_integers_and_cuspRegular_qExpand_jq_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_algHom_modularFunctionFieldFullC_of_ringHom_admissible_of_prime
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 12800000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups IntermediateField.algebraAdjoinAdjoin

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)

    (𝒜 : Subring (LaurentSeries ℚ))
    (h𝒜 : ∀ gf : LaurentSeries ℚ, gf ∈ 𝒜 ↔
      ∃ (hgf : gf ∈ modularFunctionFieldFull M')
        (_ : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M')))
    (hj𝒜 : jq ∈ 𝒜)
    (Ω : Type) [Field Ω] [Algebra (ResidueField A) Ω] (val : ↥𝒜 →+* Ω)
    (hval0 : ∀ (gf : LaurentSeries ℚ) (h : gf ∈ 𝒜) (hgf : gf ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0 → val ⟨gf, h⟩ = 0)
    (hvalj : Transcendental (ResidueField A) (val ⟨jq, hj𝒜⟩)) :
    ∃ emb : ↥(modularFunctionFieldFullC (ResidueField A) M') →ₐ[ResidueField A] Ω,
      ∀ (gf : LaurentSeries ℚ) (h : gf ∈ 𝒜) (hgf : gf ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        emb (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField A) M') (R₀.residue ⟨_, hgi⟩)) = val ⟨gf, h⟩ := by
  classical

  have hadm : ∀ gf : ↥𝒜, ∃ (hgf : (gf : LaurentSeries ℚ) ∈ modularFunctionFieldFull M')
      (_ : (⟨coeffEmb (AlgebraicClosure ℚ) (gf : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (gf : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) :=
    fun gf => (h𝒜 gf).mp gf.2
  let ebar : ↥𝒜 → ↥R₀.integers := fun gf =>
    ⟨⟨coeffEmb (AlgebraicClosure ℚ) (gf : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hadm gf).1⟩, (hadm gf).2.1⟩
  let r : ↥𝒜 → ↥(modularFunctionFieldC (ResidueField A) M') := fun gf => R₀.residue (ebar gf)
  have r_mul : ∀ a b : ↥𝒜, r (a * b) = r a * r b := fun a b => by
    show R₀.residue (ebar (a * b)) = R₀.residue (ebar a) * R₀.residue (ebar b)
    rw [← map_mul]; congr 1
    exact Subtype.ext (Subtype.ext (map_mul (coeffEmb (AlgebraicClosure ℚ)) (a : LaurentSeries ℚ) b))
  have r_one : r 1 = 1 := by
    show R₀.residue (ebar 1) = 1
    rw [← (R₀.residue).map_one]; congr 1
    exact Subtype.ext (Subtype.ext (map_one (coeffEmb (AlgebraicClosure ℚ))))

  have hcons : ∀ (n : ℕ) (idx : Fin n → ↥𝒜) (c : Fin n → ResidueField A),
      ∑ l, c l • r (idx l) = 0 → ∑ l, c l • val (idx l) = 0 := by
    intro n idx c hrel
    have h := ModularCurve.FullLevel.sum_algebraMap_mul_apply_eq_zero_of_sum_smul_residue_eq_zero_of_prime q M' hqM' A hA R₀ hR₀ 𝒜 h𝒜 hj𝒜 Ω val hval0 hvalj n (fun l => (idx l : LaurentSeries ℚ)) (fun l => (idx l).2) (fun l => (hadm (idx l)).1)
      (fun l => (hadm (idx l)).2.1) c hrel
    simpa only [Algebra.smul_def] using h
  obtain ⟨χ, hχ⟩ := Algebra.exists_algHom_adjoin_range_apply_eq_of_forall_sum_smul_eq_zero_of_algebra (K := ResidueField A) (L := Ω) r (fun gf => val gf)
    ⟨1, r_one, map_one val⟩ (fun a b => ⟨a * b, r_mul a b, map_mul val a b⟩) hcons

  have hχinj : Function.Injective χ := by

    have hjmem : r ⟨jq, hj𝒜⟩ ∈ Algebra.adjoin (ResidueField A) (Set.range r) := Algebra.subset_adjoin (Set.mem_range_self _)
    have hBS : (Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) ≤ Algebra.adjoin (ResidueField A) (Set.range r) := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]; exact hjmem
    letI algBS : Algebra ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) ↥(Algebra.adjoin (ResidueField A) (Set.range r)) := (Subalgebra.inclusion hBS).toAlgebra
    haveI hstBSF : IsScalarTower ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) ↥(Algebra.adjoin (ResidueField A) (Set.range r)) ↥(modularFunctionFieldC (ResidueField A) M') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hgen : ∀ i : ↥𝒜, IsIntegral ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) (r i) := fun i =>
      ModularCurve.FullLevel.isIntegral_adjoin_residue_jq_residue_of_mem_admissible_of_prime q M' hqM' A hA R₀ hR₀ 𝒜 h𝒜 hj𝒜
        (i : LaurentSeries ℚ) (hadm i).1 (hadm i).2.1 i.2 (hadm ⟨jq, hj𝒜⟩).2.1
    haveI hintS : Algebra.IsIntegral ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) ↥(Algebra.adjoin (ResidueField A) (Set.range r)) := by
      refine ⟨fun s => ?_⟩
      have hsub : (s : ↥(modularFunctionFieldC (ResidueField A) M')) ∈ Algebra.adjoin ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) (Set.range r) := by
        have hle : Algebra.adjoin (ResidueField A) (Set.range r) ≤ (Algebra.adjoin ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) (Set.range r)).restrictScalars (ResidueField A) :=
          Algebra.adjoin_le Algebra.subset_adjoin
        exact hle s.2
      haveI hintT : Algebra.IsIntegral ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) ↥(Algebra.adjoin ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) (Set.range r)) :=
        Algebra.IsIntegral.adjoin (by rintro _ ⟨i, rfl⟩; exact hgen i)
      have h1 : IsIntegral ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) ((⟨(s : ↥(modularFunctionFieldC (ResidueField A) M')), hsub⟩ : ↥(Algebra.adjoin ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) (Set.range r)))) := hintT.isIntegral _
      have h2 : IsIntegral ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) (s : ↥(modularFunctionFieldC (ResidueField A) M')) := h1.map (Algebra.adjoin ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) (Set.range r)).val
      have h2' : IsIntegral ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) ((IsScalarTower.toAlgHom ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) ↥(Algebra.adjoin (ResidueField A) (Set.range r)) ↥(modularFunctionFieldC (ResidueField A) M')) s) := h2
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) ↥(Algebra.adjoin (ResidueField A) (Set.range r)) ↥(modularFunctionFieldC (ResidueField A) M')) (fun x y h => Subtype.ext h)).mp h2'
    have hcomap : Ideal.comap (algebraMap ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) ↥(Algebra.adjoin (ResidueField A) (Set.range r))) (RingHom.ker χ.toRingHom) = ⊥ := by
      rw [eq_bot_iff]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker] at hb
      rw [Ideal.mem_bot]
      obtain ⟨p, hp⟩ : ∃ p : Polynomial (ResidueField A), Polynomial.aeval (r ⟨jq, hj𝒜⟩) p = (b : ↥(modularFunctionFieldC (ResidueField A) M')) := by
        have hb2 : (b : ↥(modularFunctionFieldC (ResidueField A) M')) ∈ (Polynomial.aeval (r ⟨jq, hj𝒜⟩) : Polynomial (ResidueField A) →ₐ[ResidueField A] ↥(modularFunctionFieldC (ResidueField A) M')).range :=
          (Algebra.adjoin_singleton_eq_range_aeval (ResidueField A) (r ⟨jq, hj𝒜⟩)).le b.2
        exact (AlgHom.mem_range _).mp hb2
      have hbS : algebraMap ↥(Algebra.adjoin (ResidueField A) ({r ⟨jq, hj𝒜⟩} : Set ↥(modularFunctionFieldC (ResidueField A) M'))) ↥(Algebra.adjoin (ResidueField A) (Set.range r)) b = Polynomial.aeval (⟨r ⟨jq, hj𝒜⟩, hjmem⟩ : ↥(Algebra.adjoin (ResidueField A) (Set.range r))) p := by
        apply Subtype.ext
        change (b : ↥(modularFunctionFieldC (ResidueField A) M')) = (Algebra.adjoin (ResidueField A) (Set.range r)).val (Polynomial.aeval (⟨r ⟨jq, hj𝒜⟩, hjmem⟩ : ↥(Algebra.adjoin (ResidueField A) (Set.range r))) p)
        rw [← Polynomial.aeval_algHom_apply, ← hp]
        rfl
      have hb' : Polynomial.aeval (val ⟨jq, hj𝒜⟩) p = 0 := by
        rw [← hχ ⟨jq, hj𝒜⟩, Polynomial.aeval_algHom_apply, ← hbS]; exact hb
      have hp0 : p = 0 := by
        by_contra hne; exact hvalj ⟨p, hne, hb'⟩
      apply Subtype.ext
      change (b : ↥(modularFunctionFieldC (ResidueField A) M')) = 0
      rw [← hp, hp0, map_zero]
    rw [← AlgHom.coe_toRingHom, RingHom.injective_iff_ker_eq_bot]
    exact Ideal.eq_bot_of_comap_eq_bot hcomap

  have hext : ∃ emb : ↥(modularFunctionFieldFullC (ResidueField A) M') →ₐ[ResidueField A] Ω,
      ∀ gf : ↥𝒜, emb (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField A) M') (r gf)) = val gf := by

    have RI : ∀ (d : ℕ) [NeZero d], d ∣ M' → ∃ h𝒜d : ModularCurve.qExpand ℚ d jq ∈ 𝒜,
        ((r ⟨ModularCurve.qExpand ℚ d jq, h𝒜d⟩ : ↥(modularFunctionFieldC (ResidueField A) M')) : (LaurentSeries (ResidueField A))) = ModularCurve.qExpand (ResidueField A) d (jqModC (ResidueField A)) := by
      intro d _ hd
      obtain ⟨hgi, hcusp⟩ := ModularCurve.FullLevel.mem_integers_and_cuspRegular_qExpand_jq_of_dvd M' A R₀ hR₀ d hd
      have h𝒜d : ModularCurve.qExpand ℚ d jq ∈ 𝒜 := (h𝒜 _).mpr ⟨ModularCurve.jqd_mem_full M' hd, hgi, hcusp⟩
      refine ⟨h𝒜d, ?_⟩

      have hyeq : coeffMap A.subtype (ModularCurve.qExpand ↥A d (jqModC ↥A)) = coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d jq) := by
        rw [ModularCurve.coeffMap_qExpand]
        change ModularCurve.qExpand (AlgebraicClosure ℚ) d ((jqModC ↥A).map A.subtype) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (ModularCurve.qExpand ℚ d (jqModC ℚ))
        rw [ModularCurve.map_jqModC, ModularCurve.coeffMap_qExpand]
        change _ = ModularCurve.qExpand (AlgebraicClosure ℚ) d ((jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)))
        rw [ModularCurve.map_jqModC]
      have hy : coeffMap A.subtype (ModularCurve.qExpand ↥A d (jqModC ↥A)) ∈ modularFunctionFieldBar M' := by
        rw [hyeq]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.jqd_mem_full M' hd)
      obtain ⟨hint, hres⟩ := hR₀ _ hy
      have hres' : ((R₀.residue ⟨_, hint⟩ : ↥(modularFunctionFieldC (ResidueField A) M')) : (LaurentSeries (ResidueField A))) = ModularCurve.qExpand (ResidueField A) d (jqModC (ResidueField A)) := by
        rw [hres, ModularCurve.coeffMap_qExpand]
        change ModularCurve.qExpand (ResidueField A) d ((jqModC ↥A).map (IsLocalRing.residue ↥A)) = _
        rw [ModularCurve.map_jqModC]
      have hearg : ebar ⟨ModularCurve.qExpand ℚ d jq, h𝒜d⟩ = ⟨⟨coeffMap A.subtype (ModularCurve.qExpand ↥A d (jqModC ↥A)), hy⟩, hint⟩ :=
        Subtype.ext (Subtype.ext hyeq.symm)
      show ((R₀.residue (ebar ⟨ModularCurve.qExpand ℚ d jq, h𝒜d⟩) : ↥(modularFunctionFieldC (ResidueField A) M')) : (LaurentSeries (ResidueField A))) = _
      rw [hearg]; exact hres'

    have hFullle : modularFunctionFieldFullC (ResidueField A) M' ≤ modularFunctionFieldC (ResidueField A) M' := by
      rw [modularFunctionFieldFullC, IntermediateField.adjoin_le_iff]
      rintro x ⟨d, hd0, hd, rfl⟩
      haveI := hd0
      obtain ⟨h𝒜d, hRI⟩ := RI d hd
      rw [← hRI]; exact (r _).2

    have hT : IntermediateField.adjoin (ResidueField A) (Set.range r) = (⊤ : IntermediateField (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) := by
      obtain ⟨h1, hR1⟩ := RI 1 (one_dvd M')
      obtain ⟨hM, hRM⟩ := RI M' dvd_rfl
      have hle : modularFunctionFieldC (ResidueField A) M' ≤ IntermediateField.lift (IntermediateField.adjoin (ResidueField A) (Set.range r)) := by
        rw [IntermediateField.lift_adjoin]
        change IntermediateField.adjoin (ResidueField A) {jqModC (ResidueField A), jqNModC (ResidueField A) M'} ≤ _
        apply IntermediateField.adjoin.mono
        rintro x (rfl | rfl)
        · refine ⟨r ⟨ModularCurve.qExpand ℚ 1 jq, h1⟩, ⟨_, rfl⟩, ?_⟩
          rw [hR1, ModularCurve.qExpand_one_apply]
        · exact ⟨r ⟨ModularCurve.qExpand ℚ M' jq, hM⟩, ⟨_, rfl⟩, hRM⟩
      rw [eq_top_iff]
      intro x _
      exact (IntermediateField.mem_lift x).mp (hle x.2)

    let ψ : ↥(IntermediateField.adjoin (ResidueField A) (Set.range r)) →ₐ[(ResidueField A)] Ω := IsFractionRing.liftAlgHom hχinj
    let ι₂ : ↥(modularFunctionFieldC (ResidueField A) M') →ₐ[(ResidueField A)] ↥(IntermediateField.adjoin (ResidueField A) (Set.range r)) :=
      ((IntermediateField.equivOfEq hT.symm).toAlgHom).comp (IntermediateField.topEquiv.symm.toAlgHom)
    refine ⟨(ψ.comp ι₂).comp (IntermediateField.inclusion hFullle), fun gf => ?_⟩
    have e2 : ι₂ ((IntermediateField.inclusion hFullle) (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField A) M') (r gf))) =
        algebraMap ↥(Algebra.adjoin (ResidueField A) (Set.range r)) ↥(IntermediateField.adjoin (ResidueField A) (Set.range r)) ⟨r gf, Algebra.subset_adjoin (Set.mem_range_self gf)⟩ :=
      Subtype.ext rfl
    change ψ (ι₂ ((IntermediateField.inclusion hFullle) (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField A) M') (r gf)))) = val gf
    refine (congrArg ψ e2).trans ?_
    change IsFractionRing.lift hχinj (algebraMap ↥(Algebra.adjoin (ResidueField A) (Set.range r)) ↥(IntermediateField.adjoin (ResidueField A) (Set.range r)) ⟨r gf, Algebra.subset_adjoin (Set.mem_range_self gf)⟩) = val gf
    rw [IsFractionRing.lift_algebraMap]
    exact hχ gf

  obtain ⟨emb, hemb⟩ := hext
  refine ⟨emb, fun gf h hgf hgi => ?_⟩
  have : (R₀.residue ⟨_, hgi⟩ : ↥(modularFunctionFieldC (ResidueField A) M')) = r ⟨gf, h⟩ := rfl
  rw [this]
  exact hemb ⟨gf, h⟩

end S_ModularCurve_FullLevel_exists_algHom_modularFunctionFieldFullC_of_ringHom_admissible_of_prime
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_algHom_modularFunctionFieldFullC_of_ringHom_admissible_of_prime (solution)
