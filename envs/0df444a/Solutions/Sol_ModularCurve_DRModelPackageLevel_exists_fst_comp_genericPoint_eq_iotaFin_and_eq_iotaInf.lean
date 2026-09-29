-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_fst_comp_genericPoint_eq_iotaFin_and_eq_iotaInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c0697aa2-fd17-5a50-9abb-5e4595767cdc

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_eq_spec_map_comp_iotaFin_of_comp_base_eq
import Theorems.Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import Theorems.Thm_ModularCurve_DRModelPackageLevel_range_cuspInf_inter_range_iotaFin_eq_empty_and_range_cuspZero_inter_range_iotaFin_eq_empty
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_fst_comp_genericPoint_eq_iotaFin_and_eq_iotaInf
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace GenChartsLevel

private theorem fst_crossing_mem_range_iotaFin
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
    (n : ↥(pullback (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1))) :
    (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base ((pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1) ≫ 𝔓.comp κ toκ 0).base n) ∈
      Set.range (IgusaScheme.ιFin (N₀ * q) q).base := by
  classical
  obtain ⟨⟨hcl, -⟩, -⟩ := 𝔓.node_pin κ toκ n
  obtain ⟨z, hz⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton κ
    (𝔓.Mfib κ toκ).toBase _ (mem_closedPoints_iff.mp hcl)
  have hinv : (𝔓.efib κ toκ).base ((inv (𝔓.efib κ toκ)).base
      ((pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)).base n)) =
      (pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)).base n := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have huκ : (pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1) ≫ 𝔓.comp κ toκ 0).base n =
      (z.left ≫ 𝔓.efib κ toκ ≫ 𝔓.comp κ toκ 0).base (IsLocalRing.closedPoint κ) := by
    simp only [Scheme.Hom.comp_apply]
    rw [← hinv, ← hz]
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨ψ, hψ⟩ := ModularCurve.DRModelPackageLevel.exists_eq_spec_map_comp_iotaFin_of_comp_base_eq N₀ q hqN 𝔓 κ
    toκ (RingHom.id κ)
    (fun c hc => by
      by_contra h
      exact ((IsLocalRing.mem_maximalIdeal c).mp hc) (isUnit_iff_ne_zero.mpr h))
    ((z.left ≫ 𝔓.efib κ toκ ≫ 𝔓.comp κ toκ 0) ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))))
    (z.left ≫ 𝔓.efib κ toκ ≫ 𝔓.comp κ toκ 0)
    (by rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]) n huκ
  refine ⟨(Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint κ), ?_⟩
  rw [huκ]
  exact ((Scheme.Hom.comp_apply _ _ _).symm.trans
    ((congrArg (fun g => g.base (IsLocalRing.closedPoint κ)) hψ).trans (Scheme.Hom.comp_apply _ _ _))).symm

end GenChartsLevel

set_option maxHeartbeats 3200000 in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
    [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)] :
    ∀ i : Fin 2,
      (∃ 𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q), (𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) =
        (IgusaScheme.ιFin (N₀ * q) q).base 𝔮) ∧
      (∃ 𝔯 : PrimeSpectrum ↥(IgusaScheme.chartAlgInf (N₀ * q) q), (𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) =
        (IgusaScheme.ιInf (N₀ * q) q).base 𝔯) := by
  classical

  have hgen : ∀ (i : Fin 2) (y : ↥(DRLevel.fibre (N₀ := N₀) toκ)), y ∈ Set.range (𝔓.comp κ toκ i).base →
      (𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) ⤳ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base y := by
    rintro i y ⟨t, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact ((genericPoint_specializes t).map (𝔓.comp κ toκ i).base.hom.continuous).map (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base.hom.continuous

  have hopenFin : IsOpen (Set.range (IgusaScheme.ιFin (N₀ * q) q).base) := (IgusaScheme.ιFin (N₀ * q) q).isOpenEmbedding.isOpen_range
  have hopenInf : IsOpen (Set.range (IgusaScheme.ιInf (N₀ * q) q).base) := (IgusaScheme.ιInf (N₀ * q) q).isOpenEmbedding.isOpen_range

  obtain ⟨P, hP⟩ := ModularCurve.ssPlaces_nonempty q N₀ hqN κ
  let n : ↥(pullback (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)) := (𝔓.nodeEquiv κ toκ).symm ⟨P, hP⟩
  have hyFin := GenChartsLevel.fst_crossing_mem_range_iotaFin N₀ q hqN 𝔓 κ toκ n
  have hy : ∀ i : Fin 2, (pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1) ≫ 𝔓.comp κ toκ 0).base n ∈ Set.range (𝔓.comp κ toκ i).base := by
    intro i
    fin_cases i
    · exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · refine ⟨(pullback.snd (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)).base n, ?_⟩
      show (𝔓.comp κ toκ 1).base _ = _
      rw [← Scheme.Hom.comp_apply, ← pullback.condition]

  obtain ⟨hcinf, hczero⟩ :=
    ModularCurve.DRModelPackageLevel.range_cuspInf_inter_range_iotaFin_eq_empty_and_range_cuspZero_inter_range_iotaFin_eq_empty N₀ q hqN 𝔓
  have hcusp : ∀ i : Fin 2, ∃ e : ↥(DRLevel.fibre (N₀ := N₀) toκ), e ∈ Set.range (𝔓.comp κ toκ i).base ∧
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base e ∈ Set.range (IgusaScheme.ιInf (N₀ * q) q).base := by
    intro i
    have key : ∀ (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of (DRLevel.R q)))) (DRLevel.toBase N₀ q)),
        Set.range ε.1.base ∩ Set.range (IgusaScheme.ιFin (N₀ * q) q).base = ∅ →
        Set.range (DRLevel.sectionFibre ε toκ).base ⊆ Set.range (𝔓.comp κ toκ i).base →
        ∃ e : ↥(DRLevel.fibre (N₀ := N₀) toκ), e ∈ Set.range (𝔓.comp κ toκ i).base ∧
          (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base e ∈ Set.range (IgusaScheme.ιInf (N₀ * q) q).base := by
      intro ε hε hsub
      refine ⟨(DRLevel.sectionFibre ε toκ).base (IsLocalRing.closedPoint κ), hsub ⟨_, rfl⟩, ?_⟩
      have hfst : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base ((DRLevel.sectionFibre ε toκ).base (IsLocalRing.closedPoint κ)) ∈ Set.range ε.1.base := by
        rw [← Scheme.Hom.comp_apply, DRLevel.sectionFibre_fst, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩
      rcases IgusaScheme.mem_range_ιFin_or_mem_range_ιInf (N₀ * q) q
          ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base ((DRLevel.sectionFibre ε toκ).base (IsLocalRing.closedPoint κ))) with h | h
      · exact absurd (Set.mem_inter hfst h) (by rw [hε]; exact Set.notMem_empty _)
      · exact h
    fin_cases i
    · exact key 𝔓.εinf hcinf (𝔓.εinf_mem_comp0 κ toκ)
    · exact key 𝔓.εzero hczero (𝔓.εzero_mem_comp1 κ toκ)
  intro i
  constructor
  · obtain ⟨𝔮, h𝔮⟩ := (hgen i _ (hy i)).mem_open hopenFin hyFin
    exact ⟨𝔮, h𝔮.symm⟩
  · obtain ⟨e, he, heInf⟩ := hcusp i
    obtain ⟨𝔯, h𝔯⟩ := (hgen i e he).mem_open hopenInf heInf
    exact ⟨𝔯, h𝔯.symm⟩

end S_ModularCurve_DRModelPackageLevel_exists_fst_comp_genericPoint_eq_iotaFin_and_eq_iotaInf
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_fst_comp_genericPoint_eq_iotaFin_and_eq_iotaInf (solution)
