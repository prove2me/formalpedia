-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.finite_and_injective_and_forall_exists_schemeHomOver_crossing_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9e869bff-4e2a-5c4a-aebb-126e0770dcbc

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Theorems.Thm_ModularCurve_XHDRModelAtP_finite_crossings
import Theorems.Thm_AlgebraicGeometry_eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_finite_and_injective_and_forall_exists_schemeHomOver_crossing_baseChange
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)] :
    ∀ (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    letI : Algebra (R p) (ResidueField ↥Pl) := ((IsLocalRing.residue ↥Pl).comp ρ).toAlgebra
    ∀ (hc : pullback.snd (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl)) =
        pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl))),
      Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥Pl))))
          (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl)))) ∧
      (Function.Injective fun j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥Pl))))
          (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl))) =>
        (j.1 ≫ pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1)).base (IsLocalRing.closedPoint (ResidueField ↥Pl))) ∧
      (∀ j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥Pl))))
          (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl))),
        (j.1 ≫ pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1)) ≫ (𝔛.comp Pl hPl ρ hρ 0) =
          (j.1 ≫ pullback.snd (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1)) ≫ (𝔛.comp Pl hPl ρ hρ 1)) ∧
      (∀ (q q' : ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))),
        (𝔛.comp Pl hPl ρ hρ 0).base q = (𝔛.comp Pl hPl ρ hρ 1).base q' →
          ∃ j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥Pl))))
              (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl))),
            q = (j.1 ≫ pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1)).base (IsLocalRing.closedPoint (ResidueField ↥Pl)) ∧
            q' = (j.1 ≫ pullback.snd (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1)).base (IsLocalRing.closedPoint (ResidueField ↥Pl))) := by
  intro ρ hρ
  letI : Algebra (R p) (ResidueField ↥Pl) := ((IsLocalRing.residue ↥Pl).comp ρ).toAlgebra
  intro hc
  classical

  haveI hfin : Finite ↥(pullback (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1)) := 𝔛.finite_crossings Pl hPl ρ hρ
  haveI : IsClosedImmersion (𝔛.comp Pl hPl ρ hρ 1) := 𝔛.comp_isClosedImmersion Pl hPl ρ hρ 1
  haveI : IsClosedImmersion (𝔛.comp Pl hPl ρ hρ 0) := 𝔛.comp_isClosedImmersion Pl hPl ρ hρ 0
  have hinjfst : Function.Injective (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1)).base :=
    (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1)).isClosedEmbedding.injective

  haveI := 𝔛.isProper0
  haveI hlt0 : LocallyOfFiniteType (toBase p (ΓN p M H hpM) hj) := IsProper.toLocallyOfFiniteType
  haveI hlt1 : LocallyOfFiniteType (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl)) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ hlt0
  haveI hlt2 : LocallyOfFiniteType (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1)) := inferInstance
  haveI hlt3 : LocallyOfFiniteType (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫
      (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl))) :=
    MorphismProperty.comp_mem _ _ _ hlt2 hlt1

  obtain ⟨hK1, hK2, hK3⟩ := AlgebraicGeometry.eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed
    (ResidueField ↥Pl) (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl)))
  have hinjpt : Function.Injective fun j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥Pl))))
      (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl))) =>
      j.1.base (IsLocalRing.closedPoint (ResidueField ↥Pl)) := by
    intro j j' hjj'
    exact Subtype.ext (hK1 j.1 j'.1 j.2 j'.2 hjj')
  refine ⟨Finite.of_injective _ hinjpt, ?_, ?_, ?_⟩
  · intro j j' hjj'
    apply hinjpt
    apply hinjfst
    exact hjj'
  · intro j
    rw [Category.assoc, Category.assoc, pullback.condition]
  · intro q q' hqq'
    obtain ⟨n, hn1, hn2⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback q q' hqq'
    obtain ⟨y, hy, hyn⟩ := hK2 n (hK3 hfin n)
    refine ⟨⟨y, hy⟩, ?_, ?_⟩
    · change q = (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1)).base (y.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      rw [hyn, hn1]
    · change q' = (pullback.snd (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1)).base (y.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      rw [hyn, hn2]

end S_ModularCurve_XHDRModelAtP_finite_and_injective_and_forall_exists_schemeHomOver_crossing_baseChange
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_finite_and_injective_and_forall_exists_schemeHomOver_crossing_baseChange (solution)
