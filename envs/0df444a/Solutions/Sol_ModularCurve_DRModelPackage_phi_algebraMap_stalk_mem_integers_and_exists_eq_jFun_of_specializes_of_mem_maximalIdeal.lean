-- Prove2me | solution 1 for ModularCurve.DRModelPackage.phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1699b744-e732-5f19-a75c-480f76fafc20

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
import Theorems.Thm_AlgebraicGeometry_Smooth_maximalIdeal_stalk_eq_span_of_forall_specializes
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_subfieldClosure_range_germToFunctionField_union_range_eq_top
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_eq_comap_integers_or_of_forall_exists_eq_pow_mul
import Theorems.Thm_ModularCurve_DRModelPackage_polynomialEval_mem_range_algebraMap_stalk_and_inv_mem_of_map_ne_zero
import Theorems.Thm_ModularCurve_DRModel_baseChangeMap_apply_notMem_preimage_basicOpen
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_mem_preimage_smoothLocus
import Theorems.Thm_ModularCurve_DRModelPackage_eq_baseChangeMap_genericPoint_of_specializes
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgFin_valuationSubring_pair_levelP
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace ResMatchDock

section ValSub

variable (D K : Type*) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [Field K] [Algebra D K] [IsFractionRing D K]

noncomputable def valSub : ValuationSubring K :=
  { (algebraMap D K).range with
    mem_or_inv_mem' := fun x => by
      rcases ValuationRing.isInteger_or_isInteger D x with h | h
      · exact Or.inl h
      · exact Or.inr h }

theorem mem_valSub_iff (x : K) : x ∈ valSub D K ↔ x ∈ Set.range (algebraMap D K) := by
  show x ∈ (algebraMap D K).range ↔ _
  rw [RingHom.mem_range, Set.mem_range]

theorem coe_valSub : ((valSub D K : ValuationSubring K) : Set K) = Set.range (algebraMap D K) :=
  Set.ext (mem_valSub_iff D K)

theorem algebraMap_mem_valSub (d : D) : algebraMap D K d ∈ valSub D K := (mem_valSub_iff D K _).mpr ⟨d, rfl⟩

variable {D} in

theorem algebraMap_mem_nonunits_of_mem_maximalIdeal {ϖ : D} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal D) :
    algebraMap D K ϖ ∈ (valSub D K).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases h0 : ϖ = 0
  · left; rw [h0, map_zero]
  right
  intro hinv
  obtain ⟨d, hd⟩ := (mem_valSub_iff D K _).mp hinv
  have hne : algebraMap D K ϖ ≠ 0 := fun h => h0 ((IsFractionRing.injective D K) (by rw [h, map_zero]))
  apply (IsLocalRing.mem_maximalIdeal _).mp hϖ
  refine isUnit_iff_exists_inv.mpr ⟨d, IsFractionRing.injective D K ?_⟩
  rw [map_mul, hd, map_one, mul_inv_cancel₀ hne]

variable {D} in

theorem exists_eq_pow_mul_of_maximalIdeal_eq {ϖ : D} (hϖ : IsLocalRing.maximalIdeal D = Ideal.span {ϖ})
    (g : K) (hg : g ∈ valSub D K) (hg0 : g ≠ 0) :
    ∃ n : ℕ, ∃ u ∈ valSub D K, u⁻¹ ∈ valSub D K ∧ g = (algebraMap D K ϖ) ^ n * u := by
  obtain ⟨d, rfl⟩ := (mem_valSub_iff D K _).mp hg
  have hd0 : d ≠ 0 := fun h => hg0 (by rw [h, map_zero])
  have hirr : Irreducible ϖ := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ
    (fun h => IsDiscreteValuationRing.not_a_field D (by rw [hϖ, h, Ideal.span_singleton_eq_bot.mpr rfl])) hϖ
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hirr
  refine ⟨n, algebraMap D K (v : D), algebraMap_mem_valSub D K _, ?_, ?_⟩
  · have : (algebraMap D K (v : D))⁻¹ = algebraMap D K ((v⁻¹ : Dˣ) : D) := by
      rw [inv_eq_of_mul_eq_one_right]
      rw [← map_mul, Units.mul_inv, map_one]
    rw [this]; exact algebraMap_mem_valSub D K _
  · rw [map_mul, map_pow, mul_comm]

end ValSub

end ResMatchDock

open ModularCurve AlgebraicCurve

namespace ResMatchDock

abbrev lau (p : ℕ) [NeZero p] (x : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : LaurentSeries ℚ := ((x : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ)

theorem lau_mul (p : ℕ) [NeZero p] (x y : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : lau p (x * y) = lau p x * lau p y := rfl
theorem lau_add (p : ℕ) [NeZero p] (x y : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : lau p (x + y) = lau p x + lau p y := rfl
theorem lau_neg (p : ℕ) [NeZero p] (x : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : lau p (-x) = -lau p x := rfl
theorem lau_one (p : ℕ) [NeZero p] : lau p (1 : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = 1 := rfl
theorem lau_zero (p : ℕ) [NeZero p] : lau p (0 : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = 0 := rfl
theorem lau_intCast (p : ℕ) [NeZero p] (n : ℤ) : lau p (algebraMap ℤ ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) n) = algebraMap ℚ (LaurentSeries ℚ) (n : ℚ) := by
  show (((algebraMap ℤ ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) n : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = _
  rw [Subalgebra.coe_algebraMap]
  simp

theorem exists_div_of_mem_chartAlgFin (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq) (z : ↥(modularFunctionFieldFull p)) :
    ∃ x y : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), (y : ↥(modularFunctionFieldFull p)) ≠ 0 ∧ z = (x : ↥(modularFunctionFieldFull p)) / (y : ↥(modularFunctionFieldFull p)) := by
  classical
  let S : Set (LaurentSeries ℚ) := Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions p
  have hz : (z : LaurentSeries ℚ) ∈ Subfield.closure S := by
    have h2 : (z : LaurentSeries ℚ) ∈ (modularFunctionFieldFull p).toSubfield := z.2
    rwa [show (modularFunctionFieldFull p).toSubfield = Subfield.closure S from IntermediateField.adjoin_toSubfield _ _] at h2
  have key : ∀ w ∈ Subfield.closure S, ∃ x y : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), lau p y ≠ 0 ∧ w * lau p y = lau p x := by
    intro w hw
    induction hw using Subfield.closure_induction with
    | mem w hw =>
      rcases hw with ⟨c, rfl⟩ | ⟨d, hd, hdp, rfl⟩
      · refine ⟨algebraMap ℤ ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) c.num, algebraMap ℤ ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (c.den : ℤ), ?_, ?_⟩
        · rw [lau_intCast]
          intro h0
          rw [map_eq_zero] at h0
          exact c.den_nz (by exact_mod_cast h0)
        · rw [lau_intCast, lau_intCast, ← map_mul]
          congr 1
          push_cast
          exact Rat.mul_den_eq_num c
      · haveI := hd
        rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdp with h1 | h2
        · subst h1
          refine ⟨TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p), 1, by rw [lau_one]; exact one_ne_zero, ?_⟩
          rw [lau_one, mul_one, qExpand_one_apply]
          rfl
        · exact ⟨jp, 1, by rw [lau_one]; exact one_ne_zero, by rw [lau_one, mul_one, qExpand_congr h2, ← hjp]⟩
    | one => exact ⟨1, 1, by rw [lau_one]; exact one_ne_zero, by rw [one_mul]⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, y, hy, hxy⟩ := ha
      obtain ⟨x', y', hy', hxy'⟩ := hb
      refine ⟨x * y' + x' * y, y * y', by rw [lau_mul]; exact mul_ne_zero hy hy', ?_⟩
      rw [lau_mul, lau_add, lau_mul, lau_mul, ← hxy, ← hxy']; ring
    | neg a _ ha =>
      obtain ⟨x, y, hy, hxy⟩ := ha
      exact ⟨-x, y, hy, by rw [lau_neg, ← hxy]; ring⟩
    | inv a _ ha =>
      obtain ⟨x, y, hy, hxy⟩ := ha
      by_cases ha0 : a = 0
      · exact ⟨0, 1, by rw [lau_one]; exact one_ne_zero, by rw [ha0, inv_zero, zero_mul, lau_zero]⟩
      · have hx : lau p x ≠ 0 := by rw [← hxy]; exact mul_ne_zero ha0 hy
        refine ⟨y, x, hx, ?_⟩
        rw [← hxy]
        field_simp
    | mul a b _ _ ha hb =>
      obtain ⟨x, y, hy, hxy⟩ := ha
      obtain ⟨x', y', hy', hxy'⟩ := hb
      refine ⟨x * x', y * y', by rw [lau_mul]; exact mul_ne_zero hy hy', ?_⟩
      rw [lau_mul, lau_mul, ← hxy, ← hxy']; ring
  obtain ⟨x, y, hy, hxy⟩ := key _ hz
  have hyF : (y : ↥(modularFunctionFieldFull p)) ≠ 0 := fun h => hy (by show ((y : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = 0; rw [h]; rfl)
  refine ⟨x, y, hyF, ?_⟩
  rw [eq_div_iff hyF]
  apply Subtype.ext
  exact hxy

theorem isFractionRing_chartAlgFin (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq) : IsFractionRing ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ↥(modularFunctionFieldFull p) := by
  haveI : FaithfulSMul ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ↥(modularFunctionFieldFull p) := (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  apply IsFractionRing.of_field
  intro z
  obtain ⟨x, y, -, h⟩ := exists_div_of_mem_chartAlgFin p jp hjp z
  exact ⟨x, y, h⟩

end ResMatchDock

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve IsLocalRing ModularCurve

namespace ResMatchDock

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem eq_closedPoint_of_not_mem_basicOpen (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)}) (q : PrimeSpectrum O)
    (hq : q ∉ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : Set (PrimeSpectrum O))) : q = IsLocalRing.closedPoint O := by
  apply PrimeSpectrum.ext
  have hp : ((p : ℕ) : O) ∈ q.asIdeal := by simpa [PrimeSpectrum.mem_basicOpen] using hq
  show q.asIdeal = IsLocalRing.maximalIdeal O
  apply le_antisymm (IsLocalRing.le_maximalIdeal q.2.ne_top)
  rw [hϖ, Ideal.span_singleton_le_iff_mem]
  exact hp

theorem not_mem_basicOpen_closedPoint (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)}) :
    IsLocalRing.closedPoint O ∉ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : Set (PrimeSpectrum O)) := by
  intro h
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at h
  apply h
  show ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O
  rw [hϖ]; exact Ideal.mem_span_singleton_self _

theorem isDiscreteValuationRing_and_maximalIdeal_eq
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (ξ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hξU : ξ ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ 𝔛.smoothLocus)
    (hξs : ξ ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    (hmax : ∀ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))), y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) → y ⤳ ξ → y = ξ) :
    IsDiscreteValuationRing ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) ∧
      IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) = Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ)} := by

  haveI := 𝔛.smoothLocus_relDim
  haveI : Smooth (𝔛.smoothLocus.ι ≫ DRModel.toBase p) :=
    SmoothOfRelativeDimension.smooth (n := 1) (f := 𝔛.smoothLocus.ι ≫ DRModel.toBase p)
  let g := Spec.map (CommRingCat.ofHom (algebraMap ℤ O))
  let T := pullback (𝔛.smoothLocus.ι ≫ DRModel.toBase p) g
  let t : T ⟶ Spec (CommRingCat.of O) := pullback.snd _ _
  let i : T ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) :=
    pullback.map (𝔛.smoothLocus.ι ≫ DRModel.toBase p) g (DRModel.toBase p) g 𝔛.smoothLocus.ι (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  haveI : IsOpenImmersion i := inferInstance
  have hi_snd : i ≫ pullback.snd (DRModel.toBase p) g = t := by
    show pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd, Category.comp_id]

  have hξ : ξ ∈ Set.range i.base := by
    rw [Scheme.Pullback.range_map]
    refine ⟨?_, by simp⟩
    show (pullback.fst (DRModel.toBase p) g).base ξ ∈ Set.range 𝔛.smoothLocus.ι.base
    rw [Scheme.Opens.range_ι]
    exact hξU
  obtain ⟨η, hη⟩ := hξ

  have hts : ∀ y : ↥T, t.base y = (pullback.snd (DRModel.toBase p) g).base (i.base y) := by
    intro y; rw [← hi_snd]; rfl
  have hηs : t.base η = IsLocalRing.closedPoint O := by
    rw [hts, hη]
    exact eq_closedPoint_of_not_mem_basicOpen p O hϖ _ hξs
  have hgen : ∀ y : ↥T, y ⤳ η → t.base y = IsLocalRing.closedPoint O → y = η := by
    intro y hy hyc
    apply i.isOpenEmbedding.injective
    rw [hη]
    apply hmax
    · intro hc
      have hc' : (pullback.snd (DRModel.toBase p) g).base (i.base y) ∈
          (PrimeSpectrum.basicOpen ((p : ℕ) : O) : Set (PrimeSpectrum O)) := hc
      rw [← hts, hyc] at hc'
      exact not_mem_basicOpen_closedPoint p O hϖ hc'
    · rw [← hη]; exact hy.map i.base.hom.continuous
  obtain ⟨_, hDVR⟩ := AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes O t η hηs hgen
  have hmT := AlgebraicGeometry.Smooth.maximalIdeal_stalk_eq_span_of_forall_specializes O ((p : ℕ) : O) hϖ t η hηs hgen

  let E : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ ≃+* T.presheaf.stalk η :=
    (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq hη.symm)).trans (asIso (i.stalkMap η))).commRingCatIsoToRingEquiv
  haveI : IsDiscreteValuationRing ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E.symm
  refine ⟨inferInstance, ?_⟩

  have hgenT : (T.presheaf.germ ⊤ η trivial).hom ((t.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ((p : ℕ) : O)))
      = ((p : ℕ) : T.presheaf.stalk η) := by
    simp only [map_natCast]
  rw [hgenT] at hmT
  have hm : IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) = (IsLocalRing.maximalIdeal (T.presheaf.stalk η)).comap E.toRingHom := by
    haveI : ((IsLocalRing.maximalIdeal (T.presheaf.stalk η)).comap E.toRingHom).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective (K := IsLocalRing.maximalIdeal (T.presheaf.stalk η)) E.toRingHom E.surjective
    exact (IsLocalRing.eq_maximalIdeal this).symm
  have hpE : ((p : ℕ) : T.presheaf.stalk η) = E.toRingHom ((p : ℕ) : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ)) := (map_natCast E.toRingHom p).symm
  rw [hm, hmT, hpE, ← Set.image_singleton, ← Ideal.map_span]
  exact Ideal.comap_map_of_bijective E.toRingHom E.bijective

end ResMatchDock

namespace ResMatchDock

section Readings

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (ιK : K →+* AlgebraicClosure ℚ)
  [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
  (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
  (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+* ↥(modularFunctionFieldBar (1 * p)))
  [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]

noncomputable def psi : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv ≫
    ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ≫
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) ≫
        (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))).hom

theorem psi_apply (a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : psi p O a =
    ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
      (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
          ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
        (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) := rfl

noncomputable def thetaO : O →+* ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) :=
  (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)).comp
    (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom.comp
      (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom))

theorem thetaO_apply (a : O) : thetaO p O x a =
    algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
      (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a))) := rfl

variable
  (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), ((φ (psi p O a) : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
    coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

include hφj in
theorem psi_injective : Function.Injective (psi p O) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h := hφj a
  rw [ha, map_zero, ZeroMemClass.coe_zero] at h
  have : ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = 0 := by
    apply HahnSeries.ext; funext k
    have := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff k) h
    simp only [HahnSeries.coeff_zero, coeffEmb_coeff] at this
    simp only [HahnSeries.coeff_zero]
    exact (map_eq_zero_iff _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mp this.symm
  exact Subtype.ext (Subtype.ext this)

variable (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)

noncomputable def thetaF : ↥(modularFunctionFieldFull p) →+* ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) :=
  haveI := isFractionRing_chartAlgFin p jp hjp
  IsFractionRing.lift (psi_injective p O φ hφj)

theorem thetaF_coe (a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : thetaF p O φ hφj jp hjp (a : ↥(modularFunctionFieldFull p)) = psi p O a := by
  haveI := isFractionRing_chartAlgFin p jp hjp
  exact IsFractionRing.lift_algebraMap (psi_injective p O φ hφj) a

include hφj in
theorem coe_phi_thetaF (f : ↥(modularFunctionFieldFull p)) :
    ((φ (thetaF p O φ hφj jp hjp f) : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) := by
  obtain ⟨a, b, hb, rfl⟩ := exists_div_of_mem_chartAlgFin p jp hjp f
  rw [map_div₀, map_div₀, thetaF_coe, thetaF_coe]
  show (((φ (psi p O a) / φ (psi p O b) : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ))) = _
  rw [IntermediateField.coe_div, hφj, hφj, ← map_div₀]
  congr 1

end Readings

end ResMatchDock

namespace ResMatchDock

section Feed

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
  (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
  (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+* ↥(modularFunctionFieldBar (1 * p)))
  [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
  (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), ((φ (psi p O a) : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
    coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))
  (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)

include hint hne in

theorem closure_range_thetaF_union_range_thetaO_eq_top :
    Subfield.closure (Set.range (thetaF p O φ hφj jp hjp) ∪ Set.range (thetaO p O x)) = ⊤ := by
  have h := AlgebraicCurve.TwoChartIntegralModel.subfieldClosure_range_germToFunctionField_union_range_eq_top
    ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O x
  rw [eq_top_iff, ← h]
  apply Subfield.closure_mono
  rintro y (⟨a, rfl⟩ | ⟨s, rfl⟩)
  · exact Or.inl ⟨(a : ↥(modularFunctionFieldFull p)), thetaF_coe p O φ hφj jp hjp a⟩
  · exact Or.inr ⟨s, rfl⟩

theorem thetaO_mem_range (ξ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) (a : O) :
    thetaO p O x a ∈ Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) := by
  refine ⟨((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ξ trivial).hom
      (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)), ?_⟩
  rw [thetaO_apply]

  show ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ξ trivial ≫ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom _ =
    ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial ≫ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom _
  rw [TopCat.Presheaf.germ_stalkSpecializes, TopCat.Presheaf.germ_stalkSpecializes]

theorem range_algebraMap_stalk_subset_of_specializes {ξ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))} (h : ξ ⤳ y) :
    Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk y) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) ⊆
      Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) := by
  rintro _ ⟨s, rfl⟩
  refine ⟨((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes h).hom s, ?_⟩
  show ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes h ≫ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom s = ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom s
  rw [TopCat.Presheaf.stalkSpecializes_comp]

variable (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (ιK : K →+* AlgebraicClosure ℚ)
  (hφO : ∀ a : O, φ (thetaO p O x a) =
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

include hφO hφj in

theorem thetaF_jFull_mem_range
    (hxj' : ∃ ĵ : O, ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ))) :
    thetaF p O φ hφj jp hjp (IgusaScheme.jFull p) ∈ Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) := by
  obtain ⟨ĵ, t, -, ht⟩ := hxj'
  have hj : φ (thetaF p O φ hφj jp hjp (IgusaScheme.jFull p)) = ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p := by
    apply Subtype.ext
    rw [coe_phi_thetaF]
    rfl
  have : thetaF p O φ hφj jp hjp (IgusaScheme.jFull p) = algebraMap _ _ t + thetaO p O x ĵ := by
    apply φ.injective
    rw [map_add, ht, hφO, hj, sub_add_cancel]
  rw [this]
  obtain ⟨c, hc⟩ := thetaO_mem_range p O x x ĵ
  exact ⟨t + c, by rw [map_add, hc]⟩

end Feed

end ResMatchDock

namespace ResMatchCore

section LocalRange

variable {L : Type*} [Field L] {T : Type*} [CommRing T] [IsLocalRing T]

theorem mem_maximalIdeal_iff_mem_nonunits (a : T →+* L) (ha : Function.Injective a)
    (V : ValuationSubring L) (hrange : Set.range a = (V : Set L)) (u : T) :
    u ∈ IsLocalRing.maximalIdeal T ↔ a u ∈ V.nonunits := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
  constructor
  · intro hnu
    by_contra h
    push Not at h
    obtain ⟨hne, hinv⟩ := h
    have : (a u)⁻¹ ∈ Set.range a := by rw [hrange]; exact hinv
    obtain ⟨w, hw⟩ := this
    apply hnu
    refine isUnit_iff_exists_inv.mpr ⟨w, ha ?_⟩
    rw [map_mul, map_one, hw, mul_inv_cancel₀ hne]
  · rintro (h0 | hinv) hu
    · obtain ⟨v, rfl⟩ := hu
      have := congrArg a v.mul_inv
      rw [map_mul, map_one, show a (v : T) = 0 from h0, zero_mul] at this
      exact zero_ne_one this
    · apply hinv
      obtain ⟨v, rfl⟩ := hu
      have h1 : a (v : T) * a ((v⁻¹ : Tˣ) : T) = 1 := by rw [← map_mul, v.mul_inv, map_one]
      have : (a (v : T))⁻¹ = a ((v⁻¹ : Tˣ) : T) := by
        rw [inv_eq_of_mul_eq_one_right h1]
      rw [this, ← SetLike.mem_coe, ← hrange]
      exact Set.mem_range_self _

end LocalRange

section Comap

variable {L M : Type*} [Field L] [Field M] (φ : L →+* M) (R : ValuationSubring M)

theorem mem_nonunits_comap_iff (x : L) : x ∈ (R.comap φ).nonunits ↔ φ x ∈ R.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero]

end Comap

section Main

variable {L M : Type*} [Field L] [Field M] (φ : L →+* M) (R₁ R₂ : ValuationSubring M)
variable {S T₁ T₂ : Type*} [CommRing S] [CommRing T₁] [CommRing T₂] [IsLocalRing T₁] [IsLocalRing T₂]
variable (a₀ : S →+* L) (sp₁ : S →+* T₁) (sp₂ : S →+* T₂) (a₁ : T₁ →+* L) (a₂ : T₂ →+* L)

theorem range_eq_and_range_eq
    (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (h₁ : a₁.comp sp₁ = a₀) (h₂ : a₂.comp sp₂ = a₀)
    (hV₁ : Set.range a₁ = (R₁.comap φ : Set L) ∨ Set.range a₁ = (R₂.comap φ : Set L))
    (hV₂ : Set.range a₂ = (R₁.comap φ : Set L) ∨ Set.range a₂ = (R₂.comap φ : Set L))
    (hdist : Ideal.comap sp₁ (IsLocalRing.maximalIdeal T₁) ≠ Ideal.comap sp₂ (IsLocalRing.maximalIdeal T₂))
    (tF : S) (htF₁ : sp₁ tF ∈ IsLocalRing.maximalIdeal T₁)
    (htFR₁ : φ (a₀ tF) ∈ R₁.nonunits) (htFR₂ : φ (a₀ tF) ∉ R₂.nonunits) :
    Set.range a₁ = (R₁.comap φ : Set L) ∧ Set.range a₂ = (R₂.comap φ : Set L) := by
  have hfirst : Set.range a₁ = (R₁.comap φ : Set L) := by
    rcases hV₁ with h | h
    · exact h
    · exfalso
      apply htFR₂
      have := (mem_maximalIdeal_iff_mem_nonunits a₁ ha₁ (R₂.comap φ) h (sp₁ tF)).mp htF₁
      rw [mem_nonunits_comap_iff] at this
      rwa [← h₁]
  refine ⟨hfirst, ?_⟩
  rcases hV₂ with h | h
  · exfalso
    apply hdist
    ext s
    rw [Ideal.mem_comap, Ideal.mem_comap, mem_maximalIdeal_iff_mem_nonunits a₁ ha₁ (R₁.comap φ) hfirst (sp₁ s),
      mem_maximalIdeal_iff_mem_nonunits a₂ ha₂ (R₁.comap φ) h (sp₂ s),
      show a₁ (sp₁ s) = a₀ s from by rw [← h₁]; rfl, show a₂ (sp₂ s) = a₀ s from by rw [← h₂]; rfl]
  · exact h

theorem mem_nonunits_iff_and
    (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (h₁ : a₁.comp sp₁ = a₀) (h₂ : a₂.comp sp₂ = a₀)
    (hV₁ : Set.range a₁ = (R₁.comap φ : Set L) ∨ Set.range a₁ = (R₂.comap φ : Set L))
    (hV₂ : Set.range a₂ = (R₁.comap φ : Set L) ∨ Set.range a₂ = (R₂.comap φ : Set L))
    (hdist : Ideal.comap sp₁ (IsLocalRing.maximalIdeal T₁) ≠ Ideal.comap sp₂ (IsLocalRing.maximalIdeal T₂))
    (tF : S) (htF₁ : sp₁ tF ∈ IsLocalRing.maximalIdeal T₁)
    (htFR₁ : φ (a₀ tF) ∈ R₁.nonunits) (htFR₂ : φ (a₀ tF) ∉ R₂.nonunits) (s : S) :
    (φ (a₀ s) ∈ R₁ ∧ (φ (a₀ s) ∈ R₁.nonunits ↔ sp₁ s ∈ IsLocalRing.maximalIdeal T₁)) ∧
    (φ (a₀ s) ∈ R₂ ∧ (φ (a₀ s) ∈ R₂.nonunits ↔ sp₂ s ∈ IsLocalRing.maximalIdeal T₂)) := by
  obtain ⟨e₁, e₂⟩ := range_eq_and_range_eq φ R₁ R₂ a₀ sp₁ sp₂ a₁ a₂ ha₁ ha₂ h₁ h₂ hV₁ hV₂ hdist tF htF₁ htFR₁ htFR₂
  have hs₁ : a₀ s = a₁ (sp₁ s) := by rw [← h₁]; rfl
  have hs₂ : a₀ s = a₂ (sp₂ s) := by rw [← h₂]; rfl
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : a₁ (sp₁ s) ∈ (R₁.comap φ : Set L) := e₁ ▸ Set.mem_range_self _
    rw [hs₁]; exact this
  · rw [hs₁, (mem_maximalIdeal_iff_mem_nonunits a₁ ha₁ (R₁.comap φ) e₁ (sp₁ s)), mem_nonunits_comap_iff]
  · have : a₂ (sp₂ s) ∈ (R₂.comap φ : Set L) := e₂ ▸ Set.mem_range_self _
    rw [hs₂]; exact this
  · rw [hs₂, (mem_maximalIdeal_iff_mem_nonunits a₂ ha₂ (R₂.comap φ) e₂ (sp₂ s)), mem_nonunits_comap_iff]

end Main

section Residue

variable {L M C : Type*} [Field L] [Field M] [Field C] (φ : L →+* M) (R₁ : ValuationSubring M)
variable {T : Type*} [CommRing T] [IsLocalRing T] (a : T →+* L)
variable (ρ : R₁ →+* C) (hρ : ∀ x : R₁, ρ x = 0 ↔ (x : M) ∈ R₁.nonunits)

def toVal (hrange : Set.range a = (R₁.comap φ : Set L)) : T →+* R₁ :=
  (φ.comp a).codRestrict R₁.toSubring (fun u => by
    have : a u ∈ (R₁.comap φ : Set L) := hrange ▸ Set.mem_range_self u
    exact this)

@[scoped simp] theorem coe_toVal (hrange : Set.range a = (R₁.comap φ : Set L)) (u : T) :
    ((toVal φ R₁ a hrange u : R₁) : M) = φ (a u) := rfl

include hρ in

theorem exists_residueField_hom (ha : Function.Injective a) (hrange : Set.range a = (R₁.comap φ : Set L)) :
    ∃ ψ : IsLocalRing.ResidueField T →+* C, Function.Injective ψ ∧
      ∀ u : T, ψ (IsLocalRing.residue T u) = ρ (toVal φ R₁ a hrange u) := by
  have hker : ∀ u : T, u ∈ IsLocalRing.maximalIdeal T ↔ ρ (toVal φ R₁ a hrange u) = 0 := by
    intro u
    rw [hρ, coe_toVal, ← mem_nonunits_comap_iff, mem_maximalIdeal_iff_mem_nonunits a ha (R₁.comap φ) hrange u]
  refine ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal T) (ρ.comp (toVal φ R₁ a hrange))
    (fun u hu => (hker u).mp hu), ?_, fun u => rfl⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hker u).mpr hz)

end Residue

end ResMatchCore
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal.ResMatchCore"

namespace ResMatchInst

open ResMatchCore ModularCurve.PlaceSpecialization.ProlongationTuple

theorem jQFun_sub_jFun_pow_mem_nonunits
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr k red hα hβ} (R : ProlongationTuple P) :
    (jQFun 1 p - jFun 1 p ^ p : ↥(modularFunctionFieldBar (1 * p))) ∈ R.R₁.integers.nonunits ∧
    (jQFun 1 p - jFun 1 p ^ p : ↥(modularFunctionFieldBar (1 * p))) ∉ R.R₂.integers.nonunits := by
  have hp1 : ¬ p ∣ 1 := fun h => (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h)
  obtain ⟨h₁, h₂, h₃, h₄, e₁, e₂, e₃, e₄⟩ := R.residue_jFun_sub_jQFun_sub hp1 0
  have hz : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((0 : A) : AlgebraicClosure ℚ) = 0 := by
    rw [ZeroMemClass.coe_zero, map_zero]
  have hz' : algebraMap k ↥(modularFunctionFieldC k 1) (red 0) = 0 := by rw [map_zero, map_zero]
  rw [hz'] at e₁ e₂ e₃ e₄

  have m₁ : (jFun 1 p : ↥(modularFunctionFieldBar (1 * p))) ∈ R.R₁.integers := by simpa [hz] using h₁
  have m₂ : (jFun 1 p : ↥(modularFunctionFieldBar (1 * p))) ∈ R.R₂.integers := by simpa [hz] using h₂
  have m₃ : (jQFun 1 p : ↥(modularFunctionFieldBar (1 * p))) ∈ R.R₁.integers := by simpa [hz] using h₃
  have m₄ : (jQFun 1 p : ↥(modularFunctionFieldBar (1 * p))) ∈ R.R₂.integers := by simpa [hz] using h₄
  have f₁ : R.residue₁ ⟨jFun 1 p, m₁⟩ = jGeomGen k 1 := by
    rw [← sub_zero (jGeomGen k 1), ← e₁]; congr 1; apply Subtype.ext; simp [hz]
  have f₂ : R.residue₂ ⟨jFun 1 p, m₂⟩ = jGeomGen k 1 ^ p := by
    rw [← sub_zero (jGeomGen k 1 ^ p), ← e₂]; congr 1; apply Subtype.ext; simp [hz]
  have f₃ : R.residue₁ ⟨jQFun 1 p, m₃⟩ = jGeomGen k 1 ^ p := by
    rw [← sub_zero (jGeomGen k 1 ^ p), ← e₃]; congr 1; apply Subtype.ext; simp [hz]
  have f₄ : R.residue₂ ⟨jQFun 1 p, m₄⟩ = jGeomGen k 1 := by
    rw [← sub_zero (jGeomGen k 1), ← e₄]; congr 1; apply Subtype.ext; simp [hz]
  have M₁ : (jQFun 1 p - jFun 1 p ^ p : ↥(modularFunctionFieldBar (1 * p))) ∈ R.R₁.integers :=
    sub_mem m₃ (pow_mem m₁ p)
  have M₂ : (jQFun 1 p - jFun 1 p ^ p : ↥(modularFunctionFieldBar (1 * p))) ∈ R.R₂.integers :=
    sub_mem m₄ (pow_mem m₂ p)
  have r₁ : R.residue₁ ⟨_, M₁⟩ = 0 := by
    have : (⟨_, M₁⟩ : R.R₁.integers) = ⟨jQFun 1 p, m₃⟩ - ⟨jFun 1 p, m₁⟩ ^ p := rfl
    rw [this, map_sub, map_pow, f₃, f₁, sub_self]
  have r₂ : R.residue₂ ⟨_, M₂⟩ ≠ 0 := by
    have : (⟨_, M₂⟩ : R.R₂.integers) = ⟨jQFun 1 p, m₄⟩ - ⟨jFun 1 p, m₂⟩ ^ p := rfl
    rw [this, map_sub, map_pow, f₄, f₂, ← pow_mul]

    intro h0
    have hc : (jqModC k : LaurentSeries k) - jqModC k ^ (p * p) = 0 := by
      have := congrArg (fun z : ↥(modularFunctionFieldC k 1) => (z : LaurentSeries k)) h0
      simpa using this
    have halg : IsAlgebraic k (jqModC k : LaurentSeries k) := by
      refine ⟨Polynomial.X - Polynomial.X ^ (p * p), ?_, ?_⟩
      · intro hP
        have hpp : p * p ≠ 1 := by
          have := (Fact.out : p.Prime).two_le; nlinarith
        have := congrArg (fun P : Polynomial k => P.coeff 1) hP
        simp only [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_X_pow, Polynomial.coeff_zero] at this
        rw [if_neg (Ne.symm hpp)] at this
        norm_num at this
      · simp [hc]
    exact transcendental_jqModC k halg
  refine ⟨?_, ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    refine ⟨M₁, ?_⟩
    rw [← RegularProlongation.ker_residue, RingHom.mem_ker]
    have := r₁
    rwa [residue₁_apply, map_eq_zero_iff _ R.ι.injective] at this
  · intro hn
    apply r₂
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hn
    obtain ⟨M₂', hM⟩ := hn
    rw [← RegularProlongation.ker_residue, RingHom.mem_ker] at hM
    rw [residue₂_apply, map_eq_zero_iff _ R.ι.injective]
    exact hM

end ResMatchInst
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal.ResMatchCore"

namespace ResMatchDock

open ResMatchCore ModularCurve.PlaceSpecialization.ProlongationTuple

set_option maxHeartbeats 12800000 in
open Classical in

theorem valSub_eq_comap_or
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (htF : φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p)
    (hor : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w)
    (ξ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hξU : ξ ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ 𝔛.smoothLocus)
    (hξs : ξ ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    (hmax : ∀ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))), y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) → y ⤳ ξ → y = ξ)
    (hsp : ξ ⤳ x)

    (hjunit : ∀ Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField))
          (psi p O (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) Q ∈
          Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField))
          (psi p O (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) Q)⁻¹ ∈
          Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField))) :
    haveI : IsDiscreteValuationRing ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) :=
      (isDiscreteValuationRing_and_maximalIdeal_eq p 𝔛 O hϖ ξ hξU hξs hmax).1
    valSub ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) = R.R₁.integers.comap φ ∨
      valSub ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) = R.R₂.integers.comap φ := by
  obtain ⟨hDVR, hm⟩ := isDiscreteValuationRing_and_maximalIdeal_eq p 𝔛 O hϖ ξ hξU hξs hmax
  haveI := hDVR
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨jp, -, -, hjp, -⟩ := ModularCurve.DRModel.exists_chartAlgFin_valuationSubring_pair_levelP p
  have hφj' : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), ((φ (psi p O a) : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) := hφj
  have hpmem : ((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) ∈ IsLocalRing.maximalIdeal _ := by
    rw [hm]; exact Ideal.mem_span_singleton_self _
  have hpcoe : ((p : ℕ) : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) = algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) _ ((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) :=
    (map_natCast _ p).symm
  refine ModularCurve.PlaceSpecialization.ProlongationTuple.eq_comap_integers_or_of_forall_exists_eq_pow_mul
    p O hϖ (ιK.comp (algebraMap O K)) P R (fun a => hιA a) (↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) φ
    (thetaO p O x) (fun a => by rw [thetaO_apply]; exact hφO a)
    (thetaF p O φ hφj' jp hjp) (coe_phi_thetaF p O φ hφj' jp hjp)
    (closure_range_thetaF_union_range_thetaO_eq_top p O x φ hφj' jp hjp)
    (valSub ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) ?_ ?_ ?_ ?_
  · rw [hpcoe]; exact algebraMap_mem_nonunits_of_mem_maximalIdeal _ hpmem
  · intro g hg hg0
    obtain ⟨n, u, hu, hui, e⟩ := exists_eq_pow_mul_of_maximalIdeal_eq _ hm g hg hg0
    exact ⟨n, u, hu, hui, by rw [hpcoe]; exact e⟩
  · intro a
    exact (mem_valSub_iff _ _ _).mpr (thetaO_mem_range p O x ξ a)
  · intro Q hQ
    have eJ : thetaF p O φ hφj' jp hjp ⟨jq, modularFunctionField_le_full p (jq_mem p)⟩ =
        psi p O (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
      thetaF_coe p O φ hφj' jp hjp (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
    rw [eJ, mem_valSub_iff, mem_valSub_iff]
    exact hjunit Q hQ

end ResMatchDock
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal.ResMatchCore"

namespace ResMatchDock

open ModularCurve.PlaceSpecialization.ProlongationTuple

set_option maxHeartbeats 12800000 in
open Classical in
theorem junit_at
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (htF : φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p)
    (hor : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w) :
    let J := psi p O (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
    (J ∈ Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField))) ∧
    (J ∈ Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField))) := by
  intro J
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨jp, -, -, hjp, -⟩ := ModularCurve.DRModel.exists_chartAlgFin_valuationSubring_pair_levelP p
  have hφj' := hφj
  obtain ⟨ĵ, -, t, ht, hφt⟩ := hxj
  have hx : J ∈ Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) := by
    have := thetaF_jFull_mem_range p O x φ hφj' jp hjp K ιK hφO ⟨ĵ, t, ht, hφt⟩
    rwa [show (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) = ((TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) :
        ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : ↥(modularFunctionFieldFull p)) from rfl, thetaF_coe] at this
  exact ⟨range_algebraMap_stalk_subset_of_specializes p O hsp₁ hx, range_algebraMap_stalk_subset_of_specializes p O hsp₂ hx⟩

end ResMatchDock
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal.ResMatchCore"

namespace ResMatchDock

open ResMatchCore ModularCurve.PlaceSpecialization.ProlongationTuple

set_option maxHeartbeats 12800000 in
open Classical in

theorem oriented
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (htF : φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p)
    (hor : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w)
    (𝒱₁ 𝒱₂ : ValuationSubring ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField))
    (h𝒱₁ : (𝒱₁ : Set ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) = Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)))
    (h𝒱₂ : (𝒱₂ : Set ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) = Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)))
    (hV₁ : 𝒱₁ = R.R₁.integers.comap φ ∨ 𝒱₁ = R.R₂.integers.comap φ)
    (hV₂ : 𝒱₂ = R.R₁.integers.comap φ ∨ 𝒱₂ = R.R₂.integers.comap φ) :
    Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) = ((R.R₁.integers.comap φ : ValuationSubring _) : Set _) ∧
    Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) = ((R.R₂.integers.comap φ : ValuationSubring _) : Set _) := by

  set ξ₁ := (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) with hξ₁
  set ξ₂ := (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) with hξ₂
  haveI : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := hint

  let a₀ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x →+* ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) := algebraMap _ _
  let a₁ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ₁ →+* ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) := algebraMap _ _
  let a₂ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ₂ →+* ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) := algebraMap _ _
  let sp₁ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x →+* (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ₁ := ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom
  let sp₂ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x →+* (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ₂ := ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₂).hom
  have ha₁ : Function.Injective a₁ := IsFractionRing.injective _ _
  have ha₂ : Function.Injective a₂ := IsFractionRing.injective _ _
  have hc₁ : a₁.comp sp₁ = a₀ := by
    change ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁ ≫ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom = ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  have hc₂ : a₂.comp sp₂ = a₀ := by
    change ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₂ ≫ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom = ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom
    rw [TopCat.Presheaf.stalkSpecializes_comp]

  have hr₁ : Set.range a₁ = ((R.R₁.integers.comap φ : ValuationSubring _) : Set _) ∨
      Set.range a₁ = ((R.R₂.integers.comap φ : ValuationSubring _) : Set _) := by
    rcases hV₁ with h | h
    · left; rw [← h, h𝒱₁]
    · right; rw [← h, h𝒱₁]
  have hr₂ : Set.range a₂ = ((R.R₁.integers.comap φ : ValuationSubring _) : Set _) ∨
      Set.range a₂ = ((R.R₂.integers.comap φ : ValuationSubring _) : Set _) := by
    rcases hV₂ with h | h
    · left; rw [← h, h𝒱₂]
    · right; rw [← h, h𝒱₂]

  have hpt : ∀ {ξ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))} (h : ξ ⤳ x),
      ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).fromSpecStalk x).base ((Spec.map ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes h)).base (IsLocalRing.closedPoint _)) = ξ := by
    intro ξ h
    have e := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) h
    have e2 : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).fromSpecStalk x).base
        ((Spec.map ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes h)).base
          (IsLocalRing.closedPoint _)) =
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).fromSpecStalk ξ).base (IsLocalRing.closedPoint _) := by
      rw [← e]; rfl
    rw [e2]
    exact Scheme.fromSpecStalk_closedPoint
  have hd : Ideal.comap sp₁ (IsLocalRing.maximalIdeal _) ≠ Ideal.comap sp₂ (IsLocalRing.maximalIdeal _) := by
    intro h
    apply ModularCurve.DRModelPackage.baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint p 𝔛 O hϖ k toκ
    rw [← hξ₁, ← hξ₂, ← hpt hsp₁, ← hpt hsp₂]
    congr 1
    apply PrimeSpectrum.ext
    exact h

  obtain ⟨hG₁, hG₂⟩ := ResMatchInst.jQFun_sub_jFun_pow_mem_nonunits R
  have htFR₁ : φ (a₀ tF) ∈ R.R₁.integers.nonunits := by rw [show a₀ tF = _ from rfl, htF]; exact hG₁
  have htFR₂ : φ (a₀ tF) ∉ R.R₂.integers.nonunits := by rw [show a₀ tF = _ from rfl, htF]; exact hG₂
  exact range_eq_and_range_eq φ R.R₁.integers R.R₂.integers a₀ sp₁ sp₂ a₁ a₂ ha₁ ha₂ hc₁ hc₂ hr₁ hr₂ hd tF hor htFR₁ htFR₂

set_option maxHeartbeats 12800000 in
open Classical in

theorem oriented_final
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (htF : φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p)
    (hor : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w) :
    Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) = ((R.R₁.integers.comap φ : ValuationSubring _) : Set _) ∧
    Set.range (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) = ((R.R₂.integers.comap φ : ValuationSubring _) : Set _) := by
  obtain ⟨hU₁, hU₂⟩ := ModularCurve.DRModelPackage.baseChangeMap_genericPoint_mem_preimage_smoothLocus p 𝔛 O k toκ
  have hs₁ : ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) :=
    ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O k toκ _
  have hs₂ : ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) :=
    ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O k toκ _
  obtain ⟨hmax₁, hmax₂⟩ := ModularCurve.DRModelPackage.eq_baseChangeMap_genericPoint_of_specializes p 𝔛 O hϖ k toκ
  obtain ⟨hJ₁, hJ₂⟩ := junit_at p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ w hw hxj n hy₁ hy₂ hx₁ hx₂ hsp₁ hsp₂ tF htF hor hconv
  have hjunit := ModularCurve.DRModelPackage.polynomialEval_mem_range_algebraMap_stalk_and_inv_mem_of_map_ne_zero
    p hp 𝔛 O hϖ toκ hJ₁ hJ₂
  have hV₁ := valSub_eq_comap_or p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ w hw hxj n hy₁ hy₂ hx₁ hx₂ hsp₁ hsp₂ tF htF hor hconv _ hU₁ hs₁ hmax₁ hsp₁ (fun Q hQ => (hjunit Q hQ).1)
  have hV₂ := valSub_eq_comap_or p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ w hw hxj n hy₁ hy₂ hx₁ hx₂ hsp₁ hsp₂ tF htF hor hconv _ hU₂ hs₂ hmax₂ hsp₂ (fun Q hQ => (hjunit Q hQ).2)
  haveI i₁ := (isDiscreteValuationRing_and_maximalIdeal_eq p 𝔛 O hϖ _ hU₁ hs₁ hmax₁).1
  haveI i₂ := (isDiscreteValuationRing_and_maximalIdeal_eq p 𝔛 O hϖ _ hU₂ hs₂ hmax₂).1
  exact oriented p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ w hw hxj n hy₁ hy₂ hx₁ hx₂ hsp₁ hsp₂ tF htF hor hconv (valSub ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) _) (valSub ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) _)
    (coe_valSub _ _) (coe_valSub _ _) hV₁ hV₂

set_option maxHeartbeats 12800000 in
open Classical in

theorem hval_hloc
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (htF : φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p)
    (hor : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w) :
    (∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)), φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) ∈ R.R₁.integers ∧
      (u ∈ IsLocalRing.maximalIdeal _ → φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) ∈ R.R₁.integers.nonunits)) ∧
    (∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)), φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) ∈ R.R₂.integers ∧
      (u ∈ IsLocalRing.maximalIdeal _ → φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) ∈ R.R₂.integers.nonunits)) := by
  obtain ⟨e₁, e₂⟩ := oriented_final p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ w hw hxj n hy₁ hy₂ hx₁ hx₂ hsp₁ hsp₂ tF htF hor hconv
  haveI : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := hint
  refine ⟨fun u => ⟨?_, fun hu => ?_⟩, fun u => ⟨?_, fun hu => ?_⟩⟩
  · have : algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u ∈ ((R.R₁.integers.comap φ : ValuationSubring _) : Set _) := e₁ ▸ Set.mem_range_self u
    exact this
  · rw [← mem_nonunits_comap_iff]
    exact (mem_maximalIdeal_iff_mem_nonunits _ (IsFractionRing.injective _ _) _ e₁ u).mp hu
  · have : algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u ∈ ((R.R₂.integers.comap φ : ValuationSubring _) : Set _) := e₂ ▸ Set.mem_range_self u
    exact this
  · rw [← mem_nonunits_comap_iff]
    exact (mem_maximalIdeal_iff_mem_nonunits _ (IsFractionRing.injective _ _) _ e₂ u).mp hu

theorem residue_eq_zero_of_mem_nonunits {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr k red hα hβ} (R : ProlongationTuple P)
    (f : ↥(modularFunctionFieldBar (1 * p))) :
    (∀ (h : f ∈ R.R₁.integers), f ∈ R.R₁.integers.nonunits → R.residue₁ ⟨f, h⟩ = 0) ∧
    (∀ (h : f ∈ R.R₂.integers), f ∈ R.R₂.integers.nonunits → R.residue₂ ⟨f, h⟩ = 0) := by
  constructor
  · intro h hn
    rw [residue₁_apply, map_eq_zero_iff _ R.ι.injective, ← RingHom.mem_ker, RegularProlongation.ker_residue,
      ← ValuationSubring.coe_mem_nonunits_iff]
    exact hn
  · intro h hn
    rw [residue₂_apply, map_eq_zero_iff _ R.ι.injective, ← RingHom.mem_ker, RegularProlongation.ker_residue,
      ← ValuationSubring.coe_mem_nonunits_iff]
    exact hn

set_option maxHeartbeats 12800000 in
open Classical in

theorem attain
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (htF : φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p)
    (hor : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w) :
    (∃ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)), φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) = jFun 1 p) ∧
    (∃ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)), φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) = jQFun 1 p) := by
  obtain ⟨⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩ := junit_at p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ w hw hxj n hy₁ hy₂ hx₁ hx₂ hsp₁ hsp₂ tF htF hor hconv
  have hJ : φ (psi p O (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = jFun 1 p :=
    Subtype.ext (hφj _)
  refine ⟨⟨u₁, by rw [hu₁, hJ]⟩, ⟨((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₂).hom tF + u₂ ^ p, ?_⟩⟩
  have hc : algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₂).hom tF) =
      algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) tF := by
    show ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₂ ≫ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom tF = ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom tF
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  rw [map_add, map_pow, map_add, map_pow, hc, htF, hu₂, hJ, sub_add_cancel]

set_option maxHeartbeats 6400000 in
open Classical in

theorem nodeResidue_of_eq_jFun_sub
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (htF : φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p)
    (hor : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w)
    (ĵ : O) (t : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (hφt : φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) t) =
      jFun 1 p - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ))) :
    R.nodeResidue₁ w ⟨_, hconv t⟩ = jGeomGen k 1 - algebraMap k _ (red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩) ∧
    R.nodeResidue₂ w ⟨_, hconv t⟩ = jGeomGen k 1 ^ p - algebraMap k _ (red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩) := by
  have hp1 : ¬ p ∣ 1 := fun h => (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h)
  obtain ⟨h₁, h₂, -, -, e₁, e₂, -, -⟩ := R.residue_jFun_sub_jQFun_sub hp1 ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩
  constructor
  · show R.residue₁ ⟨_, (hconv t).1⟩ = _
    rw [← e₁]; congr 1; exact Subtype.ext hφt
  · show R.residue₂ ⟨_, (hconv t).2.1⟩ = _
    rw [← e₂]; congr 1; exact Subtype.ext hφt

open Classical in

theorem phi_germ_const
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (htF : φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p)
    (hor : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w)
    (ξ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) (a : O) :
    φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ξ trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)) := by
  rw [← hφO a]
  congr 1
  show ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ξ trivial ≫ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom _ =
    ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial ≫ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom _
  rw [TopCat.Presheaf.germ_stalkSpecializes, TopCat.Presheaf.germ_stalkSpecializes]

end ResMatchDock
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal.ResMatchCore"

set_option maxHeartbeats 6400000 in
open Classical in
open ModularCurve.PlaceSpecialization.ProlongationTuple in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (htF : φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p)
    (hor : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w) :

    (∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) ∈ R.R₁.integers ∧
        (u ∈ IsLocalRing.maximalIdeal _ → φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) ∈ R.R₁.integers.nonunits)) ∧

    (∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) ∈ R.R₂.integers ∧
        (u ∈ IsLocalRing.maximalIdeal _ → φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) ∈ R.R₂.integers.nonunits)) ∧

    (∃ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) = ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p) ∧
    (∃ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) = ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p)  := by
  obtain ⟨h₁, h₂⟩ := ResMatchDock.hval_hloc p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ w hw hxj n hy₁ hy₂ hx₁ hx₂ hsp₁ hsp₂ tF htF hor hconv
  obtain ⟨h₃, h₄⟩ := ResMatchDock.attain p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ w hw hxj n hy₁ hy₂ hx₁ hx₂ hsp₁ hsp₂ tF htF hor hconv
  exact ⟨h₁, h₂, h₃, h₄⟩

end S_ModularCurve_DRModelPackage_phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal (solution)
