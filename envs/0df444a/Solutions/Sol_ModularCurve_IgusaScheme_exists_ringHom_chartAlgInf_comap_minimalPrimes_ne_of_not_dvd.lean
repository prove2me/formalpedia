-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_ringHom_chartAlgInf_comap_minimalPrimes_ne_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/5331dc23-04ee-54ba-bdd1-9c0b32b8ac7c

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_minimalPrimes_chartAlgInf_span_eq_pair_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgFin_valuationSubring_pair_levelP
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_prime
import Theorems.Thm_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap
import Theorems.Thm_ModularCurve_DRModel_mem_minimalPrimes_chartAlgInf_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_ringHom_chartAlgInf_comap_minimalPrimes_ne_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_ringHom_chartAlgInf_comap_minimalPrimes_ne_of_not_dvd.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_ringHom_chartAlgInf_comap_minimalPrimes_ne_of_not_dvd.ModularCurve.IgusaScheme"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme.jFull IgusaScheme.chartAlgInf IgusaScheme.jInvChartInf IgusaScheme.coe_jInvChartInf IgusaScheme qExpand jq divisorExpansions modularFunctionFieldFull jqd_mem_full full_degeneracy_le DRModel IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_isFrickeAutFull_of_neZero exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd DRModelPackageLevel.exists_minimalPrimes_chartAlgInf_span_eq_pair_of_valuationSubring_pair DRModelPackageLevel DRModel.exists_chartAlgFin_valuationSubring_pair_levelP exists_valuationSubring_pair_modularFunctionFieldFull_prime DRModel.valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap DRModel.mem_minimalPrimes_chartAlgInf_iff_of_valuationSubring_pair DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull chartAlgInf jInvChartInf coe_jInvChartInf"
namespace CompCompat
p2m_open "ModularCurve.IgusaScheme ModularCurve"

variable (N q : ℕ) [NeZero N] [Fact q.Prime]

theorem full_le : modularFunctionFieldFull q ≤ modularFunctionFieldFull (N * q) :=
  full_degeneracy_le (dvd_mul_left q N)

def fieldIncl : ↥(modularFunctionFieldFull q) →+* ↥(modularFunctionFieldFull (N * q)) :=
  (SubringClass.subtype (modularFunctionFieldFull q)).codRestrict (modularFunctionFieldFull (N * q))
    fun b => full_le N q b.2

theorem coe_fieldIncl (b : ↥(modularFunctionFieldFull q)) :
    ((fieldIncl N q b : ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ) = (b : LaurentSeries ℚ) := by
  rw [fieldIncl, RingHom.codRestrict_apply]; rfl

theorem fieldIncl_jFull : fieldIncl N q (IgusaScheme.jFull q) = IgusaScheme.jFull (N * q) := by
  apply Subtype.ext; rw [coe_fieldIncl]; rfl

theorem fieldIncl_jFull_inv : fieldIncl N q (IgusaScheme.jFull q)⁻¹ = (IgusaScheme.jFull (N * q))⁻¹ := by
  rw [map_inv₀, fieldIncl_jFull]

theorem fieldIncl_mem_adjoin {b : ↥(modularFunctionFieldFull q)}
    (hb : b ∈ Algebra.adjoin ℤ ({(IgusaScheme.jFull q)⁻¹} : Set ↥(modularFunctionFieldFull q))) :
    fieldIncl N q b ∈ Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q)
      ({(IgusaScheme.jFull (N * q))⁻¹} : Set ↥(modularFunctionFieldFull (N * q))) := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    rw [hx, fieldIncl_jFull_inv]
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  | algebraMap r =>
    rw [algebraMap_int_eq, eq_intCast, map_intCast]
    exact Subalgebra.intCast_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem fieldIncl_mem_chartAlgInf {b : ↥(modularFunctionFieldFull q)}
    (hb : b ∈ TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)) :
    fieldIncl N q b ∈ IgusaScheme.chartAlgInf (N * q) q := by
  have hint : IsIntegral ↥(Algebra.adjoin ℤ ({(IgusaScheme.jFull q)⁻¹} : Set ↥(modularFunctionFieldFull q))) b := hb
  let ψ : ↥(Algebra.adjoin ℤ ({(IgusaScheme.jFull q)⁻¹} : Set ↥(modularFunctionFieldFull q))) →+*
      ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q)
        ({(IgusaScheme.jFull (N * q))⁻¹} : Set ↥(modularFunctionFieldFull (N * q)))) :=
    ((fieldIncl N q).comp (Algebra.adjoin ℤ _).val.toRingHom).codRestrict
      (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q) _).toSubring fun x => fieldIncl_mem_adjoin N q x.2
  exact IsIntegral.map_of_comp_eq ψ (fieldIncl N q) (RingHom.ext fun _ => rfl) hint

def incl : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)) →+*
    ↥(IgusaScheme.chartAlgInf (N * q) q) :=
  ((fieldIncl N q).comp (TwoChartIntegralModel.chartAlgInf ℤ _ _).val.toRingHom).codRestrict
    (IgusaScheme.chartAlgInf (N * q) q).toSubring fun b => fieldIncl_mem_chartAlgInf N q b.2

theorem coe_incl (b : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q))) :
    ((incl N q b : ↥(IgusaScheme.chartAlgInf (N * q) q)) : ↥(modularFunctionFieldFull (N * q))) =
      fieldIncl N q (b : ↥(modularFunctionFieldFull q)) := by
  rw [incl, RingHom.codRestrict_apply]; rfl

theorem incl_laurent (b : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q))) :
    (((incl N q b : ↥(IgusaScheme.chartAlgInf (N * q) q)) : ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull q)) : LaurentSeries ℚ) := by
  rw [coe_incl, coe_fieldIncl]

theorem incl_jInvChartInf :
    incl N q (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)) =
      IgusaScheme.jInvChartInf (N * q) q := by
  apply Subtype.ext
  rw [coe_incl, TwoChartIntegralModel.coe_jInvChartInf, fieldIncl_jFull_inv, IgusaScheme.coe_jInvChartInf]

theorem atkinLehner_fieldIncl (hqN : ¬ q ∣ N) (f : ↥(modularFunctionFieldFull q)) :
    atkinLehnerInvolutionFull N q (fieldIncl N q f) = fieldIncl N q (frickeInvolutionFull q f) := by
  have hσ : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
      (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  have hτ : IsFrickeAutFull q (frickeInvolutionFull q) :=
    isFrickeAutFull_frickeInvolutionFull q (exists_isFrickeAutFull_of_neZero q)

  have hfi : ∀ (x : LaurentSeries ℚ) (hx : x ∈ modularFunctionFieldFull q),
      fieldIncl N q ⟨x, hx⟩ = ⟨x, full_le N q hx⟩ := fun x hx => Subtype.ext (coe_fieldIncl N q _)
  suffices h : ∀ (x : LaurentSeries ℚ) (hx : x ∈ IntermediateField.adjoin ℚ (divisorExpansions q)),
      ((atkinLehnerInvolutionFull N q (fieldIncl N q ⟨x, hx⟩) : ↥(modularFunctionFieldFull (N * q))) :
          LaurentSeries ℚ) =
        ((frickeInvolutionFull q ⟨x, hx⟩ : ↥(modularFunctionFieldFull q)) : LaurentSeries ℚ) by
    apply Subtype.ext
    rw [coe_fieldIncl]
    exact h f.1 f.2
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨d, hd0, hdq, rfl⟩ := hx
    rcases (Nat.dvd_prime (Fact.out : q.Prime)).mp hdq with h | h
    ·
      subst h
      have h1 := (hσ 1 inferInstance (one_dvd N)).1
      have h2 := hτ 1 q (one_mul q) inferInstance inferInstance
      rw [hfi, show (⟨qExpand ℚ 1 jq, full_le N q (IntermediateField.subset_adjoin ℚ _ ⟨1, hd0, hdq, rfl⟩)⟩ :
          ↥(modularFunctionFieldFull (N * q))) = ⟨qExpand ℚ 1 jq, jqd_mem_full (N * q)
            (Dvd.dvd.mul_right (one_dvd N) q)⟩ from rfl, h1,
        show (⟨qExpand ℚ 1 jq, IntermediateField.subset_adjoin ℚ _ ⟨1, hd0, hdq, rfl⟩⟩ : ↥(modularFunctionFieldFull q)) =
          ⟨qExpand ℚ 1 jq, jqd_mem_full q (Dvd.intro q (one_mul q))⟩ from rfl, h2]
      change qExpand ℚ (1 * q) jq = qExpand ℚ q jq
      simp only [one_mul]
    ·
      obtain rfl := h.symm
      have h1 := (hσ 1 inferInstance (one_dvd N)).2
      have h2 := hτ q 1 (mul_one q) inferInstance inferInstance
      have e1 : (⟨qExpand ℚ q jq, full_le N q (IntermediateField.subset_adjoin ℚ _ ⟨q, hd0, hdq, rfl⟩)⟩ :
          ↥(modularFunctionFieldFull (N * q))) = ⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q)
            (Nat.mul_dvd_mul_right (one_dvd N) q)⟩ := Subtype.ext (by change qExpand ℚ q jq = qExpand ℚ (1 * q) jq; simp only [one_mul])
      rw [hfi, e1, h1,
        show (⟨qExpand ℚ q jq, IntermediateField.subset_adjoin ℚ _ ⟨q, hd0, hdq, rfl⟩⟩ : ↥(modularFunctionFieldFull q)) =
          ⟨qExpand ℚ q jq, jqd_mem_full q (Dvd.intro 1 (mul_one q))⟩ from rfl, h2]
  | algebraMap r =>
    have e : (⟨algebraMap ℚ (LaurentSeries ℚ) r, IntermediateField.algebraMap_mem _ r⟩ :
        ↥(modularFunctionFieldFull q)) = (r : ↥(modularFunctionFieldFull q)) :=
      Subtype.ext (by rw [SubfieldClass.coe_ratCast]; exact eq_ratCast _ r)
    rw [e, map_ratCast, map_ratCast, map_ratCast, SubfieldClass.coe_ratCast, SubfieldClass.coe_ratCast]
  | add x y hx hy ihx ihy =>
    rw [← AddMemClass.mk_add_mk, map_add, map_add, map_add, AddMemClass.coe_add, AddMemClass.coe_add, ihx, ihy]
  | inv x hx ih =>
    have e : (⟨x⁻¹, inv_mem hx⟩ : ↥(modularFunctionFieldFull q)) = (⟨x, hx⟩ : ↥(modularFunctionFieldFull q))⁻¹ :=
      Subtype.ext (by rw [IntermediateField.coe_inv])
    rw [e, map_inv₀, map_inv₀, map_inv₀, IntermediateField.coe_inv, IntermediateField.coe_inv, ih]
  | mul x y hx hy ihx ihy =>
    rw [← MulMemClass.mk_mul_mk, map_mul, map_mul, map_mul, MulMemClass.coe_mul, MulMemClass.coe_mul, ihx, ihy]

end ModularCurve.IgusaScheme.CompCompat

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme.jFull IgusaScheme.chartAlgInf IgusaScheme.jInvChartInf IgusaScheme.coe_jInvChartInf IgusaScheme qExpand jq divisorExpansions modularFunctionFieldFull jqd_mem_full full_degeneracy_le DRModel IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_isFrickeAutFull_of_neZero exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd DRModelPackageLevel.exists_minimalPrimes_chartAlgInf_span_eq_pair_of_valuationSubring_pair DRModelPackageLevel DRModel.exists_chartAlgFin_valuationSubring_pair_levelP exists_valuationSubring_pair_modularFunctionFieldFull_prime DRModel.valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap DRModel.mem_minimalPrimes_chartAlgInf_iff_of_valuationSubring_pair DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull chartAlgInf jInvChartInf coe_jInvChartInf"
namespace CompCompatC
p2m_open "ModularCurve.IgusaScheme ModularCurve"

private theorem mem_nonunits_comap_iff {K L : Type*} [Field K] [Field L] (A : ValuationSubring L) (f : K →+* L) (x : K) :
    x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero]

theorem comap_minimalPrimes_of_fieldIncl
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (fieldIncl : ↥(modularFunctionFieldFull q) →+* ↥(modularFunctionFieldFull (N * q)))
    (coe_fieldIncl : ∀ f : ↥(modularFunctionFieldFull q), ((fieldIncl f : ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ) = ((f : ↥(modularFunctionFieldFull q)) : LaurentSeries ℚ))
    (incl : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)) →+* ↥(IgusaScheme.chartAlgInf (N * q) q))
    (coe_incl : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)), ((incl b : ↥(IgusaScheme.chartAlgInf (N * q) q)) : ↥(modularFunctionFieldFull (N * q))) = fieldIncl (b : ↥(modularFunctionFieldFull q)))
    (hAL : ∀ f : ↥(modularFunctionFieldFull q), atkinLehnerInvolutionFull N q (fieldIncl f) = fieldIncl (frickeInvolutionFull q f)) :
    ∀ P P' : Ideal ↥(IgusaScheme.chartAlgInf (N * q) q),
      P ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgInf (N * q) q))}).minimalPrimes →
      P' ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgInf (N * q) q))}).minimalPrimes → P ≠ P' →
        Ideal.comap incl P ∈ (Ideal.span {((q : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)))}).minimalPrimes ∧
        Ideal.comap incl P' ∈ (Ideal.span {((q : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)))}).minimalPrimes ∧
        Ideal.comap incl P ≠ Ideal.comap incl P' := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨W', hW'0, hW'1, hW'ne, hW'above, hW'complete⟩ :=
    ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd N q hqN
  obtain ⟨-, P₀, hP₀mem, -, -, hmin⟩ :=
    ModularCurve.DRModelPackageLevel.exists_minimalPrimes_chartAlgInf_span_eq_pair_of_valuationSubring_pair N q hqN
      W' hW'0 hW'1 hW'ne hW'above hW'complete

  obtain ⟨jp, W₀, W₁, hjp, hp₀, hp₁, hne, hgen, hcomplete, ht, -, -⟩ :=
    ModularCurve.DRModel.exists_chartAlgFin_valuationSubring_pair_levelP q
  obtain ⟨W, hW0, hW1, hWne, hWabove, -⟩ := ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_prime q
  have hgauss := (ModularCurve.DRModel.valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap q jp hjp W₀ W₁ hp₀ hp₁ hne
    hgen hcomplete ht).1
  have hW0eq : W 0 = W₀ := by
    ext f
    rw [hW0, hgauss]
  have hW1eq : W 1 = W₁ := by
    rcases hcomplete (W 1) (hWabove 1).1 (fun P hP => (hWabove 1).2.1 P hP) with h | h
    · exact absurd (h.trans hW0eq.symm) hWne.symm
    · exact h

  have hV0 : ∀ f : ↥(modularFunctionFieldFull q), fieldIncl f ∈ W' 0 ↔ f ∈ W₀ := by
    intro f
    rw [hW'0, ← hW0eq, hW0, coe_fieldIncl]
  have hV1 : ∀ f : ↥(modularFunctionFieldFull q), fieldIncl f ∈ W' 1 ↔ f ∈ W₁ := by
    intro f
    rw [hW'1, hAL, hV0, ← hW1eq, hW1, hW0eq]

  have hnu0 : ∀ f : ↥(modularFunctionFieldFull q), fieldIncl f ∈ (W' 0).nonunits ↔ f ∈ W₀.nonunits := by
    intro f
    rw [← mem_nonunits_comap_iff]
    congr! 2
    ext g
    rw [ValuationSubring.mem_comap, hV0]
  have hnu1 : ∀ f : ↥(modularFunctionFieldFull q), fieldIncl f ∈ (W' 1).nonunits ↔ f ∈ W₁.nonunits := by
    intro f
    rw [← mem_nonunits_comap_iff]
    congr! 2
    ext g
    rw [ValuationSubring.mem_comap, hV1]

  have hcomap0 : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)), b ∈ Ideal.comap incl (P₀ 0) ↔ (b : ↥(modularFunctionFieldFull q)) ∈ W₀.nonunits := by
    intro b
    rw [Ideal.mem_comap, hP₀mem, coe_incl, hnu0]
  have hcomap1 : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)), b ∈ Ideal.comap incl (P₀ 1) ↔ (b : ↥(modularFunctionFieldFull q)) ∈ W₁.nonunits := by
    intro b
    rw [Ideal.mem_comap, hP₀mem, coe_incl, hnu1]
  have hiff := ModularCurve.DRModel.mem_minimalPrimes_chartAlgInf_iff_of_valuationSubring_pair q jp hjp W₀ W₁ hp₀ hp₁ hne hgen
    hcomplete ht
  have hmin0 : Ideal.comap incl (P₀ 0) ∈ (Ideal.span {((q : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)))}).minimalPrimes := (hiff _).2 (Or.inl hcomap0)
  have hmin1 : Ideal.comap incl (P₀ 1) ∈ (Ideal.span {((q : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)))}).minimalPrimes := (hiff _).2 (Or.inr hcomap1)

  have hneq : Ideal.comap incl (P₀ 0) ≠ Ideal.comap incl (P₀ 1) := by
    intro heq
    have hall : ∀ 𝔭 ∈ (Ideal.span {((q : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)))}).minimalPrimes, 𝔭 = Ideal.comap incl (P₀ 0) := by
      intro 𝔭 h𝔭
      rcases (hiff 𝔭).1 h𝔭 with h | h
      · ext b; rw [h, hcomap0]
      · ext b; rw [h, heq, hcomap1]
    have h2 := (ModularCurve.DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int q).2.2.2
    have hsub : (Ideal.span {((q : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)))}).minimalPrimes ⊆ {Ideal.comap incl (P₀ 0)} :=
      fun 𝔭 h => hall 𝔭 h
    have hle := Set.ncard_le_ncard hsub (Set.finite_singleton _)
    rw [h2, Set.ncard_singleton] at hle
    omega

  intro P P' hP hP' hPP'
  rw [hmin] at hP hP'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP hP'
  rcases hP with rfl | rfl <;> rcases hP' with rfl | rfl
  · exact absurd rfl hPP'
  · exact ⟨hmin0, hmin1, hneq⟩
  · exact ⟨hmin1, hmin0, hneq.symm⟩
  · exact absurd rfl hPP'

end ModularCurve.IgusaScheme.CompCompatC

open ModularCurve.IgusaScheme.CompCompat in

theorem solution
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) :
    ∃ incl : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)) →+* ↥(IgusaScheme.chartAlgInf (N * q) q),
      (∀ b, (((incl b : ↥(IgusaScheme.chartAlgInf (N * q) q)) : ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull q)) : LaurentSeries ℚ)) ∧
      incl (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)) =
        IgusaScheme.jInvChartInf (N * q) q ∧
      ∀ P P' : Ideal ↥(IgusaScheme.chartAlgInf (N * q) q),
        P ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgInf (N * q) q))}).minimalPrimes →
        P' ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgInf (N * q) q))}).minimalPrimes → P ≠ P' →
          Ideal.comap incl P ∈ (Ideal.span {((q : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)))}).minimalPrimes ∧
          Ideal.comap incl P' ∈ (Ideal.span {((q : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)))}).minimalPrimes ∧
          Ideal.comap incl P ≠ Ideal.comap incl P' :=
  ⟨incl N q, incl_laurent N q, incl_jInvChartInf N q,
    ModularCurve.IgusaScheme.CompCompatC.comap_minimalPrimes_of_fieldIncl N q hqN (fieldIncl N q) (coe_fieldIncl N q)
      (incl N q) (coe_incl N q) (atkinLehner_fieldIncl N q hqN)⟩

end

end S_ModularCurve_IgusaScheme_exists_ringHom_chartAlgInf_comap_minimalPrimes_ne_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_ringHom_chartAlgInf_comap_minimalPrimes_ne_of_not_dvd (solution)
