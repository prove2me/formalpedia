-- Prove2me | solution 1 for ModularCurve.mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/173ae549-f514-5687-935c-096501ff1d78

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
p2m_open "AlgebraicCurve ModularCurve~coeffMap_ofPowerSeries P2MW.S_ModularCurve_mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC jNum constantCoeff_jNum jNumQ constantCoeff_jNumQ ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single jqModC exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero coeff_jqModC_neg_one transcendental_jqModC finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index"
namespace GaussLoc
p2m_open "ModularCurve~coeffMap_ofPowerSeries"

abbrev Rp (p : ℕ) : Type := ↥(GaloisRep.ratLocalizedAt p)

scoped instance (p : ℕ) [hp : Fact p.Prime] : IsDiscreteValuationRing (Rp p) :=
  GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp.out

theorem maximalIdeal_eq (p : ℕ) [hp : Fact p.Prime] :
    IsLocalRing.maximalIdeal (Rp p) = Ideal.span {(p : Rp p)} :=
  GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p hp.out

theorem residue_eq_zero_of_mem (p : ℕ) [hp : Fact p.Prime] {r : Rp p} (hr : r ∈ IsLocalRing.maximalIdeal (Rp p)) :
    GaloisRep.ratLocalizedAtResidue p r = 0 := by
  rw [maximalIdeal_eq, Ideal.mem_span_singleton] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem isUnit_of_residue_ne_zero (p : ℕ) [hp : Fact p.Prime] {r : Rp p}
    (hr : GaloisRep.ratLocalizedAtResidue p r ≠ 0) : IsUnit r := by
  by_contra h
  exact hr (residue_eq_zero_of_mem p ((IsLocalRing.mem_maximalIdeal _).mpr h))

theorem exists_eq_mul_of_residue_eq_zero (p : ℕ) [hp : Fact p.Prime] {r : Rp p}
    (hr : GaloisRep.ratLocalizedAtResidue p r = 0) : ∃ s : Rp p, r = p * s := by
  have h : ¬ IsUnit r := fun hu => (hu.map (GaloisRep.ratLocalizedAtResidue p)).ne_zero hr
  have hm : r ∈ IsLocalRing.maximalIdeal (Rp p) := (IsLocalRing.mem_maximalIdeal _).mpr h
  rw [maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact hm

abbrev psQ (p : ℕ) (x : PowerSeries (Rp p)) : LaurentSeries ℚ :=
  HahnSeries.ofPowerSeries ℤ ℚ (x.map (GaloisRep.ratLocalizedAt p).subtype)

theorem psQ_injective (p : ℕ) : Function.Injective (psQ p) := fun x y h =>
  PowerSeries.map_injective _ Subtype.coe_injective (HahnSeries.ofPowerSeries_injective h)

theorem subtype_comp_intCast (p : ℕ) :
    (GaloisRep.ratLocalizedAt p).subtype.comp (Int.castRingHom (Rp p)) = Int.castRingHom ℚ :=
  RingHom.ext_int _ _

theorem residue_comp_intCast (p : ℕ) [Fact p.Prime] :
    (GaloisRep.ratLocalizedAtResidue p).comp (Int.castRingHom (Rp p)) = Int.castRingHom (ZMod p) :=
  RingHom.ext_int _ _

theorem jqModC_rat_ne_zero : jqModC ℚ ≠ 0 := by
  intro h
  have := congrArg (fun s : LaurentSeries ℚ => s.coeff (-1)) h
  simp only [coeff_jqModC_neg_one, HahnSeries.coeff_zero] at this
  exact one_ne_zero this

theorem single_one_mul_jqModC :
    HahnSeries.single (1 : ℤ) (1 : ℚ) * jqModC ℚ = HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) := by
  rw [jqModC, ← mul_assoc, HahnSeries.single_mul_single, add_neg_cancel, one_mul]
  exact one_mul _

theorem map_map_ps {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C] (f : A →+* B) (g : B →+* C)
    (x : PowerSeries A) : (x.map f).map g = x.map (g.comp f) := by
  ext n
  simp only [PowerSeries.coeff_map, RingHom.comp_apply]

theorem psQ_jNum (p : ℕ) : psQ p (jNum.map (Int.castRingHom (Rp p))) = HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) := by
  rw [psQ, map_map_ps, subtype_comp_intCast]

theorem psQ_X (p : ℕ) : psQ p PowerSeries.X = HahnSeries.single (1 : ℤ) (1 : ℚ) := by
  rw [psQ, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

theorem jNum_map_residue_ne_zero (p : ℕ) [Fact p.Prime] :
    (jNum.map (Int.castRingHom (Rp p))).map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 := by
  rw [map_map_ps, residue_comp_intCast]
  intro h
  have := congrArg PowerSeries.constantCoeff h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one, map_zero] at this
  exact one_ne_zero this

theorem coeff_zero_inv_jqModC : ((jqModC ℚ)⁻¹).coeff 0 = 0 := by
  have hu : jNumQ * jNumQ.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNumQ]; rfl)
  have hj : jqModC ℚ = HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ := rfl
  have hinv : (jqModC ℚ)⁻¹ = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X * jNumQ.invOfUnit 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [hj, map_mul, HahnSeries.ofPowerSeries_X, mul_mul_mul_comm, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
      ← map_mul, hu, map_one (HahnSeries.ofPowerSeries ℤ ℚ), mul_one]
    rfl
  rw [hinv, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_X_mul]

abbrev FG (Γ : Subgroup SL(2, ℤ)) : Type := ↥(qExpFunctionFieldC ℚ Γ)

abbrev OO (Γ : Subgroup SL(2, ℤ)) (p : ℕ) (j : FG Γ) [Fact (j ≠ 0)] : Type :=
  ↥(TwoChartIntegralModel.chartAlgInf (Rp p) (FG Γ) j)

section Frame

variable (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [hp : Fact p.Prime]
variable (j : FG Γ) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
variable (W₀ : ValuationSubring (FG Γ))
  (hW₀ : ∀ f : FG Γ, f ∈ W₀ ↔
    ∃ a a' : PowerSeries (Rp p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      (f : LaurentSeries ℚ) * psQ p a' = psQ p a)

include hW₀ in

theorem algebraMap_mem (r : Rp p) : algebraMap (Rp p) (FG Γ) r ∈ W₀ := by
  rw [hW₀]
  refine ⟨PowerSeries.C r, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
  rw [psQ, psQ, map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
  have h1 : ((algebraMap (Rp p) (FG Γ) r : FG Γ) : LaurentSeries ℚ) = HahnSeries.single 0 (r : ℚ) := by
    first
    | exact algebraMap_laurentSeries_eq_single (r : ℚ)
    | rfl
    | (change algebraMap ℚ (LaurentSeries ℚ) (r : ℚ) = _; exact algebraMap_laurentSeries_eq_single ℚ (r : ℚ))
  rw [h1]
  rfl

include hj hW₀ in

theorem inv_j_mem : (j⁻¹ : FG Γ) ∈ W₀ := by
  rw [hW₀]
  refine ⟨PowerSeries.X, jNum.map (Int.castRingHom (Rp p)), jNum_map_residue_ne_zero p, ?_⟩
  rw [psQ_jNum, psQ_X, ← single_one_mul_jqModC, ← hj]
  show ((j : FG Γ) : LaurentSeries ℚ)⁻¹ * (HahnSeries.single 1 1 * (j : LaurentSeries ℚ)) = HahnSeries.single 1 1
  rw [mul_left_comm, inv_mul_cancel₀ (hj ▸ jqModC_rat_ne_zero), mul_one]

include hj hW₀ in

theorem j_mem : (j : FG Γ) ∈ W₀ := by
  rw [hW₀]
  refine ⟨jNum.map (Int.castRingHom (Rp p)), PowerSeries.X, by rw [PowerSeries.map_X]; exact PowerSeries.X_ne_zero, ?_⟩
  rw [psQ_jNum, psQ_X, ← single_one_mul_jqModC, ← hj, mul_comm]

include hj hW₀ in

theorem adjoin_subset (x : FG Γ) (hx : x ∈ Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))) : x ∈ W₀ := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact inv_j_mem Γ p j hj W₀ hW₀
  | algebraMap r => exact algebraMap_mem Γ p W₀ hW₀ r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

include hj hW₀ in

theorem coe_mem (b : OO Γ p j) : (b : FG Γ) ∈ W₀ := by
  have hb : IsIntegral (Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))) (b : FG Γ) := b.2
  let φ : ↥(Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))) →+* ↥W₀ :=
    (algebraMap ↥(Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))) (FG Γ)).codRestrict W₀.toSubring
      (fun x => adjoin_subset Γ p j hj W₀ hW₀ x x.2)
  have hcomp : (algebraMap ↥W₀ (FG Γ)).comp φ = (RingHom.id (FG Γ)).comp (algebraMap _ (FG Γ)) :=
    RingHom.ext fun _ => rfl
  have hint : IsIntegral ↥W₀ (b : FG Γ) := hb.map_of_comp_eq φ (RingHom.id (FG Γ)) hcomp
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W₀) (K := FG Γ)).mp hint
  rw [← hy]
  exact y.2

def toW₀ : OO Γ p j →+* ↥W₀ :=
  (algebraMap (OO Γ p j) (FG Γ)).codRestrict W₀.toSubring (fun b => coe_mem Γ p j hj W₀ hW₀ b)

def centre : Ideal (OO Γ p j) := Ideal.comap (toW₀ Γ p j hj W₀ hW₀) (IsLocalRing.maximalIdeal ↥W₀)

theorem mem_centre_iff (b : OO Γ p j) : b ∈ centre Γ p j hj W₀ hW₀ ↔ (b : FG Γ) ∈ W₀.nonunits := by
  rw [centre, Ideal.mem_comap, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · intro h; exact ⟨coe_mem Γ p j hj W₀ hW₀ b, h⟩
  · rintro ⟨_, h⟩; exact h

theorem mem_centre_iff_not_isUnit (b : OO Γ p j) :
    b ∈ centre Γ p j hj W₀ hW₀ ↔ ¬ IsUnit (toW₀ Γ p j hj W₀ hW₀ b) := by
  rw [centre, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem centre_isPrime : (centre Γ p j hj W₀ hW₀).IsPrime := by
  unfold centre
  exact Ideal.comap_isPrime _ _

include hW₀ in

theorem inv_natCast_not_mem : ((p : FG Γ))⁻¹ ∉ W₀ := by
  rw [hW₀]
  rintro ⟨a, a', ha', h⟩
  apply ha'
  have hp0 : (p : FG Γ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have h3 : ((p : FG Γ) : LaurentSeries ℚ) * psQ p a = psQ p ((p : PowerSeries (Rp p)) * a) := by
    rw [psQ, psQ, map_mul, map_natCast, map_mul, map_natCast]
    push_cast
    rfl
  have h2 : psQ p a' = psQ p ((p : PowerSeries (Rp p)) * a) := by
    rw [← h3, ← h, ← mul_assoc]
    have hpp : ((p : FG Γ) : LaurentSeries ℚ) * ((((p : FG Γ))⁻¹ : FG Γ) : LaurentSeries ℚ) = 1 := by
      rw [← show (((p : FG Γ) * (p : FG Γ)⁻¹ : FG Γ) : LaurentSeries ℚ) =
          ((p : FG Γ) : LaurentSeries ℚ) * ((((p : FG Γ))⁻¹ : FG Γ) : LaurentSeries ℚ) from by push_cast; rfl,
        mul_inv_cancel₀ hp0]
      rfl
    rw [hpp, one_mul]
  rw [psQ_injective p h2, map_mul, map_natCast, ← map_natCast (PowerSeries.C (R := ZMod p)) p, ZMod.natCast_self,
    map_zero, zero_mul]

theorem natCast_mem_centre : (p : OO Γ p j) ∈ centre Γ p j hj W₀ hW₀ := by
  rw [mem_centre_iff_not_isUnit]
  intro hu
  obtain ⟨u, hu⟩ := hu
  apply inv_natCast_not_mem Γ p W₀ hW₀
  have hcoe : ((toW₀ Γ p j hj W₀ hW₀ (p : OO Γ p j) : ↥W₀) : FG Γ) = (p : FG Γ) := by
    rw [map_natCast]; norm_cast
  have h1 : ((u⁻¹ : (↥W₀)ˣ) : ↥W₀) * (u : ↥W₀) = 1 := Units.inv_mul u
  rw [hu] at h1
  have h2 := congrArg (fun z : ↥W₀ => (z : FG Γ)) h1
  simp only [Subring.coe_mul, MulMemClass.coe_mul, Subring.coe_one, OneMemClass.coe_one, hcoe] at h2
  have hp0 : (p : FG Γ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : (((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : FG Γ) = (p : FG Γ)⁻¹ := eq_inv_of_mul_eq_one_left h2
  rw [← this]
  exact ((u⁻¹ : (↥W₀)ˣ) : ↥W₀).2

include hj hW₀ in

theorem jInv_not_mem_centre : TwoChartIntegralModel.jInvChartInf (Rp p) (FG Γ) j ∉ centre Γ p j hj W₀ hW₀ := by
  rw [mem_centre_iff_not_isUnit, not_not]
  refine IsUnit.of_mul_eq_one ⟨(j : FG Γ), j_mem Γ p j hj W₀ hW₀⟩ (Subtype.ext ?_)
  show ((j⁻¹ : FG Γ)) * (j : FG Γ) = 1
  exact inv_mul_cancel₀ (Fact.out : j ≠ 0)

include hj in
omit hp in
theorem coeff_zero_jInv :
    (((TwoChartIntegralModel.jInvChartInf (Rp p) (FG Γ) j : FG Γ)) : LaurentSeries ℚ).coeff 0 = 0 := by
  rw [TwoChartIntegralModel.coe_jInvChartInf]
  rw [show ((j⁻¹ : FG Γ) : LaurentSeries ℚ) = ((j : FG Γ) : LaurentSeries ℚ)⁻¹ from by push_cast; rfl, hj]
  exact coeff_zero_inv_jqModC

omit hp in

theorem exists_powerSeries_of_forall_coeff_neg_eq_zero (y : LaurentSeries (Rp p))
    (hy : ∀ n : ℤ, n < 0 → y.coeff n = 0) :
    ∃ Y : PowerSeries (Rp p), HahnSeries.ofPowerSeries ℤ (Rp p) Y = y := by
  refine ⟨PowerSeries.mk fun n => y.coeff n, HahnSeries.ext (funext fun k => ?_)⟩
  rcases lt_or_ge k 0 with hk | hk
  · rw [hy k hk]
    exact ofPowerSeries_coeff_of_neg (PowerSeries.mk fun n => y.coeff n) hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

theorem coeffMap_ofPowerSeries {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (Y : PowerSeries A) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ A Y) = HahnSeries.ofPowerSeries ℤ B (Y.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases lt_or_ge k 0 with hk | hk
  · rw [ofPowerSeries_coeff_of_neg Y hk, ofPowerSeries_coeff_of_neg (Y.map f) hk, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

include hj hW₀ in

theorem exists_psQ_eq (b : OO Γ p j) : ∃ Y : PowerSeries (Rp p), psQ p Y = ((b : FG Γ) : LaurentSeries ℚ) := by
  obtain ⟨y, hy⟩ := (exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC Γ p j hj).2 b
  have hj' : ∀ n : ℤ, n ≤ 0 → ((j : FG Γ) : LaurentSeries ℚ)⁻¹.coeff n = 0 := by
    intro n hn
    rw [hj]
    rcases hn.lt_or_eq with hlt | rfl
    · have hu : jNumQ * jNumQ.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNumQ]; rfl)
      have hjq : jqModC ℚ = HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ := rfl
      have hinv : (jqModC ℚ)⁻¹ = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X * jNumQ.invOfUnit 1) := by
        apply inv_eq_of_mul_eq_one_right
        rw [hjq, map_mul, HahnSeries.ofPowerSeries_X, mul_mul_mul_comm, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
          ← map_mul, hu, map_one (HahnSeries.ofPowerSeries ℤ ℚ), mul_one]
        rfl
      rw [hinv]
      exact ofPowerSeries_coeff_of_neg _ hlt
    · exact coeff_zero_inv_jqModC
  obtain ⟨ε, hε⟩ := exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero (qExpFunctionFieldC ℚ Γ) p j hj'
  have hneg : ∀ n : ℤ, n < 0 → y.coeff n = 0 := by
    intro n hn
    have h := (hε b).1 n hn
    rw [← hy, coeffMap_coeff] at h
    exact Subtype.coe_injective (by simpa using h)
  obtain ⟨Y, hY⟩ := exists_powerSeries_of_forall_coeff_neg_eq_zero p y hneg
  refine ⟨Y, ?_⟩
  rw [← hy, ← hY, psQ, coeffMap_ofPowerSeries]
  rfl

include hj hW₀ in

theorem isUnit_toW₀_of_isUnit_coeff (b : OO Γ p j) (Y : PowerSeries (Rp p)) (hY : psQ p Y = ((b : FG Γ) : LaurentSeries ℚ))
    (hu : IsUnit (PowerSeries.constantCoeff Y)) : IsUnit (toW₀ Γ p j hj W₀ hW₀ b) := by
  obtain ⟨u, hu⟩ := hu
  have hYinv : Y * Y.invOfUnit u = 1 := PowerSeries.mul_invOfUnit Y u hu.symm

  have hb0 : (b : FG Γ) ≠ 0 := by
    intro h0
    have : psQ p Y = 0 := by rw [hY, h0]; rfl
    have hY0 : Y = 0 := psQ_injective p (by rw [this]; simp [psQ])
    rw [hY0, map_zero] at hu
    exact u.ne_zero hu
  have hinv : ((b : FG Γ))⁻¹ ∈ W₀ := by
    rw [hW₀]
    refine ⟨Y.invOfUnit u, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
    rw [show psQ p 1 = 1 from by simp [psQ], mul_one]
    have hprod : psQ p Y * psQ p (Y.invOfUnit u) = 1 := by
      rw [show psQ p Y * psQ p (Y.invOfUnit u) = psQ p (Y * Y.invOfUnit u) from by simp [psQ], hYinv]
      simp [psQ]
    rw [eq_inv_of_mul_eq_one_right hprod, hY]
    norm_cast
  refine IsUnit.of_mul_eq_one ⟨((b : FG Γ))⁻¹, hinv⟩ (Subtype.ext ?_)
  show (b : FG Γ) * (b : FG Γ)⁻¹ = 1
  exact mul_inv_cancel₀ hb0

include hj hW₀ in

theorem coeff_zero_of_mem_centre (b : OO Γ p j) (hb : b ∈ centre Γ p j hj W₀ hW₀) :
    ∃ r : ℚ, r ∈ GaloisRep.ratLocalizedAt p ∧ (((b : FG Γ)) : LaurentSeries ℚ).coeff 0 = (p : ℚ) * r := by
  obtain ⟨Y, hY⟩ := exists_psQ_eq Γ p j hj W₀ hW₀ b
  have hres : GaloisRep.ratLocalizedAtResidue p (PowerSeries.constantCoeff Y) = 0 := by
    by_contra hne
    exact (mem_centre_iff_not_isUnit Γ p j hj W₀ hW₀ b).mp hb
      (isUnit_toW₀_of_isUnit_coeff Γ p j hj W₀ hW₀ b Y hY (isUnit_of_residue_ne_zero p hne))
  obtain ⟨s, hs⟩ := exists_eq_mul_of_residue_eq_zero p hres
  refine ⟨(s : ℚ), s.2, ?_⟩
  rw [← hY, psQ, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, hs]
  push_cast
  rfl

def U : PowerSeries (Rp p) := PowerSeries.X * (jNum.map (Int.castRingHom (Rp p))).invOfUnit 1

theorem constantCoeff_jNum_map : PowerSeries.constantCoeff (jNum.map (Int.castRingHom (Rp p))) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one]

theorem jNum_map_mul_invOfUnit : (jNum.map (Int.castRingHom (Rp p))) * (jNum.map (Int.castRingHom (Rp p))).invOfUnit 1 = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNum_map]; rfl)

include hj in
theorem psQ_U : psQ p (U p) = ((j : FG Γ) : LaurentSeries ℚ)⁻¹ := by
  rw [hj]
  symm
  apply inv_eq_of_mul_eq_one_right
  have h1 : jqModC ℚ = HahnSeries.single (-1 : ℤ) 1 * psQ p (jNum.map (Int.castRingHom (Rp p))) := by
    rw [psQ_jNum]; rfl
  rw [h1, U, show psQ p (PowerSeries.X * (jNum.map (Int.castRingHom (Rp p))).invOfUnit 1) =
      psQ p PowerSeries.X * psQ p ((jNum.map (Int.castRingHom (Rp p))).invOfUnit 1) from by simp [psQ],
    psQ_X, mul_mul_mul_comm, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
    show psQ p (jNum.map (Int.castRingHom (Rp p))) * psQ p ((jNum.map (Int.castRingHom (Rp p))).invOfUnit 1) =
      psQ p ((jNum.map (Int.castRingHom (Rp p))) * (jNum.map (Int.castRingHom (Rp p))).invOfUnit 1) from by simp [psQ],
    jNum_map_mul_invOfUnit]
  simp [psQ]

theorem coeff_U_zero : PowerSeries.coeff 0 (U p) = 0 := by
  rw [U, PowerSeries.coeff_zero_X_mul]

theorem coeff_U_one : PowerSeries.coeff 1 (U p) = 1 := by
  rw [U, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h := congrArg PowerSeries.constantCoeff (jNum_map_mul_invOfUnit p)
  rw [map_mul, constantCoeff_jNum_map, one_mul, map_one] at h
  exact h

theorem coeff_pow_of_coeff_zero_eq_zero {k : Type*} [CommRing k] (V : PowerSeries k) (hV0 : PowerSeries.coeff 0 V = 0)
    (i m : ℕ) : PowerSeries.coeff m (V ^ i) = if i ≤ m then PowerSeries.coeff (m - i) ((PowerSeries.mk fun n => PowerSeries.coeff (n + 1) V) ^ i) else 0 := by
  have hV : V = PowerSeries.X * PowerSeries.mk fun n => PowerSeries.coeff (n + 1) V := by
    have h := PowerSeries.eq_X_mul_shift_add_const V
    rw [show PowerSeries.constantCoeff V = 0 from by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hV0], map_zero,
      add_zero] at h
    exact h
  conv_lhs => rw [hV, mul_pow]
  rw [PowerSeries.coeff_X_pow_mul']

theorem coeff_natTrailingDegree_eval₂ {k : Type*} [CommRing k] (Q : Polynomial k) (V : PowerSeries k)
    (hV0 : PowerSeries.coeff 0 V = 0) (hV1 : PowerSeries.coeff 1 V = 1) :
    PowerSeries.coeff Q.natTrailingDegree (Q.eval₂ (PowerSeries.C) V) = Q.trailingCoeff := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  rw [Polynomial.eval₂_eq_sum_range, map_sum]
  rw [Finset.sum_eq_single Q.natTrailingDegree]
  · rw [PowerSeries.coeff_C_mul, coeff_pow_of_coeff_zero_eq_zero V hV0, if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
    rw [show PowerSeries.constantCoeff (PowerSeries.mk fun n => PowerSeries.coeff (n + 1) V) = 1 from by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, zero_add, hV1], one_pow, mul_one]
    rfl
  · intro i _ hi
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt, map_zero, zero_mul, map_zero]
    · rw [PowerSeries.coeff_C_mul, coeff_pow_of_coeff_zero_eq_zero V hV0, if_neg (not_le.mpr hgt), mul_zero]
  · intro h
    exfalso
    exact h (Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.natTrailingDegree_le_natDegree Q)))

theorem eval₂_ne_zero_of_map_ne_zero {k : Type*} [CommRing k] (Q : Polynomial k) (hQ : Q ≠ 0) (V : PowerSeries k)
    (hV0 : PowerSeries.coeff 0 V = 0) (hV1 : PowerSeries.coeff 1 V = 1) : Q.eval₂ (PowerSeries.C) V ≠ 0 := by
  intro h
  have := coeff_natTrailingDegree_eval₂ Q V hV0 hV1
  rw [h, map_zero] at this
  exact (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hQ) this.symm

include hj hW₀ in

theorem aeval_mem_and_inv_mem (P : Polynomial (Rp p)) (hP : P.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0) :
    Polynomial.aeval (j⁻¹ : FG Γ) P ∈ W₀ ∧ (Polynomial.aeval (j⁻¹ : FG Γ) P)⁻¹ ∈ W₀ := by
  have hmemW : Polynomial.aeval (j⁻¹ : FG Γ) P ∈ W₀ :=
    adjoin_subset Γ p j hj W₀ hW₀ _ (Polynomial.aeval_mem_adjoin_singleton (Rp p) (j⁻¹ : FG Γ))
  refine ⟨hmemW, ?_⟩

  set G : PowerSeries (Rp p) := P.eval₂ PowerSeries.C (U p) with hG
  let ψ : PowerSeries (Rp p) →+* LaurentSeries ℚ :=
    (HahnSeries.ofPowerSeries ℤ ℚ).comp (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype)
  have hψ : ∀ x, psQ p x = ψ x := fun _ => rfl
  let ι : FG Γ →+* LaurentSeries ℚ := (qExpFunctionFieldC ℚ Γ).toSubfield.subtype
  have hι : ∀ y : FG Γ, ι y = (y : LaurentSeries ℚ) := fun _ => rfl
  have hexp : psQ p G = ((Polynomial.aeval (j⁻¹ : FG Γ) P : FG Γ) : LaurentSeries ℚ) := by
    have hc : ψ.comp PowerSeries.C = ι.comp (algebraMap (Rp p) (FG Γ)) := by
      refine RingHom.ext fun r => ?_
      show psQ p (PowerSeries.C r) = ((algebraMap (Rp p) (FG Γ) r : FG Γ) : LaurentSeries ℚ)
      rw [psQ, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]
      rfl
    have h2 : ψ (U p) = ι (j⁻¹ : FG Γ) := by
      rw [← hψ, psQ_U Γ p j hj]
      rfl
    rw [hψ, hG, Polynomial.hom_eval₂, hc, h2, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def]
    rfl
  have hGbar : G.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 := by
    rw [hG, Polynomial.hom_eval₂, show (PowerSeries.map (GaloisRep.ratLocalizedAtResidue p)).comp PowerSeries.C =
        PowerSeries.C.comp (GaloisRep.ratLocalizedAtResidue p) from
        RingHom.ext fun r => by rw [RingHom.comp_apply, RingHom.comp_apply, PowerSeries.map_C],
      ← Polynomial.eval₂_map]
    refine eval₂_ne_zero_of_map_ne_zero _ hP _ ?_ ?_
    · rw [PowerSeries.coeff_map, coeff_U_zero, map_zero]
    · rw [PowerSeries.coeff_map, coeff_U_one, map_one]
  have hG0 : psQ p G ≠ 0 := by
    intro h0
    apply hGbar
    have : G = 0 := psQ_injective p (by rw [h0]; simp [psQ])
    rw [this, map_zero]
  rw [hW₀]
  refine ⟨1, G, hGbar, ?_⟩
  rw [show psQ p 1 = 1 from by simp [psQ], hexp, ← hι, ← hι, map_inv₀, inv_mul_cancel₀]
  rw [hι, ← hexp]
  exact hG0

include hj hW₀ in

theorem aeval_mem_and_inv_mem' (P : Polynomial (Rp p)) (hP : P.map (IsLocalRing.residue (Rp p)) ≠ 0) :
    Polynomial.aeval (j⁻¹ : FG Γ) P ∈ W₀ ∧ (Polynomial.aeval (j⁻¹ : FG Γ) P)⁻¹ ∈ W₀ := by
  refine aeval_mem_and_inv_mem Γ p j hj W₀ hW₀ P ?_
  intro h0
  apply hP
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff]
  have hn : GaloisRep.ratLocalizedAtResidue p (P.coeff n) = 0 := by
    have := congrArg (fun Q => Polynomial.coeff Q n) h0
    simpa [Polynomial.coeff_map] using this
  exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu => (hu.map (GaloisRep.ratLocalizedAtResidue p)).ne_zero hn

include hW₀ in

theorem algebraMap_mem_nonunits (a : Rp p) (ha : a ∈ IsLocalRing.maximalIdeal (Rp p)) :
    algebraMap (Rp p) (FG Γ) a ∈ W₀.nonunits := by
  rw [maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [map_mul, map_natCast]

  have hpW : (p : FG Γ) ∈ W₀ := by
    have := algebraMap_mem Γ p W₀ hW₀ (p : Rp p)
    rwa [map_natCast] at this
  have hpnu : (p : FG Γ) ∈ W₀.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    by_contra hle
    push_neg at hle
    have h1 : W₀.valuation (p : FG Γ) = 1 := le_antisymm ((W₀.valuation_le_one_iff _).mpr hpW) hle
    apply inv_natCast_not_mem Γ p W₀ hW₀
    rw [← W₀.valuation_le_one_iff, map_inv₀, h1, inv_one]
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hpnu ⊢
  obtain ⟨hp1, hp2⟩ := hpnu
  have hr := algebraMap_mem Γ p W₀ hW₀ r
  refine ⟨mul_mem hp1 hr, ?_⟩
  have : (⟨(p : FG Γ) * algebraMap (Rp p) (FG Γ) r, mul_mem hp1 hr⟩ : ↥W₀) =
      ⟨(p : FG Γ), hp1⟩ * ⟨algebraMap (Rp p) (FG Γ) r, hr⟩ := rfl
  rw [this]
  exact Ideal.mul_mem_right _ _ hp2

theorem transcendental_of_subsingleton_ratAlgebra {F : Type*} [Field F] {i₁ : Algebra ℚ F}
    (i₂ : Algebra ℚ F) {x : F} (h : @Transcendental ℚ F _ _ i₁ x) : @Transcendental ℚ F _ _ i₂ x := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

include hj in
omit hp in

theorem transcendental_inv_j : Transcendental (Rp p) (j⁻¹ : FG Γ) := by
  have h0 := ModularCurve.transcendental_jqModC ℚ
  rw [← hj] at h0
  have hQ0 := mt (IntermediateField.isAlgebraic_iff (K := ℚ) (S := qExpFunctionFieldC ℚ Γ) (x := j)).mp h0
  have hQ : Transcendental ℚ (j : FG Γ) := transcendental_of_subsingleton_ratAlgebra _ hQ0
  have hQ' : Transcendental ℚ (j⁻¹ : FG Γ) := by
    intro halg
    exact hQ (by simpa using halg.inv)
  intro halg
  exact hQ' (halg.extendScalars (R := Rp p) (S := ℚ) Subtype.val_injective)

include hj in
omit hp in

theorem finiteDimensional_adjoin_inv_j [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    FiniteDimensional ↥(IntermediateField.adjoin ℚ ({(j⁻¹ : ↥(qExpFunctionFieldC ℚ Γ))} : Set ↥(qExpFunctionFieldC ℚ Γ)))
      ↥(qExpFunctionFieldC ℚ Γ) := by
  have h := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ Γ hT Γ le_rfl
    (fun γ hγ => Or.inl hγ) j hj).1
  have heq : IntermediateField.adjoin ℚ ({(j⁻¹ : ↥(qExpFunctionFieldC ℚ Γ))} : Set ↥(qExpFunctionFieldC ℚ Γ)) =
      IntermediateField.adjoin ℚ ({(j : ↥(qExpFunctionFieldC ℚ Γ))} : Set ↥(qExpFunctionFieldC ℚ Γ)) := by
    apply le_antisymm
    · exact IntermediateField.adjoin_simple_le_iff.mpr (inv_mem (IntermediateField.mem_adjoin_simple_self ℚ _))
    · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
      have := inv_mem (IntermediateField.mem_adjoin_simple_self ℚ (j⁻¹ : ↥(qExpFunctionFieldC ℚ Γ)))
      rwa [inv_inv] at this
  rw [heq]
  convert h
  all_goals exact Subsingleton.elim _ _

end Frame

end ModularCurve.GaussLoc
p2m_reactivate "P2MW.S_ModularCurve_mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre.ModularCurve P2MW.S_ModularCurve_mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre.ModularCurve.GaussLoc"
p2m_reactivate "P2MW.S_ModularCurve_mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre.ModularCurve"

open ModularCurve.GaussLoc in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ Γ))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ Γ), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))
    (𝔮 : Ideal ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))
    (h𝔮 : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
      b ∈ 𝔮 ↔ (b : ↥(qExpFunctionFieldC ℚ Γ)) ∈ W₀.nonunits)
    (f : ↥(qExpFunctionFieldC ℚ Γ)) :
    f ∈ W₀ ↔ ∃ a b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
      b ∉ 𝔮 ∧ f * (b : ↥(qExpFunctionFieldC ℚ Γ)) = (a : ↥(qExpFunctionFieldC ℚ Γ)) := by
  haveI : Fact ((j⁻¹ : FG Γ) ≠ 0) := ⟨inv_ne_zero Fact.out⟩
  haveI : IsFractionRing (Rp p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  have htj := transcendental_inv_j Γ p j hj
  have hFD := finiteDimensional_adjoin_inv_j Γ j hj hT
  haveI := hFD
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({(j⁻¹ : FG Γ)} : Set (FG Γ))) (FG Γ) :=
    Algebra.IsSeparable.of_integral _ _
  have H := AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
    (Rp p) ℚ (FG Γ) (j⁻¹ : FG Γ) htj hFD hsep W₀
    (algebraMap_mem Γ p W₀ hW₀) (algebraMap_mem_nonunits Γ p W₀ hW₀)
    (aeval_mem_and_inv_mem' Γ p j hj W₀ hW₀)
  obtain ⟨-, ⟨𝔓, -, -, h𝔓mem, -, hloc⟩, -⟩ := H
  have h𝔮𝔓 : 𝔮 = 𝔓 := Ideal.ext fun b => (h𝔮 b).trans (h𝔓mem b).symm
  subst h𝔮𝔓
  exact hloc f

end
end S_ModularCurve_mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre
end P2MW
export P2MW.S_ModularCurve_mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre (solution)
