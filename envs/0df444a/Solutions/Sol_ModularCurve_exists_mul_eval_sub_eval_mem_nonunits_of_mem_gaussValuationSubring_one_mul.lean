-- Prove2me | solution 1 for ModularCurve.exists_mul_eval_sub_eval_mem_nonunits_of_mem_gaussValuationSubring_one_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/df4fb4af-9dd7-56ad-8c87-6f9ef36fe99b

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_exists_polynomial_mul_aeval_eq_aeval_of_coeffMap
import Theorems.Thm_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_one
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mul_eval_sub_eval_mem_nonunits_of_mem_gaussValuationSubring_one_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

set_option autoImplicit false

p2m_open "ModularCurve~coeffMap_injective"

namespace GaussNormZ

variable (p : ℕ) [hp : Fact p.Prime]

def divPow (W : LaurentSeries ℤ) (m : ℕ) : LaurentSeries ℤ where
  coeff n := W.coeff n / (p : ℤ) ^ m
  isPWO_support' := W.isPWO_support'.mono (by
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro h0
    exact hn (by rw [h0, Int.zero_ediv]))

@[scoped simp] theorem divPow_coeff (W : LaurentSeries ℤ) (m : ℕ) (n : ℤ) :
    (divPow p W m).coeff n = W.coeff n / (p : ℤ) ^ m := rfl

theorem natCast_pow_eq_C (m : ℕ) : ((p : LaurentSeries ℤ)) ^ m = HahnSeries.C (((p : ℤ)) ^ m) := by
  rw [map_pow, map_natCast]

theorem pow_mul_divPow (W : LaurentSeries ℤ) (m : ℕ) (h : ∀ n, ((p : ℤ)) ^ m ∣ W.coeff n) :
    ((p : LaurentSeries ℤ)) ^ m * divPow p W m = W := by
  rw [natCast_pow_eq_C, HahnSeries.C_mul_eq_smul]
  ext n
  rw [HahnSeries.coeff_smul, divPow_coeff, smul_eq_mul, Int.mul_ediv_cancel' (h n)]

theorem coeffMap_divPow_ne_zero (W : LaurentSeries ℤ) (m : ℕ) (n₀ : ℤ)
    (hn₀ : ¬ ((p : ℤ)) ^ (m + 1) ∣ W.coeff n₀) (hall : ∀ n, ((p : ℤ)) ^ m ∣ W.coeff n) :
    coeffMap (Int.castRingHom (ZMod p)) (divPow p W m) ≠ 0 := by
  intro h0
  apply hn₀
  have h1 := congrArg (fun x : LaurentSeries (ZMod p) => x.coeff n₀) h0
  simp only [coeffMap_coeff, divPow_coeff, HahnSeries.coeff_zero, eq_intCast] at h1
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := hall n₀
  refine ⟨c, ?_⟩
  have hpm : ((p : ℤ)) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [hd, Int.mul_ediv_cancel_left _ hpm] at hc
  rw [hd, hc, pow_succ]; ring

theorem exists_content (W : LaurentSeries ℤ) (hW : W ≠ 0) :
    ∃ m : ℕ, (∀ n, ((p : ℤ)) ^ m ∣ W.coeff n) ∧ ∃ n₀, ¬ ((p : ℤ)) ^ (m + 1) ∣ W.coeff n₀ := by
  classical
  have hex : ∃ m : ℕ, ∃ n, ¬ ((p : ℤ)) ^ (m + 1) ∣ W.coeff n := by
    obtain ⟨n, hn⟩ : ∃ n, W.coeff n ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hW (HahnSeries.ext (funext hcon))
    refine ⟨(W.coeff n).natAbs, n, fun hd => ?_⟩
    have h1 : (((p : ℤ)) ^ ((W.coeff n).natAbs + 1)).natAbs ∣ (W.coeff n).natAbs := Int.natAbs_dvd_natAbs.mpr hd
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) h1
    have h3 : (W.coeff n).natAbs + 1 < p ^ ((W.coeff n).natAbs + 1) := Nat.lt_pow_self hp.out.one_lt
    omega
  refine ⟨Nat.find hex, fun n => ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero]; exact one_dvd _
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    push_neg at hmin
    have := hmin n
    rwa [Nat.sub_add_cancel hpos] at this

theorem coeffMap_natCast_pow_succ (k : ℕ) :
    coeffMap (Int.castRingHom (ZMod p)) (((p : LaurentSeries ℤ)) ^ (k + 1)) = 0 := by
  rw [map_pow, map_natCast, pow_succ, show ((p : LaurentSeries (ZMod p))) = 0 by
    rw [show ((p : LaurentSeries (ZMod p))) = HahnSeries.C ((p : ZMod p)) by rw [map_natCast], ZMod.natCast_self, map_zero],
    mul_zero]

theorem exists_primitive_of_mul_eq_mul (a b U V : LaurentSeries ℤ)
    (hb : coeffMap (Int.castRingHom (ZMod p)) b ≠ 0) (hV : V ≠ 0) (h : U * b = a * V) :
    ∃ (m : ℕ) (U' V' : LaurentSeries ℤ), coeffMap (Int.castRingHom (ZMod p)) V' ≠ 0 ∧
      U = ((p : LaurentSeries ℤ)) ^ m * U' ∧ V = ((p : LaurentSeries ℤ)) ^ m * V' := by
  obtain ⟨m, hVall, n₀, hn₀⟩ := exists_content p V hV
  have hUall : ∀ n, ((p : ℤ)) ^ m ∣ U.coeff n := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨n₁, hn₁⟩ := hcon
    have hU0 : U ≠ 0 := by
      intro h0; apply hn₁; rw [h0, HahnSeries.coeff_zero]; exact dvd_zero _
    obtain ⟨k, hUk, n₂, hn₂⟩ := exists_content p U hU0
    have hkm : k < m := by
      by_contra hle
      push_neg at hle
      exact hn₁ ((pow_dvd_pow _ hle).trans (hUk n₁))
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hkm

    have hU := pow_mul_divPow p U k hUk
    have hV' := pow_mul_divPow p V m hVall
    have hcancel : divPow p U k * b = ((p : LaurentSeries ℤ)) ^ (d + 1) * (a * divPow p V m) := by
      have hpk : ((p : LaurentSeries ℤ)) ^ k ≠ 0 := pow_ne_zero _ (by
        rw [show ((p : LaurentSeries ℤ)) = HahnSeries.C ((p : ℤ)) by rw [map_natCast]]
        intro h0
        have h1 := congrArg (fun x : LaurentSeries ℤ => x.coeff 0) h0
        simp only [HahnSeries.C_apply, HahnSeries.coeff_single_same, HahnSeries.coeff_zero] at h1
        exact hp.out.ne_zero (by exact_mod_cast h1))
      apply mul_left_cancel₀ hpk
      calc ((p : LaurentSeries ℤ)) ^ k * (divPow p U k * b) = U * b := by rw [← mul_assoc, hU]
        _ = a * V := h
        _ = a * (((p : LaurentSeries ℤ)) ^ m * divPow p V m) := by rw [hV']
        _ = ((p : LaurentSeries ℤ)) ^ k * (((p : LaurentSeries ℤ)) ^ (d + 1) * (a * divPow p V m)) := by
            rw [hd]; ring
    have hred := congrArg (coeffMap (Int.castRingHom (ZMod p))) hcancel
    rw [map_mul, map_mul, coeffMap_natCast_pow_succ, zero_mul, mul_eq_zero] at hred
    rcases hred with h1 | h1
    · exact coeffMap_divPow_ne_zero p U k n₂ hn₂ hUk h1
    · exact hb h1
  exact ⟨m, divPow p U m, divPow p V m, coeffMap_divPow_ne_zero p V m n₀ hn₀ hVall,
    (pow_mul_divPow p U m hUall).symm, (pow_mul_divPow p V m hVall).symm⟩

end GaussNormZ
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eval_sub_eval_mem_nonunits_of_mem_gaussValuationSubring_one_mul.GaussNormZ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve~coeffMap_injective AlgebraicCurve"

namespace GaussResidue

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (hg : Function.Injective g) :
    Function.Injective (coeffMap g) := fun b c h =>
  HahnSeries.ext (funext fun k => hg (by rw [← coeffMap_coeff, ← coeffMap_coeff, h]))

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

theorem coeffMap_subtype_int (U : LaurentSeries ℤ) :
    coeffMap A.subtype (coeffMap (Int.castRingHom A) U) =
      coeffEmb (AlgebraicClosure ℚ) (coeffMap (Int.castRingHom ℚ) U) := by
  rw [coeffEmb, coeffMap_coeffMap, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_int _ _) U

theorem coeffMap_residue_int (θ : ZMod p →+* IsLocalRing.ResidueField A) (U : LaurentSeries ℤ) :
    coeffMap (IsLocalRing.residue A) (coeffMap (Int.castRingHom A) U) =
      coeffMap θ (coeffMap (Int.castRingHom (ZMod p)) U) := by
  rw [coeffMap_coeffMap, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_int _ _) U

variable (R : RegularProlongation A ↥(modularFunctionFieldBar (1 * p))
    ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1))
  (hR1 : ∀ f : ↥(modularFunctionFieldBar (1 * p)), f ∈ R.integers ↔
    ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
  (hR1' : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * p)),
    ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ R.integers,
      ((R.residue ⟨_, hint⟩ : ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)) :
        LaurentSeries (IsLocalRing.ResidueField A)) = coeffMap (IsLocalRing.residue A) y)
  (θ : ZMod p →+* IsLocalRing.ResidueField A)

include hR1' in

theorem residue_int (U : LaurentSeries ℤ) (hU : coeffMap (Int.castRingHom ℚ) U ∈ modularFunctionFieldFull (1 * p)) :
    ∃ hUR : (⟨coeffEmb (AlgebraicClosure ℚ) (coeffMap (Int.castRingHom ℚ) U),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hU⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ R.integers,
      ((R.residue ⟨_, hUR⟩ : ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)) :
          LaurentSeries (IsLocalRing.ResidueField A)) = coeffMap θ (coeffMap (Int.castRingHom (ZMod p)) U) := by
  have hval : coeffMap A.subtype (coeffMap (Int.castRingHom A) U) =
      coeffEmb (AlgebraicClosure ℚ) (coeffMap (Int.castRingHom ℚ) U) := coeffMap_subtype_int A U
  have hy : coeffMap A.subtype (coeffMap (Int.castRingHom A) U) ∈ modularFunctionFieldBar (1 * p) := by
    rw [hval]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hU
  obtain ⟨hint, hres⟩ := hR1' (coeffMap (Int.castRingHom A) U) hy
  have e : (⟨coeffMap A.subtype (coeffMap (Int.castRingHom A) U), hy⟩ : ↥(modularFunctionFieldBar (1 * p))) =
      ⟨coeffEmb (AlgebraicClosure ℚ) (coeffMap (Int.castRingHom ℚ) U),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hU⟩ := Subtype.ext hval
  refine ⟨e ▸ hint, ?_⟩
  rw [← coeffMap_residue_int p A θ U, ← hres]
  congr 2

include hR1 θ in

theorem mem_integers_of_mul_eq (x : ↥(modularFunctionFieldFull (1 * p))) (a b : LaurentSeries ℤ)
    (hb : coeffMap (Int.castRingHom (ZMod p)) b ≠ 0)
    (hx : (x : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) b = coeffMap (Int.castRingHom ℚ) a) :
    (⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ R.integers := by
  rw [hR1]
  refine ⟨coeffMap (Int.castRingHom A) a, coeffMap (Int.castRingHom A) b, ?_, ?_⟩
  · rw [coeffMap_residue_int p A θ b]
    intro h0
    exact hb (coeffMap_injective θ θ.injective (by rw [h0, map_zero]))
  · show coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ) * _ = _
    rw [coeffMap_subtype_int, coeffMap_subtype_int, ← map_mul, hx]

end GaussResidue
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eval_sub_eval_mem_nonunits_of_mem_gaussValuationSubring_one_mul.GaussNormZ"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "ModularCurve~coeffMap_injective"

namespace GaussRes

theorem natCast_laurent_ne_zero {R : Type*} [CommRing R] [CharZero R] {n : ℕ} (hn : n ≠ 0) : (n : LaurentSeries R) ≠ 0 := by
  rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := R)) n]
  intro h
  have := HahnSeries.C_injective (Γ := ℤ) (R := R) (h.trans (map_zero _).symm)
  exact hn (by exact_mod_cast this)

theorem exists_int_fraction (N : ℕ) [NeZero N] (x : LaurentSeries ℚ) (hx : x ∈ modularFunctionFieldFull N) :
    ∃ U V : LaurentSeries ℤ, V ≠ 0 ∧ coeffMap (Int.castRingHom ℚ) U ∈ modularFunctionFieldFull N ∧
      coeffMap (Int.castRingHom ℚ) V ∈ modularFunctionFieldFull N ∧
      x * coeffMap (Int.castRingHom ℚ) V = coeffMap (Int.castRingHom ℚ) U := by
  classical
  set ι := Int.castRingHom ℚ with hι

  let S : Set (LaurentSeries ℚ) := Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N
  have hmem : x ∈ Subfield.closure S := by
    have : (modularFunctionFieldFull N).toSubfield = Subfield.closure S := IntermediateField.adjoin_toSubfield _ _
    rw [← IntermediateField.mem_toSubfield, this] at hx
    exact hx
  have hsub : Subring.closure S ≤ (modularFunctionFieldFull N).toSubring := by
    rw [Subring.closure_le]
    rintro y (⟨c, rfl⟩ | hy)
    · exact (modularFunctionFieldFull N).algebraMap_mem c
    · exact IntermediateField.subset_adjoin ℚ _ hy
  have key : ∀ y ∈ Subring.closure S, ∃ n : ℕ, n ≠ 0 ∧ ∃ a : LaurentSeries ℤ, (n : LaurentSeries ℚ) * y = coeffMap ι a := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨d, hd, hdN, rfl⟩
      · refine ⟨c.den, c.den_nz, HahnSeries.single 0 c.num, ?_⟩
        rw [coeffMap_single, algebraMap_laurentSeries_eq_single,
          show ((c.den : ℕ) : LaurentSeries ℚ) = HahnSeries.single 0 ((c.den : ℕ) : ℚ) from by
            rw [← algebraMap_laurentSeries_eq_single, map_natCast],
          HahnSeries.single_mul_single, zero_add]
        congr 1
        rw [hι]
        show ((c.den : ℕ) : ℚ) * c = ((c.num : ℤ) : ℚ)
        rw [mul_comm]
        exact Rat.mul_den_eq_num c
      · haveI := hd
        refine ⟨1, one_ne_zero, qExpand ℤ d (jqModC ℤ), ?_⟩
        rw [Nat.cast_one, one_mul, coeffMap_qExpand, show coeffMap ι (jqModC ℤ) = jqModC ℚ from map_jqModC ι,
          jqModC_rat]
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | one => exact ⟨1, one_ne_zero, 1, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨n, hn, a, ha⟩ := hy
      obtain ⟨m, hm, b, hb⟩ := hz
      refine ⟨n * m, mul_ne_zero hn hm, (m : LaurentSeries ℤ) * a + (n : LaurentSeries ℤ) * b, ?_⟩
      rw [map_add, map_mul, map_mul, map_natCast, map_natCast, ← ha, ← hb]
      push_cast; ring
    | neg y _ hy =>
      obtain ⟨n, hn, a, ha⟩ := hy
      exact ⟨n, hn, -a, by rw [map_neg, ← ha, mul_neg]⟩
    | mul y z _ _ hy hz =>
      obtain ⟨n, hn, a, ha⟩ := hy
      obtain ⟨m, hm, b, hb⟩ := hz
      refine ⟨n * m, mul_ne_zero hn hm, a * b, ?_⟩
      rw [map_mul, ← ha, ← hb]; push_cast; ring
  obtain ⟨y, hy, z, hz, rfl⟩ := (Subfield.mem_closure_iff).mp hmem
  obtain ⟨n, hn, a, ha⟩ := key y hy
  obtain ⟨m, hm, b, hb⟩ := key z hz
  by_cases hz0 : z = 0
  · refine ⟨0, 1, one_ne_zero, by simp, by simp, ?_⟩
    rw [hz0, div_zero, zero_mul, map_zero]
  refine ⟨(m : LaurentSeries ℤ) * a, (n : LaurentSeries ℤ) * b, ?_, ?_, ?_, ?_⟩
  · refine mul_ne_zero (natCast_laurent_ne_zero hn) ?_
    rintro rfl
    rw [map_zero, mul_eq_zero] at hb
    rcases hb with h | h
    · exact natCast_laurent_ne_zero hm (by exact_mod_cast h)
    · exact hz0 h
  · rw [map_mul, map_natCast, ← ha, ← mul_assoc]
    exact mul_mem (mul_mem (natCast_mem _ m) (natCast_mem _ n)) (hsub hy)
  · rw [map_mul, map_natCast, ← hb, ← mul_assoc]
    exact mul_mem (mul_mem (natCast_mem _ n) (natCast_mem _ m)) (hsub hz)
  · rw [map_mul, map_mul, map_natCast, map_natCast, ← ha, ← hb]
    field_simp

end GaussRes
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eval_sub_eval_mem_nonunits_of_mem_gaussValuationSubring_one_mul.GaussNormZ"

namespace GaussResMain

p2m_open "ModularCurve~coeffMap_injective AlgebraicCurve Polynomial"

noncomputable def emb (M : ℕ) : ↥(modularFunctionFieldFull M) →+* ↥(modularFunctionFieldBar M) where
  toFun x := ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem coe_emb (M : ℕ) (x : ↥(modularFunctionFieldFull M)) :
    ((emb M x : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ) := rfl

theorem emb_eq (M : ℕ) (x : ↥(modularFunctionFieldFull M)) :
    emb M x = ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ := rfl

theorem natCast_ne_zero' {R : Type*} [CommRing R] [CharZero R] {n : ℕ} (hn : n ≠ 0) : (n : LaurentSeries R) ≠ 0 :=
  GaussRes.natCast_laurent_ne_zero hn

theorem hom_eval₂_int {S T : Type*} [CommRing S] [CommRing T] (g : S →+* T) (s : S) (P : Polynomial ℤ) :
    g (P.eval₂ (algebraMap ℤ S) s) = P.eval₂ (algebraMap ℤ T) (g s) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

theorem coeffMap_aeval_map {p : ℕ} {k : Type*} [Field k] (θ : ZMod p →+* k) (t : LaurentSeries (ZMod p)) (S : Polynomial ℤ) :
    coeffMap θ (aeval t (S.map (Int.castRingHom (ZMod p)))) = S.eval₂ (algebraMap ℤ (LaurentSeries k)) (coeffMap θ t) := by
  rw [aeval_def, eval₂_map, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

set_option maxHeartbeats 12800000 in

theorem clause0 (p : ℕ) [hp : Fact p.Prime] [NeZero p]
    (W₀ : ValuationSubring ↥(modularFunctionFieldFull (1 * p)))
    (hW₀ : ∀ f : ↥(modularFunctionFieldFull (1 * p)), f ∈ W₀ ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x)
    (x : ↥(modularFunctionFieldFull (1 * p))) (hxW : x ∈ W₀) :
    ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p)))
              ⟨jq, modularFunctionField_le_full (1 * p) (jq_mem (1 * p))⟩ Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p)))
              ⟨jq, modularFunctionField_le_full (1 * p) (jq_mem (1 * p))⟩ P ∈ W₀.nonunits := by
  classical
  let J : ↥(modularFunctionFieldFull (1 * p)) := ⟨jq, modularFunctionField_le_full (1 * p) (jq_mem (1 * p))⟩

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hp.out⟩
  have hpk : (p : IsLocalRing.ResidueField A) = 0 := by
    have h1 : ((p : A) : AlgebraicClosure ℚ) ∈ A.nonunits := by simpa [ValuationSubring.LiesOverPrime] using hA
    have h2 : (p : A) ∈ IsLocalRing.maximalIdeal A := A.coe_mem_nonunits_iff.mp h1
    have : IsLocalRing.residue A (p : A) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr h2
    simpa using this
  haveI : CharP (IsLocalRing.ResidueField A) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr hpk
  let θ : ZMod p →+* IsLocalRing.ResidueField A := ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)
  have hθinj : Function.Injective θ := θ.injective
  have hp1 : ¬ p ∣ 1 := fun h => hp.out.ne_one (Nat.dvd_one.mp h)
  obtain ⟨Rf, hR1, hR1', -, -, -, -, -⟩ :=
    exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd 1 p hp1 A hA

  have hWR : ∀ y : ↥(modularFunctionFieldFull (1 * p)), y ∈ W₀ → emb (1 * p) y ∈ (Rf 0).integers := by
    intro y hy
    obtain ⟨a, b, hb, hab⟩ := (hW₀ y).mp hy
    rw [emb_eq]
    exact GaussResidue.mem_integers_of_mul_eq p A (Rf 0) hR1 θ y a b hb hab

  obtain ⟨U, V, hV0, hUF, hVF, hxUV⟩ := GaussRes.exists_int_fraction (1 * p) (x : LaurentSeries ℚ) x.2
  obtain ⟨a, b, hb, hab⟩ := (hW₀ x).mp hxW
  have hGauss : U * b = a * V := by
    apply GaussResidue.coeffMap_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    rw [map_mul, map_mul, ← hxUV, ← hab]; ring
  obtain ⟨m, U', V', hV', hU, hV⟩ := GaussNormZ.exists_primitive_of_mul_eq_mul p a b U V hb hV0 hGauss
  have hpm : ((p : LaurentSeries ℚ)) ^ m ≠ 0 := pow_ne_zero _ (natCast_ne_zero' hp.out.ne_zero)
  have hcoe : ∀ W : LaurentSeries ℤ, coeffMap (Int.castRingHom ℚ) (((p : LaurentSeries ℤ)) ^ m * W)
      = ((p : LaurentSeries ℚ)) ^ m * coeffMap (Int.castRingHom ℚ) W := by
    intro W; rw [map_mul, map_pow, map_natCast]
  have hxUV' : (x : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) V' = coeffMap (Int.castRingHom ℚ) U' := by
    apply mul_left_cancel₀ hpm
    rw [← mul_assoc, mul_comm (_ ^ m) (x : LaurentSeries ℚ), mul_assoc, ← hcoe, ← hcoe, ← hV, ← hU, hxUV]
  have hV'F : coeffMap (Int.castRingHom ℚ) V' ∈ modularFunctionFieldFull (1 * p) := by
    have : coeffMap (Int.castRingHom ℚ) V' = ((p : LaurentSeries ℚ) ^ m)⁻¹ * coeffMap (Int.castRingHom ℚ) V := by
      rw [eq_inv_mul_iff_mul_eq₀ hpm, ← hcoe, ← hV]
    rw [this]
    exact mul_mem (inv_mem (pow_mem (natCast_mem (modularFunctionFieldFull (1 * p)) p) m)) hVF
  have hU'F : coeffMap (Int.castRingHom ℚ) U' ∈ modularFunctionFieldFull (1 * p) := by
    have : coeffMap (Int.castRingHom ℚ) U' = ((p : LaurentSeries ℚ) ^ m)⁻¹ * coeffMap (Int.castRingHom ℚ) U := by
      rw [eq_inv_mul_iff_mul_eq₀ hpm, ← hcoe, ← hU]
    rw [this]
    exact mul_mem (inv_mem (pow_mem (natCast_mem (modularFunctionFieldFull (1 * p)) p) m)) hUF

  have hxR : emb (1 * p) x ∈ (Rf 0).integers := hWR x hxW
  obtain ⟨hU'R, hresU'⟩ := GaussResidue.residue_int p A (Rf 0) hR1' θ U' hU'F
  obtain ⟨hV'R, hresV'⟩ := GaussResidue.residue_int p A (Rf 0) hR1' θ V' hV'F
  have hjZ : coeffMap (Int.castRingHom ℚ) (jqModC ℤ) = jq := by
    rw [show coeffMap (Int.castRingHom ℚ) (jqModC ℤ) = jqModC ℚ from map_jqModC _, jqModC_rat]
  have hJF : coeffMap (Int.castRingHom ℚ) (jqModC ℤ) ∈ modularFunctionFieldFull (1 * p) := by rw [hjZ]; exact J.2
  obtain ⟨hJR, hresJ⟩ := GaussResidue.residue_int p A (Rf 0) hR1' θ (jqModC ℤ) hJF
  set X : (Rf 0).integers := ⟨emb (1 * p) x, hxR⟩ with hX
  set UU : (Rf 0).integers := ⟨_, hU'R⟩ with hUU
  set VV : (Rf 0).integers := ⟨_, hV'R⟩ with hVV
  set JJ : (Rf 0).integers := ⟨_, hJR⟩ with hJJ
  have hJJ' : (JJ : ↥(modularFunctionFieldBar (1 * p))) = emb (1 * p) J := by
    rw [emb_eq]; apply Subtype.ext
    show coeffEmb _ (coeffMap (Int.castRingHom ℚ) (jqModC ℤ)) = coeffEmb _ jq
    rw [hjZ]
  have hXV : X * VV = UU := by
    apply Subtype.ext; apply Subtype.ext
    show coeffEmb _ (x : LaurentSeries ℚ) * coeffEmb _ (coeffMap (Int.castRingHom ℚ) V') = coeffEmb _ (coeffMap (Int.castRingHom ℚ) U')
    rw [← map_mul, hxUV']
  have hθV'ne : coeffMap θ (coeffMap (Int.castRingHom (ZMod p)) V') ≠ 0 := fun h0 =>
    hV' (GaussResidue.coeffMap_injective θ hθinj (h0.trans (map_zero _).symm))
  have hρeq : (((Rf 0).residue X : ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)) :
        LaurentSeries (IsLocalRing.ResidueField A)) * coeffMap θ (coeffMap (Int.castRingHom (ZMod p)) V')
      = coeffMap θ (coeffMap (Int.castRingHom (ZMod p)) U') := by
    rw [← hresV', ← hresU']
    have := congrArg (fun w : (Rf 0).integers =>
      (((Rf 0).residue w : ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)) : LaurentSeries (IsLocalRing.ResidueField A))) hXV
    simp only [map_mul] at this
    exact this

  have hρmem : (((Rf 0).residue X : ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)) : LaurentSeries (IsLocalRing.ResidueField A))
      ∈ IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A))) := by
    have h1 := ((Rf 0).residue X).2
    have h2 := (le_of_eq (modularFunctionFieldFullC_one (IsLocalRing.ResidueField A))) h1
    refine (show modularFunctionFieldC (IsLocalRing.ResidueField A) 1 ≤ _ from ?_) h2
    unfold modularFunctionFieldC
    rw [IntermediateField.adjoin_le_iff]
    rintro s (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self _ _
    · rw [jqNModC_one]
      exact IntermediateField.mem_adjoin_simple_self _ _
  obtain ⟨P₁, Q₁, hPQ₁⟩ := (IntermediateField.mem_adjoin_simple_iff _ _).mp hρmem

  set t : LaurentSeries (ZMod p) := jqModC (ZMod p) with ht
  set r : LaurentSeries (ZMod p) := coeffMap (Int.castRingHom (ZMod p)) U' / coeffMap (Int.castRingHom (ZMod p)) V' with hr
  have hθt : coeffMap θ t = jqModC (IsLocalRing.ResidueField A) := map_jqModC θ
  have hθr : coeffMap θ r = (((Rf 0).residue X : ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)) :
        LaurentSeries (IsLocalRing.ResidueField A)) := by
    rw [hr, map_div₀, div_eq_iff hθV'ne, hρeq]
  have htt : Transcendental (ZMod p) t := transcendental_jqModC (ZMod p)
  have hr' : ∃ P Q : Polynomial (IsLocalRing.ResidueField A), aeval (coeffMap θ t) Q ≠ 0 ∧
      coeffMap θ r * aeval (coeffMap θ t) Q = aeval (coeffMap θ t) P := by
    rw [hθt, hθr]
    by_cases hQ₁ : aeval (jqModC (IsLocalRing.ResidueField A)) Q₁ = 0
    · refine ⟨0, 1, by simp, ?_⟩
      rw [hPQ₁, hQ₁, div_zero]; simp
    · exact ⟨P₁, Q₁, hQ₁, by rw [hPQ₁, div_mul_cancel₀ _ hQ₁]⟩
  obtain ⟨Pb, Qb, hQb, hrel⟩ := exists_polynomial_mul_aeval_eq_aeval_of_coeffMap θ t r htt hr'
  obtain ⟨P, hP⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) Pb
  obtain ⟨Q, hQ⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) Qb
  refine ⟨P, Q, by rw [hQ]; exact hQb, ?_⟩

  set z : ↥(modularFunctionFieldFull (1 * p)) := x * eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) J Q - eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) J P with hz
  have hJW : J ∈ W₀ := (hW₀ J).mpr ⟨jqModC ℤ, 1, by simp, by rw [map_one, mul_one, hjZ]⟩
  have hev : ∀ S : Polynomial ℤ, eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) J S ∈ W₀ := by
    intro S
    have := hom_eval₂_int W₀.subtype ⟨J, hJW⟩ S

    rw [show W₀.subtype ⟨J, hJW⟩ = J from rfl] at this
    rw [← this]
    exact SetLike.coe_mem _
  have hzW : z ∈ W₀ := W₀.toSubring.sub_mem (W₀.toSubring.mul_mem hxW (hev Q)) (hev P)

  set w : (Rf 0).integers := X * eval₂ (algebraMap ℤ (Rf 0).integers) JJ Q - eval₂ (algebraMap ℤ (Rf 0).integers) JJ P with hw
  have hwz : (w : ↥(modularFunctionFieldBar (1 * p))) = emb (1 * p) z := by
    have e1 : ∀ S : Polynomial ℤ, ((eval₂ (algebraMap ℤ (Rf 0).integers) JJ S : (Rf 0).integers) : ↥(modularFunctionFieldBar (1 * p)))
        = eval₂ (algebraMap ℤ _) (emb (1 * p) J) S := by
      intro S
      rw [← hJJ']
      exact hom_eval₂_int (Rf 0).integers.subtype JJ S
    have e2 : ∀ S : Polynomial ℤ, emb (1 * p) (eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) J S) = eval₂ (algebraMap ℤ _) (emb (1 * p) J) S :=
      fun S => hom_eval₂_int (emb (1 * p)) J S
    rw [hz, map_sub, map_mul, e2, e2, hw]
    push_cast
    rw [e1, e1]
  have hwres : (Rf 0).residue w = 0 := by
    have e3 : ∀ S : Polynomial ℤ, (((Rf 0).residue (eval₂ (algebraMap ℤ (Rf 0).integers) JJ S) :
        ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)) : LaurentSeries (IsLocalRing.ResidueField A))
        = coeffMap θ (aeval t (S.map (Int.castRingHom (ZMod p)))) := by
      intro S
      rw [coeffMap_aeval_map, hθt, hom_eval₂_int (Rf 0).residue JJ S]
      have e4 := hom_eval₂_int (IntermediateField.val (modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)).toRingHom ((Rf 0).residue JJ) S
      refine e4.trans ?_
      have e6 : (IntermediateField.val (modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)).toRingHom ((Rf 0).residue JJ)
          = jqModC (IsLocalRing.ResidueField A) := by
        show (((Rf 0).residue JJ : ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)) : LaurentSeries (IsLocalRing.ResidueField A)) = jqModC (IsLocalRing.ResidueField A)
        rw [hresJ, show coeffMap (Int.castRingHom (ZMod p)) (jqModC ℤ) = jqModC (ZMod p) from map_jqModC _]
        exact map_jqModC θ
      rw [e6]
      try (congr 1; exact RingHom.ext_int _ _)
    have hval : (((Rf 0).residue w : ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)) : LaurentSeries (IsLocalRing.ResidueField A)) = 0 := by
      rw [hw, map_sub, map_mul]
      push_cast
      rw [e3, e3, ← hθr, ← map_mul, ← map_sub, hQ, hP, hrel, sub_self, map_zero]
    exact_mod_cast hval
  have hwunit : ¬ IsUnit w := fun hu => (Rf 0).residue_ne_zero_of_isUnit hu hwres

  show z ∈ W₀.nonunits
  rw [show z = ((⟨z, hzW⟩ : W₀) : ↥(modularFunctionFieldFull (1 * p))) from rfl, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff]
  intro hzu
  apply hwunit
  obtain ⟨u, hu⟩ := hzu
  have hvW : (((u⁻¹ : W₀ˣ) : W₀) : ↥(modularFunctionFieldFull (1 * p))) ∈ W₀ := ((u⁻¹ : W₀ˣ) : W₀).2
  refine isUnit_iff_exists_inv.mpr ⟨⟨emb (1 * p) (((u⁻¹ : W₀ˣ) : W₀) : ↥(modularFunctionFieldFull (1 * p))), hWR _ hvW⟩, ?_⟩
  apply Subtype.ext
  show (w : ↥(modularFunctionFieldBar (1 * p))) * emb (1 * p) _ = 1
  rw [hwz, ← map_mul]
  have hmul : z * (((u⁻¹ : W₀ˣ) : W₀) : ↥(modularFunctionFieldFull (1 * p))) = 1 := by
    have := congrArg (fun s : W₀ => (s : ↥(modularFunctionFieldFull (1 * p)))) u.mul_inv
    rw [hu] at this
    first | exact_mod_cast this | simpa using this | (push_cast at this; exact this)
  rw [hmul, map_one]

end GaussResMain
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eval_sub_eval_mem_nonunits_of_mem_gaussValuationSubring_one_mul.GaussNormZ"

namespace GaussResMain

p2m_open "ModularCurve~coeffMap_injective AlgebraicCurve Polynomial"

set_option maxHeartbeats 6400000 in
theorem main (p : ℕ) [hp : Fact p.Prime] [NeZero p]
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull (1 * p)))
    (hW₀ : ∀ f : ↥(modularFunctionFieldFull (1 * p)), f ∈ W₀ ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x)
    (hW₁ : ∀ f : ↥(modularFunctionFieldFull (1 * p)), f ∈ W₁ ↔ atkinLehnerInvolutionFull 1 p f ∈ W₀)
    (hne : W₀ ≠ W₁)
    (jp : ↥(modularFunctionFieldFull (1 * p))) (hjp : (jp : LaurentSeries ℚ) = qExpand ℚ p jq) :
    (∀ x : ↥(modularFunctionFieldFull (1 * p)), x ∈ W₀ →
      ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p)))
              ⟨jq, modularFunctionField_le_full (1 * p) (jq_mem (1 * p))⟩ Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p)))
              ⟨jq, modularFunctionField_le_full (1 * p) (jq_mem (1 * p))⟩ P ∈ W₀.nonunits) ∧
    (∀ x : ↥(modularFunctionFieldFull (1 * p)), x ∈ W₁ →
      ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) jp Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) jp P ∈ W₁.nonunits) := by
  classical
  refine ⟨fun x hx => clause0 p W₀ hW₀ x hx, ?_⟩

  have hAL : ∃ σ : ↥(modularFunctionFieldFull (1 * p)) ≃ₐ[ℚ] ↥(modularFunctionFieldFull (1 * p)), IsAtkinLehnerAutFull 1 p σ := by
    by_contra h
    apply hne
    ext f
    rw [hW₁ f, atkinLehnerInvolutionFull_eq_refl 1 p h]
    rfl
  obtain ⟨h1, h2⟩ := isAtkinLehnerAutFull_atkinLehnerInvolutionFull 1 p hAL 1 inferInstance (one_dvd 1)
  let J : ↥(modularFunctionFieldFull (1 * p)) := ⟨jq, modularFunctionField_le_full (1 * p) (jq_mem (1 * p))⟩
  have eJ : (⟨qExpand ℚ 1 jq, jqd_mem_full (1 * p) (Dvd.dvd.mul_right (one_dvd 1) p)⟩ : ↥(modularFunctionFieldFull (1 * p))) = J :=
    Subtype.ext (qExpand_one_apply jq)
  have eP : (⟨qExpand ℚ (1 * p) jq, jqd_mem_full (1 * p) (Nat.mul_dvd_mul_right (one_dvd 1) p)⟩ : ↥(modularFunctionFieldFull (1 * p))) = jp :=
    Subtype.ext (by show qExpand ℚ (1 * p) jq = (jp : LaurentSeries ℚ); rw [hjp]; exact qExpand_congr (one_mul p) jq)
  have hwjp : atkinLehnerInvolutionFull 1 p jp = J := by rw [← eP, h2, eJ]
  intro x hx
  have hx0 : atkinLehnerInvolutionFull 1 p x ∈ W₀ := (hW₁ x).mp hx
  obtain ⟨P, Q, hQ, hz⟩ := clause0 p W₀ hW₀ _ hx0
  refine ⟨P, Q, hQ, ?_⟩
  set y : ↥(modularFunctionFieldFull (1 * p)) := x * eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) jp Q - eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) jp P with hy
  have hwy : atkinLehnerInvolutionFull 1 p y
      = atkinLehnerInvolutionFull 1 p x * eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) J Q - eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) J P := by
    have e5 : ∀ S : Polynomial ℤ, atkinLehnerInvolutionFull 1 p (eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) jp S)
        = eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) (atkinLehnerInvolutionFull 1 p jp) S :=
      fun S => hom_eval₂_int ((atkinLehnerInvolutionFull 1 p : ↥(modularFunctionFieldFull (1 * p)) ≃ₐ[ℚ] ↥(modularFunctionFieldFull (1 * p))) : ↥(modularFunctionFieldFull (1 * p)) →+* ↥(modularFunctionFieldFull (1 * p))) jp S
    rw [hy, map_sub, map_mul, e5, e5, hwjp]
  have hzW₀ : atkinLehnerInvolutionFull 1 p y ∈ W₀ := by rw [hwy]; exact W₀.nonunits_subset hz
  have hyW₁ : y ∈ W₁ := (hW₁ y).mpr hzW₀
  show y ∈ W₁.nonunits
  rw [show y = ((⟨y, hyW₁⟩ : W₁) : ↥(modularFunctionFieldFull (1 * p))) from rfl, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff]
  intro hyu
  obtain ⟨u, hu⟩ := hyu
  have hvW₁ : (((u⁻¹ : W₁ˣ) : W₁) : ↥(modularFunctionFieldFull (1 * p))) ∈ W₁ := ((u⁻¹ : W₁ˣ) : W₁).2
  have hvW₀ : atkinLehnerInvolutionFull 1 p (((u⁻¹ : W₁ˣ) : W₁) : ↥(modularFunctionFieldFull (1 * p))) ∈ W₀ := (hW₁ _).mp hvW₁
  have hmul : y * (((u⁻¹ : W₁ˣ) : W₁) : ↥(modularFunctionFieldFull (1 * p))) = 1 := by
    have := congrArg (fun s : W₁ => (s : ↥(modularFunctionFieldFull (1 * p)))) u.mul_inv
    rw [hu] at this
    first | exact_mod_cast this | simpa using this | (push_cast at this; exact this)
  have hzunit : IsUnit (⟨atkinLehnerInvolutionFull 1 p y, hzW₀⟩ : W₀) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hvW₀⟩, ?_⟩
    apply Subtype.ext
    show atkinLehnerInvolutionFull 1 p y * atkinLehnerInvolutionFull 1 p _ = 1
    rw [← map_mul, hmul, map_one]
  have hz' : ((⟨atkinLehnerInvolutionFull 1 p y, hzW₀⟩ : W₀) : ↥(modularFunctionFieldFull (1 * p))) ∈ W₀.nonunits := by
    show atkinLehnerInvolutionFull 1 p y ∈ W₀.nonunits
    rw [hwy]; exact hz
  exact ((IsLocalRing.mem_maximalIdeal _).mp (ValuationSubring.coe_mem_nonunits_iff.mp hz')) hzunit

end GaussResMain
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eval_sub_eval_mem_nonunits_of_mem_gaussValuationSubring_one_mul.GaussNormZ"

set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull (1 * p)))
    (hW₀ : ∀ f : ↥(modularFunctionFieldFull (1 * p)), f ∈ W₀ ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x)
    (hW₁ : ∀ f : ↥(modularFunctionFieldFull (1 * p)), f ∈ W₁ ↔ atkinLehnerInvolutionFull 1 p f ∈ W₀)
    (hne : W₀ ≠ W₁)
    (jp : ↥(modularFunctionFieldFull (1 * p))) (hjp : (jp : LaurentSeries ℚ) = qExpand ℚ p jq) :
    (∀ x : ↥(modularFunctionFieldFull (1 * p)), x ∈ W₀ →
      ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p)))
              ⟨jq, modularFunctionField_le_full (1 * p) (jq_mem (1 * p))⟩ Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p)))
              ⟨jq, modularFunctionField_le_full (1 * p) (jq_mem (1 * p))⟩ P ∈ W₀.nonunits) ∧
    (∀ x : ↥(modularFunctionFieldFull (1 * p)), x ∈ W₁ →
      ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) jp Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) jp P ∈ W₁.nonunits) :=
  GaussResMain.main p W₀ W₁ hW₀ hW₁ hne jp hjp

end S_ModularCurve_exists_mul_eval_sub_eval_mem_nonunits_of_mem_gaussValuationSubring_one_mul
end P2MW
export P2MW.S_ModularCurve_exists_mul_eval_sub_eval_mem_nonunits_of_mem_gaussValuationSubring_one_mul (solution)
