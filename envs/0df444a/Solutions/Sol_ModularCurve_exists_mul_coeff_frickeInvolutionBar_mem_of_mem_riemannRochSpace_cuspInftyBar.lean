-- Prove2me | solution 1 for ModularCurve.exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d9208b36-40b7-5877-8e1a-2fc7eea2a5b0

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_ord_coeffEmb_modularUnitSeries_of_not_isCusp
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000

p2m_open "AlgebraicCurve ModularCurve~coeffMap_qExpand"

namespace ZXGauss0

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : coeffMap φ (qExpand R N x) = qExpand S N (coeffMap φ x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, coeffMap_coeff, coeffMap_coeff, qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd N _ hk, coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : PowerSeries R) :
    coeffMap φ (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map φ) := by
  ext k
  rw [coeffMap_coeff]
  change φ (((x : PowerSeries R) : LaurentSeries R).coeff k) = ((x.map φ : PowerSeries S) : LaurentSeries S).coeff k
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · exact map_zero φ
  · rw [PowerSeries.coeff_map]

noncomputable def unitInvInt (N : ℕ) [NeZero N] : LaurentSeries ℤ :=
  qExpand ℤ N (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit) *
    (HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)

theorem coeffMap_unitInvInt (N : ℕ) [NeZero N] :
    coeffMap (Int.castRingHom ℚ) (unitInvInt N) = (modularUnitSeries N)⁻¹ := by
  have hX : coeffMap (Int.castRingHom ℚ) (unitInvInt N)
      = deltaSeriesN N * (HahnSeries.single (-1 : ℤ) (1 : ℚ) *
          HahnSeries.ofPowerSeries ℤ ℚ (dedekindEtaUnitInv.map (Int.castRingHom ℚ))) := by
    simp only [unitInvInt, deltaSeriesN, deltaSeries, dedekindEtaUnitQ, map_mul, coeffMap_qExpand,
      coeffMap_single, coeffMap_ofPowerSeries, map_one]
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [hX, ← mul_assoc, modularUnitSeries_mul_deltaSeriesN, deltaSeries, dedekindEtaUnitQ]
  have h1 : HahnSeries.ofPowerSeries ℤ ℚ (dedekindEtaUnit.map (Int.castRingHom ℚ)) *
      HahnSeries.ofPowerSeries ℤ ℚ (dedekindEtaUnitInv.map (Int.castRingHom ℚ)) = 1 := by
    rw [← map_mul, ← map_mul, dedekindEtaUnit_mul_inv, map_one, map_one]
  calc HahnSeries.single (1 : ℤ) (1 : ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (dedekindEtaUnit.map (Int.castRingHom ℚ)) *
        (HahnSeries.single (-1 : ℤ) (1 : ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (dedekindEtaUnitInv.map (Int.castRingHom ℚ)))
      = (HahnSeries.single (1 : ℤ) (1 : ℚ) * HahnSeries.single (-1 : ℤ) (1 : ℚ)) *
          (HahnSeries.ofPowerSeries ℤ ℚ (dedekindEtaUnit.map (Int.castRingHom ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℚ (dedekindEtaUnitInv.map (Int.castRingHom ℚ))) := by ring
    _ = 1 := by rw [h1, HahnSeries.single_mul_single, mul_one, add_neg_cancel, mul_one]; rfl

theorem exists_int_coeff_modularUnitSeries_inv (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ z : ℤ, ((modularUnitSeries N)⁻¹).coeff k = (z : ℚ) :=
  ⟨(unitInvInt N).coeff k, by rw [← coeffMap_unitInvInt, coeffMap_coeff]; rfl⟩

theorem ord_frickeInvolutionBar (N : ℕ) [NeZero N] (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (f : modularFunctionFieldBar N) :
    W.ord (frickeInvolutionBar N f) = (frickeInvolutionBar N • W).ord f := by
  have hsq : frickeInvolutionBar N * frickeInvolutionBar N = 1 :=
    AlgEquiv.ext fun x => by rw [AlgEquiv.mul_apply, frickeInvolutionBar_frickeInvolutionBar]; rfl
  have hW : frickeInvolutionBar N • (frickeInvolutionBar N • W) = W := by
    rw [smul_smul, hsq, one_smul]
  conv_lhs => rw [← hW]
  exact Place.ord_smul (frickeInvolutionBar N) (frickeInvolutionBar N • W) f

end ZXGauss0

open ZXGauss0 in

theorem solution
    (p : ℕ) [Fact p.Prime] (n : ℕ) (f : modularFunctionFieldBar (1 * p))
    (hf : f ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ))) (hf0 : f ≠ 0)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      ∀ k : ℤ, c * ((frickeInvolutionBar (1 * p) f : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A := by
  haveI hP : Fact (1 * p).Prime := ⟨by rw [Nat.one_mul]; exact Fact.out⟩
  have hp2 : (2 : ℤ) ≤ ((1 * p : ℕ) : ℤ) := by
    have := (Fact.out : (1 * p).Prime).two_le; exact_mod_cast this
  set w := frickeInvolutionBar (1 * p) with hw_def

  have hmemU : modularUnitSeries (1 * p) ∈ modularFunctionFieldFull (1 * p) :=
    modularUnitSeries_mem_modularFunctionFieldFull (1 * p)
  set u : modularFunctionFieldBar (1 * p) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * p)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmemU⟩ with hu_def
  have hu_inf : (cuspInftyBar (1 * p)).ord u = 1 - ((1 * p : ℕ) : ℤ) :=
    ord_cuspInftyBar_coeffEmb_modularUnitSeries (1 * p) hmemU
  have hu_zero : (cuspZeroBar (1 * p)).ord u = ((1 * p : ℕ) : ℤ) - 1 :=
    ord_cuspZeroBar_coeffEmb_modularUnitSeries (1 * p) hmemU
  have hu_else : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)),
      W ≠ cuspInftyBar (1 * p) → W ≠ cuspZeroBar (1 * p) → W.ord u = 0 := by
    intro W h1 h2
    apply ord_coeffEmb_modularUnitSeries_of_not_isCusp (1 * p) hmemU W
    intro hc
    rcases eq_cuspInftyBar_or_eq_cuspZeroBar (1 * p) W hc with h | h
    · exact h1 h
    · exact h2 h
  have hne : cuspZeroBar (1 * p) ≠ cuspInftyBar (1 * p) := by
    intro h; rw [h] at hu_zero; rw [hu_zero] at hu_inf; omega
  have hu0 : u ≠ 0 := by
    intro h
    have h' : coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * p)) = 0 := congrArg Subtype.val h
    exact modularUnitSeries_ne_zero (1 * p) (((coeffEmb (AlgebraicClosure ℚ)).injective.eq_iff' (map_zero _)).mp h')

  set g : modularFunctionFieldBar (1 * p) := w f with hg_def
  have hg0 : g ≠ 0 := by
    intro h; apply hf0; exact (EmbeddingLike.map_eq_zero_iff (f := w)).mp h
  have hford : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)),
      -(((n : ℤ) • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ)) V) ≤ V.ord f := fun V =>
    ((mem_riemannRochSpace_iff.mp hf) V).resolve_left hf0
  have hf_inf : -(n : ℤ) ≤ (cuspInftyBar (1 * p)).ord f := by
    have := hford (cuspInftyBar (1 * p)); simpa using this
  have hf_off : ∀ V, V ≠ cuspInftyBar (1 * p) → 0 ≤ V.ord f := by
    intro V hV; have := hford V
    rw [Finsupp.smul_apply] at this
    first
    | rw [Finsupp.single_eq_of_ne hV, smul_zero, neg_zero] at this
    | rw [Finsupp.single_eq_of_ne (Ne.symm hV), smul_zero, neg_zero] at this
    exact this
  have hgord : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord g = (w • W).ord f :=
    fun W => ord_frickeInvolutionBar (1 * p) W f
  have hzero_def : cuspZeroBar (1 * p) = w • cuspInftyBar (1 * p) := cuspZeroBar_def (1 * p)
  have hsq : w * w = 1 :=
    AlgEquiv.ext fun x => by rw [AlgEquiv.mul_apply, hw_def, frickeInvolutionBar_frickeInvolutionBar]; rfl
  have hwzero : w • cuspZeroBar (1 * p) = cuspInftyBar (1 * p) := by
    rw [hzero_def, smul_smul, hsq, one_smul]

  set h : modularFunctionFieldBar (1 * p) := g * u ^ n with hh_def
  have hh0 : h ≠ 0 := mul_ne_zero hg0 (pow_ne_zero _ hu0)
  have hhord : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)),
      W.ord h = (w • W).ord f + (n : ℤ) * W.ord u := by
    intro W
    rw [hh_def, W.ord_mul hg0 (pow_ne_zero _ hu0), hgord, ← zpow_natCast, W.ord_zpow]
  set M : ℕ := n * (1 * p) with hM_def
  have hmem : h ∈ riemannRochSpace ((M : ℤ) • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ)) := by
    rw [mem_riemannRochSpace_iff]
    intro V
    right
    rw [hhord V]
    by_cases hVi : V = cuspInftyBar (1 * p)
    · subst hVi
      rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, hu_inf]
      have h0 : 0 ≤ (w • cuspInftyBar (1 * p)).ord f := hf_off _ (by rw [← hzero_def]; exact hne)
      have : (M : ℤ) = (n : ℤ) * ((1 * p : ℕ) : ℤ) := by rw [hM_def]; push_cast; ring
      nlinarith
    · rw [Finsupp.smul_apply]
      first
      | rw [Finsupp.single_eq_of_ne hVi, smul_zero, neg_zero]
      | rw [Finsupp.single_eq_of_ne (Ne.symm hVi), smul_zero, neg_zero]
      have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
      by_cases hVz : V = cuspZeroBar (1 * p)
      · subst hVz
        rw [hwzero, hu_zero]
        nlinarith
      · rw [hu_else V hVi hVz, mul_zero, add_zero]
        apply hf_off
        intro hV
        apply hVz
        have := congrArg (fun P => w • P) hV
        simp only [smul_smul, hsq, one_smul] at this
        rw [this, ← hzero_def]

  obtain ⟨c, hc0, hcA, -⟩ :=
    exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits (1 * p) M h hmem hh0 A
      (Fact.out : p.Prime) hA
  refine ⟨c, hc0, fun k => ?_⟩

  have hgu : g = h * u⁻¹ ^ n := by
    rw [hh_def, mul_assoc, ← mul_pow, mul_inv_cancel₀ hu0, one_pow, mul_one]
  have hcoe_u : ((u⁻¹ ^ n : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) ((modularUnitSeries (1 * p))⁻¹ ^ n) := by
    rw [map_pow, map_inv₀]
    simp [hu_def]

  have key : ∀ m : ℕ, ∃ Z : LaurentSeries ℤ, coeffMap (Int.castRingHom ℚ) Z = (modularUnitSeries (1 * p))⁻¹ ^ m :=
    fun m => ⟨(unitInvInt (1 * p)) ^ m, by rw [map_pow, coeffMap_unitInvInt]⟩
  have hint : ∀ j : ℤ, (coeffEmb (AlgebraicClosure ℚ) ((modularUnitSeries (1 * p))⁻¹ ^ n)).coeff j ∈ A := by
    intro j
    obtain ⟨Z, hZ⟩ := key n
    rw [coeffEmb_coeff, ← hZ, coeffMap_coeff]
    show algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) (Z.coeff j)) ∈ A
    rw [eq_intCast, map_intCast]
    exact intCast_mem A (Z.coeff j)
  have hch : ∀ j : ℤ, c * (h : LaurentSeries (AlgebraicClosure ℚ)).coeff j ∈ A := by
    intro j
    have := hcA j
    first
    | rw [IntermediateField.coe_smul] at this
    | push_cast at this
    first
    | (simp only [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul,
        HahnSeries.coeff_smul, smul_eq_mul] at this; exact this)
    | exact this
    | (convert this using 2)
  rw [hgu]
  show c * ((h : LaurentSeries (AlgebraicClosure ℚ)) *
      ((u⁻¹ ^ n : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ))).coeff k ∈ A
  rw [hcoe_u, HahnSeries.coeff_mul, Finset.mul_sum]
  refine sum_mem fun ij _ => ?_
  rw [← mul_assoc]
  exact mul_mem (hch _) (hint _)

end S_ModularCurve_exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar
end P2MW
export P2MW.S_ModularCurve_exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar (solution)
