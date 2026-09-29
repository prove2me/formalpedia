-- Prove2me | solution 1 for ModularCurve.exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/cb6c2879-4b5a-57c1-b59a-4da33afd7b99

import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_AlgebraicCurve_Place_hasValue_iff_mem_and_eq_or_ord_sub_pos
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option Elab.async false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue.ModularCurve Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint jqModC modularFunctionFieldC jqModC_mem transcendental_jqModC"
namespace JLineAlgebra
p2m_open "ModularCurve"

section Transport

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)

theorem mem_congrRingEquiv_iff (v : Place K F) (f : F) :
    e f ∈ (Place.congrRingEquiv e he v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
  rw [Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
  show e.symm (e f) ∈ v.toValuationSubring ↔ _
  rw [e.symm_apply_apply]

theorem hasValue_congrRingEquiv_iff (v : Place K F) (f : F) (c : K) :
    (Place.congrRingEquiv e he v).HasValue (e f) c ↔ v.HasValue f c := by
  rw [Place.hasValue_iff_mem_and_eq_or_ord_sub_pos, Place.hasValue_iff_mem_and_eq_or_ord_sub_pos,
    mem_congrRingEquiv_iff, ← he c, ← map_sub, Place.ord_congrRingEquiv, e.injective.eq_iff]

end Transport

section Poly

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

theorem finitePlace_ne_placeInfty {p : K[X]} (hp : Irreducible p) :
    RationalFunctionField.finitePlace K hp ≠ RationalFunctionField.placeInfty K := by
  intro h
  have h1 : (algebraMap K[X] (RatFunc K) X) ∈ (RationalFunctionField.finitePlace K hp).toValuationSubring :=
    RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K _ _
  rw [h, RatFunc.algebraMap_X] at h1
  have h2 := (Place.mem_iff_ord_nonneg _ RatFunc.X_ne_zero).mp h1
  rw [RationalFunctionField.ord_placeInfty_X] at h2
  exact absurd h2 (by norm_num)

theorem exists_eq_algebraMap_of_forall_ord_nonneg (r : RatFunc K)
    (hr : ∀ w : Place K (RatFunc K), w ≠ RationalFunctionField.placeInfty K → 0 ≤ w.ord r) :
    ∃ P : K[X], r = algebraMap K[X] (RatFunc K) P := by
  classical

  by_contra hne
  have hden1 : r.denom ≠ 1 := by
    intro h1
    exact hne ⟨r.num, by conv_lhs => rw [← RatFunc.num_div_denom r, h1, map_one, div_one]⟩
  have hdu : ¬ IsUnit r.denom := fun hu => hden1 (r.monic_denom.eq_one_of_isUnit hu)
  obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hdu r.denom_ne_zero
  set w := RationalFunctionField.finitePlace K hp with hw
  have hw' : w = Place.ofHeightOneSpectrum (RationalFunctionField.heightOneSpectrumOfIrreducible K hp) := rfl

  have hden0 : algebraMap K[X] (RatFunc K) r.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr r.denom_ne_zero
  have hden_pos : 0 < w.ord (algebraMap K[X] (RatFunc K) r.denom) := by
    have hne0 : w.ord (algebraMap K[X] (RatFunc K) r.denom) ≠ 0 := by
      rw [hw', Place.ord_ofHeightOneSpectrum_ne_zero_iff _ r.denom_ne_zero,
        RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton]
      exact hpd
    have hge : 0 ≤ w.ord (algebraMap K[X] (RatFunc K) r.denom) :=
      (Place.mem_iff_ord_nonneg _ hden0).mp (RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K _ _)
    omega

  have hnum : r.num ≠ 0 := by
    intro h0
    apply hne
    refine ⟨0, ?_⟩
    rw [map_zero]
    exact RatFunc.num_eq_zero_iff.mp h0
  have hnum0 : algebraMap K[X] (RatFunc K) r.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hnum
  have hnum_ord : w.ord (algebraMap K[X] (RatFunc K) r.num) = 0 := by
    by_contra hne0
    have hne0' := (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K)
      (RationalFunctionField.heightOneSpectrumOfIrreducible K hp) hnum).mp (hw' ▸ hne0)
    rw [RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton] at hne0'

    have hcop := RatFunc.isCoprime_num_denom r
    exact hp.not_isUnit (hcop.isUnit_of_dvd' hne0' hpd)

  have hlt : w.ord r < 0 := by
    have e1 : r = algebraMap K[X] (RatFunc K) r.num / algebraMap K[X] (RatFunc K) r.denom :=
      (RatFunc.num_div_denom r).symm
    rw [e1, div_eq_mul_inv, w.ord_mul hnum0 (inv_ne_zero hden0), w.ord_inv, hnum_ord]
    omega
  exact absurd (hr w (finitePlace_ne_placeInfty hp)) (not_le.mpr hlt)

end Poly

theorem algebraMap_ratFunc_eq_aeval {K : Type*} [Field K] (P : K[X]) :
    algebraMap K[X] (RatFunc K) P = aeval (RatFunc.X : RatFunc K) P := by
  have h : (IsScalarTower.toAlgHom K K[X] (RatFunc K)) = aeval (RatFunc.X : RatFunc K) := by
    apply Polynomial.algHom_ext
    simp [RatFunc.algebraMap_X]
  exact DFunLike.congr_fun h P

end ModularCurve.JLineAlgebra

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open ModularCurve.JLineAlgebra in
theorem solution
    {k : Type*} [Field k] [DecidableEq k] [DecidableEq (RatFunc k)] (S₀ : Finset k) (c : k) (n : ℕ)
    (φ : ↥(modularFunctionFieldC k 1))
    (hreg : ∀ v : Place k ↥(modularFunctionFieldC k 1),
      v ≠ charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) → 0 ≤ v.ord φ)
    (hinf : -(n : ℤ) ≤ (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord φ)
    (hval : ∀ a ∈ S₀, (charLGeomPlaceOfPoint k a).HasValue φ c) :
    ∃ Q : Polynomial k, (Q ≠ 0 → Q.natDegree + S₀.card ≤ n) ∧
      φ = algebraMap k ↥(modularFunctionFieldC k 1) c
        + (∏ a ∈ S₀, ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))
            - algebraMap k ↥(modularFunctionFieldC k 1) a))
          * Polynomial.aeval (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) Q := by
  classical

  set e := ratFuncEquivCharLOneC k with he_def
  have he : ∀ a : k, e.toRingEquiv (algebraMap k (RatFunc k) a) = algebraMap k _ a := fun a => e.commutes a
  have hX : e RatFunc.X = ⟨jqModC k, jqModC_mem k 1⟩ := by
    apply Subtype.ext
    show ((ratFuncEquivCharLOneC k RatFunc.X : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = jqModC k
    rw [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
    exact RatFunc.algEquivOfTranscendental_X (jqModC k) (transcendental_jqModC k)
  have hplace : ∀ w : Place k (RatFunc k),
      charLGeomPlaceEquiv k w = Place.congrRingEquiv e.toRingEquiv he w := fun w => rfl
  set ψ := e.symm φ with hψ
  have hφ : φ = e.toRingEquiv ψ := (e.apply_symm_apply φ).symm

  have hreg' : ∀ w : Place k (RatFunc k), w ≠ RationalFunctionField.placeInfty k → 0 ≤ w.ord ψ := by
    intro w hw
    have h := hreg (charLGeomPlaceEquiv k w)
      (fun h => hw ((charLGeomPlaceEquiv k).injective h))
    rwa [hplace, hφ, Place.ord_congrRingEquiv] at h

  obtain ⟨P, hP⟩ := exists_eq_algebraMap_of_forall_ord_nonneg ψ hreg'

  have hPdeg : P.natDegree ≤ n := by
    rcases eq_or_ne P 0 with rfl | hP0
    · simp
    have h := hinf
    rw [hplace, hφ, Place.ord_congrRingEquiv, hP, RationalFunctionField.ord_placeInfty_algebraMap hP0] at h
    omega

  have hroot : ∀ a ∈ S₀, (X - C a) ∣ (P - C c) := by
    intro a ha
    rw [dvd_iff_isRoot]
    have hv := hval a ha
    rw [show charLGeomPlaceOfPoint k a = Place.congrRingEquiv e.toRingEquiv he
        (RationalFunctionField.placeOfPoint k a) from rfl, hφ, hasValue_congrRingEquiv_iff,
      Place.hasValue_iff_mem_and_eq_or_ord_sub_pos, hP] at hv
    obtain ⟨-, h | h⟩ := hv
    ·
      have : P = C c := by
        apply IsFractionRing.injective k[X] (RatFunc k)
        rw [h, RatFunc.algebraMap_eq_C]; rfl
      simp [this]
    · rcases eq_or_ne (P - C c) 0 with h0 | h0
      · simp [h0]
      rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, ← map_sub,
        RationalFunctionField.ord_placeOfPoint_algebraMap a h0] at h
      exact (Polynomial.rootMultiplicity_pos h0).mp (by exact_mod_cast h)

  have hdvd : (∏ a ∈ S₀, (X - C a)) ∣ (P - C c) := by
    refine Finset.prod_dvd_of_coprime ?_ hroot
    intro a _ b _ hab
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
  obtain ⟨Q, hQ⟩ := hdvd
  refine ⟨Q, ?_, ?_⟩
  · intro hQ0
    have hmon : (∏ a ∈ S₀, (X - C a)).Monic := monic_prod_of_monic _ _ fun a _ => monic_X_sub_C a
    have hdeg1 : (P - C c).natDegree = S₀.card + Q.natDegree := by
      rw [hQ, hmon.natDegree_mul' hQ0,
        natDegree_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)]
      simp
    have hdeg2 : (P - C c).natDegree ≤ n :=
      (natDegree_sub_le _ _).trans (max_le hPdeg (by simp))
    omega
  ·
    have hC : ∀ a : k, e.toRingEquiv (algebraMap k[X] (RatFunc k) (C a)) = algebraMap k _ a := by
      intro a
      rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]
      exact he a
    have hXE : e.toRingEquiv (algebraMap k[X] (RatFunc k) X) = ⟨jqModC k, jqModC_mem k 1⟩ := by
      rw [RatFunc.algebraMap_X]; exact hX
    have hQE : e.toRingEquiv (algebraMap k[X] (RatFunc k) Q)
        = Polynomial.aeval (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) Q := by
      rw [algebraMap_ratFunc_eq_aeval, ← hX]
      exact (Polynomial.aeval_algHom_apply e.toAlgHom RatFunc.X Q).symm
    have h1 : φ = e.toRingEquiv (algebraMap k[X] (RatFunc k) ((∏ a ∈ S₀, (X - C a)) * Q + C c)) := by
      rw [← sub_add_cancel P (C c), hQ] at hP
      rw [hφ, hP]

    set E := e.toRingEquiv with hE
    set ι := algebraMap k[X] (RatFunc k) with hι
    have h2 : E (ι ((∏ a ∈ S₀, (X - C a)) * Q + C c))
        = (∏ a ∈ S₀, ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))
            - algebraMap k ↥(modularFunctionFieldC k 1) a))
          * Polynomial.aeval (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) Q
          + algebraMap k ↥(modularFunctionFieldC k 1) c := by
      rw [ι.map_add, ι.map_mul, map_prod ι, E.map_add, E.map_mul, map_prod E, hC, hQE]
      congr 2
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [ι.map_sub, E.map_sub, hXE, hC]
    rw [h1, h2, add_comm]

end S_ModularCurve_exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue
end P2MW
export P2MW.S_ModularCurve_exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue (solution)
