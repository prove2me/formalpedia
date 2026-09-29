-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2b977f69-3ff8-5e61-9083-938b102c365f

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_exists_int_poly_natDegree_aeval_jFull_eq_mul_aeval_modularUnitSeries
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_Module_Finite_quotient_of_isUnit_leadingCoeff_of_mem
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_GaloisRep_ratLocalizedAt_isUnit_iff
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel Polynomial AlgebraicGeometry.Polynomial"
open scoped MatrixGroups

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

namespace FinH

p2m_open "Polynomial AlgebraicGeometry.Polynomial ModularCurve ModularCurve.XHDRLevel AlgebraicCurve"

theorem ringHom_aeval_int {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T) (x : S) (P : ℤ[X]) :
    φ (Polynomial.aeval x P) = Polynomial.aeval (φ x) P := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

theorem finrank_quotient_le_mul_natDegree
    (R : Type*) [CommRing R] [Nontrivial R] (A : Type*) [CommRing A] [Algebra R A] [Algebra R[X] A]
    [IsScalarTower R R[X] A] (m : ℕ) (f : (Fin m → R[X]) →ₗ[R[X]] A) (hf : Function.Surjective f)
    (N : R[X]) (hN : IsUnit N.leadingCoeff) (I : Ideal A) (hNI : algebraMap R[X] A N ∈ I) :
    Module.finrank R (A ⧸ I) ≤ m * N.natDegree := by
  classical
  obtain ⟨u, hu⟩ := hN

  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : R[X], N₁ = Polynomial.C (↑u⁻¹ : R) * N := ⟨_, rfl⟩
  have hmon : N₁.Monic := by
    rw [hN₁]
    exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu, Units.inv_mul])
  have hdeg : N₁.natDegree = N.natDegree := by
    rw [hN₁]
    exact Polynomial.natDegree_C_mul_of_mul_ne_zero (by rw [← hu, Units.inv_mul]; exact one_ne_zero)
  have hN₁I : algebraMap R[X] A N₁ ∈ I := by
    rw [hN₁, map_mul]
    exact I.mul_mem_left _ hNI

  obtain ⟨a, ha⟩ : ∃ a : A, a = algebraMap R[X] A Polynomial.X := ⟨_, rfl⟩
  have hX : (Polynomial.aeval a : R[X] →ₐ[R] A) = IsScalarTower.toAlgHom R R[X] A :=
    Polynomial.algHom_ext (by rw [Polynomial.aeval_X, IsScalarTower.toAlgHom_apply, ha])
  have hX' : ∀ P : R[X], Polynomial.aeval a P = algebraMap R[X] A P := fun P => by
    rw [hX, IsScalarTower.toAlgHom_apply]

  have hroot : N₁.eval₂ (↑(Algebra.ofId R (A ⧸ I)) : R →+* A ⧸ I) (Ideal.Quotient.mk I a) = 0 := by
    have h1 : (↑(Algebra.ofId R (A ⧸ I)) : R →+* A ⧸ I) = (Ideal.Quotient.mk I).comp (algebraMap R A) := rfl
    rw [h1, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hX', Ideal.Quotient.eq_zero_iff_mem]
    exact hN₁I
  let ψ : AdjoinRoot N₁ →ₐ[R] A ⧸ I := AdjoinRoot.liftAlgHom N₁ (Algebra.ofId R (A ⧸ I)) (Ideal.Quotient.mk I a) hroot
  have hψ : ∀ P : R[X], ψ (AdjoinRoot.mk N₁ P) = Ideal.Quotient.mk I (algebraMap R[X] A P) := by
    intro P
    change AdjoinRoot.liftAlgHom N₁ (Algebra.ofId R (A ⧸ I)) (Ideal.Quotient.mk I a) hroot (AdjoinRoot.mk N₁ P) = _
    rw [AdjoinRoot.liftAlgHom_mk]
    have h1 : (↑(Algebra.ofId R (A ⧸ I)) : R →+* A ⧸ I) = (Ideal.Quotient.mk I).comp (algebraMap R A) := rfl
    rw [h1, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hX']

  let gen : Fin m → A := fun i => f (fun j => if i = j then 1 else 0)
  let Φ : (Fin m → AdjoinRoot N₁) →ₗ[R] A ⧸ I :=
    { toFun := fun w => ∑ i, ψ (w i) * Ideal.Quotient.mk I (gen i)
      map_add' := fun w w' => by
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r w => by
        simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply] }
  have hΦ : Function.Surjective Φ := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨w, rfl⟩ := hf x
    refine ⟨fun i => AdjoinRoot.mk N₁ (w i), ?_⟩
    change ∑ i, ψ (AdjoinRoot.mk N₁ (w i)) * Ideal.Quotient.mk I (gen i) = Ideal.Quotient.mk I (f w)
    rw [LinearMap.pi_apply_eq_sum_univ f w, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψ, Algebra.smul_def, map_mul]

  let pb := AdjoinRoot.powerBasis' hmon
  haveI : Module.Free R (AdjoinRoot N₁) := Module.Free.of_basis pb.basis
  haveI : Module.Finite R (AdjoinRoot N₁) := Module.Finite.of_basis pb.basis
  have hrk : Module.finrank R (Fin m → AdjoinRoot N₁) = m * N.natDegree := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, pb.finrank,
      ← hdeg]
    rfl
  calc Module.finrank R (A ⧸ I) = Module.finrank R ↥(LinearMap.range Φ) := by
        rw [LinearMap.range_eq_top.mpr hΦ, finrank_top]
    _ ≤ Module.finrank R (Fin m → AdjoinRoot N₁) := LinearMap.finrank_range_le Φ
    _ = m * N.natDegree := hrk

theorem gammaM_le_gamma0 (p M : ℕ) (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) :
    ΓM M H ≤ CongruenceSubgroup.Gamma0 p := by
  intro γ hγ
  have h0 : γ ∈ CongruenceSubgroup.Gamma0 M := CohCarrier.GammaH_le_Gamma0 H hγ
  rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
  have := congrArg (ZMod.castHom hpM (ZMod p)) h0
  rwa [map_intCast, map_zero] at this

theorem full_le (p M : ℕ) [NeZero p] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) :
    modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H) := by
  rw [← modularFunctionFieldFullC_rat]
  exact (modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ p).trans
    (qExpFunctionFieldC_mono ℚ (gammaM_le_gamma0 p M H hpM))

noncomputable def incl (p M : ℕ) [NeZero p] (H : Subgroup (ZMod M)ˣ)
    (hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H)) :
    ↥(modularFunctionFieldFull p) →ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)) :=
  (RingHomClass.toRingHom (IntermediateField.inclusion hle)).toRatAlgHom

theorem coe_incl (p M : ℕ) [NeZero p] (H : Subgroup (ZMod M)ˣ)
    (hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H)) (x : ↥(modularFunctionFieldFull p)) :
    ((incl p M H hle x : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) := by
  rw [incl, RingHom.toRatAlgHom_apply, RingHom.coe_coe, IntermediateField.coe_inclusion]

theorem incl_jFull (p M : ℕ) [NeZero p] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H)) :
    incl p M H hle (IgusaScheme.jFull p) = jAt (ΓM M H) hj := by
  apply Subtype.ext
  rw [coe_incl, IgusaScheme.coe_jFull, coe_jAt, jqModC_rat]

theorem incl_mem_chartAlgFin (p M : ℕ) [Fact p.Prime] [NeZero p] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H))
    {a : ↥(modularFunctionFieldFull p)}
    (ha : a ∈ TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :
    incl p M H hle a ∈ chartAlgFin p (ΓM M H) hj := by
  classical
  set ι := incl p M H hle with hιdef
  let θℤ : ↥(modularFunctionFieldFull p) →ₐ[ℤ] ↥(qExpFunctionFieldC ℚ (ΓM M H)) := ι.toRingHom.toIntAlgHom
  have hmapadj : ∀ x ∈ Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)),
      ι x ∈ Algebra.adjoin (R p) ({jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by
    intro x hx
    have h1 : θℤ x ∈ (Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))).map θℤ :=
      Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩
    rw [AlgHom.map_adjoin, Set.image_singleton] at h1
    have h2 : Algebra.adjoin ℤ ({θℤ (IgusaScheme.jFull p)} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))) ≤
        (Algebra.adjoin (R p) ({jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)))).restrictScalars ℤ := by
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      show ι (IgusaScheme.jFull p) ∈ Algebra.adjoin (R p) ({jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)))
      rw [hιdef, incl_jFull p M H hj hle]
      exact Algebra.subset_adjoin rfl
    exact h2 h1
  let φ : ↥(Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))) →+*
      ↥(Algebra.adjoin (R p) ({jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)))) :=
    RingHom.codRestrict (ι.toRingHom.comp
      (Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))).toSubring.subtype) _
      (fun x => hmapadj x x.2)
  have hcomp : (algebraMap ↥(Algebra.adjoin (R p) ({jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))))
        ↥(qExpFunctionFieldC ℚ (ΓM M H))).comp φ =
      ι.toRingHom.comp (algebraMap ↥(Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)))
        ↥(modularFunctionFieldFull p)) := by
    ext x
    rfl
  rw [TwoChartIntegralModel.mem_chartAlg_iff] at ha ⊢
  exact ha.map_of_comp_eq φ ι.toRingHom hcomp

end FinH

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (v : ↥(chartAlgFin p (ΓM M H) hj))
    (hv : ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = modularUnitSeries p ∨
      ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 * (modularUnitSeries p)⁻¹) :
    ∃ K : ℕ, ∀ g : ℤ[X], g.Monic → ¬ (p : ℤ) ∣ g.coeff 0 →
      Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
      Module.finrank (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v g}) ≤ K * g.natDegree := by
  classical
  haveI hpF : Fact p.Prime := inferInstance
  haveI : NeZero p := ⟨hpF.out.ne_zero⟩
  haveI : IsPrincipalIdealRing (R p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p

  obtain ⟨jA, hjA⟩ : ∃ jA : ↥(chartAlgFin p (ΓM M H) hj), jA = jChartFin p (ΓM M H) hj := ⟨_, rfl⟩
  letI algRXA : Algebra (R p)[X] ↥(chartAlgFin p (ΓM M H) hj) := (Polynomial.aeval jA).toRingHom.toAlgebra
  haveI istRXA : IsScalarTower (R p) (R p)[X] ↥(chartAlgFin p (ΓM M H) hj) :=
    IsScalarTower.of_algebraMap_eq' (Polynomial.aeval jA).comp_algebraMap.symm
  have halgXA : ∀ P : (R p)[X], algebraMap (R p)[X] ↥(chartAlgFin p (ΓM M H) hj) P = Polynomial.aeval jA P :=
    fun _ => rfl
  have hjM : ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = jqModC ℚ := coe_jAt _ hj
  have htjℚ : Transcendental ℚ (jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by
    intro halg
    obtain ⟨P, hP, hev⟩ := halg
    refine ModularCurve.transcendental_jq ⟨P, hP, ?_⟩
    have h0' : (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) (LaurentSeries ℚ))
        ((Polynomial.aeval (jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))) P) = 0 := by
      rw [hev, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
        show (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) (LaurentSeries ℚ)) (jAt (ΓM M H) hj) = jq from hjM] at h0'
    rw [Polynomial.aeval_def]
    convert h0' using 2 <;> first | rfl | exact Subsingleton.elim _ _
  have htj : Transcendental (R p) (jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) := fun h =>
    htjℚ ((IsFractionRing.isAlgebraic_iff (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H))).mp h)
  haveI hFI_M : (ΓM M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)
  have hTM : ModularGroup.T ∈ ΓM M H := translation_mem_GammaH M H

  have hFD :=
    (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ (ΓM M H) hTM (ΓM M H) le_rfl
      (fun γ hγ => Or.inl hγ) (jAt (ΓM M H) hj) hjM).1
  haveI := hFD
  have hIST : @IsScalarTower (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) _
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))).toSMul _ :=
    @IsScalarTower.of_algebraMap_eq' (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) _ _ _ _
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))) _
      (RingHom.ext fun r => by
        show ((r : ℚ) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) =
          @algebraMap ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))) (r : ℚ)
        exact (eq_ratCast _ _).symm)
  have hfin' := (@AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf (R p) _ _ _ _
    ℚ _ _ _ ↥(qExpFunctionFieldC ℚ (ΓM M H)) _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))) hIST
    (jAt (ΓM M H) hj) _ htj hFD inferInstance).1
  have hfin : Module.Finite (R p)[X] ↥(chartAlgFin p (ΓM M H) hj) := by
    subst hjA
    exact hfin'
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (R p)[X] ↥(chartAlgFin p (ΓM M H) hj)
  refine ⟨m * (p - 1), fun g hg hq0 => ?_⟩
  by_cases hD : g.natDegree = 0
  ·
    have hg1 : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hg hD
    subst hg1
    have htop : Ideal.span {Polynomial.aeval v (1 : ℤ[X])} = (⊤ : Ideal ↥(chartAlgFin p (ΓM M H) hj)) := by
      rw [map_one, Ideal.span_singleton_one]
    haveI : Subsingleton (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (1 : ℤ[X])}) :=
      Ideal.Quotient.subsingleton_iff.mpr htop
    exact ⟨inferInstance, by rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _⟩
  have hD1 : 1 ≤ g.natDegree := Nat.one_le_iff_ne_zero.mpr hD
  have h0 : g.coeff 0 ≠ 0 := fun h => hq0 (h ▸ dvd_zero _)

  have hmemq : modularUnitSeries p ∈ modularFunctionFieldFull p :=
    ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull p
  have hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H) := FinH.full_le p M H hpM
  let ι : ↥(modularFunctionFieldFull p) →+* ↥(qExpFunctionFieldC ℚ (ΓM M H)) := (FinH.incl p M H hle).toRingHom
  have hιcoe : ∀ x : ↥(modularFunctionFieldFull p), ((ι x : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) :=
    fun x => FinH.coe_incl p M H hle x
  have hιj : ι (IgusaScheme.jFull p) = jAt (ΓM M H) hj := FinH.incl_jFull p M H hj hle
  obtain ⟨vq, hvq, hιv⟩ : ∃ vq : ↥(modularFunctionFieldFull p),
      (vq = ⟨modularUnitSeries p, hmemq⟩ ∨
        vq = (p : ↥(modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmemq⟩ : ↥(modularFunctionFieldFull p))⁻¹) ∧
      ι vq = (v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by
    rcases hv with h | h
    · refine ⟨_, Or.inl rfl, Subtype.ext ?_⟩
      rw [hιcoe, h]
    · refine ⟨_, Or.inr rfl, Subtype.ext ?_⟩
      rw [hιcoe, h]
      push_cast
      rfl
  obtain ⟨N, ε, k, c, hdegN, hlcN, hcA, hNc⟩ :=
    ModularCurve.exists_int_poly_natDegree_aeval_jFull_eq_mul_aeval_modularUnitSeries p hmemq vq hvq g hg hD1 h0

  have hcA' : ι c ∈ chartAlgFin p (ΓM M H) hj := FinH.incl_mem_chartAlgFin p M H hj hle hcA
  obtain ⟨c', hc'⟩ : ∃ c' : ↥(chartAlgFin p (ΓM M H) hj), c' = ⟨ι c, hcA'⟩ := ⟨_, rfl⟩

  have hNF : Polynomial.aeval (jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) N =
      ι c * Polynomial.aeval (v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) g := by
    have h := congrArg ι hNc
    rw [map_mul, FinH.ringHom_aeval_int, FinH.ringHom_aeval_int, hιj, hιv] at h
    exact h
  have hNA : Polynomial.aeval jA N = c' * Polynomial.aeval v g := by
    have e1 : ((Polynomial.aeval jA N : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) =
        Polynomial.aeval (jA : ↥(qExpFunctionFieldC ℚ (ΓM M H))) N :=
      FinH.ringHom_aeval_int (chartAlgFin p (ΓM M H) hj).val.toRingHom jA N
    have e2 : ((Polynomial.aeval v g : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) =
        Polynomial.aeval (v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) g :=
      FinH.ringHom_aeval_int (chartAlgFin p (ΓM M H) hj).val.toRingHom v g
    have e3 : ((c' * Polynomial.aeval v g : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) =
        (c' : ↥(qExpFunctionFieldC ℚ (ΓM M H))) *
          ((Polynomial.aeval v g : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) := rfl
    apply Subtype.ext
    rw [e3, e2, e1, hjA, hc']
    exact hNF

  have hlcU : IsUnit (algebraMap ℤ (R p) N.leadingCoeff) := by
    rw [hlcN, map_mul, map_pow]
    refine ((Units.isUnit ε).map _).mul (IsUnit.pow _ ?_)
    rw [GaloisRep.ratLocalizedAt.isUnit_iff hpF.out]
    have hcoe : (((algebraMap ℤ (R p) (g.coeff 0) : R p)) : ℚ) = ((g.coeff 0 : ℤ) : ℚ) := by simp
    rw [hcoe, Rat.num_intCast, ← Int.ofNat_dvd_left]
    exact hq0

  obtain ⟨NR, hNR⟩ : ∃ NR : (R p)[X], NR = N.map (algebraMap ℤ (R p)) := ⟨_, rfl⟩
  have hlc' : IsUnit NR.leadingCoeff := by
    rwa [hNR, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (algebraMap ℤ (R p)) hlcU.ne_zero]
  have hdegNR : NR.natDegree = g.natDegree * (p - 1) := by
    rw [hNR, Polynomial.natDegree_map_of_leadingCoeff_ne_zero (algebraMap ℤ (R p)) hlcU.ne_zero, hdegN]
  have hmapN : algebraMap (R p)[X] ↥(chartAlgFin p (ΓM M H) hj) NR = Polynomial.aeval jA N := by
    rw [halgXA, hNR, Polynomial.aeval_map_algebraMap]
  have hmemI : algebraMap (R p)[X] ↥(chartAlgFin p (ΓM M H) hj) NR ∈
      Ideal.span {Polynomial.aeval v g} := by
    rw [hmapN, hNA]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  refine ⟨Module.Finite.quotient_of_isUnit_leadingCoeff_of_mem (R p) ↥(chartAlgFin p (ΓM M H) hj) NR hlc' _ hmemI,
    ?_⟩
  calc Module.finrank (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v g})
        ≤ m * NR.natDegree :=
          FinH.finrank_quotient_le_mul_natDegree (R p) ↥(chartAlgFin p (ΓM M H) hj) m f hf NR hlc' _ hmemI
    _ = m * (p - 1) * g.natDegree := by rw [hdegNR]; ring

end S_ModularCurve_XHDRModelAtP_exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin (solution)
