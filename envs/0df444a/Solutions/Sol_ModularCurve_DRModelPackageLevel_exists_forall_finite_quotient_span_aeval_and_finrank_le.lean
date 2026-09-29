-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_forall_finite_quotient_span_aeval_and_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/86d5f083-84fe-50fc-9165-f0972d4dd4b9

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Theorems.Thm_ModularCurve_exists_int_poly_natDegree_aeval_jFull_eq_mul_aeval_modularUnitSeries
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Theorems.Thm_Module_Finite_quotient_of_isUnit_leadingCoeff_of_mem
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_GaloisRep_ratLocalizedAt_isUnit_iff
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_finite_quotient_span_aeval_and_finrank_le
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"

namespace C1FinLevel

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

private theorem ringHom_aeval_int {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T) (x : S) (P : ℤ[X]) :
    φ (Polynomial.aeval x P) = Polynomial.aeval (φ x) P := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

private theorem finrank_quotient_le_mul_natDegree
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

end C1FinLevel

open C1FinLevel in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hv : ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = modularUnitSeries q ∨
      ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = (q : LaurentSeries ℚ) ^ 12 * (modularUnitSeries q)⁻¹) :
    ∃ K : ℕ, ∀ g : ℤ[X], g.Monic → ¬ (q : ℤ) ∣ g.coeff 0 →
      Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
      Module.finrank (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v g}) ≤ K * g.natDegree := by
  classical
  haveI hqF : Fact q.Prime := inferInstance
  haveI : NeZero q := ⟨hqF.out.ne_zero⟩
  haveI : IsPrincipalIdealRing (R q) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt q
  haveI : IsFractionRing (R q) ℚ := GaloisRep.isFractionRing_ratLocalizedAt q

  obtain ⟨jA, hjA⟩ : ∃ jA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q), jA = IgusaScheme.jChartFin (N₀ * q) q := ⟨_, rfl⟩
  letI algRXA : Algebra (R q)[X] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := (Polynomial.aeval jA).toRingHom.toAlgebra
  haveI istRXA : IsScalarTower (R q) (R q)[X] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) :=
    IsScalarTower.of_algebraMap_eq' (Polynomial.aeval jA).comp_algebraMap.symm
  have halgXA : ∀ P : (R q)[X], algebraMap (R q)[X] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) P = Polynomial.aeval jA P :=
    fun _ => rfl
  have htjℚ : Transcendental ℚ (IgusaScheme.jFull (N₀ * q) : ↥(modularFunctionFieldFull (N₀ * q))) := by
    intro halg
    obtain ⟨P, hP, hev⟩ := halg
    refine ModularCurve.transcendental_jq ⟨P, hP, ?_⟩
    have h0' : (algebraMap ↥(modularFunctionFieldFull (N₀ * q)) (LaurentSeries ℚ))
        ((Polynomial.aeval (IgusaScheme.jFull (N₀ * q) : ↥(modularFunctionFieldFull (N₀ * q)))) P) = 0 := by
      rw [hev, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
        show (algebraMap ↥(modularFunctionFieldFull (N₀ * q)) (LaurentSeries ℚ)) (IgusaScheme.jFull (N₀ * q)) = jq from
          IgusaScheme.coe_jFull (N₀ * q)] at h0'
    rw [Polynomial.aeval_def]
    convert h0' using 2 <;> first | rfl | exact Subsingleton.elim _ _
  have htj : Transcendental (R q) (IgusaScheme.jFull (N₀ * q) : ↥(modularFunctionFieldFull (N₀ * q))) := fun h =>
    htjℚ ((IsFractionRing.isAlgebraic_iff (R q) ℚ ↥(modularFunctionFieldFull (N₀ * q))).mp h)
  have hFD := ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull (N₀ * q)
  haveI := hFD
  have hsep : Algebra.IsSeparable
      ↥(IntermediateField.adjoin ℚ ({IgusaScheme.jFull (N₀ * q)} : Set ↥(modularFunctionFieldFull (N₀ * q))))
      ↥(modularFunctionFieldFull (N₀ * q)) := inferInstance
  have hfin : Module.Finite (R q)[X] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := by
    subst hjA
    exact (AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf (R q) ℚ
      ↥(modularFunctionFieldFull (N₀ * q)) (IgusaScheme.jFull (N₀ * q)) htj hFD hsep).1
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (R q)[X] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)
  refine ⟨m * (q - 1), fun g hg hq0 => ?_⟩
  by_cases hD : g.natDegree = 0
  ·
    have hg1 : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hg hD
    subst hg1
    have htop : Ideal.span {Polynomial.aeval v (1 : ℤ[X])} = (⊤ : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) := by
      rw [map_one, Ideal.span_singleton_one]
    haveI : Subsingleton (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (1 : ℤ[X])}) :=
      Ideal.Quotient.subsingleton_iff.mpr htop
    exact ⟨inferInstance, by rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _⟩
  have hD1 : 1 ≤ g.natDegree := Nat.one_le_iff_ne_zero.mpr hD
  have h0 : g.coeff 0 ≠ 0 := fun h => hq0 (h ▸ dvd_zero _)

  have hmemq : modularUnitSeries q ∈ modularFunctionFieldFull q :=
    ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull q
  have hle : modularFunctionFieldFull q ≤ modularFunctionFieldFull (N₀ * q) := by
    apply IntermediateField.adjoin.mono
    rintro x ⟨d, hd, hdq, rfl⟩
    exact ⟨d, hd, hdq.trans (dvd_mul_left q N₀), rfl⟩
  let ι : ↥(modularFunctionFieldFull q) →+* ↥(modularFunctionFieldFull (N₀ * q)) :=
    { toFun := fun x => ⟨x.1, hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hιj : ι (IgusaScheme.jFull q) = IgusaScheme.jFull (N₀ * q) := rfl
  obtain ⟨vq, hvq, hιv⟩ : ∃ vq : ↥(modularFunctionFieldFull q),
      (vq = ⟨modularUnitSeries q, hmemq⟩ ∨
        vq = (q : ↥(modularFunctionFieldFull q)) ^ 12 * (⟨modularUnitSeries q, hmemq⟩ : ↥(modularFunctionFieldFull q))⁻¹) ∧
      ι vq = (v : ↥(modularFunctionFieldFull (N₀ * q))) := by
    rcases hv with h | h
    · exact ⟨_, Or.inl rfl, Subtype.ext h.symm⟩
    · refine ⟨_, Or.inr rfl, ?_⟩
      rw [map_mul, map_pow, map_inv₀, map_natCast]
      apply Subtype.ext
      rw [h]
      push_cast
      rfl
  obtain ⟨N, ε, k, c, hdegN, hlcN, hcA, hNc⟩ :=
    ModularCurve.exists_int_poly_natDegree_aeval_jFull_eq_mul_aeval_modularUnitSeries q hmemq vq hvq g hg hD1 h0

  have hcA' : ι c ∈ IgusaScheme.chartAlgFin (N₀ * q) q := by
    let A₀ : Subalgebra ℤ ↥(modularFunctionFieldFull q) := Algebra.adjoin ℤ {IgusaScheme.jFull q}
    let B₀ : Subalgebra ℤ ↥(modularFunctionFieldFull (N₀ * q)) := Algebra.adjoin ℤ {IgusaScheme.jFull (N₀ * q)}
    have hc' : IsIntegral A₀ c := hcA
    have hAB : ∀ y : ↥(modularFunctionFieldFull q), y ∈ A₀ → ι y ∈ B₀ := by
      intro y hy
      have hy' : y ∈ Subring.closure {IgusaScheme.jFull q} := by
        have : A₀ = subalgebraOfSubring (Subring.closure {IgusaScheme.jFull q}) := Algebra.adjoin_int _
        rw [this] at hy
        exact hy
      have hcl : Subring.closure {IgusaScheme.jFull q} ≤ B₀.toSubring.comap ι :=
        Subring.closure_le.mpr (Set.singleton_subset_iff.mpr (by
          change ι (IgusaScheme.jFull q) ∈ B₀
          rw [hιj]
          exact Algebra.subset_adjoin rfl))
      exact hcl hy'
    let φ : A₀ →+* B₀ := (ι.comp A₀.val.toRingHom).codRestrict B₀ (fun y => hAB y y.2)
    have hB : IsIntegral B₀ (ι c) := hc'.map_of_comp_eq φ ι (by ext; rfl)
    exact AlgebraicCurve.TwoChartIntegralModel.chartAlg_le_chartAlg ℤ ↥(modularFunctionFieldFull (N₀ * q))
      ↥(GaloisRep.ratLocalizedAt q) {IgusaScheme.jFull (N₀ * q)} (x := ι c) hB
  obtain ⟨c', hc'⟩ : ∃ c' : ↥(IgusaScheme.chartAlgFin (N₀ * q) q), c' = ⟨ι c, hcA'⟩ := ⟨_, rfl⟩

  have hNF : Polynomial.aeval (IgusaScheme.jFull (N₀ * q) : ↥(modularFunctionFieldFull (N₀ * q))) N =
      ι c * Polynomial.aeval (v : ↥(modularFunctionFieldFull (N₀ * q))) g := by
    have h := congrArg ι hNc
    rw [map_mul, ringHom_aeval_int, ringHom_aeval_int, hιj, hιv] at h
    exact h
  have hNA : Polynomial.aeval jA N = c' * Polynomial.aeval v g := by
    have e1 : ((Polynomial.aeval jA N : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) =
        Polynomial.aeval (jA : ↥(modularFunctionFieldFull (N₀ * q))) N :=
      ringHom_aeval_int (IgusaScheme.chartAlgFin (N₀ * q) q).val.toRingHom jA N
    have e2 : ((Polynomial.aeval v g : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) =
        Polynomial.aeval (v : ↥(modularFunctionFieldFull (N₀ * q))) g :=
      ringHom_aeval_int (IgusaScheme.chartAlgFin (N₀ * q) q).val.toRingHom v g
    have e3 : ((c' * Polynomial.aeval v g : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) =
        (c' : ↥(modularFunctionFieldFull (N₀ * q))) *
          ((Polynomial.aeval v g : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) := rfl
    apply Subtype.ext
    rw [e3, e2, e1, hjA, IgusaScheme.coe_jChartFin, hc']
    exact hNF

  have hlcU : IsUnit (algebraMap ℤ (R q) N.leadingCoeff) := by
    rw [hlcN, map_mul, map_pow]
    refine ((Units.isUnit ε).map _).mul (IsUnit.pow _ ?_)
    rw [GaloisRep.ratLocalizedAt.isUnit_iff hqF.out]
    have hcoe : (((algebraMap ℤ (R q) (g.coeff 0) : R q)) : ℚ) = ((g.coeff 0 : ℤ) : ℚ) := by simp
    rw [hcoe, Rat.num_intCast, ← Int.ofNat_dvd_left]
    exact hq0

  obtain ⟨NR, hNR⟩ : ∃ NR : (R q)[X], NR = N.map (algebraMap ℤ (R q)) := ⟨_, rfl⟩
  have hlc' : IsUnit NR.leadingCoeff := by
    rwa [hNR, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (algebraMap ℤ (R q)) hlcU.ne_zero]
  have hdegNR : NR.natDegree = g.natDegree * (q - 1) := by
    rw [hNR, Polynomial.natDegree_map_of_leadingCoeff_ne_zero (algebraMap ℤ (R q)) hlcU.ne_zero, hdegN]
  have hmapN : algebraMap (R q)[X] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) NR = Polynomial.aeval jA N := by
    rw [halgXA, hNR, Polynomial.aeval_map_algebraMap]
  have hmemI : algebraMap (R q)[X] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) NR ∈
      Ideal.span {Polynomial.aeval v g} := by
    rw [hmapN, hNA]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  refine ⟨Module.Finite.quotient_of_isUnit_leadingCoeff_of_mem (R q) ↥(IgusaScheme.chartAlgFin (N₀ * q) q) NR hlc' _ hmemI,
    ?_⟩
  calc Module.finrank (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v g})
        ≤ m * NR.natDegree :=
          finrank_quotient_le_mul_natDegree (R q) ↥(IgusaScheme.chartAlgFin (N₀ * q) q) m f hf NR hlc' _ hmemI
    _ = m * (q - 1) * g.natDegree := by rw [hdegNR]; ring

end S_ModularCurve_DRModelPackageLevel_exists_forall_finite_quotient_span_aeval_and_finrank_le
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_finite_quotient_span_aeval_and_finrank_le (solution)
