-- Prove2me | solution 1 for ModularCurve.XOne.isPrincipalIdealRing_localization_atPrime_chartAlgFin_of_not_mem_twoChartIntegralModel_x1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a5af31b7-9215-5829-8f6c-2310dddd5c2f

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgFin
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOne_isPrincipalIdealRing_localization_atPrime_chartAlgFin_of_not_mem_twoChartIntegralModel_x1
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false

open AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct

namespace LevelFiniteFlat
namespace Leaf

theorem CruxB.isPrincipalIdealRing_of_isRegularLocalRing_of_ringKrullDim_eq_one
    (Sm : Type*) [CommRing Sm] [IsDomain Sm]
    (hreg : IsRegularLocalRing Sm) (hdim : ringKrullDim Sm = (1 : ℕ∞)) : IsPrincipalIdealRing Sm := by
  haveI := hreg
  have h := (IsRegularLocalRing.iff_finrank_cotangentSpace Sm).mp hreg
  rw [hdim] at h
  have hfin : Module.finrank (IsLocalRing.ResidueField Sm) (IsLocalRing.CotangentSpace Sm) = 1 := by
    exact_mod_cast h
  haveI : IsDiscreteValuationRing Sm := IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hfin
  infer_instance

theorem CruxB.core {A : Type*} [CommRing A] [IsDomain A] (L : Type*) [Field L] [Algebra A L] [IsFractionRing A L]
    {S : Type*} [CommRing S] [IsDomain S] [Algebra A S]
    (𝔪 : Ideal S) [h𝔪 : 𝔪.IsMaximal]
    (h𝔪A : ∀ a : A, algebraMap A S a ∈ 𝔪 → a = 0)
    (hreg : ∀ (m : Ideal (L ⊗[A] S)) [m.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = (1 : ℕ∞)) :
    IsPrincipalIdealRing (Localization.AtPrime 𝔪) := by
  classical
  letI : Algebra S (L ⊗[A] S) := Algebra.TensorProduct.rightAlgebra

  let N : Submonoid S := Algebra.algebraMapSubmonoid S (nonZeroDivisors A)
  haveI : IsLocalization N (L ⊗[A] S) := IsLocalization.tensorRight (R := A) (S := S) L (nonZeroDivisors A)

  have hdisj : Disjoint (N : Set S) (𝔪 : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    exact nonZeroDivisors.ne_zero ha (h𝔪A a hmem)

  let m' : Ideal (L ⊗[A] S) := 𝔪.map (algebraMap S (L ⊗[A] S))
  haveI hm'p : m'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint N _ 𝔪 h𝔪.isPrime hdisj
  have hcomap : m'.comap (algebraMap S (L ⊗[A] S)) = 𝔪 :=
    IsLocalization.under_map_of_isPrime_disjoint N (L ⊗[A] S) h𝔪.isPrime hdisj
  obtain ⟨q, hq, hmq⟩ := Ideal.exists_le_maximal m' hm'p.ne_top
  have hqc : q.comap (algebraMap S (L ⊗[A] S)) = 𝔪 := by
    refine (Ideal.IsMaximal.eq_of_le h𝔪 ?_ ?_).symm
    · exact Ideal.comap_ne_top _ hq.ne_top
    · rw [← hcomap]; exact Ideal.comap_mono hmq
  have hqm : q = m' := by
    rw [← IsLocalization.map_under N (L ⊗[A] S) q]
    show Ideal.map (algebraMap S (L ⊗[A] S)) (q.comap (algebraMap S (L ⊗[A] S))) = m'
    rw [hqc]
  haveI hm'max : m'.IsMaximal := hqm ▸ hq
  obtain ⟨hregm, hdimm⟩ := hreg m'

  have hloc : IsLocalization.AtPrime (Localization.AtPrime m') (m'.comap (algebraMap S (L ⊗[A] S))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization N (Localization.AtPrime m') m'
  have hpc : 𝔪.primeCompl = (m'.comap (algebraMap S (L ⊗[A] S))).primeCompl := by
    ext x
    change x ∉ 𝔪 ↔ x ∉ m'.comap (algebraMap S (L ⊗[A] S))
    rw [hcomap]
  haveI : IsLocalization 𝔪.primeCompl (Localization.AtPrime m') := by rw [hpc]; exact hloc
  let e : Localization.AtPrime 𝔪 ≃ₐ[S] Localization.AtPrime m' :=
    IsLocalization.algEquiv 𝔪.primeCompl (Localization.AtPrime 𝔪) (Localization.AtPrime m')
  have hreg' : IsRegularLocalRing (Localization.AtPrime 𝔪) := by
    haveI := hregm
    exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime m') e.symm.toRingEquiv
  have hdim' : ringKrullDim (Localization.AtPrime 𝔪) = (1 : ℕ∞) := by
    rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]; exact hdimm
  exact CruxB.isPrincipalIdealRing_of_isRegularLocalRing_of_ringKrullDim_eq_one _ hreg' hdim'

end Leaf
end LevelFiniteFlat

open LevelFiniteFlat.Leaf

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (ϖ : A) (hϖ : Irreducible ϖ)
    (K_M : IntermediateField L (LaurentSeries L))
    (hK_M : K_M = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    [Algebra A ↥K_M] [IsScalarTower A L ↥K_M]
    (j_M : ↥K_M) (hj_M : ((j_M : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_M ≠ 0)]
    (𝔪 : Ideal ↥(chartAlgFin A (↥K_M) j_M)) [𝔪.IsMaximal] (hϖ𝔪 : algebraMap A _ ϖ ∉ 𝔪) :
    IsPrincipalIdealRing (Localization.AtPrime 𝔪) := by
  classical

  have htj : Transcendental A j_M := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K_M A j_M hj_M
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j_M} : Set ↥K_M)) ↥K_M :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 M) (by simp [ModularGroup.T]) L K_M hK_M j_M hj_M
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j_M} : Set ↥K_M)) ↥K_M :=
    Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j_M} : Set ↥K_M)) ↥K_M := inferInstance
  have hreg : ∀ (m : Ideal (L ⊗[A] ↥(chartAlgFin A (↥K_M) j_M))) [m.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = (1 : ℕ∞) :=
    fun m _ => isRegularLocalRing_localization_fractionRing_tensor_chartAlgFin A L (↥K_M) j_M htj hFD hsep m

  have h𝔪A : ∀ a : A, algebraMap A ↥(chartAlgFin A (↥K_M) j_M) a ∈ 𝔪 → a = 0 := by
    intro a ha
    by_contra ha0
    set P : Ideal A := 𝔪.comap (algebraMap A ↥(chartAlgFin A (↥K_M) j_M)) with hP
    haveI : P.IsPrime := Ideal.IsPrime.comap _
    have hPne : P ≠ ⊥ := fun h => ha0 (by
      have : a ∈ P := ha
      rw [h] at this
      exact (Ideal.mem_bot).mp this)
    have hPmax : P.IsMaximal := IsPrime.to_maximal_ideal hPne
    have hPeq : P = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hPmax
    have hϖP : ϖ ∈ P := by
      rw [hPeq, hϖ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self ϖ
    exact hϖ𝔪 hϖP
  exact CruxB.core L 𝔪 h𝔪A hreg

end S_ModularCurve_XOne_isPrincipalIdealRing_localization_atPrime_chartAlgFin_of_not_mem_twoChartIntegralModel_x1
end P2MW
export P2MW.S_ModularCurve_XOne_isPrincipalIdealRing_localization_atPrime_chartAlgFin_of_not_mem_twoChartIntegralModel_x1 (solution)
