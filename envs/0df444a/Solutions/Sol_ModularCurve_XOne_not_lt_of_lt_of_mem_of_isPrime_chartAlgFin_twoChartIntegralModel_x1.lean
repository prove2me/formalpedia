-- Prove2me | solution 1 for ModularCurve.XOne.not_lt_of_lt_of_mem_of_isPrime_chartAlgFin_twoChartIntegralModel_x1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9dc9541b-145b-5768-87c6-91d524e84c08

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOne_not_lt_of_lt_of_mem_of_isPrime_chartAlgFin_twoChartIntegralModel_x1
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false

open AlgebraicCurve.TwoChartIntegralModel

namespace LevelFiniteFlat
namespace Leaf

theorem CruxC.false_of_chain {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.IsIntegral R S] (hR : ringKrullDim R ≤ ((2 : ℕ) : ℕ∞))
    {𝔮 𝔭' m : Ideal S} [𝔮.IsPrime] [𝔭'.IsPrime] [m.IsPrime]
    (h0 : 𝔮 ≠ ⊥) (h1 : 𝔮 < 𝔭') (h2 : 𝔭' < m) : False := by
  have hb : (⊥ : Ideal S) < 𝔮 := bot_lt_iff_ne_bot.mpr h0
  have c01 := Ideal.IsIntegral.comap_lt_comap (R := R) hb
  have c12 := Ideal.IsIntegral.comap_lt_comap (R := R) h1
  have c23 := Ideal.IsIntegral.comap_lt_comap (R := R) h2
  have e01 := Ideal.height_add_one_le_of_lt_of_isPrime c01
  have e12 := Ideal.height_add_one_le_of_lt_of_isPrime c12
  have e23 := Ideal.height_add_one_le_of_lt_of_isPrime c23
  have h3 : ((3 : ℕ) : ℕ∞) ≤ (m.comap (algebraMap R S)).height :=
    calc ((3 : ℕ) : ℕ∞) = 0 + 1 + 1 + 1 := by norm_num
      _ ≤ (Ideal.comap (algebraMap R S) ⊥).height + 1 + 1 + 1 := by gcongr; simp
      _ ≤ (Ideal.comap (algebraMap R S) 𝔮).height + 1 + 1 := by gcongr
      _ ≤ (Ideal.comap (algebraMap R S) 𝔭').height + 1 := by gcongr
      _ ≤ (Ideal.comap (algebraMap R S) m).height := e23
  have h4 : (((3 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ) : ℕ∞) :=
    (WithBot.coe_le_coe.mpr h3).trans (Ideal.height_le_ringKrullDim_of_isPrime.trans hR)
  have h5 : ((3 : ℕ) : ℕ∞) ≤ ((2 : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp h4
  have h6 : (3 : ℕ) ≤ 2 := by exact_mod_cast h5
  omega

theorem CruxC.ringKrullDim_polynomial_le (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    ringKrullDim (Polynomial A) ≤ ((2 : ℕ) : ℕ∞) := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
  exact le_of_eq (by norm_cast)

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
    (j_M : ↥K_M) (hj_M : ((j_M : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_M ≠ 0)] :
    ∀ 𝔮 𝔭' m : Ideal ↥(chartAlgFin A (↥K_M) j_M), 𝔮.IsPrime → 𝔭'.IsPrime → m.IsPrime →
      algebraMap A _ ϖ ∈ 𝔮 → 𝔮 < 𝔭' → ¬ 𝔭' < m := by
  classical
  intro 𝔮 𝔭' m h𝔮 h𝔭' hm hϖ𝔮 h1 h2

  have htj : Transcendental A j_M := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K_M A j_M hj_M
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j_M} : Set ↥K_M)) ↥K_M :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 M) (by simp [ModularGroup.T]) L K_M hK_M j_M hj_M
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j_M} : Set ↥K_M)) ↥K_M :=
    Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j_M} : Set ↥K_M)) ↥K_M := inferInstance
  have hfin := (finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K_M) j_M htj hFD hsep).1
  letI algP : Algebra (Polynomial A) ↥(chartAlgFin A (↥K_M) j_M) :=
    (polynomialToChartFin A (↥K_M) j_M).toRingHom.toAlgebra
  haveI : Module.Finite (Polynomial A) ↥(chartAlgFin A (↥K_M) j_M) := hfin
  haveI : Algebra.IsIntegral (Polynomial A) ↥(chartAlgFin A (↥K_M) j_M) := Algebra.IsIntegral.of_finite _ _

  have hϖ0 : (algebraMap A ↥(chartAlgFin A (↥K_M) j_M) ϖ) ≠ 0 := by
    intro h
    have h' : algebraMap A ↥K_M ϖ = 0 := by
      have := congrArg (fun x : ↥(chartAlgFin A (↥K_M) j_M) => (x : ↥K_M)) h
      simpa using this
    rw [IsScalarTower.algebraMap_apply A L ↥K_M, map_eq_zero] at h'
    exact hϖ.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective A L)).mp h')
  have h0 : 𝔮 ≠ ⊥ := fun h => hϖ0 (by rw [h] at hϖ𝔮; exact (Ideal.mem_bot).mp hϖ𝔮)
  exact CruxC.false_of_chain (R := Polynomial A) (CruxC.ringKrullDim_polynomial_le A) h0 h1 h2

end S_ModularCurve_XOne_not_lt_of_lt_of_mem_of_isPrime_chartAlgFin_twoChartIntegralModel_x1
end P2MW
export P2MW.S_ModularCurve_XOne_not_lt_of_lt_of_mem_of_isPrime_chartAlgFin_twoChartIntegralModel_x1 (solution)
