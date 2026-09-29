-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.tateFourier_tateFourier_indicator_setOf_valued_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d731f63a-2720-5a11-b1c8-38692b48bf9e

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
import Theorems.Thm_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_tateFourier_tateFourier_indicator_setOf_valued_sub_le
p2m_attr_erase "instance" "NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField

open LanglandsTunnell.TateLocal in

theorem solution (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (a : v.adicCompletion K) (m : ℤ) (x : v.adicCompletion K) :
    tateFourier ψ μ (tateFourier ψ μ
        ({x' : v.adicCompletion K | Valued.v (x' - a) ≤ WithZero.exp (-m)}.indicator fun _ => (1 : ℂ))) x
      = (((Ideal.absNorm v.asIdeal : ℝ) ^ n
            * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ^ 2 : ℝ) : ℂ)
          * {x' : v.adicCompletion K | Valued.v (x' + a) ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x := by

  have h1 : tateFourier ψ μ
        ({x' : v.adicCompletion K | Valued.v (x' - a) ≤ WithZero.exp (-m)}.indicator fun _ => (1 : ℂ))
      = fun y => ψ (a * y) * ((μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)} : ℝ) : ℂ)
          * {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + m)}.indicator (fun _ => (1 : ℂ)) y :=
    funext fun y => tateFourier_indicator_setOf_valued_sub_le K v μ ψ n hψn hψn' a m y
  rw [h1]

  set c : ℂ := ((μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)} : ℝ) : ℂ) with hc
  set D : Set (v.adicCompletion K) := {y' | Valued.v y' ≤ WithZero.exp (n + m)} with hD
  have hker : ∀ y : v.adicCompletion K, ψ (a * y) * c * D.indicator (fun _ => (1 : ℂ)) y * ψ (y * x)
      = c * (D.indicator (fun _ => (1 : ℂ)) y * ψ (y * (a + x))) := by
    intro y
    have : ψ (a * y) * ψ (y * x) = ψ (y * (a + x)) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [← this]; ring
  have houter : tateFourier ψ μ (fun y => ψ (a * y) * c * D.indicator (fun _ => (1 : ℂ)) y) x
      = c * tateFourier ψ μ (D.indicator fun _ => (1 : ℂ)) (a + x) := by
    unfold tateFourier
    simp_rw [hker]
    rw [integral_const_mul]
  have hD0 : D = {x' : v.adicCompletion K | Valued.v (x' - 0) ≤ WithZero.exp (-(-(n + m)))} := by
    ext y
    rw [hD, Set.mem_setOf_eq, Set.mem_setOf_eq, sub_zero, neg_neg]
  rw [houter, hD0, tateFourier_indicator_setOf_valued_sub_le K v μ ψ n hψn hψn' 0 (-(n + m)) (a + x), zero_mul,
    AddChar.map_zero_eq_one, one_mul]

  have hset : {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + -(n + m))}
      = {x' : v.adicCompletion K | Valued.v x' ≤ WithZero.exp (-m)} := by
    rw [show n + -(n + m) = -m by ring]
  have hmem : ((a + x) ∈ {x' : v.adicCompletion K | Valued.v x' ≤ WithZero.exp (-m)})
      ↔ x ∈ {x' : v.adicCompletion K | Valued.v (x' + a) ≤ WithZero.exp (-m)} := by
    simp only [Set.mem_setOf_eq, add_comm]
  rw [hset, neg_neg]
  have hN : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hconst : μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)}
      * μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (n + m)}
      = (Ideal.absNorm v.asIdeal : ℝ) ^ n * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ^ 2 := by
    rw [measureReal_setOf_valued_le_exp K v μ (-m), measureReal_setOf_valued_le_exp K v μ (n + m)]
    have : (Ideal.absNorm v.asIdeal : ℝ) ^ (-m) * (Ideal.absNorm v.asIdeal : ℝ) ^ (n + m)
        = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
      rw [← zpow_add₀ hN]; congr 1; ring
    calc (Ideal.absNorm v.asIdeal : ℝ) ^ (-m) * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K))
          * ((Ideal.absNorm v.asIdeal : ℝ) ^ (n + m) * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
        = ((Ideal.absNorm v.asIdeal : ℝ) ^ (-m) * (Ideal.absNorm v.asIdeal : ℝ) ^ (n + m))
            * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ^ 2 := by ring
      _ = _ := by rw [this]
  by_cases hx : x ∈ {x' : v.adicCompletion K | Valued.v (x' + a) ≤ WithZero.exp (-m)}
  · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx, mul_one, mul_one, hc, ← Complex.ofReal_mul,
      hconst]
  · rw [Set.indicator_of_notMem (fun h => hx (hmem.mp h)), Set.indicator_of_notMem hx, mul_zero, mul_zero, mul_zero]

end S_LanglandsTunnell_TateLocal_tateFourier_tateFourier_indicator_setOf_valued_sub_le
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_tateFourier_tateFourier_indicator_setOf_valued_sub_le (solution)
