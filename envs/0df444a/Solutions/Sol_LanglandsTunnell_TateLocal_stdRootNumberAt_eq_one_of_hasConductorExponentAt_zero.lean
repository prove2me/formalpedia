-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/7cdc096d-3b9b-5257-92cf-ce27c15fe337

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_of_unramified
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.StandardAddChar IsDedekindDomain NumberField.AdelicTrace NumberField.AdelicBox

open IsDedekindDomain.HeightOneSpectrum
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localZeta_stdTestFunAt_eq_of_unramified"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdTestFunAt stdRootNumberAt stdRootNumberAt_def HasConductorExponentAt hasConductorExponentAt_zero_iff localLFactorAt localLFactorAt_of_hasConductorExponentAt_zero localEpsilonAt localEpsilonAt_def tateFourier localZeta localGammaAt localZeta_stdTestFunAt_eq_of_unramified"
namespace Unram0
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

attribute [local instance] localBorel borelSpace_localBorel

private theorem absNorm_ne_zero' : Ideal.absNorm v.asIdeal ≠ 0 :=
  Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot

private theorem one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have h0 := absNorm_ne_zero' K v
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private def unitSphere : Set (v.adicCompletion K) := {x | Valued.v x = 1}

private theorem mem_unitSphere {x : v.adicCompletion K} :
    x ∈ unitSphere K v ↔ Valued.v x = 1 := Iff.rfl

private theorem isClopen_sphere_valued {y : v.adicCompletion K} (hy : y ≠ 0) :
    IsClopen {x : v.adicCompletion K | Valued.v x = Valued.v y} := by
  have hr : Valued.v.restrict y ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff]
    exact (Valuation.ne_zero_iff _).mpr hy
  have hset : {x : v.adicCompletion K | Valued.v x = Valued.v y}
      = {x | Valued.v.restrict x = Valued.v.restrict y} := by
    ext x
    simp only [Set.mem_setOf_eq, le_antisymm_iff, Valuation.restrict_le_iff]
  rw [hset]
  exact Valued.isClopen_sphere _ hr

private theorem isOpen_unitSphere : IsOpen (unitSphere K v) := by
  have h := (isClopen_sphere_valued K v (one_ne_zero : (1 : v.adicCompletion K) ≠ 0)).isOpen
  rw [map_one] at h
  exact h

private theorem one_mem_unitSphere : (1 : v.adicCompletion K) ∈ unitSphere K v := by
  rw [mem_unitSphere, map_one]

private theorem unitSphere_subset_integers :
    unitSphere K v ⊆ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := fun x hx => by
  rw [SetLike.mem_coe, mem_adicCompletionIntegers]
  exact le_of_eq hx

private theorem psiLocal_eq_one_of_valued_le_one (x : v.adicCompletion K) (hx : Valued.v x ≤ 1) :
    psiLocal K v x = 1 := by
  rw [psiLocal_apply, show stdAddChar K = (adelicTraceData K).psiK from rfl,
    AdelicTraceData.psiK_apply, AdelicTraceData.adelicTrace_apply, psiQ_apply]
  change psiArch ((adelicTraceData K).traceInf 0)
      * psiFin (traceFinHom K (finAdeleSingleAt K v x)) = 1
  have hint : ∀ w : HeightOneSpectrum (𝓞 K),
      finAdeleSingleAt K v x w ∈ w.adicCompletionIntegers K := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [finAdeleSingleAt_apply_self]
      exact hx
    · rw [finAdeleSingleAt_apply_of_ne K v x hw]
      exact zero_mem _
  let z : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K := fun w => ⟨_, hint w⟩
  have hsm : RestrictedProduct.structureMap
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
        (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite z
      = finAdeleSingleAt K v x :=
    RestrictedProduct.ext _ _ fun w => rfl
  rw [← hsm, traceFinHom_structureMap, map_zero, AddChar.map_zero_eq_one, one_mul]
  exact psiFin_eq_one_of_forall_mem _ fun w => (traceInt K z w).2

private theorem exists_psiLocal_ne_one_of_level_zero (hlev : addCharLevel (psiLocal K v) = 0)
    (hψ : psiLocal K v ≠ 1) :
    ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ psiLocal K v x ≠ 1 := by
  set S : Set ℤ :=
    {n : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → psiLocal K v x = 1}
    with hS
  have hsup : sSup S = 0 := hlev
  have h0 : (0 : ℤ) ∈ S := fun x hx =>
    psiLocal_eq_one_of_valued_le_one K v x (by rwa [WithZero.exp_zero] at hx)
  obtain ⟨x₁, hx₁⟩ := DFunLike.ne_iff.mp hψ
  rw [AddChar.one_apply] at hx₁
  have hx₁0 : x₁ ≠ 0 := fun h => hx₁ (by rw [h, AddChar.map_zero_eq_one])
  have hv₁ : Valued.v x₁ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx₁0
  have hbdd : BddAbove S := by
    refine ⟨WithZero.log (Valued.v x₁), fun n hn => ?_⟩
    by_contra hlt
    apply hx₁
    apply hn
    rw [← WithZero.exp_log hv₁]
    exact WithZero.exp_le_exp.mpr (by omega)
  have h1 : (1 : ℤ) ∉ S := fun h1 => by
    have := le_csSup hbdd h1
    omega
  obtain ⟨x, hx⟩ := not_forall.mp h1
  exact ⟨x, (Classical.not_imp.mp hx).1, (Classical.not_imp.mp hx).2⟩

private theorem tateFourier_indicator_integers {ψ : AddChar (v.adicCompletion K) ℂ}
    (hψ0 : ∀ x : v.adicCompletion K, Valued.v x ≤ 1 → ψ x = 1)
    (hψ1 : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψ x ≠ 1) :
    tateFourier ψ (Measure.addHaarMeasure (integersPositiveCompacts K v))
        ((v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator fun _ => (1 : ℂ))
      = (v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator fun _ => (1 : ℂ) := by
  set μ : Measure (v.adicCompletion K) := Measure.addHaarMeasure (integersPositiveCompacts K v)
    with hμ
  set O : Set (v.adicCompletion K) := (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    with hO
  have hOmeas : MeasurableSet O := (Valued.isOpen_valuationSubring _).measurableSet
  have hμO : μ.real O = 1 := by
    rw [measureReal_def, hμ, hO, ← coe_integersPositiveCompacts K v, Measure.addHaarMeasure_self,
      ENNReal.toReal_one]
  funext y
  unfold tateFourier
  have hind : ∀ x, O.indicator (fun _ => (1 : ℂ)) x * ψ (x * y)
      = O.indicator (fun x => ψ (x * y)) x := by
    intro x
    by_cases hx : x ∈ O
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  simp_rw [hind]
  by_cases hy : y ∈ O
  · rw [Set.indicator_of_mem hy, integral_indicator hOmeas]
    have hone : Set.EqOn (fun x => ψ (x * y)) (fun _ => (1 : ℂ)) O := fun x hx => by
      show ψ (x * y) = 1
      apply hψ0
      rw [map_mul]
      rw [hO, SetLike.mem_coe, mem_adicCompletionIntegers] at hx hy
      exact mul_le_one' hx hy
    rw [setIntegral_congr_fun hOmeas hone, setIntegral_const, hμO, one_smul]
  · rw [Set.indicator_of_notMem hy]
    obtain ⟨x₀, hx₀, hne⟩ := hψ1
    have hy0 : y ≠ 0 := fun h => hy (by rw [h, hO, SetLike.mem_coe]; exact zero_mem _)
    have hvy0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
    have hvy : WithZero.exp (1 : ℤ) ≤ Valued.v y := by
      have hlt : 1 < Valued.v y := by
        rw [hO, SetLike.mem_coe, mem_adicCompletionIntegers, not_le] at hy
        exact hy
      rw [← WithZero.exp_log hvy0] at hlt ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      exact WithZero.exp_le_exp.mpr (by omega)
    set t : v.adicCompletion K := x₀ * y⁻¹ with ht
    have htO : t ∈ O := by
      rw [hO, SetLike.mem_coe, mem_adicCompletionIntegers, ht, map_mul, map_inv₀]
      rw [mul_inv_le_iff₀ (zero_lt_iff.mpr hvy0), one_mul]
      exact hx₀.trans hvy
    have hty : t * y = x₀ := by rw [ht, inv_mul_cancel_right₀ hy0]
    have hpt : ∀ x, O.indicator (fun x => ψ (x * y)) (t + x)
        = ψ x₀ * O.indicator (fun x => ψ (x * y)) x := by
      intro x
      by_cases hx : x ∈ O
      · have htx : t + x ∈ O := by
          rw [hO, SetLike.mem_coe] at htO hx ⊢
          exact add_mem htO hx
        rw [Set.indicator_of_mem htx, Set.indicator_of_mem hx, add_mul, AddChar.map_add_eq_mul,
          hty]
      · have htx : t + x ∉ O := fun h => hx <| by
          rw [hO, SetLike.mem_coe] at htO h ⊢
          have := sub_mem h htO
          rwa [add_sub_cancel_left] at this
        rw [Set.indicator_of_notMem htx, Set.indicator_of_notMem hx, mul_zero]
    have htrans : ∫ x, O.indicator (fun x => ψ (x * y)) x ∂μ
        = ψ x₀ * ∫ x, O.indicator (fun x => ψ (x * y)) x ∂μ := by
      calc ∫ x, O.indicator (fun x => ψ (x * y)) x ∂μ
          = ∫ x, O.indicator (fun x => ψ (x * y)) (t + x) ∂μ :=
            (integral_add_left_eq_self _ t).symm
        _ = ∫ x, ψ x₀ * O.indicator (fun x => ψ (x * y)) x ∂μ := by simp_rw [hpt]
        _ = ψ x₀ * ∫ x, O.indicator (fun x => ψ (x * y)) x ∂μ := integral_const_mul _ _
    have h1ne : (1 : ℂ) - ψ x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hprod : ((1 : ℂ) - ψ x₀) * ∫ x, O.indicator (fun x => ψ (x * y)) x ∂μ = 0 := by
      rw [sub_mul, one_mul, ← htrans, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left h1ne

private theorem stdRootNumberAt_eq_one_of_zeta
    (hB : ∀ (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ), HasConductorExponentAt K v χ 0 →
      ‖(χ (uniformizerUnit K v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1 →
      localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ s
        = ((selfDualHaarAt K v).real {x | Valued.v x = 1} : ℂ) * localLFactorAt K v χ s)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : HasConductorExponentAt K v χ 0)
    (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) (hlev : addCharLevel (psiLocal K v) = 0)
    (hψ : psiLocal K v ≠ 1) : stdRootNumberAt K v χ = 1 := by
  set μ₀ : Measure (v.adicCompletion K) := Measure.addHaarMeasure (integersPositiveCompacts K v)
    with hμ₀
  set O : Set (v.adicCompletion K) := (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    with hO

  have hμ : selfDualHaarAt K v = μ₀ := by
    rw [show selfDualHaarAt K v = ((Ideal.absNorm v.asIdeal : ℝ≥0)
        ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2)) • μ₀ from rfl, hlev, Int.cast_zero,
      neg_zero, zero_div, NNReal.rpow_zero, one_smul]

  have hχ' : HasConductorExponentAt K v χ⁻¹ 0 := by
    rw [hasConductorExponentAt_zero_iff] at hχ ⊢
    intro u hu'
    rw [MonoidHom.inv_apply, hχ u hu', inv_one]
  have hu' : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ)‖ = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]

  have hf : stdTestFunAt K v χ = O.indicator fun _ => (1 : ℂ) := by
    unfold stdTestFunAt
    rw [if_pos hχ]
  have hf' : stdTestFunAt K v χ⁻¹ = O.indicator fun _ => (1 : ℂ) := by
    unfold stdTestFunAt
    rw [if_pos hχ']

  have hq1 : 1 < Ideal.absNorm v.asIdeal := one_lt_absNorm K v
  have hq : 0 < Ideal.absNorm v.asIdeal := by omega
  have hqR : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hq1
  have hre1 : (-(1 / 2 : ℂ).re) = -(1 / 2 : ℝ) := by norm_num
  have hre2 : (-(1 - 1 / 2 : ℂ).re) = -(1 / 2 : ℝ) := by norm_num
  have hhalf : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hqR (by norm_num)
  have hs1 : ‖(χ (uniformizerUnit K v) : ℂ)‖
      * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℂ).re) < 1 := by
    rw [hu, one_mul, hre1]
    exact hhalf
  have hs2 : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ)‖
      * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 - 1 / 2 : ℂ).re) < 1 := by
    rw [hu', one_mul, hre2]
    exact hhalf

  have hne1 : (1 : ℂ) - (χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ)
      ^ (-(1 / 2 : ℂ)) ≠ 0 := by
    refine sub_ne_zero.mpr fun h => ?_
    have hn : ‖(χ (uniformizerUnit K v) : ℂ)
        * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ))‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re]
      exact hs1
    rw [← h, norm_one] at hn
    exact lt_irrefl _ hn
  have hne2 : (1 : ℂ) - (χ⁻¹ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ)
      ^ (-(1 - 1 / 2 : ℂ)) ≠ 0 := by
    refine sub_ne_zero.mpr fun h => ?_
    have hn : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ)
        * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - 1 / 2 : ℂ))‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re]
      exact hs2
    rw [← h, norm_one] at hn
    exact lt_irrefl _ hn

  have hμ₀O : μ₀ O = 1 := by
    rw [hμ₀, hO, ← coe_integersPositiveCompacts K v, Measure.addHaarMeasure_self]
  have hfin : μ₀ (unitSphere K v) ≠ ⊤ := by
    refine (lt_of_le_of_lt (measure_mono (unitSphere_subset_integers K v)) ?_).ne
    rw [hμ₀O]
    exact ENNReal.one_lt_top
  have hpos : μ₀ (unitSphere K v) ≠ 0 :=
    (isOpen_unitSphere K v).measure_ne_zero μ₀ ⟨1, one_mem_unitSphere K v⟩
  have hU : ((μ₀.real {x : v.adicCompletion K | Valued.v x = 1} : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff, not_or]
    exact ⟨hpos, hfin⟩

  have hZ1 := hB χ (1 / 2) hχ hs1
  have hZ2 := hB χ⁻¹ (1 - 1 / 2) hχ' hs2
  rw [hf, hμ] at hZ1
  rw [hf', hμ] at hZ2
  have hF : tateFourier (psiLocal K v) μ₀ (O.indicator fun _ => (1 : ℂ))
      = O.indicator fun _ => (1 : ℂ) :=
    tateFourier_indicator_integers K v (psiLocal_eq_one_of_valued_le_one K v)
      (exists_psiLocal_ne_one_of_level_zero K v hlev hψ)

  rw [stdRootNumberAt_def]
  show localEpsilonAt K v (selfDualHaarAt K v) (psiLocal K v) (stdTestFunAt K v χ) χ (1 / 2) = 1
  rw [localEpsilonAt_def, localGammaAt, hμ, hf, hF, hZ1, hZ2,
    localLFactorAt_of_hasConductorExponentAt_zero K v hχ,
    localLFactorAt_of_hasConductorExponentAt_zero K v hχ', mul_div_mul_left _ _ hU,
    div_mul_cancel₀ _ (inv_ne_zero hne1), div_self (inv_ne_zero hne2)]

end LanglandsTunnell.TateLocal.Unram0

end

p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero.LanglandsTunnell.TateLocal NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain"

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : HasConductorExponentAt K v χ 0)
    (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) (hlev : addCharLevel (psiLocal K v) = 0)
    (hψ : psiLocal K v ≠ 1) :
    stdRootNumberAt K v χ = 1 :=
  LanglandsTunnell.TateLocal.Unram0.stdRootNumberAt_eq_one_of_zeta K v
    (LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_eq_of_unramified K v) χ hχ hu hlev hψ

#print axioms solution

end S_LanglandsTunnell_TateLocal_stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero (solution)
