-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.localZeta_tateFourier_indicator_setOf_valued_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e27076fb-0ef4-56f4-aca5-d8b5c2c3f018

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_localZeta_tateFourier_indicator_setOf_valued_sub_one_le
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.tateFourier_indicator_setOf_valued_sub_le TateLocal.measureReal_setOf_valued_le_exp"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt modulus modulus_coe_units modulus_ne_zero modulus_mul tateFourier charExt charExt_of_ne_zero mulMeasure localZeta tateFourier_indicator_setOf_valued_sub_le modulus_adicCompletion_eq_nnnorm measureReal_setOf_valued_le_exp"
namespace RamifiedKv
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

section Generic

private theorem preimage_mul_left_eq_smul {F : Type*} [Field F] (u : Fˣ) (s : Set F) :
    (fun x => (u : F) * x) ⁻¹' s = u⁻¹ • s := by
  ext x
  rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]

private theorem charExt_units_mul {F : Type*} [Field F] (χ : Fˣ →* ℂˣ) (u : Fˣ) (y : F) :
    charExt χ ((u : F) * y) = (χ u : ℂ) * charExt χ y := by
  by_cases hy : y = 0
  · simp [hy]
  · have hne : (u : F) * y ≠ 0 := mul_ne_zero u.ne_zero hy
    rw [charExt_of_ne_zero χ hne, charExt_of_ne_zero χ hy, ← Units.val_mul, ← map_mul]
    congr 2
    ext
    simp

private theorem modulus_units_mul_cpow {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace F] (u : Fˣ) (y : F) (w : ℂ) :
    ((modulus ((u : F) * y) : ℝ) : ℂ) ^ w =
      ((modulus (u : F) : ℝ) : ℂ) ^ w * ((modulus y : ℝ) : ℂ) ^ w := by
  rw [modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]

private theorem mulMeasure_apply {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace F] [MeasurableSpace F] (μ : Measure F) {s : Set F} (hs : MeasurableSet s) :
    mulMeasure μ s = ∫⁻ x in s ∩ {0}ᶜ, ((modulus x : ℝ≥0∞))⁻¹ ∂μ := by
  rw [mulMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]

private theorem integral_mulMeasure {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace F] [MeasurableSpace F] [MeasurableSingletonClass F] (μ : Measure F) (Φ : F → ℂ)
    (hm : AEMeasurable (fun x : F => (modulus x)⁻¹) (μ.restrict {0}ᶜ)) :
    ∫ x, Φ x ∂(mulMeasure μ) = ∫ x in ({0}ᶜ : Set F), ((modulus x)⁻¹ : ℝ≥0) • Φ x ∂μ := by
  have hae : (fun x : F => ((modulus x : ℝ≥0∞))⁻¹)
      =ᵐ[μ.restrict {0}ᶜ] fun x : F => (((modulus x)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    refine (MeasureTheory.ae_restrict_iff' (MeasurableSet.singleton (0 : F)).compl).mpr ?_
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : x ≠ 0 := by simpa using hx
    show ((modulus x : ℝ≥0∞))⁻¹ = (((modulus x)⁻¹ : ℝ≥0) : ℝ≥0∞)
    rw [ENNReal.coe_inv (modulus_ne_zero hx0)]
  rw [mulMeasure, MeasureTheory.withDensity_congr_ae hae,
    integral_withDensity_eq_integral_smul₀ hm]

private theorem ofReal_zpow_neg_cpow (q : ℕ) (w : ℂ) (j : ℕ) :
    ((((q : ℝ) ^ (-(j : ℤ)) : ℝ) : ℂ)) ^ w = ((q : ℂ) ^ (-w)) ^ j := by
  rw [Complex.ofReal_zpow, Complex.ofReal_natCast]
  have harg : ((q : ℂ)).arg = 0 := Complex.natCast_arg
  have h1 : -Real.pi < ((-(j : ℤ) : ℤ) : ℝ) * (q : ℂ).arg := by
    rw [harg, mul_zero]; exact neg_lt_zero.mpr Real.pi_pos
  have h2 : ((-(j : ℤ) : ℤ) : ℝ) * (q : ℂ).arg ≤ Real.pi := by
    rw [harg, mul_zero]; exact Real.pi_pos.le
  have := Complex.cpow_int_mul' (x := (q : ℂ)) (n := -(j : ℤ)) h1 h2 w
  rw [← this, show (((-(j : ℤ) : ℤ)) : ℂ) * w = (j : ℕ) * (-w) by push_cast; ring,
    Complex.cpow_nat_mul]

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]
  [MeasurableSpace F] [BorelSpace F]

private theorem map_mul_left_eq_smul (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] (u : Fˣ) :
    Measure.map (fun x => (u : F) * x) μ = ((modulus (u : F) : ℝ≥0∞)⁻¹) • μ := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul _) hs, preimage_mul_left_eq_smul,
    Measure.smul_apply, smul_eq_mul, ← distribHaarChar_mul μ u⁻¹ s, map_inv, modulus_coe_units,
    ENNReal.coe_inv distribHaarChar_pos.ne']

private theorem map_mul_left_of_modulus_eq_one (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] {u : Fˣ}
    (hu : modulus (u : F) = 1) : Measure.map (fun x => (u : F) * x) μ = μ := by
  rw [map_mul_left_eq_smul μ u, hu, ENNReal.coe_one, inv_one, one_smul]

private theorem setLIntegral_comp_mul_left (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] (u : Fˣ)
    (Φ : F → ℝ≥0∞) (T : Set F) :
    ∫⁻ x in (fun x => (u : F) * x) ⁻¹' T, Φ ((u : F) * x) ∂μ =
      (modulus (u : F) : ℝ≥0∞)⁻¹ * ∫⁻ y in T, Φ y ∂μ := by
  set e : F ≃ᵐ F := MeasurableEquiv.mulLeft₀ (u : F) u.ne_zero
  have hecoe : (⇑e : F → F) = fun x => (u : F) * x := rfl
  calc ∫⁻ x in (fun x => (u : F) * x) ⁻¹' T, Φ ((u : F) * x) ∂μ
      = ∫⁻ x, Φ (e x) ∂(μ.restrict (e ⁻¹' T)) := by rw [hecoe]
    _ = ∫⁻ y, Φ y ∂((Measure.map e μ).restrict T) := by
        rw [MeasurableEquiv.restrict_map, lintegral_map_equiv]
    _ = ∫⁻ y, Φ y ∂((((modulus (u : F) : ℝ≥0∞)⁻¹) • μ).restrict T) := by
        rw [hecoe, map_mul_left_eq_smul]
    _ = (modulus (u : F) : ℝ≥0∞)⁻¹ * ∫⁻ y in T, Φ y ∂μ := by
        rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

private theorem mulMeasure_map_mul_left [MeasurableSingletonClass F] (μ : Measure F) [μ.IsAddHaarMeasure]
    [μ.Regular] (u : Fˣ) :
    Measure.map (fun x => (u : F) * x) (mulMeasure μ) = mulMeasure μ := by
  ext s hs
  have hmeas : Measurable fun x => (u : F) * x := measurable_const_mul _
  rw [Measure.map_apply hmeas hs, mulMeasure_apply μ (hmeas hs), mulMeasure_apply μ hs]
  have hpre : (fun x => (u : F) * x) ⁻¹' s ∩ {0}ᶜ = (fun x => (u : F) * x) ⁻¹' (s ∩ {0}ᶜ) := by
    ext x
    simp [Units.ne_zero]
  rw [hpre]
  have hu0 : (modulus (u : F) : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero)
  have hutop : (modulus (u : F) : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hcongr : ∀ x ∈ (fun x => (u : F) * x) ⁻¹' (s ∩ {0}ᶜ),
      ((modulus x : ℝ≥0∞))⁻¹ = (modulus (u : F) : ℝ≥0∞) * ((modulus ((u : F) * x) : ℝ≥0∞))⁻¹ := by
    intro x hx
    have hx0 : x ≠ 0 := by
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
        mul_eq_zero, Units.ne_zero, false_or] at hx
      exact hx.2
    rw [modulus_mul, ENNReal.coe_mul, ENNReal.mul_inv (Or.inl hu0) (Or.inl hutop),
      ENNReal.mul_inv_cancel_left hu0 hutop]
  rw [setLIntegral_congr_fun (hmeas (hs.inter (measurableSet_singleton 0).compl)) hcongr,
    lintegral_const_mul' _ _ hutop,
    setLIntegral_comp_mul_left μ u (fun y => ((modulus y : ℝ≥0∞))⁻¹) (s ∩ {0}ᶜ),
    ENNReal.mul_inv_cancel_left hu0 hutop]

private theorem integral_comp_mul_left_mulMeasure [MeasurableSingletonClass F] (μ : Measure F)
    [μ.IsAddHaarMeasure] [μ.Regular] (u : Fˣ) (Φ : F → ℂ) :
    ∫ x, Φ ((u : F) * x) ∂(mulMeasure μ) = ∫ x, Φ x ∂(mulMeasure μ) := by
  have h := (measurableEmbedding_mulLeft₀ (u.ne_zero : (u : F) ≠ 0)).integral_map
    (μ := mulMeasure μ) Φ
  rw [mulMeasure_map_mul_left] at h
  exact h.symm

private theorem localZeta_comp_units_mul [MeasurableSingletonClass F] (μ : Measure F) [μ.IsAddHaarMeasure]
    [μ.Regular] (Φ : F → ℂ) (χ : Fˣ →* ℂˣ) (w : ℂ) (u : Fˣ) :
    localZeta μ (fun y => Φ ((u : F) * y)) χ w =
      (χ u⁻¹ : ℂ) * ((modulus ((u⁻¹ : Fˣ) : F) : ℝ) : ℂ) ^ w * localZeta μ Φ χ w := by
  set G : F → ℂ := fun z => Φ z * charExt χ (((u⁻¹ : Fˣ) : F) * z) *
    ((modulus (((u⁻¹ : Fˣ) : F) * z) : ℝ) : ℂ) ^ w with hG
  have hGu : ∀ y, G ((u : F) * y) = Φ ((u : F) * y) * charExt χ y * ((modulus y : ℝ) : ℂ) ^ w := by
    intro y
    simp only [hG, ← mul_assoc, Units.inv_mul, one_mul]
  have h1 : localZeta μ (fun y => Φ ((u : F) * y)) χ w = ∫ y, G ((u : F) * y) ∂(mulMeasure μ) := by
    simp only [localZeta, hGu]
  rw [h1, integral_comp_mul_left_mulMeasure μ u G]
  simp only [hG, localZeta, charExt_units_mul, modulus_units_mul_cpow, ← integral_const_mul]
  congr 1
  funext z
  ring

private theorem setIntegral_mul_charExt_eq_zero (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] {S : Set F}
    (hSm : MeasurableSet S) (g : F → ℂ) (χ : Fˣ →* ℂˣ) {u₁ : Fˣ} (hu₁ : modulus (u₁ : F) = 1)
    (hχ : χ u₁ ≠ 1) (hS : ∀ y, (u₁ : F) * y ∈ S ↔ y ∈ S) (hg : ∀ y ∈ S, g ((u₁ : F) * y) = g y) :
    ∫ y in S, g y * charExt χ y ∂μ = 0 := by
  set Φ : F → ℂ := S.indicator fun y => g y * charExt χ y with hΦdef
  have hΦ : ∀ y, Φ ((u₁ : F) * y) = (χ u₁ : ℂ) * Φ y := by
    intro y
    by_cases hy : y ∈ S
    · rw [hΦdef, Set.indicator_of_mem ((hS y).mpr hy), Set.indicator_of_mem hy, hg y hy,
        charExt_units_mul]
      ring
    · rw [hΦdef, Set.indicator_of_notMem (fun h => hy ((hS y).mp h)), Set.indicator_of_notMem hy,
        mul_zero]
  have hI : ∫ y, Φ y ∂μ = (χ u₁ : ℂ) * ∫ y, Φ y ∂μ := by
    calc ∫ y, Φ y ∂μ = ∫ y, Φ y ∂(Measure.map (fun x => (u₁ : F) * x) μ) := by
          rw [map_mul_left_of_modulus_eq_one μ hu₁]
      _ = ∫ y, Φ ((u₁ : F) * y) ∂μ := by
          rw [← MeasurableEquiv.coe_mulLeft₀ u₁.ne_zero, integral_map_equiv]; rfl
      _ = ∫ y, (χ u₁ : ℂ) * Φ y ∂μ := by simp_rw [hΦ]
      _ = (χ u₁ : ℂ) * ∫ y, Φ y ∂μ := integral_const_mul _ _
  have h1 : (1 - (χ u₁ : ℂ)) * ∫ y, Φ y ∂μ = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact hI
  have hne : (χ u₁ : ℂ) ≠ 1 := fun h => hχ (Units.val_eq_one.mp h)
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne
  · rwa [hΦdef, integral_indicator hSm] at h

end Generic

section Kv

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast one_lt_absNorm v

private theorem absNorm_real_pos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) :=
  one_pos.trans (one_lt_absNorm_real v)

private theorem norm_eq_zpow_of_valued {x : v.adicCompletion K} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

private theorem modulus_eq_nnnorm_fun :
    (modulus : v.adicCompletion K → ℝ≥0) = fun x => ‖x‖₊ :=
  funext (modulus_adicCompletion_eq_nnnorm K v)

private theorem coe_modulus_of_valued {x : v.adicCompletion K} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    (modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm, norm_eq_zpow_of_valued v hx]

private theorem modulus_eq_one_of_valued {u : v.adicCompletion K} (hu : Valued.v u = 1) : modulus u = 1 := by
  rw [← NNReal.coe_inj, NNReal.coe_one, coe_modulus_of_valued v (m := 0) (by rw [hu, WithZero.exp_zero]),
    zpow_zero]

private theorem isClosed_ball (k : ℤ) : IsClosed {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 :=
    Units.ne_zero _
  have h := isClosed_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

private theorem isOpen_ball (k : ℤ) : IsOpen {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 :=
    Units.ne_zero _
  have h := isOpen_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

private theorem coe_integers_eq :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = {x | Valued.v x ≤ WithZero.exp 0} := by
  ext x
  rw [WithZero.exp_zero]
  exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v

private theorem isCompact_integers : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)

private theorem continuous_addChar_of_level (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1) : Continuous ψ := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hmem : (fun y => y - x) ⁻¹' {h : v.adicCompletion K | Valued.v h ≤ WithZero.exp n} ∈ nhds x := by
    refine ((isOpen_ball v n).preimage (continuous_id.sub continuous_const)).mem_nhds ?_
    show Valued.v (x - x) ≤ WithZero.exp n
    rw [sub_self, map_zero]
    exact zero_le'
  have hev : (fun _ => ψ x) =ᶠ[nhds x] (ψ : v.adicCompletion K → ℂ) := by
    refine Filter.mem_of_superset hmem fun y hy => ?_
    show ψ x = ψ y
    rw [show ψ y = ψ (x + (y - x)) by rw [add_sub_cancel], AddChar.map_add_eq_mul, hψn _ hy, mul_one]
  exact continuousAt_const.congr hev

private def shell (j : ℕ) : Set (v.adicCompletion K) := {y | Valued.v y = WithZero.exp (-(j : ℤ))}

private theorem mem_shell {j : ℕ} {y : v.adicCompletion K} : y ∈ shell v j ↔ Valued.v y = WithZero.exp (-(j : ℤ)) :=
  Iff.rfl

private theorem shell_eq_diff (j : ℕ) :
    shell v j = {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(j : ℤ))}
      \ {y | Valued.v y ≤ WithZero.exp (-((j + 1 : ℕ) : ℤ))} := by
  ext y
  rw [Set.mem_diff, Set.mem_setOf_eq, Set.mem_setOf_eq, mem_shell]
  constructor
  · intro hy
    refine ⟨hy.le, fun h => ?_⟩
    rw [hy, WithZero.exp_le_exp] at h
    push_cast at h
    omega
  · rintro ⟨h1, h2⟩
    have hne : Valued.v y ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hne).symm⟩
    rw [hm, WithZero.exp_le_exp] at h1 h2
    rw [hm]
    push_cast at h2
    congr 1
    omega

private theorem measurableSet_shell [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (j : ℕ) : MeasurableSet (shell v j) := by
  rw [shell_eq_diff]
  exact (isClosed_ball v _).measurableSet.diff (isClosed_ball v _).measurableSet

private theorem isClosed_shell (j : ℕ) : IsClosed (shell v j) := by
  rw [shell_eq_diff]
  exact (isClosed_ball v _).sdiff (isOpen_ball v _)

private theorem shell_subset_integers (j : ℕ) :
    shell v j ⊆ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  intro y hy
  rw [coe_integers_eq, Set.mem_setOf_eq, (mem_shell v).mp hy, WithZero.exp_le_exp]
  omega

private theorem shell_subset_ball (j : ℕ) :
    shell v j ⊆ {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(j : ℤ))} := fun _ hy => le_of_eq hy

private theorem isCompact_shell (j : ℕ) : IsCompact (shell v j) :=
  (isCompact_integers v).of_isClosed_subset (isClosed_shell v j) (shell_subset_integers v j)

private theorem shell_zero : shell v 0 = {u : v.adicCompletion K | Valued.v u = 1} := by
  ext u
  rw [mem_shell, Set.mem_setOf_eq, Nat.cast_zero, neg_zero, WithZero.exp_zero]

private theorem pairwise_disjoint_shell : Pairwise (Function.onFun Disjoint (shell v)) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro y hi hj
  rw [mem_shell] at hi hj
  have h := hi.symm.trans hj
  have h1 := WithZero.exp_le_exp.mp h.le
  have h2 := WithZero.exp_le_exp.mp h.ge
  exact hij (by omega)

private theorem iUnion_shell :
    (⋃ j, shell v j) = (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ∩ {0}ᶜ := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff, mem_shell,
    coe_integers_eq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨?_, fun h0 => ?_⟩
    · rw [hj, WithZero.exp_le_exp]
      omega
    · rw [h0, map_zero] at hj
      exact WithZero.exp_ne_zero hj.symm
  · rintro ⟨h1, h0⟩
    have hne : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hne).symm⟩
    rw [hm, WithZero.exp_le_exp] at h1
    refine ⟨(-m).toNat, ?_⟩
    rw [hm]
    congr 1
    omega

private theorem exists_eq_uniformizer_zpow_mul {j : ℕ} {y : v.adicCompletion K} (hy : y ∈ shell v j) :
    ∃ u ∈ shell v 0, y = ((uniformizerUnit K v ^ (j : ℤ) : (v.adicCompletion K)ˣ) : v.adicCompletion K) * u := by
  refine ⟨((uniformizerUnit K v ^ (-(j : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K) * y, ?_, ?_⟩
  · rw [mem_shell, map_mul, valued_uniformizerUnit_zpow, neg_neg, (mem_shell v).mp hy, ← WithZero.exp_add,
      add_neg_cancel, Nat.cast_zero, neg_zero]
  · rw [← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, one_mul]

private theorem charExt_eq_of_valued_sub_le {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt K v a, χ u = 1) {y₀ y : v.adicCompletion K} (hy₀ : y₀ ≠ 0)
    (h : Valued.v (y - y₀) ≤ Valued.v y₀ * WithZero.exp (-((a + 1 : ℕ) : ℤ))) :
    charExt χ y = charExt χ y₀ := by
  have hv0 : Valued.v y₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hy₀
  obtain ⟨m₀, hm₀⟩ : ∃ m : ℤ, Valued.v y₀ = WithZero.exp m := ⟨_, (WithZero.exp_log hv0).symm⟩
  have h' : Valued.v (y - y₀) ≤ WithZero.exp (m₀ + -((a + 1 : ℕ) : ℤ)) := by
    rwa [hm₀, ← WithZero.exp_add] at h
  have hlt : Valued.v (y - y₀) < Valued.v y₀ := by
    refine h'.trans_lt ?_
    rw [hm₀, WithZero.exp_lt_exp]
    omega
  have hyy : Valued.v y = Valued.v y₀ := Valuation.map_eq_of_sub_lt _ hlt
  have hy : y ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hyy]; exact hv0)
  set u : (v.adicCompletion K)ˣ := Units.mk0 y hy * (Units.mk0 y₀ hy₀)⁻¹ with hu
  have huval : (u : v.adicCompletion K) = y * y₀⁻¹ := by simp [hu]
  have humem : u ∈ higherUnitsAt K v a := by
    refine ⟨?_, Or.inr ?_⟩
    · rw [huval, map_mul, map_inv₀, hyy, mul_inv_cancel₀ hv0]
    · have hsub : (u : v.adicCompletion K) - 1 = y₀⁻¹ * (y - y₀) := by
        rw [huval, mul_sub, inv_mul_cancel₀ hy₀, mul_comm y₀⁻¹ y]
      rw [hsub, map_mul, map_inv₀, hm₀, ← WithZero.exp_neg]
      calc WithZero.exp (-m₀) * Valued.v (y - y₀)
          ≤ WithZero.exp (-m₀) * WithZero.exp (m₀ + -((a + 1 : ℕ) : ℤ)) := mul_le_mul_right h' _
        _ = WithZero.exp (-((a + 1 : ℕ) : ℤ)) := by rw [← WithZero.exp_add]; congr 1; omega
        _ ≤ WithZero.exp (-(a : ℤ)) := WithZero.exp_le_exp.mpr (by push_cast; omega)
  have hmk : Units.mk0 y hy = u * Units.mk0 y₀ hy₀ := by rw [hu, inv_mul_cancel_right]
  rw [charExt_of_ne_zero χ hy, charExt_of_ne_zero χ hy₀, hmk, map_mul, hχ u humem, one_mul]

private theorem continuousOn_charExt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt K v a, χ u = 1) :
    ContinuousOn (charExt χ) ({0}ᶜ : Set (v.adicCompletion K)) := by
  intro y₀ hy₀
  have hy₀' : y₀ ≠ 0 := hy₀
  set t : v.adicCompletion K :=
    y₀ * ((uniformizerUnit K v ^ ((a + 1 : ℕ) : ℤ) : (v.adicCompletion K)ˣ) : v.adicCompletion K) with ht
  have ht0 : t ≠ 0 := mul_ne_zero hy₀' (Units.ne_zero _)
  have hvt : Valued.v t = Valued.v y₀ * WithZero.exp (-((a + 1 : ℕ) : ℤ)) := by
    rw [ht, map_mul, valued_uniformizerUnit_zpow]
  have hmem : (fun y => y - y₀) ⁻¹' {h : v.adicCompletion K | Valued.v h ≤ Valued.v t} ∈ nhds y₀ := by
    refine ((isOpen_setOf_valued_le v t ht0).preimage (continuous_id.sub continuous_const)).mem_nhds ?_
    show Valued.v (y₀ - y₀) ≤ Valued.v t
    rw [sub_self, map_zero]
    exact zero_le'
  have hev : charExt χ =ᶠ[nhdsWithin y₀ {0}ᶜ] fun _ => charExt χ y₀ :=
    Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds hmem) fun y hy =>
      charExt_eq_of_valued_sub_le v hχ hy₀' (by rw [← hvt]; exact hy)
  exact (continuousWithinAt_const.congr_of_eventuallyEq hev
    (by simp : charExt χ y₀ = (fun _ => charExt χ y₀) y₀))

private theorem measurable_charExt [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (hχ : ∀ u ∈ higherUnitsAt K v a, χ u = 1) :
    Measurable (charExt χ) :=
  measurable_of_continuousOn_compl_singleton 0 (continuousOn_charExt v hχ)

private theorem exists_unit_of_hasConductorExponentAt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) {j : ℕ} (hj : 1 ≤ j) :
    ∃ u₁ : (v.adicCompletion K)ˣ, Valued.v (u₁ : v.adicCompletion K) = 1 ∧
      Valued.v ((u₁ : v.adicCompletion K) - 1) ≤ WithZero.exp (-((a - j : ℕ) : ℤ)) ∧ χ⁻¹ u₁ ≠ 1 := by
  obtain ⟨u₁, hmem, hne⟩ := hχ.2 (a - j) (by omega)
  obtain ⟨hval, hball⟩ := (mem_higherUnitsAt_iff K v).mp hmem
  refine ⟨u₁, hval, ?_, by rwa [MonoidHom.inv_apply, inv_ne_one]⟩
  rcases hball with h0 | h
  · rw [h0, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    calc Valued.v ((u₁ : v.adicCompletion K) - 1)
        ≤ max (Valued.v (u₁ : v.adicCompletion K)) (Valued.v (1 : v.adicCompletion K)) :=
          Valuation.map_sub _ _ _
      _ = 1 := by rw [hval, map_one, max_self]
  · exact h

private theorem psi_mul_invariant (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1) (a j : ℕ)
    {t : v.adicCompletion K} (hvt : Valued.v t = WithZero.exp (n + a)) {u₁ : (v.adicCompletion K)ˣ}
    (hu₁' : Valued.v ((u₁ : v.adicCompletion K) - 1) ≤ WithZero.exp (-((a - j : ℕ) : ℤ)))
    {y : v.adicCompletion K} (hy : y ∈ shell v j) :
    ψ (t * ((u₁ : v.adicCompletion K) * y)) = ψ (t * y) := by
  have hsplit : t * ((u₁ : v.adicCompletion K) * y) = t * y + t * (((u₁ : v.adicCompletion K) - 1) * y) := by
    ring
  have hsmall : Valued.v (t * (((u₁ : v.adicCompletion K) - 1) * y)) ≤ WithZero.exp n := by
    rw [map_mul, map_mul, hvt, (mem_shell v).mp hy]
    calc WithZero.exp (n + a) * (Valued.v ((u₁ : v.adicCompletion K) - 1) * WithZero.exp (-(j : ℤ)))
        ≤ WithZero.exp (n + a) * (WithZero.exp (-((a - j : ℕ) : ℤ)) * WithZero.exp (-(j : ℤ))) :=
          mul_le_mul' le_rfl (mul_le_mul' hu₁' le_rfl)
      _ = WithZero.exp (n + a + (-((a - j : ℕ) : ℤ) + -(j : ℤ))) := by
          rw [← WithZero.exp_add, ← WithZero.exp_add]
      _ ≤ WithZero.exp n := WithZero.exp_le_exp.mpr (by omega)
  rw [hsplit, AddChar.map_add_eq_mul, hψn _ hsmall, mul_one]

private theorem setIntegral_shell_eq_zero [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a)
    {t : v.adicCompletion K} (hvt : Valued.v t = WithZero.exp (n + a)) {j : ℕ} (hj : 1 ≤ j) :
    ∫ y in shell v j, ψ (t * y) * charExt χ⁻¹ y ∂μ = 0 := by
  obtain ⟨u₁, hu₁, hu₁', hne⟩ := exists_unit_of_hasConductorExponentAt v ha hχ hj
  refine setIntegral_mul_charExt_eq_zero μ (measurableSet_shell v j) _ χ⁻¹ (modulus_eq_one_of_valued v hu₁) hne
    (fun y => ?_) (fun y hy => psi_mul_invariant v ψ n hψn a j hvt hu₁' hy)
  rw [mem_shell, mem_shell, map_mul, hu₁, one_mul]

private def rescaledFun (ψ : AddChar (v.adicCompletion K) ℂ) (t : v.adicCompletion K) (V : ℂ)
    (z : v.adicCompletion K) : ℂ :=
  ψ (t * z) * (V * (v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator (fun _ => (1 : ℂ)) z)

private def gaussIntegralAt [MeasurableSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K))
    (ψ : AddChar (v.adicCompletion K) ℂ) (t : v.adicCompletion K) (χ : (v.adicCompletion K)ˣ →* ℂˣ) : ℂ :=
  ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (t * u) * charExt χ⁻¹ u ∂μ

private theorem ball_natneg_subset_integers (j : ℕ) :
    {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(j : ℤ))}
      ⊆ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  intro y hy
  rw [coe_integers_eq, Set.mem_setOf_eq]
  exact le_trans hy (WithZero.exp_le_exp.mpr (by omega))

private theorem localZeta_rescaledFun [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (hV : ∀ k : ℤ, μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (Ideal.absNorm v.asIdeal : ℝ) ^ k * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a) (s : ℂ)
    (hs : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))‖ < 1)
    {t : v.adicCompletion K} (hvt : Valued.v t = WithZero.exp (n + a)) (V : ℂ) :
    localZeta μ (rescaledFun v ψ t V) χ⁻¹ (1 - s) = V * gaussIntegralAt v μ ψ t χ := by
  have hχ' : ∀ u ∈ higherUnitsAt K v a, χ⁻¹ u = 1 := fun u hu => by
    rw [MonoidHom.inv_apply, hχ.1 u hu, inv_one]
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := absNorm_real_pos v

  have hm : AEMeasurable (fun x : v.adicCompletion K => (modulus x)⁻¹) (μ.restrict {0}ᶜ) := by
    rw [modulus_eq_nnnorm_fun v]
    exact measurable_nnnorm.inv.aemeasurable
  rw [localZeta, integral_mulMeasure μ _ hm]
  set G : v.adicCompletion K → ℂ := fun x => ((modulus x)⁻¹ : ℝ≥0) •
    (rescaledFun v ψ t V x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)) with hG
  set qs : ℂ := (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)) with hqs

  have hGshell : ∀ j, ∀ y ∈ shell v j, G y =
      V * ((((Ideal.absNorm v.asIdeal : ℝ) ^ j : ℝ) : ℂ) * qs ^ j) * (ψ (t * y) * charExt χ⁻¹ y) := by
    intro j y hy
    have hyO : y ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := shell_subset_integers v j hy
    have hny : ‖y‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(j : ℤ)) := norm_eq_zpow_of_valued v ((mem_shell v).mp hy)
    have hmody : modulus y = ‖y‖₊ := modulus_adicCompletion_eq_nnnorm K v y
    simp only [hG, rescaledFun, Set.indicator_of_mem hyO, mul_one, hmody, coe_nnnorm, hny]
    rw [ofReal_zpow_neg_cpow, NNReal.smul_def, Complex.real_smul, NNReal.coe_inv, Complex.ofReal_inv]
    have : (‖y‖₊ : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(j : ℤ)) := by rw [coe_nnnorm, hny]
    rw [this, zpow_neg, zpow_natCast, Complex.ofReal_inv, inv_inv]
    push_cast
    ring
  have hGoff : ∀ y ∈ ({0}ᶜ : Set (v.adicCompletion K)) \ ⋃ j, shell v j, G y = 0 := by
    intro y hy
    rw [iUnion_shell] at hy
    have hyO : y ∉ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := fun h => hy.2 ⟨h, hy.1⟩
    simp [hG, rescaledFun, Set.indicator_of_notMem hyO]
  have hsub : (⋃ j, shell v j) ⊆ ({0}ᶜ : Set (v.adicCompletion K)) := by
    rw [iUnion_shell]; exact Set.inter_subset_right
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero (measurableSet_singleton 0).compl hsub hGoff]

  obtain ⟨B₁, hB₁⟩ : ∃ B₁, ∀ z ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)), ‖ψ (t * z)‖ ≤ B₁ :=
    (isCompact_integers v).exists_bound_of_continuousOn
      (((continuous_addChar_of_level v ψ n hψn).comp (continuous_const.mul continuous_id)).continuousOn)
  obtain ⟨B₂, hB₂⟩ : ∃ B₂, ∀ u ∈ shell v 0, ‖charExt χ⁻¹ u‖ ≤ B₂ :=
    (isCompact_shell v 0).exists_bound_of_continuousOn ((continuousOn_charExt v hχ').mono fun u hu h0 => by
      rw [Set.mem_singleton_iff] at h0
      rw [mem_shell, h0, map_zero] at hu
      exact WithZero.exp_ne_zero hu.symm)
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 0 (v.adicCompletionIntegers K).zero_mem)
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ 1 (by
    rw [mem_shell, map_one, Nat.cast_zero, neg_zero, WithZero.exp_zero]))
  set r : ℝ := ‖(χ⁻¹ (uniformizerUnit K v) : ℂ) * qs‖ with hr
  set C : ℝ := ‖V‖ * (B₁ * B₂) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity

  have hnormG : ∀ j, ∀ y ∈ shell v j, ‖G y‖ ≤ C * ((Ideal.absNorm v.asIdeal : ℝ) ^ j * r ^ j) := by
    intro j y hy
    have hψb : ‖ψ (t * y)‖ ≤ B₁ := hB₁ y (shell_subset_integers v j hy)
    have hχb : ‖charExt χ⁻¹ y‖ ≤ ‖(χ⁻¹ (uniformizerUnit K v) : ℂ)‖ ^ j * B₂ := by
      obtain ⟨u, hu, hyu⟩ := exists_eq_uniformizer_zpow_mul v hy
      rw [hyu, charExt_units_mul, norm_mul, map_zpow, Units.val_zpow_eq_zpow_val, norm_zpow, zpow_natCast]
      exact mul_le_mul_of_nonneg_left (hB₂ u hu) (pow_nonneg (norm_nonneg _) _)
    have hcj : ‖((((Ideal.absNorm v.asIdeal : ℝ) ^ j : ℝ) : ℂ) * qs ^ j)‖
        = (Ideal.absNorm v.asIdeal : ℝ) ^ j * ‖qs‖ ^ j := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hq0.le _)]
    calc ‖G y‖ = ‖V‖ * ((Ideal.absNorm v.asIdeal : ℝ) ^ j * ‖qs‖ ^ j) * (‖ψ (t * y)‖ * ‖charExt χ⁻¹ y‖) := by
          rw [hGshell j y hy, norm_mul, norm_mul, hcj, norm_mul]
      _ ≤ ‖V‖ * ((Ideal.absNorm v.asIdeal : ℝ) ^ j * ‖qs‖ ^ j)
            * (B₁ * (‖(χ⁻¹ (uniformizerUnit K v) : ℂ)‖ ^ j * B₂)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hψb hχb (norm_nonneg _) hB₁0) (by positivity)
      _ = C * ((Ideal.absNorm v.asIdeal : ℝ) ^ j * r ^ j) := by
          rw [hC, hr, norm_mul, mul_pow]; ring

  have hOfin : μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) < ∞ :=
    (isCompact_integers v).measure_lt_top
  have hshell_fin : ∀ j, μ (shell v j) ≠ ∞ := fun j =>
    ((measure_mono (shell_subset_integers v j)).trans_lt hOfin).ne
  set M : ℝ := μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) with hM
  have hshell_real : ∀ j, μ.real (shell v j) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(j : ℤ)) * M := fun j => by
    rw [hM, ← hV (-(j : ℤ))]
    exact measureReal_mono (shell_subset_ball v j)
      (((measure_mono (ball_natneg_subset_integers v j)).trans_lt hOfin).ne)

  have hmeas : ∀ j, AEStronglyMeasurable G (μ.restrict (shell v j)) := by
    intro j
    have hF : Measurable fun y : v.adicCompletion K =>
        V * ((((Ideal.absNorm v.asIdeal : ℝ) ^ j : ℝ) : ℂ) * qs ^ j) * (ψ (t * y) * charExt χ⁻¹ y) :=
      measurable_const.mul ((((continuous_addChar_of_level v ψ n hψn).comp
        (continuous_const.mul continuous_id)).measurable).mul (measurable_charExt v hχ'))
    refine hF.aestronglyMeasurable.congr ?_
    exact (ae_restrict_iff' (measurableSet_shell v j)).mpr (Filter.Eventually.of_forall fun y hy =>
      (hGshell j y hy).symm)
  have hint_j : ∀ j, IntegrableOn G (shell v j) μ := fun j =>
    Integrable.mono' (integrableOn_const (C := C * ((Ideal.absNorm v.asIdeal : ℝ) ^ j * r ^ j))
      (hshell_fin j)) (hmeas j) ((ae_restrict_iff' (measurableSet_shell v j)).mpr
        (Filter.Eventually.of_forall fun y hy => hnormG j y hy))

  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := hs
  have hsum : Summable fun j => ∫ x in shell v j, ‖G x‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun x => norm_nonneg _) (fun j => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (C * M))
    have hprod : (Ideal.absNorm v.asIdeal : ℝ) ^ j * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(j : ℤ)) = 1 := by
      rw [zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hq0.ne')]
    calc ∫ x in shell v j, ‖G x‖ ∂μ ≤ ‖∫ x in shell v j, ‖G x‖ ∂μ‖ := Real.le_norm_self _
      _ ≤ C * ((Ideal.absNorm v.asIdeal : ℝ) ^ j * r ^ j) * μ.real (shell v j) :=
          norm_setIntegral_le_of_norm_le_const ((measure_mono (shell_subset_integers v j)).trans_lt hOfin)
            fun x hx => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hnormG j x hx
      _ ≤ C * ((Ideal.absNorm v.asIdeal : ℝ) ^ j * r ^ j) * ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(j : ℤ)) * M) :=
          mul_le_mul_of_nonneg_left (hshell_real j) (by positivity)
      _ = C * M * r ^ j * ((Ideal.absNorm v.asIdeal : ℝ) ^ j * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(j : ℤ))) := by
          ring
      _ = C * M * r ^ j := by rw [hprod, mul_one]
  have hint : IntegrableOn G (⋃ j, shell v j) μ := integrableOn_iUnion_of_summable_integral_norm hint_j hsum
  rw [integral_iUnion (measurableSet_shell v) (pairwise_disjoint_shell v) hint]

  have hshell_int : ∀ j, ∫ x in shell v j, G x ∂μ =
      V * ((((Ideal.absNorm v.asIdeal : ℝ) ^ j : ℝ) : ℂ) * qs ^ j) *
        ∫ x in shell v j, ψ (t * x) * charExt χ⁻¹ x ∂μ := by
    intro j
    rw [setIntegral_congr_fun (measurableSet_shell v j) (hGshell j), integral_const_mul]
  have hzero : ∀ j, j ≠ 0 → ∫ x in shell v j, G x ∂μ = 0 := by
    intro j hj
    rw [hshell_int, setIntegral_shell_eq_zero v μ ψ n hψn ha hχ hvt (Nat.one_le_iff_ne_zero.mpr hj), mul_zero]
  rw [tsum_eq_single 0 hzero, hshell_int 0, gaussIntegralAt, shell_zero]
  simp

private theorem tateFourier_indicator_eq_rescaledFun [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1) (a : ℕ) :
    tateFourier ψ μ
        ({x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))}.indicator fun _ => (1 : ℂ))
      = fun y => rescaledFun v ψ
          ((uniformizerUnit K v ^ (-(n + a : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K)
          ((μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-(a : ℤ))} : ℝ) : ℂ)
          (((uniformizerUnit K v ^ (n + a : ℤ) : (v.adicCompletion K)ˣ) : v.adicCompletion K) * y) := by
  funext y
  rw [LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le K v μ ψ n hψn hψn' 1 (a : ℤ) y,
    rescaledFun, one_mul]
  have hcancel : ((uniformizerUnit K v ^ (-(n + a : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      * (((uniformizerUnit K v ^ (n + a : ℤ) : (v.adicCompletion K)ˣ) : v.adicCompletion K) * y) = y := by
    rw [← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_mul]
  rw [hcancel, mul_assoc]
  congr 2

  have hiff : Valued.v y ≤ WithZero.exp (n + (a : ℤ)) ↔
      ((uniformizerUnit K v ^ (n + a : ℤ) : (v.adicCompletion K)ˣ) : v.adicCompletion K) * y
        ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    rw [coe_integers_eq, Set.mem_setOf_eq, map_mul, valued_uniformizerUnit_zpow, WithZero.exp_zero]
    constructor
    · intro h
      calc WithZero.exp (-(n + (a : ℤ))) * Valued.v y
          ≤ WithZero.exp (-(n + (a : ℤ))) * WithZero.exp (n + (a : ℤ)) := mul_le_mul_right h _
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    · intro h
      calc Valued.v y = WithZero.exp (n + (a : ℤ)) * (WithZero.exp (-(n + (a : ℤ))) * Valued.v y) := by
            rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]
        _ ≤ WithZero.exp (n + (a : ℤ)) * 1 := mul_le_mul_right h _
        _ = WithZero.exp (n + (a : ℤ)) := mul_one _
  by_cases hy : Valued.v y ≤ WithZero.exp (n + (a : ℤ))
  · rw [Set.indicator_of_mem (show y ∈ {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + (a : ℤ))}
        from hy), Set.indicator_of_mem (hiff.mp hy)]
  · rw [Set.indicator_of_notMem (show y ∉ {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + (a : ℤ))}
        from hy), Set.indicator_of_notMem (fun h => hy (hiff.mpr h))]

private theorem main_of_ballVolume [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (hV : ∀ k : ℤ, μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (Ideal.absNorm v.asIdeal : ℝ) ^ k * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a) (s : ℂ)
    (hs : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))‖ < 1) :
    localZeta μ (tateFourier ψ μ
        ({x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))}.indicator fun _ => (1 : ℂ)))
        χ⁻¹ (1 - s)
      = ((μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-(a : ℤ))} : ℝ) : ℂ)
          * (χ (uniformizerUnit K v) : ℂ) ^ (n + a : ℤ)
          * ((((Ideal.absNorm v.asIdeal : ℝ) ^ (n + a : ℤ) : ℝ) : ℂ)) ^ (1 - s)
          * ∫ u in {u : v.adicCompletion K | Valued.v u = 1},
              ψ (((uniformizerUnit K v ^ (-(n + a : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K) * u)
                * charExt χ⁻¹ u ∂μ := by
  have hvt : Valued.v (((uniformizerUnit K v ^ (-(n + a : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K))
      = WithZero.exp (n + a) := by
    rw [valued_uniformizerUnit_zpow, neg_neg]
  rw [tateFourier_indicator_eq_rescaledFun v μ ψ n hψn hψn' a,
    localZeta_comp_units_mul μ (rescaledFun v ψ
        ((uniformizerUnit K v ^ (-(n + a : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K)
        ((μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-(a : ℤ))} : ℝ) : ℂ))
      χ⁻¹ (1 - s) (uniformizerUnit K v ^ (n + a : ℤ)),
    localZeta_rescaledFun v μ hV ψ n hψn χ a ha hχ s hs hvt]
  have h1 : ((χ⁻¹ (uniformizerUnit K v ^ (n + a : ℤ))⁻¹ : ℂˣ) : ℂ)
      = ((χ (uniformizerUnit K v) : ℂˣ) : ℂ) ^ (n + a : ℤ) := by
    rw [MonoidHom.inv_apply, map_inv, inv_inv, map_zpow, Units.val_zpow_eq_zpow_val]
  have hinv : ((uniformizerUnit K v ^ (n + a : ℤ))⁻¹ : (v.adicCompletion K)ˣ)
      = uniformizerUnit K v ^ (-(n + a : ℤ)) := (zpow_neg _ _).symm
  have h2 : ((modulus (((uniformizerUnit K v ^ (n + a : ℤ))⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      : ℝ) : ℂ) = ((((Ideal.absNorm v.asIdeal : ℝ) ^ (n + a : ℤ)) : ℝ) : ℂ) := by
    rw [coe_modulus_of_valued v (m := n + a) (by rw [hinv, valued_uniformizerUnit_zpow, neg_neg])]
  rw [h1, h2, gaussIntegralAt]
  ring

end Kv

end LanglandsTunnell.TateLocal.RamifiedKv

end

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel

open _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_TateLocal_localZeta_tateFourier_indicator_setOf_valued_sub_one_le.LanglandsTunnell.TateLocal in

theorem solution (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a) (s : ℂ)
    (hs : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))‖ < 1) :
    localZeta μ (tateFourier ψ μ
        ({x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))}.indicator fun _ => (1 : ℂ)))
        χ⁻¹ (1 - s)
      = ((μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-(a : ℤ))} : ℝ) : ℂ)
          * (χ (uniformizerUnit K v) : ℂ) ^ (n + a : ℤ)
          * ((((Ideal.absNorm v.asIdeal : ℝ) ^ (n + a : ℤ) : ℝ) : ℂ)) ^ (1 - s)
          * ∫ u in {u : v.adicCompletion K | Valued.v u = 1},
              ψ (((uniformizerUnit K v ^ (-(n + a : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K) * u)
                * charExt χ⁻¹ u ∂μ :=
  LanglandsTunnell.TateLocal.RamifiedKv.main_of_ballVolume v μ
    (LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp K v μ) ψ n hψn hψn' χ a ha hχ s hs

end S_LanglandsTunnell_TateLocal_localZeta_tateFourier_indicator_setOf_valued_sub_one_le
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_localZeta_tateFourier_indicator_setOf_valued_sub_one_le (solution)
