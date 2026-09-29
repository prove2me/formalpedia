-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.matFourier22_congr_of_forall_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/71dc0967-167c-5609-8bd3-dbf038199d5d

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_matFourier22_congr_of_forall_det_ne_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Topology
open scoped ENNReal NNReal Pointwise

namespace MF22Congr

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "Fˣ" => ((HeightOneSpectrum.adicCompletion ℚ p)ˣ)

theorem modulus_eq_nnnorm (x : F) : modulus x = ‖x‖₊ :=
  LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x

theorem smul_set_eq_preimage {c : F} (hc : c ≠ 0) (T : Set F) :
    c • T = (fun y => c⁻¹ * y) ⁻¹' T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_eq_mul, inv_mul_cancel_left₀ hc] using hy
  · intro hx
    exact ⟨c⁻¹ * x, hx, by simp [smul_eq_mul, mul_inv_cancel_left₀ hc]⟩

theorem norm_eq_zpow_of_valued {x : F} {k : ℤ} (hx : Valued.v x = WithZero.exp k) :
    ‖x‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ k := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp k) = ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

section Haar

variable [MeasurableSpace (HeightOneSpectrum.adicCompletion ℚ p)] [BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)]

theorem map_mul_left_eq_smul (ν : Measure F) [ν.IsAddHaarMeasure] (u : Fˣ) :
    ν.map (fun x : F => (u : F) * x) = ((modulus (u : F) : ℝ≥0∞))⁻¹ • ν := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun x : F => (u : F) * x) ⁻¹' s = ((u⁻¹ : Fˣ) : F) • s := by
    rw [smul_set_eq_preimage p (u⁻¹).ne_zero, Units.val_inv_eq_inv_val, inv_inv]
  rw [hpre]
  have h := distribHaarChar_mul ν (u⁻¹) s
  rw [show ((u⁻¹ : Fˣ) • s : Set F) = ((u⁻¹ : Fˣ) : F) • s from rfl] at h
  rw [← h, map_inv, modulus_coe_units, ENNReal.coe_inv (distribHaarChar_pos).ne']

theorem measure_zero_singleton (ν : Measure F) [ν.IsAddHaarMeasure] : ν {0} = 0 := by
  set u : Fˣ := NumberField.AdelicLevel.uniformizerUnit ℚ p with hu
  have hvu : Valued.v (u : F) = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit ℚ p
  have hN1 : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by
    have h2 : 2 ≤ Ideal.absNorm p.asIdeal := by
      have hne1 : Ideal.absNorm p.asIdeal ≠ 1 := by
        rw [Ne, Ideal.absNorm_eq_one_iff]; exact p.isPrime.ne_top
      have hne0 : Ideal.absNorm p.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
      omega
    exact_mod_cast h2
  have hmu : (modulus (u : F) : ℝ≥0∞) ≠ 1 := by
    intro h
    have h' : ‖(u : F)‖ = 1 := by
      have := congrArg (fun t : ℝ≥0∞ => t.toNNReal) h
      simp only [ENNReal.toNNReal_coe, ENNReal.toNNReal_one] at this
      rw [modulus_eq_nnnorm] at this
      have := congrArg (fun t : ℝ≥0 => (t : ℝ)) this
      simpa using this
    rw [norm_eq_zpow_of_valued p hvu, zpow_neg_one] at h'
    have : (Ideal.absNorm p.asIdeal : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hN1
    exact absurd h' this.ne
  have hpre : (fun x : F => (u : F) * x) ⁻¹' ({0} : Set F) = {0} := by
    ext x; simp [u.ne_zero]
  have h1 : ν {0} = ((modulus (u : F) : ℝ≥0∞))⁻¹ * ν {0} := by
    have := congrArg (fun μ : Measure F => μ {0}) (map_mul_left_eq_smul p ν u)
    simp only [Measure.smul_apply, smul_eq_mul] at this
    rwa [Measure.map_apply (measurable_const_mul _) (measurableSet_singleton 0), hpre] at this
  have hfin : ν {0} ≠ ⊤ := (isCompact_singleton.measure_lt_top).ne
  by_contra h0
  have h2 : (1 : ℝ≥0∞) * ν {0} = ((modulus (u : F) : ℝ≥0∞))⁻¹ * ν {0} := by rw [one_mul]; exact h1
  have h3 : (1 : ℝ≥0∞) = ((modulus (u : F) : ℝ≥0∞))⁻¹ :=
    (ENNReal.mul_left_inj h0 hfin).mp h2
  exact hmu (by rw [← inv_inv ((modulus (u : F) : ℝ≥0∞)), ← h3, inv_one])

theorem measure_point (ν : Measure F) [ν.IsAddHaarMeasure] (c : F) : ν {c} = 0 := by
  have h : (fun x : F => x + (-c)) ⁻¹' ({0} : Set F) = {c} := by
    ext x; simp [add_neg_eq_zero]
  rw [← h, measure_preimage_add_right, measure_zero_singleton p ν]

theorem measure_line_eq_zero (ν : Measure F) [ν.IsAddHaarMeasure] [SFinite ν] (u : F × F) (hu : u ≠ (0, 0)) :
    (ν.prod ν) {w : F × F | u.1 * w.2 - w.1 * u.2 = 0} = 0 := by
  have hmeas : MeasurableSet {w : F × F | u.1 * w.2 - w.1 * u.2 = 0} := by
    have hc : Continuous fun w : F × F => u.1 * w.2 - w.1 * u.2 := by fun_prop
    exact (isClosed_singleton.preimage hc : IsClosed ((fun w : F × F => u.1 * w.2 - w.1 * u.2) ⁻¹' {0}))
      |>.measurableSet
  rw [Measure.measure_prod_null hmeas]
  have hν0 : ν {0} = 0 := measure_zero_singleton p ν
  by_cases h1 : u.1 = 0
  ·
    have h2 : u.2 ≠ 0 := by
      intro h2; exact hu (Prod.ext h1 h2)
    have hae : ∀ᵐ x ∂ν, x ∈ ({0}ᶜ : Set F) := compl_mem_ae_iff.mpr hν0
    filter_upwards [hae] with x hx
    have hx0 : x ≠ 0 := hx
    have : Prod.mk x ⁻¹' {w : F × F | u.1 * w.2 - w.1 * u.2 = 0} = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_setOf_eq, h1, zero_mul, zero_sub, neg_eq_zero, Set.mem_empty_iff_false,
        iff_false]
      exact mul_ne_zero hx0 h2
    show ν (Prod.mk x ⁻¹' {w : F × F | u.1 * w.2 - w.1 * u.2 = 0}) = (0 : F → ℝ≥0∞) x
    rw [this, measure_empty, Pi.zero_apply]
  · refine Filter.Eventually.of_forall fun x => ?_
    have : Prod.mk x ⁻¹' {w : F × F | u.1 * w.2 - w.1 * u.2 = 0} = {x * u.2 * u.1⁻¹} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hy
        field_simp
        linear_combination hy
      · intro hy
        rw [hy]; field_simp
        ring
    show ν (Prod.mk x ⁻¹' {w : F × F | u.1 * w.2 - w.1 * u.2 = 0}) = 0
    rw [this]
    exact measure_point p ν _

end Haar

end MF22Congr

end

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ)
    (φ φ' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (h : ∀ X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), X.det ≠ 0 → φ X = φ' X) :
    matFourier22 v η φ = matFourier22 v η φ' := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
    set c : NNReal := (Ideal.absNorm v.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2)
      with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact (NNReal.rpow_pos
        (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))).ne'
    have hdef : selfDualHaarAt ℚ v = (c : ENNReal) • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := rfl
    rw [hdef]
    exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top
  have hν0 : (selfDualHaarAt ℚ v) {0} = 0 := MF22Congr.measure_zero_singleton v _
  have hdet : ∀ (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (u w : v.adicCompletion ℚ × v.adicCompletion ℚ),
      (setCol22 v (setCol22 v Y 0 u) 1 w).det = u.1 * w.2 - w.1 * u.2 := by
    intro Y u w
    rw [Matrix.det_fin_two]
    simp [setCol22_apply]
  funext Y
  rw [matFourier22_eq, matFourier22_eq, colFourier22_apply, colFourier22_apply]
  refine integral_congr_ae ?_
  have h00 : ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) {((0 : v.adicCompletion ℚ), (0 : v.adicCompletion ℚ))} = 0 := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod, hν0, zero_mul]
  have hae : ∀ᵐ u ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)),
      u ∈ ({((0 : v.adicCompletion ℚ), (0 : v.adicCompletion ℚ))}ᶜ : Set (v.adicCompletion ℚ × v.adicCompletion ℚ)) :=
    compl_mem_ae_iff.mpr h00
  filter_upwards [hae] with u hu
  have hu' : u ≠ (0, 0) := hu

  have hinner : colFourier22 v η 1 φ (setCol22 v Y 0 u) = colFourier22 v η 1 φ' (setCol22 v Y 0 u) := by
    rw [colFourier22_apply, colFourier22_apply]
    refine integral_congr_ae ?_
    have hL := MF22Congr.measure_line_eq_zero v (selfDualHaarAt ℚ v) u hu'
    have haeL : ∀ᵐ w ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)),
        w ∈ ({w : v.adicCompletion ℚ × v.adicCompletion ℚ | u.1 * w.2 - w.1 * u.2 = 0}ᶜ :
          Set (v.adicCompletion ℚ × v.adicCompletion ℚ)) := compl_mem_ae_iff.mpr hL
    filter_upwards [haeL] with w hw
    have hw' : u.1 * w.2 - w.1 * u.2 ≠ 0 := hw
    rw [h _ (by rw [hdet]; exact hw')]
  rw [hinner]

end S_LanglandsTunnell_CubicInduction_matFourier22_congr_of_forall_det_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_matFourier22_congr_of_forall_det_ne_zero (solution)
