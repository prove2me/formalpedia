-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/1053b077-652f-5fab-9afa-154b9bcdee4c

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

noncomputable section

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt.LanglandsTunnell.TateLocal NumberField.AdelicLevel"
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.tateFourier_indicator_setOf_valued_sub_le"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "higherUnitsAt mem_higherUnitsAt_iff higherUnitsAt_antitone modulus modulus_coe_units tateFourier charExt charExt_of_ne_zero tateFourier_indicator_setOf_valued_sub_le modulus_adicCompletion_eq_nnnorm"
namespace DeligneLocalization
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

section Generic

theorem preimage_mul_left_eq_smul {F : Type*} [Field F] (u : Fˣ) (s : Set F) :
    (fun x => (u : F) * x) ⁻¹' s = u⁻¹ • s := by
  ext x
  rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]

theorem charExt_units_mul {F : Type*} [Field F] (χ : Fˣ →* ℂˣ) (u : Fˣ) (y : F) :
    charExt χ ((u : F) * y) = (χ u : ℂ) * charExt χ y := by
  by_cases hy : y = 0
  · simp [hy]
  · have hne : (u : F) * y ≠ 0 := mul_ne_zero u.ne_zero hy
    rw [charExt_of_ne_zero χ hne, charExt_of_ne_zero χ hy, ← Units.val_mul, ← map_mul]
    congr 2
    ext
    simp

theorem tateFourier_indicator_one {F : Type*} [Field F] [MeasurableSpace F] (ψ : AddChar F ℂ)
    (μ : Measure F) {S : Set F} (hS : MeasurableSet S) (x : F) :
    tateFourier ψ μ (S.indicator fun _ => (1 : ℂ)) x = ∫ y in S, ψ (y * x) ∂μ := by
  rw [tateFourier, ← integral_indicator hS]
  congr 1
  funext y
  by_cases hy : y ∈ S <;> simp [hy]

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]
  [MeasurableSpace F] [BorelSpace F]

theorem map_mul_left_eq_smul (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] (u : Fˣ) :
    Measure.map (fun x => (u : F) * x) μ = ((modulus (u : F) : ℝ≥0∞)⁻¹) • μ := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul _) hs, preimage_mul_left_eq_smul,
    Measure.smul_apply, smul_eq_mul, ← distribHaarChar_mul μ u⁻¹ s, map_inv, modulus_coe_units,
    ENNReal.coe_inv distribHaarChar_pos.ne']

theorem map_mul_left_of_modulus_eq_one (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] {u : Fˣ}
    (hu : modulus (u : F) = 1) : Measure.map (fun x => (u : F) * x) μ = μ := by
  rw [map_mul_left_eq_smul μ u, hu, ENNReal.coe_one, inv_one, one_smul]

theorem integral_comp_mul_left_of_modulus_eq_one (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular]
    {u : Fˣ} (hu : modulus (u : F) = 1) (Φ : F → ℂ) :
    ∫ y, Φ y ∂μ = ∫ y, Φ ((u : F) * y) ∂μ := by
  calc ∫ y, Φ y ∂μ = ∫ y, Φ y ∂(Measure.map (fun x => (u : F) * x) μ) := by
        rw [map_mul_left_of_modulus_eq_one μ hu]
    _ = ∫ y, Φ ((u : F) * y) ∂μ := by
        rw [← MeasurableEquiv.coe_mulLeft₀ u.ne_zero, integral_map_equiv]; rfl

theorem setIntegral_comp_mul_left_of_modulus_eq_one (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular]
    {u : Fˣ} (hu : modulus (u : F) = 1) (Φ : F → ℂ) {S : Set F} (hS : MeasurableSet S) :
    ∫ y in S, Φ y ∂μ = ∫ y in (fun y => (u : F) * y) ⁻¹' S, Φ ((u : F) * y) ∂μ := by
  have hpre : MeasurableSet ((fun y => (u : F) * y) ⁻¹' S) := (measurable_const_mul (u : F)) hS
  rw [← integral_indicator hS, ← integral_indicator hpre,
    integral_comp_mul_left_of_modulus_eq_one μ hu (S.indicator Φ)]
  congr 1

end Generic

section Kv

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem norm_eq_zpow_of_valued {x : v.adicCompletion K} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem coe_modulus_of_valued {x : v.adicCompletion K} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    (modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm, norm_eq_zpow_of_valued v hx]

theorem modulus_eq_one_of_valued {u : v.adicCompletion K} (hu : Valued.v u = 1) : modulus u = 1 := by
  rw [← NNReal.coe_inj, NNReal.coe_one, coe_modulus_of_valued v (m := 0) (by rw [hu, WithZero.exp_zero]),
    zpow_zero]

theorem isClosed_ball (k : ℤ) : IsClosed {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 :=
    Units.ne_zero _
  have h := isClosed_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem isOpen_ball (k : ℤ) : IsOpen {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 :=
    Units.ne_zero _
  have h := isOpen_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem coe_integers_eq :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = {x | Valued.v x ≤ WithZero.exp 0} := by
  ext x
  rw [WithZero.exp_zero]
  exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v

theorem isCompact_ball_zero : IsCompact {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp 0} := by
  rw [← coe_integers_eq]
  exact isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)

theorem isCompact_ball (k : ℤ) : IsCompact {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by

  set t : v.adicCompletion K := ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K)
    with ht
  have ht0 : t ≠ 0 := Units.ne_zero _
  have hvt : Valued.v t = WithZero.exp k := by rw [ht, valued_uniformizerUnit_zpow, neg_neg]
  have himage : {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (fun y => t * y) '' {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hx
      refine ⟨t⁻¹ * x, ?_, by rw [← mul_assoc, mul_inv_cancel₀ ht0, one_mul]⟩
      rw [map_mul, map_inv₀, hvt, WithZero.exp_zero]
      have hk0 : (WithZero.exp k : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
      calc (WithZero.exp k)⁻¹ * Valued.v x ≤ (WithZero.exp k)⁻¹ * WithZero.exp k :=
            mul_le_mul_right hx _
        _ = 1 := inv_mul_cancel₀ hk0
    · rintro ⟨y, hy, rfl⟩
      rw [map_mul, hvt, WithZero.exp_zero] at *
      calc WithZero.exp k * Valued.v y ≤ WithZero.exp k * 1 := mul_le_mul_right hy _
        _ = WithZero.exp k := mul_one _
  rw [himage]
  exact (isCompact_ball_zero v).image (continuous_const.mul continuous_id)

theorem continuous_addChar_of_level (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
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

theorem units_set_eq_diff :
    {u : v.adicCompletion K | Valued.v u = 1}
      = {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (0 : ℤ)}
          \ {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(1 : ℤ))} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · intro hy
    refine ⟨by rw [hy, WithZero.exp_zero], fun h => ?_⟩
    rw [hy, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega
  · rintro ⟨h1, h2⟩
    have hne : Valued.v y ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hne).symm⟩
    rw [hm, WithZero.exp_le_exp] at h1 h2
    rw [hm, ← WithZero.exp_zero]
    congr 1
    omega

theorem isClosed_units_set : IsClosed {u : v.adicCompletion K | Valued.v u = 1} := by
  rw [units_set_eq_diff]
  exact (isClosed_ball v _).sdiff (isOpen_ball v _)

theorem isOpen_units_set : IsOpen {u : v.adicCompletion K | Valued.v u = 1} := by
  rw [units_set_eq_diff]
  exact (isOpen_ball v _).sdiff (isClosed_ball v _)

theorem units_set_subset_ball_zero :
    {u : v.adicCompletion K | Valued.v u = 1} ⊆ {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp 0} := by
  intro u hu
  have hu' : Valued.v u = 1 := hu
  show Valued.v u ≤ WithZero.exp 0
  rw [hu', WithZero.exp_zero]

theorem isCompact_units_set : IsCompact {u : v.adicCompletion K | Valued.v u = 1} :=
  (isCompact_ball_zero v).of_isClosed_subset (isClosed_units_set v) (units_set_subset_ball_zero v)

theorem measurableSet_units_set [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] :
    MeasurableSet {u : v.adicCompletion K | Valued.v u = 1} :=
  (isClosed_units_set v).measurableSet

theorem ne_zero_of_valued_eq_one {u : v.adicCompletion K} (hu : Valued.v u = 1) : u ≠ 0 :=
  (Valuation.ne_zero_iff _).mp (by rw [hu]; exact one_ne_zero)

theorem valued_eq_one_of_valued_sub_one_le {x : v.adicCompletion K} {m : ℕ} (hm : 1 ≤ m)
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-(m : ℤ))) : Valued.v x = 1 := by
  have hlt : Valued.v (x - 1) < Valued.v (1 : v.adicCompletion K) := by
    rw [map_one, ← WithZero.exp_zero]
    exact hx.trans_lt (WithZero.exp_lt_exp.mpr (by omega))
  have h := Valuation.map_eq_of_sub_lt _ hlt
  rw [map_one] at h
  exact h

theorem mem_higherUnitsAt_of_valued_sub_one_le {u : (v.adicCompletion K)ˣ} {m : ℕ} (hm : 1 ≤ m)
    (hu : Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(m : ℤ))) :
    u ∈ higherUnitsAt K v m :=
  (mem_higherUnitsAt_iff K v).mpr ⟨valued_eq_one_of_valued_sub_one_le v hm hu, Or.inr hu⟩

theorem exp_mul_le_iff {k m r : ℤ} (hr : k + r = m) (X : WithZero (Multiplicative ℤ)) :
    WithZero.exp k * X ≤ WithZero.exp m ↔ X ≤ WithZero.exp r := by
  by_cases hX : X = 0
  · subst hX
    rw [mul_zero]
    exact ⟨fun _ => zero_le', fun _ => zero_le'⟩
  · obtain ⟨j, rfl⟩ : ∃ j : ℤ, X = WithZero.exp j := ⟨_, (WithZero.exp_log hX).symm⟩
    rw [← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]
    omega

theorem exp_mul_lt_iff {k m r : ℤ} (hr : k + r = m) (X : WithZero (Multiplicative ℤ)) :
    WithZero.exp m < WithZero.exp k * X ↔ WithZero.exp r < X := by
  rw [← not_le, ← not_le, exp_mul_le_iff hr]

theorem charExt_eq_of_valued_sub_le {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
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

theorem continuousOn_charExt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
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

theorem continuousOn_charExt_units_set {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt K v a, χ u = 1) :
    ContinuousOn (charExt χ) {u : v.adicCompletion K | Valued.v u = 1} :=
  (continuousOn_charExt v hχ).mono fun _ hu => ne_zero_of_valued_eq_one v hu

theorem continuousOn_units_of_invariant (f : v.adicCompletion K → ℂ) (m : ℕ)
    (hf : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ∀ w ∈ higherUnitsAt K v m, f ((u : v.adicCompletion K) * w) = f u) :
    ContinuousOn f {u : v.adicCompletion K | Valued.v u = 1} := by
  intro y₀ hy₀
  have hy₀1 : Valued.v y₀ = 1 := hy₀
  have hy₀0 : y₀ ≠ 0 := ne_zero_of_valued_eq_one v hy₀1

  set t : v.adicCompletion K :=
    ((uniformizerUnit K v ^ ((m + 1 : ℕ) : ℤ) : (v.adicCompletion K)ˣ) : v.adicCompletion K) with ht
  have ht0 : t ≠ 0 := Units.ne_zero _
  have hvt : Valued.v t = WithZero.exp (-((m + 1 : ℕ) : ℤ)) := by
    rw [ht, valued_uniformizerUnit_zpow]
  have hmem : (fun y => y - y₀) ⁻¹' {h : v.adicCompletion K | Valued.v h ≤ Valued.v t} ∈ nhds y₀ := by
    refine ((isOpen_setOf_valued_le v t ht0).preimage (continuous_id.sub continuous_const)).mem_nhds ?_
    show Valued.v (y₀ - y₀) ≤ Valued.v t
    rw [sub_self, map_zero]
    exact zero_le'
  have hev : f =ᶠ[nhdsWithin y₀ {u : v.adicCompletion K | Valued.v u = 1}] fun _ => f y₀ := by
    refine Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds hmem) fun y hy => ?_
    have hy' : Valued.v (y - y₀) ≤ WithZero.exp (-((m + 1 : ℕ) : ℤ)) := by rw [← hvt]; exact hy

    have hw1 : Valued.v (y * y₀⁻¹ - 1) ≤ WithZero.exp (-((m + 1 : ℕ) : ℤ)) := by
      have : y * y₀⁻¹ - 1 = y₀⁻¹ * (y - y₀) := by field_simp
      rw [this, map_mul, map_inv₀, hy₀1, inv_one, one_mul]
      exact hy'
    have hwval : Valued.v (y * y₀⁻¹) = 1 :=
      valued_eq_one_of_valued_sub_one_le v (m := m + 1) (by omega) hw1
    have hw0 : y * y₀⁻¹ ≠ 0 := ne_zero_of_valued_eq_one v hwval
    have hwmem : Units.mk0 (y * y₀⁻¹) hw0 ∈ higherUnitsAt K v m := by
      refine (mem_higherUnitsAt_iff K v).mpr ⟨by rw [Units.val_mk0]; exact hwval, ?_⟩
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · exact Or.inl h0
      · right
        rw [Units.val_mk0]
        exact hw1.trans (WithZero.exp_le_exp.mpr (by push_cast; omega))
    have key := hf (Units.mk0 y₀ hy₀0) (by rw [Units.val_mk0]; exact hy₀1) _ hwmem
    rw [Units.val_mk0, Units.val_mk0, mul_comm y, ← mul_assoc, mul_inv_cancel₀ hy₀0, one_mul] at key
    exact key
  exact (continuousWithinAt_const.congr_of_eventuallyEq hev (by simp : f y₀ = (fun _ => f y₀) y₀))

theorem setIntegral_ball_addChar [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1) (m : ℤ)
    (x : v.adicCompletion K) :
    ∫ y in {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-m)}, ψ (y * x) ∂μ
      = if Valued.v x ≤ WithZero.exp (n + m)
          then ((μ.real {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-m)} : ℝ) : ℂ) else 0 := by
  have h := tateFourier_indicator_setOf_valued_sub_le K v μ ψ n hψn hψn' 0 m x
  simp only [sub_zero, zero_mul, AddChar.map_zero_eq_one, one_mul] at h
  rw [tateFourier_indicator_one ψ μ (isClosed_ball v (-m)).measurableSet x] at h
  rw [h]
  by_cases hx : Valued.v x ≤ WithZero.exp (n + m) <;>
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hx, ite_true, ite_false, mul_one, mul_zero]

end Kv

section Main

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
  (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
  (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
  (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a h : ℕ) (hh : 1 ≤ h) (hah : a ≤ 2 * h)
  (hχa : ∀ u ∈ higherUnitsAt K v a, χ u = 1)
  (c : v.adicCompletion K)
  (hc : ∀ u ∈ higherUnitsAt K v h, ((χ u : ℂˣ) : ℂ) = ψ (c * ((u : v.adicCompletion K) - 1)))
  (z : v.adicCompletion K) (hz : Valued.v z = WithZero.exp (n + a))

def badSet : Set (v.adicCompletion K) :=
  {u : v.adicCompletion K | Valued.v u = 1 ∧ WithZero.exp (n + h) < Valued.v (z * u + c)}

def goodSet : Set (v.adicCompletion K) :=
  {u : v.adicCompletion K | Valued.v u = 1 ∧ Valued.v (z * u + c) ≤ WithZero.exp (n + h)}

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem badSet_subset_units : badSet v n h c z ⊆ {u : v.adicCompletion K | Valued.v u = 1} :=
  fun _ hu => hu.1

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem goodSet_subset_units : goodSet v n h c z ⊆ {u : v.adicCompletion K | Valued.v u = 1} :=
  fun _ hu => hu.1

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem units_eq_goodSet_union_badSet :
    {u : v.adicCompletion K | Valued.v u = 1} = goodSet v n h c z ∪ badSet v n h c z := by
  ext u
  simp only [goodSet, badSet, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro hu
    by_cases hle : Valued.v (z * u + c) ≤ WithZero.exp (n + h)
    · exact Or.inl ⟨hu, hle⟩
    · exact Or.inr ⟨hu, not_le.mp hle⟩
  · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem disjoint_goodSet_badSet : Disjoint (goodSet v n h c z) (badSet v n h c z) := by
  rw [Set.disjoint_left]
  rintro u ⟨_, hle⟩ ⟨_, hlt⟩
  exact absurd hle (not_le.mpr hlt)

theorem measurableSet_badSet : MeasurableSet (badSet v n h c z) := by
  have hcont : Continuous fun u : v.adicCompletion K => z * u + c := (continuous_const.mul continuous_id).add
    continuous_const
  have : badSet v n h c z = {u : v.adicCompletion K | Valued.v u = 1} ∩
      (fun u => z * u + c) ⁻¹' ({y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (n + h)}ᶜ) := by
    ext u
    simp only [badSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, not_le]
  rw [this]
  exact (measurableSet_units_set v).inter ((isClosed_ball v _).measurableSet.compl.preimage hcont.measurable)

theorem measurableSet_goodSet : MeasurableSet (goodSet v n h c z) := by
  have hcont : Continuous fun u : v.adicCompletion K => z * u + c := (continuous_const.mul continuous_id).add
    continuous_const
  have : goodSet v n h c z = {u : v.adicCompletion K | Valued.v u = 1} ∩
      (fun u => z * u + c) ⁻¹' {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (n + h)} := by
    ext u
    simp only [goodSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  rw [this]
  exact (measurableSet_units_set v).inter ((isClosed_ball v _).measurableSet.preimage hcont.measurable)

include hz hah in
omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in

theorem valued_mul_mul_le {u x : v.adicCompletion K} (hu : Valued.v u = 1)
    (hx : Valued.v x ≤ WithZero.exp (-(h : ℤ))) :
    Valued.v (z * u * x) ≤ WithZero.exp (n + h) := by
  rw [map_mul, map_mul, hz, hu, mul_one]
  calc WithZero.exp (n + a) * Valued.v x ≤ WithZero.exp (n + a) * WithZero.exp (-(h : ℤ)) :=
        mul_le_mul_right hx _
    _ = WithZero.exp (n + a + -(h : ℤ)) := (WithZero.exp_add _ _).symm
    _ ≤ WithZero.exp (n + h) := WithZero.exp_le_exp.mpr (by omega)

include hz hah hh in
omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in

theorem mul_mem_badSet_iff {x : v.adicCompletion K} (hx : Valued.v x ≤ WithZero.exp (-(h : ℤ)))
    (u : v.adicCompletion K) : (1 + x) * u ∈ badSet v n h c z ↔ u ∈ badSet v n h c z := by
  have hw : Valued.v (1 + x) = 1 := by
    have : Valued.v (1 + x - 1) ≤ WithZero.exp (-(h : ℤ)) := by rw [add_sub_cancel_left]; exact hx
    exact valued_eq_one_of_valued_sub_one_le v hh this
  simp only [badSet, Set.mem_setOf_eq, map_mul, hw, one_mul]
  constructor
  · rintro ⟨hu, hlt⟩
    refine ⟨hu, ?_⟩

    have hsmall := valued_mul_mul_le v n a h hah z hz hu hx
    by_contra hle
    rw [not_lt] at hle
    have : Valued.v (z * ((1 + x) * u) + c) ≤ WithZero.exp (n + h) := by
      have heq : z * ((1 + x) * u) + c = (z * u + c) + z * u * x := by ring
      rw [heq]
      exact (Valuation.map_add _ _ _).trans (max_le hle hsmall)
    exact absurd this (not_le.mpr hlt)
  · rintro ⟨hu, hlt⟩
    refine ⟨hu, ?_⟩
    have hsmall := valued_mul_mul_le v n a h hah z hz hu hx
    by_contra hle
    rw [not_lt] at hle
    have : Valued.v (z * u + c) ≤ WithZero.exp (n + h) := by
      have heq : z * u + c = (z * ((1 + x) * u) + c) + -(z * u * x) := by ring
      rw [heq]
      refine (Valuation.map_add _ _ _).trans (max_le hle ?_)
      rw [Valuation.map_neg]
      exact hsmall
    exact absurd this (not_le.mpr hlt)

variable (f : v.adicCompletion K → ℂ)
  (hfh : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ∀ w ∈ higherUnitsAt K v h, f ((u : v.adicCompletion K) * w) = f u)

def integrand (u : v.adicCompletion K) : ℂ := ψ (z * u) * f u * charExt χ u

include hψn hχa hfh in
theorem continuousOn_integrand :
    ContinuousOn (integrand v ψ χ z f) {u : v.adicCompletion K | Valued.v u = 1} := by
  have hψc : Continuous ψ := continuous_addChar_of_level v ψ n hψn
  refine ContinuousOn.mul (ContinuousOn.mul ?_ (continuousOn_units_of_invariant v f h hfh)) ?_
  · exact (hψc.comp (continuous_const.mul continuous_id)).continuousOn
  · exact continuousOn_charExt_units_set v hχa

include hψn hχa hfh hc hh in

theorem integrand_mul_shift {x : v.adicCompletion K} (hx : Valued.v x ≤ WithZero.exp (-(h : ℤ)))
    {u : v.adicCompletion K} (hu : Valued.v u = 1) :
    integrand v ψ χ z f ((1 + x) * u) = integrand v ψ χ z f u * ψ ((z * u + c) * x) := by
  have hw1 : Valued.v (1 + x - 1) ≤ WithZero.exp (-(h : ℤ)) := by rw [add_sub_cancel_left]; exact hx
  have hwval : Valued.v (1 + x) = 1 := valued_eq_one_of_valued_sub_one_le v hh hw1
  have hw0 : (1 + x : v.adicCompletion K) ≠ 0 := ne_zero_of_valued_eq_one v hwval
  set w : (v.adicCompletion K)ˣ := Units.mk0 (1 + x) hw0 with hwdef
  have hwmem : w ∈ higherUnitsAt K v h :=
    mem_higherUnitsAt_of_valued_sub_one_le v hh (by rw [hwdef, Units.val_mk0]; exact hw1)
  have hu0 : u ≠ 0 := ne_zero_of_valued_eq_one v hu

  have hf' : f ((1 + x) * u) = f u := by
    have := hfh (Units.mk0 u hu0) (by rw [Units.val_mk0]; exact hu) w hwmem
    rw [Units.val_mk0, hwdef, Units.val_mk0, mul_comm] at this
    exact this

  have hχ' : charExt χ ((1 + x) * u) = ψ (c * x) * charExt χ u := by
    have h1 : charExt χ ((1 + x) * u) = (χ w : ℂ) * charExt χ u := by
      rw [show (1 + x) * u = (w : v.adicCompletion K) * u by rw [hwdef, Units.val_mk0]]
      exact charExt_units_mul χ w u
    rw [h1, hc w hwmem, hwdef, Units.val_mk0, add_sub_cancel_left]

  have hψ' : ψ (z * ((1 + x) * u)) = ψ (z * u) * ψ (z * u * x) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hψ2 : ψ ((z * u + c) * x) = ψ (z * u * x) * ψ (c * x) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [integrand]
  rw [hf', hχ', hψ', hψ2]
  ring

def hBall : Set (v.adicCompletion K) := {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-(h : ℤ))}

theorem measurableSet_hBall : MeasurableSet (hBall v h) := (isClosed_ball v _).measurableSet

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem isCompact_hBall : IsCompact (hBall v h) := isCompact_ball v _

theorem measureReal_hBall_pos : 0 < μ.real (hBall v h) := by
  refine lt_of_le_of_ne measureReal_nonneg (Ne.symm ?_)
  refine (measureReal_ne_zero_iff (isCompact_hBall v h).measure_lt_top.ne).mpr ?_
  refine ((isOpen_ball v _).measure_pos μ ⟨0, ?_⟩).ne'
  show Valued.v (0 : v.adicCompletion K) ≤ WithZero.exp (-(h : ℤ))
  rw [map_zero]
  exact zero_le'

include hψn hψn' in

theorem setIntegral_hBall_eq_zero {u : v.adicCompletion K} (hu : u ∈ badSet v n h c z) :
    ∫ x in hBall v h, ψ ((z * u + c) * x) ∂μ = 0 := by
  have hcomm : (fun x => ψ ((z * u + c) * x)) = fun x => ψ (x * (z * u + c)) := by
    funext x; rw [mul_comm]
  rw [hcomm]
  show ∫ x in {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-(h : ℤ))}, ψ (x * (z * u + c)) ∂μ = 0
  rw [setIntegral_ball_addChar v μ ψ n hψn hψn' (h : ℤ) (z * u + c), if_neg (not_le.mpr hu.2)]

include hψn hψn' hh hah hχa hc hz hfh in

theorem setIntegral_badSet_eq_zero : ∫ u in badSet v n h c z, integrand v ψ χ z f u ∂μ = 0 := by
  haveI : SecondCountableTopology (v.adicCompletion K) := UniformSpace.secondCountable_of_separable _
  have hψc : Continuous ψ := continuous_addChar_of_level v ψ n hψn
  set S := badSet v n h c z with hSdef
  set B := hBall v h with hBdef
  have hSm : MeasurableSet S := measurableSet_badSet v n h c z
  have hBm : MeasurableSet B := measurableSet_hBall v h
  set F : v.adicCompletion K → ℂ := integrand v ψ χ z f with hFdef

  have hshift : ∀ x ∈ B, ∫ u in S, F u ∂μ = ∫ u in S, F u * ψ ((z * u + c) * x) ∂μ := by
    intro x hx
    have hx' : Valued.v x ≤ WithZero.exp (-(h : ℤ)) := hx
    have hw1 : Valued.v (1 + x - 1) ≤ WithZero.exp (-(h : ℤ)) := by rw [add_sub_cancel_left]; exact hx'
    have hwval : Valued.v (1 + x) = 1 := valued_eq_one_of_valued_sub_one_le v hh hw1
    have hw0 : (1 + x : v.adicCompletion K) ≠ 0 := ne_zero_of_valued_eq_one v hwval
    set w : (v.adicCompletion K)ˣ := Units.mk0 (1 + x) hw0 with hwdef
    have hmod : modulus (w : v.adicCompletion K) = 1 := by
      rw [hwdef, Units.val_mk0]; exact modulus_eq_one_of_valued v hwval
    rw [setIntegral_comp_mul_left_of_modulus_eq_one μ hmod F hSm]
    have hpre : (fun y => (w : v.adicCompletion K) * y) ⁻¹' S = S := by
      ext u
      simp only [Set.mem_preimage, hwdef, Units.val_mk0]
      exact mul_mem_badSet_iff v n a h hh hah c z hz hx' u
    rw [hpre]
    refine setIntegral_congr_fun hSm fun u hu => ?_
    show F ((w : v.adicCompletion K) * u) = F u * ψ ((z * u + c) * x)
    rw [hwdef, Units.val_mk0]
    exact integrand_mul_shift v ψ n hψn χ a h hh hχa c hc z f hfh hx' hu.1

  have hFcont : ContinuousOn F {u : v.adicCompletion K | Valued.v u = 1} :=
    continuousOn_integrand v ψ n hψn χ a h hχa z f hfh
  have hG : Integrable (Function.uncurry fun (x u : v.adicCompletion K) => F u * ψ ((z * u + c) * x))
      ((μ.restrict B).prod (μ.restrict S)) := by
    rw [Measure.prod_restrict]
    have hK : IsCompact (B ×ˢ {u : v.adicCompletion K | Valued.v u = 1}) :=
      (isCompact_hBall v h).prod (isCompact_units_set v)
    have hcont : ContinuousOn (Function.uncurry fun (x u : v.adicCompletion K) => F u * ψ ((z * u + c) * x))
        (B ×ˢ {u : v.adicCompletion K | Valued.v u = 1}) := by
      refine ContinuousOn.mul ?_ ?_
      · exact hFcont.comp continuous_snd.continuousOn fun p hp => hp.2
      · exact (hψc.comp (((continuous_const.mul continuous_snd).add continuous_const).mul
          continuous_fst)).continuousOn
    exact (hcont.integrableOn_compact hK).mono_set (Set.prod_mono le_rfl (badSet_subset_units v n h c z))
  have hswap := integral_integral_swap hG

  have hlhs : ∫ x in B, (∫ u in S, F u * ψ ((z * u + c) * x) ∂μ) ∂μ = (μ.real B : ℂ) * ∫ u in S, F u ∂μ := by
    rw [setIntegral_congr_fun hBm fun x hx => (hshift x hx).symm, setIntegral_const, Complex.real_smul]
  have hrhs : ∫ u in S, (∫ x in B, F u * ψ ((z * u + c) * x) ∂μ) ∂μ = 0 := by
    refine (setIntegral_congr_fun hSm fun u hu => ?_).trans (integral_zero _ _)
    show ∫ x in B, F u * ψ ((z * u + c) * x) ∂μ = 0
    rw [integral_const_mul, setIntegral_hBall_eq_zero v μ ψ n hψn hψn' h c z hu, mul_zero]
  have hswap' : ∫ x in B, (∫ u in S, F u * ψ ((z * u + c) * x) ∂μ) ∂μ
      = ∫ u in S, (∫ x in B, F u * ψ ((z * u + c) * x) ∂μ) ∂μ := hswap
  rw [hlhs, hrhs] at hswap'
  have hB0 : (μ.real B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_hBall_pos v μ h).ne'
  exact (mul_eq_zero.mp hswap').resolve_left hB0

end Main

end LanglandsTunnell.TateLocal.DeligneLocalization

end

open MeasureTheory IsDedekindDomain NumberField _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt.LanglandsTunnell.TateLocal LanglandsTunnell.TateLocal.DeligneLocalization in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a h : ℕ) (hh : 1 ≤ h) (hah : a ≤ 2 * h)
    (hχa : ∀ u ∈ higherUnitsAt K v a, χ u = 1)
    (c : v.adicCompletion K)
    (hc : ∀ u ∈ higherUnitsAt K v h, ((χ u : ℂˣ) : ℂ) = ψ (c * ((u : v.adicCompletion K) - 1)))
    (z : v.adicCompletion K) (hz : Valued.v z = WithZero.exp (n + a))
    (f : v.adicCompletion K → ℂ)
    (hf : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ∀ w ∈ higherUnitsAt K v (a - h), f ((u : v.adicCompletion K) * w) = f u) :
    (∀ u₁ : v.adicCompletion K, Valued.v u₁ = 1 → Valued.v (z * u₁ + c) ≤ WithZero.exp (n + h) →
      (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (z * u) * f u * charExt χ u ∂μ) =
        f u₁ * ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (z * u) * charExt χ u ∂μ) ∧
    ((∀ u : v.adicCompletion K, Valued.v u = 1 → WithZero.exp (n + h) < Valued.v (z * u + c)) →
      (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (z * u) * f u * charExt χ u ∂μ) = 0) := by

  have hah' : a - h ≤ h := by omega
  have hfh : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ∀ w ∈ higherUnitsAt K v h, f ((u : v.adicCompletion K) * w) = f u :=
    fun u hu w hw => hf u hu w (higherUnitsAt_antitone K v hah' hw)
  have h1h : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ∀ w ∈ higherUnitsAt K v h, (fun _ => (1 : ℂ)) ((u : v.adicCompletion K) * w) = (fun _ => (1 : ℂ)) u :=
    fun _ _ _ _ => rfl

  have hbadf := setIntegral_badSet_eq_zero v μ ψ n hψn hψn' χ a h hh hah hχa c hc z hz f hfh
  have hbad1 := setIntegral_badSet_eq_zero v μ ψ n hψn hψn' χ a h hh hah hχa c hc z hz (fun _ => (1 : ℂ)) h1h
  have hU := units_eq_goodSet_union_badSet v n h c z
  have hSm := measurableSet_badSet v n h c z
  have hGm := measurableSet_goodSet v n h c z
  have hdisj := disjoint_goodSet_badSet v n h c z

  have hintF : IntegrableOn (integrand v ψ χ z f) {u : v.adicCompletion K | Valued.v u = 1} μ :=
    (continuousOn_integrand v ψ n hψn χ a h hχa z f hfh).integrableOn_compact (isCompact_units_set v)
  have hint1 : IntegrableOn (integrand v ψ χ z fun _ => (1 : ℂ)) {u : v.adicCompletion K | Valued.v u = 1} μ :=
    (continuousOn_integrand v ψ n hψn χ a h hχa z (fun _ => (1 : ℂ)) h1h).integrableOn_compact
      (isCompact_units_set v)

  have hsplitF : ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, integrand v ψ χ z f u ∂μ
      = ∫ u in goodSet v n h c z, integrand v ψ χ z f u ∂μ := by
    rw [hU, setIntegral_union hdisj hSm (hintF.mono_set (hU ▸ Set.subset_union_left))
      (hintF.mono_set (hU ▸ Set.subset_union_right)), hbadf, add_zero]
  have hsplit1 : ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, integrand v ψ χ z (fun _ => (1 : ℂ)) u ∂μ
      = ∫ u in goodSet v n h c z, integrand v ψ χ z (fun _ => (1 : ℂ)) u ∂μ := by
    rw [hU, setIntegral_union hdisj hSm (hint1.mono_set (hU ▸ Set.subset_union_left))
      (hint1.mono_set (hU ▸ Set.subset_union_right)), hbad1, add_zero]
  have hF : (fun u => ψ (z * u) * f u * charExt χ u) = integrand v ψ χ z f := rfl
  have hF1 : (fun u => ψ (z * u) * charExt χ u) = integrand v ψ χ z fun _ => (1 : ℂ) := by
    funext u; simp [integrand]
  refine ⟨fun u₁ hu₁ hgood => ?_, fun hall => ?_⟩
  ·
    rw [hF, hF1, hsplitF, hsplit1, ← integral_const_mul]
    refine setIntegral_congr_fun hGm fun u hu => ?_
    obtain ⟨hu1, hule⟩ := hu
    have hu0 : u ≠ 0 := ne_zero_of_valued_eq_one v hu1
    have hu₁0 : u₁ ≠ 0 := ne_zero_of_valued_eq_one v hu₁

    have hz0 : Valued.v z ≠ 0 := by rw [hz]; exact WithZero.exp_ne_zero
    have hdiff : Valued.v (z * (u - u₁)) ≤ WithZero.exp (n + h) := by
      have : z * (u - u₁) = (z * u + c) + -(z * u₁ + c) := by ring
      rw [this]
      refine (Valuation.map_add _ _ _).trans (max_le hule ?_)
      rw [Valuation.map_neg]; exact hgood
    have hwval : Valued.v (u * u₁⁻¹) = 1 := by rw [map_mul, map_inv₀, hu1, hu₁, inv_one, mul_one]
    have hw0 : u * u₁⁻¹ ≠ 0 := ne_zero_of_valued_eq_one v hwval
    have hwmem : Units.mk0 (u * u₁⁻¹) hw0 ∈ higherUnitsAt K v (a - h) := by
      refine (mem_higherUnitsAt_iff K v).mpr ⟨by rw [Units.val_mk0]; exact hwval, ?_⟩
      rcases Nat.eq_zero_or_pos (a - h) with h0 | hpos
      · exact Or.inl h0
      · refine Or.inr ?_
        rw [Units.val_mk0]
        have heq : u * u₁⁻¹ - 1 = u₁⁻¹ * (u - u₁) := by field_simp
        rw [heq, map_mul, map_inv₀, hu₁, inv_one, one_mul]
        rw [map_mul, hz] at hdiff
        have h' := (exp_mul_le_iff (k := n + a) (m := n + h) (r := (h : ℤ) - a) (by omega) _).mp hdiff
        refine h'.trans (WithZero.exp_le_exp.mpr ?_)
        have : ((a - h : ℕ) : ℤ) = (a : ℤ) - h := by omega
        omega
    have key := hf (Units.mk0 u₁ hu₁0) (by rw [Units.val_mk0]; exact hu₁) _ hwmem
    rw [Units.val_mk0, Units.val_mk0, mul_comm u, ← mul_assoc, mul_inv_cancel₀ hu₁0, one_mul] at key
    simp only [integrand, key]
    ring
  ·
    have hgood_empty : goodSet v n h c z = ∅ := by
      ext u
      simp only [goodSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      exact fun hu => hall u hu
    rw [hF, hsplitF, hgood_empty, Measure.restrict_empty, integral_zero_measure]

end S_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt (solution)
