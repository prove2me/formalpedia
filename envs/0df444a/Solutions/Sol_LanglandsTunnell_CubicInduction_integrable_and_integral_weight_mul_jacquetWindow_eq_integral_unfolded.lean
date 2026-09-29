-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b14039a6-1c27-5bbe-99d8-e0219dc843d7

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_coupledIntegrand
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

section Part2

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt modulus modulus_of_ne_zero modulus_pos modulus_ne_zero modulus_mul charExt charExt_zero charExt_of_ne_zero charExt_coe_units mulMeasure modulus_adicCompletion_eq_nnnorm integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

section Scaling

private theorem modulus_coe_units_eq (u : (v.adicCompletion K)ˣ) :
    modulus (u : v.adicCompletion K) = distribHaarChar (v.adicCompletion K) u := by
  rw [modulus_of_ne_zero u.ne_zero, Units.mk0_val]

private theorem charExt_mul (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a b : v.adicCompletion K) :
    charExt χ (a * b) = charExt χ a * charExt χ b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [charExt_of_ne_zero χ (mul_ne_zero ha hb), charExt_of_ne_zero χ ha, charExt_of_ne_zero χ hb,
    ← Units.val_mul, ← map_mul]
  congr 2
  exact Units.ext (by simp)

private theorem selfDualHaarAt_smul_set (u : (v.adicCompletion K)ˣ) (S : Set (v.adicCompletion K)) :
    letI := localBorel K v
    selfDualHaarAt K v (u • S) = (modulus (u : v.adicCompletion K) : ℝ≥0∞) * selfDualHaarAt K v S := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  rw [modulus_coe_units_eq]
  unfold selfDualHaarAt
  simp only [Measure.smul_apply]
  rw [← distribHaarChar_mul (Measure.addHaarMeasure (integersPositiveCompacts K v)) u S]
  exact (mul_smul_comm _ _ _).symm

private theorem map_mul_left_selfDualHaarAt (u : (v.adicCompletion K)ˣ) :
    letI := localBorel K v
    Measure.map (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) (selfDualHaarAt K v) =
      (modulus (u : v.adicCompletion K) : ℝ≥0∞)⁻¹ • selfDualHaarAt K v := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hmul : Measurable fun x : v.adicCompletion K => (u : v.adicCompletion K) * x := measurable_id.const_mul _
  ext S hS
  rw [Measure.map_apply hmul hS, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) ⁻¹' S = u⁻¹ • S :=
    Set.preimage_smul u S
  rw [hpre, selfDualHaarAt_smul_set, modulus_coe_units_eq, modulus_coe_units_eq, map_inv,
    ENNReal.coe_inv (distribHaarChar_pos (A := v.adicCompletion K) (g := u)).ne']

private theorem lintegral_mul_left_selfDualHaarAt (u : (v.adicCompletion K)ˣ) (g : v.adicCompletion K → ℝ≥0∞) :
    letI := localBorel K v
    ∫⁻ x, g ((u : v.adicCompletion K) * x) ∂(selfDualHaarAt K v) =
      (modulus (u : v.adicCompletion K) : ℝ≥0∞)⁻¹ * ∫⁻ x, g x ∂(selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  rw [← (measurableEmbedding_mulLeft₀ u.ne_zero).lintegral_map g, map_mul_left_selfDualHaarAt]
  simp only [lintegral_smul_measure, smul_eq_mul]

private theorem map_mul_left_mulMeasure (u : (v.adicCompletion K)ˣ) :
    letI := localBorel K v
    Measure.map (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) (mulMeasure (selfDualHaarAt K v)) =
      mulMeasure (selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hc : MeasurableSet ({0}ᶜ : Set (v.adicCompletion K)) := isClosed_singleton.measurableSet.compl
  have hmul : Measurable fun x : v.adicCompletion K => (u : v.adicCompletion K) * x := measurable_id.const_mul _
  ext S hS
  rw [Measure.map_apply hmul hS]
  unfold mulMeasure
  rw [withDensity_apply _ (hmul hS), withDensity_apply _ hS, Measure.restrict_restrict (hmul hS),
    Measure.restrict_restrict hS, ← lintegral_indicator (hmul hS |>.inter hc), ← lintegral_indicator (hS.inter hc)]
  have hpt : ∀ x : v.adicCompletion K,
      ((fun y => (u : v.adicCompletion K) * y) ⁻¹' S ∩ {0}ᶜ).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) x =
        (modulus (u : v.adicCompletion K) : ℝ≥0∞) *
          (S ∩ {0}ᶜ).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) ((u : v.adicCompletion K) * x) := by
    intro x
    by_cases hx : (u : v.adicCompletion K) * x ∈ S ∩ {0}ᶜ
    · have hx' : x ∈ (fun y => (u : v.adicCompletion K) * y) ⁻¹' S ∩ {0}ᶜ := by
        refine ⟨hx.1, ?_⟩
        intro h0
        exact hx.2 (by simp [Set.mem_singleton_iff.mp h0])
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, modulus_mul, ENNReal.coe_mul,
        ENNReal.mul_inv (Or.inl (ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero))) (Or.inl ENNReal.coe_ne_top),
        ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero)) ENNReal.coe_ne_top,
        one_mul]
    · have hx' : x ∉ (fun y => (u : v.adicCompletion K) * y) ⁻¹' S ∩ {0}ᶜ := by
        intro h
        refine hx ⟨h.1, ?_⟩
        intro h0
        exact h.2 (by simp [mul_eq_zero, u.ne_zero] at h0; simp [h0])
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]
  simp only [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_mul_left_selfDualHaarAt,
    ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero)) ENNReal.coe_ne_top,
    one_mul]

end Scaling

section MeasureClasses

private theorem selfDualConst_ne_zero :
    ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (StandardAddChar.psiLocal K v) : ℝ) / 2)) ≠ 0 := by
  have hq : (0 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := by
    have h : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h
  exact (NNReal.rpow_pos hq).ne'

private theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul (Measure.addHaarMeasure (integersPositiveCompacts K v))
    (selfDualConst_ne_zero K v)

private theorem sFinite_selfDualHaarAt :
    letI := localBorel K v
    SFinite (selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  infer_instance

private theorem sFinite_mulMeasure_selfDualHaarAt :
    letI := localBorel K v
    SFinite (mulMeasure (selfDualHaarAt K v)) := by
  letI := localBorel K v
  haveI := sFinite_selfDualHaarAt K v
  unfold mulMeasure
  infer_instance

end MeasureClasses

end LanglandsTunnell.TateLocal
end Part2

section Part1

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal"
open scoped NNReal ENNReal

open Polynomial in
private def IsLaurentInQPow (q : ℂ) (P : ℂ → ℂ) : Prop :=
  ∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ, P s = Q.eval (q ^ (-s)) * q ^ ((m : ℂ) * s)

namespace IsLaurentInQPow

variable {q : ℂ}

private theorem mul (hq : q ≠ 0) {P₁ P₂ : ℂ → ℂ} (h₁ : IsLaurentInQPow q P₁) (h₂ : IsLaurentInQPow q P₂) :
    IsLaurentInQPow q fun s => P₁ s * P₂ s := by
  obtain ⟨Q₁, m₁, e₁⟩ := h₁
  obtain ⟨Q₂, m₂, e₂⟩ := h₂
  refine ⟨Q₁ * Q₂, m₁ + m₂, fun s => ?_⟩
  show P₁ s * P₂ s = _
  rw [e₁ s, e₂ s, Polynomial.eval_mul, Nat.cast_add, add_mul, Complex.cpow_add _ _ hq]
  ring

end IsLaurentInQPow

namespace LaurentZetaSlot

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem _root_.LaurentZetaSlot.absNorm_ne_zero : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by
  intro h0
  have h := one_lt_absNorm_real v
  rw [h0] at h
  norm_num at h

p2m_export "LaurentZetaSlot" "absNorm_ne_zero"
private def shell (j : ℤ) : Set (v.adicCompletion ℚ) := {x | Valued.v x = WithZero.exp (-j)}

private theorem modulus_eq_of_mem_shell {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) :
    modulus x = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-j) := by
  have hnorm : ‖x‖ = ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ≥0) : ℝ) :=
    FinitePlace.norm_def v x
  have hx' : Valued.v x = WithZero.exp (-j) := hx
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x]
  apply NNReal.coe_injective
  rw [coe_nnnorm, hnorm, hx', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have htoAdd : ∀ h : WithZero.exp (-j) ≠ (0 : WithZero (Multiplicative ℤ)),
      Multiplicative.toAdd (WithZero.unzero h) = -j := fun _ => rfl
  rw [htoAdd]

private def unitShell : Set (v.adicCompletion ℚ) := {x | Valued.v x = 1}

private theorem isAddHaarMeasure_selfDualHaarAt' : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  exact LanglandsTunnell.TateLocal.isAddHaarMeasure_selfDualHaarAt ℚ v

private theorem sFinite_mulMeasure_selfDualHaarAt' : SFinite (mulMeasure (selfDualHaarAt ℚ v)) := by
  exact LanglandsTunnell.TateLocal.sFinite_mulMeasure_selfDualHaarAt ℚ v

attribute [local instance] sFinite_mulMeasure_selfDualHaarAt'

private theorem continuousOn_charExt_compl (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ContinuousOn (charExt χ) ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hmk : Continuous fun x : ({0}ᶜ : Set (v.adicCompletion ℚ)) => Units.mk0 (x : v.adicCompletion ℚ) x.2 :=
    Units.isEmbedding_val₀.continuous_iff.mpr continuous_subtype_val
  have hlc : IsLocallyConstant fun x : ({0}ᶜ : Set (v.adicCompletion ℚ)) =>
      ((χ (Units.mk0 (x : v.adicCompletion ℚ) x.2) : ℂˣ) : ℂ) :=
    IsLocallyConstant.comp (IsLocallyConstant.comp_continuous hχ hmk) fun u : ℂˣ => (u : ℂ)
  refine (IsLocallyConstant.continuous hlc).congr fun x => ?_
  simp only [Set.restrict_apply, charExt_of_ne_zero χ x.2]

private theorem measurable_modulus : Measurable fun x : v.adicCompletion ℚ => (modulus x : ℝ) := by
  have h : (fun x : v.adicCompletion ℚ => (modulus x : ℝ)) = fun x => ‖x‖ := by
    funext x
    rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]
  rw [h]
  exact measurable_norm

private theorem measurable_modulus_cpow (s : ℂ) :
    Measurable fun x : v.adicCompletion ℚ => ((modulus x : ℝ) : ℂ) ^ s :=
  (Complex.measurable_ofReal.comp (measurable_modulus v)).pow_const s

private theorem measurable_charExt (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    Measurable (charExt χ) :=
  measurable_of_continuousOn_compl_singleton (0 : v.adicCompletion ℚ) (continuousOn_charExt_compl v χ hχ)

private theorem isClopen_shell (j : ℤ) : IsClopen (shell v j) := by
  obtain ⟨x₀, hx₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp (-j))
  have hset : shell v j = {x | Valued.v.restrict x = Valued.v.restrict x₀} := by
    ext x
    simp only [shell, Set.mem_setOf_eq, Valuation.restrict_inj, hx₀]
  have hne : Valued.v.restrict x₀ ≠ 0 := by
    intro h0
    have h1 : Valued.v x₀ = Valued.v (0 : v.adicCompletion ℚ) :=
      (Valuation.restrict_inj Valued.v).mp (by rw [h0, map_zero])
    rw [map_zero, hx₀] at h1
    exact WithZero.exp_ne_zero h1
  rw [hset]
  exact Valued.isClopen_sphere _ hne

private theorem unitShell_eq_shell_zero : unitShell v = shell v 0 := by
  simp only [unitShell, shell, neg_zero, WithZero.exp_zero]

private theorem modulus_eq_one_of_mem_unitShell {x : v.adicCompletion ℚ} (hx : x ∈ unitShell v) : modulus x = 1 := by
  rw [unitShell_eq_shell_zero] at hx
  rw [modulus_eq_of_mem_shell v hx, neg_zero, zpow_zero]

private theorem isClopen_unitShell : IsClopen (unitShell v) := by
  rw [unitShell_eq_shell_zero]
  exact isClopen_shell v 0

private theorem measurableSet_shell (j : ℤ) : MeasurableSet (shell v j) :=
  (isClopen_shell v j).isOpen.measurableSet

private theorem measurableSet_unitShell : MeasurableSet (unitShell v) :=
  (isClopen_unitShell v).isOpen.measurableSet

private theorem unitShell_subset_integers : unitShell v ⊆ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
  fun x hx => by
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact le_of_eq hx

private theorem isCompact_unitShell : IsCompact (unitShell v) := by
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← coe_integersPositiveCompacts ℚ v]
    exact (integersPositiveCompacts ℚ v).isCompact
  exact hO.of_isClosed_subset (isClopen_unitShell v).isClosed (unitShell_subset_integers v)

private theorem shell_subset_compl_zero (j : ℤ) : shell v j ⊆ ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
  intro x hx
  have hx' : Valued.v x = WithZero.exp (-j) := hx
  intro h0
  rw [Set.mem_singleton_iff.mp h0, map_zero] at hx'
  exact WithZero.exp_ne_zero hx'.symm

private theorem valued_uniformizerUnit_zpow (j : ℤ) :
    Valued.v ((uniformizerUnit ℚ v ^ j : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-j) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem image_unitShell_eq_shell (j : ℤ) :
    (fun x : v.adicCompletion ℚ => ((uniformizerUnit ℚ v ^ j : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) ''
      unitShell v = shell v j := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : Valued.v x = 1 := hx
    show Valued.v _ = WithZero.exp (-j)
    rw [map_mul, valued_uniformizerUnit_zpow, hx', mul_one]
  · intro hy
    have hy' : Valued.v y = WithZero.exp (-j) := hy
    refine ⟨((uniformizerUnit ℚ v ^ j : (v.adicCompletion ℚ)ˣ)⁻¹ : (v.adicCompletion ℚ)ˣ) * y, ?_, ?_⟩
    · show Valued.v _ = 1
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, valued_uniformizerUnit_zpow, hy']
      exact inv_mul_cancel₀ WithZero.exp_ne_zero
    · exact Units.mul_inv_cancel_left _ _

private theorem isCompact_shell (j : ℤ) : IsCompact (shell v j) := by
  rw [← image_unitShell_eq_shell]
  exact (isCompact_unitShell v).image (continuous_const.mul continuous_id)

private theorem
    mulMeasure_unitShell : mulMeasure (selfDualHaarAt ℚ v) (unitShell v) = selfDualHaarAt ℚ v (unitShell v) := by
  rw [mulMeasure, withDensity_apply _ (measurableSet_unitShell v),
    Measure.restrict_restrict (measurableSet_unitShell v)]
  have hsub : unitShell v ∩ {(0 : v.adicCompletion ℚ)}ᶜ = unitShell v := by
    refine Set.inter_eq_left.mpr fun x hx => ?_
    rintro rfl
    simp [unitShell] at hx
  rw [hsub]
  calc ∫⁻ x in unitShell v, ((modulus x : ℝ≥0∞))⁻¹ ∂(selfDualHaarAt ℚ v)
      = ∫⁻ _ in unitShell v, (1 : ℝ≥0∞) ∂(selfDualHaarAt ℚ v) := by
        refine setLIntegral_congr_fun (measurableSet_unitShell v) fun x hx => ?_
        rw [modulus_eq_one_of_mem_unitShell v hx]
        simp
    _ = selfDualHaarAt ℚ v (unitShell v) := by simp

private theorem mulMeasure_unitShell_lt_top : mulMeasure (selfDualHaarAt ℚ v) (unitShell v) < ⊤ := by
  haveI := isAddHaarMeasure_selfDualHaarAt' v
  rw [mulMeasure_unitShell]
  exact (isCompact_unitShell v).measure_lt_top

private scoped instance isFiniteMeasure_restrict_unitShell :
    IsFiniteMeasure ((mulMeasure (selfDualHaarAt ℚ v)).restrict (unitShell v)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact mulMeasure_unitShell_lt_top v⟩

private theorem charExt_ne_zero (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    charExt χ x ≠ 0 := by
  rw [charExt_of_ne_zero χ hx]
  exact Units.ne_zero _

private theorem exists_mem_shell {x : v.adicCompletion ℚ} (hx : x ≠ 0) : ∃ j : ℤ, x ∈ shell v j := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨-WithZero.log (Valued.v x), ?_⟩
  show Valued.v x = WithZero.exp (- -WithZero.log (Valued.v x))
  rw [neg_neg, WithZero.exp_log hv]

private theorem coe_modulus_eq_of_mem_shell {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) :
    (modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) := by
  rw [modulus_eq_of_mem_shell v hx, NNReal.coe_zpow, NNReal.coe_natCast]

private theorem exists_bound_charExt_unitShell (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ Mχ : ℝ, ∀ u ∈ unitShell v, ‖charExt χ u‖ ≤ Mχ :=
  (isCompact_unitShell v).exists_bound_of_continuousOn ((continuousOn_charExt_compl v χ hχ).mono
    (by rw [unitShell_eq_shell_zero]; exact shell_subset_compl_zero v 0))

end LaurentZetaSlot
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
end Part1
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

section Part3

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 integrable_coupledIntegrand"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TransposeInverse

variable {A : Type*} [CommRing A]

private theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change ((((g * h)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ =
    (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ * (((h⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem transposeInv3_one : transposeInv3 (1 : GL (Fin 3) A) = 1 := by
  refine Units.ext ?_
  change ((((1 : GL (Fin 3) A)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = ((1 : GL (Fin 3) A) : Matrix _ _ _)
  rw [inv_one, Units.val_one, Matrix.transpose_one]

private theorem coe_inv_diagUnitGL2 (a : Aˣ) :
    (((diagUnitGL2 a)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![((a⁻¹ : Aˣ) : A), 0; 0, 1] :=
  rfl

private theorem transposeInv3_iotaGL_diagUnitGL2 (a : Aˣ) :
    transposeInv3 (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 a⁻¹) := by
  refine Units.ext ?_
  change ((((iotaGL (diagUnitGL2 a))⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [← map_inv, coe_iotaGL, coe_iotaGL, coe_inv_diagUnitGL2, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

private theorem coe_longWeyl3_mul_transposeInv3_mul_longWeyl3 (a : Aˣ) (x : A) :
    ((longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
          longWeyl3 : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : Aˣ) : A) * x), 0, ((a⁻¹ : Aˣ) : A)] := by
  rw [transposeInv3_one, mul_one, transposeInv3_mul, transposeInv3_mul, transposeInv3_iotaGL_diagUnitGL2,
    transposeInv3_lowerUnipotent21, transposeInv3_weylPrime3]
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, longWeyl3_coe, weylPrime3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

end TransposeInverse
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem longWeyl3_eq_antidiagonal3 : (longWeyl3 : LocalGL3 v) = antidiagonal3 v :=
  Units.ext (longWeyl3_coe.trans (antidiagonal3_coe v).symm)

private theorem coe_dualPoint_mul_antidiagonal3 (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    ((longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
          antidiagonal3 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x), 0,
        ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)] := by
  rw [← longWeyl3_eq_antidiagonal3]
  exact coe_longWeyl3_mul_transposeInv3_mul_longWeyl3 a x

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
end Part3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

section Part4

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 integrable_coupledIntegrand"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section DualPoint

private noncomputable def
    dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    LocalGL3 v :=
  antidiagonal3 v * upperUnipotent3 α β γ *
    (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
      antidiagonal3 v)

private theorem dualCellPoint_coe (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    (dualCellPoint v α β γ a x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![-(x * (a : v.adicCompletion ℚ)⁻¹), 0, (a : v.adicCompletion ℚ)⁻¹;
        1 - β * (x * (a : v.adicCompletion ℚ)⁻¹), 0, β * (a : v.adicCompletion ℚ)⁻¹;
        α - γ * (x * (a : v.adicCompletion ℚ)⁻¹), 1, γ * (a : v.adicCompletion ℚ)⁻¹] := by
  rw [dualCellPoint, Units.val_mul, coe_dualPoint_mul_antidiagonal3, Units.val_mul, antidiagonal3_coe,
    upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem
    gl3Entry_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ)
    (i j : Fin 3) :
    gl3Entry v (dualCellPoint v α β γ a x) i j =
      !![-(x * (a : v.adicCompletion ℚ)⁻¹), 0, (a : v.adicCompletion ℚ)⁻¹;
        1 - β * (x * (a : v.adicCompletion ℚ)⁻¹), 0, β * (a : v.adicCompletion ℚ)⁻¹;
        α - γ * (x * (a : v.adicCompletion ℚ)⁻¹), 1, γ * (a : v.adicCompletion ℚ)⁻¹] i j := by
  rw [gl3Entry, dualCellPoint_coe]

private theorem cornerEntry_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    cornerEntry v (dualCellPoint v α β γ a x) = α - γ * x / a := by
  simp only [cornerEntry, gl3Entry_dualCellPoint]
  simp
  ring

private theorem lowerMinor_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    lowerMinor v (dualCellPoint v α β γ a x) = 1 - β * x / a := by
  simp only [lowerMinor, gl3Entry_dualCellPoint]
  simp
  ring

private theorem outerMinor_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    outerMinor v (dualCellPoint v α β γ a x) = (γ - α * β) / a := by
  simp only [outerMinor, gl3Entry_dualCellPoint]
  simp
  ring

private theorem
    gl3Det_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    gl3Det v (dualCellPoint v α β γ a x) = (a : v.adicCompletion ℚ)⁻¹ := by
  rw [gl3Det, dualCellPoint_coe, Matrix.det_fin_three]
  simp
  ring

private theorem
    cellRatio_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    cellRatio v (dualCellPoint v α β γ a x) =
      ![1 / (α - γ * x / a), γ * (a : v.adicCompletion ℚ)⁻¹ / (α - γ * x / a),
        (γ - α * β) / a / (1 - β * x / a)] := by
  rw [cellRatio, cornerEntry_dualCellPoint, outerMinor_dualCellPoint, lowerMinor_dualCellPoint]
  simp [gl3Entry_dualCellPoint]

private theorem cellValue_dualCellPoint (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (α β γ : v.adicCompletion ℚ)
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    cellValue v χ (dualCellPoint v α β γ a x) =
      charExt (χ 0) ((a : v.adicCompletion ℚ)⁻¹ / (1 - β * x / a)) *
          charExt (χ 1) ((1 - β * x / a) / (α - γ * x / a)) * charExt (χ 2) (α - γ * x / a) *
        ((‖(a : v.adicCompletion ℚ)⁻¹ / (1 - β * x / a)‖ / ‖α - γ * x / a‖ : ℝ) : ℂ) := by
  rw [cellValue, gl3Det_dualCellPoint, lowerMinor_dualCellPoint, cornerEntry_dualCellPoint]

end DualPoint
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
end Part4
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

section Part5

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 integrable_coupledIntegrand"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem modulus_real_eq_norm (x : v.adicCompletion ℚ) : (modulus x : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

private theorem _root_.LanglandsTunnell.CubicInduction.one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

p2m_export "LanglandsTunnell.CubicInduction" "one_lt_absNorm_real"
private theorem isClosed_valued_le (n : ℤ) : IsClosed {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  obtain ⟨y₀, hy₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp n)
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n}
      = {x | Valued.v.restrict x ≤ Valued.v.restrict y₀} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Valuation.restrict_le_iff, hy₀]
  rw [hset]
  exact Valued.isClosed_closedBall _ _

end TorusValues
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
end Part5
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

section Part14

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt modulus modulus_of_ne_zero modulus_pos modulus_ne_zero modulus_mul charExt charExt_zero charExt_of_ne_zero charExt_coe_units mulMeasure modulus_adicCompletion_eq_nnnorm integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem modulus_coe_eq_norm (x : v.adicCompletion ℚ) : (modulus x : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

private theorem integral_mulMeasure_eq_integral_indicator (μ : @Measure (v.adicCompletion ℚ) (localBorel ℚ v))
    (G : v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    ∫ x, G x ∂(mulMeasure μ) =
      ∫ x, ({0}ᶜ : Set (v.adicCompletion ℚ)).indicator (fun x => (‖x‖⁻¹ : ℝ) • G x) x ∂μ := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hc : MeasurableSet ({0}ᶜ : Set (v.adicCompletion ℚ)) := isClosed_singleton.measurableSet.compl
  have hfun : (fun x : v.adicCompletion ℚ => ((modulus x : ℝ≥0∞))⁻¹) = fun x => ((‖x‖₊ : ℝ≥0∞))⁻¹ := by
    funext x
    rw [modulus_adicCompletion_eq_nnnorm ℚ v x]
  have hmeas : Measurable fun x : v.adicCompletion ℚ => ((modulus x : ℝ≥0∞))⁻¹ := by
    rw [hfun]
    exact measurable_nnnorm.coe_nnreal_ennreal.inv
  have hlt : ∀ᵐ x ∂(μ.restrict {0}ᶜ), ((modulus x : ℝ≥0∞))⁻¹ < ∞ := by
    rw [ae_restrict_iff' hc]
    exact Filter.Eventually.of_forall fun x hx => ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr (modulus_pos hx))
  unfold mulMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hlt, ← integral_indicator hc]
  congr 1
  funext x
  by_cases hx : x = 0
  · simp [hx]
  · rw [Set.indicator_of_mem (show x ∈ ({0}ᶜ : Set (v.adicCompletion ℚ)) from hx),
      Set.indicator_of_mem (show x ∈ ({0}ᶜ : Set (v.adicCompletion ℚ)) from hx), ENNReal.toReal_inv,
      ENNReal.coe_toReal, modulus_coe_eq_norm]

private theorem integral_comp_inv_mulMeasure_selfDualHaarAt (F : v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    ∫ x, F x⁻¹ ∂(mulMeasure (selfDualHaarAt ℚ v)) = ∫ x, F x ∂(mulMeasure (selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  rw [integral_mulMeasure_eq_integral_indicator v _ (fun x => F x⁻¹), integral_mulMeasure_eq_integral_indicator v _ F]

  set f : v.adicCompletion ℚ → ℂ := ({0}ᶜ : Set (v.adicCompletion ℚ)).indicator fun u => (‖u‖ : ℝ) • F u with hf
  have hleft : (fun x => ({0}ᶜ : Set (v.adicCompletion ℚ)).indicator (fun x => (‖x‖⁻¹ : ℝ) • F x⁻¹) x) =
      fun x => f x⁻¹ := by
    funext x
    by_cases hx : x = 0
    · simp [f, hx]
    · rw [Set.indicator_of_mem (show x ∈ ({0}ᶜ : Set (v.adicCompletion ℚ)) from hx), hf,
        Set.indicator_of_mem (show x⁻¹ ∈ ({0}ᶜ : Set (v.adicCompletion ℚ)) from inv_ne_zero hx), norm_inv]
  rw [hleft, integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion ℚ v (selfDualHaarAt ℚ v) f]
  congr 1
  funext u
  by_cases hu : u = 0
  · simp [f, hu]
  · rw [hf, Set.indicator_of_mem (show u ∈ ({0}ᶜ : Set (v.adicCompletion ℚ)) from hu),
      Set.indicator_of_mem (show u ∈ ({0}ᶜ : Set (v.adicCompletion ℚ)) from hu), modulus_coe_eq_norm, smul_smul]
    congr 1
    have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    field_simp

section MeasureForm

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

private theorem inv_preimage_shell (j : ℤ) :
    (fun x : v.adicCompletion ℚ => x⁻¹) ⁻¹' LaurentZetaSlot.shell v j = LaurentZetaSlot.shell v (-j) := by
  ext x
  show Valued.v x⁻¹ = WithZero.exp (-j) ↔ Valued.v x = WithZero.exp (-(-j))
  rw [map_inv₀, neg_neg, inv_eq_iff_eq_inv, ← WithZero.exp_neg, neg_neg]

private theorem disjoint_shell {i j : ℤ} (h : i ≠ j) :
    Disjoint (LaurentZetaSlot.shell v i) (LaurentZetaSlot.shell v j) := by
  rw [Set.disjoint_left]
  intro x hi hj
  have hi' : Valued.v x = WithZero.exp (-i) := hi
  have hj' : Valued.v x = WithZero.exp (-j) := hj
  exact h (neg_injective (WithZero.exp_injective (hi'.symm.trans hj')))

private theorem iUnion_shell_eq : (⋃ j : ℤ, LaurentZetaSlot.shell v j) = ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj⟩ h0
    exact LaurentZetaSlot.shell_subset_compl_zero v j hj (Set.mem_singleton_iff.mpr h0)
  · intro hx
    exact LaurentZetaSlot.exists_mem_shell v hx

private theorem mulMeasure_singleton_zero (μ : Measure (v.adicCompletion ℚ)) :
    mulMeasure μ ({0} : Set (v.adicCompletion ℚ)) = 0 := by
  unfold mulMeasure
  rw [withDensity_apply _ (measurableSet_singleton 0), Measure.restrict_restrict (measurableSet_singleton 0),
    Set.inter_compl_self, Measure.restrict_empty, lintegral_zero_measure]

private theorem mulMeasure_selfDualHaarAt_shell_lt_top (j : ℤ) :
    mulMeasure (selfDualHaarAt ℚ v) (LaurentZetaSlot.shell v j) < ∞ := by
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  have hs : MeasurableSet (LaurentZetaSlot.shell v j) := LaurentZetaSlot.measurableSet_shell v j
  have hq : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by
    exact_mod_cast fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hc : ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-j)) ≠ 0 := zpow_ne_zero _ hq
  unfold mulMeasure
  rw [withDensity_apply _ hs]
  calc ∫⁻ x in LaurentZetaSlot.shell v j, ((modulus x : ℝ≥0∞))⁻¹ ∂((selfDualHaarAt ℚ v).restrict {0}ᶜ)
      = ∫⁻ x in LaurentZetaSlot.shell v j, ((((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-j) : ℝ≥0) : ℝ≥0∞))⁻¹
          ∂((selfDualHaarAt ℚ v).restrict {0}ᶜ) :=
        setLIntegral_congr_fun hs fun x hx => by rw [LaurentZetaSlot.modulus_eq_of_mem_shell v hx]
    _ = ((((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-j) : ℝ≥0) : ℝ≥0∞))⁻¹ *
          ((selfDualHaarAt ℚ v).restrict {0}ᶜ) (LaurentZetaSlot.shell v j) := setLIntegral_const _ _
    _ < ∞ := by
        refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc))) ?_
        rw [Measure.restrict_apply hs]
        exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) (LaurentZetaSlot.isCompact_shell v j).measure_lt_top

private theorem mulMeasure_inv_preimage_eq_of_lt_top {T : Set (v.adicCompletion ℚ)} (hT : MeasurableSet T)
    (h1 : mulMeasure (selfDualHaarAt ℚ v) ((fun x : v.adicCompletion ℚ => x⁻¹) ⁻¹' T) < ∞)
    (h2 : mulMeasure (selfDualHaarAt ℚ v) T < ∞) :
    mulMeasure (selfDualHaarAt ℚ v) ((fun x : v.adicCompletion ℚ => x⁻¹) ⁻¹' T) =
      mulMeasure (selfDualHaarAt ℚ v) T := by
  have hind := integral_comp_inv_mulMeasure_selfDualHaarAt v (T.indicator fun _ => (1 : ℂ))
  have hL : (fun x : v.adicCompletion ℚ => T.indicator (fun _ => (1 : ℂ)) x⁻¹) =
      ((fun x : v.adicCompletion ℚ => x⁻¹) ⁻¹' T).indicator fun _ => (1 : ℂ) := by
    funext x
    rw [← Set.indicator_comp_right]
    rfl
  rw [hL, integral_indicator_const _ (measurable_inv hT), integral_indicator_const _ hT, Complex.real_smul,
    Complex.real_smul, mul_one, mul_one, Complex.ofReal_inj] at hind
  simp only [measureReal_def] at hind
  exact (ENNReal.toReal_eq_toReal_iff' h1.ne h2.ne).mp hind

private theorem map_inv_mulMeasure_selfDualHaarAt :
    letI := localBorel ℚ v
    Measure.map (fun x : v.adicCompletion ℚ => x⁻¹) (mulMeasure (selfDualHaarAt ℚ v)) =
      mulMeasure (selfDualHaarAt ℚ v) := by
  have hmi : Measurable fun x : v.adicCompletion ℚ => x⁻¹ := measurable_inv
  have hc : MeasurableSet ({0}ᶜ : Set (v.adicCompletion ℚ)) := (measurableSet_singleton 0).compl
  ext S hS
  rw [Measure.map_apply hmi hS]

  have hdecomp : ∀ {T : Set (v.adicCompletion ℚ)}, MeasurableSet T →
      mulMeasure (selfDualHaarAt ℚ v) T =
        ∑' j : ℤ, mulMeasure (selfDualHaarAt ℚ v) (T ∩ LaurentZetaSlot.shell v j) := by
    intro T hT
    have hz : mulMeasure (selfDualHaarAt ℚ v) (T \ {0}ᶜ) = 0 :=
      measure_mono_null (fun x hx => by simpa using hx.2) (mulMeasure_singleton_zero v _)
    rw [← measure_inter_add_diff T hc, hz, add_zero, ← iUnion_shell_eq v, Set.inter_iUnion]
    exact measure_iUnion (fun i j hij => (disjoint_shell v hij).mono Set.inter_subset_right Set.inter_subset_right)
      fun j => hT.inter (LaurentZetaSlot.measurableSet_shell v j)
  rw [hdecomp (hmi hS), hdecomp hS]
  have hterm : ∀ j : ℤ,
      mulMeasure (selfDualHaarAt ℚ v) ((fun x : v.adicCompletion ℚ => x⁻¹) ⁻¹' S ∩ LaurentZetaSlot.shell v j) =
        mulMeasure (selfDualHaarAt ℚ v) (S ∩ LaurentZetaSlot.shell v (-j)) := by
    intro j
    have hset : (fun x : v.adicCompletion ℚ => x⁻¹) ⁻¹' S ∩ LaurentZetaSlot.shell v j =
        (fun x : v.adicCompletion ℚ => x⁻¹) ⁻¹' (S ∩ LaurentZetaSlot.shell v (-j)) := by
      rw [Set.preimage_inter, inv_preimage_shell, neg_neg]
    rw [hset]
    refine mulMeasure_inv_preimage_eq_of_lt_top v (hS.inter (LaurentZetaSlot.measurableSet_shell v (-j))) ?_ ?_
    · rw [← hset]
      exact lt_of_le_of_lt (measure_mono Set.inter_subset_right) (mulMeasure_selfDualHaarAt_shell_lt_top v j)
    · exact lt_of_le_of_lt (measure_mono Set.inter_subset_right) (mulMeasure_selfDualHaarAt_shell_lt_top v (-j))
  simp_rw [hterm]
  exact (Equiv.neg ℤ).tsum_eq fun j => mulMeasure (selfDualHaarAt ℚ v) (S ∩ LaurentZetaSlot.shell v j)

end MeasureForm
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

end LanglandsTunnell.TateLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
end Part14
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

section Part15

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 integrable_coupledIntegrand"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def truncChar (c : ℤ) (t : v.adicCompletion ℚ) : ℂ :=
  if Valued.v t ≤ WithZero.exp c then (NumberField.StandardAddChar.psiLocal ℚ v t : ℂ) else 0

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
end Part15
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

section Part18
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 integrable_coupledIntegrand"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualLevelLegs

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem mulMeasure_singleton_zero :
    mulMeasure (selfDualHaarAt ℚ v) {(0 : v.adicCompletion ℚ)} = 0 := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hs : MeasurableSet {(0 : v.adicCompletion ℚ)} := isClosed_singleton.measurableSet
  rw [mulMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs, Set.inter_compl_self,
    Measure.restrict_empty, lintegral_zero_measure]

end DualLevelLegs
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

end Part18
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

section Part22
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 integrable_coupledIntegrand"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem truncChar_eq_zero_of_lt {c : ℤ} {t : v.adicCompletion ℚ} (ht : WithZero.exp c < Valued.v t) :
    truncChar v c t = 0 := by
  simp only [truncChar, if_neg (not_le.mpr ht)]

private theorem truncChar_exists_norm_le (c : ℤ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c' : ℤ) (t : v.adicCompletion ℚ), Valued.v t ≤ WithZero.exp c →
      ‖truncChar v c' t‖ ≤ B := by
  set w : (v.adicCompletion ℚ)ˣ := NumberField.AdelicLevel.uniformizerUnit ℚ v ^ c with hw
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← coe_integersPositiveCompacts ℚ v]
    exact (integersPositiveCompacts ℚ v).isCompact
  have hcont : Continuous fun s : v.adicCompletion ℚ =>
      (NumberField.StandardAddChar.psiLocal ℚ v (((w⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * s) : ℂ) :=
    (NumberField.StandardAddChar.continuous_psiLocal ℚ v).comp (continuous_const.mul continuous_id)
  obtain ⟨B, hB⟩ := hO.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun c' t ht => ?_⟩
  by_cases htc : Valued.v t ≤ WithZero.exp c'
  · have hs : (w : v.adicCompletion ℚ) * t ∈ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
      rw [SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hw,
        LaurentZetaSlot.valued_uniformizerUnit_zpow]
      calc WithZero.exp (-c) * Valued.v t ≤ WithZero.exp (-c) * WithZero.exp c := mul_le_mul_right ht _
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    have hval : truncChar v c' t =
        NumberField.StandardAddChar.psiLocal ℚ v
          (((w⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * ((w : v.adicCompletion ℚ) * t)) := by
      simp only [truncChar, if_pos htc, Units.inv_mul_cancel_left]
    rw [hval]
    exact (hB _ hs).trans (le_max_left _ _)
  · rw [truncChar_eq_zero_of_lt v (not_le.mp htc), norm_zero]
    exact le_max_right _ _

private theorem gaussShell_ball_inter_compl_zero_eq (r : ℤ) :
    {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp r} ∩ ({0}ᶜ : Set (v.adicCompletion ℚ)) =
      ⋃ n : ℕ, {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (r - n)} := by
  ext t
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨ht, ht0⟩
    obtain ⟨k, hk⟩ := LaurentZetaSlot.exists_mem_shell v ht0
    have hk' : Valued.v t = WithZero.exp (-k) := hk
    have hkr : -k ≤ r := by rw [hk'] at ht; exact WithZero.exp_le_exp.mp ht
    refine ⟨(r + k).toNat, ?_⟩
    rw [hk', Int.toNat_of_nonneg (by omega)]
    congr 1
    ring
  · rintro ⟨n, hn⟩
    refine ⟨?_, ?_⟩
    · rw [hn]
      exact WithZero.exp_le_exp.mpr (by omega)
    · rintro rfl
      rw [map_zero] at hn
      exact WithZero.exp_ne_zero hn.symm

private theorem gaussShell_exists_norm_charExt_le (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (hη1 : ‖((η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : v.adicCompletion ℚ, ‖charExt η t‖ ≤ M := by
  obtain ⟨M, hM⟩ := LaurentZetaSlot.exists_bound_charExt_unitShell v η hη
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht0 : t = 0
  · rw [ht0, charExt_zero, norm_zero]
    exact le_max_right _ _
  obtain ⟨k, hk⟩ := LaurentZetaSlot.exists_mem_shell v ht0
  rw [← LaurentZetaSlot.image_unitShell_eq_shell] at hk
  obtain ⟨u, hu, rfl⟩ := hk
  rw [charExt_mul ℚ v, charExt_coe_units, map_zpow, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, hη1,
    one_zpow, one_mul]
  exact (hM u hu).trans (le_max_left _ _)

private theorem gaussShell_coe_modulus_of_valued_eq {j : ℤ} {t : v.adicCompletion ℚ}
    (ht : Valued.v t = WithZero.exp j) : (modulus t : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ j := by
  have ht' : t ∈ LaurentZetaSlot.shell v (-j) := by
    show Valued.v t = WithZero.exp (- -j)
    rw [neg_neg]
    exact ht
  rw [LaurentZetaSlot.coe_modulus_eq_of_mem_shell v ht', neg_neg]

private theorem gaussShell_mulMeasure_eq (j : ℤ) :
    mulMeasure (selfDualHaarAt ℚ v) {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} =
      mulMeasure (selfDualHaarAt ℚ v) {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)} := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hS : {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} = LaurentZetaSlot.shell v (-j) := by
    ext t
    simp only [Set.mem_setOf_eq, LaurentZetaSlot.shell, neg_neg]
  have hU : {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)} = LaurentZetaSlot.unitShell v := by
    ext t
    simp only [Set.mem_setOf_eq, LaurentZetaSlot.unitShell, WithZero.exp_zero]
  rw [hS, hU]
  set u : (v.adicCompletion ℚ)ˣ := NumberField.AdelicLevel.uniformizerUnit ℚ v ^ (-j) with hu
  have hmap : Measure.map (fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x)
      (mulMeasure (selfDualHaarAt ℚ v)) = mulMeasure (selfDualHaarAt ℚ v) := map_mul_left_mulMeasure ℚ v u
  have hmeas : Measurable fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x :=
    (continuous_const.mul continuous_id).measurable
  calc mulMeasure (selfDualHaarAt ℚ v) (LaurentZetaSlot.shell v (-j))
      = Measure.map (fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x) (mulMeasure (selfDualHaarAt ℚ v))
          (LaurentZetaSlot.shell v (-j)) := by rw [hmap]
    _ = mulMeasure (selfDualHaarAt ℚ v)
          ((fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x) ⁻¹' LaurentZetaSlot.shell v (-j)) :=
        Measure.map_apply hmeas (LaurentZetaSlot.measurableSet_shell v (-j))
    _ = mulMeasure (selfDualHaarAt ℚ v) (LaurentZetaSlot.unitShell v) := by
        rw [← LaurentZetaSlot.image_unitShell_eq_shell, hu,
          Set.preimage_image_eq _ (mul_right_injective₀ (Units.ne_zero _))]

private theorem gaussShell_mulMeasure_lt_top :
    mulMeasure (selfDualHaarAt ℚ v) {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)} < ⊤ := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  have hU : {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)} = LaurentZetaSlot.unitShell v := by
    ext t
    simp only [Set.mem_setOf_eq, LaurentZetaSlot.unitShell, WithZero.exp_zero]
  have hmeasU : MeasurableSet (LaurentZetaSlot.unitShell v) := LaurentZetaSlot.measurableSet_unitShell v
  have hfin : selfDualHaarAt ℚ v (LaurentZetaSlot.unitShell v) < ⊤ :=
    (LaurentZetaSlot.isCompact_unitShell v).measure_lt_top
  have hdens : ∀ t ∈ LaurentZetaSlot.unitShell v, ((modulus t : ENNReal))⁻¹ = 1 := by
    intro t ht
    have ht' : Valued.v t = WithZero.exp (0 : ℤ) := by
      have h : Valued.v t = 1 := ht
      rw [h, WithZero.exp_zero]
    have hm : (modulus t : ℝ) = 1 := by
      rw [gaussShell_coe_modulus_of_valued_eq v ht', zpow_zero]
    have hm' : modulus t = 1 := NNReal.coe_injective (by rw [hm, NNReal.coe_one])
    rw [hm', ENNReal.coe_one, inv_one]
  rw [hU]
  unfold mulMeasure
  rw [MeasureTheory.withDensity_apply _ hmeasU, Measure.restrict_restrict hmeasU,
    MeasureTheory.setLIntegral_congr_fun (hmeasU.inter (measurableSet_singleton 0).compl)
      (fun t ht => hdens t ht.1),
    MeasureTheory.setLIntegral_one]
  exact (measure_mono Set.inter_subset_left).trans_lt hfin

private theorem gaussShell_integrableOn_and_integral_norm_le (η : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hη : IsLocallyConstant η) (z : ℂ) (c j : ℤ) {B M : ℝ} (_ : 0 ≤ M)
    (hB : ∀ t : v.adicCompletion ℚ, Valued.v t = WithZero.exp j → ‖truncChar v c (-t)‖ ≤ B)
    (hM : ∀ t : v.adicCompletion ℚ, ‖charExt η t‖ ≤ M) :
    IntegrableOn (fun t : v.adicCompletion ℚ => truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z)
        {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} (mulMeasure (selfDualHaarAt ℚ v)) ∧
      (∫ t in {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j},
          ‖truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z‖ ∂(mulMeasure (selfDualHaarAt ℚ v))) ≤
        (mulMeasure (selfDualHaarAt ℚ v)).real {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)} *
          (B * M * ((Ideal.absNorm v.asIdeal : ℝ) ^ j) ^ z.re) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : SFinite (mulMeasure (selfDualHaarAt ℚ v)) := sFinite_mulMeasure_selfDualHaarAt ℚ v
  set S : Set (v.adicCompletion ℚ) := {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} with hSdef
  set K : ℝ := B * M * ((Ideal.absNorm v.asIdeal : ℝ) ^ j) ^ z.re with hK
  have hSmeas : MeasurableSet S := by
    have hS : S = LaurentZetaSlot.shell v (-j) := by
      ext t
      simp only [hSdef, Set.mem_setOf_eq, LaurentZetaSlot.shell, neg_neg]
    rw [hS]
    exact LaurentZetaSlot.measurableSet_shell v (-j)
  have hSfin : mulMeasure (selfDualHaarAt ℚ v) S ≠ ⊤ := by
    rw [hSdef, gaussShell_mulMeasure_eq v j]
    exact (gaussShell_mulMeasure_lt_top v).ne
  have hpt : ∀ t ∈ S, ‖truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z‖ ≤ K := by
    intro t ht
    have ht' : Valued.v t = WithZero.exp j := ht
    have hpos : (0 : ℝ) < (modulus t : ℝ) := by
      rw [gaussShell_coe_modulus_of_valued_eq v ht']
      exact zpow_pos (by exact_mod_cast Nat.pos_of_ne_zero (LaurentZetaSlot.absNorm_ne_zero v)) j
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, gaussShell_coe_modulus_of_valued_eq v ht',
      hK]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t ht')
    have hq : (0 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ j) ^ z.re := Real.rpow_nonneg (by positivity) _
    gcongr
    · exact hB t ht'
    · exact hM t
  have hmeas : AEStronglyMeasurable
      (fun t : v.adicCompletion ℚ => truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z)
      (mulMeasure (selfDualHaarAt ℚ v)) := by
    have htr : Measurable fun t : v.adicCompletion ℚ => truncChar v c (-t) := by
      have hind : (fun t : v.adicCompletion ℚ => truncChar v c (-t)) =
          {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp c}.indicator
            fun t => (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) := by
        ext t
        simp only [truncChar, Set.indicator, Set.mem_setOf_eq, Valuation.map_neg]
      rw [hind]
      exact Measurable.indicator
        ((NumberField.StandardAddChar.continuous_psiLocal ℚ v).comp continuous_neg).measurable
        (isClosed_valued_le v c).measurableSet
    exact ((htr.mul (LaurentZetaSlot.measurable_charExt v η hη)).mul
      (LaurentZetaSlot.measurable_modulus_cpow v z)).aestronglyMeasurable
  have hint : IntegrableOn
      (fun t : v.adicCompletion ℚ => truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z) S
      (mulMeasure (selfDualHaarAt ℚ v)) := by
    refine Measure.integrableOn_of_bounded hSfin hmeas (M := K) ?_
    exact (ae_restrict_mem hSmeas).mono hpt
  refine ⟨hint, ?_⟩
  calc (∫ t in S, ‖truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z‖
          ∂(mulMeasure (selfDualHaarAt ℚ v)))
      ≤ ∫ _ in S, K ∂(mulMeasure (selfDualHaarAt ℚ v)) :=
        setIntegral_mono_on hint.norm (integrableOn_const hSfin) hSmeas hpt
    _ = (mulMeasure (selfDualHaarAt ℚ v)).real S * K := by rw [setIntegral_const, smul_eq_mul]
    _ = (mulMeasure (selfDualHaarAt ℚ v)).real {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)} * K := by
        rw [measureReal_def, measureReal_def, hSdef, gaussShell_mulMeasure_eq v j]

private theorem truncChar_integrable (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (hη1 : ‖((η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (z : ℂ) (hz : 0 < z.re) (c : ℤ) :
    Integrable (fun t : v.adicCompletion ℚ => truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z)
      (mulMeasure (selfDualHaarAt ℚ v)) := by
  obtain ⟨B, hB0, hB⟩ := truncChar_exists_norm_le v c
  obtain ⟨M, hM0, hM⟩ := gaussShell_exists_norm_charExt_le v η hη hη1
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq
  have hq1 : (1 : ℝ) < q := LaurentZetaSlot.one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq1
  set ρ : ℝ := q⁻¹ ^ z.re with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (inv_nonneg.mpr hq0.le) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one (inv_nonneg.mpr hq0.le) (inv_lt_one_of_one_lt₀ hq1) hz
  set V : ℝ := (mulMeasure (selfDualHaarAt ℚ v)).real {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)}
    with hV
  set F : v.adicCompletion ℚ → ℂ := fun t => truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z with hF

  have hshell : ∀ n : ℕ,
      IntegrableOn F {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (c - n)} (mulMeasure (selfDualHaarAt ℚ v)) ∧
        (∫ t in {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (c - n)}, ‖F t‖
            ∂(mulMeasure (selfDualHaarAt ℚ v))) ≤ (V * (B * M * (q ^ c) ^ z.re)) * ρ ^ n := by
    intro n
    have hBn : ∀ t : v.adicCompletion ℚ, Valued.v t = WithZero.exp (c - n) → ‖truncChar v c (-t)‖ ≤ B := by
      intro t ht
      apply hB c (-t)
      rw [Valuation.map_neg, ht]
      exact WithZero.exp_le_exp.mpr (by omega)
    obtain ⟨h1, h2⟩ := gaussShell_integrableOn_and_integral_norm_le v η hη z c (c - n) hM0 hBn hM
    refine ⟨h1, h2.trans (le_of_eq ?_)⟩
    have hsplit : ((q ^ (c - (n : ℤ))) ^ z.re : ℝ) = (q ^ c) ^ z.re * ρ ^ n := by
      rw [zpow_sub₀ hq0.ne', div_eq_mul_inv, ← inv_zpow, zpow_natCast,
        Real.mul_rpow (zpow_nonneg hq0.le _) (pow_nonneg (inv_nonneg.mpr hq0.le) _), hρ,
        ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hq0.le), mul_comm (n : ℝ),
        Real.rpow_mul (inv_nonneg.mpr hq0.le), Real.rpow_natCast]
    rw [← hV, ← hq, hsplit]
    ring

  have hsupp : Function.support F ⊆
      ⋃ n : ℕ, {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (c - n)} := by
    intro t ht
    rw [← gaussShell_ball_inter_compl_zero_eq v c]
    refine ⟨?_, ?_⟩
    · by_contra hlt
      apply ht
      simp only [hF, truncChar_eq_zero_of_lt v (by rw [Valuation.map_neg]; exact not_le.mp hlt), zero_mul]
    · rintro rfl
      apply ht
      simp only [hF, charExt_zero, mul_zero, zero_mul]
  have hunion : IntegrableOn F (⋃ n : ℕ, {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (c - n)})
      (mulMeasure (selfDualHaarAt ℚ v)) := by
    refine integrableOn_iUnion_of_summable_integral_norm (fun n => (hshell n).1) ?_
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) (fun n => (hshell n).2) ?_
    exact (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hunion

private theorem integrable_truncChar_mul_charExt_mul_cpow
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (hη1 : ‖((η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (z : ℂ) (hz : 0 < z.re) (c : ℤ) :
    Integrable (fun t : v.adicCompletion ℚ => truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z)
      (mulMeasure (selfDualHaarAt ℚ v)) := by
  exact truncChar_integrable v η hη hη1 z hz c

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

end Part22
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

section Part28

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 integrable_coupledIntegrand"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualPointwise

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem charExt_mul_char (η₁ η₂ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (y : v.adicCompletion ℚ) :
    charExt (η₁ * η₂) y = charExt η₁ y * charExt η₂ y := by
  by_cases hy : y = 0
  · subst hy
    simp
  · rw [charExt_of_ne_zero _ hy, charExt_of_ne_zero _ hy, charExt_of_ne_zero _ hy, MonoidHom.mul_apply,
      Units.val_mul]

private theorem charExt_inv_char (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (y : v.adicCompletion ℚ) :
    charExt η⁻¹ y = (charExt η y)⁻¹ := by
  by_cases hy : y = 0
  · subst hy
    simp
  · rw [charExt_of_ne_zero _ hy, charExt_of_ne_zero _ hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

private theorem charExt_inv_arg (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (y : v.adicCompletion ℚ) :
    charExt η y⁻¹ = (charExt η y)⁻¹ := by
  by_cases hy : y = 0
  · subst hy
    simp
  · have hu : y⁻¹ = (((Units.mk0 y hy)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := by simp
    rw [hu, charExt_coe_units, map_inv, Units.val_inv_eq_inv_val, charExt_of_ne_zero _ hy]

private theorem charExt_div_arg (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (y z : v.adicCompletion ℚ) :
    charExt η (y / z) = charExt η y * (charExt η z)⁻¹ := by
  rw [div_eq_mul_inv, charExt_mul ℚ v, charExt_inv_arg]

private theorem charExt_units_inv (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : (v.adicCompletion ℚ)ˣ) :
    charExt η ((a : v.adicCompletion ℚ)⁻¹) = ((η a : ℂˣ) : ℂ)⁻¹ := by
  rw [charExt_inv_arg, charExt_coe_units]

private theorem cellSectionOf_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    cellSectionOf v ν Φ (dualCellPoint v α β γ a x) =
      (((ν 0) a : ℂˣ) : ℂ)⁻¹ * ((‖(a : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) *
        (charExt (ν 1 * (ν 0)⁻¹) (1 - β / (a : v.adicCompletion ℚ) * x) *
            charExt (ν 2 * (ν 1)⁻¹) (α - γ / (a : v.adicCompletion ℚ) * x) *
            ((‖1 - β / (a : v.adicCompletion ℚ) * x‖⁻¹ * ‖α - γ / (a : v.adicCompletion ℚ) * x‖⁻¹ : ℝ) : ℂ) *
            Φ ![(α - γ / (a : v.adicCompletion ℚ) * x)⁻¹,
              γ / (a : v.adicCompletion ℚ) / (α - γ / (a : v.adicCompletion ℚ) * x),
              (γ / (a : v.adicCompletion ℚ) - α * (β / (a : v.adicCompletion ℚ))) /
                (1 - β / (a : v.adicCompletion ℚ) * x)]) := by
  have h₁ : γ * x / (a : v.adicCompletion ℚ) = γ / (a : v.adicCompletion ℚ) * x := by ring
  have h₂ : β * x / (a : v.adicCompletion ℚ) = β / (a : v.adicCompletion ℚ) * x := by ring
  by_cases hc : α - γ / (a : v.adicCompletion ℚ) * x = 0
  · have hnot : dualCellPoint v α β γ a x ∉ bigCell3 v := by
      rw [mem_bigCell3_iff, cornerEntry_dualCellPoint, h₁, hc]
      exact fun h => h.1 rfl
    rw [cellSectionOf_apply_of_notMem v ν Φ hnot, hc]
    simp
  by_cases hl : 1 - β / (a : v.adicCompletion ℚ) * x = 0
  · have hnot : dualCellPoint v α β γ a x ∉ bigCell3 v := by
      rw [mem_bigCell3_iff, lowerMinor_dualCellPoint, h₂, hl]
      exact fun h => h.2 rfl
    rw [cellSectionOf_apply_of_notMem v ν Φ hnot, hl]
    simp
  have hmem : dualCellPoint v α β γ a x ∈ bigCell3 v := by
    rw [mem_bigCell3_iff, cornerEntry_dualCellPoint, lowerMinor_dualCellPoint, h₁, h₂]
    exact ⟨hc, hl⟩
  have h₃ : 1 / (α - γ / (a : v.adicCompletion ℚ) * x) = (α - γ / (a : v.adicCompletion ℚ) * x)⁻¹ := by ring
  have h₄ : γ * (a : v.adicCompletion ℚ)⁻¹ = γ / (a : v.adicCompletion ℚ) := by ring
  have h₅ : (γ - α * β) / (a : v.adicCompletion ℚ) =
      γ / (a : v.adicCompletion ℚ) - α * (β / (a : v.adicCompletion ℚ)) := by ring
  rw [cellSectionOf_apply_of_mem v ν Φ hmem, cellValue_dualCellPoint, cellRatio_dualCellPoint, h₁, h₂, h₃, h₄,
    h₅]
  simp only [charExt_div_arg, charExt_units_inv, charExt_mul_char, charExt_inv_char, norm_div, norm_inv]
  push_cast
  ring

end DualPointwise
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
end Part28
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

section Part31
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped NNReal

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 integrable_coupledIntegrand"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section UnfoldedFactors

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private theorem charExt_factors_eq (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : (v.adicCompletion ℚ)ˣ)
    {β γ U L : v.adicCompletion ℚ} (hβ : β ≠ 0) (hγ : γ ≠ 0) (hU : U ≠ 0) (hL : L ≠ 0) :
    charExt (ν 0 * χ)⁻¹ β * charExt (ν 1 * χ)⁻¹ (γ / β) * charExt (ν 2 * χ)⁻¹ U⁻¹ *
          charExt (ν 1 * χ) (γ / (a : v.adicCompletion ℚ) / U) *
        charExt (ν 0 * (ν 1)⁻¹) (β / (a : v.adicCompletion ℚ) / L) =
      (((ν 0) a : ℂˣ) : ℂ)⁻¹ * charExt χ⁻¹ (a : v.adicCompletion ℚ) *
        (charExt (ν 1 * (ν 0)⁻¹) L * charExt (ν 2 * (ν 1)⁻¹) U) := by
  have h0β := LaurentZetaSlot.charExt_ne_zero v (ν 0) hβ
  have h1β := LaurentZetaSlot.charExt_ne_zero v (ν 1) hβ
  have hχβ := LaurentZetaSlot.charExt_ne_zero v χ hβ
  have h1γ := LaurentZetaSlot.charExt_ne_zero v (ν 1) hγ
  have hχγ := LaurentZetaSlot.charExt_ne_zero v χ hγ
  have h1U := LaurentZetaSlot.charExt_ne_zero v (ν 1) hU
  have h2U := LaurentZetaSlot.charExt_ne_zero v (ν 2) hU
  have hχU := LaurentZetaSlot.charExt_ne_zero v χ hU
  have h0L := LaurentZetaSlot.charExt_ne_zero v (ν 0) hL
  have h1L := LaurentZetaSlot.charExt_ne_zero v (ν 1) hL
  have h0a : (((ν 0) a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h1a : (((ν 1) a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hχa : ((χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  simp only [charExt_inv_char, charExt_mul_char, charExt_div_arg, charExt_inv_arg, charExt_coe_units,
    MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

private theorem ofReal_div_cpow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (r : ℂ) :
    ((x / y : ℝ) : ℂ) ^ r = (x : ℂ) ^ r * ((y : ℂ) ^ r)⁻¹ := by
  have harg : ((y : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy]
    exact Real.pi_ne_zero.symm
  rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx (inv_nonneg.mpr hy), Complex.ofReal_inv,
    Complex.inv_cpow _ _ harg]

private theorem ofReal_inv_cpow {y : ℝ} (hy : 0 ≤ y) (r : ℂ) : ((y⁻¹ : ℝ) : ℂ) ^ r = ((y : ℂ) ^ r)⁻¹ := by
  have harg : ((y : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy]
    exact Real.pi_ne_zero.symm
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg]

private theorem modulus_factors_eq (a : (v.adicCompletion ℚ)ˣ) {β γ U L : v.adicCompletion ℚ} (hβ : β ≠ 0)
    (hγ : γ ≠ 0) (hU : U ≠ 0) (hL : L ≠ 0) (s : ℂ) :
    ((modulus β : ℝ) : ℂ) ^ (1 - s) * ((modulus (γ / β) : ℝ) : ℂ) ^ (1 - s) *
              ((modulus U⁻¹ : ℝ) : ℂ) ^ (1 - s) *
            ((modulus (γ / (a : v.adicCompletion ℚ) / U) : ℝ) : ℂ) ^ s *
          ((modulus (β / (a : v.adicCompletion ℚ) / L) : ℝ) : ℂ)⁻¹ *
        (((modulus β : ℝ) : ℂ) ^ 2 * ((modulus (γ / β) : ℝ) : ℂ) *
            (((modulus (β / (a : v.adicCompletion ℚ) / L) : ℝ) : ℂ) ^ 2)⁻¹)⁻¹ =
      ((‖(a : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) * ((‖L‖⁻¹ * ‖U‖⁻¹ : ℝ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s) := by
  have hB : ((‖β‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hβ)
  have hG : ((‖γ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hγ)
  have hUc : ((‖U‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hU)
  have hLc : ((‖L‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hL)
  have hA : ((‖(a : v.adicCompletion ℚ)‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr a.ne_zero)
  have hBs : ((‖β‖ : ℝ) : ℂ) ^ s ≠ 0 := fun h => hB ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hGs : ((‖γ‖ : ℝ) : ℂ) ^ s ≠ 0 := fun h => hG ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hUs : ((‖U‖ : ℝ) : ℂ) ^ s ≠ 0 := fun h => hUc ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hAs : ((‖(a : v.adicCompletion ℚ)‖ : ℝ) : ℂ) ^ s ≠ 0 := fun h => hA ((Complex.cpow_eq_zero_iff _ _).mp h).1
  simp only [modulus_real_eq_norm, norm_div, norm_inv]
  rw [ofReal_div_cpow (norm_nonneg γ) (norm_nonneg β), ofReal_inv_cpow (norm_nonneg U),
    ofReal_div_cpow (div_nonneg (norm_nonneg γ) (norm_nonneg _)) (norm_nonneg U),
    ofReal_div_cpow (norm_nonneg γ) (norm_nonneg _), Complex.cpow_sub _ _ hB, Complex.cpow_sub _ _ hG,
    Complex.cpow_sub _ _ hUc, Complex.cpow_sub _ _ hA, Complex.cpow_one, Complex.cpow_one, Complex.cpow_one,
    Complex.cpow_one]
  push_cast
  field_simp

private theorem truncChar_factors_eq (c : ℤ) (α : v.adicCompletion ℚ) {β : v.adicCompletion ℚ} (hβ : β ≠ 0)
    (γ : v.adicCompletion ℚ) :
    truncChar v c (-β) * truncChar v c (-(γ / β)) * truncChar v c (γ / β - α) =
      if Valued.v β ≤ WithZero.exp c ∧ Valued.v γ ≤ WithZero.exp c * Valued.v β ∧
          Valued.v (α - γ / β) ≤ WithZero.exp c then
        (psiLocal ℚ v (-(α + β)) : ℂ)
      else 0 := by
  have hb : Valued.v (-β) = Valued.v β := Valuation.map_neg _ _
  have hg : Valued.v (-(γ / β)) ≤ WithZero.exp c ↔ Valued.v γ ≤ WithZero.exp c * Valued.v β := by
    rw [Valuation.map_neg, map_div₀, div_le_iff₀ ((Valuation.pos_iff _).mpr hβ)]
  have ha : Valued.v (γ / β - α) = Valued.v (α - γ / β) := Valuation.map_sub_swap _ _ _
  simp only [truncChar, hb, ha]
  by_cases h1 : Valued.v β ≤ WithZero.exp c
  · by_cases h2 : Valued.v γ ≤ WithZero.exp c * Valued.v β
    · by_cases h3 : Valued.v (α - γ / β) ≤ WithZero.exp c
      · rw [if_pos h1, if_pos (hg.mpr h2), if_pos h3, if_pos ⟨h1, h2, h3⟩, ← AddChar.map_add_eq_mul,
          ← AddChar.map_add_eq_mul]
        congr 1
        ring
      · rw [if_neg h3, mul_zero, if_neg fun h => h3 h.2.2]
    · rw [if_neg fun h => h2 (hg.mp h), mul_zero, zero_mul, if_neg fun h => h2 h.2.1]
  · rw [if_neg h1, zero_mul, zero_mul, if_neg fun h => h1 h.1]

end UnfoldedFactors
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

end Part31
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

section Part32

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal"
open scoped ENNReal NNReal Pointwise

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 integrable_coupledIntegrand"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section UnfoldingMeasure

variable (v : HeightOneSpectrum (𝓞 ℚ))

private scoped instance instBorelSpaceUnfolding : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v

private scoped instance instSFiniteSelfDualHaarAt : SFinite (selfDualHaarAt ℚ v) := sFinite_selfDualHaarAt ℚ v

private scoped instance instSFiniteMulMeasure : SFinite (mulMeasure (selfDualHaarAt ℚ v)) :=
  sFinite_mulMeasure_selfDualHaarAt ℚ v

private scoped instance instIsAddHaarMeasureSelfDualHaarAt : (selfDualHaarAt ℚ v).IsAddHaarMeasure :=
  isAddHaarMeasure_selfDualHaarAt ℚ v

private theorem measurable_modulus_ennreal :
    Measurable fun x : v.adicCompletion ℚ => (modulus x : ℝ≥0∞) := by
  have h : (fun x : v.adicCompletion ℚ => (modulus x : ℝ≥0∞)) = fun x => ((‖x‖₊ : ℝ≥0) : ℝ≥0∞) := by
    funext x
    rw [modulus_adicCompletion_eq_nnnorm ℚ v x]
  rw [h]
  exact measurable_nnnorm.coe_nnreal_ennreal

private theorem modulus_ennreal_ne_zero {x : v.adicCompletion ℚ} (hx : x ≠ 0) : (modulus x : ℝ≥0∞) ≠ 0 := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x]
  exact ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr hx)

private theorem modulus_ennreal_inv {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    (modulus x⁻¹ : ℝ≥0∞) = ((modulus x : ℝ≥0∞))⁻¹ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x⁻¹, modulus_adicCompletion_eq_nnnorm ℚ v x, nnnorm_inv,
    ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hx)]

private theorem modulus_ennreal_neg_one : (modulus (-1 : v.adicCompletion ℚ) : ℝ≥0∞) = 1 := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v (-1), nnnorm_neg, nnnorm_one, ENNReal.coe_one]

private theorem selfDualHaarAt_singleton_zero : selfDualHaarAt ℚ v {0} = 0 := by
  set u := NumberField.AdelicLevel.uniformizerUnit ℚ v with hu
  have hsm : u • ({0} : Set (v.adicCompletion ℚ)) = {0} := by
    rw [Set.smul_set_singleton, Units.smul_def, smul_eq_mul, mul_zero]
  have h := selfDualHaarAt_smul_set ℚ v u {0}
  rw [hsm] at h
  have hfin : selfDualHaarAt ℚ v {0} ≠ ∞ := (isCompact_singleton.measure_lt_top).ne
  have hmem : (u : v.adicCompletion ℚ) ∈ LaurentZetaSlot.shell v 1 := by
    show Valued.v (u : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)
    rw [hu]
    exact NumberField.AdelicLevel.valued_uniformizerUnit ℚ v
  have hq : (1 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := by
    exact_mod_cast LaurentZetaSlot.one_lt_absNorm_real v
  have hNu : (modulus (u : v.adicCompletion ℚ) : ℝ≥0∞) ≠ 1 := by
    rw [LaurentZetaSlot.modulus_eq_of_mem_shell v hmem, zpow_neg, zpow_one, ne_eq, ENNReal.coe_eq_one,
      inv_eq_one]
    exact hq.ne'
  by_contra h0
  have h1 : 1 * selfDualHaarAt ℚ v {0} = (modulus (u : v.adicCompletion ℚ) : ℝ≥0∞) * selfDualHaarAt ℚ v {0} := by
    rwa [one_mul]
  exact hNu ((ENNReal.mul_left_inj h0 hfin).mp h1).symm

private theorem selfDualHaarAt_singleton (c : v.adicCompletion ℚ) : selfDualHaarAt ℚ v {c} = 0 := by
  have hset : (fun h : v.adicCompletion ℚ => -c + h) ⁻¹' {0} = {c} := by
    ext h
    simp only [Set.mem_preimage, Set.mem_singleton_iff, neg_add_eq_zero]
    exact eq_comm
  rw [← hset, measure_preimage_add]
  exact selfDualHaarAt_singleton_zero v

private theorem ae_ne_selfDualHaarAt (c : v.adicCompletion ℚ) : ∀ᵐ x ∂(selfDualHaarAt ℚ v), x ≠ c := by
  have h : ({c}ᶜ : Set (v.adicCompletion ℚ)) ∈ ae (selfDualHaarAt ℚ v) :=
    compl_mem_ae_iff.mpr (selfDualHaarAt_singleton v c)
  filter_upwards [h] with x hx
  exact hx

private theorem restrict_compl_zero_selfDualHaarAt :
    (selfDualHaarAt ℚ v).restrict {0}ᶜ = selfDualHaarAt ℚ v :=
  Measure.restrict_eq_self_of_ae_mem (ae_ne_selfDualHaarAt v 0)

private theorem ae_ne_zero_mulMeasure : ∀ᵐ x ∂(mulMeasure (selfDualHaarAt ℚ v)), x ≠ (0 : v.adicCompletion ℚ) := by
  have h0 : mulMeasure (selfDualHaarAt ℚ v) {0} = 0 := by
    unfold mulMeasure
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply (measurableSet_singleton 0), Set.inter_compl_self, measure_empty]
  have h : ({0}ᶜ : Set (v.adicCompletion ℚ)) ∈ ae (mulMeasure (selfDualHaarAt ℚ v)) := compl_mem_ae_iff.mpr h0
  filter_upwards [h] with x hx
  exact hx

private theorem lintegral_selfDualHaarAt_eq_mulMeasure (f : v.adicCompletion ℚ → ℝ≥0∞) :
    ∫⁻ x, f x ∂(selfDualHaarAt ℚ v) =
      ∫⁻ x, f x * (modulus x : ℝ≥0∞) ∂(mulMeasure (selfDualHaarAt ℚ v)) := by
  have hfin : ∀ᵐ x ∂(selfDualHaarAt ℚ v).restrict {0}ᶜ, ((modulus x : ℝ≥0∞))⁻¹ < ∞ := by
    rw [restrict_compl_zero_selfDualHaarAt]
    filter_upwards [ae_ne_selfDualHaarAt v 0] with x hx
    exact ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr (modulus_ennreal_ne_zero v hx))
  unfold mulMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_modulus_ennreal v).fun_inv hfin,
    restrict_compl_zero_selfDualHaarAt]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_ne_selfDualHaarAt v 0] with x hx
  simp only [Pi.mul_apply]
  rw [mul_comm (f x), ← mul_assoc, ENNReal.inv_mul_cancel (modulus_ennreal_ne_zero v hx) ENNReal.coe_ne_top,
    one_mul]

private theorem lintegral_selfDualHaarAt_comp_mul_left {c : v.adicCompletion ℚ} (hc : c ≠ 0)
    (g : v.adicCompletion ℚ → ℝ≥0∞) :
    ∫⁻ x, g x ∂(selfDualHaarAt ℚ v) = ∫⁻ x, g (c * x) * (modulus c : ℝ≥0∞) ∂(selfDualHaarAt ℚ v) := by
  rw [lintegral_mul_const' _ _ ENNReal.coe_ne_top]
  have h := lintegral_mul_left_selfDualHaarAt ℚ v (Units.mk0 c hc) g
  rw [Units.val_mk0] at h
  rw [h, mul_comm ((modulus c : ℝ≥0∞))⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel (modulus_ennreal_ne_zero v hc) ENNReal.coe_ne_top, mul_one]

private theorem lintegral_mulMeasure_comp_mul_left {c : v.adicCompletion ℚ} (hc : c ≠ 0)
    (g : v.adicCompletion ℚ → ℝ≥0∞) :
    ∫⁻ x, g (c * x) ∂(mulMeasure (selfDualHaarAt ℚ v)) = ∫⁻ x, g x ∂(mulMeasure (selfDualHaarAt ℚ v)) := by
  have h := map_mul_left_mulMeasure ℚ v (Units.mk0 c hc)
  rw [Units.val_mk0] at h
  calc ∫⁻ x, g (c * x) ∂(mulMeasure (selfDualHaarAt ℚ v))
      = ∫⁻ x, g x ∂(Measure.map (fun x => c * x) (mulMeasure (selfDualHaarAt ℚ v))) :=
        (lintegral_map_equiv g (MeasurableEquiv.mulLeft₀ c hc)).symm
    _ = ∫⁻ x, g x ∂(mulMeasure (selfDualHaarAt ℚ v)) := by rw [h]

private noncomputable def invEquiv : v.adicCompletion ℚ ≃ᵐ v.adicCompletion ℚ where
  toFun := fun x => x⁻¹
  invFun := fun x => x⁻¹
  left_inv := fun x => inv_inv x
  right_inv := fun x => inv_inv x
  measurable_toFun := measurable_inv
  measurable_invFun := measurable_inv

private theorem lintegral_mulMeasure_comp_inv (g : v.adicCompletion ℚ → ℝ≥0∞) :
    ∫⁻ x, g x⁻¹ ∂(mulMeasure (selfDualHaarAt ℚ v)) = ∫⁻ x, g x ∂(mulMeasure (selfDualHaarAt ℚ v)) := by
  calc ∫⁻ x, g x⁻¹ ∂(mulMeasure (selfDualHaarAt ℚ v))
      = ∫⁻ x, g x ∂(Measure.map (fun x : v.adicCompletion ℚ => x⁻¹) (mulMeasure (selfDualHaarAt ℚ v))) :=
        (lintegral_map_equiv g (invEquiv v)).symm
    _ = ∫⁻ x, g x ∂(mulMeasure (selfDualHaarAt ℚ v)) := by rw [map_inv_mulMeasure_selfDualHaarAt v]

private theorem lintegral_selfDualHaarAt_comp_inv (g : v.adicCompletion ℚ → ℝ≥0∞) :
    ∫⁻ x, g x⁻¹ ∂(selfDualHaarAt ℚ v) =
      ∫⁻ x, g x * ((modulus x : ℝ≥0∞) ^ 2)⁻¹ ∂(selfDualHaarAt ℚ v) := by
  rw [lintegral_selfDualHaarAt_eq_mulMeasure, lintegral_selfDualHaarAt_eq_mulMeasure]
  refine Eq.trans ?_ (lintegral_mulMeasure_comp_inv v
    (fun x => g x * ((modulus x : ℝ≥0∞) ^ 2)⁻¹ * (modulus x : ℝ≥0∞)))
  refine lintegral_congr_ae ?_
  filter_upwards [ae_ne_zero_mulMeasure v] with x hx
  have h0 : (modulus x : ℝ≥0∞) ≠ 0 := modulus_ennreal_ne_zero v hx
  rw [modulus_ennreal_inv v hx, ENNReal.inv_pow, inv_inv, sq, mul_assoc, mul_assoc,
    ENNReal.mul_inv_cancel h0 ENNReal.coe_ne_top, mul_one]

private theorem lintegral_prod_five {μ₁ μ₂ μ₃ μ₄ μ₅ : Measure (v.adicCompletion ℚ)}
    [SFinite μ₂] [SFinite μ₃] [SFinite μ₄] [SFinite μ₅]
    {f : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(μ₁.prod (μ₂.prod (μ₃.prod (μ₄.prod μ₅)))) =
      ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, ∫⁻ e, f (a, b, c, d, e) ∂μ₅ ∂μ₄ ∂μ₃ ∂μ₂ ∂μ₁ := by
  rw [lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun a => ?_
  have ha : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      f (a, y) := hf.comp measurable_prodMk_left
  rw [lintegral_prod _ ha.aemeasurable]
  refine lintegral_congr fun b => ?_
  have hb : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => f (a, b, y) :=
    ha.comp measurable_prodMk_left
  rw [lintegral_prod _ hb.aemeasurable]
  refine lintegral_congr fun c => ?_
  have hc : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ => f (a, b, c, y) :=
    hb.comp measurable_prodMk_left
  rw [lintegral_prod _ hc.aemeasurable]

private theorem lintegral_prod_two_three {μ₁ μ₂ μ₃ μ₄ μ₅ : Measure (v.adicCompletion ℚ)}
    [SFinite μ₁] [SFinite μ₂] [SFinite μ₃] [SFinite μ₄] [SFinite μ₅]
    {f : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂((μ₁.prod μ₂).prod (μ₃.prod (μ₄.prod μ₅))) =
      ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, ∫⁻ e, f ((a, b), c, d, e) ∂μ₅ ∂μ₄ ∂μ₃ ∂μ₂ ∂μ₁ := by
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ (hf.lintegral_prod_right').aemeasurable]
  refine lintegral_congr fun a => lintegral_congr fun b => ?_
  have hb : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => f ((a, b), y) :=
    hf.comp measurable_prodMk_left
  rw [lintegral_prod _ hb.aemeasurable]
  refine lintegral_congr fun c => ?_
  have hc : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ => f ((a, b), c, y) :=
    hb.comp measurable_prodMk_left
  rw [lintegral_prod _ hc.aemeasurable]

private theorem lintegral_mul_const_three {μ₁ μ₂ μ₃ : Measure (v.adicCompletion ℚ)}
    (f : v.adicCompletion ℚ → v.adicCompletion ℚ → v.adicCompletion ℚ → ℝ≥0∞) {r : ℝ≥0∞} (hr : r ≠ ∞) :
    (∫⁻ a, ∫⁻ b, ∫⁻ c, f a b c ∂μ₃ ∂μ₂ ∂μ₁) * r = ∫⁻ a, ∫⁻ b, ∫⁻ c, f a b c * r ∂μ₃ ∂μ₂ ∂μ₁ := by
  rw [← lintegral_mul_const' _ _ hr]
  refine lintegral_congr fun a => ?_
  rw [← lintegral_mul_const' _ _ hr]
  refine lintegral_congr fun b => ?_
  rw [← lintegral_mul_const' _ _ hr]

private theorem lintegral_mul_const_four {μ₁ μ₂ μ₃ μ₄ : Measure (v.adicCompletion ℚ)}
    (f : v.adicCompletion ℚ → v.adicCompletion ℚ → v.adicCompletion ℚ → v.adicCompletion ℚ → ℝ≥0∞)
    {r : ℝ≥0∞} (hr : r ≠ ∞) :
    (∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, f a b c d ∂μ₄ ∂μ₃ ∂μ₂ ∂μ₁) * r =
      ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, f a b c d * r ∂μ₄ ∂μ₃ ∂μ₂ ∂μ₁ := by
  rw [← lintegral_mul_const' _ _ hr]
  refine lintegral_congr fun a => ?_
  rw [lintegral_mul_const_three v (f a) hr]

private noncomputable def unfoldMap
    (z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
  ((z.2.2.2.1, z.2.2.2.2 / z.2.2.2.1),
    ((z.2.2.1 - z.2.2.2.2 / z.1 * z.2.1)⁻¹,
      (z.2.2.2.2 / z.1 / (z.2.2.1 - z.2.2.2.2 / z.1 * z.2.1),
        (z.2.2.2.2 / z.1 - z.2.2.1 * (z.2.2.2.1 / z.1)) / (1 - z.2.2.2.1 / z.1 * z.2.1))))

private noncomputable def unfoldDensity
    (y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℝ≥0∞ :=
  (modulus y.1.1 : ℝ≥0∞) ^ 2 * (modulus y.1.2 : ℝ≥0∞) * ((modulus (y.2.2.1 - y.2.1 * y.2.2.2) : ℝ≥0∞) ^ 2)⁻¹

private theorem measurable_unfoldMap : Measurable (unfoldMap v) := by
  have h1 : Measurable fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ × v.adicCompletion ℚ => z.1 := measurable_fst
  have h2 : Measurable fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ × v.adicCompletion ℚ => z.2.1 := measurable_snd.fst
  have h3 : Measurable fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ × v.adicCompletion ℚ => z.2.2.1 := measurable_snd.snd.fst
  have h4 : Measurable fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ × v.adicCompletion ℚ => z.2.2.2.1 := measurable_snd.snd.snd.fst
  have h5 : Measurable fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ × v.adicCompletion ℚ => z.2.2.2.2 := measurable_snd.snd.snd.snd
  have hu : Measurable fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ × v.adicCompletion ℚ => z.2.2.1 - z.2.2.2.2 / z.1 * z.2.1 := h3.sub ((h5.div h1).mul h2)
  exact (h4.prodMk (h5.div h4)).prodMk (hu.inv.prodMk (((h5.div h1).div hu).prodMk
    (((h5.div h1).sub (h3.mul (h4.div h1))).div (measurable_const.sub ((h4.div h1).mul h2)))))

private theorem measurable_unfoldDensity : Measurable (unfoldDensity v) := by
  have hN := measurable_modulus_ennreal v
  refine (((hN.comp measurable_fst.fst).pow_const 2).mul (hN.comp measurable_fst.snd)).mul ?_
  exact ((hN.comp (measurable_snd.snd.fst.sub (measurable_snd.fst.mul measurable_snd.snd.snd))).pow_const 2).inv

private noncomputable def subst₀
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
  (y.2.2.1, y.2.2.2.1, y.2.2.2.2, y.1, y.2.1)

private noncomputable def subst₁
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
  subst₀ v (y.1, y.2.1, y.2.2.1, y.2.2.2.1, y.2.2.2.2 + y.2.1 / y.2.2.1 * y.2.2.2.1)

private noncomputable def subst₂
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
  subst₁ v (y.1, y.1 * y.2.1, y.2.2.1, y.2.2.2.1, y.2.2.2.2)

private noncomputable def subst₃
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
  subst₂ v (y.1, y.2.1, y.2.2.1, y.2.2.1 / y.1 + (-1) * y.2.2.2.1⁻¹, y.2.2.2.2)

private noncomputable def subst₄
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
  subst₃ v (y.1, y.2.1, ((y.1 * y.2.1)⁻¹ * y.2.2.1)⁻¹, y.2.2.2.1, y.2.2.2.2)

section Projections

private theorem measurable_proj₁ : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ ×
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => y.1 := measurable_fst
private theorem measurable_proj₂ : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ ×
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => y.2.1 := measurable_snd.fst
private theorem measurable_proj₃ : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ ×
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => y.2.2.1 := measurable_snd.snd.fst
private theorem measurable_proj₄ : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ ×
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => y.2.2.2.1 := measurable_snd.snd.snd.fst
private theorem measurable_proj₅ : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ ×
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => y.2.2.2.2 := measurable_snd.snd.snd.snd

end Projections
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

private theorem measurable_subst₀ : Measurable (subst₀ v) :=
  (measurable_proj₃ v).prodMk ((measurable_proj₄ v).prodMk ((measurable_proj₅ v).prodMk
    ((measurable_proj₁ v).prodMk (measurable_proj₂ v))))

private theorem measurable_subst₁ : Measurable (subst₁ v) :=
  (measurable_subst₀ v).comp ((measurable_proj₁ v).prodMk ((measurable_proj₂ v).prodMk ((measurable_proj₃ v).prodMk
    ((measurable_proj₄ v).prodMk ((measurable_proj₅ v).add (((measurable_proj₂ v).div (measurable_proj₃ v)).mul
      (measurable_proj₄ v)))))))

private theorem measurable_subst₂ : Measurable (subst₂ v) :=
  (measurable_subst₁ v).comp ((measurable_proj₁ v).prodMk (((measurable_proj₁ v).mul (measurable_proj₂ v)).prodMk
    ((measurable_proj₃ v).prodMk ((measurable_proj₄ v).prodMk (measurable_proj₅ v)))))

private theorem measurable_subst₃ : Measurable (subst₃ v) :=
  (measurable_subst₂ v).comp ((measurable_proj₁ v).prodMk ((measurable_proj₂ v).prodMk ((measurable_proj₃ v).prodMk
    ((((measurable_proj₃ v).div (measurable_proj₁ v)).add (measurable_const.mul (measurable_proj₄ v).inv)).prodMk
      (measurable_proj₅ v)))))

private theorem measurable_subst₄ : Measurable (subst₄ v) :=
  (measurable_subst₃ v).comp ((measurable_proj₁ v).prodMk ((measurable_proj₂ v).prodMk
    (((((measurable_proj₁ v).mul (measurable_proj₂ v)).inv.mul (measurable_proj₃ v)).inv).prodMk
      ((measurable_proj₄ v).prodMk (measurable_proj₅ v)))))

private noncomputable def reorderEquiv :
    (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) ≃ᵐ
      (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  (MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodAssoc.symm).trans
    (MeasurableEquiv.prodComm.trans ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      MeasurableEquiv.prodAssoc).trans MeasurableEquiv.prodAssoc))

private theorem measurePreserving_reorderEquiv :
    MeasurePreserving (reorderEquiv v)
      ((mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod
        ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))))
      ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod
        ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))) := by
  have h1 := (measurePreserving_prodAssoc (mulMeasure (selfDualHaarAt ℚ v)) (selfDualHaarAt ℚ v)
    ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))).symm _
  have h2 := (measurePreserving_prodAssoc ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))
    (selfDualHaarAt ℚ v) ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))).symm _
  have h3 : MeasurePreserving MeasurableEquiv.prodComm
      ((((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)).prod
        ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
      (((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)).prod
        (((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))) :=
    Measure.measurePreserving_swap
  have h4 := (MeasurePreserving.id ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))).prod
    (measurePreserving_prodAssoc (mulMeasure (selfDualHaarAt ℚ v)) (selfDualHaarAt ℚ v) (selfDualHaarAt ℚ v))
  have h5 := measurePreserving_prodAssoc (selfDualHaarAt ℚ v) (selfDualHaarAt ℚ v)
    ((mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

section Chain

variable (G : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ ×
  v.adicCompletion ℚ → ℝ≥0∞)

private noncomputable def body₀
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℝ≥0∞ :=
  G (unfoldMap v (subst₀ v y))

private noncomputable def body₁
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℝ≥0∞ :=
  G (unfoldMap v (subst₁ v y))

private noncomputable def body₂
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℝ≥0∞ :=
  G (unfoldMap v (subst₂ v y)) * (modulus y.1 : ℝ≥0∞)

private noncomputable def body₃
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℝ≥0∞ :=
  G (unfoldMap v (subst₃ v y)) * (modulus y.1 : ℝ≥0∞) * ((modulus y.2.2.2.1 : ℝ≥0∞) ^ 2)⁻¹

private noncomputable def body₄
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℝ≥0∞ :=
  G (unfoldMap v (subst₄ v y)) * (modulus y.1 : ℝ≥0∞) * ((modulus y.2.2.2.1 : ℝ≥0∞) ^ 2)⁻¹

private noncomputable def body₅
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℝ≥0∞ :=
  body₄ v G (y.1, y.2.1, y.2.2.1, y.2.2.2.1⁻¹ * ((-1) * y.2.2.2.2 + y.2.2.1), y.2.2.2.1) *
    (modulus y.2.2.2.1⁻¹ : ℝ≥0∞)

private noncomputable def body₆
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℝ≥0∞ :=
  body₅ v G (y.1, y.2.1, y.2.2.1, y.2.2.2.1⁻¹, y.2.2.2.2) * (modulus y.2.2.2.1⁻¹ : ℝ≥0∞)

private noncomputable def body₇
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℝ≥0∞ :=
  body₆ v G (y.1, y.2.1, y.2.2.1⁻¹ * y.2.2.2.1, y.2.2.1, y.2.2.2.2)

private noncomputable def body₈
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℝ≥0∞ :=
  body₇ v G y * (modulus y.2.1 : ℝ≥0∞)

private noncomputable def body₉
    (y : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℝ≥0∞ :=
  body₈ v G y * (modulus y.1 : ℝ≥0∞)

variable {G}

private theorem measurable_body₄ (hG : Measurable G) : Measurable (body₄ v G) :=
  ((hG.comp ((measurable_unfoldMap v).comp (measurable_subst₄ v))).mul
    ((measurable_modulus_ennreal v).comp (measurable_proj₁ v))).mul
    (((measurable_modulus_ennreal v).comp (measurable_proj₄ v)).pow_const 2).inv

private theorem measurable_body₅ (hG : Measurable G) : Measurable (body₅ v G) :=
  ((measurable_body₄ v hG).comp ((measurable_proj₁ v).prodMk ((measurable_proj₂ v).prodMk ((measurable_proj₃ v).prodMk
    (((measurable_proj₄ v).inv.mul ((measurable_const.mul (measurable_proj₅ v)).add (measurable_proj₃ v))).prodMk
      (measurable_proj₄ v)))))).mul ((measurable_modulus_ennreal v).comp (measurable_proj₄ v).inv)

private theorem measurable_body₆ (hG : Measurable G) : Measurable (body₆ v G) :=
  ((measurable_body₅ v hG).comp ((measurable_proj₁ v).prodMk ((measurable_proj₂ v).prodMk ((measurable_proj₃ v).prodMk
    ((measurable_proj₄ v).inv.prodMk (measurable_proj₅ v)))))).mul
    ((measurable_modulus_ennreal v).comp (measurable_proj₄ v).inv)

private theorem unfold_stage₀ (hG : Measurable G) :
    ∫⁻ z, G (unfoldMap v z) ∂((mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod
        ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))) =
      ∫⁻ β, ∫⁻ γ, ∫⁻ a, ∫⁻ x, ∫⁻ α, body₀ v G (β, γ, a, x, α)
        ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))
        ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) := by
  have hF : Measurable fun z => G (unfoldMap v z) := hG.comp (measurable_unfoldMap v)
  have h1 : ∫⁻ z, G (unfoldMap v z) ∂((mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod
      ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))) =
      ∫⁻ w, G (unfoldMap v ((reorderEquiv v).symm w)) ∂((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod
        ((mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))) := by
    rw [← (measurePreserving_reorderEquiv v).map_eq, lintegral_map_equiv]
    simp only [MeasurableEquiv.symm_apply_apply]
  have hF' : Measurable fun w => G (unfoldMap v ((reorderEquiv v).symm w)) :=
    hF.comp (reorderEquiv v).symm.measurable
  rw [h1, lintegral_prod_five v hF']
  rfl

private theorem unfold_stage₁ (β γ a x : v.adicCompletion ℚ) :
    ∫⁻ α, body₀ v G (β, γ, a, x, α) ∂(selfDualHaarAt ℚ v) = ∫⁻ u, body₁ v G (β, γ, a, x, u) ∂(selfDualHaarAt ℚ v) :=
  (lintegral_add_right_eq_self (μ := selfDualHaarAt ℚ v) (fun α => body₀ v G (β, γ, a, x, α)) (γ / a * x)).symm

private theorem unfold_stage₂ {β : v.adicCompletion ℚ} (hβ : β ≠ 0) (P : v.adicCompletion ℚ → ℝ≥0∞) :
    ∫⁻ γ, P γ ∂(selfDualHaarAt ℚ v) = ∫⁻ t, P (β * t) * (modulus β : ℝ≥0∞) ∂(selfDualHaarAt ℚ v) :=
  lintegral_selfDualHaarAt_comp_mul_left v hβ P

private theorem unfold_stage₃ (e : v.adicCompletion ℚ) (P : v.adicCompletion ℚ → ℝ≥0∞) :
    ∫⁻ x, P x ∂(selfDualHaarAt ℚ v) =
      ∫⁻ d, P (e + (-1) * d⁻¹) * ((modulus d : ℝ≥0∞) ^ 2)⁻¹ ∂(selfDualHaarAt ℚ v) := by
  calc ∫⁻ x, P x ∂(selfDualHaarAt ℚ v) = ∫⁻ x, P (e + x) ∂(selfDualHaarAt ℚ v) :=
        (lintegral_add_left_eq_self (μ := selfDualHaarAt ℚ v) P e).symm
    _ = ∫⁻ x, P (e + (-1) * x) * (modulus (-1 : v.adicCompletion ℚ) : ℝ≥0∞) ∂(selfDualHaarAt ℚ v) :=
        lintegral_selfDualHaarAt_comp_mul_left v (neg_ne_zero.mpr one_ne_zero) (fun x => P (e + x))
    _ = ∫⁻ x, P (e + (-1) * x) ∂(selfDualHaarAt ℚ v) := by simp only [modulus_ennreal_neg_one, mul_one]
    _ = ∫⁻ d, P (e + (-1) * d⁻¹) * ((modulus d : ℝ≥0∞) ^ 2)⁻¹ ∂(selfDualHaarAt ℚ v) := by
        simpa only [inv_inv] using lintegral_selfDualHaarAt_comp_inv v (fun y => P (e + (-1) * y⁻¹))

private theorem unfold_stage₄ {c : v.adicCompletion ℚ} (hc : c ≠ 0) (P : v.adicCompletion ℚ → ℝ≥0∞) :
    ∫⁻ a, P a ∂(mulMeasure (selfDualHaarAt ℚ v)) =
      ∫⁻ g, P ((c⁻¹ * g)⁻¹) ∂(mulMeasure (selfDualHaarAt ℚ v)) := by
  rw [← lintegral_mulMeasure_comp_inv v P,
    ← lintegral_mulMeasure_comp_mul_left v (inv_ne_zero hc) (fun a => P a⁻¹)]

private theorem unfold_stage₅ {u : v.adicCompletion ℚ} (hu : u ≠ 0) (g : v.adicCompletion ℚ)
    (P : v.adicCompletion ℚ → ℝ≥0∞) :
    ∫⁻ d, P d ∂(selfDualHaarAt ℚ v) =
      ∫⁻ w, P (u⁻¹ * ((-1) * w + g)) * (modulus u⁻¹ : ℝ≥0∞) ∂(selfDualHaarAt ℚ v) := by
  rw [lintegral_selfDualHaarAt_comp_mul_left v (inv_ne_zero hu) P,
    ← lintegral_add_right_eq_self (μ := selfDualHaarAt ℚ v)
      (fun d => P (u⁻¹ * d) * (modulus u⁻¹ : ℝ≥0∞)) g,
    lintegral_selfDualHaarAt_comp_mul_left v (neg_ne_zero.mpr one_ne_zero)
      (fun d => P (u⁻¹ * (d + g)) * (modulus u⁻¹ : ℝ≥0∞)), modulus_ennreal_neg_one]
  simp only [mul_one]

private theorem unfold_stage₆ (P : v.adicCompletion ℚ → ℝ≥0∞) :
    ∫⁻ u, P u ∂(selfDualHaarAt ℚ v) =
      ∫⁻ u, P u⁻¹ * (modulus u⁻¹ : ℝ≥0∞) ∂(mulMeasure (selfDualHaarAt ℚ v)) := by
  rw [lintegral_selfDualHaarAt_eq_mulMeasure,
    ← lintegral_mulMeasure_comp_inv v (fun u => P u * (modulus u : ℝ≥0∞))]

private theorem unfold_stage₇ {u : v.adicCompletion ℚ} (hu : u ≠ 0) (P : v.adicCompletion ℚ → ℝ≥0∞) :
    ∫⁻ g, P g ∂(mulMeasure (selfDualHaarAt ℚ v)) =
      ∫⁻ w, P (u⁻¹ * w) ∂(mulMeasure (selfDualHaarAt ℚ v)) :=
  (lintegral_mulMeasure_comp_mul_left v (inv_ne_zero hu) P).symm

private theorem body₉_eq {β t u w x : v.adicCompletion ℚ} (hβ : β ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0)
    (hw : w ≠ 0) (hd : w - u * x ≠ 0) :
    body₉ v G (β, t, u, w, x) = G ((β, t), u, w, x) * unfoldDensity v ((β, t), u, w, x) := by
  obtain ⟨D, hD⟩ : ∃ D, w - u * x = D := ⟨_, rfl⟩
  have hD0 : D ≠ 0 := hD ▸ hd
  have hx : x = (w - D) / u := eq_div_of_mul_eq hu (by rw [← hD]; ring)
  subst hx
  have hNu : (modulus u : ℝ≥0∞) ≠ 0 := modulus_ennreal_ne_zero v hu
  have hA : ((β * t)⁻¹ * (u⁻¹ * w))⁻¹ = β * t * u / w := by
    field_simp
  have hdd : u * ((-1) * ((w - D) / u) + u⁻¹ * w) = D := by
    field_simp
    ring
  have hwD : w - u * ((w - D) / u) = D := by
    field_simp
    ring
  have hB : (1 : v.adicCompletion ℚ) - β / (β * t * u / w) * (β * t * u / w / β + (-1) * D⁻¹) = w / (t * u * D) := by
    field_simp
    ring
  have hBne : (1 : v.adicCompletion ℚ) - β / (β * t * u / w) * (β * t * u / w / β + (-1) * D⁻¹) ≠ 0 := by
    rw [hB]
    exact div_ne_zero hw (mul_ne_zero (mul_ne_zero ht hu) hD0)
  have hfac : ∀ r : ℝ≥0∞,
      r * ((modulus β : ℝ≥0∞) ^ 2 * (modulus t : ℝ≥0∞) * ((modulus D : ℝ≥0∞) ^ 2)⁻¹) =
        r * (modulus β : ℝ≥0∞) * ((modulus D : ℝ≥0∞) ^ 2)⁻¹ * (modulus u : ℝ≥0∞) * ((modulus u : ℝ≥0∞))⁻¹ *
          (modulus t : ℝ≥0∞) * (modulus β : ℝ≥0∞) := by
    intro r
    rw [mul_assoc (r * (modulus β : ℝ≥0∞) * ((modulus D : ℝ≥0∞) ^ 2)⁻¹),
      ENNReal.mul_inv_cancel hNu ENNReal.coe_ne_top, mul_one, sq]
    ring
  simp only [body₉, body₈, body₇, body₆, body₅, body₄, subst₄, subst₃, subst₂, subst₁, subst₀, unfoldMap,
    unfoldDensity, inv_inv]
  rw [hA, hdd, hwD, modulus_ennreal_inv v hu, hfac]
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact mul_div_cancel_left₀ t hβ
  · show (u⁻¹ + β * t / (β * t * u / w) * (β * t * u / w / β + (-1) * D⁻¹) -
        β * t / (β * t * u / w) * (β * t * u / w / β + (-1) * D⁻¹))⁻¹ = u
    rw [add_sub_cancel_right, inv_inv]
  · show β * t / (β * t * u / w) / (u⁻¹ + β * t / (β * t * u / w) * (β * t * u / w / β + (-1) * D⁻¹) -
        β * t / (β * t * u / w) * (β * t * u / w / β + (-1) * D⁻¹)) = w
    rw [add_sub_cancel_right]
    field_simp
  · show (β * t / (β * t * u / w) - (u⁻¹ + β * t / (β * t * u / w) * (β * t * u / w / β + (-1) * D⁻¹)) *
        (β / (β * t * u / w))) / (1 - β / (β * t * u / w) * (β * t * u / w / β + (-1) * D⁻¹)) = (w - D) / u
    rw [div_eq_iff hBne]
    field_simp
    ring

private theorem lintegral_comp_unfoldMap (hG : Measurable G) :
    ∫⁻ z, G (unfoldMap v z) ∂((mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod
        ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))) =
      ∫⁻ y, G y * unfoldDensity v y ∂(((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
        ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))) := by
  have hβ0 := ae_ne_selfDualHaarAt v 0
  have hM0 := ae_ne_zero_mulMeasure v
  calc ∫⁻ z, G (unfoldMap v z) ∂((mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod
        ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))))
      = ∫⁻ β, ∫⁻ γ, ∫⁻ a, ∫⁻ x, ∫⁻ α, body₀ v G (β, γ, a, x, α)
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) := unfold_stage₀ v hG

    _ = ∫⁻ β, ∫⁻ γ, ∫⁻ a, ∫⁻ x, ∫⁻ u, body₁ v G (β, γ, a, x, u)
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) := by
        refine lintegral_congr fun β => lintegral_congr fun γ => lintegral_congr fun a =>
          lintegral_congr fun x => ?_
        exact unfold_stage₁ v β γ a x

    _ = ∫⁻ β, ∫⁻ t, ∫⁻ a, ∫⁻ x, ∫⁻ u, body₂ v G (β, t, a, x, u)
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hβ0] with β hβ
        refine (unfold_stage₂ v hβ (fun γ => ∫⁻ a, ∫⁻ x, ∫⁻ u, body₁ v G (β, γ, a, x, u)
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v)))).trans ?_
        refine lintegral_congr fun t => ?_
        exact lintegral_mul_const_three v (fun a x u => body₁ v G (β, β * t, a, x, u)) ENNReal.coe_ne_top

    _ = ∫⁻ β, ∫⁻ t, ∫⁻ a, ∫⁻ d, ∫⁻ u, body₃ v G (β, t, a, d, u)
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) := by
        refine lintegral_congr fun β => lintegral_congr fun t => lintegral_congr fun a => ?_
        refine (unfold_stage₃ v (a / β) (fun x => ∫⁻ u, body₂ v G (β, t, a, x, u) ∂(selfDualHaarAt ℚ v))).trans ?_
        refine lintegral_congr_ae ?_
        filter_upwards [hβ0] with d hd
        have hfin : ((modulus d : ℝ≥0∞) ^ 2)⁻¹ ≠ ∞ :=
          ENNReal.inv_ne_top.mpr (pow_ne_zero 2 (modulus_ennreal_ne_zero v hd))
        exact (lintegral_mul_const' _ (fun u => body₂ v G (β, t, a, a / β + (-1) * d⁻¹, u)) hfin).symm

    _ = ∫⁻ β, ∫⁻ t, ∫⁻ g, ∫⁻ d, ∫⁻ u, body₄ v G (β, t, g, d, u)
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hβ0] with β hβ
        refine lintegral_congr_ae ?_
        filter_upwards [hβ0] with t ht
        exact unfold_stage₄ v (mul_ne_zero hβ ht)
          (fun a => ∫⁻ d, ∫⁻ u, body₃ v G (β, t, a, d, u) ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v))

    _ = ∫⁻ β, ∫⁻ t, ∫⁻ g, ∫⁻ u, ∫⁻ d, body₄ v G (β, t, g, d, u)
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) := by
        refine lintegral_congr fun β => lintegral_congr fun t => lintegral_congr fun g => ?_
        exact lintegral_lintegral_swap (((measurable_body₄ v hG).comp (measurable_const.prodMk
          (measurable_const.prodMk (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))))).aemeasurable)

    _ = ∫⁻ β, ∫⁻ t, ∫⁻ g, ∫⁻ u, ∫⁻ w, body₅ v G (β, t, g, u, w)
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) := by
        refine lintegral_congr fun β => lintegral_congr fun t => lintegral_congr fun g => ?_
        refine lintegral_congr_ae ?_
        filter_upwards [hβ0] with u hu
        exact unfold_stage₅ v hu g (fun d => body₄ v G (β, t, g, d, u))

    _ = ∫⁻ β, ∫⁻ t, ∫⁻ g, ∫⁻ u, ∫⁻ w, body₆ v G (β, t, g, u, w)
          ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v)) ∂(mulMeasure (selfDualHaarAt ℚ v))
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) := by
        refine lintegral_congr fun β => lintegral_congr fun t => lintegral_congr fun g => ?_
        refine (unfold_stage₆ v (fun u => ∫⁻ w, body₅ v G (β, t, g, u, w) ∂(selfDualHaarAt ℚ v))).trans ?_
        refine lintegral_congr fun u => ?_
        exact (lintegral_mul_const' _ (fun w => body₅ v G (β, t, g, u⁻¹, w)) ENNReal.coe_ne_top).symm

    _ = ∫⁻ β, ∫⁻ t, ∫⁻ u, ∫⁻ g, ∫⁻ w, body₆ v G (β, t, g, u, w)
          ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v)) ∂(mulMeasure (selfDualHaarAt ℚ v))
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) := by
        refine lintegral_congr fun β => lintegral_congr fun t => ?_
        exact lintegral_lintegral_swap (((measurable_body₆ v hG).comp (measurable_const.prodMk
          (measurable_const.prodMk (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk
            measurable_snd))))).lintegral_prod_right').aemeasurable

    _ = ∫⁻ β, ∫⁻ t, ∫⁻ u, ∫⁻ w, ∫⁻ x, body₇ v G (β, t, u, w, x)
          ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v)) ∂(mulMeasure (selfDualHaarAt ℚ v))
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) := by
        refine lintegral_congr fun β => lintegral_congr fun t => ?_
        refine lintegral_congr_ae ?_
        filter_upwards [hM0] with u hu
        exact unfold_stage₇ v hu (fun g => ∫⁻ x, body₆ v G (β, t, g, u, x) ∂(selfDualHaarAt ℚ v))

    _ = ∫⁻ β, ∫⁻ t, ∫⁻ u, ∫⁻ w, ∫⁻ x, body₈ v G (β, t, u, w, x)
          ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v)) ∂(mulMeasure (selfDualHaarAt ℚ v))
          ∂(mulMeasure (selfDualHaarAt ℚ v)) ∂(selfDualHaarAt ℚ v) := by
        refine lintegral_congr fun β => ?_
        refine (lintegral_selfDualHaarAt_eq_mulMeasure v (fun t => ∫⁻ u, ∫⁻ w, ∫⁻ x, body₇ v G (β, t, u, w, x)
          ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v)) ∂(mulMeasure (selfDualHaarAt ℚ v)))).trans ?_
        refine lintegral_congr fun t => ?_
        exact lintegral_mul_const_three v (fun u w x => body₇ v G (β, t, u, w, x)) ENNReal.coe_ne_top

    _ = ∫⁻ β, ∫⁻ t, ∫⁻ u, ∫⁻ w, ∫⁻ x, body₉ v G (β, t, u, w, x)
          ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v)) ∂(mulMeasure (selfDualHaarAt ℚ v))
          ∂(mulMeasure (selfDualHaarAt ℚ v)) ∂(mulMeasure (selfDualHaarAt ℚ v)) := by
        refine (lintegral_selfDualHaarAt_eq_mulMeasure v (fun β => ∫⁻ t, ∫⁻ u, ∫⁻ w, ∫⁻ x,
          body₈ v G (β, t, u, w, x) ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))
          ∂(mulMeasure (selfDualHaarAt ℚ v)) ∂(mulMeasure (selfDualHaarAt ℚ v)))).trans ?_
        refine lintegral_congr fun β => ?_
        exact lintegral_mul_const_four v (fun t u w x => body₈ v G (β, t, u, w, x)) ENNReal.coe_ne_top

    _ = ∫⁻ y, G y * unfoldDensity v y ∂(((mulMeasure (selfDualHaarAt ℚ v)).prod
          (mulMeasure (selfDualHaarAt ℚ v))).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod
            ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))) := by
        rw [lintegral_prod_two_three v (hG.fun_mul (measurable_unfoldDensity v))]
        refine lintegral_congr_ae ?_
        filter_upwards [hM0] with β hβ
        refine lintegral_congr_ae ?_
        filter_upwards [hM0] with t ht
        refine lintegral_congr_ae ?_
        filter_upwards [hM0] with u hu
        refine lintegral_congr_ae ?_
        filter_upwards [hM0] with w hw
        refine lintegral_congr_ae ?_
        filter_upwards [ae_ne_selfDualHaarAt v (u⁻¹ * w)] with x hx
        have hd : w - u * x ≠ 0 := fun h => hx ((eq_inv_mul_iff_mul_eq₀ hu).mpr (sub_eq_zero.mp h).symm)
        exact body₉_eq v hβ ht hu hw hd

end Chain
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

private theorem map_unfoldMap :
    Measure.map (unfoldMap v) ((mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod
        ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))) =
      (((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
        ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod
          (selfDualHaarAt ℚ v)))).withDensity (unfoldDensity v) := by
  refine Measure.ext fun S hS => ?_
  have hind : Measurable (S.indicator 1 : _ → ℝ≥0∞) := measurable_one.indicator hS
  rw [withDensity_apply _ hS, ← lintegral_indicator hS, ← lintegral_indicator_one hS,
    lintegral_map hind (measurable_unfoldMap v), lintegral_comp_unfoldMap v hind]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ S
  · simp only [Set.indicator_of_mem hy, Pi.one_apply, one_mul]
  · simp only [Set.indicator_of_notMem hy, zero_mul]

end UnfoldingMeasure
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell"
end Part32
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"

section Part33

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal"
open scoped ENNReal NNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 integrable_coupledIntegrand"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section NullSlices

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem measurableSet_ne_zero {X : Type*} [MeasurableSpace X] {f : X → v.adicCompletion ℚ}
    (hf : Measurable f) : MeasurableSet {z : X | f z ≠ 0} :=
  (hf (measurableSet_singleton 0)).compl

private theorem eq_of_sub_div_mul_eq_zero {a x α γ : v.adicCompletion ℚ} (ha : a ≠ 0) (hx : x ≠ 0)
    (h : α - γ / a * x = 0) : γ = α * a / x := by
  rw [eq_div_iff hx, sub_eq_zero.mp h, div_mul_eq_mul_div, div_mul_cancel₀ _ ha]

private theorem eq_of_one_sub_div_mul_eq_zero {a x β : v.adicCompletion ℚ} (ha : a ≠ 0) (hx : x ≠ 0)
    (h : 1 - β / a * x = 0) : β = a / x := by
  rw [eq_div_iff hx]
  have h1 : β * x / a = 1 := by
    rw [← div_mul_eq_mul_div]
    exact (sub_eq_zero.mp h).symm
  exact (div_eq_one_iff_eq ha).mp h1

private theorem ae_unfold_source :
    ∀ᵐ z ∂((mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod
        ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))),
      z.1 ≠ 0 ∧ z.2.2.2.1 ≠ 0 ∧ z.2.2.2.2 ≠ 0 ∧ z.2.2.1 - z.2.2.2.2 / z.1 * z.2.1 ≠ 0 ∧
        1 - z.2.2.2.1 / z.1 * z.2.1 ≠ 0 := by
  have h1 : Measurable fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ => z.1 := measurable_fst
  have h2 : Measurable fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ => z.2.1 := measurable_snd.fst
  have h3 : Measurable fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ => z.2.2.1 := measurable_snd.snd.fst
  have h4 : Measurable fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ => z.2.2.2.1 := measurable_snd.snd.snd.fst
  have h5 : Measurable fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ => z.2.2.2.2 := measurable_snd.snd.snd.snd
  have hU : Measurable fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ => z.2.2.1 - z.2.2.2.2 / z.1 * z.2.1 := h3.sub ((h5.div h1).mul h2)
  have hL : Measurable fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ => 1 - z.2.2.2.1 / z.1 * z.2.1 := measurable_const.sub ((h4.div h1).mul h2)
  have hS : MeasurableSet {z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ | z.1 ≠ 0 ∧ z.2.2.2.1 ≠ 0 ∧ z.2.2.2.2 ≠ 0 ∧ z.2.2.1 - z.2.2.2.2 / z.1 * z.2.1 ≠ 0 ∧
        1 - z.2.2.2.1 / z.1 * z.2.1 ≠ 0} :=
    (measurableSet_ne_zero v h1).inter ((measurableSet_ne_zero v h4).inter ((measurableSet_ne_zero v h5).inter
      ((measurableSet_ne_zero v hU).inter (measurableSet_ne_zero v hL))))
  refine (Measure.ae_prod_iff_ae_ae hS).2 ?_
  filter_upwards [ae_ne_zero_mulMeasure v] with a ha
  refine (Measure.ae_prod_iff_ae_ae (measurable_prodMk_left hS)).2 (Filter.Eventually.of_forall fun x => ?_)
  refine (Measure.ae_prod_iff_ae_ae (measurable_prodMk_left (measurable_prodMk_left hS))).2 ?_
  filter_upwards [ae_ne_selfDualHaarAt v 0] with α hα
  refine (Measure.ae_prod_iff_ae_ae (measurable_prodMk_left (measurable_prodMk_left (measurable_prodMk_left hS)))).2
    ?_
  filter_upwards [ae_ne_selfDualHaarAt v 0, ae_ne_selfDualHaarAt v (a / x)] with β hβ hβx
  filter_upwards [ae_ne_selfDualHaarAt v 0, ae_ne_selfDualHaarAt v (α * a / x)] with γ hγ hγx
  refine ⟨ha, hβ, hγ, ?_, ?_⟩
  · show α - γ / a * x ≠ 0
    intro h
    by_cases hx : x = 0
    · rw [hx, mul_zero, sub_zero] at h
      exact hα h
    · exact hγx (eq_of_sub_div_mul_eq_zero v ha hx h)
  · show 1 - β / a * x ≠ 0
    intro h
    by_cases hx : x = 0
    · rw [hx, mul_zero, sub_zero] at h
      exact one_ne_zero h
    · exact hβx (eq_of_one_sub_div_mul_eq_zero v ha hx h)

private theorem ae_unfold_target :
    ∀ᵐ y ∂(((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
        ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))),
      y.1.1 ≠ 0 ∧ y.1.2 ≠ 0 ∧ y.2.1 ≠ 0 ∧ y.2.2.1 - y.2.1 * y.2.2.2 ≠ 0 := by
  have hS : MeasurableSet {y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ | y.1.1 ≠ 0 ∧ y.1.2 ≠ 0 ∧ y.2.1 ≠ 0 ∧ y.2.2.1 - y.2.1 * y.2.2.2 ≠ 0} :=
    (measurableSet_ne_zero v measurable_fst.fst).inter ((measurableSet_ne_zero v measurable_fst.snd).inter
      ((measurableSet_ne_zero v measurable_snd.fst).inter
        (measurableSet_ne_zero v (measurable_snd.snd.fst.sub (measurable_snd.fst.mul measurable_snd.snd.snd)))))
  have hT : MeasurableSet {t : v.adicCompletion ℚ × v.adicCompletion ℚ | t.1 ≠ 0 ∧ t.2 ≠ 0} :=
    (measurableSet_ne_zero v measurable_fst).inter (measurableSet_ne_zero v measurable_snd)
  have ht : ∀ᵐ t ∂((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))), t.1 ≠ 0 ∧ t.2 ≠ 0 := by
    refine (Measure.ae_prod_iff_ae_ae hT).2 ?_
    filter_upwards [ae_ne_zero_mulMeasure v] with t₀ ht₀
    filter_upwards [ae_ne_zero_mulMeasure v] with t₁ ht₁
    exact ⟨ht₀, ht₁⟩
  refine (Measure.ae_prod_iff_ae_ae hS).2 ?_
  filter_upwards [ht] with t ht'
  refine (Measure.ae_prod_iff_ae_ae (measurable_prodMk_left hS)).2 ?_
  filter_upwards [ae_ne_zero_mulMeasure v] with u hu
  refine (Measure.ae_prod_iff_ae_ae (measurable_prodMk_left (measurable_prodMk_left hS))).2
    (Filter.Eventually.of_forall fun v' => ?_)
  filter_upwards [ae_ne_selfDualHaarAt v (v' / u)] with w hw
  refine ⟨ht'.1, ht'.2, hu, ?_⟩
  show v' - u * w ≠ 0
  intro h
  apply hw
  rw [eq_div_iff hu, mul_comm]
  exact (sub_eq_zero.mp h).symm

end NullSlices
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"
end Part33
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"

section Part34
set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal NumberField.StandardAddChar"
open scoped ENNReal NNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 integrable_coupledIntegrand"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualFiniteLevel

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def primedBall3 (c : ℤ) : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  {p | Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1 ∧
    Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c}

private noncomputable def jacquetPrimed3 (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) : ℂ :=
  ∫ p in primedBall3 v c,
    NumberField.StandardAddChar.psiLocal ℚ v (-(p.1 + p.2.1)) *
      cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 a x) ∂(jacquetHaar3 v)

private theorem setOf_valued_snd_le_eq (c : ℤ) :
    {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
        Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1} =
      {p | p.2.1 = 0 ∧ p.2.2 = 0} ∪ {p | p.2.1 ≠ 0 ∧ Valued.v (p.2.2 / p.2.1) ≤ WithZero.exp c} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_union]
  by_cases hβ : p.2.1 = 0
  · rw [hβ, map_zero, mul_zero, le_zero_iff, map_eq_zero]
    exact ⟨fun h => Or.inl ⟨rfl, h⟩, fun h => h.elim (fun h => h.2) fun h => absurd rfl h.1⟩
  · have hpos : 0 < Valued.v p.2.1 := zero_lt_iff.mpr ((Valuation.ne_zero_iff Valued.v).mpr hβ)
    rw [map_div₀, div_le_iff₀ hpos]
    exact ⟨fun h => Or.inr ⟨hβ, h⟩, fun h => h.elim (fun h => absurd h.1 hβ) fun h => h.2⟩

private theorem measurableSet_primedBall3 (c : ℤ) : MeasurableSet (primedBall3 v c) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hc : MeasurableSet {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} :=
    (isClosed_valued_le v c).measurableSet
  have h₁ : MeasurableSet {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
      Valued.v p.2.1 ≤ WithZero.exp c} :=
    hc.preimage measurable_snd.fst
  have h₂ : MeasurableSet {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
      Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1} := by
    rw [setOf_valued_snd_le_eq]
    refine (((measurableSet_singleton 0).preimage measurable_snd.fst).inter
      ((measurableSet_singleton 0).preimage measurable_snd.snd)).union
      (((measurableSet_singleton 0).preimage measurable_snd.fst).compl.inter
        (hc.preimage (measurable_snd.snd.div measurable_snd.fst)))
  have h₃ : MeasurableSet {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
      Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c} :=
    hc.preimage (measurable_fst.sub (measurable_snd.snd.div measurable_snd.fst))
  have hset : primedBall3 v c = {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
      Valued.v p.2.1 ≤ WithZero.exp c} ∩ {p | Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1} ∩
      {p | Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c} := by
    ext p
    simp only [primedBall3, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
  rw [hset]
  exact (h₁.inter h₂).inter h₃

private noncomputable def gaussFn (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (z : ℂ) (c : ℤ) (t : v.adicCompletion ℚ) : ℂ :=
  truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z

private noncomputable def coupledFn (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (c : ℤ)
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) : ℂ :=
  Φ ![p.1, p.2.1, p.2.2] *
      (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
      (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
      (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) * ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
      truncChar v c (p.2.2 / (p.2.1 - p.1 * p.2.2))

private noncomputable def targetFn (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (c : ℤ)
    (y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ) : ℂ :=
  gaussFn v (ν 0 * χ)⁻¹ (1 - s) c y.1.1 * gaussFn v (ν 1 * χ)⁻¹ (1 - s) c y.1.2 * coupledFn v ν Φ χ s c y.2

private noncomputable def sourceFn (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (c : ℤ)
    (z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℂ :=
  (primedBall3 v c).indicator (fun _ => (1 : ℂ)) z.2.2 *
      (psiLocal ℚ v (-(z.2.2.1 + z.2.2.2.1)) : ℂ) *
      ((charExt (ν 0) z.1)⁻¹ * ((‖z.1‖⁻¹ : ℝ) : ℂ) *
        (charExt (ν 1 * (ν 0)⁻¹) (1 - z.2.2.2.1 / z.1 * z.2.1) *
            charExt (ν 2 * (ν 1)⁻¹) (z.2.2.1 - z.2.2.2.2 / z.1 * z.2.1) *
            ((‖1 - z.2.2.2.1 / z.1 * z.2.1‖⁻¹ * ‖z.2.2.1 - z.2.2.2.2 / z.1 * z.2.1‖⁻¹ : ℝ) : ℂ) *
            Φ ![(z.2.2.1 - z.2.2.2.2 / z.1 * z.2.1)⁻¹,
              z.2.2.2.2 / z.1 / (z.2.2.1 - z.2.2.2.2 / z.1 * z.2.1),
              (z.2.2.2.2 / z.1 - z.2.2.1 * (z.2.2.2.1 / z.1)) / (1 - z.2.2.2.1 / z.1 * z.2.1)])) *
      (((modulus z.1 : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ z.1 * ((modulus z.1 : ℝ) : ℂ) ^ (1 - s))

private theorem indicator_one_mul {S : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ)}
    (f : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ)
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    S.indicator f p = S.indicator (fun _ => (1 : ℂ)) p * f p := by
  by_cases hp : p ∈ S
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, one_mul]
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, zero_mul]

private noncomputable def unfoldWeight
    (y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℝ≥0 :=
  (unfoldDensity v y).toNNReal

private theorem measurable_unfoldWeight : Measurable (unfoldWeight v) :=
  (measurable_unfoldDensity v).ennreal_toNNReal

private theorem unfoldDensity_ne_zero
    {y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ}
    (h₀ : y.1.1 ≠ 0) (h₁ : y.1.2 ≠ 0) : unfoldDensity v y ≠ 0 := by
  simp only [unfoldDensity]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (modulus_ennreal_ne_zero v h₀)) (modulus_ennreal_ne_zero v h₁))
    (ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.coe_ne_top))

private theorem unfoldDensity_ne_top
    {y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ}
    (hd : y.2.2.1 - y.2.1 * y.2.2.2 ≠ 0) : unfoldDensity v y ≠ ∞ := by
  simp only [unfoldDensity]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) ENNReal.coe_ne_top)
    (ENNReal.inv_ne_top.mpr (pow_ne_zero 2 (modulus_ennreal_ne_zero v hd)))

private noncomputable def transportFn
    (F : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ →
      ℂ)
    (y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℂ :=
  F y * ((unfoldWeight v y : ℝ) : ℂ)⁻¹

private theorem integrable_transportFn_comp_unfoldMap_and_integral_eq
    {F : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ →
      ℂ}
    (hF : Integrable F (((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
      ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))))) :
    Integrable (fun z => transportFn v F (unfoldMap v z)) ((mulMeasure (selfDualHaarAt ℚ v)).prod
        ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))) ∧
      ∫ z, transportFn v F (unfoldMap v z) ∂((mulMeasure (selfDualHaarAt ℚ v)).prod
          ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))) =
        ∫ y, F y ∂(((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
          ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))) := by
  have hden : unfoldDensity v =ᵐ[((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
      ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))]
      fun y => (unfoldWeight v y : ℝ≥0∞) := by
    filter_upwards [ae_unfold_target v] with y hy
    exact (ENNReal.coe_toNNReal (unfoldDensity_ne_top v hy.2.2.2)).symm
  have hsmul : (fun y => (unfoldWeight v y : ℝ) • transportFn v F y) =ᵐ[((mulMeasure (selfDualHaarAt ℚ v)).prod
      (mulMeasure (selfDualHaarAt ℚ v))).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod
        ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))] F := by
    filter_upwards [ae_unfold_target v] with y hy
    have hw : ((unfoldWeight v y : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, NNReal.coe_ne_zero, unfoldWeight, Ne, ENNReal.toNNReal_eq_zero_iff, not_or]
      exact ⟨unfoldDensity_ne_zero v hy.1 hy.2.1, unfoldDensity_ne_top v hy.2.2.2⟩
    simp only [transportFn, Complex.real_smul]
    rw [mul_left_comm, mul_inv_cancel₀ hw, mul_one]
  have hmap : Measure.map (unfoldMap v) ((mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod
      ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))) =
      (((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
        ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod
          (selfDualHaarAt ℚ v)))).withDensity fun y => (unfoldWeight v y : ℝ≥0∞) := by
    rw [map_unfoldMap, withDensity_congr_ae hden]
  have hFm : AEStronglyMeasurable (transportFn v F) (Measure.map (unfoldMap v) ((mulMeasure (selfDualHaarAt ℚ v)).prod
      ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))))) := by
    rw [hmap]
    refine (hF.aestronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)).mul
      (Measurable.aestronglyMeasurable ?_)
    exact (Complex.measurable_ofReal.comp (measurable_unfoldWeight v).coe_nnreal_real).inv
  have hint : Integrable (transportFn v F) (Measure.map (unfoldMap v) ((mulMeasure (selfDualHaarAt ℚ v)).prod
      ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))))) := by
    rw [hmap, integrable_withDensity_iff_integrable_smul (measurable_unfoldWeight v)]
    exact hF.congr hsmul.symm
  refine ⟨(integrable_map_measure hFm (measurable_unfoldMap v).aemeasurable).mp hint, ?_⟩
  rw [← integral_map (measurable_unfoldMap v).aemeasurable hFm, hmap,
    integral_withDensity_eq_integral_smul (measurable_unfoldWeight v)]
  refine integral_congr_ae ?_
  filter_upwards [hsmul] with y hy
  rw [NNReal.smul_def]
  exact hy

private theorem unfoldWeight_unfoldMap {a x α β γ : v.adicCompletion ℚ}
    (hU : α - γ / a * x ≠ 0) (hL : 1 - β / a * x ≠ 0) :
    ((unfoldWeight v (unfoldMap v (a, x, α, β, γ)) : ℝ) : ℂ) =
      ((modulus β : ℝ) : ℂ) ^ 2 * ((modulus (γ / β) : ℝ) : ℂ) *
        (((modulus (β / a / (1 - β / a * x)) : ℝ) : ℂ) ^ 2)⁻¹ := by
  have hd : γ / a / (α - γ / a * x) - (α - γ / a * x)⁻¹ * ((γ / a - α * (β / a)) / (1 - β / a * x)) =
      β / a / (1 - β / a * x) := by
    have hnum : γ / a - (γ / a - α * (β / a)) / (1 - β / a * x) = β / a * (α - γ / a * x) / (1 - β / a * x) := by
      rw [eq_div_iff hL, sub_mul, div_mul_cancel₀ _ hL]
      ring
    calc γ / a / (α - γ / a * x) - (α - γ / a * x)⁻¹ * ((γ / a - α * (β / a)) / (1 - β / a * x))
        = (α - γ / a * x)⁻¹ * (γ / a - (γ / a - α * (β / a)) / (1 - β / a * x)) := by ring
      _ = (α - γ / a * x)⁻¹ * (β / a * (α - γ / a * x) / (1 - β / a * x)) := by rw [hnum]
      _ = β / a / (1 - β / a * x) := by
          rw [← mul_div_assoc, mul_comm (β / a) (α - γ / a * x), inv_mul_cancel_left₀ hU]
  simp only [unfoldWeight, unfoldDensity, unfoldMap]
  rw [hd]
  simp only [ENNReal.toNNReal_mul, ENNReal.toNNReal_pow, ENNReal.toNNReal_inv, ENNReal.toNNReal_coe, NNReal.coe_mul,
    NNReal.coe_pow, NNReal.coe_inv, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv]

private theorem sourceFn_eq_mul (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (c : ℤ)
    (a x α β γ : v.adicCompletion ℚ) :
    sourceFn v ν Φ χ s c (a, x, α, β, γ) =
      (primedBall3 v c).indicator (fun _ => (1 : ℂ)) (α, β, γ) * (psiLocal ℚ v (-(α + β)) : ℂ) *
        ((charExt (ν 0) a)⁻¹ * charExt χ⁻¹ a *
          (charExt (ν 1 * (ν 0)⁻¹) (1 - β / a * x) * charExt (ν 2 * (ν 1)⁻¹) (α - γ / a * x))) *
        (((‖a‖⁻¹ : ℝ) : ℂ) * ((‖1 - β / a * x‖⁻¹ * ‖α - γ / a * x‖⁻¹ : ℝ) : ℂ) * ((modulus a : ℝ) : ℂ)⁻¹ *
          ((modulus a : ℝ) : ℂ) ^ (1 - s)) *
        Φ ![(α - γ / a * x)⁻¹, γ / a / (α - γ / a * x), (γ / a - α * (β / a)) / (1 - β / a * x)] := by
  simp only [sourceFn]
  ring

private theorem sourceFn_eq_transportFn (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (c : ℤ)
    {a x α β γ : v.adicCompletion ℚ} (ha : a ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hU : α - γ / a * x ≠ 0)
    (hL : 1 - β / a * x ≠ 0) :
    sourceFn v ν Φ χ s c (a, x, α, β, γ) = transportFn v (targetFn v ν Φ χ s c) (unfoldMap v (a, x, α, β, γ)) := by
  have hd : γ / a / (α - γ / a * x) - (α - γ / a * x)⁻¹ * ((γ / a - α * (β / a)) / (1 - β / a * x)) =
      β / a / (1 - β / a * x) := by
    have hnum : γ / a - (γ / a - α * (β / a)) / (1 - β / a * x) = β / a * (α - γ / a * x) / (1 - β / a * x) := by
      rw [eq_div_iff hL, sub_mul, div_mul_cancel₀ _ hL]
      ring
    calc γ / a / (α - γ / a * x) - (α - γ / a * x)⁻¹ * ((γ / a - α * (β / a)) / (1 - β / a * x))
        = (α - γ / a * x)⁻¹ * (γ / a - (γ / a - α * (β / a)) / (1 - β / a * x)) := by ring
      _ = (α - γ / a * x)⁻¹ * (β / a * (α - γ / a * x) / (1 - β / a * x)) := by rw [hnum]
      _ = β / a / (1 - β / a * x) := by
          rw [← mul_div_assoc, mul_comm (β / a) (α - γ / a * x), inv_mul_cancel_left₀ hU]
  have hw : (γ / a - α * (β / a)) / (1 - β / a * x) / (β / a / (1 - β / a * x)) = γ / β - α := by
    rw [div_div_div_cancel_right₀ hL, sub_div, div_div_div_cancel_right₀ ha,
      mul_div_cancel_right₀ _ (div_ne_zero hβ ha)]
  have Hχ := charExt_factors_eq v ν χ (Units.mk0 a ha) hβ hγ hU hL
  have HN := modulus_factors_eq v (Units.mk0 a ha) hβ hγ hU hL s
  have Hψ := truncChar_factors_eq v c α hβ γ
  simp only [Units.val_mk0] at Hχ HN
  rw [← charExt_of_ne_zero (ν 0) ha] at Hχ
  rw [sourceFn_eq_mul, ← Hχ, ← HN, transportFn, unfoldWeight_unfoldMap v hU hL]
  simp only [targetFn, gaussFn, coupledFn, unfoldMap]
  rw [hd, hw]
  by_cases hmem : (α, β, γ) ∈ primedBall3 v c
  · have hcond : Valued.v β ≤ WithZero.exp c ∧ Valued.v γ ≤ WithZero.exp c * Valued.v β ∧
        Valued.v (α - γ / β) ≤ WithZero.exp c := hmem
    rw [if_pos hcond] at Hψ
    rw [Set.indicator_of_mem hmem, ← Hψ]
    ring
  · have hcond : ¬ (Valued.v β ≤ WithZero.exp c ∧ Valued.v γ ≤ WithZero.exp c * Valued.v β ∧
        Valued.v (α - γ / β) ≤ WithZero.exp c) := hmem
    rw [if_neg hcond] at Hψ
    rw [Set.indicator_of_notMem hmem]
    rcases mul_eq_zero.mp Hψ with h₁₂ | h₃
    · rcases mul_eq_zero.mp h₁₂ with h₁ | h₂
      · simp only [h₁, zero_mul]
      · simp only [h₂, zero_mul, mul_zero]
    · simp only [h₃, zero_mul, mul_zero]

end DualFiniteLevel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"

end Part34
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"

section Part35

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal NumberField.StandardAddChar"
open scoped ENNReal NNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 integrable_coupledIntegrand"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualRemainder

variable (v : HeightOneSpectrum (𝓞 ℚ))

open Classical in
private noncomputable def primedKernel (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (c : ℤ) (a x : v.adicCompletion ℚ) : ℂ :=
  if h : a = 0 then 0 else jacquetPrimed3 v ν Φ c (Units.mk0 a h) x

private noncomputable def dualWeight (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (a : v.adicCompletion ℚ) : ℂ :=
  ((modulus a : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s)

private theorem torus_unfoldMap {a x α β γ : v.adicCompletion ℚ} (ha : a ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (hU : α - γ / a * x ≠ 0) :
    (unfoldMap v (a, x, α, β, γ)).1.1 *
        ((unfoldMap v (a, x, α, β, γ)).1.2 * (unfoldMap v (a, x, α, β, γ)).2.1 /
          (unfoldMap v (a, x, α, β, γ)).2.2.1) = a := by
  have hC : γ / β * (α - γ / a * x)⁻¹ / (γ / a / (α - γ / a * x)) = a / β := by
    generalize α - γ / a * x = U at hU ⊢
    field_simp
  simp only [unfoldMap]
  rw [hC]
  field_simp

private theorem unipotent_unfoldMap {a x α β γ : v.adicCompletion ℚ} (ha : a ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (hU : α - γ / a * x ≠ 0) (hL : 1 - β / a * x ≠ 0) :
    (unfoldMap v (a, x, α, β, γ)).1.2 * (unfoldMap v (a, x, α, β, γ)).2.1 / (unfoldMap v (a, x, α, β, γ)).2.2.1 -
        ((unfoldMap v (a, x, α, β, γ)).2.2.1 -
          (unfoldMap v (a, x, α, β, γ)).2.1 * (unfoldMap v (a, x, α, β, γ)).2.2.2)⁻¹ = x := by
  have hC : γ / β * (α - γ / a * x)⁻¹ / (γ / a / (α - γ / a * x)) = a / β := by
    generalize α - γ / a * x = U at hU ⊢
    field_simp
  have hd : γ / a / (α - γ / a * x) - (α - γ / a * x)⁻¹ * ((γ / a - α * (β / a)) / (1 - β / a * x)) =
      β / a / (1 - β / a * x) := by
    have hnum : γ / a - (γ / a - α * (β / a)) / (1 - β / a * x) = β / a * (α - γ / a * x) / (1 - β / a * x) := by
      rw [eq_div_iff hL, sub_mul, div_mul_cancel₀ _ hL]
      ring
    calc γ / a / (α - γ / a * x) - (α - γ / a * x)⁻¹ * ((γ / a - α * (β / a)) / (1 - β / a * x))
        = (α - γ / a * x)⁻¹ * (γ / a - (γ / a - α * (β / a)) / (1 - β / a * x)) := by ring
      _ = (α - γ / a * x)⁻¹ * (β / a * (α - γ / a * x) / (1 - β / a * x)) := by rw [hnum]
      _ = β / a / (1 - β / a * x) := by
          rw [← mul_div_assoc, mul_comm (β / a) (α - γ / a * x), inv_mul_cancel_left₀ hU]
  simp only [unfoldMap]
  rw [hC, hd, inv_div, div_div_eq_mul_div, sub_mul, one_mul, mul_right_comm, div_mul_cancel₀ _ ha, ← sub_div,
    sub_sub_cancel, mul_div_cancel_left₀ _ hβ]

private theorem integral_sourceFn_eq (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (c : ℤ)
    {a : v.adicCompletion ℚ} (ha : a ≠ 0) (x : v.adicCompletion ℚ) :
    ∫ p, sourceFn v ν Φ χ s c (a, x, p) ∂((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))) =
      primedKernel v ν Φ c a x * dualWeight v χ s a := by
  simp only [primedKernel, dif_neg ha]
  have hJ : jacquetPrimed3 v ν Φ c (Units.mk0 a ha) x =
      ∫ p, (primedBall3 v c).indicator (fun p => psiLocal ℚ v (-(p.1 + p.2.1)) *
        cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 (Units.mk0 a ha) x)) p
        ∂((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))) := by
    rw [integral_indicator (measurableSet_primedBall3 v c)]
    rfl
  rw [hJ, ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  beta_reduce
  rw [indicator_one_mul]
  rw [cellSectionOf_dualCellPoint, ← charExt_of_ne_zero (ν 0) ha]
  simp only [sourceFn, dualWeight, Units.val_mk0]
  ring

private theorem integrable_mul_sourceFn_and_integral_eq
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) (c : ℤ)
    (ω : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ) (hω : Measurable (Function.uncurry ω)) {B : ℝ}
    (hB : ∀ a x, ‖ω a x‖ ≤ B) :
    Integrable (fun y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ ×
        v.adicCompletion ℚ => targetFn v ν Φ χ s c y *
          ω (y.1.1 * (y.1.2 * y.2.1 / y.2.2.1)) (y.1.2 * y.2.1 / y.2.2.1 - (y.2.2.1 - y.2.1 * y.2.2.2)⁻¹))
        (((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
          ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))) ∧
    Integrable (fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
        v.adicCompletion ℚ => ω z.1 z.2.1 * sourceFn v ν Φ χ s c z)
        ((mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod
          ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))) ∧
    ∫ z, ω z.1 z.2.1 * sourceFn v ν Φ χ s c z ∂((mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod
          ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))) =
      ∫ y, targetFn v ν Φ χ s c y *
          ω (y.1.1 * (y.1.2 * y.2.1 / y.2.2.1)) (y.1.2 * y.2.1 / y.2.2.1 - (y.2.2.1 - y.2.1 * y.2.2.2)⁻¹)
        ∂(((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
          ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))) := by

  have hz : 0 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hηl : ∀ i, IsLocallyConstant ⇑((ν i * χ)⁻¹) := fun i => ((hν i).mul hχ).inv
  have hη1 : ∀ i, ‖((((ν i * χ)⁻¹) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1 := fun i => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu i, inv_one]
  have hT : Integrable (targetFn v ν Φ χ s c) (((mulMeasure (selfDualHaarAt ℚ v)).prod
      (mulMeasure (selfDualHaarAt ℚ v))).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod
        ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))) :=
    ((integrable_truncChar_mul_charExt_mul_cpow v (ν 0 * χ)⁻¹ (hηl 0) (hη1 0) (1 - s) hz c).mul_prod
      (integrable_truncChar_mul_charExt_mul_cpow v (ν 1 * χ)⁻¹ (hηl 1) (hη1 1) (1 - s) hz c)).mul_prod
      (integrable_coupledIntegrand v ν hν Φ hΦl hΦc χ hχ hu s hs hs' c)
  have hcoord : Measurable fun y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ ×
      v.adicCompletion ℚ × v.adicCompletion ℚ =>
        (y.1.1 * (y.1.2 * y.2.1 / y.2.2.1), y.1.2 * y.2.1 / y.2.2.1 - (y.2.2.1 - y.2.1 * y.2.2.2)⁻¹) :=
    (measurable_fst.fst.mul ((measurable_fst.snd.mul measurable_snd.fst).div measurable_snd.snd.fst)).prodMk
      (((measurable_fst.snd.mul measurable_snd.fst).div measurable_snd.snd.fst).sub
        (measurable_snd.snd.fst.sub (measurable_snd.fst.mul measurable_snd.snd.snd)).inv)
  have hF : Integrable (fun y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ ×
      v.adicCompletion ℚ × v.adicCompletion ℚ => targetFn v ν Φ χ s c y *
        ω (y.1.1 * (y.1.2 * y.2.1 / y.2.2.1)) (y.1.2 * y.2.1 / y.2.2.1 - (y.2.2.1 - y.2.1 * y.2.2.2)⁻¹))
      (((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
        ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))) :=
    hT.mul_bdd (hω.comp hcoord).aestronglyMeasurable (ae_of_all _ fun y => hB _ _)
  obtain ⟨hFint, hFeq⟩ := integrable_transportFn_comp_unfoldMap_and_integral_eq v hF

  have hae : (fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ => ω z.1 z.2.1 * sourceFn v ν Φ χ s c z)
        =ᵐ[(mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod
          ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))]
      fun z => transportFn v (fun y => targetFn v ν Φ χ s c y *
        ω (y.1.1 * (y.1.2 * y.2.1 / y.2.2.1)) (y.1.2 * y.2.1 / y.2.2.1 - (y.2.2.1 - y.2.1 * y.2.2.2)⁻¹))
          (unfoldMap v z) := by
    filter_upwards [ae_unfold_source v] with z hz'
    obtain ⟨a, x, α, β, γ⟩ := z
    have hid := sourceFn_eq_transportFn v ν Φ χ s c hz'.1 hz'.2.1 hz'.2.2.1 hz'.2.2.2.1 hz'.2.2.2.2
    simp only [transportFn] at hid ⊢
    rw [hid, torus_unfoldMap v hz'.1 hz'.2.1 hz'.2.2.1 hz'.2.2.2.1,
      unipotent_unfoldMap v hz'.1 hz'.2.1 hz'.2.2.1 hz'.2.2.2.1 hz'.2.2.2.2]
    ring
  have hS : Integrable (fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
      v.adicCompletion ℚ => ω z.1 z.2.1 * sourceFn v ν Φ χ s c z)
      ((mulMeasure (selfDualHaarAt ℚ v)).prod ((selfDualHaarAt ℚ v).prod
        ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))) :=
    hFint.congr hae.symm
  exact ⟨hF, hS, by rw [integral_congr_ae hae, hFeq]⟩

end DualRemainder
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"
end Part35
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal NumberField.StandardAddChar"
open scoped ENNReal NNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 integrable_coupledIntegrand"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section WindowTransport

private theorem integrable_and_integral_weight_mul_window_eq_integral_unfolded_of_forall_eq
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (K : ℤ → v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hK : ∀ (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      letI := localBorel ℚ v
      K c a x =
        ∫ p in {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
            Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1 ∧
              Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c},
          (psiLocal ℚ v (-(p.1 + p.2.1)) : ℂ) *
            cellSectionOf v ν Φ
              (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 *
                (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
                  (weylPrime3 * transposeInv3 1)) * antidiagonal3 v))
          ∂(jacquetHaar3 v))
    (c : ℤ) (ω : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hω :
      letI := localBorel ℚ v
      Measurable (Function.uncurry ω))
    (B : ℝ) (hB : ∀ a x, ‖ω a x‖ ≤ B) :
    letI := localBorel ℚ v
    Integrable
        (fun y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ ×
            v.adicCompletion ℚ =>
          (if Valued.v (-y.1.1) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.1) : ℂ) else 0) *
                  charExt (ν 0 * χ)⁻¹ y.1.1 * ((modulus y.1.1 : ℝ) : ℂ) ^ (1 - s) *
                ((if Valued.v (-y.1.2) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.2) : ℂ) else 0) *
                  charExt (ν 1 * χ)⁻¹ y.1.2 * ((modulus y.1.2 : ℝ) : ℂ) ^ (1 - s)) *
              (Φ ![y.2.1, y.2.2.1, y.2.2.2] *
                  (charExt (ν 2 * χ)⁻¹ y.2.1 * ((modulus y.2.1 : ℝ) : ℂ) ^ (1 - s)) *
                  (charExt (ν 1 * χ) y.2.2.1 * ((modulus y.2.2.1 : ℝ) : ℂ) ^ s) *
                  (charExt (ν 0 * (ν 1)⁻¹) (y.2.2.1 - y.2.1 * y.2.2.2) *
                    ((modulus (y.2.2.1 - y.2.1 * y.2.2.2) : ℝ) : ℂ)⁻¹) *
                  (if Valued.v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) ≤ WithZero.exp c then
                    (psiLocal ℚ v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) : ℂ)
                  else 0)) *
            ω (y.1.1 * (y.1.2 * y.2.1 / y.2.2.1)) (y.1.2 * y.2.1 / y.2.2.1 - (y.2.2.1 - y.2.1 * y.2.2.2)⁻¹))
        ((((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
          ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))))) ∧
      Integrable
          (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ =>
            ω q.1 q.2 *
              (((modulus q.1 : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ q.1 * ((modulus q.1 : ℝ) : ℂ) ^ (1 - s) * K c q.1 q.2))
          ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)) ∧
        ∫ q : v.adicCompletion ℚ × v.adicCompletion ℚ,
            ω q.1 q.2 *
              (((modulus q.1 : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ q.1 * ((modulus q.1 : ℝ) : ℂ) ^ (1 - s) * K c q.1 q.2)
            ∂((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)) =
          ∫ y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ ×
              v.adicCompletion ℚ,
            (if Valued.v (-y.1.1) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.1) : ℂ) else 0) *
                    charExt (ν 0 * χ)⁻¹ y.1.1 * ((modulus y.1.1 : ℝ) : ℂ) ^ (1 - s) *
                  ((if Valued.v (-y.1.2) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.2) : ℂ) else 0) *
                    charExt (ν 1 * χ)⁻¹ y.1.2 * ((modulus y.1.2 : ℝ) : ℂ) ^ (1 - s)) *
                (Φ ![y.2.1, y.2.2.1, y.2.2.2] *
                    (charExt (ν 2 * χ)⁻¹ y.2.1 * ((modulus y.2.1 : ℝ) : ℂ) ^ (1 - s)) *
                    (charExt (ν 1 * χ) y.2.2.1 * ((modulus y.2.2.1 : ℝ) : ℂ) ^ s) *
                    (charExt (ν 0 * (ν 1)⁻¹) (y.2.2.1 - y.2.1 * y.2.2.2) *
                      ((modulus (y.2.2.1 - y.2.1 * y.2.2.2) : ℝ) : ℂ)⁻¹) *
                    (if Valued.v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) ≤ WithZero.exp c then
                      (psiLocal ℚ v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) : ℂ)
                    else 0)) *
              ω (y.1.1 * (y.1.2 * y.2.1 / y.2.2.1)) (y.1.2 * y.2.1 / y.2.2.1 - (y.2.2.1 - y.2.1 * y.2.2.2)⁻¹)
            ∂((((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
              ((mulMeasure (selfDualHaarAt ℚ v)).prod
                ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))))) := by

  have hKp : ∀ a x : v.adicCompletion ℚ, ∀ ha : a ≠ 0, K c a x = primedKernel v ν Φ c a x := fun a x ha => by
    have h := hK c (Units.mk0 a ha) x
    simp only [Units.val_mk0] at h
    rw [primedKernel, dif_neg ha, h]
    rfl
  obtain ⟨hF, hS, heq⟩ := integrable_mul_sourceFn_and_integral_eq v ν hν Φ hΦl hΦc χ hχ hu s hs hs' c ω hω hB
  refine ⟨hF, ?_⟩

  have hpres := measurePreserving_prodAssoc (mulMeasure (selfDualHaarAt ℚ v)) (selfDualHaarAt ℚ v)
    ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
  have hS₂ := (hpres.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hS

  have hin : ∀ q : v.adicCompletion ℚ × v.adicCompletion ℚ, q.1 ≠ 0 →
      ∫ p, ω q.1 q.2 * sourceFn v ν Φ χ s c (q.1, q.2, p)
          ∂((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))) =
        ω q.1 q.2 *
          (((modulus q.1 : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ q.1 * ((modulus q.1 : ℝ) : ℂ) ^ (1 - s) * K c q.1 q.2) :=
    fun q hq => by
    rw [integral_const_mul, integral_sourceFn_eq v ν Φ χ s c hq q.2, hKp q.1 q.2 hq, dualWeight]
    ring
  have hae : ∀ᵐ q : v.adicCompletion ℚ × v.adicCompletion ℚ
      ∂((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)), q.1 ≠ 0 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_ne_zero_mulMeasure v)
  have h₂ : Integrable (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ =>
      ∫ p, ω q.1 q.2 * sourceFn v ν Φ χ s c (q.1, q.2, p)
        ∂((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))))
      ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)) :=
    hS₂.integral_prod_left
  refine ⟨h₂.congr ?_, ?_⟩
  · filter_upwards [hae] with q hq
    exact hin q hq
  ·
    refine Eq.trans ?_ heq
    have hS₃ : Integrable (fun x : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ ×
        v.adicCompletion ℚ × v.adicCompletion ℚ =>
        ω (MeasurableEquiv.prodAssoc x).1 (MeasurableEquiv.prodAssoc x).2.1 *
          sourceFn v ν Φ χ s c (MeasurableEquiv.prodAssoc x))
        (((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)).prod
          ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))) := hS₂
    rw [← hpres.integral_comp' (fun z : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ×
        v.adicCompletion ℚ × v.adicCompletion ℚ => ω z.1 z.2.1 * sourceFn v ν Φ χ s c z), integral_prod _ hS₃]
    refine integral_congr_ae ?_
    filter_upwards [hae] with q hq
    exact (hin q hq).symm

end WindowTransport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction"

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.TateLocal in
open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (K : ℤ → v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hK : ∀ (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      letI := localBorel ℚ v
      K c a x =
        ∫ p in {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
            Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1 ∧
              Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c},
          (psiLocal ℚ v (-(p.1 + p.2.1)) : ℂ) *
            cellSectionOf v ν Φ
              (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 *
                (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
                  (weylPrime3 * transposeInv3 1)) * antidiagonal3 v))
          ∂(jacquetHaar3 v))
    (c : ℤ) (ω : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hω :
      letI := localBorel ℚ v
      Measurable (Function.uncurry ω))
    (B : ℝ) (hB : ∀ a x, ‖ω a x‖ ≤ B) :
    letI := localBorel ℚ v
    Integrable
        (fun y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ ×
            v.adicCompletion ℚ =>
          (if Valued.v (-y.1.1) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.1) : ℂ) else 0) *
                  charExt (ν 0 * χ)⁻¹ y.1.1 * ((modulus y.1.1 : ℝ) : ℂ) ^ (1 - s) *
                ((if Valued.v (-y.1.2) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.2) : ℂ) else 0) *
                  charExt (ν 1 * χ)⁻¹ y.1.2 * ((modulus y.1.2 : ℝ) : ℂ) ^ (1 - s)) *
              (Φ ![y.2.1, y.2.2.1, y.2.2.2] *
                  (charExt (ν 2 * χ)⁻¹ y.2.1 * ((modulus y.2.1 : ℝ) : ℂ) ^ (1 - s)) *
                  (charExt (ν 1 * χ) y.2.2.1 * ((modulus y.2.2.1 : ℝ) : ℂ) ^ s) *
                  (charExt (ν 0 * (ν 1)⁻¹) (y.2.2.1 - y.2.1 * y.2.2.2) *
                    ((modulus (y.2.2.1 - y.2.1 * y.2.2.2) : ℝ) : ℂ)⁻¹) *
                  (if Valued.v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) ≤ WithZero.exp c then
                    (psiLocal ℚ v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) : ℂ)
                  else 0)) *
            ω (y.1.1 * (y.1.2 * y.2.1 / y.2.2.1)) (y.1.2 * y.2.1 / y.2.2.1 - (y.2.2.1 - y.2.1 * y.2.2.2)⁻¹))
        ((((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
          ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))))) ∧
      Integrable
          (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ =>
            ω q.1 q.2 *
              (((modulus q.1 : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ q.1 * ((modulus q.1 : ℝ) : ℂ) ^ (1 - s) * K c q.1 q.2))
          ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)) ∧
        ∫ q : v.adicCompletion ℚ × v.adicCompletion ℚ,
            ω q.1 q.2 *
              (((modulus q.1 : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ q.1 * ((modulus q.1 : ℝ) : ℂ) ^ (1 - s) * K c q.1 q.2)
            ∂((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)) =
          ∫ y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ ×
              v.adicCompletion ℚ,
            (if Valued.v (-y.1.1) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.1) : ℂ) else 0) *
                    charExt (ν 0 * χ)⁻¹ y.1.1 * ((modulus y.1.1 : ℝ) : ℂ) ^ (1 - s) *
                  ((if Valued.v (-y.1.2) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.2) : ℂ) else 0) *
                    charExt (ν 1 * χ)⁻¹ y.1.2 * ((modulus y.1.2 : ℝ) : ℂ) ^ (1 - s)) *
                (Φ ![y.2.1, y.2.2.1, y.2.2.2] *
                    (charExt (ν 2 * χ)⁻¹ y.2.1 * ((modulus y.2.1 : ℝ) : ℂ) ^ (1 - s)) *
                    (charExt (ν 1 * χ) y.2.2.1 * ((modulus y.2.2.1 : ℝ) : ℂ) ^ s) *
                    (charExt (ν 0 * (ν 1)⁻¹) (y.2.2.1 - y.2.1 * y.2.2.2) *
                      ((modulus (y.2.2.1 - y.2.1 * y.2.2.2) : ℝ) : ℂ)⁻¹) *
                    (if Valued.v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) ≤ WithZero.exp c then
                      (psiLocal ℚ v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) : ℂ)
                    else 0)) *
              ω (y.1.1 * (y.1.2 * y.2.1 / y.2.2.1)) (y.1.2 * y.2.1 / y.2.2.1 - (y.2.2.1 - y.2.1 * y.2.2.2)⁻¹)
            ∂((((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
              ((mulMeasure (selfDualHaarAt ℚ v)).prod
                ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))))) := by
  exact integrable_and_integral_weight_mul_window_eq_integral_unfolded_of_forall_eq v ν hν Φ hΦl hΦc χ hχ hu s hs hs'
    K hK c ω hω B hB

end S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded (solution)
