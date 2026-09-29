-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.selfDualHaarAt_real_units_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2be03f05-419a-5a7c-9e58-f129227f5c37

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_selfDualHaarAt_real_units_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.StandardAddChar IsDedekindDomain NumberField.AdelicTrace NumberField.AdelicBox

open IsDedekindDomain.HeightOneSpectrum
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt modulus modulus_coe_units modulus_adicCompletion_eq_nnnorm"
namespace UnramB
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

private def shell (m : ℕ) : Set (v.adicCompletion K) :=
  {x | Valued.v x = WithZero.exp (-(m : ℤ))}

private theorem mem_unitSphere {x : v.adicCompletion K} :
    x ∈ unitSphere K v ↔ Valued.v x = 1 := Iff.rfl

private theorem mem_shell {m : ℕ} {x : v.adicCompletion K} :
    x ∈ shell K v m ↔ Valued.v x = WithZero.exp (-(m : ℤ)) := Iff.rfl

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

private theorem toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  have h : WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp n ≠ 0) = Multiplicative.ofAdd n :=
    WithZero.unzero_coe _
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero, h, toAdd_ofAdd]

private theorem modulus_of_mem_shell
    (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊) {m : ℕ}
    {x : v.adicCompletion K} (hx : x ∈ shell K v m) :
    modulus x = ((Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹) ^ m := by
  rw [hA x]
  apply NNReal.coe_injective
  rw [coe_nnnorm, NumberField.FinitePlace.norm_def, (mem_shell K v).mp hx,
    toNNReal_exp _ (-(m : ℤ)), zpow_neg, zpow_natCast, inv_pow]

private theorem smul_integers_eq :
    (uniformizerUnit K v) • (v.adicCompletionIntegers K : Set (v.adicCompletion K))
      = {x | Valued.v x ≤ WithZero.exp (-1 : ℤ)} := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, mem_adicCompletionIntegers,
    Set.mem_setOf_eq, Units.smul_def, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    valued_uniformizerUnit, inv_mul_le_iff₀ WithZero.exp_pos, mul_one]

private theorem withZero_lt_one_iff_le_exp_neg_one (x : WithZero (Multiplicative ℤ)) :
    x < 1 ↔ x ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, neg_add_cancel,
    WithZero.exp_zero]

private theorem integers_eq_unitSphere_union :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K))
      = unitSphere K v ∪ {x | Valued.v x ≤ WithZero.exp (-1 : ℤ)} := by
  ext x
  rw [SetLike.mem_coe, mem_adicCompletionIntegers, Set.mem_union, mem_unitSphere, Set.mem_setOf_eq,
    ← withZero_lt_one_iff_le_exp_neg_one]
  exact le_iff_eq_or_lt

private theorem disjoint_unitSphere_smul_integers :
    Disjoint (unitSphere K v) {x | Valued.v x ≤ WithZero.exp (-1 : ℤ)} := by
  rw [Set.disjoint_iff]
  rintro x ⟨h1, h2⟩
  rw [mem_unitSphere] at h1
  rw [Set.mem_setOf_eq, h1, ← withZero_lt_one_iff_le_exp_neg_one] at h2
  exact lt_irrefl _ h2

private theorem addHaar_unitSphere (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊) :
    Measure.addHaarMeasure (integersPositiveCompacts K v) (unitSphere K v)
      = 1 - (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ := by
  set μ₀ := Measure.addHaarMeasure (integersPositiveCompacts K v) with hμ₀
  have hO : μ₀ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1 := by
    rw [hμ₀, ← coe_integersPositiveCompacts K v, Measure.addHaarMeasure_self]
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 :=
    Nat.cast_ne_zero.mpr (absNorm_ne_zero' K v)
  have hq0' : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (absNorm_ne_zero' K v)
  have hmem : (uniformizerUnit K v : v.adicCompletion K) ∈ shell K v 1 := by
    rw [mem_shell, Nat.cast_one]
    exact valued_uniformizerUnit K v
  have hS : μ₀ {x | Valued.v x ≤ WithZero.exp (-1 : ℤ)} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ := by
    rw [← smul_integers_eq,
      ← distribHaarChar_mul μ₀ (uniformizerUnit K v)
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)),
      hO, mul_one, ← modulus_coe_units, modulus_of_mem_shell K v hA hmem, pow_one,
      ENNReal.coe_inv hq0, ENNReal.coe_natCast]
  have hsum : μ₀ (unitSphere K v) + μ₀ {x | Valued.v x ≤ WithZero.exp (-1 : ℤ)} = 1 := by
    rw [← measure_union' (disjoint_unitSphere_smul_integers K v)
      (isOpen_unitSphere K v).measurableSet, ← integers_eq_unitSphere_union, hO]
  rw [hS] at hsum
  exact ENNReal.eq_sub_of_add_eq (ENNReal.inv_ne_top.mpr hq0') hsum

private theorem selfDualHaarAt_eq_smul :
    selfDualHaarAt K v = ((Ideal.absNorm v.asIdeal : ℝ≥0)
        ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2))
          • Measure.addHaarMeasure (integersPositiveCompacts K v) :=
  rfl

private theorem selfDualHaarAt_real_unitSphere (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊) :
    (selfDualHaarAt K v).real (unitSphere K v)
      = (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
          * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2) := by
  have hq1 : (1 : ℝ≥0∞) ≤ (Ideal.absNorm v.asIdeal : ℝ≥0∞) := by
    exact_mod_cast (one_lt_absNorm K v).le
  rw [selfDualHaarAt_eq_smul, measureReal_nnreal_smul_apply, measureReal_def,
    addHaar_unitSphere K v hA, ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr hq1)
      ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    NNReal.coe_rpow, NNReal.coe_natCast, mul_comm]

end LanglandsTunnell.TateLocal.UnramB

end

p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_selfDualHaarAt_real_units_eq.LanglandsTunnell.TateLocal NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain MeasureTheory"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K)) :
    (selfDualHaarAt K v).real {x | Valued.v x = 1}
      = (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
          * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2) :=
  LanglandsTunnell.TateLocal.UnramB.selfDualHaarAt_real_unitSphere K v
    (LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v)

end S_LanglandsTunnell_TateLocal_selfDualHaarAt_real_units_eq
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_selfDualHaarAt_real_units_eq (solution)
