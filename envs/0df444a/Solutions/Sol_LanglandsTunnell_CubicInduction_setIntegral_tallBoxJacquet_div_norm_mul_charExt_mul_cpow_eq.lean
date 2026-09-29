-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0b376f39-1b02-57a8-8a3f-b6b79983d2f7

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

section
set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt modulus modulus_of_ne_zero modulus_pos modulus_ne_zero modulus_mul charExt charExt_zero charExt_of_ne_zero charExt_coe_units mulMeasure integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion modulus_adicCompletion_eq_nnnorm"
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

private theorem integral_mul_left_selfDualHaarAt (u : (v.adicCompletion K)ˣ) (F : v.adicCompletion K → ℂ) :
    letI := localBorel K v
    ∫ x, F ((u : v.adicCompletion K) * x) ∂(selfDualHaarAt K v) =
      ((modulus (u : v.adicCompletion K) : ℝ≥0∞)⁻¹).toReal • ∫ x, F x ∂(selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  rw [← (measurableEmbedding_mulLeft₀ u.ne_zero).integral_map F, map_mul_left_selfDualHaarAt,
    integral_smul_measure]

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

private theorem integral_mul_left_mulMeasure (c : v.adicCompletion K) (hc : c ≠ 0) (F : v.adicCompletion K → ℂ) :
    letI := localBorel K v
    ∫ x, F (c * x) ∂(mulMeasure (selfDualHaarAt K v)) = ∫ x, F x ∂(mulMeasure (selfDualHaarAt K v)) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have h := map_mul_left_mulMeasure K v (Units.mk0 c hc)
  simp only [Units.val_mk0] at h
  rw [← (measurableEmbedding_mulLeft₀ hc).integral_map F, h]

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

private theorem measurableSingletonClass_adicCompletion :
    letI := localBorel K v
    MeasurableSingletonClass (v.adicCompletion K) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  infer_instance

end MeasureClasses

end LanglandsTunnell.TateLocal
end

section
set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq.LanglandsTunnell.TateLocal"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) : LocalGL3 v :=
  antidiagonal3 v * upperUnipotent3 x y z * (iotaGL (diagUnitGL2 a) * antidiagonal3 v)

private theorem torusCellPoint_coe (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    (torusCellPoint v x y z a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, 0, 0; y, 1, 0; z, x, (a : v.adicCompletion ℚ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusCellPoint, antidiagonal3_coe, embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (i j : Fin 3) :
    gl3Entry v (torusCellPoint v x y z a) i j = !![1, 0, 0; y, 1, 0; z, x, (a : v.adicCompletion ℚ)] i j := by
  rw [gl3Entry, torusCellPoint_coe]

private theorem cornerEntry_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    cornerEntry v (torusCellPoint v x y z a) = z := by
  simp [cornerEntry, gl3Entry_torusCellPoint]

private theorem lowerMinor_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    lowerMinor v (torusCellPoint v x y z a) = x * y - z := by
  simp only [lowerMinor, gl3Entry_torusCellPoint]
  simp
  ring

private theorem outerMinor_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    outerMinor v (torusCellPoint v x y z a) = (a : v.adicCompletion ℚ) * y := by
  simp only [outerMinor, gl3Entry_torusCellPoint]
  simp
  ring

private theorem gl3Det_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    gl3Det v (torusCellPoint v x y z a) = (a : v.adicCompletion ℚ) := by
  rw [gl3Det, torusCellPoint_coe, Matrix.det_fin_three]
  simp

private theorem cellRatio_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    cellRatio v (torusCellPoint v x y z a) =
      ![x / z, (a : v.adicCompletion ℚ) / z, (a : v.adicCompletion ℚ) * y / (x * y - z)] := by
  rw [cellRatio, cornerEntry_torusCellPoint, outerMinor_torusCellPoint, lowerMinor_torusCellPoint]
  simp [gl3Entry_torusCellPoint]

private theorem cellValue_torusCellPoint (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (x y z : v.adicCompletion ℚ)
    (a : (v.adicCompletion ℚ)ˣ) :
    cellValue v χ (torusCellPoint v x y z a) =
      charExt (χ 0) ((a : v.adicCompletion ℚ) / (x * y - z)) * charExt (χ 1) ((x * y - z) / z) * charExt (χ 2) z *
        ((‖(a : v.adicCompletion ℚ) / (x * y - z)‖ / ‖z‖ : ℝ) : ℂ) := by
  rw [cellValue, gl3Det_torusCellPoint, lowerMinor_torusCellPoint, cornerEntry_torusCellPoint]

section DualPoint

end DualPoint

end LanglandsTunnell.CubicInduction
end

section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private noncomputable def torusIntegrand (a : (v.adicCompletion ℚ)ˣ)
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) : ℂ :=
  psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (torusCellPoint v p.1 p.2.1 p.2.2 a)

private theorem modulus_real_eq_norm (x : v.adicCompletion ℚ) : (modulus x : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

private theorem torusCellPoint_mem_bigCell3_iff (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    torusCellPoint v x y z a ∈ bigCell3 v ↔ z ≠ 0 ∧ x * y - z ≠ 0 := by
  rw [mem_bigCell3_iff, cornerEntry_torusCellPoint, lowerMinor_torusCellPoint]

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

end LanglandsTunnell.CubicInduction
end

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq.LanglandsTunnell.TateLocal"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section CoupledCoordinates

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem charExt_mul_inv_of_ne_zero (η θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x : v.adicCompletion ℚ}
    (hx : x ≠ 0) : charExt (η * θ⁻¹) x = charExt η x * (charExt θ x)⁻¹ := by
  rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hx, MonoidHom.mul_apply,
    MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]

private theorem charExt_inv_of_ne_zero (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    charExt η x⁻¹ = (charExt η x)⁻¹ := by
  rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ (inv_ne_zero hx), ← Units.val_inv_eq_inv_val, ← map_inv]
  congr 2
  exact Units.ext (by simp)

private theorem charExt_mul_of_ne_zero (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x y : v.adicCompletion ℚ} (hx : x ≠ 0)
    (hy : y ≠ 0) : charExt η (x * y) = charExt η x * charExt η y := by
  rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hy, charExt_of_ne_zero _ (mul_ne_zero hx hy), ← Units.val_mul,
    ← map_mul]
  congr 2
  exact Units.ext (by simp)

private theorem torusCell_sub_eq (a : (v.adicCompletion ℚ)ˣ) (x y z : v.adicCompletion ℚ) (hz : z ≠ 0)
    (hc : x * y - z ≠ 0) :
    (a : v.adicCompletion ℚ) / z - x / z * ((a : v.adicCompletion ℚ) * y / (x * y - z)) =
      -((a : v.adicCompletion ℚ) / (x * y - z)) := by
  field_simp
  ring

private theorem torusCell_mid_eq (a : (v.adicCompletion ℚ)ˣ) (x y z : v.adicCompletion ℚ) (hz : z ≠ 0)
    (hc : x * y - z ≠ 0) :
    (x * y - z) / z = -1 * ((a : v.adicCompletion ℚ) / z * (-((a : v.adicCompletion ℚ) / (x * y - z)))⁻¹) := by
  have ha : (a : v.adicCompletion ℚ) ≠ 0 := a.ne_zero
  field_simp

private theorem cellSectionOf_torusCellPoint_eq_coupled (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (a : (v.adicCompletion ℚ)ˣ) (x y z : v.adicCompletion ℚ) (hz : z ≠ 0)
    (hc : x * y - z ≠ 0) :
    cellSectionOf v ν Φ (torusCellPoint v x y z a) =
      charExt (ν 0) (-1) * charExt (ν 1) (-1) *
        (charExt (ν 0 * (ν 1)⁻¹)
            ((a : v.adicCompletion ℚ) / z - x / z * ((a : v.adicCompletion ℚ) * y / (x * y - z))) *
          charExt (ν 1 * (ν 2)⁻¹) ((a : v.adicCompletion ℚ) / z) * ((ν 2 a : ℂˣ) : ℂ)) *
        ((‖(a : v.adicCompletion ℚ) / z - x / z * ((a : v.adicCompletion ℚ) * y / (x * y - z))‖ *
            ‖(a : v.adicCompletion ℚ) / z‖ / ‖(a : v.adicCompletion ℚ)‖ : ℝ) : ℂ) *
        Φ ![x / z, (a : v.adicCompletion ℚ) / z, (a : v.adicCompletion ℚ) * y / (x * y - z)] := by
  have ha : (a : v.adicCompletion ℚ) ≠ 0 := a.ne_zero
  have hmem : torusCellPoint v x y z a ∈ bigCell3 v := (torusCellPoint_mem_bigCell3_iff v x y z a).mpr ⟨hz, hc⟩
  have hR : (a : v.adicCompletion ℚ) / (x * y - z) ≠ 0 := div_ne_zero ha hc
  have haz : (a : v.adicCompletion ℚ) / z ≠ 0 := div_ne_zero ha hz
  have hn1 : (-1 : v.adicCompletion ℚ) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rw [cellSectionOf_apply_of_mem v ν Φ hmem, cellValue_torusCellPoint, cellRatio_torusCellPoint,
    torusCell_sub_eq v a x y z hz hc, torusCell_mid_eq v a x y z hz hc]

  have h0 : charExt (ν 0) ((a : v.adicCompletion ℚ) / (x * y - z)) =
      charExt (ν 0) (-1) * charExt (ν 0) (-((a : v.adicCompletion ℚ) / (x * y - z))) := by
    rw [← charExt_mul_of_ne_zero v (ν 0) hn1 (neg_ne_zero.mpr hR), neg_one_mul, neg_neg]
  have hnR : -((a : v.adicCompletion ℚ) / (x * y - z)) ≠ 0 := neg_ne_zero.mpr hR
  have h1 : charExt (ν 1) (-1 * ((a : v.adicCompletion ℚ) / z * (-((a : v.adicCompletion ℚ) / (x * y - z)))⁻¹)) =
      charExt (ν 1) (-1) * (charExt (ν 1) ((a : v.adicCompletion ℚ) / z) *
        (charExt (ν 1) (-((a : v.adicCompletion ℚ) / (x * y - z))))⁻¹) := by
    rw [charExt_mul_of_ne_zero v (ν 1) hn1 (mul_ne_zero haz (inv_ne_zero hnR)),
      charExt_mul_of_ne_zero v (ν 1) haz (inv_ne_zero hnR), charExt_inv_of_ne_zero v (ν 1) hnR]
  have h2 : charExt (ν 2) z = (charExt (ν 2) ((a : v.adicCompletion ℚ) / z))⁻¹ * ((ν 2 a : ℂˣ) : ℂ) := by
    have hν2 : ((ν 2 a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hcz : charExt (ν 2) z ≠ 0 := by rw [charExt_of_ne_zero _ hz]; exact Units.ne_zero _
    rw [div_eq_mul_inv, charExt_mul_of_ne_zero v (ν 2) ha (inv_ne_zero hz), charExt_inv_of_ne_zero v (ν 2) hz,
      charExt_coe_units]
    field_simp
  rw [h0, h1, h2, charExt_mul_inv_of_ne_zero v (ν 0) (ν 1) hnR,
    charExt_mul_inv_of_ne_zero v (ν 1) (ν 2) haz, norm_neg]

  have hnorm : ‖(a : v.adicCompletion ℚ) / (x * y - z)‖ / ‖z‖ =
      ‖(a : v.adicCompletion ℚ) / (x * y - z)‖ * ‖(a : v.adicCompletion ℚ) / z‖ / ‖(a : v.adicCompletion ℚ)‖ := by
    rw [norm_div, norm_div]
    have han : ‖(a : v.adicCompletion ℚ)‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hcn : ‖x * y - z‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    field_simp
  rw [hnorm]
  ring

end CoupledCoordinates

end LanglandsTunnell.CubicInduction

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section BeyondTheBall

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private def tallBox (c c' : ℤ) : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  {p | Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * c')}

private theorem measurableSet_tallBox (c c' : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (tallBox v c c') := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hset : tallBox v c c' =
      (Prod.fst ⁻¹' {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.1) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.2) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (2 * c')}) := by
    ext p
    simp only [tallBox, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]
  rw [hset]
  exact (((isClosed_valued_le v c).measurableSet.preimage measurable_fst).inter
    ((isClosed_valued_le v c).measurableSet.preimage (measurable_fst.comp measurable_snd))).inter
    ((isClosed_valued_le v (2 * c')).measurableSet.preimage (measurable_snd.comp measurable_snd))

end BeyondTheBall
end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq.LanglandsTunnell.TateLocal"
open scoped NNReal ENNReal

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Substitutions

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

private theorem integral_eq_norm_mul_integral_comp_affine (c b : v.adicCompletion ℚ) (hc : c ≠ 0)
    (f : v.adicCompletion ℚ → ℂ) :
    ∫ y, f y ∂(selfDualHaarAt ℚ v) = (‖c‖ : ℂ) * ∫ w, f (c * w + b) ∂(selfDualHaarAt ℚ v) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v

  have hshift : ∫ w, f (c * w + b) ∂(selfDualHaarAt ℚ v) = ∫ w, f (c * w) ∂(selfDualHaarAt ℚ v) := by
    have h := integral_add_right_eq_self (μ := selfDualHaarAt ℚ v) (fun w => f (c * w)) (b / c)
    have hfun : (fun w => f (c * w + b)) = fun w => (fun w => f (c * w)) (w + b / c) := by
      funext w
      simp only [mul_add, mul_div_cancel₀ b hc]
    rw [hfun, h]

  have hscale := integral_mul_left_selfDualHaarAt ℚ v (Units.mk0 c hc) f
  simp only [Units.val_mk0] at hscale
  have hm0 : (modulus c : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr (modulus_ne_zero hc)
  have hmC : ((modulus c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm0
  rw [hshift, hscale, ENNReal.toReal_inv, ENNReal.coe_toReal, Complex.real_smul, Complex.ofReal_inv,
    ← modulus_real_eq_norm v c, ← mul_assoc, mul_inv_cancel₀ hmC, one_mul]

private theorem integral_eq_integral_norm_inv_sq_mul_comp_inv (g : v.adicCompletion ℚ → ℂ) :
    ∫ x, g x ∂(selfDualHaarAt ℚ v) = ∫ u, (((‖u‖ ^ 2)⁻¹ : ℝ) : ℂ) * g u⁻¹ ∂(selfDualHaarAt ℚ v) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  have h := integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion ℚ v (selfDualHaarAt ℚ v)
    (fun x => g x⁻¹)
  simp only [inv_inv] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [Complex.real_smul, modulus_real_eq_norm v u]

private theorem integral_eq_integral_comp_moebius (α β : v.adicCompletion ℚ) (hβ : β ≠ 0)
    (f : v.adicCompletion ℚ → ℂ) :
    ∫ y, f y ∂(selfDualHaarAt ℚ v) =
      ∫ w, ((‖β‖ * (‖β - α * w‖ ^ 2)⁻¹ : ℝ) : ℂ) * f (-w / (β - α * w)) ∂(selfDualHaarAt ℚ v) := by
  by_cases hα : α = 0
  ·
    subst hα
    have hc : -β⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hβ)
    rw [integral_eq_norm_mul_integral_comp_affine v (-β⁻¹) 0 hc f, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [zero_mul, sub_zero, add_zero]
    have hβn : ‖β‖ ≠ 0 := norm_ne_zero_iff.mpr hβ
    have hi : ‖β‖ * (‖β‖ ^ 2)⁻¹ = ‖β‖⁻¹ := by
      rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hβn, one_mul]
    rw [hi, norm_neg, norm_inv]
    congr 2
    ring
  ·
    have hc₁ : -(β / α) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hβ hα)
    have hc₃ : -α ≠ 0 := neg_ne_zero.mpr hα
    have h1 := integral_eq_norm_mul_integral_comp_affine v (-(β / α)) α⁻¹ hc₁ f
    have h2 := integral_eq_integral_norm_inv_sq_mul_comp_inv v (fun r' => f (-(β / α) * r' + α⁻¹))
    have h3 := integral_eq_norm_mul_integral_comp_affine v (-α) β hc₃
      (fun r => (((‖r‖ ^ 2)⁻¹ : ℝ) : ℂ) * f (-(β / α) * r⁻¹ + α⁻¹))
    beta_reduce at h2 h3
    rw [h1, h2, h3, ← mul_assoc, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hr : -α * w + β = β - α * w := by ring
    simp only [hr]
    by_cases hpole : β - α * w = 0
    ·
      simp [hpole]
    · have harg : -(β / α) * (β - α * w)⁻¹ + α⁻¹ = -w / (β - α * w) := by
        field_simp
        ring
      rw [harg, ← mul_assoc]
      congr 1
      have hαC : (‖α‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hα)
      rw [norm_neg, norm_div, norm_neg]
      push_cast
      rw [div_mul_cancel₀ (‖β‖ : ℂ) hαC]

private theorem integral_eq_integral_comp_div (a : v.adicCompletion ℚ) (ha : a ≠ 0)
    (f : v.adicCompletion ℚ → ℂ) :
    ∫ z, f z ∂(selfDualHaarAt ℚ v) =
      ∫ r, ((‖a‖ * (‖r‖ ^ 2)⁻¹ : ℝ) : ℂ) * f (a / r) ∂(selfDualHaarAt ℚ v) := by
  have h1 := integral_eq_norm_mul_integral_comp_affine v a 0 ha f
  have h2 := integral_eq_integral_norm_inv_sq_mul_comp_inv v (fun r' => f (a * r' + 0))
  beta_reduce at h2
  rw [h1, h2, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  show (‖a‖ : ℂ) * ((((‖r‖ ^ 2)⁻¹ : ℝ) : ℂ) * f (a * r⁻¹ + 0)) = ((‖a‖ * (‖r‖ ^ 2)⁻¹ : ℝ) : ℂ) * f (a / r)
  rw [add_zero, show a * r⁻¹ = a / r from (div_eq_mul_inv a r).symm]
  push_cast
  ring

private theorem integral_eq_norm_mul_integral_comp_mul_right (d : v.adicCompletion ℚ) (hd : d ≠ 0)
    (f : v.adicCompletion ℚ → ℂ) :
    ∫ x, f x ∂(selfDualHaarAt ℚ v) = (‖d‖ : ℂ) * ∫ u, f (u * d) ∂(selfDualHaarAt ℚ v) := by
  rw [integral_eq_norm_mul_integral_comp_affine v d 0 hd f]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show f (d * u + 0) = f (u * d)
  rw [add_zero, mul_comm]

private theorem integral_eq_integral_norm_mul_mulMeasure (f : v.adicCompletion ℚ → ℂ) (hf : f 0 = 0) :
    ∫ x, f x ∂(selfDualHaarAt ℚ v) = ∫ x, (‖x‖ : ℂ) * f x ∂(mulMeasure (selfDualHaarAt ℚ v)) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hc : MeasurableSet ({0}ᶜ : Set (v.adicCompletion ℚ)) := isClosed_singleton.measurableSet.compl

  have hdens : Measurable fun x : v.adicCompletion ℚ => ((modulus x : ℝ≥0∞))⁻¹ :=
    (measurable_coe_nnreal_ennreal_iff.mpr
      (measurable_coe_nnreal_real_iff.mp (by simpa only [modulus_real_eq_norm] using measurable_norm))).inv
  have hfin : ∀ᵐ x ∂((selfDualHaarAt ℚ v).restrict {0}ᶜ), ((modulus x : ℝ≥0∞))⁻¹ < ∞ := by
    rw [ae_restrict_iff' hc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : x ≠ 0 := hx
    exact ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr (modulus_pos hx0))
  unfold mulMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hdens hfin, ← integral_indicator hc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x = 0
  · subst hx
    simp [hf]
  · have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    rw [Set.indicator_of_mem (show x ∈ ({0}ᶜ : Set (v.adicCompletion ℚ)) from hx), ENNReal.toReal_inv,
      ENNReal.coe_toReal, modulus_real_eq_norm v x, Complex.real_smul, ← mul_assoc]
    push_cast
    rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hxn), one_mul]

end Substitutions

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section CoupledIntegrand

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem moebiusDenom_eq (a x z w : v.adicCompletion ℚ) : a / z - x / z * w = (a - x * w) / z := by
  rw [div_mul_eq_mul_div, ← sub_div]

private theorem torusCell_xy_sub_z_of_moebius (a x z w : v.adicCompletion ℚ) (hz : z ≠ 0)
    (hD : a / z - x / z * w ≠ 0) :
    x * (-w / (a / z - x / z * w)) - z = -(a / (a / z - x / z * w)) := by
  rw [moebiusDenom_eq] at hD ⊢
  have haw : a - x * w ≠ 0 := (div_ne_zero_iff.mp hD).1
  field_simp
  ring

private theorem torusCell_coord_of_moebius (a x z w : v.adicCompletion ℚ) (ha : a ≠ 0) (hz : z ≠ 0)
    (hD : a / z - x / z * w ≠ 0) :
    a * (-w / (a / z - x / z * w)) / (x * (-w / (a / z - x / z * w)) - z) = w := by
  rw [torusCell_xy_sub_z_of_moebius v a x z w hz hD, div_eq_iff (neg_ne_zero.mpr (div_ne_zero ha hD))]
  ring

private theorem cellSectionOf_torusCellPoint_moebius (a : (v.adicCompletion ℚ)ˣ) (x z w : v.adicCompletion ℚ)
    (hz : z ≠ 0) (hD : (a : v.adicCompletion ℚ) / z - x / z * w ≠ 0) :
    cellSectionOf v ν Φ (torusCellPoint v x (-w / ((a : v.adicCompletion ℚ) / z - x / z * w)) z a) =
      charExt (ν 0) (-1) * charExt (ν 1) (-1) *
        (charExt (ν 0 * (ν 1)⁻¹) ((a : v.adicCompletion ℚ) / z - x / z * w) *
          charExt (ν 1 * (ν 2)⁻¹) ((a : v.adicCompletion ℚ) / z) * ((ν 2 a : ℂˣ) : ℂ)) *
        ((‖(a : v.adicCompletion ℚ) / z - x / z * w‖ * ‖(a : v.adicCompletion ℚ) / z‖ /
          ‖(a : v.adicCompletion ℚ)‖ : ℝ) : ℂ) *
        Φ ![x / z, (a : v.adicCompletion ℚ) / z, w] := by
  have ha : (a : v.adicCompletion ℚ) ≠ 0 := a.ne_zero
  have hxy : x * (-w / ((a : v.adicCompletion ℚ) / z - x / z * w)) - z ≠ 0 := by
    rw [torusCell_xy_sub_z_of_moebius v (a : v.adicCompletion ℚ) x z w hz hD]
    exact neg_ne_zero.mpr (div_ne_zero ha hD)
  rw [cellSectionOf_torusCellPoint_eq_coupled v ν Φ a x (-w / ((a : v.adicCompletion ℚ) / z - x / z * w)) z hz hxy,
    torusCell_coord_of_moebius v (a : v.adicCompletion ℚ) x z w ha hz hD]

private theorem moebius_norm_bookkeeping (A E N : ℝ) (hE : E ≠ 0) (hN : N ≠ 0) :
    A * (E ^ 2)⁻¹ * (E * A / N) = A ^ 2 / N * E⁻¹ := by
  field_simp

private theorem moebiusDensity_mul_torusIntegrand_eq (a : (v.adicCompletion ℚ)ˣ) (c : ℤ)
    (x z w : v.adicCompletion ℚ) :
    ((‖(a : v.adicCompletion ℚ) / z‖ * (‖(a : v.adicCompletion ℚ) / z - x / z * w‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        ((if Valued.v (-w / ((a : v.adicCompletion ℚ) / z - x / z * w)) ≤ WithZero.exp c then
            (psiLocal ℚ v (-(x + -w / ((a : v.adicCompletion ℚ) / z - x / z * w))) : ℂ) else 0) *
          cellSectionOf v ν Φ (torusCellPoint v x (-w / ((a : v.adicCompletion ℚ) / z - x / z * w)) z a)) =
      (psiLocal ℚ v (-x) : ℂ) *
        (charExt (ν 0) (-1) * charExt (ν 1) (-1) *
          (charExt (ν 1 * (ν 2)⁻¹) ((a : v.adicCompletion ℚ) / z) * ((ν 2 a : ℂˣ) : ℂ)) *
          ((‖(a : v.adicCompletion ℚ) / z‖ ^ 2 / ‖(a : v.adicCompletion ℚ)‖ : ℝ) : ℂ)) *
        (Φ ![x / z, (a : v.adicCompletion ℚ) / z, w] *
          (charExt (ν 0 * (ν 1)⁻¹) ((a : v.adicCompletion ℚ) / z - x / z * w) *
            ((modulus ((a : v.adicCompletion ℚ) / z - x / z * w) : ℝ) : ℂ)⁻¹) *
          (if Valued.v (w / ((a : v.adicCompletion ℚ) / z - x / z * w)) ≤ WithZero.exp c then
              (psiLocal ℚ v (w / ((a : v.adicCompletion ℚ) / z - x / z * w)) : ℂ) else 0)) := by
  have ha : (a : v.adicCompletion ℚ) ≠ 0 := a.ne_zero

  by_cases hz : z = 0
  · subst hz
    simp only [div_zero, norm_zero, zero_mul, Complex.ofReal_zero, charExt_zero, mul_zero]
  by_cases hD : (a : v.adicCompletion ℚ) / z - x / z * w = 0
  · simp only [hD, norm_zero, pow_two, inv_zero, mul_zero, zero_mul, Complex.ofReal_zero, charExt_zero]

  have hval : Valued.v (-w / ((a : v.adicCompletion ℚ) / z - x / z * w)) =
      Valued.v (w / ((a : v.adicCompletion ℚ) / z - x / z * w)) := by
    rw [neg_div, Valuation.map_neg]
  by_cases hle : Valued.v (w / ((a : v.adicCompletion ℚ) / z - x / z * w)) ≤ WithZero.exp c
  swap
  ·
    have hle' : ¬ Valued.v (-w / ((a : v.adicCompletion ℚ) / z - x / z * w)) ≤ WithZero.exp c := by rwa [hval]
    rw [if_neg hle', if_neg hle]
    simp only [zero_mul, mul_zero]
  have hle' : Valued.v (-w / ((a : v.adicCompletion ℚ) / z - x / z * w)) ≤ WithZero.exp c := by rwa [hval]
  rw [if_pos hle', if_pos hle, cellSectionOf_torusCellPoint_moebius v ν Φ a x z w hz hD]

  have hψ : (psiLocal ℚ v (-(x + -w / ((a : v.adicCompletion ℚ) / z - x / z * w))) : ℂ) =
      psiLocal ℚ v (-x) * psiLocal ℚ v (w / ((a : v.adicCompletion ℚ) / z - x / z * w)) := by
    rw [show -(x + -w / ((a : v.adicCompletion ℚ) / z - x / z * w)) =
        -x + w / ((a : v.adicCompletion ℚ) / z - x / z * w) by ring,
      AddChar.map_add_eq_mul]
  rw [hψ, modulus_real_eq_norm v ((a : v.adicCompletion ℚ) / z - x / z * w)]

  have hB := moebius_norm_bookkeeping ‖(a : v.adicCompletion ℚ) / z‖ ‖(a : v.adicCompletion ℚ) / z - x / z * w‖
    ‖(a : v.adicCompletion ℚ)‖
    (norm_ne_zero_iff.mpr hD) (norm_ne_zero_iff.mpr ha)
  have hBC := congrArg (fun r : ℝ => (r : ℂ)) hB
  push_cast at hBC ⊢
  linear_combination ((psiLocal ℚ v (-x) : ℂ) * (psiLocal ℚ v (w / ((a : v.adicCompletion ℚ) / z - x / z * w)) : ℂ) *
    (charExt (ν 0) (-1) * charExt (ν 1) (-1)) * charExt (ν 0 * (ν 1)⁻¹) ((a : v.adicCompletion ℚ) / z - x / z * w) *
    charExt (ν 1 * (ν 2)⁻¹) ((a : v.adicCompletion ℚ) / z) * ((ν 2 a : ℂˣ) : ℂ) *
    Φ ![x / z, (a : v.adicCompletion ℚ) / z, w]) * hBC

end CoupledIntegrand

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TallBoxCoupled

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

private noncomputable def innerK (c : ℤ) (u r w : v.adicCompletion ℚ) : ℂ :=
  Φ ![u, r, w] *
    (charExt (ν 0 * (ν 1)⁻¹) (r - u * w) * ((modulus (r - u * w) : ℝ) : ℂ)⁻¹) *
    (if Valued.v (w / (r - u * w)) ≤ WithZero.exp c then (psiLocal ℚ v (w / (r - u * w)) : ℂ) else 0)

private noncomputable def innerI (c : ℤ) (u r : v.adicCompletion ℚ) : ℂ :=
  ∫ w, innerK v ν Φ c u r w ∂(selfDualHaarAt ℚ v)

private noncomputable def torusPrefactor (a : (v.adicCompletion ℚ)ˣ) (z : v.adicCompletion ℚ) : ℂ :=
  charExt (ν 0) (-1) * charExt (ν 1) (-1) *
      (charExt (ν 1 * (ν 2)⁻¹) ((a : v.adicCompletion ℚ) / z) * ((ν 2 a : ℂˣ) : ℂ)) *
    ((‖(a : v.adicCompletion ℚ) / z‖ ^ 2 / ‖(a : v.adicCompletion ℚ)‖ : ℝ) : ℂ)

private theorem integral_jacquetHaar3_eq_integral_zxy
    (H : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ) (hH : Integrable H (jacquetHaar3 v)) :
    ∫ p, H p ∂(jacquetHaar3 v) =
      ∫ z, ∫ x, ∫ y, H (x, y, z) ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) := by
  haveI : SFinite (selfDualHaarAt ℚ v) := sFinite_selfDualHaarAt ℚ v
  have hJ : jacquetHaar3 v = (selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) := rfl
  rw [hJ] at hH ⊢
  have hA := measurePreserving_prodAssoc (selfDualHaarAt ℚ v) (selfDualHaarAt ℚ v) (selfDualHaarAt ℚ v)

  have hperm : Integrable (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      H (MeasurableEquiv.prodAssoc q.swap))
      ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))) :=
    (hA.integrable_comp_of_integrable hH).swap
  rw [← hA.integral_comp' H, ← integral_prod_swap (fun q => H (MeasurableEquiv.prodAssoc q)),
    integral_prod _ hperm]
  refine integral_congr_ae ?_
  filter_upwards [hperm.prod_right_ae] with z hz
  rw [integral_prod _ hz]
  rfl

private theorem integral_indicator_tallBox_torusIntegrand (a : (v.adicCompletion ℚ)ˣ) (c c' : ℤ)
    (x z : v.adicCompletion ℚ) :
    ∫ y, (tallBox v c c').indicator (torusIntegrand v ν Φ a) (x, y, z) ∂(selfDualHaarAt ℚ v) =
      (if Valued.v x ≤ WithZero.exp c then (1 : ℂ) else 0) *
          (if Valued.v z ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
        ((psiLocal ℚ v (-x) : ℂ) * torusPrefactor v ν a z *
          innerI v ν Φ c (x / z) ((a : v.adicCompletion ℚ) / z)) := by

  have hpt : ∀ y, (tallBox v c c').indicator (torusIntegrand v ν Φ a) (x, y, z) =
      (if Valued.v x ≤ WithZero.exp c then (1 : ℂ) else 0) *
          (if Valued.v z ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
        ((if Valued.v y ≤ WithZero.exp c then (psiLocal ℚ v (-(x + y)) : ℂ) else 0) *
          cellSectionOf v ν Φ (torusCellPoint v x y z a)) := by
    intro y
    classical
    rw [Set.indicator_apply]
    simp only [tallBox, Set.mem_setOf_eq, torusIntegrand]
    by_cases hx : Valued.v x ≤ WithZero.exp c <;> by_cases hy : Valued.v y ≤ WithZero.exp c <;>
      by_cases hz : Valued.v z ≤ WithZero.exp (2 * c') <;> simp [hx, hy, hz]
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  by_cases hz0 : z = 0
  ·
    subst hz0
    have hzero : ∀ y, cellSectionOf v ν Φ (torusCellPoint v x y 0 a) = 0 := fun y =>
      cellSectionOf_apply_of_notMem v ν Φ (fun h => ((torusCellPoint_mem_bigCell3_iff v x y 0 a).mp h).1 rfl)
    simp [hzero, torusPrefactor]
  · have hβ : (a : v.adicCompletion ℚ) / z ≠ 0 := div_ne_zero a.ne_zero hz0
    have hM := integral_eq_integral_comp_moebius v (x / z) ((a : v.adicCompletion ℚ) / z) hβ
      (fun y => (if Valued.v y ≤ WithZero.exp c then (psiLocal ℚ v (-(x + y)) : ℂ) else 0) *
        cellSectionOf v ν Φ (torusCellPoint v x y z a))
    beta_reduce at hM
    rw [hM]
    simp_rw [moebiusDensity_mul_torusIntegrand_eq v ν Φ a c x z]
    rw [integral_const_mul]
    rfl

private theorem integral_dilation_step (a : (v.adicCompletion ℚ)ˣ) (c c' : ℤ) (z : v.adicCompletion ℚ)
    (I : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ) :
    ∫ x, (if Valued.v x ≤ WithZero.exp c then (1 : ℂ) else 0) *
          (if Valued.v z ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
        ((psiLocal ℚ v (-x) : ℂ) * torusPrefactor v ν a z * I (x / z) ((a : v.adicCompletion ℚ) / z))
        ∂(selfDualHaarAt ℚ v) =
      (if Valued.v z ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) * torusPrefactor v ν a z * (‖z‖ : ℂ) *
        ∫ u, (if Valued.v (u * z) ≤ WithZero.exp c then (psiLocal ℚ v (-(u * z)) : ℂ) else 0) *
          I u ((a : v.adicCompletion ℚ) / z) ∂(selfDualHaarAt ℚ v) := by
  by_cases hz0 : z = 0
  · subst hz0
    simp [torusPrefactor]
  rw [integral_eq_norm_mul_integral_comp_mul_right v z hz0, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  beta_reduce
  rw [mul_div_assoc, div_self hz0, mul_one]
  by_cases hu : Valued.v (u * z) ≤ WithZero.exp c
  · rw [if_pos hu, if_pos hu]
    ring
  · rw [if_neg hu, if_neg hu]
    ring

private theorem quotient_norm_bookkeeping (N R : ℝ) (hN : N ≠ 0) (hR : R ≠ 0) :
    N * (R ^ 2)⁻¹ * (R ^ 2 / N) * (N / R) = N / R := by
  field_simp

private theorem integral_quotient_step (a : (v.adicCompletion ℚ)ˣ) (c' : ℤ)
    (G : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ) :
    ∫ z, (if Valued.v z ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) * torusPrefactor v ν a z * (‖z‖ : ℂ) *
        G z ((a : v.adicCompletion ℚ) / z) ∂(selfDualHaarAt ℚ v) =
      ∫ r, (if Valued.v ((a : v.adicCompletion ℚ) / r) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
          (charExt (ν 0) (-1) * charExt (ν 1) (-1) * (charExt (ν 1 * (ν 2)⁻¹) r * ((ν 2 a : ℂˣ) : ℂ))) *
          ((‖(a : v.adicCompletion ℚ)‖ / ‖r‖ : ℝ) : ℂ) *
        G ((a : v.adicCompletion ℚ) / r) r ∂(selfDualHaarAt ℚ v) := by
  have ha : (a : v.adicCompletion ℚ) ≠ 0 := a.ne_zero
  have h := integral_eq_integral_comp_div v (a : v.adicCompletion ℚ) ha
    (fun z => (if Valued.v z ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) * torusPrefactor v ν a z * (‖z‖ : ℂ) *
      G z ((a : v.adicCompletion ℚ) / z))
  beta_reduce at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  beta_reduce
  by_cases hr : r = 0
  · subst hr
    simp [torusPrefactor]
  rw [div_div_cancel₀ ha]
  unfold torusPrefactor
  rw [div_div_cancel₀ ha, norm_div]
  have hB := quotient_norm_bookkeeping ‖(a : v.adicCompletion ℚ)‖ ‖r‖ (norm_ne_zero_iff.mpr ha)
    (norm_ne_zero_iff.mpr hr)
  have hBC := congrArg (fun t : ℝ => (t : ℂ)) hB
  push_cast at hBC ⊢
  linear_combination ((if Valued.v ((a : v.adicCompletion ℚ) / r) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
    (charExt (ν 0) (-1) * charExt (ν 1) (-1) * (charExt (ν 1 * (ν 2)⁻¹) r * ((ν 2 a : ℂˣ) : ℂ))) *
    G ((a : v.adicCompletion ℚ) / r) r) * hBC

private theorem setIntegral_tallBox_torusIntegrand_eq (a : (v.adicCompletion ℚ)ˣ) (c c' : ℤ)
    (hint : IntegrableOn (torusIntegrand v ν Φ a) (tallBox v c c') (jacquetHaar3 v)) :
    ∫ p in tallBox v c c', torusIntegrand v ν Φ a p ∂(jacquetHaar3 v) =
      ∫ r, (if Valued.v ((a : v.adicCompletion ℚ) / r) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
          (charExt (ν 0) (-1) * charExt (ν 1) (-1) * (charExt (ν 1 * (ν 2)⁻¹) r * ((ν 2 a : ℂˣ) : ℂ))) *
          ((‖(a : v.adicCompletion ℚ)‖ / ‖r‖ : ℝ) : ℂ) *
        ∫ u, (if Valued.v (u * ((a : v.adicCompletion ℚ) / r)) ≤ WithZero.exp c then
              (psiLocal ℚ v (-(u * ((a : v.adicCompletion ℚ) / r))) : ℂ) else 0) *
          innerI v ν Φ c u r ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v) := by
  have hmeas : MeasurableSet (tallBox v c c') := measurableSet_tallBox v c c'
  rw [← integral_indicator hmeas,
    integral_jacquetHaar3_eq_integral_zxy v _ ((integrable_indicator_iff hmeas).mpr hint)]
  simp_rw [integral_indicator_tallBox_torusIntegrand v ν Φ a c c',
    integral_dilation_step v ν a c c' (I := innerI v ν Φ c)]
  exact integral_quotient_step v ν a c' fun z r =>
    ∫ u, (if Valued.v (u * z) ≤ WithZero.exp c then (psiLocal ℚ v (-(u * z)) : ℂ) else 0) * innerI v ν Φ c u r
      ∂(selfDualHaarAt ℚ v)

end TallBoxCoupled

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq.LanglandsTunnell.TateLocal"
open scoped ENNReal

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section SwapDevice

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

local notation "dmul" => mulMeasure (selfDualHaarAt ℚ v)
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "Kv3" => Prod (Prod (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)

private theorem selfDualHaarAt_singleton_zero : selfDualHaarAt ℚ v {(0 : Kv)} = 0 := by
  haveI : BorelSpace (Kv) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI : MeasurableSingletonClass (Kv) := measurableSingletonClass_adicCompletion ℚ v
  by_contra h0

  have hsame : ∀ x : Kv, selfDualHaarAt ℚ v {(0 : Kv)} ≤ selfDualHaarAt ℚ v {x} := by
    intro x
    have hpre : (fun y : Kv => y + -x) ⁻¹' {0} = {x} := by
      ext y
      simp [← sub_eq_add_neg, sub_eq_zero]
    rw [← hpre, measure_preimage_add_right]

  have hnat : ∀ n : ℕ, Valued.v ((n : Kv)) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.cast_succ]
        exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))
  haveI : CharZero (Kv) := charZero_of_injective_algebraMap (algebraMap ℚ (Kv)).injective
  have hinf : (Set.range (fun n : ℕ => (n : Kv))).Infinite :=
    Set.infinite_range_of_injective Nat.cast_injective
  have htop := hinf.meas_eq_top (μ := selfDualHaarAt ℚ v) ⟨_, h0, fun x _ => hsame x⟩
  have hsub : Set.range (fun n : ℕ => (n : Kv)) ⊆
      (integersPositiveCompacts ℚ v : Set (Kv)) := by
    rintro _ ⟨n, rfl⟩
    rw [coe_integersPositiveCompacts]
    show Valued.v ((n : Kv)) ≤ 1
    exact hnat n
  have hlt : selfDualHaarAt ℚ v (Set.range (fun n : ℕ => (n : Kv))) < ∞ :=
    (measure_mono hsub).trans_lt (integersPositiveCompacts ℚ v).isCompact.measure_lt_top
  exact absurd htop hlt.ne

private theorem ae_ne_zero_selfDualHaarAt : ∀ᵐ x ∂(selfDualHaarAt ℚ v), x ≠ 0 := by
  rw [ae_iff]
  simpa only [ne_eq, not_not, Set.setOf_eq_eq_singleton] using selfDualHaarAt_singleton_zero v

private theorem integral_eq_integral_norm_mul_mulMeasure' (f : Kv → ℂ) :
    ∫ x, f x ∂(selfDualHaarAt ℚ v) = ∫ x, (‖x‖ : ℂ) * f x ∂dmul := by
  have hc : ({0}ᶜ : Set (Kv)).indicator f 0 = 0 := Set.indicator_of_notMem (by simp) f
  have h1 : ∫ x, f x ∂(selfDualHaarAt ℚ v) = ∫ x, ({0}ᶜ : Set (Kv)).indicator f x ∂(selfDualHaarAt ℚ v) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero_selfDualHaarAt v] with x hx
    rw [Set.indicator_of_mem (show x ∈ ({0}ᶜ : Set (Kv)) from hx)]
  rw [h1, integral_eq_integral_norm_mul_mulMeasure v _ hc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x = 0
  · subst hx
    simp
  · show (‖x‖ : ℂ) * ({0}ᶜ : Set (Kv)).indicator f x = (‖x‖ : ℂ) * f x
    rw [Set.indicator_of_mem (show x ∈ ({0}ᶜ : Set (Kv)) from hx)]

private theorem mulMeasure_apply_singleton_zero :
    dmul ({0} : Set (Kv)) = 0 := by
  haveI : MeasurableSingletonClass (Kv) := measurableSingletonClass_adicCompletion ℚ v
  unfold mulMeasure
  rw [withDensity_apply _ (measurableSet_singleton 0), Measure.restrict_restrict (measurableSet_singleton 0),
    Set.inter_compl_self, Measure.restrict_empty, lintegral_zero_measure]

private theorem prod_mulMeasure_axes :
    (Measure.prod dmul dmul)
      ((({0} : Set (Kv)) ×ˢ Set.univ) ∪ (Set.univ ×ˢ ({0} : Set (Kv)))) = 0 := by
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  have h0 := mulMeasure_apply_singleton_zero v
  exact measure_union_null (by rw [Measure.prod_prod, h0, zero_mul]) (by rw [Measure.prod_prod, h0, mul_zero])

private theorem ae_fst_ne_zero_and_snd_ne_zero :
    ∀ᵐ p ∂(Measure.prod dmul dmul), p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  filter_upwards [compl_mem_ae_iff.mpr (prod_mulMeasure_axes v)] with p hp
  simpa only [Set.mem_compl_iff, Set.mem_union, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true,
    true_and, not_or, ne_eq] using hp

open scoped Classical in

private noncomputable def skewFun (q : Kv3) : Kv :=
  if q.1.1 = 0 ∨ q.1.2 = 0 then q.2 else q.1.1 * (q.1.2)⁻¹ * q.2

open scoped Classical in

private noncomputable def skewInv (q : Kv3) : Kv :=
  if q.1.1 = 0 ∨ q.1.2 = 0 then q.2 else q.1.2 * (q.1.1)⁻¹ * q.2

private theorem skewFun_of_not {q : Kv3} (h : ¬ (q.1.1 = 0 ∨ q.1.2 = 0)) :
    skewFun v q = q.1.1 * (q.1.2)⁻¹ * q.2 := by
  simp [skewFun, h]

private theorem skewFun_of {q : Kv3} (h : q.1.1 = 0 ∨ q.1.2 = 0) : skewFun v q = q.2 := by
  simp [skewFun, h]

private theorem skewInv_of_not {q : Kv3} (h : ¬ (q.1.1 = 0 ∨ q.1.2 = 0)) :
    skewInv v q = q.1.2 * (q.1.1)⁻¹ * q.2 := by
  simp [skewInv, h]

private theorem skewInv_of {q : Kv3} (h : q.1.1 = 0 ∨ q.1.2 = 0) : skewInv v q = q.2 := by
  simp [skewInv, h]

private theorem measurableSet_axes :
    MeasurableSet {q : Kv3 | q.1.1 = 0 ∨ q.1.2 = 0} := by
  haveI : MeasurableSingletonClass (Kv) := measurableSingletonClass_adicCompletion ℚ v
  exact ((measurableSet_singleton 0).preimage measurable_fst.fst).union
    ((measurableSet_singleton 0).preimage measurable_fst.snd)

private theorem measurable_skewFun : Measurable (skewFun v) := by
  haveI : BorelSpace (Kv) := borelSpace_localBorel ℚ v
  unfold skewFun
  exact Measurable.ite (measurableSet_axes v) measurable_snd
    ((measurable_fst.fst.mul measurable_fst.snd.inv).mul measurable_snd)

private theorem measurable_skewInv : Measurable (skewInv v) := by
  haveI : BorelSpace (Kv) := borelSpace_localBorel ℚ v
  unfold skewInv
  exact Measurable.ite (measurableSet_axes v) measurable_snd
    ((measurable_fst.snd.mul measurable_fst.fst.inv).mul measurable_snd)

private noncomputable def skewEquiv : Kv3 ≃ᵐ Kv3 where
  toFun q := (q.1, skewFun v q)
  invFun q := (q.1, skewInv v q)
  left_inv q := by
    by_cases h : q.1.1 = 0 ∨ q.1.2 = 0
    · rw [Prod.ext_iff]
      exact ⟨rfl, (skewInv_of v (q := (q.1, skewFun v q)) h).trans (skewFun_of v h)⟩
    · obtain ⟨hr, hu⟩ := not_or.mp h
      rw [Prod.ext_iff]
      refine ⟨rfl, ?_⟩
      show skewInv v (q.1, skewFun v q) = q.2
      rw [skewInv_of_not v (q := (q.1, skewFun v q)) h, skewFun_of_not v h]
      show q.1.2 * (q.1.1)⁻¹ * (q.1.1 * (q.1.2)⁻¹ * q.2) = q.2
      rw [show q.1.2 * (q.1.1)⁻¹ * (q.1.1 * (q.1.2)⁻¹ * q.2) = q.1.2 * (q.1.2)⁻¹ * ((q.1.1)⁻¹ * q.1.1) * q.2 by ring,
        mul_inv_cancel₀ hu, inv_mul_cancel₀ hr, one_mul, one_mul]
  right_inv q := by
    by_cases h : q.1.1 = 0 ∨ q.1.2 = 0
    · rw [Prod.ext_iff]
      exact ⟨rfl, (skewFun_of v (q := (q.1, skewInv v q)) h).trans (skewInv_of v h)⟩
    · obtain ⟨hr, hu⟩ := not_or.mp h
      rw [Prod.ext_iff]
      refine ⟨rfl, ?_⟩
      show skewFun v (q.1, skewInv v q) = q.2
      rw [skewFun_of_not v (q := (q.1, skewInv v q)) h, skewInv_of_not v h]
      show q.1.1 * (q.1.2)⁻¹ * (q.1.2 * (q.1.1)⁻¹ * q.2) = q.2
      rw [show q.1.1 * (q.1.2)⁻¹ * (q.1.2 * (q.1.1)⁻¹ * q.2) = q.1.1 * (q.1.1)⁻¹ * ((q.1.2)⁻¹ * q.1.2) * q.2 by ring,
        mul_inv_cancel₀ hr, inv_mul_cancel₀ hu, one_mul, one_mul]
  measurable_toFun := measurable_fst.prodMk (measurable_skewFun v)
  measurable_invFun := measurable_fst.prodMk (measurable_skewInv v)

private theorem skewEquiv_apply (q : Kv3) : skewEquiv v q = (q.1, skewFun v q) := rfl

private theorem measurePreserving_skewEquiv :
    MeasurePreserving (skewEquiv v) (Measure.prod (Measure.prod dmul dmul) dmul)
      (Measure.prod (Measure.prod dmul dmul) dmul) := by
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  have hg : ∀ p : Kv × Kv,
      Measure.map (fun t => skewFun v (p, t)) dmul = dmul := by
    intro p
    by_cases h : p.1 = 0 ∨ p.2 = 0
    · have hid : (fun t => skewFun v (p, t)) = id := funext fun t => skewFun_of v (q := (p, t)) h
      rw [hid, Measure.map_id]
    · obtain ⟨h1, h2⟩ := not_or.mp h
      have hc : p.1 * (p.2)⁻¹ ≠ 0 := mul_ne_zero h1 (inv_ne_zero h2)
      have hfun : (fun t => skewFun v (p, t)) =
          fun t => ((Units.mk0 _ hc : (Kv)ˣ) : Kv) * t :=
        funext fun t => by rw [skewFun_of_not v (q := (p, t)) h, Units.val_mk0]
      rw [hfun]
      exact map_mul_left_mulMeasure ℚ v (Units.mk0 _ hc)
  have h := MeasurePreserving.skew_product (μa := Measure.prod dmul dmul)
    (μc := dmul) (g := fun p t => skewFun v (p, t))
    (MeasurePreserving.id (Measure.prod dmul dmul)) (measurable_skewFun v) (Filter.Eventually.of_forall hg)
  exact h

private theorem integral_integral_integral_swap_scale
    (Φ₂ : Kv → Kv × Kv → ℂ) (T : Kv3 → ℂ)
    (hT : Integrable T (Measure.prod (Measure.prod dmul dmul) dmul))
    (hpt : ∀ p : Kv × Kv, ∀ t : Kv, p.1 ≠ 0 → p.2 ≠ 0 →
      Φ₂ (p.1 * (p.2)⁻¹ * t) p = T (p, t)) :
    ∫ b, ∫ r, ∫ u, Φ₂ b (r, u) ∂dmul ∂dmul ∂dmul =
      ∫ r, ∫ u, ∫ t, T ((r, u), t) ∂dmul ∂dmul ∂dmul := by
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  have hp := ae_fst_ne_zero_and_snd_ne_zero v

  have hq : ∀ᵐ q ∂(Measure.prod (Measure.prod dmul dmul) dmul), q.1.1 ≠ 0 ∧ q.1.2 ≠ 0 := by
    have hN : (Measure.prod (Measure.prod dmul dmul) dmul)
        (((({0} : Set (Kv)) ×ˢ Set.univ) ∪ (Set.univ ×ˢ ({0} : Set (Kv)))) ×ˢ Set.univ) = 0 := by
      rw [Measure.prod_prod, prod_mulMeasure_axes v, zero_mul]
    filter_upwards [compl_mem_ae_iff.mpr hN] with q hq
    simpa only [Set.mem_compl_iff, Set.mem_union, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true,
      true_and, not_or, ne_eq] using hq

  have hae : (fun q => Φ₂ (skewEquiv v q).2 (skewEquiv v q).1) =ᵐ[Measure.prod (Measure.prod dmul dmul) dmul] T := by
    filter_upwards [hq] with q hq
    show Φ₂ (skewFun v q) q.1 = T q
    rw [skewFun_of_not v (not_or.mpr hq), hpt q.1 q.2 hq.1 hq.2]
  have hskew : Integrable (fun q => Φ₂ (skewEquiv v q).2 (skewEquiv v q).1)
      (Measure.prod (Measure.prod dmul dmul) dmul) := hT.congr hae.symm
  have hH : Integrable (fun q : Kv3 => Φ₂ q.2 q.1) (Measure.prod (Measure.prod dmul dmul) dmul) :=
    ((measurePreserving_skewEquiv v).integrable_comp_emb (skewEquiv v).measurableEmbedding).mp hskew

  have hΦ : Integrable (Function.uncurry Φ₂) (Measure.prod dmul (Measure.prod dmul dmul)) := hH.swap
  have hT' : Integrable (fun p => ∫ t, T (p, t) ∂dmul) (Measure.prod dmul dmul) := hT.integral_prod_left
  calc ∫ b, ∫ r, ∫ u, Φ₂ b (r, u) ∂dmul ∂dmul ∂dmul
      = ∫ b, ∫ p, Φ₂ b p ∂(Measure.prod dmul dmul) ∂dmul := by
        refine integral_congr_ae ?_
        filter_upwards [hΦ.prod_right_ae] with b hb
        exact (integral_prod _ hb).symm
    _ = ∫ p, ∫ b, Φ₂ b p ∂dmul ∂(Measure.prod dmul dmul) := integral_integral_swap hΦ
    _ = ∫ p, ∫ t, T (p, t) ∂dmul ∂(Measure.prod dmul dmul) := by
        refine integral_congr_ae ?_
        filter_upwards [hp] with p hp'
        have hc : p.1 * (p.2)⁻¹ ≠ 0 := mul_ne_zero hp'.1 (inv_ne_zero hp'.2)
        have h6 := integral_mul_left_mulMeasure ℚ v (p.1 * (p.2)⁻¹) hc (fun b => Φ₂ b p)
        beta_reduce at h6
        rw [← h6]
        exact integral_congr_ae (Filter.Eventually.of_forall fun t => hpt p t hp'.1 hp'.2)
    _ = ∫ r, ∫ u, ∫ t, T ((r, u), t) ∂dmul ∂dmul ∂dmul := integral_prod _ hT'

end SwapDevice

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 jacquetHaar3 bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section LevelIdentity

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

local notation "dmul" => mulMeasure (selfDualHaarAt ℚ v)
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v

private theorem charExt_charMul (η θ : Kvˣ →* ℂˣ) (x : Kv) : charExt (η * θ) x = charExt η x * charExt θ x := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hx, MonoidHom.mul_apply,
      Units.val_mul]

private theorem charExt_charInv (θ : Kvˣ →* ℂˣ) (x : Kv) : charExt θ⁻¹ x = (charExt θ x)⁻¹ := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hx, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

private theorem charExt_ne_zero_of_ne_zero (η : Kvˣ →* ℂˣ) {x : Kv} (hx : x ≠ 0) : charExt η x ≠ 0 := by
  rw [charExt_of_ne_zero _ hx]
  exact Units.ne_zero _

private theorem cpow_norm_mul_inv_mul (x y z : Kv) (s : ℂ) :
    ((‖x * y⁻¹ * z‖ : ℝ) : ℂ) ^ s = ((‖x‖ : ℝ) : ℂ) ^ s * (((‖y‖ : ℝ) : ℂ) ^ s)⁻¹ * ((‖z‖ : ℝ) : ℂ) ^ s := by
  have harg : ((‖y‖ : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (norm_nonneg y)]
    exact Real.pi_pos.ne
  rw [norm_mul, norm_mul, norm_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (mul_nonneg (norm_nonneg x) (inv_nonneg.mpr (norm_nonneg y))) (norm_nonneg z),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg x) (inv_nonneg.mpr (norm_nonneg y)),
    Complex.ofReal_inv, Complex.inv_cpow _ _ harg]

private theorem weights_of_torusPoint (χ : Kvˣ →* ℂˣ) (s : ℂ) (r u t : Kv) (hr : r ≠ 0) (hu : u ≠ 0)
    (ht : t ≠ 0) :
    (‖r * u⁻¹ * t‖ : ℂ)⁻¹ * (charExt χ (r * u⁻¹ * t) * ((modulus (r * u⁻¹ * t) : ℝ) : ℂ) ^ s) * (‖r‖ : ℂ) *
          (charExt (ν 1 * (ν 2)⁻¹) r * charExt (ν 2) (r * u⁻¹ * t)) * ((‖r * u⁻¹ * t‖ / ‖r‖ : ℝ) : ℂ) *
        (‖u‖ : ℂ) =
      charExt (ν 2 * χ) t * ((modulus t : ℝ) : ℂ) ^ s *
        (charExt (ν 2 * χ)⁻¹ u * ((modulus u : ℝ) : ℂ) ^ (1 - s) * charExt (ν 1 * χ) r *
          ((modulus r : ℝ) : ℂ) ^ s) := by
  have hrC : ((‖r‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hr)
  have huC : ((‖u‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu)
  have htC : ((‖t‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ht)
  have hν2r := charExt_ne_zero_of_ne_zero v (ν 2) hr
  have hν2u := charExt_ne_zero_of_ne_zero v (ν 2) hu
  have hχu := charExt_ne_zero_of_ne_zero v χ hu
  have hus : ((‖u‖ : ℝ) : ℂ) ^ s ≠ 0 := fun h => huC ((Complex.cpow_eq_zero_iff _ _).mp h).1

  rw [charExt_mul_inv_of_ne_zero v (ν 1) (ν 2) hr]
  simp only [charExt_mul, charExt_charMul, charExt_charInv, charExt_inv_of_ne_zero v _ hu]

  simp only [modulus_real_eq_norm]
  rw [cpow_norm_mul_inv_mul, Complex.cpow_sub _ _ huC, Complex.cpow_one, norm_mul, norm_mul, norm_inv]
  push_cast
  field_simp

private noncomputable def gaussKer (χ : Kvˣ →* ℂˣ) (s : ℂ) (c : ℤ) (t : Kv) : ℂ :=
  (if Valued.v (-t) ≤ WithZero.exp c then (psiLocal ℚ v (-t) : ℂ) else 0) * charExt (ν 2 * χ) t *
    ((modulus t : ℝ) : ℂ) ^ s

private noncomputable def cWeight (χ : Kvˣ →* ℂˣ) (s : ℂ) (u r : Kv) : ℂ :=
  charExt (ν 2 * χ)⁻¹ u * ((modulus u : ℝ) : ℂ) ^ (1 - s) * charExt (ν 1 * χ) r * ((modulus r : ℝ) : ℂ) ^ s

open scoped Classical in

private noncomputable def jacquetTallBox (c c' : ℤ) (b : Kv) : ℂ :=
  if hb : b = 0 then 0 else ∫ p in tallBox v c c', torusIntegrand v ν Φ (Units.mk0 b hb) p ∂(jacquetHaar3 v)

private noncomputable def torusPhi (χ : Kvˣ →* ℂˣ) (s : ℂ) (c c' : ℤ) (S : Set Kv) (b : Kv) (p : Kv × Kv) : ℂ :=
  (S.indicator (fun _ => (1 : ℂ)) b * ((‖b‖ : ℂ)⁻¹ * (charExt χ b * ((modulus b : ℝ) : ℂ) ^ s))) *
    ((‖p.1‖ : ℂ) *
      ((if Valued.v (b / p.1) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
            (charExt (ν 0) (-1) * charExt (ν 1) (-1) * (charExt (ν 1 * (ν 2)⁻¹) p.1 * charExt (ν 2) b)) *
            ((‖b‖ / ‖p.1‖ : ℝ) : ℂ) *
        ((‖p.2‖ : ℂ) *
          ((if Valued.v (p.2 * (b / p.1)) ≤ WithZero.exp c then (psiLocal ℚ v (-(p.2 * (b / p.1))) : ℂ) else 0) *
            innerI v ν Φ c p.2 p.1))))

private noncomputable def torusT (χ : Kvˣ →* ℂˣ) (s : ℂ) (c c' : ℤ) (S : Set Kv) (q : (Kv × Kv) × Kv) : ℂ :=
  charExt (ν 0) (-1) * charExt (ν 1) (-1) *
    ((S.indicator (fun _ => (1 : ℂ)) (q.1.1 * (q.1.2)⁻¹ * q.2) *
          (if Valued.v ((q.1.2)⁻¹ * q.2) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) * gaussKer v ν χ s c q.2) *
      (cWeight v ν χ s q.1.2 q.1.1 * innerI v ν Φ c q.1.2 q.1.1))

private theorem jacquetTallBox_eq_of_ne_zero (c c' : ℤ) (b : Kv) (hb : b ≠ 0)
    (hint : ∀ a : Kvˣ, IntegrableOn (torusIntegrand v ν Φ a) (tallBox v c c') (jacquetHaar3 v)) :
    jacquetTallBox v ν Φ c c' b =
      ∫ r, (‖r‖ : ℂ) *
          ((if Valued.v (b / r) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
                (charExt (ν 0) (-1) * charExt (ν 1) (-1) * (charExt (ν 1 * (ν 2)⁻¹) r * charExt (ν 2) b)) *
                ((‖b‖ / ‖r‖ : ℝ) : ℂ) *
            ∫ u, (‖u‖ : ℂ) *
                ((if Valued.v (u * (b / r)) ≤ WithZero.exp c then (psiLocal ℚ v (-(u * (b / r))) : ℂ) else 0) *
                  innerI v ν Φ c u r) ∂dmul) ∂dmul := by
  unfold jacquetTallBox
  rw [dif_neg hb, setIntegral_tallBox_torusIntegrand_eq v ν Φ (Units.mk0 b hb) c c' (hint _),
    ← charExt_of_ne_zero (ν 2) hb, Units.val_mk0]
  simp_rw [integral_eq_integral_norm_mul_mulMeasure' v]

private theorem torusPhi_mk (χ : Kvˣ →* ℂˣ) (s : ℂ) (c c' : ℤ) (S : Set Kv) (b r u : Kv) :
    torusPhi v ν Φ χ s c c' S b (r, u) =
      S.indicator (fun _ => (1 : ℂ)) b * ((‖b‖ : ℂ)⁻¹ * (charExt χ b * ((modulus b : ℝ) : ℂ) ^ s)) *
        ((‖r‖ : ℂ) *
          ((if Valued.v (b / r) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
                (charExt (ν 0) (-1) * charExt (ν 1) (-1) * (charExt (ν 1 * (ν 2)⁻¹) r * charExt (ν 2) b)) *
                ((‖b‖ / ‖r‖ : ℝ) : ℂ) *
            ((‖u‖ : ℂ) *
              ((if Valued.v (u * (b / r)) ≤ WithZero.exp c then (psiLocal ℚ v (-(u * (b / r))) : ℂ) else 0) *
                innerI v ν Φ c u r)))) :=
  rfl

private theorem indicator_torusIntegrand_eq (χ : Kvˣ →* ℂˣ) (s : ℂ) (c c' : ℤ) (S : Set Kv)
    (hint : ∀ a : Kvˣ, IntegrableOn (torusIntegrand v ν Φ a) (tallBox v c c') (jacquetHaar3 v)) (b : Kv) :
    S.indicator (fun b => jacquetTallBox v ν Φ c c' b / (‖b‖ : ℂ) * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s) b =
      ∫ r, ∫ u, torusPhi v ν Φ χ s c c' S b (r, u) ∂dmul ∂dmul := by

  have hinner : ∀ r : Kv, ∫ u, torusPhi v ν Φ χ s c c' S b (r, u) ∂dmul =
      S.indicator (fun _ => (1 : ℂ)) b * ((‖b‖ : ℂ)⁻¹ * (charExt χ b * ((modulus b : ℝ) : ℂ) ^ s)) *
        ((‖r‖ : ℂ) *
          ((if Valued.v (b / r) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
                (charExt (ν 0) (-1) * charExt (ν 1) (-1) * (charExt (ν 1 * (ν 2)⁻¹) r * charExt (ν 2) b)) *
                ((‖b‖ / ‖r‖ : ℝ) : ℂ) *
            ∫ u, (‖u‖ : ℂ) *
                ((if Valued.v (u * (b / r)) ≤ WithZero.exp c then (psiLocal ℚ v (-(u * (b / r))) : ℂ) else 0) *
                  innerI v ν Φ c u r) ∂dmul)) := by
    intro r
    simp_rw [torusPhi_mk]
    rw [integral_const_mul, integral_const_mul, integral_const_mul]
  simp_rw [hinner]
  rw [integral_const_mul]
  by_cases hb : b = 0
  · subst hb
    have h0 : S.indicator (fun b => jacquetTallBox v ν Φ c c' b / (‖b‖ : ℂ) * charExt χ b *
        ((modulus b : ℝ) : ℂ) ^ s) 0 = 0 :=
      Set.indicator_apply_eq_zero.mpr (fun _ => by simp)
    rw [h0]
    simp
  by_cases hbS : b ∈ S
  · rw [Set.indicator_of_mem hbS, Set.indicator_of_mem hbS, jacquetTallBox_eq_of_ne_zero v ν Φ c c' b hb hint]
    ring
  · rw [Set.indicator_of_notMem hbS, Set.indicator_of_notMem hbS]
    simp

private theorem torusPhi_torusPoint (χ : Kvˣ →* ℂˣ) (s : ℂ) (c c' : ℤ) (S : Set Kv) (p : Kv × Kv) (t : Kv)
    (hr : p.1 ≠ 0) (hu : p.2 ≠ 0) :
    torusPhi v ν Φ χ s c c' S (p.1 * (p.2)⁻¹ * t) p = torusT v ν Φ χ s c c' S (p, t) := by
  obtain ⟨r, u⟩ := p
  change r ≠ 0 at hr
  change u ≠ 0 at hu
  by_cases ht : t = 0
  · subst ht
    simp [torusPhi, torusT, gaussKer]
  simp only [torusPhi, torusT, gaussKer, cWeight]
  have hbr : r * u⁻¹ * t / r = u⁻¹ * t := by rw [mul_assoc, mul_div_cancel_left₀ _ hr]
  have hub : u * (u⁻¹ * t) = t := mul_inv_cancel_left₀ hu t
  simp only [hbr, hub, Valuation.map_neg]
  linear_combination (S.indicator (fun _ => (1 : ℂ)) (r * u⁻¹ * t) *
    (if Valued.v (u⁻¹ * t) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) * (charExt (ν 0) (-1) * charExt (ν 1) (-1)) *
    (if Valued.v t ≤ WithZero.exp c then (psiLocal ℚ v (-t) : ℂ) else 0) * innerI v ν Φ c u r) *
    weights_of_torusPoint v ν χ s r u t hr hu ht

private theorem norm_indicator_one_mul_ite_le (S : Set Kv) (x y : Kv) (c' : ℤ) :
    ‖S.indicator (fun _ => (1 : ℂ)) x * (if Valued.v y ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0)‖ ≤ 1 := by
  rw [norm_mul]
  refine mul_le_one₀ ?_ (norm_nonneg _) ?_
  · by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, norm_one]
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact zero_le_one
  · by_cases hy : Valued.v y ≤ WithZero.exp (2 * c')
    · rw [if_pos hy, norm_one]
    · rw [if_neg hy, norm_zero]
      exact zero_le_one

private theorem integrable_torusT (χ : Kvˣ →* ℂˣ) (s : ℂ) (c c' : ℤ) (S : Set Kv) (hS : MeasurableSet S)
    (hIg : Integrable (gaussKer v ν χ s c) dmul)
    (hWI : Integrable (fun p : Kv × Kv => cWeight v ν χ s p.2 p.1 * innerI v ν Φ c p.2 p.1)
      (Measure.prod dmul dmul)) :
    Integrable (torusT v ν Φ χ s c c' S) (Measure.prod (Measure.prod dmul dmul) dmul) := by
  haveI : BorelSpace Kv := borelSpace_localBorel ℚ v
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  have hF := hWI.mul_prod hIg

  have hB : Measurable fun q : (Kv × Kv) × Kv =>
      S.indicator (fun _ => (1 : ℂ)) (q.1.1 * (q.1.2)⁻¹ * q.2) *
        (if Valued.v ((q.1.2)⁻¹ * q.2) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) := by
    refine Measurable.mul ?_ ?_
    · exact (measurable_const.indicator hS).comp ((measurable_fst.fst.mul measurable_fst.snd.inv).mul measurable_snd)
    · refine Measurable.ite ?_ measurable_const measurable_const
      exact (isClosed_valued_le v (2 * c')).measurableSet.preimage (measurable_fst.snd.inv.mul measurable_snd)
  have hT := (hF.bdd_mul hB.aestronglyMeasurable (Filter.Eventually.of_forall fun q =>
    norm_indicator_one_mul_ite_le v S _ _ c')).const_mul (charExt (ν 0) (-1) * charExt (ν 1) (-1))
  refine hT.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [torusT]
  ring

private theorem setIntegral_jacquetTallBox_mul_charExt_mul_cpow_eq (χ : Kvˣ →* ℂˣ) (s : ℂ) (c c' : ℤ)
    (S : Set Kv) (hS : MeasurableSet S)
    (hint : ∀ a : Kvˣ, IntegrableOn (torusIntegrand v ν Φ a) (tallBox v c c') (jacquetHaar3 v))
    (hIg : Integrable (gaussKer v ν χ s c) dmul)
    (hWI : Integrable (fun p : Kv × Kv => cWeight v ν χ s p.2 p.1 * innerI v ν Φ c p.2 p.1)
      (Measure.prod dmul dmul)) :
    ∫ b in S, jacquetTallBox v ν Φ c c' b / (‖b‖ : ℂ) * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s ∂dmul =
      charExt (ν 0) (-1) * charExt (ν 1) (-1) *
        ∫ r, ∫ u, (∫ t, S.indicator (fun _ => (1 : ℂ)) (r * u⁻¹ * t) *
              (if Valued.v (u⁻¹ * t) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) * gaussKer v ν χ s c t ∂dmul) *
            (cWeight v ν χ s u r * innerI v ν Φ c u r) ∂dmul ∂dmul := by
  rw [← integral_indicator hS]
  simp_rw [indicator_torusIntegrand_eq v ν Φ χ s c c' S hint]
  rw [integral_integral_integral_swap_scale v (torusPhi v ν Φ χ s c c' S) (torusT v ν Φ χ s c c' S)
    (integrable_torusT v ν Φ χ s c c' S hS hIg hWI) (fun p t hr hu => torusPhi_torusPoint v ν Φ χ s c c' S p t hr hu)]
  simp only [torusT]
  simp_rw [integral_const_mul, integral_mul_const]

end LevelIdentity

end LanglandsTunnell.CubicInduction

open MeasureTheory IsDedekindDomain NumberField _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq.LanglandsTunnell.TateLocal _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq.LanglandsTunnell.CubicInduction in
attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (c c' : ℤ)
    (J : v.adicCompletion ℚ → ℂ)
    (hJ : ∀ a : (v.adicCompletion ℚ)ˣ, J a =
      ∫ p in {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
          Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * c')},
        NumberField.StandardAddChar.psiLocal ℚ v (-(p.1 + p.2.1)) *
          cellSectionOf v ν Φ
            (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * (iotaGL (diagUnitGL2 a) * antidiagonal3 v))
        ∂(jacquetHaar3 v))
    (S : Set (v.adicCompletion ℚ)) (hS : MeasurableSet S)
    (hint : ∀ a : (v.adicCompletion ℚ)ˣ, IntegrableOn
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        NumberField.StandardAddChar.psiLocal ℚ v (-(p.1 + p.2.1)) *
          cellSectionOf v ν Φ
            (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * (iotaGL (diagUnitGL2 a) * antidiagonal3 v)))
      {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
          Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * c')}
      (jacquetHaar3 v))
    (hIg : Integrable
      (fun t : v.adicCompletion ℚ =>
        (if Valued.v (-t) ≤ WithZero.exp c then (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) else 0) *
          charExt (ν 2 * χ) t * ((modulus t : ℝ) : ℂ) ^ s)
      (mulMeasure (selfDualHaarAt ℚ v)))
    (hWI : Integrable
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ =>
        (charExt (ν 2 * χ)⁻¹ p.2 * ((modulus p.2 : ℝ) : ℂ) ^ (1 - s) * charExt (ν 1 * χ) p.1 *
            ((modulus p.1 : ℝ) : ℂ) ^ s) *
          ∫ w, Φ ![p.2, p.1, w] *
              (charExt (ν 0 * (ν 1)⁻¹) (p.1 - p.2 * w) * ((modulus (p.1 - p.2 * w) : ℝ) : ℂ)⁻¹) *
              (if Valued.v (w / (p.1 - p.2 * w)) ≤ WithZero.exp c then
                (NumberField.StandardAddChar.psiLocal ℚ v (w / (p.1 - p.2 * w)) : ℂ) else 0)
            ∂(selfDualHaarAt ℚ v))
      ((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v)))) :
    ∫ b in S, J b / (‖b‖ : ℂ) * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s ∂(mulMeasure (selfDualHaarAt ℚ v)) =
      charExt (ν 0) (-1) * charExt (ν 1) (-1) *
        ∫ r, ∫ u, (∫ t, S.indicator (fun _ => (1 : ℂ)) (r * u⁻¹ * t) *
              (if Valued.v (u⁻¹ * t) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
              ((if Valued.v (-t) ≤ WithZero.exp c then (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) else 0) *
                charExt (ν 2 * χ) t * ((modulus t : ℝ) : ℂ) ^ s) ∂(mulMeasure (selfDualHaarAt ℚ v))) *
            ((charExt (ν 2 * χ)⁻¹ u * ((modulus u : ℝ) : ℂ) ^ (1 - s) * charExt (ν 1 * χ) r *
                ((modulus r : ℝ) : ℂ) ^ s) *
              ∫ w, Φ ![u, r, w] *
                  (charExt (ν 0 * (ν 1)⁻¹) (r - u * w) * ((modulus (r - u * w) : ℝ) : ℂ)⁻¹) *
                  (if Valued.v (w / (r - u * w)) ≤ WithZero.exp c then
                    (NumberField.StandardAddChar.psiLocal ℚ v (w / (r - u * w)) : ℂ) else 0)
                ∂(selfDualHaarAt ℚ v))
          ∂(mulMeasure (selfDualHaarAt ℚ v)) ∂(mulMeasure (selfDualHaarAt ℚ v)) := by
  have hJ' : (fun b => J b / (‖b‖ : ℂ) * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s) =
      fun b => jacquetTallBox v ν Φ c c' b / (‖b‖ : ℂ) * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s := by
    funext b
    by_cases hb : b = 0
    · simp [hb]
    · have h := hJ (Units.mk0 b hb)
      rw [Units.val_mk0] at h
      rw [h]
      simp only [jacquetTallBox, dif_neg hb]
      rfl
  rw [hJ']
  exact setIntegral_jacquetTallBox_mul_charExt_mul_cpow_eq v ν Φ χ s c c' S hS hint hIg hWI

end S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq (solution)
