-- Prove2me | solution 1 for NumberField.TateGlobal.exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0864ef1e-76ab-5c26-9dce-9359e26025a7

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_NumberField_TateGlobal_exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div.NumberField.TateGlobal AutomorphicForm Set Complex"

noncomputable section

namespace NumberField
p2m_export "NumberField" "AdeleRing TateGlobal.ideleNorm TateGlobal.normPowChar TateGlobal.exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log TateGlobal.continuous_ideleNorm TateGlobal.setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos mem_normOneIdeles_iff normPowChar coe_normPowChar_apply exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log continuous_ideleNorm setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne exists_eq_normPowChar_of_forall_mem_normOneIdeles"
namespace PoleTerms
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]
  [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

theorem measurable_ideleNorm : Measurable (ideleNorm F) :=
  (NumberField.TateGlobal.continuous_ideleNorm F).measurable

theorem measurable_logNorm : Measurable (fun x : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F x)) :=
  Real.measurable_log.comp measurable_ideleNorm

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem preimage_logNorm_Icc (a b : ℝ) :
    (fun x : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F x)) ⁻¹' Icc a b =
      {x | ideleNorm F x ∈ Icc (Real.exp a) (Real.exp b)} := by
  ext x
  simp only [mem_preimage, mem_Icc, mem_setOf_eq]
  have hx := ideleNorm_pos x
  rw [Real.le_log_iff_exp_le hx, Real.log_le_iff_le_exp hx]

theorem measurableSet_le_one : MeasurableSet {x : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F x ≤ 1} :=
  measurableSet_le measurable_ideleNorm measurable_const

theorem measurableSet_one_le : MeasurableSet {x : (AdeleRing (𝓞 F) F)ˣ | 1 ≤ ideleNorm F x} :=
  measurableSet_le measurable_const measurable_ideleNorm

theorem map_logNorm_restrict_eq (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ) {C : ENNReal} (hC : C ≠ ⊤)
    (hband : ∀ a b : ℝ, 0 < a → a ≤ b →
      ν (Ω ∩ {x | ideleNorm F x ∈ Icc a b}) = C * ENNReal.ofReal (Real.log (b / a))) :
    Measure.map (fun x : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F x)) (ν.restrict Ω) =
      C • (volume : Measure ℝ) := by
  have key : ∀ a b : ℝ, a ≤ b →
      Measure.map (fun x : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F x)) (ν.restrict Ω) (Icc a b) =
        C * ENNReal.ofReal (b - a) := by
    intro a b hab
    rw [Measure.map_apply measurable_logNorm measurableSet_Icc,
      Measure.restrict_apply (measurable_logNorm measurableSet_Icc), preimage_logNorm_Icc, inter_comm,
      hband _ _ (Real.exp_pos a) (Real.exp_le_exp.mpr hab), ← Real.exp_sub, Real.log_exp]
  refine Measure.ext_of_Icc' _ _ (fun a b hab => ?_) (fun a b hab => ?_)
  · rw [key a b hab]
    exact ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top
  · rw [key a b hab, Measure.smul_apply, Real.volume_Icc, smul_eq_mul]

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem comp_exp_log_ideleNorm (g : ℝ → ℂ) :
    (fun x : (AdeleRing (𝓞 F) F)ˣ => g (ideleNorm F x)) =
      fun x => (g ∘ Real.exp) (Real.log (ideleNorm F x)) := by
  funext x
  simp only [Function.comp_apply, Real.exp_log (ideleNorm_pos x)]

theorem integral_comp_exp_eq_setIntegral_Ioi (g : ℝ → ℂ) :
    ∫ y : ℝ, g (Real.exp y) = ∫ r in Ioi (0 : ℝ), (r : ℂ)⁻¹ * g r := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := (univ : Set ℝ)) (f := Real.exp)
    (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun r : ℝ => (r : ℂ)⁻¹ * g r)
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [abs_of_pos (Real.exp_pos y), Complex.real_smul, ← mul_assoc,
    mul_inv_cancel₀ (ofReal_ne_zero.mpr (Real.exp_pos y).ne'), one_mul]

theorem integrable_comp_exp_iff (g : ℝ → ℂ) :
    Integrable (fun y : ℝ => g (Real.exp y)) ↔
      IntegrableOn (fun r : ℝ => (r : ℂ)⁻¹ * g r) (Ioi (0 : ℝ)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := (univ : Set ℝ)) (f := Real.exp)
    (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun r : ℝ => (r : ℂ)⁻¹ * g r)
  rw [image_univ, Real.range_exp, integrableOn_univ] at h
  rw [h]
  have hfun : (fun x : ℝ => |Real.exp x| • ((((Real.exp x : ℝ) : ℂ))⁻¹ * g (Real.exp x))) =
      fun y => g (Real.exp y) := by
    funext y
    rw [abs_of_pos (Real.exp_pos y), Complex.real_smul, ← mul_assoc,
      mul_inv_cancel₀ (ofReal_ne_zero.mpr (Real.exp_pos y).ne'), one_mul]
  rw [hfun]

theorem setIntegral_comp_ideleNorm_of_map_eq (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ) {C : ENNReal}
    (hmap : Measure.map (fun x : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F x)) (ν.restrict Ω) =
      C • (volume : Measure ℝ))
    (g : ℝ → ℂ) (hg : Measurable g) :
    ∫ x in Ω, g (ideleNorm F x) ∂ν = C.toReal * ∫ r in Ioi (0 : ℝ), (r : ℂ)⁻¹ * g r := by
  rw [comp_exp_log_ideleNorm g]
  have h2 : ∫ x in Ω, (g ∘ Real.exp) (Real.log (ideleNorm F x)) ∂ν =
      ∫ y, (g ∘ Real.exp) y ∂(Measure.map (fun x : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F x))
        (ν.restrict Ω)) := by
    rw [MeasureTheory.integral_map measurable_logNorm.aemeasurable]
    exact (hg.comp Real.measurable_exp).aestronglyMeasurable
  rw [h2, hmap, integral_smul_measure, Complex.real_smul]
  congr 1
  exact integral_comp_exp_eq_setIntegral_Ioi g

theorem integrableOn_comp_ideleNorm_iff_of_map_eq (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ) {C : ENNReal} (hC0 : C ≠ 0) (hC : C ≠ ⊤)
    (hmap : Measure.map (fun x : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F x)) (ν.restrict Ω) =
      C • (volume : Measure ℝ))
    (g : ℝ → ℂ) (hg : Measurable g) :
    IntegrableOn (fun x => g (ideleNorm F x)) Ω ν ↔
      IntegrableOn (fun r : ℝ => (r : ℂ)⁻¹ * g r) (Ioi (0 : ℝ)) := by
  rw [IntegrableOn, comp_exp_log_ideleNorm g]
  have h1 : Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ => (g ∘ Real.exp) (Real.log (ideleNorm F x)))
      (ν.restrict Ω) ↔
      Integrable (g ∘ Real.exp) (Measure.map (fun x : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F x))
        (ν.restrict Ω)) := by
    rw [integrable_map_measure _ measurable_logNorm.aemeasurable]
    · rfl
    · exact (hg.comp Real.measurable_exp).aestronglyMeasurable
  rw [h1, hmap, integrable_smul_measure hC0 hC]
  exact integrable_comp_exp_iff g

theorem measurable_ofReal_cpow_const (w : ℂ) : Measurable fun r : ℝ => (r : ℂ) ^ w :=
  Complex.measurable_ofReal.pow_const w

def gLow (w : ℂ) : ℝ → ℂ := (Iic (1 : ℝ)).indicator fun r : ℝ => (r : ℂ) ^ w

def gUp (w : ℂ) : ℝ → ℂ := (Ici (1 : ℝ)).indicator fun r : ℝ => (r : ℂ) ^ (-w)

theorem measurable_gLow (w : ℂ) : Measurable (gLow w) :=
  (measurable_ofReal_cpow_const w).indicator measurableSet_Iic

theorem measurable_gUp (w : ℂ) : Measurable (gUp w) :=
  (measurable_ofReal_cpow_const (-w)).indicator measurableSet_Ici

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem gLow_comp_ideleNorm (w : ℂ) :
    (fun x : (AdeleRing (𝓞 F) F)ˣ => gLow w (ideleNorm F x)) =
      {x | ideleNorm F x ≤ 1}.indicator fun x => ((ideleNorm F x : ℝ) : ℂ) ^ w := by
  funext x
  by_cases hx : ideleNorm F x ≤ 1
  · rw [gLow, indicator_of_mem (show ideleNorm F x ∈ Iic (1 : ℝ) from hx),
      indicator_of_mem (show x ∈ {x | ideleNorm F x ≤ 1} from hx)]
  · rw [gLow, indicator_of_notMem (show ideleNorm F x ∉ Iic (1 : ℝ) from hx),
      indicator_of_notMem (show x ∉ {x | ideleNorm F x ≤ 1} from hx)]

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem gUp_comp_ideleNorm (w : ℂ) :
    (fun x : (AdeleRing (𝓞 F) F)ˣ => gUp w (ideleNorm F x)) =
      {x | 1 ≤ ideleNorm F x}.indicator fun x => ((ideleNorm F x : ℝ) : ℂ) ^ (-w) := by
  funext x
  by_cases hx : 1 ≤ ideleNorm F x
  · rw [gUp, indicator_of_mem (show ideleNorm F x ∈ Ici (1 : ℝ) from hx),
      indicator_of_mem (show x ∈ {x | 1 ≤ ideleNorm F x} from hx)]
  · rw [gUp, indicator_of_notMem (show ideleNorm F x ∉ Ici (1 : ℝ) from hx),
      indicator_of_notMem (show x ∉ {x | 1 ≤ ideleNorm F x} from hx)]

theorem inv_mul_gLow (w : ℂ) :
    (fun r : ℝ => (r : ℂ)⁻¹ * gLow w r) = (Iic (1 : ℝ)).indicator fun r : ℝ => (r : ℂ)⁻¹ * (r : ℂ) ^ w := by
  funext r
  rw [gLow, indicator_mul_right]

theorem inv_mul_gUp (w : ℂ) :
    (fun r : ℝ => (r : ℂ)⁻¹ * gUp w r) = (Ici (1 : ℝ)).indicator fun r : ℝ => (r : ℂ)⁻¹ * (r : ℂ) ^ (-w) := by
  funext r
  rw [gUp, indicator_mul_right]

theorem inv_mul_cpow_of_pos {r : ℝ} (hr : 0 < r) (w : ℂ) : (r : ℂ)⁻¹ * (r : ℂ) ^ w = (r : ℂ) ^ (w - 1) := by
  rw [cpow_sub _ _ (ofReal_ne_zero.mpr hr.ne'), cpow_one, div_eq_inv_mul]

theorem Ioi_inter_Iic_eq : Ioi (0 : ℝ) ∩ Iic 1 = Ioc 0 1 := rfl

theorem Ioi_inter_Ici_eq : Ioi (0 : ℝ) ∩ Ici 1 = Ici 1 := by
  ext r
  exact ⟨fun h => h.2, fun h => ⟨Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos (Set.mem_Ici.mp h)), h⟩⟩

theorem setIntegral_inv_mul_gLow {w : ℂ} (hw : 0 < w.re) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ)⁻¹ * gLow w r = 1 / w := by
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_re] at hw; exact lt_irrefl _ hw
  have hw1 : -1 < (w - 1).re := by rw [sub_re, one_re]; linarith
  rw [inv_mul_gLow, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic_eq,
    setIntegral_congr_fun measurableSet_Ioc (fun r hr => inv_mul_cpow_of_pos hr.1 w),
    ← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl hw1), sub_add_cancel,
    ofReal_one, ofReal_zero, one_cpow, zero_cpow hw0, sub_zero]

theorem setIntegral_inv_mul_gUp {w : ℂ} (hw : 0 < w.re) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ)⁻¹ * gUp w r = 1 / w := by
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_re] at hw; exact lt_irrefl _ hw
  have hw1 : (-w - 1).re < -1 := by rw [sub_re, neg_re, one_re]; linarith
  rw [inv_mul_gUp, setIntegral_indicator measurableSet_Ici, Ioi_inter_Ici_eq,
    setIntegral_congr_fun measurableSet_Ici (fun r hr => inv_mul_cpow_of_pos (lt_of_lt_of_le one_pos (Set.mem_Ici.mp hr)) (-w)),
    integral_Ici_eq_integral_Ioi, integral_Ioi_cpow_of_lt hw1 one_pos, sub_add_cancel, ofReal_one, one_cpow]
  field_simp

theorem integrableOn_inv_mul_gLow {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun r : ℝ => (r : ℂ)⁻¹ * gLow w r) (Ioi (0 : ℝ)) := by
  have hw1 : -1 < (w - 1).re := by rw [sub_re, one_re]; linarith
  rw [inv_mul_gLow, IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iic, show Iic (1 : ℝ) ∩ Ioi 0 = Ioc 0 1 from by
      rw [inter_comm]; rfl]
  have h : IntegrableOn (fun r : ℝ => (r : ℂ) ^ (w - 1)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_cpow' hw1)
  exact h.congr_fun (fun r hr => (inv_mul_cpow_of_pos hr.1 w).symm) measurableSet_Ioc

theorem integrableOn_inv_mul_gUp {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun r : ℝ => (r : ℂ)⁻¹ * gUp w r) (Ioi (0 : ℝ)) := by
  have hw1 : (-w - 1).re < -1 := by rw [sub_re, neg_re, one_re]; linarith
  rw [inv_mul_gUp, IntegrableOn, integrable_indicator_iff measurableSet_Ici, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ici, show Ici (1 : ℝ) ∩ Ioi 0 = Ici 1 from by
      rw [inter_comm]; exact Ioi_inter_Ici_eq]
  have h : IntegrableOn (fun r : ℝ => (r : ℂ) ^ (-w - 1)) (Ici 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_Ioi_cpow_of_lt hw1 one_pos)
  exact h.congr_fun (fun r hr => (inv_mul_cpow_of_pos (lt_of_lt_of_le one_pos (Set.mem_Ici.mp hr)) (-w)).symm)
    measurableSet_Ici

section Omega

variable (ν : Measure (AdeleRing (𝓞 F) F)ˣ) (Ω : Set (AdeleRing (𝓞 F) F)ˣ) {C : ENNReal}

theorem setIntegral_le_one_cpow (hC0 : C ≠ 0) (hC : C ≠ ⊤)
    (hmap : Measure.map (fun x : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F x)) (ν.restrict Ω) =
      C • (volume : Measure ℝ)) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun x => ((ideleNorm F x : ℝ) : ℂ) ^ w) (Ω ∩ {x | ideleNorm F x ≤ 1}) ν ∧
    ∫ x in Ω ∩ {x | ideleNorm F x ≤ 1}, ((ideleNorm F x : ℝ) : ℂ) ^ w ∂ν = C.toReal / w := by
  constructor
  · have h := (integrableOn_comp_ideleNorm_iff_of_map_eq ν Ω hC0 hC hmap (gLow w) (measurable_gLow w)).mpr
      (integrableOn_inv_mul_gLow hw)
    rw [gLow_comp_ideleNorm, IntegrableOn, integrable_indicator_iff measurableSet_le_one, IntegrableOn,
      Measure.restrict_restrict measurableSet_le_one, inter_comm] at h
    exact h
  · rw [← setIntegral_indicator measurableSet_le_one, ← gLow_comp_ideleNorm,
      setIntegral_comp_ideleNorm_of_map_eq ν Ω hmap (gLow w) (measurable_gLow w),
      setIntegral_inv_mul_gLow hw, mul_one_div]

theorem setIntegral_one_le_cpow (hC0 : C ≠ 0) (hC : C ≠ ⊤)
    (hmap : Measure.map (fun x : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F x)) (ν.restrict Ω) =
      C • (volume : Measure ℝ)) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun x => ((ideleNorm F x : ℝ) : ℂ) ^ (-w)) (Ω ∩ {x | 1 ≤ ideleNorm F x}) ν ∧
    ∫ x in Ω ∩ {x | 1 ≤ ideleNorm F x}, ((ideleNorm F x : ℝ) : ℂ) ^ (-w) ∂ν = C.toReal / w := by
  constructor
  · have h := (integrableOn_comp_ideleNorm_iff_of_map_eq ν Ω hC0 hC hmap (gUp w) (measurable_gUp w)).mpr
      (integrableOn_inv_mul_gUp hw)
    rw [gUp_comp_ideleNorm, IntegrableOn, integrable_indicator_iff measurableSet_one_le, IntegrableOn,
      Measure.restrict_restrict measurableSet_one_le, inter_comm] at h
    exact h
  · rw [← setIntegral_indicator measurableSet_one_le, ← gUp_comp_ideleNorm,
      setIntegral_comp_ideleNorm_of_map_eq ν Ω hmap (gUp w) (measurable_gUp w),
      setIntegral_inv_mul_gUp hw, mul_one_div]

end Omega

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem continuous_ofReal_ideleNorm_cpow (w : ℂ) :
    Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ideleNorm F x : ℝ) : ℂ) ^ w :=
  (continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)).cpow continuous_const
    fun x => ofReal_mem_slitPlane.mpr (ideleNorm_pos x)

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in

theorem continuous_units_of_continuous_coe (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) : Continuous χ := by
  refine Units.continuous_iff.mpr ⟨hχc, ?_⟩
  have h : (fun x : (AdeleRing (𝓞 F) F)ˣ => (((χ x)⁻¹ : ℂˣ) : ℂ)) =
      fun x => ((χ x⁻¹ : ℂˣ) : ℂ) := by
    funext x; rw [map_inv]
  rw [h]
  exact hχc.comp continuous_inv

theorem integrableOn_char_mul {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ))
    {f : (AdeleRing (𝓞 F) F)ˣ → ℂ} (hf : Continuous f) {S : Set (AdeleRing (𝓞 F) F)ˣ}
    {ν : Measure (AdeleRing (𝓞 F) F)ˣ} (h : IntegrableOn f S ν) :
    IntegrableOn (fun x => ((χ x : ℂˣ) : ℂ) * f x) S ν := by
  refine Integrable.mono h (hχc.mul hf).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, hχu x, one_mul]

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem indicator_char_mul {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (S : Set (AdeleRing (𝓞 F) F)ˣ)
    (f : (AdeleRing (𝓞 F) F)ˣ → ℂ) :
    S.indicator (fun x => ((χ x : ℂˣ) : ℂ) * f x) = fun x => ((χ x : ℂˣ) : ℂ) * S.indicator f x := by
  funext x
  rw [indicator_mul_right]

theorem setIntegral_char_mul_eq_zero (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant]
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχF : IsIdeleClassChar (𝓞 F) F χ)
    (hχ : ∃ z : (AdeleRing (𝓞 F) F)ˣ, ideleNorm F z = 1 ∧ χ z ≠ 1) (w : ℂ) :
    ∫ x in Ω ∩ {x | ideleNorm F x ≤ 1}, ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ w ∂ν = 0 ∧
    ∫ x in Ω ∩ {x | 1 ≤ ideleNorm F x}, ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ (-w) ∂ν = 0 := by
  constructor
  · rw [← setIntegral_indicator measurableSet_le_one, indicator_char_mul, ← gLow_comp_ideleNorm]
    exact NumberField.TateGlobal.setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
      F ν Ω hΩ χ hχF hχ (gLow w)
  · rw [← setIntegral_indicator measurableSet_one_le, indicator_char_mul, ← gUp_comp_ideleNorm]
    exact NumberField.TateGlobal.setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
      F ν Ω hΩ χ hχF hχ (gUp w)

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem normPowChar_mul_cpow (τ : ℝ) (w : ℂ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((normPowChar F τ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ w =
      ((ideleNorm F x : ℝ) : ℂ) ^ (w + (τ : ℂ) * I) := by
  rw [coe_normPowChar_apply, ← cpow_add _ _ (ofReal_ne_zero.mpr (ideleNorm_pos x).ne')]
  congr 1
  ring

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem normPowChar_mul_cpow_neg (τ : ℝ) (w : ℂ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((normPowChar F τ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ (-w) =
      ((ideleNorm F x : ℝ) : ℂ) ^ (-(w - (τ : ℂ) * I)) := by
  rw [coe_normPowChar_apply, ← cpow_add _ _ (ofReal_ne_zero.mpr (ideleNorm_pos x).ne')]
  congr 1
  ring

theorem re_add_mul_I (w : ℂ) (τ : ℝ) : (w + (τ : ℂ) * I).re = w.re := by
  simp [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]

theorem re_sub_mul_I (w : ℂ) (τ : ℝ) : (w - (τ : ℂ) * I).re = w.re := by
  simp [sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]

theorem setIntegral_normPowChar_mul (ν : Measure (AdeleRing (𝓞 F) F)ˣ) (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    {C : ENNReal} (hC0 : C ≠ 0) (hC : C ≠ ⊤)
    (hmap : Measure.map (fun x : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F x)) (ν.restrict Ω) =
      C • (volume : Measure ℝ)) (τ : ℝ) {w : ℂ} (hw : 0 < w.re) :
    ∫ x in Ω ∩ {x | ideleNorm F x ≤ 1}, ((normPowChar F τ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ w ∂ν =
        C.toReal / (w + (τ : ℂ) * I) ∧
    ∫ x in Ω ∩ {x | 1 ≤ ideleNorm F x}, ((normPowChar F τ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ (-w) ∂ν =
        C.toReal / (w - (τ : ℂ) * I) := by
  constructor
  · simp_rw [normPowChar_mul_cpow]
    exact (setIntegral_le_one_cpow ν Ω hC0 hC hmap (by rw [re_add_mul_I]; exact hw)).2
  · simp_rw [normPowChar_mul_cpow_neg]
    exact (setIntegral_one_le_cpow ν Ω hC0 hC hmap (by rw [re_sub_mul_I]; exact hw)).2

end NumberField.TateGlobal.PoleTerms

end

open NumberField.TateGlobal.PoleTerms in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    ∃ C : ℝ, 0 < C ∧
      ∀ Ω : Set (AdeleRing (𝓞 F) F)ˣ,
        IsFundamentalDomain
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν →
        (∀ g : ℝ → ℂ, Measurable g →
          (IntegrableOn (fun x => g (NumberField.TateGlobal.ideleNorm F x)) Ω ν ↔
              IntegrableOn (fun r : ℝ => (r : ℂ)⁻¹ * g r) (Set.Ioi (0 : ℝ))) ∧
          ∫ x in Ω, g (NumberField.TateGlobal.ideleNorm F x) ∂ν =
            C * ∫ r in Set.Ioi (0 : ℝ), (r : ℂ)⁻¹ * g r) ∧
        (∀ w : ℂ, 0 < w.re →
          IntegrableOn (fun x => ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w)
              (Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1}) ν ∧
          ∫ x in Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1},
              ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w ∂ν = C / w ∧
          IntegrableOn (fun x => ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w))
              (Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x}) ν ∧
          ∫ x in Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x},
              ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w) ∂ν = C / w) ∧
        (∀ χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ →
          AutomorphicForm.IsUnitaryChar (𝓞 F) F χ →
          Continuous (fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) →
          ∀ w : ℂ, 0 < w.re →
            IntegrableOn (fun x => ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w)
                (Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1}) ν ∧
            IntegrableOn (fun x => ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w))
                (Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x}) ν ∧
            ((∃ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = 1 ∧ χ z ≠ 1) →
              ∫ x in Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1},
                  ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w ∂ν = 0 ∧
              ∫ x in Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x},
                  ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w) ∂ν = 0) ∧
            ((∀ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = 1 → χ z = 1) →
              ∃ τ : ℝ, χ = NumberField.TateGlobal.normPowChar F τ ∧
                ∫ x in Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1},
                    ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w ∂ν =
                  C / (w + (τ : ℂ) * Complex.I) ∧
                ∫ x in Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x},
                    ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w) ∂ν =
                  C / (w - (τ : ℂ) * Complex.I))) := by
  obtain ⟨C, hC0, hC, hband⟩ :=
    NumberField.TateGlobal.exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log F ν
  refine ⟨C.toReal, ENNReal.toReal_pos hC0 hC, fun Ω hΩ => ?_⟩
  have hmap := map_logNorm_restrict_eq ν Ω hC (hband Ω hΩ)
  refine ⟨fun g hg => ⟨integrableOn_comp_ideleNorm_iff_of_map_eq ν Ω hC0 hC hmap g hg,
    setIntegral_comp_ideleNorm_of_map_eq ν Ω hmap g hg⟩, fun w hw => ?_, fun χ hχF hχu hχc w hw => ?_⟩
  · exact ⟨(setIntegral_le_one_cpow ν Ω hC0 hC hmap hw).1, (setIntegral_le_one_cpow ν Ω hC0 hC hmap hw).2,
      (setIntegral_one_le_cpow ν Ω hC0 hC hmap hw).1, (setIntegral_one_le_cpow ν Ω hC0 hC hmap hw).2⟩
  · refine ⟨integrableOn_char_mul hχu hχc (continuous_ofReal_ideleNorm_cpow w)
        (setIntegral_le_one_cpow ν Ω hC0 hC hmap hw).1,
      integrableOn_char_mul hχu hχc (continuous_ofReal_ideleNorm_cpow (-w))
        (setIntegral_one_le_cpow ν Ω hC0 hC hmap hw).1,
      fun hχ => setIntegral_char_mul_eq_zero ν Ω hΩ χ hχF hχ w, fun hχ1 => ?_⟩
    obtain ⟨τ, rfl⟩ :=
      NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles F χ
        (continuous_units_of_continuous_coe χ hχc) hχu
        (fun x hx => hχ1 x ((mem_normOneIdeles_iff x).mp hx))
    exact ⟨τ, rfl, setIntegral_normPowChar_mul ν Ω hC0 hC hmap τ hw⟩

end S_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div (solution)
