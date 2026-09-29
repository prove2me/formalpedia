-- Prove2me | solution 1 for NumberField.AdicCompletion.lintegral_comp_torusAffineChart_mul_eq_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1f5a8975-f989-546b-870a-b0035979feb0

import Mathlib
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_AdicCompletion_lintegral_comp_torusAffineChart_mul_eq_lintegral
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Set Function
open scoped ENNReal NNReal Pointwise

namespace KcAdicProdJac

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

local notation "F" => v.adicCompletion K
local notation "P" => Fin 4 → v.adicCompletion K

theorem charZero_F : CharZero F :=
  charZero_of_injective_algebraMap (algebraMap K F).injective

theorem two_ne_zero_F : (2 : F) ≠ 0 := by
  haveI := charZero_F (K := K) (v := v); exact two_ne_zero

theorem four_ne_zero_F : (4 : F) ≠ 0 := by
  haveI := charZero_F (K := K) (v := v); norm_num

theorem measure_smul_set (μ : Measure F) [μ.IsAddHaarMeasure] (a : F) (ha : a ≠ 0) (s : Set F) :
    μ (a • s) = (‖a‖₊ : ℝ≥0∞) * μ s := by
  have h := MeasureTheory.distribHaarChar_mul μ (Units.mk0 a ha) s
  have hmod : distribHaarChar F (Units.mk0 a ha) = ‖a‖₊ := by
    rw [← LanglandsTunnell.TateLocal.modulus_of_ne_zero ha]
    exact LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v a
  rw [hmod] at h
  exact h.symm

theorem map_mul_left (μ : Measure F) [μ.IsAddHaarMeasure] (a : F) (ha : a ≠ 0) :
    Measure.map (fun x => a * x) μ = (‖a‖₊ : ℝ≥0∞)⁻¹ • μ := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul a) hs, Measure.smul_apply, smul_eq_mul]
  have : (fun x => a * x) ⁻¹' s = a⁻¹ • s := by
    ext x; rw [Set.mem_preimage, Set.mem_inv_smul_set_iff₀ ha, smul_eq_mul]
  rw [this, measure_smul_set μ a⁻¹ (inv_ne_zero ha), nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.2 ha)]

theorem lintegral_comp_affine (μ : Measure F) [μ.IsAddHaarMeasure] (H : F → ℝ≥0∞) {a : F}
    (ha : a ≠ 0) (c : F) :
    ∫⁻ y, H (a * y + c) ∂μ = (‖a‖₊ : ℝ≥0∞)⁻¹ * ∫⁻ y, H y ∂μ := by
  set e : F ≃ᵐ F := (MeasurableEquiv.mulLeft₀ a ha).trans (MeasurableEquiv.addRight c) with he
  have hfun : (e : F → F) = (fun y => y + c) ∘ fun y => a * y := by
    funext y; simp [he, MeasurableEquiv.coe_mulLeft₀, MeasurableEquiv.coe_addRight]
  have hmap : Measure.map e μ = (‖a‖₊ : ℝ≥0∞)⁻¹ • μ := by
    rw [hfun, ← Measure.map_map (measurable_add_const c) (measurable_const_mul a),
      map_mul_left μ a ha, Measure.map_smul, map_add_right_eq_self]
  have hfun' : ∀ y, a * y + c = e y := fun y => by rw [hfun]; rfl
  calc ∫⁻ y, H (a * y + c) ∂μ = ∫⁻ y, H (e y) ∂μ := by simp_rw [hfun']
    _ = ∫⁻ y, H y ∂(Measure.map e μ) := (lintegral_map_equiv H e).symm
    _ = (‖a‖₊ : ℝ≥0∞)⁻¹ * ∫⁻ y, H y ∂μ := by rw [hmap, lintegral_smul_measure, smul_eq_mul]

theorem lintegral_comp_affine_mul (μ : Measure F) [μ.IsAddHaarMeasure] (H : F → ℝ≥0∞) {a : F}
    (ha : a ≠ 0) (c : F) :
    ∫⁻ y, H (a * y + c) * (‖a‖₊ : ℝ≥0∞) ∂μ = ∫⁻ y, H y ∂μ := by
  rw [lintegral_mul_const' _ _ ENNReal.coe_ne_top, lintegral_comp_affine μ H ha c, mul_comm,
    ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 ha))
      ENNReal.coe_ne_top, one_mul]

variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

local notation "π" => Measure.pi fun _ : Fin 4 => μ

theorem step (i : Fin 4) {f g : P → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (N : Set P) (hNm : MeasurableSet N) (hN : π N = 0)
    (hcyl : ∀ (x : P) (y : F), update x i y ∈ N ↔ x ∈ N)
    (h : ∀ x : P, x ∉ N → ∫⁻ y, f (update x i y) ∂μ = ∫⁻ y, g (update x i y) ∂μ) :
    ∫⁻ x, f x ∂π = ∫⁻ x, g x ∂π := by
  have hae : ∀ k : P → ℝ≥0∞, ∫⁻ x, k x ∂π = ∫⁻ x, Nᶜ.indicator k x ∂π := by
    intro k
    refine lintegral_congr_ae ?_
    filter_upwards [(measure_eq_zero_iff_ae_notMem (μ := π)).1 hN] with x hx
    rw [indicator_of_mem (mem_compl hx)]
  rw [hae f, hae g]
  refine lintegral_eq_of_lmarginal_eq {i} (hf.indicator hNm.compl) (hg.indicator hNm.compl) ?_
  simp_rw [lmarginal_singleton]
  funext x
  by_cases hx : x ∈ N
  · have h1 : ∀ (k : P → ℝ≥0∞) (y : F), Nᶜ.indicator k (update x i y) = 0 := fun k y =>
      indicator_of_notMem (show update x i y ∉ Nᶜ from fun hc => hc ((hcyl x y).2 hx)) _
    simp_rw [h1]
  · have h1 : ∀ (k : P → ℝ≥0∞) (y : F), Nᶜ.indicator k (update x i y) = k (update x i y) :=
      fun k y => indicator_of_mem (show update x i y ∈ Nᶜ from fun hc => hx ((hcyl x y).1 hc)) _
    simp_rw [h1]
    exact h x hx

def Nz (j : Fin 4) : Set P := {x | x j = 0}

theorem measurableSet_Nz (j : Fin 4) : MeasurableSet (Nz j : Set P) := by
  have : (Nz j : Set P) = (fun f : P => f j) ⁻¹' ({0} : Set F) := rfl
  rw [this]
  exact measurable_pi_apply j (isClosed_singleton (x := (0 : F))).measurableSet

theorem measure_zero_singleton : μ ({0} : Set F) = 0 := by

  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  set c : F := FinitePlace.embedding v (x : K) with hc
  have hc0 : c ≠ 0 := by
    intro h; apply hx0
    have h' : ((x : K) : F) = 0 := h
    have h2 : (x : K) = 0 := (algebraMap K F).injective (by simp at h'; exact h')
    exact_mod_cast h2
  have hc1 : ‖c‖ < 1 := (FinitePlace.norm_lt_one_iff_mem (K := K) v x).2 hxv
  have h : μ ({0} : Set F) = (‖c‖₊ : ℝ≥0∞) * μ ({0} : Set F) := by
    conv_lhs => rw [show ({0} : Set F) = c • ({0} : Set F) by
      rw [Set.smul_set_singleton, smul_zero]]
    exact measure_smul_set μ c hc0 _
  have hfin : μ ({0} : Set F) < ⊤ := isCompact_singleton.measure_lt_top
  by_contra hne
  have hlt : (‖c‖₊ : ℝ≥0∞) < 1 := by exact_mod_cast hc1
  have : (‖c‖₊ : ℝ≥0∞) * μ {0} < 1 * μ {0} := ENNReal.mul_lt_mul_left hne hfin.ne hlt
  rw [one_mul, ← h] at this
  exact lt_irrefl _ this

theorem measure_Nz (j : Fin 4) : π (Nz j) = 0 := by
  have : (Nz j : Set P) = eval j ⁻¹' {0} := rfl
  rw [this]
  exact Measure.pi_eval_preimage_null _ (measure_zero_singleton μ)

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem update_mem_Nz_iff {i j : Fin 4} (hij : i ≠ j) (x : P) (y : F) :
    update x i y ∈ Nz j ↔ x ∈ Nz j := by
  simp only [Nz, mem_setOf_eq, update_of_ne hij.symm]

section Maps

variable (d : v.adicCompletion K)

noncomputable def BA (q : P) : P := update q 1 (q 2 * q 1)

noncomputable def BB (q : P) : P := update q 3 (q 3 * q 1 / q 2)

noncomputable def BC (q : P) : P := update q 0 (q 2 * q 0 + q 2 * q 3 / q 1)

noncomputable def BD (q : P) : P := update q 2 ((d * q 1 ^ 2 - q 3 ^ 2) / q 1 ^ 2 * q 2 + q 0 * q 3 / q 1)

variable (H : (Fin 4 → v.adicCompletion K) → ℝ≥0∞)

noncomputable def G₃ (q : P) : ℝ≥0∞ := H (BD d q) * (‖(d * q 1 ^ 2 - q 3 ^ 2) / q 1 ^ 2‖₊ : ℝ≥0∞)
noncomputable def G₂ (q : P) : ℝ≥0∞ := G₃ d H (BC q) * (‖q 2‖₊ : ℝ≥0∞)
noncomputable def G₁ (q : P) : ℝ≥0∞ := G₂ d H (BB q) * (‖q 1 / q 2‖₊ : ℝ≥0∞)
noncomputable def G₀ (q : P) : ℝ≥0∞ := G₁ d H (BA q) * (‖q 2‖₊ : ℝ≥0∞)

theorem measurable_update_of {i : Fin 4} {h : P → F} (hh : Measurable h) :
    Measurable fun x : P => update x i (h x) :=
  (measurable_update' (a := i)).comp (measurable_id.prodMk hh)

theorem measurable_BA : Measurable (BA : P → P) := measurable_update_of (by fun_prop)
theorem measurable_BB : Measurable (BB : P → P) := measurable_update_of (by fun_prop)
theorem measurable_BC : Measurable (BC : P → P) := measurable_update_of (by fun_prop)
theorem measurable_BD : Measurable (BD d : P → P) := measurable_update_of (by fun_prop)

theorem measurable_nnnorm_of {h : P → F} (hh : Measurable h) :
    Measurable fun x : P => (‖h x‖₊ : ℝ≥0∞) :=
  hh.nnnorm.coe_nnreal_ennreal

variable {H}

theorem measurable_G₃ (hH : Measurable H) : Measurable (G₃ d H) :=
  (hH.comp (measurable_BD d)).mul (measurable_nnnorm_of (by fun_prop))
theorem measurable_G₂ (hH : Measurable H) : Measurable (G₂ d H) :=
  ((measurable_G₃ d hH).comp measurable_BC).mul (measurable_nnnorm_of (by fun_prop))
theorem measurable_G₁ (hH : Measurable H) : Measurable (G₁ d H) :=
  ((measurable_G₂ d hH).comp measurable_BB).mul (measurable_nnnorm_of (by fun_prop))
theorem measurable_G₀ (hH : Measurable H) : Measurable (G₀ d H) :=
  ((measurable_G₁ d hH).comp measurable_BA).mul (measurable_nnnorm_of (by fun_prop))

end Maps

section Steps

variable (d : v.adicCompletion K) {H : (Fin 4 → v.adicCompletion K) → ℝ≥0∞}

theorem fin_facts : ((0 : Fin 4) ≠ 1 ∧ (0 : Fin 4) ≠ 2 ∧ (0 : Fin 4) ≠ 3 ∧ (1 : Fin 4) ≠ 2 ∧
    (1 : Fin 4) ≠ 3 ∧ (2 : Fin 4) ≠ 3) := by decide

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem coe_nnnorm_eq (z : F) : (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by
  rw [ofReal_norm]; rfl

theorem measure_Nz_union : π (Nz 1 ∪ Nz 2) = 0 :=
  measure_union_null (measure_Nz μ 1) (measure_Nz μ 2)

theorem stepA (hH : Measurable H) : ∫⁻ q, G₀ d H q ∂π = ∫⁻ q, G₁ d H q ∂π := by
  refine step μ 1 (measurable_G₀ d hH) (measurable_G₁ d hH) (Nz 2) (measurableSet_Nz 2)
    (measure_Nz μ 2) (update_mem_Nz_iff (by decide)) fun q hq => ?_
  have hq2 : q 2 ≠ 0 := hq
  have key : ∀ y : F, G₀ d H (update q 1 y) = G₁ d H (update q 1 (q 2 * y + 0)) * (‖q 2‖₊ : ℝ≥0∞) := by
    intro y
    have hA : BA (update q 1 y) = update q 1 (q 2 * y + 0) := by simp [BA]
    simp only [G₀, hA]
    simp
  simp_rw [key]
  exact lintegral_comp_affine_mul μ (fun w => G₁ d H (update q 1 w)) hq2 0

theorem stepB (hH : Measurable H) : ∫⁻ q, G₁ d H q ∂π = ∫⁻ q, G₂ d H q ∂π := by
  refine step μ 3 (measurable_G₁ d hH) (measurable_G₂ d hH) (Nz 1 ∪ Nz 2)
    ((measurableSet_Nz 1).union (measurableSet_Nz 2)) (measure_Nz_union μ)
    (fun q y => by simp [Nz]) fun q hq => ?_
  have hq1 : q 1 ≠ 0 := fun h => hq (Or.inl h)
  have hq2 : q 2 ≠ 0 := fun h => hq (Or.inr h)
  have ha : q 1 / q 2 ≠ 0 := div_ne_zero hq1 hq2
  have key : ∀ y : F, G₁ d H (update q 3 y) = G₂ d H (update q 3 (q 1 / q 2 * y + 0)) * (‖q 1 / q 2‖₊ : ℝ≥0∞) := by
    intro y
    have hB : BB (update q 3 y) = update q 3 (q 1 / q 2 * y + 0) := by
      simp only [BB, update_self, update_idem]
      congr 1
      simp
      ring
    simp only [G₁, hB]
    simp
  simp_rw [key]
  exact lintegral_comp_affine_mul μ (fun w => G₂ d H (update q 3 w)) ha 0

theorem stepC (hH : Measurable H) : ∫⁻ q, G₂ d H q ∂π = ∫⁻ q, G₃ d H q ∂π := by
  refine step μ 0 (measurable_G₂ d hH) (measurable_G₃ d hH) (Nz 2) (measurableSet_Nz 2)
    (measure_Nz μ 2) (update_mem_Nz_iff (by decide)) fun q hq => ?_
  have hq2 : q 2 ≠ 0 := hq
  have key : ∀ y : F, G₂ d H (update q 0 y) =
      G₃ d H (update q 0 (q 2 * y + q 2 * q 3 / q 1)) * (‖q 2‖₊ : ℝ≥0∞) := by
    intro y
    have hC : BC (update q 0 y) = update q 0 (q 2 * y + q 2 * q 3 / q 1) := by simp [BC]
    simp only [G₂, hC]
    simp
  simp_rw [key]
  exact lintegral_comp_affine_mul μ (fun w => G₃ d H (update q 0 w)) hq2 _

theorem stepD (hd : ¬ IsSquare d) (hH : Measurable H) : ∫⁻ q, G₃ d H q ∂π = ∫⁻ q, H q ∂π := by
  refine step μ 2 (measurable_G₃ d hH) hH (Nz 1) (measurableSet_Nz 1)
    (measure_Nz μ 1) (update_mem_Nz_iff (by decide)) fun q hq => ?_
  have hq1 : q 1 ≠ 0 := hq
  set s : F := (d * q 1 ^ 2 - q 3 ^ 2) / q 1 ^ 2 with hs
  have hs0 : s ≠ 0 := by
    rw [hs]
    refine div_ne_zero ?_ (pow_ne_zero 2 hq1)
    intro h
    apply hd
    refine ⟨q 3 / q 1, ?_⟩
    field_simp
    linear_combination h
  have key : ∀ y : F, G₃ d H (update q 2 y) = H (update q 2 (s * y + q 0 * q 3 / q 1)) * (‖s‖₊ : ℝ≥0∞) := by
    intro y
    have hD : BD d (update q 2 y) = update q 2 (s * y + q 0 * q 3 / q 1) := by
      simp [BD, hs]
    simp only [G₃, hD]
    simp [hs]
  simp_rw [key]
  exact lintegral_comp_affine_mul μ (fun w => H (update q 2 w)) hs0 _

theorem G₀_eq {q : P} (hq1 : q 1 ≠ 0) (hq2 : q 2 ≠ 0) :
    G₀ d H q = H ![q 3 + q 2 * q 0, q 2 * q 1, d * q 2 + q 3 * q 0, q 3 * q 1] *
      ENNReal.ofReal (‖q 1‖ * ‖q 3 ^ 2 - d * q 2 ^ 2‖) := by
  have hcomp : BD d (BC (BB (BA q))) = ![q 3 + q 2 * q 0, q 2 * q 1, d * q 2 + q 3 * q 0, q 3 * q 1] := by
    funext j
    fin_cases j <;> simp [BA, BB, BC, BD]
    · field_simp
      ring
    · field_simp
      ring
    · field_simp
  simp only [G₀, G₁, G₂, G₃, hcomp]
  simp only [BA, BB, BC, update_self, ne_eq, fin_facts, not_false_eq_true, update_of_ne, Ne.symm]
  rw [mul_assoc, mul_assoc, mul_assoc]
  congr 1
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← nnnorm_mul, ← nnnorm_mul, ← nnnorm_mul,
    ← norm_mul, ← coe_nnnorm_eq]
  have h1 : (d * (q 2 * q 1) ^ 2 - (q 3 * (q 2 * q 1) / q 2) ^ 2) / (q 2 * q 1) ^ 2 *
      (q 2 * (q 2 * q 1 / q 2 * q 2)) = -(q 1 * (q 3 ^ 2 - d * q 2 ^ 2)) := by
    field_simp
    ring
  rw [h1, nnnorm_neg]

theorem measure_compl_good : π ({q : P | q 1 ≠ 0 ∧ q 2 ≠ 0}ᶜ) = 0 := by
  have : ({q : P | q 1 ≠ 0 ∧ q 2 ≠ 0}ᶜ : Set P) = Nz 1 ∪ Nz 2 := by
    ext q; simp only [Nz, mem_compl_iff, mem_setOf_eq, mem_union, not_and_or, not_not]
  rw [this]; exact measure_Nz_union μ

theorem main (hd : ¬ IsSquare d) (hH : Measurable H) :
    ∫⁻ q, H ![q 3 + q 2 * q 0, q 2 * q 1, d * q 2 + q 3 * q 0, q 3 * q 1] *
        ENNReal.ofReal (‖q 1‖ * ‖q 3 ^ 2 - d * q 2 ^ 2‖) ∂π = ∫⁻ q, H q ∂π := by
  have h0 : ∫⁻ q, H ![q 3 + q 2 * q 0, q 2 * q 1, d * q 2 + q 3 * q 0, q 3 * q 1] *
      ENNReal.ofReal (‖q 1‖ * ‖q 3 ^ 2 - d * q 2 ^ 2‖) ∂π = ∫⁻ q, G₀ d H q ∂π := by
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ q ∂π, q ∈ {q : P | q 1 ≠ 0 ∧ q 2 ≠ 0} :=
      (measure_eq_zero_iff_ae_notMem.1 (measure_compl_good μ)).mono fun q hq => not_notMem.1 hq
    filter_upwards [hae] with q hq
    exact (G₀_eq d hq.1 hq.2).symm
  rw [h0, stepA μ d hH, stepB μ d hH, stepC μ d hH, stepD μ d hd hH]

end Steps

end KcAdicProdJac

open KcAdicProdJac in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (d : v.adicCompletion K) (hd : ¬ IsSquare d)
    (H : (Fin 4 → v.adicCompletion K) → ENNReal) (hH : Measurable H) :
    ∫⁻ q, H ![q 3 + q 2 * q 0, q 2 * q 1, d * q 2 + q 3 * q 0, q 3 * q 1] *
        ENNReal.ofReal (‖q 1‖ * ‖q 3 ^ 2 - d * q 2 ^ 2‖) ∂(Measure.pi fun _ : Fin 4 => μ) =
      ∫⁻ x, H x ∂(Measure.pi fun _ : Fin 4 => μ) :=
  main μ d hd hH

end S_NumberField_AdicCompletion_lintegral_comp_torusAffineChart_mul_eq_lintegral
end P2MW
export P2MW.S_NumberField_AdicCompletion_lintegral_comp_torusAffineChart_mul_eq_lintegral (solution)
