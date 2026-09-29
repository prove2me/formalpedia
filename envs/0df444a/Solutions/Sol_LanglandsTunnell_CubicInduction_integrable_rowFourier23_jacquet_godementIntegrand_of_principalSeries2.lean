-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integrable_rowFourier23_jacquet_godementIntegrand_of_principalSeries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/034822aa-deeb-5e9a-aee3-a3d79958736e

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isOpen_forall_mul_eq_of_mem_principalSeries2
import Theorems.Thm_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_norm_jacquetIntegral_principalSeries2_diagUnits2_mul_le_and_eq_zero_of_chamber
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_integrable_rowFourier23_jacquet_godementIntegrand_of_principalSeries2
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction NumberField.StandardAddChar

open scoped NNReal ENNReal Topology

noncomputable section

namespace F1GI

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mx" => (Matrix (Fin 2) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm p.asIdeal : ℝ≥0) ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm p.asIdeal : ℝ≥0) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure F)).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

theorem regular_selfDualHaarAt : (selfDualHaarAt ℚ p : Measure F).Regular := by
  show ((((Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure F)).Regular
  rw [ENNReal.smul_def]
  exact Measure.Regular.smul ENNReal.coe_ne_top

theorem norm_le_iff_valued_le (x y : F) : ‖x‖ ≤ ‖y‖ ↔ Valued.v x ≤ Valued.v y :=
  Valued.toNormedField.norm_le_iff

theorem norm_lt_iff_valued_lt (x y : F) : ‖x‖ < ‖y‖ ↔ Valued.v x < Valued.v y :=
  Valued.toNormedField.norm_lt_iff

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem eta_eq_one_of_norm_le_one {η : AddChar F ℂ} (hη : η = psiLocal ℚ p ∨ η = (psiLocal ℚ p)⁻¹)
    {x : F} (hx : ‖x‖ ≤ 1) : η x = 1 := by
  have key : ∀ y : F, ‖y‖ ≤ 1 → psiLocal ℚ p y = 1 := by
    intro y hy
    refine LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p y ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact Valued.toNormedField.norm_le_one_iff.mp hy
  rcases hη with rfl | rfl
  · exact key x hx
  · rw [AddChar.inv_apply]
    exact key (-x) (by rwa [norm_neg])

theorem exists_eta_ne_one {η : AddChar F ℂ} (hη : η = psiLocal ℚ p ∨ η = (psiLocal ℚ p)⁻¹) :
    ∃ s : F, η s ≠ 1 := by
  have hne : psiLocal ℚ p ≠ 1 := LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p
  have key : ∃ s : F, psiLocal ℚ p s ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  obtain ⟨s, hs⟩ := key
  rcases hη with rfl | rfl
  · exact ⟨s, hs⟩
  · exact ⟨-s, by rwa [AddChar.inv_apply, neg_neg]⟩

theorem godementArg_two (h : G₂) (i : Fin 2) :
    godementArg p h i 2 = ((h⁻¹ : G₂) : M2) 1 i := by
  rw [show (2 : Fin 3) = Fin.last 2 from rfl, godementArg_apply_last, coe_transposeInvN, Matrix.transpose_apply]

def ext23 (M : M2) (u : F × F) : Mx :=
  Matrix.of fun i k => Fin.lastCases (if i = 0 then u.1 else u.2) (fun k' : Fin 2 => M i k') k

theorem ext23_apply_castSucc (M : M2) (u : F × F) (i k : Fin 2) :
    ext23 p M u i (Fin.castSucc k) = M i k := by
  simp only [ext23, Matrix.of_apply, Fin.lastCases_castSucc]

theorem ext23_apply_last (M : M2) (u : F × F) (i : Fin 2) :
    ext23 p M u i (Fin.last 2) = if i = 0 then u.1 else u.2 := by
  simp only [ext23, Matrix.of_apply, Fin.lastCases_last]

theorem ext23_apply_zero (M : M2) (u : F × F) (i : Fin 2) : ext23 p M u i 0 = M i 0 :=
  ext23_apply_castSucc p M u i 0

theorem ext23_apply_one (M : M2) (u : F × F) (i : Fin 2) : ext23 p M u i 1 = M i 1 :=
  ext23_apply_castSucc p M u i 1

theorem ext23_apply_two (M : M2) (u : F × F) (i : Fin 2) : ext23 p M u i 2 = if i = 0 then u.1 else u.2 :=
  ext23_apply_last p M u i

theorem ext23_add (M M' : M2) (u u' : F × F) : ext23 p (M + M') (u + u') = ext23 p M u + ext23 p M' u' := by
  ext i k
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · simp only [Matrix.add_apply, ext23_apply_last, Prod.fst_add, Prod.snd_add]
    split_ifs <;> rfl
  · simp only [Matrix.add_apply, ext23_apply_castSucc]

theorem ext23_zero : ext23 p 0 0 = 0 := by
  ext i k
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · simp only [ext23_apply_last, Matrix.zero_apply, Prod.fst_zero, Prod.snd_zero]
    split_ifs <;> rfl
  · simp only [ext23_apply_castSucc, Matrix.zero_apply]

theorem setCol23_godementArg (h : G₂) (u : F × F) :
    setCol23 p (godementArg p h) 2 u = ext23 p (h : M2) u := by
  ext i k
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · rw [ext23_apply_last, setCol23_apply]
    simp
  · rw [ext23_apply_castSucc, setCol23_apply, godementArg_apply_castSucc]
    have : (Fin.castSucc k' : Fin 3) ≠ 2 := by
      intro hk
      have := congrArg Fin.val hk
      simp at this
      omega
    simp [this]

theorem continuous_ext23 : Continuous (fun P : M2 × (F × F) => ext23 p P.1 P.2) := by
  refine continuous_matrix fun i k => ?_
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · simp only [ext23_apply_last]
    split_ifs
    · exact continuous_fst.comp continuous_snd
    · exact continuous_snd.comp continuous_snd
  · simp only [ext23_apply_castSucc]
    exact (continuous_apply_apply i k').comp continuous_fst

def kLow (c : F) : G₂ where
  val := !![1, 0; c, 1]
  inv := !![1, 0; -c, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def kFlip (c : F) : G₂ where
  val := !![0, 1; 1, c]
  inv := !![-c, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mem_K0 (k : G₂) (h : ∀ i j, Valued.v ((k : M2) i j) ≤ 1)
    (h' : ∀ i j, Valued.v (((k⁻¹ : G₂) : M2) i j) ≤ 1) :
    k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  rw [AdelicDock.mem_localLevelOne_iff]
  have aux : ∀ (m : M2), (∀ i j, Valued.v (m i j) ≤ 1) → AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
    intro m hm
    refine ⟨fun i j => by rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]; exact hm i j, ?_, ?_⟩
    · rw [NumberField.AdelicLevel.idealBound_top]; exact hm 1 0
    · rw [NumberField.AdelicLevel.idealBound_top]
      refine (Valuation.map_sub _ _ _).trans (max_le (hm 1 1) ?_)
      rw [Valuation.map_one]
  exact ⟨aux _ h, aux _ h'⟩

theorem valued_le_one_of_mem_K0 {k : G₂} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) (i j : Fin 2) :
    Valued.v ((k : M2) i j) ≤ 1 := by
  rw [AdelicDock.mem_localLevelOne_iff] at hk
  have := hk.1.1 i j
  rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem valued_le_one_iff_norm_le_one (x : F) : Valued.v x ≤ 1 ↔ ‖x‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).symm

theorem kLow_mem (c : F) (hc : ‖c‖ ≤ 1) : kLow p c ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have hc' : Valued.v c ≤ 1 := (valued_le_one_iff_norm_le_one p c).mpr hc
  have hnc : Valued.v (-c) ≤ 1 := by rwa [Valuation.map_neg]
  refine mem_K0 p _ ?_ ?_ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [kLow, hc', Valuation.map_neg]

theorem kFlip_mem (c : F) (hc : ‖c‖ ≤ 1) : kFlip p c ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have hc' : Valued.v c ≤ 1 := (valued_le_one_iff_norm_le_one p c).mpr hc
  have hnc : Valued.v (-c) ≤ 1 := by rwa [Valuation.map_neg]
  refine mem_K0 p _ ?_ ?_ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [kFlip, hc', Valuation.map_neg]

theorem exists_iwasawa (g : G₂) :
    ∃ (x : F) (α β : Fˣ) (k : G₂), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ ∧
      g = upperUnipotent2 p x * diagUnits2 α β * k ∧
      ‖(β : F)‖ = max ‖(g : M2) 1 0‖ ‖(g : M2) 1 1‖ ∧
      ‖(α : F)‖ * ‖(β : F)‖ = ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ := by
  set g10 := (g : M2) 1 0 with h10
  set g11 := (g : M2) 1 1 with h11
  set g00 := (g : M2) 0 0 with h00
  set g01 := (g : M2) 0 1 with h01
  have hdet : ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = g00 * g11 - g01 * g10 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hdet0 : g00 * g11 - g01 * g10 ≠ 0 := hdet ▸ (Matrix.GeneralLinearGroup.det g).ne_zero
  by_cases hle : ‖g10‖ ≤ ‖g11‖
  · have h11ne : g11 ≠ 0 := by
      intro h; apply hdet0
      have : g10 = 0 := by rw [h, norm_zero] at hle; exact norm_le_zero_iff.mp hle
      rw [h, this]; ring
    set α : F := (g00 * g11 - g01 * g10) / g11 with hα
    have hα0 : α ≠ 0 := div_ne_zero hdet0 h11ne
    refine ⟨g01 / g11, Units.mk0 α hα0, Units.mk0 g11 h11ne, kLow p (g10 / g11),
      kLow_mem p _ (by rw [norm_div]; exact div_le_one_of_le₀ hle (norm_nonneg _)), ?_, ?_, ?_⟩
    · refine Units.ext ?_
      simp only [Units.val_mul, upperUnipotent2_coe, coe_diagUnits2, Units.val_mk0]
      show (g : M2) = _
      ext i j : 1
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, kLow, ← h00, ← h01, ← h10, ← h11, hα] <;>
        field_simp <;> ring
    · rw [Units.val_mk0, max_eq_right hle]
    · rw [Units.val_mk0, Units.val_mk0, hdet, hα, norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr h11ne)]
  · push Not at hle
    have h10ne : g10 ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) hle)
    set α : F := -(g00 * g11 - g01 * g10) / g10 with hα
    have hα0 : α ≠ 0 := div_ne_zero (neg_ne_zero.mpr hdet0) h10ne
    refine ⟨g00 / g10, Units.mk0 α hα0, Units.mk0 g10 h10ne, kFlip p (g11 / g10),
      kFlip_mem p _ (by rw [norm_div]; exact div_le_one_of_le₀ hle.le (norm_nonneg _)), ?_, ?_, ?_⟩
    · refine Units.ext ?_
      simp only [Units.val_mul, upperUnipotent2_coe, coe_diagUnits2, Units.val_mk0]
      show (g : M2) = _
      ext i j : 1
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, kFlip, ← h00, ← h01, ← h10, ← h11, hα] <;>
        field_simp <;> ring
    · rw [Units.val_mk0, max_eq_left hle.le]
    · rw [Units.val_mk0, Units.val_mk0, hdet, hα, norm_div, norm_neg, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr h10ne)]

theorem norm_inv_entry_le (g : G₂) (R : ℝ) (hR : ∀ i j, ‖(g : M2) i j‖ ≤ R) (i j : Fin 2) :
    ‖((g⁻¹ : G₂) : M2) i j‖ ≤ ‖((Matrix.GeneralLinearGroup.det g⁻¹ : Fˣ) : F)‖ * R := by
  have hdet : ((Matrix.GeneralLinearGroup.det g⁻¹ : Fˣ) : F) = ((g : M2).det)⁻¹ := by
    rw [map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply]
  have hinv : ((g⁻¹ : G₂) : M2) = ((g : M2).det)⁻¹ • (g : M2).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [hdet, hinv, Matrix.smul_apply, smul_eq_mul, norm_mul, Matrix.adjugate_fin_two]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  fin_cases i <;> fin_cases j <;> simp [hR]

def jac (ε : AddChar F ℂ) (φ : G₂ → ℂ) (k : G₂) : ℂ :=
  ∫ x : F, ε x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)

theorem isLocallyConstant_jac (ε : AddChar F ℂ) (φ : G₂ → ℂ) (U : Subgroup G₂) (hU : IsOpen (U : Set G₂))
    (hφU : ∀ k ∈ U, ∀ g : G₂, φ (g * k) = φ g) : IsLocallyConstant (jac p ε φ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro k₀
  have hcont : Continuous fun k : G₂ => k₀⁻¹ * k := continuous_const.mul continuous_id
  have hmem : ∀ᶠ k in 𝓝 k₀, k₀⁻¹ * k ∈ (U : Set G₂) :=
    hcont.continuousAt.eventually_mem (hU.mem_nhds (by rw [inv_mul_cancel]; exact U.one_mem))
  filter_upwards [hmem] with k hk
  unfold jac
  congr 1
  funext x
  rw [show antidiagonal2 p * upperUnipotent2 p x * k = antidiagonal2 p * upperUnipotent2 p x * k₀ * (k₀⁻¹ * k) by
    simp only [mul_assoc, mul_inv_cancel_left], hφU _ hk]

theorem jac_upperUnipotent2_mul (ε : AddChar F ℂ) (φ : G₂ → ℂ) (y : F) (g : G₂) :
    jac p ε φ (upperUnipotent2 p y * g) = ε (-y) * jac p ε φ g := by
  haveI := isAddHaarMeasure_selfDualHaarAt p
  unfold jac
  have hre : ∀ x : F, antidiagonal2 p * upperUnipotent2 p x * (upperUnipotent2 p y * g)
      = antidiagonal2 p * upperUnipotent2 p (x + y) * g := by
    intro x
    rw [← upperUnipotent2_mul, ← mul_assoc, ← mul_assoc]
  simp_rw [hre]
  have h := integral_add_right_eq_self (μ := selfDualHaarAt ℚ p)
    (fun x => ε (x - y) * φ (antidiagonal2 p * upperUnipotent2 p x * g)) y
  simp only [add_sub_cancel_right] at h
  rw [h, ← integral_const_mul]
  congr 1
  funext x
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

theorem antidiagonal2_mul_upperUnipotent2_neg (x : F) (g : G₂) :
    antidiagonal2 p * upperUnipotent2 p (-x) * g
      = diagonal2 p ![1, -1] * (antidiagonal2 p * upperUnipotent2 p x * (diagUnits2 (-1) 1 * g)) := by
  have key : antidiagonal2 p * upperUnipotent2 p (-x)
      = diagonal2 p ![1, -1] * (antidiagonal2 p * upperUnipotent2 p x) * diagUnits2 (-1) 1 := by
    refine Units.ext ?_
    simp only [Units.val_mul, upperUnipotent2_coe, coe_diagUnits2, antidiagonal2_coe, diagonal2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  rw [key]
  simp only [mul_assoc]

theorem diagUnits2_neg_one_mem_K0 : (diagUnits2 (-1) 1 : G₂) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have hinv : ((diagUnits2 (-1) 1 : G₂)⁻¹ : G₂) = diagUnits2 (-1) 1 := by
    rw [inv_eq_iff_mul_eq_one]
    refine Units.ext ?_
    simp only [Units.val_mul, coe_diagUnits2, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine mem_K0 p _ ?_ ?_
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg]
  · rw [hinv]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg]

theorem diagUnits2_neg_one_mul_diagUnits2 (a₁ a₂ : Fˣ) :
    (diagUnits2 (-1) 1 : G₂) * diagUnits2 a₁ a₂ = diagUnits2 a₁ a₂ * diagUnits2 (-1) 1 := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem jac_inv_eq (μ : Fin 2 → (Fˣ →* ℂˣ)) (φ : G₂ → ℂ) (hφ : φ ∈ principalSeries2 p μ) (g : G₂) :
    jac p (psiLocal ℚ p)⁻¹ φ g
      = torusChar2 p μ ![1, -1] * halfModulus2 p ![1, -1] * jac p (psiLocal ℚ p) φ (diagUnits2 (-1) 1 * g) := by
  haveI := isAddHaarMeasure_selfDualHaarAt p
  haveI := regular_selfDualHaarAt p
  obtain ⟨-, -, ht⟩ := mem_principalSeries2_iff.mp hφ
  unfold jac
  have h1 : ∫ x : F, (psiLocal ℚ p)⁻¹ x * φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)
      = ∫ x : F, (fun y : F => psiLocal ℚ p y * φ (antidiagonal2 p * upperUnipotent2 p (-y) * g)) (-x)
          ∂(selfDualHaarAt ℚ p) := by
    congr 1
    funext x
    simp only [AddChar.inv_apply, neg_neg]
  have h2 : ∫ x : F, (fun y : F => psiLocal ℚ p y * φ (antidiagonal2 p * upperUnipotent2 p (-y) * g)) (-x)
          ∂(selfDualHaarAt ℚ p)
      = ∫ y : F, psiLocal ℚ p y * φ (antidiagonal2 p * upperUnipotent2 p (-y) * g) ∂(selfDualHaarAt ℚ p) :=
    integral_neg_eq_self (fun y : F => psiLocal ℚ p y * φ (antidiagonal2 p * upperUnipotent2 p (-y) * g))
      (selfDualHaarAt ℚ p)
  rw [h1, h2, ← integral_const_mul]
  congr 1
  funext y
  rw [antidiagonal2_mul_upperUnipotent2_neg, ht]
  ring

theorem exists_jac_diagUnits2_eq_zero
    (μ : Fin 2 → (Fˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i)) (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : Fˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : F)‖ ^ (σ i)) (h01 : σ 1 < σ 0)
    (φ : G₂ → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    {ε : AddChar F ℂ} (hε : ε = psiLocal ℚ p ∨ ε = (psiLocal ℚ p)⁻¹) :
    ∃ M₁ : ℤ, ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ a₁ a₂ : Fˣ,
      WithZero.exp M₁ < Valued.v ((a₁ * a₂⁻¹ : Fˣ) : F) → jac p ε φ (diagUnits2 a₁ a₂ * k) = 0 := by
  obtain ⟨C, M₁, -, h725⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_norm_jacquetIntegral_principalSeries2_diagUnits2_mul_le_and_eq_zero_of_chamber
      p μ hμ σ hσ h01 φ hφ
  refine ⟨M₁, fun k hk a₁ a₂ hlt => ?_⟩
  rcases hε with rfl | rfl
  · exact (h725 k hk a₁ a₂).2 hlt
  · have hk' : diagUnits2 (-1) 1 * k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ :=
      Subgroup.mul_mem _ (diagUnits2_neg_one_mem_K0 p) hk
    have hz := (h725 _ hk' a₁ a₂).2 hlt
    rw [jac_inv_eq p μ φ hφ]
    have hre : (diagUnits2 (-1) 1 : G₂) * (diagUnits2 a₁ a₂ * k) = diagUnits2 a₁ a₂ * (diagUnits2 (-1) 1 * k) := by
      rw [← mul_assoc, diagUnits2_neg_one_mul_diagUnits2, mul_assoc]
    rw [hre]
    unfold jac
    rw [hz, mul_zero]

section Slice

def slice (φ₀ : Mx → ℂ) (g : GL (Fin 3) F) (h : G₂) (u : F × F) : ℂ := φ₀ (ext23 p (h : M2) u * (g : Matrix (Fin 3) (Fin 3) F))

def Fη (φ₀ : Mx → ℂ) (g : GL (Fin 3) F) (η : AddChar F ℂ) (h : G₂) : ℂ :=
  ∫ u : F × F, slice p φ₀ g h u * η (u.1 * ((h⁻¹ : G₂) : M2) 1 0 + u.2 * ((h⁻¹ : G₂) : M2) 1 1)
    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))

theorem exists_stab (φ₀ : Mx → ℂ) (hφ₀ : IsLocallyConstant φ₀ ∧ HasCompactSupport φ₀) :
    ∃ W : Set Mx, W ∈ 𝓝 (0 : Mx) ∧ ∀ Y : Mx, ∀ w ∈ W, φ₀ (Y + w) = φ₀ Y := by
  obtain ⟨W, hWo, hW1, hW⟩ := IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
      (G := Multiplicative Mx) (fun X => φ₀ (Multiplicative.toAdd X)) hφ₀.1 hφ₀.2
  exact ⟨{b : Mx | Multiplicative.ofAdd b ∈ W}, (continuous_ofAdd.isOpen_preimage W hWo).mem_nhds hW1,
    fun Y w hw => (hW (Multiplicative.ofAdd Y) (Multiplicative.ofAdd w) hw).1⟩

theorem eventually_slice_eq (φ₀ : Mx → ℂ) (g : GL (Fin 3) F) (hφ₀ : IsLocallyConstant φ₀ ∧ HasCompactSupport φ₀) (h₀ : G₂) :
    ∀ᶠ h in 𝓝 h₀, ∀ u, slice p φ₀ g h u = slice p φ₀ g h₀ u := by
  obtain ⟨W, hW, hstab⟩ := exists_stab p φ₀ hφ₀
  have hT : Continuous fun h : G₂ => ext23 p ((h : M2) - (h₀ : M2)) 0 * (g : Matrix (Fin 3) (Fin 3) F) :=
    ((continuous_ext23 p).comp ((Units.continuous_val.sub continuous_const).prodMk continuous_const)).matrix_mul
      continuous_const
  have hT0 : ext23 p ((h₀ : M2) - (h₀ : M2)) 0 * (g : Matrix (Fin 3) (Fin 3) F) = 0 := by
    rw [sub_self, ext23_zero, Matrix.zero_mul]
  have hev : ∀ᶠ h : G₂ in 𝓝 h₀, ext23 p ((h : M2) - (h₀ : M2)) 0 * (g : Matrix (Fin 3) (Fin 3) F) ∈ W :=
    hT.continuousAt.eventually_mem (by rwa [hT0])
  filter_upwards [hev] with h hh
  intro u
  unfold slice
  have : ext23 p (h : M2) u * (g : Matrix (Fin 3) (Fin 3) F)
      = ext23 p (h₀ : M2) u * (g : Matrix (Fin 3) (Fin 3) F)
        + ext23 p ((h : M2) - (h₀ : M2)) 0 * (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Matrix.add_mul, ← ext23_add, add_sub_cancel, add_zero]
  rw [this, hstab _ _ hh]

theorem exists_nhds_slice_add (φ₀ : Mx → ℂ) (g : GL (Fin 3) F) (hφ₀ : IsLocallyConstant φ₀ ∧ HasCompactSupport φ₀) :
    ∃ V ∈ 𝓝 (0 : F × F), ∀ (h : G₂) (u : F × F), ∀ t ∈ V, slice p φ₀ g h (u + t) = slice p φ₀ g h u := by
  obtain ⟨W, hW, hstab⟩ := exists_stab p φ₀ hφ₀
  have hS : Continuous fun t : F × F => ext23 p 0 t * (g : Matrix (Fin 3) (Fin 3) F) :=
    ((continuous_ext23 p).comp (continuous_const.prodMk continuous_id)).matrix_mul continuous_const
  have hS0 : ext23 p (0 : M2) (0 : F × F) * (g : Matrix (Fin 3) (Fin 3) F) = 0 := by rw [ext23_zero, Matrix.zero_mul]
  refine ⟨_, hS.continuousAt.preimage_mem_nhds (by rwa [hS0]), fun h u t ht => ?_⟩
  unfold slice
  have : ext23 p (h : M2) (u + t) * (g : Matrix (Fin 3) (Fin 3) F)
      = ext23 p (h : M2) u * (g : Matrix (Fin 3) (Fin 3) F) + ext23 p 0 t * (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Matrix.add_mul, ← ext23_add, add_zero]
  rw [this, hstab _ _ ht]

theorem exists_bound_of_slice_ne_zero (φ₀ : Mx → ℂ) (g : GL (Fin 3) F) (hφ₀ : IsLocallyConstant φ₀ ∧ HasCompactSupport φ₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ (h : G₂) (u : F × F), slice p φ₀ g h u ≠ 0 →
      (∀ i j, ‖(h : M2) i j‖ ≤ R) ∧ ‖u.1‖ ≤ R ∧ ‖u.2‖ ≤ R := by
  set S' : Set Mx := (fun Y : Mx => Y * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) '' tsupport φ₀ with hS'
  have hS'c : IsCompact S' := hφ₀.2.image (continuous_id.matrix_mul continuous_const)
  have hbd : ∀ i k, ∃ C : ℝ, ∀ Y ∈ S', ‖Y i k‖ ≤ C := fun i k =>
    hS'c.exists_bound_of_continuousOn (f := fun Y : Mx => Y i k) (continuous_apply_apply i k).continuousOn
  choose C hC using hbd
  refine ⟨1 + ∑ i, ∑ k, |C i k|, by positivity, fun h u hne => ?_⟩
  have hmem : ext23 p (h : M2) u ∈ S' := by
    refine ⟨ext23 p (h : M2) u * (g : Matrix (Fin 3) (Fin 3) F), subset_tsupport _ hne, ?_⟩
    simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hle : ∀ i k, ‖ext23 p (h : M2) u i k‖ ≤ 1 + ∑ i, ∑ k, |C i k| := by
    intro i k
    refine (hC i k _ hmem).trans ((le_abs_self _).trans ?_)
    have h1 : |C i k| ≤ ∑ k', |C i k'| :=
      Finset.single_le_sum (f := fun k' => |C i k'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h2 : ∑ k', |C i k'| ≤ ∑ i', ∑ k', |C i' k'| :=
      Finset.single_le_sum (f := fun i' => ∑ k', |C i' k'|) (fun _ _ => by positivity) (Finset.mem_univ i)
    linarith
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · have := hle i (Fin.castSucc j)
    rwa [ext23_apply_castSucc] at this
  · have := hle 0 2
    rwa [ext23_apply_two] at this
  · have := hle 1 2
    rwa [ext23_apply_two] at this

theorem Fη_eq_zero_of_forall (φ₀ : Mx → ℂ) (g : GL (Fin 3) F) (η : AddChar F ℂ) (h : G₂) (h0 : ∀ u, slice p φ₀ g h u = 0) : Fη p φ₀ g η h = 0 := by
  unfold Fη
  simp [h0]

theorem isLocallyConstant_Fη (φ₀ : Mx → ℂ) (g : GL (Fin 3) F) (hφ₀ : IsLocallyConstant φ₀ ∧ HasCompactSupport φ₀)
    {η : AddChar F ℂ} (hη : η = psiLocal ℚ p ∨ η = (psiLocal ℚ p)⁻¹) :
    IsLocallyConstant (Fη p φ₀ g η) := by
  obtain ⟨R, hR, hbd⟩ := exists_bound_of_slice_ne_zero p φ₀ g hφ₀
  rw [IsLocallyConstant.iff_eventually_eq]
  intro h₀
  have hcont : ∀ i : Fin 2, Continuous fun h : G₂ => ((h⁻¹ : G₂) : M2) 1 i := fun i =>
    Units.continuous_coe_inv.matrix_elem 1 i
  have hnear : ∀ i : Fin 2, ∀ᶠ h in 𝓝 h₀, ‖((h⁻¹ : G₂) : M2) 1 i - ((h₀⁻¹ : G₂) : M2) 1 i‖ < (2 * R)⁻¹ := by
    intro i
    have := Metric.tendsto_nhds.mp ((hcont i).tendsto h₀) (2 * R)⁻¹ (by positivity)
    filter_upwards [this] with h hh
    rwa [dist_eq_norm] at hh
  filter_upwards [eventually_slice_eq p φ₀ g hφ₀ h₀, hnear 0, hnear 1] with h hsl hr0 hr1
  unfold Fη
  congr 1
  funext u
  by_cases hu : slice p φ₀ g h₀ u = 0
  · rw [hsl u, hu, zero_mul, zero_mul]
  obtain ⟨-, hu1, hu2⟩ := hbd h₀ u hu
  rw [hsl u]
  congr 1
  set a := ((h⁻¹ : G₂) : M2) 1 0
  set b := ((h⁻¹ : G₂) : M2) 1 1
  set a₀ := ((h₀⁻¹ : G₂) : M2) 1 0
  set b₀ := ((h₀⁻¹ : G₂) : M2) 1 1
  have hsplit : u.1 * a + u.2 * b = (u.1 * a₀ + u.2 * b₀) + (u.1 * (a - a₀) + u.2 * (b - b₀)) := by ring
  rw [hsplit, AddChar.map_add_eq_mul, eta_eq_one_of_norm_le_one p hη (x := u.1 * (a - a₀) + u.2 * (b - b₀)), mul_one]
  calc ‖u.1 * (a - a₀) + u.2 * (b - b₀)‖ ≤ ‖u.1 * (a - a₀)‖ + ‖u.2 * (b - b₀)‖ := norm_add_le _ _
    _ = ‖u.1‖ * ‖a - a₀‖ + ‖u.2‖ * ‖b - b₀‖ := by rw [norm_mul, norm_mul]
    _ ≤ R * (2 * R)⁻¹ + R * (2 * R)⁻¹ := by
        gcongr
    _ = 1 := by field_simp; ring

theorem exists_bound_freq (φ₀ : Mx → ℂ) (g : GL (Fin 3) F) (hφ₀ : IsLocallyConstant φ₀ ∧ HasCompactSupport φ₀)
    {η : AddChar F ℂ} (hη : η = psiLocal ℚ p ∨ η = (psiLocal ℚ p)⁻¹) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ h : G₂, Fη p φ₀ g η h ≠ 0 → ∀ i : Fin 2, ‖((h⁻¹ : G₂) : M2) 1 i‖ ≤ B := by
  haveI := isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨V, hV, hadd⟩ := exists_nhds_slice_add p φ₀ g hφ₀
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨s₀, hs₀⟩ := exists_eta_ne_one p hη
  refine ⟨‖s₀‖ / δ, by positivity, fun h hne => ?_⟩

  have key : ∀ t ∈ V, η (t.1 * ((h⁻¹ : G₂) : M2) 1 0 + t.2 * ((h⁻¹ : G₂) : M2) 1 1) = 1 := by
    intro t ht
    have hid : Fη p φ₀ g η h = η (t.1 * ((h⁻¹ : G₂) : M2) 1 0 + t.2 * ((h⁻¹ : G₂) : M2) 1 1) * Fη p φ₀ g η h := by
      unfold Fη
      rw [← integral_const_mul]
      rw [← integral_add_right_eq_self
        (μ := (selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) _ t]
      congr 1
      funext u
      rw [hadd h u t ht, Prod.fst_add, Prod.snd_add,
        show (u.1 + t.1) * ((h⁻¹ : G₂) : M2) 1 0 + (u.2 + t.2) * ((h⁻¹ : G₂) : M2) 1 1
          = (u.1 * ((h⁻¹ : G₂) : M2) 1 0 + u.2 * ((h⁻¹ : G₂) : M2) 1 1)
            + (t.1 * ((h⁻¹ : G₂) : M2) 1 0 + t.2 * ((h⁻¹ : G₂) : M2) 1 1) by ring,
        AddChar.map_add_eq_mul]
      ring
    have := mul_left_eq_self₀.mp hid.symm
    exact this.resolve_right hne

  have gen : ∀ ξ : F, (∀ c : F, ‖c‖ < δ → η (c * ξ) = 1) → ‖ξ‖ ≤ ‖s₀‖ / δ := by
    intro ξ hξ1
    by_contra hlt
    push Not at hlt
    have hξpos : 0 < ‖ξ‖ := lt_of_le_of_lt (by positivity) hlt
    have hξ : ξ ≠ 0 := norm_pos_iff.mp hξpos
    have hc : ‖s₀ / ξ‖ < δ := by
      rw [norm_div, div_lt_iff₀ hξpos]
      rw [div_lt_iff₀ hδ] at hlt
      linarith
    have := hξ1 (s₀ / ξ) hc
    rw [div_mul_cancel₀ _ hξ] at this
    exact hs₀ this
  have hV0 : ∀ c : F, ‖c‖ < δ → ((c, 0) : F × F) ∈ V := fun c hc =>
    hball (by rw [mem_ball_zero_iff, Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]; exact hc)
  have hV1 : ∀ c : F, ‖c‖ < δ → ((0, c) : F × F) ∈ V := fun c hc =>
    hball (by rw [mem_ball_zero_iff, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]; exact hc)
  intro i
  fin_cases i
  · refine gen _ fun c hc => ?_
    have := key (c, 0) (hV0 c hc)
    first
      | simpa only [zero_mul, add_zero] using this
      | (have h' := this; simp only [zero_mul, add_zero] at h' ⊢; exact h')
      | (have h' := this; simp only [zero_mul, add_zero] at h'; exact h')
      | exact this
      | (simpa only [zero_mul, add_zero, Function.comp_def] using this)
  · refine gen _ fun c hc => ?_
    have := key (0, c) (hV1 c hc)
    first
      | simpa only [zero_mul, zero_add] using this
      | (have h' := this; simp only [zero_mul, zero_add] at h' ⊢; exact h')
      | (have h' := this; simp only [zero_mul, zero_add] at h'; exact h')
      | exact this
      | (simpa only [zero_mul, zero_add, Function.comp_def] using this)

end Slice

theorem exists_norm_le_of_jac_ne_zero
    (μ : Fin 2 → (Fˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i)) (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : Fˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : F)‖ ^ (σ i)) (h01 : σ 1 < σ 0)
    (φ : G₂ → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    {ε : AddChar F ℂ} (hε : ε = psiLocal ℚ p ∨ ε = (psiLocal ℚ p)⁻¹) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ α β : Fˣ,
      jac p ε φ (diagUnits2 α β * k) ≠ 0 → ‖(α : F)‖ ≤ C₁ * ‖(β : F)‖ := by
  obtain ⟨M₁, hM₁⟩ := exists_jac_diagUnits2_eq_zero p μ hμ σ hσ h01 φ hφ hε
  obtain ⟨t₁, -, ht₁⟩ := exists_valued_eq_exp p M₁
  refine ⟨‖t₁‖, norm_nonneg _, fun k hk α β hne => ?_⟩
  have hle : Valued.v ((α * β⁻¹ : Fˣ) : F) ≤ Valued.v t₁ := by
    rw [ht₁]
    exact not_lt.mp fun hlt => hne (hM₁ k hk α β hlt)
  have := (norm_le_iff_valued_le p _ _).mpr hle
  rwa [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv,
    mul_inv_le_iff₀ (norm_pos_iff.mpr β.ne_zero)] at this

theorem exists_compact_support
    (μ : Fin 2 → (Fˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i)) (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : Fˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : F)‖ ^ (σ i)) (h01 : σ 1 < σ 0)
    (φ : G₂ → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (φ₀ : Mx → ℂ) (hφ₀ : IsLocallyConstant φ₀ ∧ HasCompactSupport φ₀) (g : GL (Fin 3) F)
    {ε : AddChar F ℂ} (hε : ε = psiLocal ℚ p ∨ ε = (psiLocal ℚ p)⁻¹)
    {η : AddChar F ℂ} (hη : η = psiLocal ℚ p ∨ η = (psiLocal ℚ p)⁻¹) (L : G₂ → ℂ) :
    ∃ S : Set G₂, IsCompact S ∧ ∀ h, h ∉ S → jac p ε φ h⁻¹ * Fη p φ₀ g η h * L h = 0 := by
  obtain ⟨C₁, hC₁, hvan⟩ := exists_norm_le_of_jac_ne_zero p μ hμ σ hσ h01 φ hφ hε
  obtain ⟨R, hR, hbd⟩ := exists_bound_of_slice_ne_zero p φ₀ g hφ₀
  obtain ⟨B, hB, hfreq⟩ := exists_bound_freq p φ₀ g hφ₀ hη
  haveI := properSpace_adicCompletion_rat p
  refine ⟨AutomorphicForm.integralUnitsSet (Metric.closedBall (0 : F) (max R (C₁ * B * B * R))),
    AutomorphicForm.isCompact_integralUnitsSet (isCompact_closedBall 0 _), fun h hnot => ?_⟩
  by_contra hne
  apply hnot
  have hK0 : jac p ε φ h⁻¹ ≠ 0 := by
    intro h0; apply hne; rw [h0, zero_mul, zero_mul]
  have hF0 : Fη p φ₀ g η h ≠ 0 := by
    intro h0; apply hne; rw [h0, mul_zero, zero_mul]

  have hu : ∃ u, slice p φ₀ g h u ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hF0 (Fη_eq_zero_of_forall p φ₀ g η h hall)
  obtain ⟨u, hu⟩ := hu
  obtain ⟨hh, -, -⟩ := hbd h u hu

  have hfr := hfreq h hF0

  obtain ⟨x, α, β, k, hk, hdec, hβ, hαβ⟩ := exists_iwasawa p h⁻¹
  have hβB : ‖(β : F)‖ ≤ B := by
    rw [hβ]
    exact max_le (hfr 0) (hfr 1)
  have hjk : jac p ε φ (diagUnits2 α β * k) ≠ 0 := by
    intro h0
    apply hK0
    rw [hdec, mul_assoc, jac_upperUnipotent2_mul, h0, mul_zero]
  have hαB : ‖(α : F)‖ ≤ C₁ * B := (hvan k hk α β hjk).trans (by gcongr)
  have hdet : ‖((Matrix.GeneralLinearGroup.det h⁻¹ : Fˣ) : F)‖ ≤ C₁ * B * B := by
    rw [← hαβ]
    exact mul_le_mul hαB hβB (norm_nonneg _) (by positivity)
  have hinv : ∀ i j, ‖((h⁻¹ : G₂) : M2) i j‖ ≤ C₁ * B * B * R := fun i j =>
    (norm_inv_entry_le p h R hh i j).trans (by gcongr)
  rw [AutomorphicForm.mem_integralUnitsSet]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (hh i j).trans (le_max_left _ _)
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (hinv i j).trans (le_max_right _ _)

theorem rowFourier23_jacquetDatum_eq (φ₀ : Mx → ℂ) (g : GL (Fin 3) F) (ε η : AddChar F ℂ) (φ : G₂ → ℂ) (h : G₂) :
    rowFourier23 p η
        (fun X => (fun (X : Mx) (k : G₂) =>
            φ₀ X * ∫ x : F, ε x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))
          (X * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h⁻¹)
        (godementArg p h)
      = jac p ε φ h⁻¹ * Fη p φ₀ g η h := by
  rw [rowFourier23_eq, colFourier23_apply]
  unfold Fη slice jac
  rw [← integral_const_mul]
  congr 1
  funext u
  simp only [setCol23_godementArg, godementArg_two]
  ring

theorem isLocallyConstant_charFactor (lam0 : Fˣ →* ℂˣ) (hlam0 : IsLocallyConstant lam0) :
    IsLocallyConstant fun h : G₂ =>
      ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
        * ((modulus ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
  have hdetc : Continuous fun h : G₂ => ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) := by
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.continuous_val.matrix_det
  have hdetU : Continuous fun h : G₂ => (Matrix.GeneralLinearGroup.det h : Fˣ) := by
    refine Units.continuous_iff.mpr ⟨hdetc, ?_⟩
    have : (fun h : G₂ => (((Matrix.GeneralLinearGroup.det h)⁻¹ : Fˣ) : F)) = fun h => (((h⁻¹ : G₂) : M2)).det := by
      funext h
      rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact Units.continuous_coe_inv.matrix_det
  have hL1 : IsLocallyConstant fun h : G₂ => ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) :=
    (hlam0.comp_continuous hdetU).comp Units.val
  have hL2 : IsLocallyConstant fun h : G₂ => ‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro h₀
    exact (hdetc.tendsto h₀).eventually (eventually_norm_eq p (Matrix.GeneralLinearGroup.det h₀).ne_zero)
  have hL3 : IsLocallyConstant fun h : G₂ =>
      (((‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖ : ℝ) : ℂ)) ^ (1 / 2 : ℂ) :=
    hL2.comp (fun r : ℝ => ((r : ℝ) : ℂ) ^ (1 / 2 : ℂ))
  have heq : (fun h : G₂ =>
      ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
        * ((modulus ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ))
      = fun h => ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
        * (((‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖ : ℝ) : ℂ)) ^ (1 / 2 : ℂ) := by
    funext h
    rw [coe_modulus_eq_norm]
  rw [heq]
  exact hL1.comp₂ hL3 (· * ·)

end F1GI

open F1GI in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (φ₀ : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → ℂ) (hφ₀ : IsLocallyConstant φ₀ ∧ HasCompactSupport φ₀)
    (lam0 : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hlam0 : IsLocallyConstant lam0)
    (ε : AddChar (p.adicCompletion ℚ) ℂ) (hε : ε = psiLocal ℚ p ∨ ε = (psiLocal ℚ p)⁻¹)
    (η : AddChar (p.adicCompletion ℚ) ℂ) (hη : η = psiLocal ℚ p ∨ η = (psiLocal ℚ p)⁻¹) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (g : LocalGL3 p),
      Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        rowFourier23 p η
            (fun X => (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
                φ₀ X * ∫ x : p.adicCompletion ℚ, ε x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))
              (X * ((g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹)
            (godementArg p h)
          * ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ)) μ₂ := by
  letI := localBorel ℚ p
  haveI := borelSpace_localBorel ℚ p
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  intro μ₂ _ g

  obtain ⟨U, hUo, hU⟩ :=
    LanglandsTunnell.CubicInduction.exists_isOpen_forall_mul_eq_of_mem_principalSeries2 p μ φ hφ
  have hKinv : IsLocallyConstant (fun h : GL (Fin 2) (p.adicCompletion ℚ) => jac p ε φ h⁻¹) :=
    (isLocallyConstant_jac p ε φ U hUo hU).comp_continuous continuous_inv
  have hF : IsLocallyConstant (Fη p φ₀ g η) := isLocallyConstant_Fη p φ₀ g hφ₀ hη
  have hL := isLocallyConstant_charFactor p lam0 hlam0
  have hI : IsLocallyConstant (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      jac p ε φ h⁻¹ * Fη p φ₀ g η h
        * (((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ))) :=
    (hKinv.comp₂ hF (· * ·)).comp₂ hL (· * ·)

  obtain ⟨S, hS, hoff⟩ := exists_compact_support p μ hμ σ hσ h01 φ hφ φ₀ hφ₀ g hε hη
    (fun h => ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
      * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
          ^ (1 / 2 : ℂ))
  have hint := hI.continuous.integrable_of_hasCompactSupport (μ := μ₂) (HasCompactSupport.intro hS hoff)
  refine hint.congr (ae_of_all _ fun h => ?_)
  simp only []
  rw [rowFourier23_jacquetDatum_eq p φ₀ g ε η φ h]
  ring

end
end S_LanglandsTunnell_CubicInduction_integrable_rowFourier23_jacquet_godementIntegrand_of_principalSeries2
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integrable_rowFourier23_jacquet_godementIntegrand_of_principalSeries2 (solution)
