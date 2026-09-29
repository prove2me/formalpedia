-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.godementDatum_mem_principalSeries2_and_support
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/10aa17fd-55c7-5454-b9e6-6ad5c3e35986

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_godementDatum_mem_principalSeries2_and_support
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace B1djf

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "Mx" => Matrix (Fin 2) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p)
local notation "M2" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)

theorem row_one_upperUnipotent2_mul (x : F) (g : GL (Fin 2) F) (Z : Mx) (k : Fin 3) :
    (((upperUnipotent2 p x * g : GL (Fin 2) F) : M2) * Z) 1 k = ((g : M2) * Z) 1 k := by
  have h1 : ∀ j : Fin 2, ((upperUnipotent2 p x * g : GL (Fin 2) F) : M2) 1 j = (g : M2) 1 j := by
    intro j
    rw [Units.val_mul, upperUnipotent2_coe, Matrix.mul_apply]
    simp [Fin.sum_univ_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h1]

theorem det_upperUnipotent2_mul (x : F) (g : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (upperUnipotent2 p x * g) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul]
  have : Matrix.GeneralLinearGroup.det (upperUnipotent2 p x) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent2_coe, Matrix.det_fin_two_of]; simp
  rw [this, one_mul]

theorem row_one_diagonal2_mul (a : Fin 2 → Fˣ) (g : GL (Fin 2) F) (Z : Mx) (k : Fin 3) :
    (((diagonal2 p a * g : GL (Fin 2) F) : M2) * Z) 1 k = (a 1 : F) * ((g : M2) * Z) 1 k := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, diagonal2_coe, Matrix.diagonal]
  ring

theorem det_diagonal2_mul (a : Fin 2 → Fˣ) (g : GL (Fin 2) F) :
    ((Matrix.GeneralLinearGroup.det (diagonal2 p a * g) : Fˣ) : F) =
      (a 0 : F) * (a 1 : F) * ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := by
  rw [map_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, diagonal2_coe, Matrix.det_diagonal,
    Fin.prod_univ_two]

theorem norm_eq_modulus (x : F) : ((modulus x : ℝ)) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p]; rfl

theorem mul_leftBlock_apply (g : M2) (Z : Mx) (k : Fin 2) :
    (g * (Matrix.of fun i j => Z i (Fin.castSucc j))) 1 k = (g * Z) 1 (Fin.castSucc k) := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

section Slot

variable (lam : Fin 3 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ))
  (Φ : (Fin 3 → HeightOneSpectrum.adicCompletion ℚ p) → ℂ) (T : LocalGL3 p)
  (c₀ : ℂ) (Kset : Set (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)))

def Zf (X : Mx) : Mx := X * ((T : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

def sf (X : Mx) : M2 := Matrix.of fun i j => Zf p T X i (Fin.castSucc j)

def Nf (X : Mx) (g : GL (Fin 2) F) : Mx := (g : M2) * Zf p T X

def slot (X : Mx) (g : GL (Fin 2) F) : ℂ :=
  c₀ * Kset.indicator (fun _ => (1 : ℂ)) (sf p T X) *
    (charExt (lam 0) (sf p T X).det)⁻¹ * ((‖(sf p T X).det‖⁻¹ : ℝ) : ℂ) *
    ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
    charExt (lam 1) (((Matrix.GeneralLinearGroup.det g : Fˣ) : F) * (sf p T X).det / Nf p T X g 1 0) *
    charExt (lam 2) (Nf p T X g 1 0) * ((‖Nf p T X g 1 0‖⁻¹ : ℝ) : ℂ) *
    Φ ![Nf p T X g 1 1 / Nf p T X g 1 0, Nf p T X g 1 2 / Nf p T X g 1 0,
      (Zf p T X 0 0 * Zf p T X 1 2 - Zf p T X 0 2 * Zf p T X 1 0) / (sf p T X).det]

theorem Nf_upperUnipotent2_mul (X : Mx) (x : F) (g : GL (Fin 2) F) (k : Fin 3) :
    Nf p T X (upperUnipotent2 p x * g) 1 k = Nf p T X g 1 k :=
  row_one_upperUnipotent2_mul p x g _ k

theorem Nf_diagonal2_mul (X : Mx) (a : Fin 2 → Fˣ) (g : GL (Fin 2) F) (k : Fin 3) :
    Nf p T X (diagonal2 p a * g) 1 k = (a 1 : F) * Nf p T X g 1 k :=
  row_one_diagonal2_mul p a g _ k

theorem slot_upperUnipotent2_mul (X : Mx) (x : F) (g : GL (Fin 2) F) :
    slot p lam Φ T c₀ Kset X (upperUnipotent2 p x * g) = slot p lam Φ T c₀ Kset X g := by
  simp only [slot, Nf_upperUnipotent2_mul, det_upperUnipotent2_mul]

theorem slot_diagonal2_mul (X : Mx) (a : Fin 2 → Fˣ) (g : GL (Fin 2) F) :
    slot p lam Φ T c₀ Kset X (diagonal2 p a * g) =
      torusChar2 p ![lam 1, lam 2] a * halfModulus2 p a * slot p lam Φ T c₀ Kset X g := by
  simp only [slot, Nf_diagonal2_mul]
  set N10 := Nf p T X g 1 0 with hN10
  set N11 := Nf p T X g 1 1
  set N12 := Nf p T X g 1 2
  set d := ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) with hd
  have hdet : ((Matrix.GeneralLinearGroup.det (diagonal2 p a * g) : Fˣ) : F) = (a 0 : F) * (a 1 : F) * d :=
    det_diagonal2_mul p a g
  rw [hdet]
  have ha0 : (a 0 : F) ≠ 0 := (a 0).ne_zero
  have ha1 : (a 1 : F) ≠ 0 := (a 1).ne_zero
  by_cases h0 : N10 = 0
  ·
    simp [h0]

  have e1 : (a 0 : F) * (a 1 : F) * d * (sf p T X).det / ((a 1 : F) * N10) = (a 0 : F) * (d * (sf p T X).det / N10) := by
    field_simp
  have e2 : charExt (lam 1) ((a 0 : F) * (d * (sf p T X).det / N10)) = ((lam 1 (a 0) : ℂˣ) : ℂ) * charExt (lam 1) (d * (sf p T X).det / N10) :=
    charExt_units_mul _ _ _ _
  have e3 : charExt (lam 2) ((a 1 : F) * N10) = ((lam 2 (a 1) : ℂˣ) : ℂ) * charExt (lam 2) N10 := charExt_units_mul _ _ _ _
  have e4 : ((‖(a 1 : F) * N10‖⁻¹ : ℝ) : ℂ) = ((‖(a 1 : F)‖⁻¹ : ℝ) : ℂ) * ((‖N10‖⁻¹ : ℝ) : ℂ) := by
    rw [norm_mul, mul_inv]; push_cast; ring
  have e5 : (a 1 : F) * N11 / ((a 1 : F) * N10) = N11 / N10 := by field_simp
  have e6 : (a 1 : F) * N12 / ((a 1 : F) * N10) = N12 / N10 := by field_simp
  have e7 : ((modulus ((a 0 : F) * (a 1 : F) * d) : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (‖(a 0 : F)‖ * ‖(a 1 : F)‖) : ℝ) : ℂ) * ((modulus d : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
    rw [norm_eq_modulus, norm_eq_modulus, norm_mul, norm_mul, Real.sqrt_eq_rpow,
      Complex.ofReal_cpow (by positivity), show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by push_cast; ring]
    rw [show (((‖(a 0 : F)‖ * ‖(a 1 : F)‖ * ‖d‖ : ℝ)) : ℂ) = ((‖(a 0 : F)‖ * ‖(a 1 : F)‖ : ℝ) : ℂ) * ((‖d‖ : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]
  have e8 : torusChar2 p ![lam 1, lam 2] a * halfModulus2 p a =
      ((lam 1 (a 0) : ℂˣ) : ℂ) * ((lam 2 (a 1) : ℂˣ) : ℂ) *
        (((Real.sqrt (‖(a 0 : F)‖ * ‖(a 1 : F)‖) : ℝ) : ℂ) * ((‖(a 1 : F)‖⁻¹ : ℝ) : ℂ)) := by
    simp only [torusChar2, halfModulus2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 1
    have h1 : 0 < ‖(a 1 : F)‖ := norm_pos_iff.mpr ha1
    rw [← Complex.ofReal_mul]
    congr 1
    set x := ‖(a 0 : F)‖ with hx
    set y := ‖(a 1 : F)‖ with hy
    have hx0 : 0 ≤ x := norm_nonneg _
    symm
    calc Real.sqrt (x * y) * y⁻¹ = Real.sqrt (x / y * (y * y)) * y⁻¹ := by
          congr 2; field_simp
      _ = Real.sqrt (x / y) * Real.sqrt (y * y) * y⁻¹ := by rw [Real.sqrt_mul (div_nonneg hx0 h1.le)]
      _ = Real.sqrt (x / y) := by rw [Real.sqrt_mul_self h1.le]; field_simp
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  ring

end Slot

section Support

variable (lam : Fin 3 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ))
  (Φ : (Fin 3 → HeightOneSpectrum.adicCompletion ℚ p) → ℂ) (T : LocalGL3 p)
  (c₀ : ℂ) (Kset : Set (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)))

theorem charExt_ne_zero_imp (χ : Fˣ →* ℂˣ) {x : F} (h : charExt χ x ≠ 0) : x ≠ 0 := by
  rintro rfl; simp at h

theorem of_slot_ne_zero (R : ℝ) (hR : ∀ y : Fin 3 → F, Φ y ≠ 0 → ∀ i, ‖y i‖ ≤ R)
    (X : Mx) (g : GL (Fin 2) F) (h : slot p lam Φ T c₀ Kset X g ≠ 0) :
    sf p T X ∈ Kset ∧ Nf p T X g 1 0 ≠ 0 ∧
      ‖Nf p T X g 1 1‖ ≤ R * ‖Nf p T X g 1 0‖ ∧ ‖Nf p T X g 1 2‖ ≤ R * ‖Nf p T X g 1 0‖ ∧
      ‖(Zf p T X 0 0 * Zf p T X 1 2 - Zf p T X 0 2 * Zf p T X 1 0) / (sf p T X).det‖ ≤ R := by
  unfold slot at h
  have hΦ := right_ne_zero_of_mul h
  have h7 := left_ne_zero_of_mul h
  have h6 := left_ne_zero_of_mul h7
  have hχ2 := right_ne_zero_of_mul h6
  have h5 := left_ne_zero_of_mul h6
  have h4 := left_ne_zero_of_mul h5
  have h3 := left_ne_zero_of_mul h4
  have h2 := left_ne_zero_of_mul h3
  have h1 := left_ne_zero_of_mul h2
  have hind := right_ne_zero_of_mul h1
  have hK : sf p T X ∈ Kset := by
    by_contra hn; exact hind (Set.indicator_of_notMem hn _)
  have hN : Nf p T X g 1 0 ≠ 0 := charExt_ne_zero_imp p (lam 2) hχ2
  have hNpos : 0 < ‖Nf p T X g 1 0‖ := norm_pos_iff.mpr hN
  have hb := hR _ hΦ
  refine ⟨hK, hN, ?_, ?_, ?_⟩
  · have := hb 0
    simp only [Matrix.cons_val_zero, norm_div] at this
    rwa [div_le_iff₀ hNpos] at this
  · have := hb 1
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, norm_div] at this
    rwa [div_le_iff₀ hNpos] at this
  · have := hb 2
    simpa using this

theorem bottom_row_of_mul {R δ : ℝ} (hR : 1 ≤ R) (hδ1 : δ < 1) (hRδ : R * δ < 1)
    (g : GL (Fin 2) F) (s : M2)
    (hs00 : ‖s 0 0 - 1‖ < δ) (hs01 : ‖s 0 1‖ < δ) (hs10 : ‖s 1 0‖ < δ) (hs11 : ‖s 1 1 - 1‖ < δ)
    (h10 : ((g : M2) * s) 1 0 ≠ 0) (hle : ‖((g : M2) * s) 1 1‖ ≤ R * ‖((g : M2) * s) 1 0‖) :
    (g : M2) 1 0 ≠ 0 ∧ ‖(g : M2) 1 1‖ ≤ R * ‖(g : M2) 1 0‖ := by
  set a := (g : M2) 1 0 with ha
  set b := (g : M2) 1 1 with hb
  have hδ0 : 0 ≤ δ := le_of_lt (lt_of_le_of_lt (norm_nonneg _) hs01)
  have hgs10 : ((g : M2) * s) 1 0 = a * s 0 0 + b * s 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  have hgs11 : ((g : M2) * s) 1 1 = a * s 0 1 + b * s 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]

  have hunit : ∀ u : F, ‖u - 1‖ < δ → ‖u‖ = 1 := by
    intro u hu
    have hu1 : ‖u - 1‖ < 1 := hu.trans hδ1
    have e : u = (u - 1) + 1 := by ring
    apply le_antisymm
    · rw [e]; refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      simp [hu1.le]
    · by_contra hlt
      push Not at hlt
      have : ‖(1 : F)‖ ≤ max ‖u‖ ‖u - 1‖ := by
        calc ‖(1 : F)‖ = ‖u + -(u - 1)‖ := by congr 1; ring
          _ ≤ max ‖u‖ ‖-(u - 1)‖ := IsUltrametricDist.norm_add_le_max _ _
          _ = max ‖u‖ ‖u - 1‖ := by rw [norm_neg]
      rw [norm_one] at this
      rcases le_max_iff.mp this with h | h
      · exact absurd h (not_le.mpr hlt)
      · exact absurd h (not_le.mpr hu1)
  have hs00' : ‖s 0 0‖ = 1 := hunit _ hs00
  have hs11' : ‖s 1 1‖ = 1 := hunit _ hs11

  have hab : ¬ (a = 0 ∧ b = 0) := by
    rintro ⟨ha0, hb0⟩
    apply h10
    rw [hgs10, ha0, hb0]; ring

  have hmain : ‖b‖ ≤ R * ‖a‖ := by
    by_contra hlt
    push Not at hlt
    have hb0 : b ≠ 0 := by
      intro hb0'
      rw [hb0', norm_zero] at hlt
      have := mul_nonneg (le_trans zero_le_one hR) (norm_nonneg a)
      linarith
    have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0

    have h1 : ‖a * s 0 1‖ < ‖b * s 1 1‖ := by
      rw [norm_mul, norm_mul, hs11', mul_one]
      by_cases ha0 : a = 0
      · rw [ha0, norm_zero, zero_mul]; exact hbpos
      · have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
        calc ‖a‖ * ‖s 0 1‖ < ‖a‖ * 1 := by gcongr; exact hs01.trans hδ1
          _ ≤ R * ‖a‖ := by rw [mul_one]; nlinarith
          _ < ‖b‖ := hlt
    have h2 : ‖((g : M2) * s) 1 1‖ = ‖b‖ := by
      rw [hgs11, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt h1), max_eq_right h1.le,
        norm_mul, hs11', mul_one]
    have h3 : ‖((g : M2) * s) 1 0‖ ≤ max ‖a‖ (δ * ‖b‖) := by
      rw [hgs10]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
      · rw [norm_mul, hs00', mul_one]
      · rw [norm_mul, mul_comm]; gcongr
    rw [h2] at hle
    have h4 : ‖b‖ ≤ R * max ‖a‖ (δ * ‖b‖) := hle.trans (by gcongr)
    rcases le_total ‖a‖ (δ * ‖b‖) with hcase | hcase
    · rw [max_eq_right hcase] at h4
      nlinarith
    · rw [max_eq_left hcase] at h4
      linarith
  refine ⟨?_, hmain⟩
  intro ha0
  rw [ha0, norm_zero, mul_zero] at hmain
  exact hab ⟨ha0, norm_le_zero_iff.mp hmain⟩

end Support

section CompactSupport

variable (lam : Fin 3 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ))
  (Φ : (Fin 3 → HeightOneSpectrum.adicCompletion ℚ p) → ℂ) (T : LocalGL3 p)
  (c₀ : ℂ) (Kset : Set (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)))

def glue (P : M2 × (F × F)) : Mx :=
  Matrix.of fun i k => Fin.lastCases (![P.2.1, P.2.2] i) (fun k' : Fin 2 => P.1 i k') k

theorem continuous_glue : Continuous (glue p) := by
  refine continuous_matrix fun i k => ?_
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · simp only [glue, Matrix.of_apply, Fin.lastCases_last]
    fin_cases i <;> simp <;> fun_prop
  · simp only [glue, Matrix.of_apply, Fin.lastCases_castSucc]
    exact (Continuous.matrix_elem continuous_fst i k')

theorem glue_sf (X : Mx) : glue p (sf p T X, (Zf p T X 0 2, Zf p T X 1 2)) = Zf p T X := by
  ext i k
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · simp only [glue, Matrix.of_apply, Fin.lastCases_last]
    fin_cases i <;> simp <;> rfl
  · simp only [glue, Matrix.of_apply, Fin.lastCases_castSucc, sf]

def mv (P : M2 × (F × F)) : F × F :=
  (P.1 0 0 * P.2.1 + P.1 0 1 * P.2.2, P.1 1 0 * P.2.1 + P.1 1 1 * P.2.2)

theorem continuous_mv : Continuous (mv p) := by
  unfold mv
  refine Continuous.prodMk ?_ ?_
  · exact ((Continuous.matrix_elem continuous_fst 0 0).mul (continuous_fst.comp continuous_snd)).add
      ((Continuous.matrix_elem continuous_fst 0 1).mul (continuous_snd.comp continuous_snd))
  · exact ((Continuous.matrix_elem continuous_fst 1 0).mul (continuous_fst.comp continuous_snd)).add
      ((Continuous.matrix_elem continuous_fst 1 1).mul (continuous_snd.comp continuous_snd))

def bigBox (R : ℝ) : Set Mx :=
  (fun Z : Mx => Z * ((T⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ''
    (glue p '' (Kset ×ˢ (mv p '' (Kset ×ˢ (Metric.closedBall (0 : F) (max R (R * R)) ×ˢ Metric.closedBall (0 : F) R)))))

theorem isCompact_bigBox (hK : IsCompact Kset) (R : ℝ) : IsCompact (bigBox p T Kset R) := by
  unfold bigBox
  refine IsCompact.image ?_ (continuous_id.matrix_mul continuous_const)
  refine IsCompact.image (hK.prod ?_) (continuous_glue p)
  refine IsCompact.image (hK.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))) (continuous_mv p)

theorem mem_bigBox_of_slot_ne_zero (hKdet : ∀ s ∈ Kset, s.det ≠ 0)
    (R : ℝ) (hR : ∀ y : Fin 3 → F, Φ y ≠ 0 → ∀ i, ‖y i‖ ≤ R)
    (X : Mx) (g : GL (Fin 2) F) (h : slot p lam Φ T c₀ Kset X g ≠ 0) : X ∈ bigBox p T Kset R := by
  obtain ⟨hK, hN, h11, h12, hmin⟩ := of_slot_ne_zero p lam Φ T c₀ Kset R hR X g h
  set Z := Zf p T X with hZ
  set s := sf p T X with hs
  have hsdet : s.det ≠ 0 := hKdet s hK

  set c0 := Z 0 2 with hc0
  set c1 := Z 1 2 with hc1
  set u1 := (s 1 1 * c0 - s 0 1 * c1) / s.det with hu1
  set u2 := (s 0 0 * c1 - s 1 0 * c0) / s.det with hu2
  have hsd : s.det = s 0 0 * s 1 1 - s 0 1 * s 1 0 := Matrix.det_fin_two s
  have hmv : mv p (s, (u1, u2)) = (c0, c1) := by
    simp only [mv, hu1, hu2, Prod.mk.injEq]
    constructor <;> field_simp <;> rw [hsd] <;> ring

  have hs00 : s 0 0 = Z 0 0 := rfl
  have hs10 : s 1 0 = Z 1 0 := rfl
  have hs01 : s 0 1 = Z 0 1 := rfl
  have hs11 : s 1 1 = Z 1 1 := rfl

  have hmin' : (Z 0 0 * Z 1 2 - Z 0 2 * Z 1 0) / s.det = u2 := by
    simp only [hu2, hs00, hs10, hc0, hc1]; ring
  have hu2b : ‖u2‖ ≤ R := by rw [← hmin']; exact hmin

  set N10 := Nf p T X g 1 0 with hN10
  set N11 := Nf p T X g 1 1 with hN11
  set N12 := Nf p T X g 1 2 with hN12
  have hN10e : N10 = (g : M2) 1 0 * Z 0 0 + (g : M2) 1 1 * Z 1 0 := by
    simp [hN10, Nf, hZ, Matrix.mul_apply, Fin.sum_univ_two]
  have hN11e : N11 = (g : M2) 1 0 * Z 0 1 + (g : M2) 1 1 * Z 1 1 := by
    simp [hN11, Nf, hZ, Matrix.mul_apply, Fin.sum_univ_two]
  have hN12e : N12 = (g : M2) 1 0 * Z 0 2 + (g : M2) 1 1 * Z 1 2 := by
    simp [hN12, Nf, hZ, Matrix.mul_apply, Fin.sum_univ_two]
  have hrel : u1 = N12 / N10 - (N11 / N10) * u2 := by
    rw [hN10e, hN11e, hN12e, hu1, hu2]
    rw [hN10e] at hN
    field_simp
    rw [hsd, hs00, hs01, hs10, hs11, hc0, hc1]
    ring
  have hNpos : 0 < ‖N10‖ := norm_pos_iff.mpr hN
  have ht : ‖N11 / N10‖ ≤ R := by rw [norm_div, div_le_iff₀ hNpos]; exact h11
  have h12' : ‖N12 / N10‖ ≤ R := by rw [norm_div, div_le_iff₀ hNpos]; exact h12
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) ht
  have hu1b : ‖u1‖ ≤ max R (R * R) := by
    rw [hrel, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg, norm_mul]
    exact max_le_max h12' (mul_le_mul ht hu2b (norm_nonneg _) hR0)

  have hX : X = Z * ((T⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [hZ, Zf, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  refine ⟨Z, ⟨(s, (c0, c1)), ⟨hK, (s, (u1, u2)), ⟨hK, ?_, ?_⟩, hmv⟩, ?_⟩, hX.symm⟩
  · simpa [Metric.mem_closedBall, dist_zero_right] using hu1b
  · simpa [Metric.mem_closedBall, dist_zero_right] using hu2b
  · rw [hs, hc0, hc1, hZ]; exact glue_sf p T X

theorem hasCompactSupport_slot (hK : IsCompact Kset) (hKdet : ∀ s ∈ Kset, s.det ≠ 0)
    (R : ℝ) (hR : ∀ y : Fin 3 → F, Φ y ≠ 0 → ∀ i, ‖y i‖ ≤ R) :
    HasCompactSupport (slot p lam Φ T c₀ Kset) := by
  refine HasCompactSupport.intro (isCompact_bigBox p T Kset hK R) fun X hX => ?_
  funext g
  by_contra h
  exact hX (mem_bigBox_of_slot_ne_zero p lam Φ T c₀ Kset hKdet R hR X g h)

end CompactSupport

private theorem _root_.B1djf_secondCountable : SecondCountableTopology (GL (Fin 2) F) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → F))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) F)).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

end B1djf

set_option linter.unusedSectionVars false

noncomputable section

namespace B1dLC48

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem coe_unipotent (x : F) : ((unipotent x : G₂) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl

theorem mem_K0 (k : G₂) (h : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1)
    (h' : ∀ i j, Valued.v (((k⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1) :
    k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  rw [AdelicDock.mem_localLevelOne_iff]
  have aux : ∀ (m : Matrix (Fin 2) (Fin 2) F), (∀ i j, Valued.v (m i j) ≤ 1) → AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
    intro m hm
    refine ⟨fun i j => by rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]; exact hm i j, ?_, ?_⟩
    · rw [NumberField.AdelicLevel.idealBound_top]; exact hm 1 0
    · rw [NumberField.AdelicLevel.idealBound_top]
      refine (Valuation.map_sub _ _ _).trans (max_le (hm 1 1) ?_)
      rw [Valuation.map_one]
  exact ⟨aux _ h, aux _ h'⟩

theorem valued_le_one_iff_norm_le_one (x : F) : Valued.v x ≤ 1 ↔ ‖x‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).symm

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

theorem kLow_mem (c : F) (hc : ‖c‖ ≤ 1) : kLow (p := p) c ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have hc' : Valued.v c ≤ 1 := (valued_le_one_iff_norm_le_one c).mpr hc
  have hnc : Valued.v (-c) ≤ 1 := by rwa [Valuation.map_neg]
  refine mem_K0 _ ?_ ?_ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [kLow, hc', hnc, Valuation.map_neg]

theorem kFlip_mem (c : F) (hc : ‖c‖ ≤ 1) : kFlip (p := p) c ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have hc' : Valued.v c ≤ 1 := (valued_le_one_iff_norm_le_one c).mpr hc
  have hnc : Valued.v (-c) ≤ 1 := by rwa [Valuation.map_neg]
  refine mem_K0 _ ?_ ?_ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [kFlip, hc', hnc, Valuation.map_neg]

theorem exists_iwasawa (g : G₂) :
    ∃ (x : F) (α β : Fˣ) (k : G₂), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ ∧
      g = unipotent x * diagUnits2 α β * k ∧
      ‖(β : F)‖ = max ‖(g : Matrix (Fin 2) (Fin 2) F) 1 0‖ ‖(g : Matrix (Fin 2) (Fin 2) F) 1 1‖ ∧
      ‖(α : F)‖ * ‖(β : F)‖ = ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ := by
  set g10 := (g : Matrix (Fin 2) (Fin 2) F) 1 0 with h10
  set g11 := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with h11
  set g00 := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with h00
  set g01 := (g : Matrix (Fin 2) (Fin 2) F) 0 1 with h01
  have hdet : ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = g00 * g11 - g01 * g10 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hdet0 : g00 * g11 - g01 * g10 ≠ 0 := hdet ▸ (Matrix.GeneralLinearGroup.det g).ne_zero
  by_cases hle : ‖g10‖ ≤ ‖g11‖
  ·
    have h11ne : g11 ≠ 0 := by
      intro h; apply hdet0
      have : g10 = 0 := by rw [h, norm_zero] at hle; exact norm_le_zero_iff.mp hle
      rw [h, this]; ring
    set α : F := (g00 * g11 - g01 * g10) / g11 with hα
    have hα0 : α ≠ 0 := div_ne_zero hdet0 h11ne
    refine ⟨g01 / g11, Units.mk0 α hα0, Units.mk0 g11 h11ne, kLow (g10 / g11),
      kLow_mem _ (by rw [norm_div]; exact div_le_one_of_le₀ hle (norm_nonneg _)), ?_, ?_, ?_⟩
    · refine Units.ext ?_
      simp only [Units.val_mul, coe_unipotent, coe_diagUnits2, Units.val_mk0]
      show (g : Matrix (Fin 2) (Fin 2) F) = _
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, kLow, ← h00, ← h01, ← h10, ← h11, hα] <;>
        field_simp <;> ring
    · rw [Units.val_mk0, max_eq_right hle]
    · rw [Units.val_mk0, Units.val_mk0, hdet, hα, norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr h11ne)]
  ·
    push Not at hle
    have h10ne : g10 ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) hle)
    set α : F := -(g00 * g11 - g01 * g10) / g10 with hα
    have hα0 : α ≠ 0 := div_ne_zero (neg_ne_zero.mpr hdet0) h10ne
    refine ⟨g00 / g10, Units.mk0 α hα0, Units.mk0 g10 h10ne, kFlip (g11 / g10),
      kFlip_mem _ (by rw [norm_div]; exact div_le_one_of_le₀ hle.le (norm_nonneg _)), ?_, ?_, ?_⟩
    · refine Units.ext ?_
      simp only [Units.val_mul, coe_unipotent, coe_diagUnits2, Units.val_mk0]
      show (g : Matrix (Fin 2) (Fin 2) F) = _
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, kFlip, ← h00, ← h01, ← h10, ← h11, hα] <;>
        field_simp <;> ring
    · rw [Units.val_mk0, max_eq_left hle.le]
    · rw [Units.val_mk0, Units.val_mk0, hdet, hα, norm_div, norm_neg, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr h10ne)]

end B1dLC48

namespace B1dLC48

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction Filter Topology

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "M23" => Matrix (Fin 2) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p)

theorem upperUnipotent2_eq_unipotent (x : F) : upperUnipotent2 p x = (unipotent x : G₂) :=
  Units.ext rfl

theorem diagUnits2_eq_diagonal2 (α β : Fˣ) : (diagUnits2 α β : G₂) = diagonal2 p ![α, β] := by
  refine Units.ext ?_
  rw [coe_diagUnits2, diagonal2_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem uniform_of_joint (χ : Fin 2 → (Fˣ →* ℂˣ)) (φ : M23 → G₂ → ℂ)
    (hA : IsLocallyConstant (fun P : M23 × G₂ => φ P.1 P.2))
    (hN : ∀ (X : M23) (x : F) (g : G₂), φ X (upperUnipotent2 p x * g) = φ X g)
    (hT : ∀ (X : M23) (a : Fin 2 → Fˣ) (g : G₂), φ X (diagonal2 p a * g) = torusChar2 p χ a * halfModulus2 p a * φ X g) :
    IsLocallyConstant φ := by
  classical
  obtain ⟨hKc, -⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p (⊤ : Ideal (𝓞 ℚ)) top_ne_bot
  rw [IsLocallyConstant.iff_eventually_eq]
  intro X₀

  have hloc := (IsLocallyConstant.iff_exists_open _).1 hA
  choose U hUo hUmem hUconst using fun c : G₂ => hloc (X₀, c)
  have hprod : ∀ c : G₂, ∃ V ∈ 𝓝 X₀, ∃ W ∈ 𝓝 c, V ×ˢ W ⊆ U c :=
    fun c => mem_nhds_prod_iff.1 ((hUo c).mem_nhds (hUmem c))
  choose V hV W hW hVW using hprod
  obtain ⟨t, -, hcover⟩ := hKc.elim_nhds_subcover W (fun c _ => hW c)
  have hVt : (⋂ c ∈ t, V c) ∈ 𝓝 X₀ := (Filter.biInter_finset_mem t).2 (fun c _ => hV c)
  refine Filter.eventually_of_mem hVt fun X hX => ?_

  have hK : ∀ k ∈ (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set G₂), φ X k = φ X₀ k := by
    intro k hk
    obtain ⟨c, hct, hkc⟩ := Set.mem_iUnion₂.mp (hcover hk)
    have hXc : X ∈ V c := Set.mem_iInter₂.mp hX c hct
    have h1 : φ X k = φ X₀ c := hUconst c (X, k) (hVW c ⟨hXc, hkc⟩)
    have h2 : φ X₀ k = φ X₀ c := hUconst c (X₀, k) (hVW c ⟨mem_of_mem_nhds (hV c), hkc⟩)
    rw [h1, h2]
  funext g
  obtain ⟨x, α, β, k, hk, hg, -, -⟩ := exists_iwasawa g
  rw [hg, ← upperUnipotent2_eq_unipotent, diagUnits2_eq_diagonal2, mul_assoc, hN, hN, hT, hT, hK k hk]

end B1dLC48

end

namespace B1dLC48

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction Filter Topology MeasureTheory

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "M2" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)
local notation "M23" => Matrix (Fin 2) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p)

theorem isOpen_image_val {K : Set G₂} (hK : IsOpen K) : IsOpen (Units.val '' K) := by

  have hD : IsOpen {m : M2 | m.det ≠ 0} := isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  let σ : {m : M2 // m.det ≠ 0} → G₂ := fun m => Matrix.GeneralLinearGroup.mkOfDetNeZero m.1 m.2
  have hσ : Continuous σ := by
    rw [Units.continuous_iff]
    refine ⟨continuous_subtype_val, ?_⟩
    show Continuous fun m : {m : M2 // m.det ≠ 0} => (((σ m)⁻¹ : G₂) : M2)
    have : (fun m : {m : M2 // m.det ≠ 0} => (((σ m)⁻¹ : G₂) : M2)) = fun m => Ring.inverse (m.1.det) • (m.1).adjugate := by
      funext m
      rw [Matrix.coe_units_inv, Matrix.inv_def]
      rfl
    rw [this]
    refine Continuous.fun_smul ?_ (continuous_subtype_val.matrix_adjugate)
    have : (fun m : {m : M2 // m.det ≠ 0} => Ring.inverse (m.1.det)) = fun m => (m.1.det)⁻¹ := by
      funext m; rw [Ring.inverse_eq_inv']
    rw [this]
    exact (continuous_subtype_val.matrix_det).inv₀ fun m => m.2
  have heq : Units.val '' K = Subtype.val '' (σ ⁻¹' K) := by
    ext m
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hkd : (k : M2).det ≠ 0 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det k).ne_zero
      refine ⟨⟨(k : M2), hkd⟩, ?_, rfl⟩
      show σ ⟨(k : M2), hkd⟩ ∈ K
      have : σ ⟨(k : M2), hkd⟩ = k := Units.ext rfl
      rw [this]; exact hk
    · rintro ⟨m, hm, rfl⟩
      exact ⟨σ m, hm, rfl⟩
  rw [heq]
  exact hD.isOpenMap_subtype_val _ (hK.preimage hσ)

theorem continuous_vec3 : Continuous fun q : F × F × F => (![q.1, q.2.1, q.2.2] : Fin 3 → F) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

theorem exists_bound_of_hasCompactSupport (Φ : (Fin 3 → F) → ℂ) (hΦ : HasCompactSupport Φ) :
    ∃ R : ℝ, ∀ z : Fin 3 → F, Φ z ≠ 0 → ‖z 0‖ ≤ R := by
  obtain ⟨R, hR⟩ := hΦ.isCompact.isBounded.exists_norm_le
  exact ⟨R, fun z hz => (norm_le_pi_norm z 0).trans (hR z (subset_tsupport _ hz))⟩

set_option maxHeartbeats 6400000 in

theorem jointA
    (lam : Fin 3 → (Fˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → F) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (T : LocalGL3 p) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure G₂) [μ₂.IsHaarMeasure] (K : Subgroup G₂),
      IsOpen (K : Set G₂) → IsCompact (K : Set G₂) →
    ∀ (φsec : M23 → G₂ → ℂ),
      (φsec = fun (X : M23) (g : G₂) =>
        let Z : M23 := X * (T : Matrix (Fin 3) (Fin 3) F)
        let s : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => Z i (Fin.castSucc j)
        let N : M23 := (g : Matrix (Fin 2) (Fin 2) F) * Z
        ((μ₂ (K : Set G₂)).toReal : ℂ)⁻¹ *
          (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det T : Fˣ) : F) : ℝ) : ℂ)) *
          (Units.val '' (K : Set G₂)).indicator (fun _ => (1 : ℂ)) s *
          (charExt (lam 0) s.det)⁻¹ * ((‖s.det‖⁻¹ : ℝ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          charExt (lam 1) (((Matrix.GeneralLinearGroup.det g : Fˣ) : F) * s.det / N 1 0) *
          charExt (lam 2) (N 1 0) * ((‖N 1 0‖⁻¹ : ℝ) : ℂ) *
          Φ ![N 1 1 / N 1 0, N 1 2 / N 1 0, (Z 0 0 * Z 1 2 - Z 0 2 * Z 1 0) / s.det]) →
    IsLocallyConstant (fun P : M23 × G₂ => φsec P.1 P.2) := by
  intro μ₂ _ K hKo hKc φsec hφ
  subst hφ
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨X₀, g₀⟩
  dsimp only

  have hT : Continuous fun y : M23 × G₂ => y.1 * (T : Matrix (Fin 3) (Fin 3) F) := continuous_fst.matrix_mul continuous_const
  have hs : Continuous fun y : M23 × G₂ => (Matrix.of fun i j => (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2) :=
    continuous_matrix fun i j => hT.matrix_elem i (Fin.castSucc j)
  have hsdet : Continuous fun y : M23 × G₂ => (Matrix.of fun i j => (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2).det :=
    hs.matrix_det
  have hg : Continuous fun y : M23 × G₂ => ((y.2 : G₂) : M2) := Units.continuous_val.comp continuous_snd
  have hN : Continuous fun y : M23 × G₂ => ((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) := hg.matrix_mul hT
  have hN1 : ∀ j : Fin 3, Continuous fun y : M23 × G₂ => (((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 j :=
    fun j => hN.matrix_elem 1 j
  have hdg : Continuous fun y : M23 × G₂ => ((Matrix.GeneralLinearGroup.det y.2 : Fˣ) : F) := by
    have : (fun y : M23 × G₂ => ((Matrix.GeneralLinearGroup.det y.2 : Fˣ) : F)) = fun y => (((y.2 : G₂) : M2)).det := by
      funext y; rw [Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]; exact hg.matrix_det
  have hw : Continuous fun y : M23 × G₂ =>
      (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) 0 0 * (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) 1 2 -
        (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) 0 2 * (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) 1 0 :=
    ((hT.matrix_elem 0 0).mul (hT.matrix_elem 1 2)).sub ((hT.matrix_elem 0 2).mul (hT.matrix_elem 1 0))
  have hK'open : IsOpen (Units.val '' (K : Set G₂)) := isOpen_image_val hKo
  have hK'closed : IsClosed (Units.val '' (K : Set G₂)) := (hKc.image Units.continuous_val).isClosed

  by_cases hsK : (Matrix.of fun i j => (X₀ * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2) ∈ Units.val '' (K : Set G₂)
  · obtain ⟨k₀, hk₀, hk₀s⟩ := hsK
    have hsdet0 : (Matrix.of fun i j => (X₀ * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2).det ≠ 0 := by
      rw [← hk₀s, ← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det k₀).ne_zero
    have hsK' : (Matrix.of fun i j => (X₀ * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2) ∈ Units.val '' (K : Set G₂) := ⟨k₀, hk₀, hk₀s⟩
    have e1 : ∀ᶠ y : M23 × G₂ in 𝓝 (X₀, g₀),
        (Matrix.of fun i j => (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2) ∈ Units.val '' (K : Set G₂) :=
      (hs.continuousAt (x := (X₀, g₀))).eventually (hK'open.mem_nhds hsK')
    have e3 : ∀ᶠ y : M23 × G₂ in 𝓝 (X₀, g₀),
        ‖(Matrix.of fun i j => (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2).det‖ = ‖(Matrix.of fun i j => (X₀ * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2).det‖ :=
      (hsdet.continuousAt (x := (X₀, g₀))).eventually (p := fun z : F => ‖z‖ = ‖(Matrix.of fun i j => (X₀ * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2).det‖) (eventually_norm_eq p hsdet0)
    have e2 : ∀ᶠ y : M23 × G₂ in 𝓝 (X₀, g₀),
        charExt (lam 0) (Matrix.of fun i j => (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2).det = charExt (lam 0) (Matrix.of fun i j => (X₀ * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2).det :=
      (hsdet.continuousAt (x := (X₀, g₀))).eventually (eventually_charExt_eq p (lam 0) (hlam 0) hsdet0)
    have hdg0 : ((Matrix.GeneralLinearGroup.det g₀ : Fˣ) : F) ≠ 0 := (Matrix.GeneralLinearGroup.det g₀).ne_zero
    have e4 : ∀ᶠ y : M23 × G₂ in 𝓝 (X₀, g₀),
        ‖((Matrix.GeneralLinearGroup.det y.2 : Fˣ) : F)‖ = ‖((Matrix.GeneralLinearGroup.det g₀ : Fˣ) : F)‖ :=
      (hdg.continuousAt (x := (X₀, g₀))).eventually (eventually_norm_eq p hdg0)
    by_cases hn0 : ((((g₀ : G₂) : M2) * (X₀ * (T : Matrix (Fin 3) (Fin 3) F))) 1 0) = 0
    ·

      have hn1 : ((((g₀ : G₂) : M2) * (X₀ * (T : Matrix (Fin 3) (Fin 3) F))) 1 1) ≠ 0 := by
        intro h1
        apply (Matrix.GeneralLinearGroup.det g₀).ne_zero
        have hv : ∀ j : Fin 2, ∑ l : Fin 2, ((g₀ : G₂) : M2) 1 l * (Matrix.of fun i j => (X₀ * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2) l j = 0 := by
          intro j
          fin_cases j
          · have := hn0; rw [Matrix.mul_apply, Fin.sum_univ_two] at this
            rw [Fin.sum_univ_two]; simpa [Matrix.of_apply] using this
          · have := h1; rw [Matrix.mul_apply, Fin.sum_univ_two] at this
            rw [Fin.sum_univ_two]; simpa [Matrix.of_apply] using this
        have hkk : (Matrix.of fun i j => (X₀ * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2) * (((k₀⁻¹ : G₂)) : M2) = 1 := by rw [← hk₀s, ← Units.val_mul, mul_inv_cancel, Units.val_one]
        have hv' : Matrix.vecMul (fun l : Fin 2 => ((g₀ : G₂) : M2) 1 l) (Matrix.of fun i j => (X₀ * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2) = 0 := by
          funext j
          exact hv j
        have hrow0 : (fun l : Fin 2 => ((g₀ : G₂) : M2) 1 l) = 0 := by
          calc (fun l : Fin 2 => ((g₀ : G₂) : M2) 1 l) = Matrix.vecMul (fun l : Fin 2 => ((g₀ : G₂) : M2) 1 l) (1 : M2) :=
                (Matrix.vecMul_one _).symm
            _ = Matrix.vecMul (fun l : Fin 2 => ((g₀ : G₂) : M2) 1 l) ((Matrix.of fun i j => (X₀ * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2) * (((k₀⁻¹ : G₂)) : M2)) := by rw [hkk]
            _ = Matrix.vecMul (Matrix.vecMul (fun l : Fin 2 => ((g₀ : G₂) : M2) 1 l) (Matrix.of fun i j => (X₀ * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2)) (((k₀⁻¹ : G₂)) : M2) :=
                (Matrix.vecMul_vecMul _ _ _).symm
            _ = 0 := by rw [hv', Matrix.zero_vecMul]
        have hrow : ∀ l : Fin 2, ((g₀ : G₂) : M2) 1 l = 0 := fun l => congrFun hrow0 l
        rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hrow 0, hrow 1]; ring
      obtain ⟨R, hR⟩ := exists_bound_of_hasCompactSupport Φ hΦ.2
      have hn1pos : 0 < ‖((((g₀ : G₂) : M2) * (X₀ * (T : Matrix (Fin 3) (Fin 3) F))) 1 1)‖ := norm_pos_iff.mpr hn1
      set R' : ℝ := max R 0 + 1 with hR'
      have hR'pos : 0 < R' := by rw [hR']; positivity
      have e5 : ∀ᶠ y : M23 × G₂ in 𝓝 (X₀, g₀),
          ‖(((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 1‖ = ‖((((g₀ : G₂) : M2) * (X₀ * (T : Matrix (Fin 3) (Fin 3) F))) 1 1)‖ :=
        ((hN1 1).continuousAt (x := (X₀, g₀))).eventually (eventually_norm_eq p hn1)
      have e6 : ∀ᶠ y : M23 × G₂ in 𝓝 (X₀, g₀),
          ‖(((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 0‖ < ‖((((g₀ : G₂) : M2) * (X₀ * (T : Matrix (Fin 3) (Fin 3) F))) 1 1)‖ / R' := by
        have ht : Tendsto (fun y : M23 × G₂ => (((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 0) (𝓝 (X₀, g₀)) (𝓝 0) := by
          have := (hN1 0).continuousAt (x := (X₀, g₀))
          rw [ContinuousAt] at this
          dsimp only at this
          rwa [hn0] at this
        exact (NormedAddGroup.tendsto_nhds_zero.1 ht) _ (div_pos hn1pos hR'pos)
      filter_upwards [e5, e6] with y h5 h6
      rw [hn0]
      simp only [norm_zero, inv_zero, Complex.ofReal_zero, mul_zero, zero_mul]

      generalize hc : ‖((((g₀ : G₂) : M2) * (X₀ * (T : Matrix (Fin 3) (Fin 3) F))) 1 1)‖ = c at h5 h6 hn1pos hR'pos
      generalize ha10 : (((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 0 = a10 at h5 h6
      generalize ha11 : (((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 1 = a11 at h5 h6
      by_cases hy0 : a10 = 0
      · rw [hy0]; simp only [norm_zero, inv_zero, Complex.ofReal_zero, mul_zero, zero_mul]
      · have hpos : 0 < ‖a10‖ := norm_pos_iff.mpr hy0
        have hbig : R < ‖a11 / a10‖ := by
          rw [norm_div, h5, lt_div_iff₀ hpos]
          have h1 : R * ‖a10‖ ≤ (max R 0 + 1) * ‖a10‖ :=
            mul_le_mul_of_nonneg_right (by linarith [le_max_left R 0]) (norm_nonneg _)
          have h2 : (max R 0 + 1) * ‖a10‖ < (max R 0 + 1) * (c / R') := mul_lt_mul_of_pos_left h6 (by positivity)
          have h3 : (max R 0 + 1) * (c / R') = c := by
            rw [hR', ← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity : (max R 0 + 1 : ℝ) ≠ 0)]
          linarith
        have hΦ0 : ∀ (b d : F), Φ ![a11 / a10, b, d] = 0 := by
          intro b d
          by_contra hne
          have hle := hR _ hne
          simp only [Matrix.cons_val_zero] at hle
          exact absurd hle (not_le.mpr hbig)
        rw [hΦ0, mul_zero]
    ·
      have hq0 : ((Matrix.GeneralLinearGroup.det g₀ : Fˣ) : F) * (Matrix.of fun i j => (X₀ * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2).det / ((((g₀ : G₂) : M2) * (X₀ * (T : Matrix (Fin 3) (Fin 3) F))) 1 0) ≠ 0 :=
        div_ne_zero (mul_ne_zero hdg0 hsdet0) hn0
      have hcq : ContinuousAt (fun y : M23 × G₂ => ((Matrix.GeneralLinearGroup.det y.2 : Fˣ) : F) *
          (Matrix.of fun i j => (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2).det /
          (((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 0) (X₀, g₀) :=
        ((hdg.mul hsdet).continuousAt (x := (X₀, g₀))).div ((hN1 0).continuousAt (x := (X₀, g₀))) hn0
      have e5 : ∀ᶠ y : M23 × G₂ in 𝓝 (X₀, g₀),
          charExt (lam 1) (((Matrix.GeneralLinearGroup.det y.2 : Fˣ) : F) *
            (Matrix.of fun i j => (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2).det /
            (((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 0) =
          charExt (lam 1) (((Matrix.GeneralLinearGroup.det g₀ : Fˣ) : F) * (Matrix.of fun i j => (X₀ * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2).det / ((((g₀ : G₂) : M2) * (X₀ * (T : Matrix (Fin 3) (Fin 3) F))) 1 0)) :=
        hcq.eventually (eventually_charExt_eq p (lam 1) (hlam 1) hq0)
      have e6 : ∀ᶠ y : M23 × G₂ in 𝓝 (X₀, g₀),
          charExt (lam 2) ((((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 0) = charExt (lam 2) ((((g₀ : G₂) : M2) * (X₀ * (T : Matrix (Fin 3) (Fin 3) F))) 1 0) :=
        ((hN1 0).continuousAt (x := (X₀, g₀))).eventually (eventually_charExt_eq p (lam 2) (hlam 2) hn0)
      have e7 : ∀ᶠ y : M23 × G₂ in 𝓝 (X₀, g₀),
          ‖(((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 0‖ = ‖((((g₀ : G₂) : M2) * (X₀ * (T : Matrix (Fin 3) (Fin 3) F))) 1 0)‖ :=
        ((hN1 0).continuousAt (x := (X₀, g₀))).eventually (eventually_norm_eq p hn0)
      have hcv : ContinuousAt (fun y : M23 × G₂ =>
          (![(((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 1 / (((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 0,
            (((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 2 / (((y.2 : G₂) : M2) * (y.1 * (T : Matrix (Fin 3) (Fin 3) F))) 1 0,
            ((y.1 * (T : Matrix (Fin 3) (Fin 3) F)) 0 0 * (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) 1 2 -
              (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) 0 2 * (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) 1 0) /
              (Matrix.of fun i j => (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2).det] : Fin 3 → F))
          (X₀, g₀) := by
        refine (continuous_vec3.continuousAt).comp (ContinuousAt.prodMk ?_ (ContinuousAt.prodMk ?_ ?_))
        · exact ((hN1 1).continuousAt (x := (X₀, g₀))).div ((hN1 0).continuousAt (x := (X₀, g₀))) hn0
        · exact ((hN1 2).continuousAt (x := (X₀, g₀))).div ((hN1 0).continuousAt (x := (X₀, g₀))) hn0
        · exact (hw.continuousAt (x := (X₀, g₀))).div (hsdet.continuousAt (x := (X₀, g₀))) hsdet0
      have e8 := hcv.eventually ((IsLocallyConstant.iff_eventually_eq Φ).1 hΦ.1 _)
      filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8] with y h1 h2 h3 h4 h5 h6 h7 h8
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem hsK', h2, h3, h5, h6, h7, h8]
      simp only [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm, h4]
  ·
    have e0 : ∀ᶠ y : M23 × G₂ in 𝓝 (X₀, g₀),
        (Matrix.of fun i j => (y.1 * (T : Matrix (Fin 3) (Fin 3) F)) i (Fin.castSucc j) : M2) ∉ Units.val '' (K : Set G₂) :=
      (hs.continuousAt (x := (X₀, g₀))).eventually (hK'closed.isOpen_compl.mem_nhds hsK)
    filter_upwards [e0] with y h0
    rw [Set.indicator_of_notMem h0, Set.indicator_of_notMem hsK]
    simp only [mul_zero, zero_mul]

end B1dLC48

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction in

theorem B1dLC.isLocallyConstant_slot
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (T : LocalGL3 p) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
    ∀ (φsec : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (φsec = fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)) =>
        let Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))
        let s : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) := Matrix.of fun i j => Z i (Fin.castSucc j)
        let N : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Z
        ((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
          (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) *
          (Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).indicator (fun _ => (1 : ℂ)) s *
          (charExt (lam 0) s.det)⁻¹ * ((‖s.det‖⁻¹ : ℝ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ) *
          charExt (lam 1) (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * s.det / N 1 0) *
          charExt (lam 2) (N 1 0) * ((‖N 1 0‖⁻¹ : ℝ) : ℂ) *
          Φ ![N 1 1 / N 1 0, N 1 2 / N 1 0, (Z 0 0 * Z 1 2 - Z 0 2 * Z 1 0) / s.det]) →
    (∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      φsec X (upperUnipotent2 p x * g) = φsec X g) →
    (∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (a : Fin 2 → (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      φsec X (diagonal2 p a * g) = torusChar2 p ![lam 1, lam 2] a * halfModulus2 p a * φsec X g) →
    IsLocallyConstant (fun P : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) => φsec P.1 P.2) ∧
    IsLocallyConstant φsec := by
  intro μ₂ _ K hKo hKc φsec hφ hN hT
  have hA := B1dLC48.jointA (p := p) lam hlam Φ hΦ T μ₂ K hKo hKc φsec hφ
  exact ⟨hA, B1dLC48.uniform_of_joint (p := p) ![lam 1, lam 2] φsec hA hN hT⟩

end

open B1djf in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (T : LocalGL3 p) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) := borel _
    ∃ (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) (R : ℝ), IsOpen U ∧ (1 : GL (Fin 2) (p.adicCompletion ℚ)) ∈ U ∧
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
    ∀ (φsec : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (φsec = fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)) =>
        let Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))
        let s : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) := Matrix.of fun i j => Z i (Fin.castSucc j)
        let N : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Z
        ((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
          (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) *
          (Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).indicator (fun _ => (1 : ℂ)) s *
          (charExt (lam 0) s.det)⁻¹ * ((‖s.det‖⁻¹ : ℝ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ) *
          charExt (lam 1) (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * s.det / N 1 0) *
          charExt (lam 2) (N 1 0) * ((‖N 1 0‖⁻¹ : ℝ) : ℂ) *
          Φ ![N 1 1 / N 1 0, N 1 2 / N 1 0, (Z 0 0 * Z 1 2 - Z 0 2 * Z 1 0) / s.det]) →

    Measurable (fun P : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) => φsec P.1 P.2) ∧
    IsLocallyConstant φsec ∧ HasCompactSupport φsec ∧
    (∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), φsec X g ≠ 0 →
      (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j)) ∈ Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))) ∧

    (∀ X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ),
      φsec X ∈ principalSeries2 p ![lam 1, lam 2] ∧
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φsec X g ≠ 0 →
        ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 0 ≠ 0 ∧
        ‖((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 1‖ ≤ R * ‖((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 0‖) ∧

    ((K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ⊆ U →
      ∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), φsec X g ≠ 0 →
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ≠ 0 ∧ ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ≤ R * ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖) := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI : MeasurableSpace (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) := borel _
  haveI : BorelSpace (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) := ⟨rfl⟩
  classical

  obtain ⟨R₀, hR₀⟩ := hΦ.2.isCompact.isBounded.exists_norm_le
  set R : ℝ := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRΦ : ∀ y : Fin 3 → p.adicCompletion ℚ, Φ y ≠ 0 → ∀ i, ‖y i‖ ≤ R := by
    intro y hy i
    exact (norm_le_pi_norm y i).trans ((hR₀ y (subset_tsupport Φ hy)).trans (le_max_left _ _))

  set δ : ℝ := 1 / (2 * R) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one (by positivity)]; linarith
  have hRδ : R * δ < 1 := by
    rw [hδ]; field_simp; linarith
  set U : Set (GL (Fin 2) (p.adicCompletion ℚ)) :=
    {s | ‖(s : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 - 1‖ < δ ∧
      ‖(s : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1‖ < δ ∧
      ‖(s : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖ < δ ∧
      ‖(s : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 - 1‖ < δ} with hU
  have hUo : IsOpen U := by
    have hc : ∀ i j : Fin 2, Continuous fun s : GL (Fin 2) (p.adicCompletion ℚ) =>
        (s : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j := fun i j => Units.continuous_val.matrix_elem i j
    rw [hU]
    refine ((isOpen_lt ((hc 0 0).sub continuous_const).norm continuous_const).inter
      ((isOpen_lt (hc 0 1).norm continuous_const).inter
      ((isOpen_lt (hc 1 0).norm continuous_const).inter
      (isOpen_lt ((hc 1 1).sub continuous_const).norm continuous_const))))
  have hU1 : (1 : GL (Fin 2) (p.adicCompletion ℚ)) ∈ U := by
    rw [hU]
    simp only [Set.mem_setOf_eq, Units.val_one, Matrix.one_apply_eq, sub_self, norm_zero, ne_eq,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
    exact ⟨hδpos, hδpos, hδpos, hδpos⟩
  refine ⟨U, R, hUo, hU1, ?_⟩
  intro μ₂ _ K hKo hKc φsec hφ

  set Kset : Set (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
    Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) with hKset
  set c₀ : ℂ := ((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
    (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
      ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) with hc₀
  have hφs : ∀ X g, φsec X g = slot p lam Φ T c₀ Kset X g := by
    intro X g; rw [hφ]; rfl
  have hφs' : φsec = slot p lam Φ T c₀ Kset := by
    funext X g; exact hφs X g
  have hKc' : IsCompact Kset := hKc.image Units.continuous_val
  have hKdet : ∀ s ∈ Kset, s.det ≠ 0 := by
    rintro s ⟨k, -, rfl⟩
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det k).ne_zero

  have hN : ∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      φsec X (upperUnipotent2 p x * g) = φsec X g := by
    intro X x g; rw [hφs, hφs]; exact slot_upperUnipotent2_mul p lam Φ T c₀ Kset X x g
  have hT : ∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (a : Fin 2 → (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      φsec X (diagonal2 p a * g) = torusChar2 p ![lam 1, lam 2] a * halfModulus2 p a * φsec X g := by
    intro X a g; rw [hφs, hφs]; exact slot_diagonal2_mul p lam Φ T c₀ Kset X a g

  obtain ⟨hjoint, hlcX⟩ := B1dLC.isLocallyConstant_slot p lam hlam Φ hΦ T μ₂ K hKo hKc φsec hφ hN hT

  have hNk : ∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)) (k : Fin 2),
      ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
        (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 k =
        Nf p T X g 1 (Fin.castSucc k) := fun X g k => mul_leftBlock_apply p _ _ k
  haveI := B1djf_secondCountable p
  refine ⟨?_, hlcX, ?_, ?_, ?_, ?_⟩
  · exact hjoint.continuous.measurable
  · rw [hφs']; exact hasCompactSupport_slot p lam Φ T c₀ Kset hKc' hKdet R hRΦ
  · intro X g h
    rw [hφs] at h
    exact (of_slot_ne_zero p lam Φ T c₀ Kset R hRΦ X g h).1
  · intro X
    refine ⟨?_, fun g h => ?_⟩
    · rw [mem_principalSeries2_iff]
      refine ⟨?_, hN X, hT X⟩
      exact hjoint.comp_continuous (continuous_const.prodMk continuous_id)
    · rw [hφs] at h
      obtain ⟨-, hN0, h11, -, -⟩ := of_slot_ne_zero p lam Φ T c₀ Kset R hRΦ X g h
      rw [hNk X g 0, hNk X g 1]
      exact ⟨hN0, h11⟩
  · intro hKU X g h
    rw [hφs] at h
    obtain ⟨hKs, hN0, h11, -, -⟩ := of_slot_ne_zero p lam Φ T c₀ Kset R hRΦ X g h
    obtain ⟨k, hk, hks⟩ := hKs
    have hkU := hKU hk
    simp only [hU, Set.mem_setOf_eq] at hkU
    obtain ⟨h00, h01, h10, h11'⟩ := hkU
    have e0 := hNk X g 0
    have e1 := hNk X g 1
    refine bottom_row_of_mul p hR1 hδ1 hRδ g (sf p T X) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [show sf p T X = (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) from hks.symm]; exact h00
    · rw [show sf p T X = (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) from hks.symm]; exact h01
    · rw [show sf p T X = (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) from hks.symm]; exact h10
    · rw [show sf p T X = (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) from hks.symm]; exact h11'
    · show ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * sf p T X) 1 0 ≠ 0
      rw [show sf p T X = (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j)) from rfl,
        e0]; exact hN0
    · show ‖((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * sf p T X) 1 1‖ ≤ R * ‖((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * sf p T X) 1 0‖
      rw [show sf p T X = (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j)) from rfl,
        e0, e1]; exact h11

end S_LanglandsTunnell_CubicInduction_godementDatum_mem_principalSeries2_and_support
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_godementDatum_mem_principalSeries2_and_support (solution)
