-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5a5a20a2-ef60-50ca-b79b-e0f08c62d82c

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

import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_polynomial_forall_diagZ_mul_eq_zero_and_sum_coeff_mul_eq_zero_of_admissible
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_Polynomial_exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

open scoped ENNReal NNReal

noncomputable section

section KBblock
open IsDedekindDomain NumberField
open scoped WithZero Pointwise

namespace KBKD

section Valuation

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem exists_uniformizer :
    ∃ ϖ : v.adicCompletion K, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K v
  exact ⟨((WithVal.equiv (HeightOneSpectrum.valuation K v)).symm π : v.adicCompletion K),
    by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ⟩

variable {K v}

theorem uniformizer_ne_zero {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    ϖ ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm

theorem v_uniformizer_zpow {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (j : ℤ) : Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem v_uniformizer_pow {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (n : ℕ) : Valued.v (ϖ ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [← zpow_natCast, v_uniformizer_zpow hϖ]

theorem v_add_le {x y : v.adicCompletion K} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x + y) ≤ γ :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

theorem v_sub_le {x y : v.adicCompletion K} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x - y) ≤ γ := by
  rw [sub_eq_add_neg]; exact v_add_le hx (by rwa [Valuation.map_neg])

theorem v_mul_le {x y : v.adicCompletion K} {a b : ℤ} (hx : Valued.v x ≤ WithZero.exp a)
    (hy : Valued.v y ≤ WithZero.exp b) : Valued.v (x * y) ≤ WithZero.exp (a + b) := by
  rw [Valuation.map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

theorem exp_neg_succ_lt_one (n : ℕ) : WithZero.exp (-((n : ℤ) + 1)) < (1 : ℤᵐ⁰) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem exp_neg_succ_le_one (n : ℕ) : WithZero.exp (-((n : ℤ) + 1)) ≤ (1 : ℤᵐ⁰) :=
  (exp_neg_succ_lt_one n).le

theorem exp_antitone_succ (n : ℕ) :
    WithZero.exp (-(((n + 1 : ℕ) : ℤ) + 1)) ≤ WithZero.exp (-((n : ℤ) + 1)) := by
  rw [WithZero.exp_le_exp]; push_cast; omega

theorem v_lt_one_iff (x : v.adicCompletion K) :
    Valued.v x < 1 ↔ Valued.v x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hx : Valued.v x = 0
  · simp [hx]
  · rw [← WithZero.exp_log hx, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem eq_zero_of_forall_v_le (x : v.adicCompletion K)
    (h : ∀ n : ℕ, Valued.v x ≤ WithZero.exp (-((n : ℤ) + 1))) : x = 0 := by
  by_contra hx
  have hx' : Valued.v x ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  set L := WithZero.log (Valued.v x) with hL
  have hxL : Valued.v x = WithZero.exp L := (WithZero.exp_log hx').symm
  have := h ((-L).toNat)
  rw [hxL, WithZero.exp_le_exp] at this
  omega

theorem v_eq_one_of_sub_one {x : v.adicCompletion K} {n : ℕ}
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) : Valued.v x = 1 := by
  have : x = 1 + (x - 1) := by ring
  rw [this]
  exact Valuation.map_one_add_of_lt _ (hx.trans_lt (exp_neg_succ_lt_one n))

theorem ne_zero_of_v_eq_one {x : v.adicCompletion K} (hx : Valued.v x = 1) : x ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx

theorem v_inv_sub_one {x : v.adicCompletion K} {n : ℕ}
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) :
    Valued.v (x⁻¹ - 1) ≤ WithZero.exp (-((n : ℤ) + 1)) := by
  have h1 := v_eq_one_of_sub_one hx
  have hx0 := ne_zero_of_v_eq_one h1
  have : x⁻¹ - 1 = x⁻¹ * (-(x - 1)) := by field_simp; ring
  rw [this, Valuation.map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, one_mul]
  exact hx

theorem isOpen_ball (m : ℤ) : IsOpen {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer K v
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖ
  have hset : {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ m * x) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_uniformizer_zpow hϖ,
      WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m :=
            mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp m * ((WithZero.exp m)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp m * 1 := mul_le_mul_right h _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

theorem exists_eq_zpow_mul (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (y : v.adicCompletion K) (hy : y ≠ 0) :
    ∃ (j : ℤ) (t : v.adicCompletion K), Valued.v t = 1 ∧ y = ϖ ^ j * t ∧
      Valued.v y = WithZero.exp (-j) := by
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖ
  have hy' : Valued.v y ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  set L := WithZero.log (Valued.v y) with hL
  have hyL : Valued.v y = WithZero.exp L := (WithZero.exp_log hy').symm
  refine ⟨-L, ϖ ^ L * y, ?_, ?_, ?_⟩
  · rw [Valuation.map_mul, v_uniformizer_zpow hϖ, hyL, ← WithZero.exp_add, neg_add_cancel,
      WithZero.exp_zero]
  · rw [zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hϖ0), one_mul]
  · rw [neg_neg, hyL]

end Valuation

section GLtwo

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

def gl2 (a b c d : F) (h : a * d - b * c ≠ 0) : G :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by rwa [Matrix.det_fin_two_of])

@[scoped simp] theorem gl2_coe (a b c d : F) (h : a * d - b * c ≠ 0) :
    ((gl2 a b c d h : G) : Mat) = !![a, b; c, d] := rfl

theorem unipotent_coe (x : F) :
    ((UnramifiedWhittaker.unipotent x : G) : Mat) = !![1, x; 0, 1] := rfl

theorem diagOne_coe (a : Fˣ) :
    ((AdelicLevel.diagOne a : G) : Mat) = !![(a : F), 0; 0, 1] := by
  ext i j
  rw [AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem gl_eq_of_entries {g h : G}
    (h00 : (g : Mat) 0 0 = (h : Mat) 0 0) (h01 : (g : Mat) 0 1 = (h : Mat) 0 1)
    (h10 : (g : Mat) 1 0 = (h : Mat) 1 0) (h11 : (g : Mat) 1 1 = (h : Mat) 1 1) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem mul_coe_apply (g h : G) (i j : Fin 2) :
    ((g * h : G) : Mat) i j = (g : Mat) i 0 * (h : Mat) 0 j + (g : Mat) i 1 * (h : Mat) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_mul (x y : F) :
    (UnramifiedWhittaker.unipotent x : G) * UnramifiedWhittaker.unipotent y =
      UnramifiedWhittaker.unipotent (x + y) := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe] <;> ring

theorem unipotent_zero : (UnramifiedWhittaker.unipotent (0 : F) : G) = 1 := by
  apply gl_eq_of_entries <;> simp [unipotent_coe]

theorem diagOne_mul_unipotent (a : Fˣ) (x : F) :
    (AdelicLevel.diagOne a : G) * UnramifiedWhittaker.unipotent x =
      UnramifiedWhittaker.unipotent ((a : F) * x) * AdelicLevel.diagOne a := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe, diagOne_coe]

theorem diag_mul_unipotent (t₁ t₂ : F) (h : t₁ * t₂ - 0 * 0 ≠ 0) (x : F) :
    gl2 t₁ 0 0 t₂ h * UnramifiedWhittaker.unipotent x =
      UnramifiedWhittaker.unipotent (t₁ * x * t₂⁻¹) * gl2 t₁ 0 0 t₂ h := by
  have ht₂ : t₂ ≠ 0 := by intro h'; apply h; simp [h']
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe] ; field_simp

theorem iwahori_factor (k : G) (hα : (k : Mat) 0 0 ≠ 0) :
    ∃ (hL : (1 : F) * 1 - 0 * ((k : Mat) 1 0 / (k : Mat) 0 0) ≠ 0)
      (hD : (k : Mat) 0 0 * ((k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0 / (k : Mat) 0 0) - 0 * 0 ≠ 0),
      k = gl2 1 0 ((k : Mat) 1 0 / (k : Mat) 0 0) 1 hL *
        gl2 ((k : Mat) 0 0) 0 0 ((k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0 / (k : Mat) 0 0) hD *
        UnramifiedWhittaker.unipotent ((k : Mat) 0 1 / (k : Mat) 0 0) := by
  have hdet : (k : Mat).det ≠ 0 := (Matrix.GeneralLinearGroup.det_ne_zero k)
  rw [Matrix.det_fin_two] at hdet
  have hL : (1 : F) * 1 - 0 * ((k : Mat) 1 0 / (k : Mat) 0 0) ≠ 0 := by simp
  have hD : (k : Mat) 0 0 * ((k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0 / (k : Mat) 0 0) - 0 * 0 ≠ 0 := by
    have : (k : Mat) 0 0 * ((k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0 / (k : Mat) 0 0) - 0 * 0 =
        (k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0 := by field_simp; ring
    rw [this]; exact hdet
  refine ⟨hL, hD, ?_⟩
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe] <;> field_simp <;> ring

theorem lower_mul_unipotent (c w : F) (hcw : 1 + c * w ≠ 0)
    (hL : (1 : F) * 1 - 0 * c ≠ 0)
    (hk : (1 - w / (1 + c * w) * c) * (1 + c * w) - 0 * c ≠ 0) :
    gl2 1 0 c 1 hL * UnramifiedWhittaker.unipotent w =
      UnramifiedWhittaker.unipotent (w / (1 + c * w)) *
        gl2 (1 - w / (1 + c * w) * c) 0 c (1 + c * w) hk := by
  have hcw' : 1 + w * c ≠ 0 := by rwa [mul_comm w c]
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe] <;> field_simp <;> ring

def lvl (n : ℕ) : ℤᵐ⁰ := WithZero.exp (-((n : ℤ) + 1))

theorem lvl_le_one (n : ℕ) : lvl n ≤ 1 := exp_neg_succ_le_one n

theorem lvl_lt_one (n : ℕ) : lvl n < 1 := exp_neg_succ_lt_one n

theorem lvl_succ_le (n : ℕ) : lvl (n + 1) ≤ lvl n := exp_antitone_succ n

theorem v_mul_le_lvl_left {n : ℕ} {x y : F} (hx : Valued.v x ≤ lvl n) (hy : Valued.v y ≤ 1) :
    Valued.v (x * y) ≤ lvl n := by
  rw [Valuation.map_mul]; simpa using mul_le_mul' hx hy

theorem v_mul_le_lvl_right {n : ℕ} {x y : F} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ lvl n) :
    Valued.v (x * y) ≤ lvl n := by
  rw [Valuation.map_mul]; simpa using mul_le_mul' hx hy

theorem v_le_one_of_sub_one_le {n : ℕ} {x : F} (hx : Valued.v (x - 1) ≤ lvl n) : Valued.v x ≤ 1 := by
  have : x = (x - 1) + 1 := by ring
  rw [this]; exact v_add_le (hx.trans (lvl_le_one n)) (by simp)

structure IsCong (n : ℕ) (m : Mat) : Prop where
  h00 : Valued.v (m 0 0 - 1) ≤ lvl n
  h01 : Valued.v (m 0 1) ≤ lvl n
  h10 : Valued.v (m 1 0) ≤ lvl n
  h11 : Valued.v (m 1 1 - 1) ≤ lvl n

theorem IsCong.v00 {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v (m 0 0) = 1 := v_eq_one_of_sub_one h.h00
theorem IsCong.v11 {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v (m 1 1) = 1 := v_eq_one_of_sub_one h.h11

theorem IsCong.integral {n : ℕ} {m : Mat} (h : IsCong n m) (i j : Fin 2) : Valued.v (m i j) ≤ 1 := by
  fin_cases i <;> fin_cases j
  · exact h.v00.le
  · exact h.h01.trans (lvl_le_one n)
  · exact h.h10.trans (lvl_le_one n)
  · exact h.v11.le

theorem isCong_one (n : ℕ) : IsCong n (1 : Mat) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem IsCong.mul {n : ℕ} {a b : Mat} (ha : IsCong n a) (hb : IsCong n b) : IsCong n (a * b) := by
  have e00 : (a * b) 0 0 - 1 = (a 0 0 - 1) * b 0 0 + (b 0 0 - 1) + a 0 1 * b 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e01 : (a * b) 0 1 = a 0 0 * b 0 1 + a 0 1 * b 1 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (a * b) 1 0 = a 1 0 * b 0 0 + a 1 1 * b 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (a * b) 1 1 - 1 = a 1 0 * b 0 1 + ((a 1 1 - 1) * b 1 1 + (b 1 1 - 1)) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00]
    exact v_add_le (v_add_le (v_mul_le_lvl_left ha.h00 hb.v00.le) hb.h00)
      (v_mul_le_lvl_left ha.h01 (hb.integral 1 0))
  · rw [e01]
    exact v_add_le (v_mul_le_lvl_right ha.v00.le hb.h01) (v_mul_le_lvl_left ha.h01 hb.v11.le)
  · rw [e10]
    exact v_add_le (v_mul_le_lvl_left ha.h10 hb.v00.le) (v_mul_le_lvl_right ha.v11.le hb.h10)
  · rw [e11]
    exact v_add_le (v_mul_le_lvl_left ha.h10 (hb.integral 0 1))
      (v_add_le (v_mul_le_lvl_left ha.h11 hb.v11.le) hb.h11)

theorem IsCong.v_det_sub_one {n : ℕ} {m : Mat} (h : IsCong n m) :
    Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0 - 1) ≤ lvl n := by
  have : m 0 0 * m 1 1 - m 0 1 * m 1 0 - 1 = (m 0 0 - 1) * m 1 1 + (m 1 1 - 1) - m 0 1 * m 1 0 := by ring
  rw [this]
  exact v_sub_le (v_add_le (v_mul_le_lvl_left h.h00 h.v11.le) h.h11) (v_mul_le_lvl_left h.h01 (h.integral 1 0))

theorem IsCong.v_det {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0) = 1 :=
  v_eq_one_of_sub_one h.v_det_sub_one

theorem IsCong.inv {n : ℕ} {g : G} (h : IsCong n (g : Mat)) : IsCong n ((g⁻¹ : G) : Mat) := by
  set D : F := (g : Mat) 0 0 * (g : Mat) 1 1 - (g : Mat) 0 1 * (g : Mat) 1 0 with hD
  have hvD : Valued.v D = 1 := h.v_det
  have hD0 : D ≠ 0 := ne_zero_of_v_eq_one hvD
  set B : Mat := !![(g : Mat) 1 1 / D, -(g : Mat) 0 1 / D; -(g : Mat) 1 0 / D, (g : Mat) 0 0 / D] with hB
  have hmul : (g : Mat) * B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  have hinv : ((g⁻¹ : G) : Mat) = B := by
    rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv hmul]
  have hvdiv : ∀ x : F, Valued.v (x / D) = Valued.v x := by
    intro x; rw [map_div₀, hvD, div_one]
  rw [hinv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : B 0 0 - 1 = ((g : Mat) 1 1 - 1 - (D - 1)) / D := by
      simp only [B, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
      field_simp; ring
    rw [this, hvdiv]
    exact v_sub_le h.h11 h.v_det_sub_one
  · have : B 0 1 = -(g : Mat) 0 1 / D := by simp [B]
    rw [this, hvdiv, Valuation.map_neg]; exact h.h01
  · have : B 1 0 = -(g : Mat) 1 0 / D := by simp [B]
    rw [this, hvdiv, Valuation.map_neg]; exact h.h10
  · have : B 1 1 - 1 = ((g : Mat) 0 0 - 1 - (D - 1)) / D := by
      simp only [B, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp; ring
    rw [this, hvdiv]
    exact v_sub_le h.h00 h.v_det_sub_one

variable (K v) in

def congr (n : ℕ) : Subgroup G where
  carrier := {g | IsCong n (g : Mat)}
  one_mem' := by simpa using isCong_one n
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Matrix.GeneralLinearGroup.coe_mul] at *
    exact ha.mul hb
  inv_mem' := by
    intro g hg
    exact hg.inv

theorem mem_congr {n : ℕ} {g : G} : g ∈ congr K v n ↔ IsCong n (g : Mat) := Iff.rfl

theorem congr_antitone (n : ℕ) : congr K v (n + 1) ≤ congr K v n := by
  intro g hg
  exact ⟨hg.h00.trans (lvl_succ_le n), hg.h01.trans (lvl_succ_le n), hg.h10.trans (lvl_succ_le n),
    hg.h11.trans (lvl_succ_le n)⟩

theorem congr_antitone' {m n : ℕ} (h : m ≤ n) : congr K v n ≤ congr K v m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (congr_antitone _).trans ih

theorem isOpen_congr (n : ℕ) : IsOpen (congr K v n : Set G) := by
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have hball : IsOpen {x : F | Valued.v x ≤ lvl n} := isOpen_ball _
  have hball' : IsOpen {x : F | Valued.v (x - 1) ≤ lvl n} :=
    hball.preimage (continuous_id.sub continuous_const)
  have hset : (congr K v n : Set G) =
      ((fun g : G => (g : Mat) 0 0) ⁻¹' {x : F | Valued.v (x - 1) ≤ lvl n}) ∩
      ((fun g : G => (g : Mat) 0 1) ⁻¹' {x : F | Valued.v x ≤ lvl n}) ∩
      ((fun g : G => (g : Mat) 1 0) ⁻¹' {x : F | Valued.v x ≤ lvl n}) ∩
      ((fun g : G => (g : Mat) 1 1) ⁻¹' {x : F | Valued.v (x - 1) ≤ lvl n}) := by
    ext g
    simp only [SetLike.mem_coe, mem_congr, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨⟨⟨h.h00, h.h01⟩, h.h10⟩, h.h11⟩, fun h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩⟩
  rw [hset]
  exact (((hball'.preimage (hc 0 0)).inter (hball.preimage (hc 0 1))).inter
    (hball.preimage (hc 1 0))).inter (hball'.preimage (hc 1 1))

theorem congr_subset_localIntegralSet (n : ℕ) :
    (congr K v n : Set G) ⊆ AutomorphicForm.localIntegralSet K v := by
  intro g hg
  rw [AutomorphicForm.mem_localIntegralSet]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact (mem_congr.mp hg).integral i j
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact (mem_congr.mp ((congr K v n).inv_mem hg)).integral i j

theorem isCompact_congr (n : ℕ) : IsCompact (congr K v n : Set G) :=
  (AutomorphicForm.isCompact_localIntegralSet K v).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_congr n)) (congr_subset_localIntegralSet n)

theorem eq_one_of_forall_mem_congr {g : G} (hg : ∀ n, g ∈ congr K v n) : g = 1 := by
  have h00 : (g : Mat) 0 0 - 1 = 0 := eq_zero_of_forall_v_le _ fun n => (hg n).h00
  have h01 : (g : Mat) 0 1 = 0 := eq_zero_of_forall_v_le _ fun n => (hg n).h01
  have h10 : (g : Mat) 1 0 = 0 := eq_zero_of_forall_v_le _ fun n => (hg n).h10
  have h11 : (g : Mat) 1 1 - 1 = 0 := eq_zero_of_forall_v_le _ fun n => (hg n).h11
  apply gl_eq_of_entries
  · simpa [sub_eq_zero] using h00
  · simpa using h01
  · simpa using h10
  · simpa [sub_eq_zero] using h11

theorem exists_congr_subset {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    ∃ n, (congr K v n : Set G) ⊆ U := by
  have hdir : Directed (fun x1 x2 : Set G => x1 ⊇ x2) fun n : ℕ => (congr K v n : Set G) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · exact fun g hg => congr_antitone' (le_max_left i j) hg
    · exact fun g hg => congr_antitone' (le_max_right i j) hg
  refine exists_subset_nhds_of_isCompact' hdir (fun n => isCompact_congr n)
    (fun n => Subgroup.isClosed_of_isOpen _ (isOpen_congr n)) ?_
  intro x hx
  rw [Set.mem_iInter] at hx
  have : x = 1 := eq_one_of_forall_mem_congr hx
  subst this
  exact hU.mem_nhds h1

end GLtwo

end KBKD
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible.KBKD"

end KBblock
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible.KBKD"

namespace SSKD

section Generic

variable {G : Type*} [Group G]

theorem translate_mem_span (f : G → ℂ) (h : G) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    (fun g : G => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      exact Submodule.subset_span ⟨h * h', funext fun g => by simp only [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add W₁ W₂ _ _ h₁ h₂ =>
      have : (fun g : G => (W₁ + W₂) (g * h)) = (fun g : G => W₁ (g * h)) + fun g : G => W₂ (g * h) := rfl
      rw [this]; exact Submodule.add_mem _ h₁ h₂
  | smul a W _ h₁ =>
      have : (fun g : G => (a • W) (g * h)) = a • fun g : G => W (g * h) := rfl
      rw [this]; exact Submodule.smul_mem _ a h₁

theorem span_le_span_of_mem (f W₀ : G → ℂ)
    (h₀ : f ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h'))) :
    Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) ≤
      Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h')) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, rfl⟩
  exact translate_mem_span W₀ h h₀

theorem law_of_mem_span (f : G → ℂ) (a : G) (χ : ℂ) (hf : ∀ g : G, f (a * g) = χ * f g) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    ∀ g : G, W (a * g) = χ * W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      intro g
      show f (a * g * h') = χ * f (g * h')
      rw [mul_assoc, hf]
  | zero => intro g; simp
  | add W₁ W₂ _ _ h₁ h₂ => intro g; simp only [Pi.add_apply, h₁ g, h₂ g]; ring
  | smul c W _ h₁ => intro g; simp only [Pi.smul_apply, smul_eq_mul, h₁ g]; ring

variable [TopologicalSpace G] [ContinuousMul G]

theorem exists_open_stabilizer_of_mem_span (f : G → ℂ) (K : Subgroup G) (hK : IsOpen (K : Set G))
    (hf : ∀ k ∈ K, ∀ g : G, f (g * k) = f g) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h, rfl⟩ := hWm
      refine ⟨K.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
      · have hc : Continuous fun k : G => h⁻¹ * k * h⁻¹⁻¹ :=
          (continuous_const.mul continuous_id).mul continuous_const
        have hset : ((K.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup G) : Set G) =
            (fun k : G => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (K : Set G) := by
          ext k
          simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            SetLike.mem_coe]
        rw [hset]
        exact hK.preimage hc
      · intro k hk g
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hk
        show f (g * k * h) = f (g * h)
        rw [show g * k * h = g * h * (h⁻¹ * k * h) by simp only [mul_assoc, mul_inv_cancel_left]]
        exact hf _ hk (g * h)
  | zero => exact ⟨⊤, by simp, fun _ _ _ => rfl⟩
  | add W₁ W₂ _ _ h₁ h₂ =>
      obtain ⟨U₁, hU₁, hW₁⟩ := h₁
      obtain ⟨U₂, hU₂, hW₂⟩ := h₂
      refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
      · intro k hk g
        rw [Subgroup.mem_inf] at hk
        simp only [Pi.add_apply, hW₁ k hk.1 g, hW₂ k hk.2 g]
  | smul c W _ h₁ =>
      obtain ⟨U, hU, hWU⟩ := h₁
      exact ⟨U, hU, fun k hk g => by simp only [Pi.smul_apply, hWU k hk g]⟩

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible.KBKD"

end SSKD
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible.KBKD"

namespace WBGauge

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

theorem scalar2_coe (u : (F)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : G2) : Matrix (Fin 2) (Fin 2) F) = !![(u : F), 0; 0, (u : F)] := by
  show Matrix.scalar (Fin 2) (u : F) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar]

theorem diagUnits2_eq_scalar_mul (a₁ a₂ : (F)ˣ) :
    (diagUnits2 a₁ a₂ : G2) = Matrix.GeneralLinearGroup.scalar (Fin 2) a₂ * diagUnits2 (a₁ * a₂⁻¹) 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_diagUnits2, coe_diagUnits2, scalar2_coe, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
  have h : (a₂ : F) ≠ 0 := a₂.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem diagUnits2_mul_one (x y : (F)ˣ) :
    (diagUnits2 (x * y) 1 : G2) = diagUnits2 x 1 * diagUnits2 y 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_diagUnits2, coe_diagUnits2, coe_diagUnits2, Units.val_mul, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnits2_zpow_eq_diagZ (π : (F)ˣ) (m : ℤ) :
    (diagUnits2 (π ^ m) 1 : G2) = diagZ (π : F) π.ne_zero m := by
  apply Units.ext
  rw [coe_diagUnits2, Units.val_zpow_eq_zpow_val, Units.val_one]
  rfl

theorem scalar_mul_comm (z : (F)ˣ) (g : G2) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, scalar2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem diagUnits2_unit_inv (u : (F)ˣ) : ((diagUnits2 u 1 : G2)⁻¹ : G2) = diagUnits2 u⁻¹ 1 := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← diagUnits2_mul_one, inv_mul_cancel]
  apply Units.ext
  rw [coe_diagUnits2, Units.val_one, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagUnits2_unit_mem (u : (F)ˣ) (hu : Valued.v (u : F) = 1) :
    (diagUnits2 u 1 : G2) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have key : ∀ w : (F)ˣ, Valued.v (w : F) = 1 →
      AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ ((diagUnits2 w 1 : G2) : Matrix (Fin 2) (Fin 2) F) := by
    intro w hw
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, coe_diagUnits2]
      fin_cases i <;> fin_cases j <;> simp [hw]
    · rw [NumberField.AdelicLevel.idealBound_top, coe_diagUnits2]; simp
    · rw [NumberField.AdelicLevel.idealBound_top, coe_diagUnits2]; simp
  rw [AdelicDock.mem_localLevelOne_iff, diagUnits2_unit_inv]
  refine ⟨key u hu, key u⁻¹ ?_⟩
  rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

theorem exists_eq_zpow_mul_unit (π : (F)ˣ) (hπ : Valued.v (π : F) = WithZero.exp (-1 : ℤ)) (y : (F)ˣ) :
    ∃ (m : ℤ) (u : (F)ˣ), Valued.v (u : F) = 1 ∧ y = π ^ m * u := by
  have hvy : Valued.v (y : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  set m : ℤ := -WithZero.log (Valued.v (y : F)) with hm
  have hvπm : Valued.v (((π ^ m : (F)ˣ)) : F) = Valued.v (y : F) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, hm, neg_neg,
      WithZero.exp_log hvy]
  refine ⟨m, (π ^ m)⁻¹ * y, ?_, (mul_inv_cancel_left (π ^ m) y).symm⟩
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvπm, inv_mul_cancel₀ hvy]

theorem v_zpow_mul_unit (π : (F)ˣ) (hπ : Valued.v (π : F) = WithZero.exp (-1 : ℤ)) (m : ℤ) (u : (F)ˣ)
    (hu : Valued.v (u : F) = 1) : Valued.v (((π ^ m * u : (F)ˣ)) : F) = WithZero.exp (-m) := by
  rw [Units.val_mul, map_mul, hu, mul_one, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul,
    mul_neg, mul_one]

def qR : ℝ := ((Ideal.absNorm p.asIdeal : NNReal) : ℝ)

theorem one_lt_qR : 1 < qR p := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
  unfold qR; exact_mod_cast this

theorem norm_eq_qR_zpow (y : F) (j : ℤ) (hy : Valued.v y = WithZero.exp (-j)) : ‖y‖ = qR p ^ (-j) := by
  rw [NumberField.FinitePlace.norm_def, hy, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, NNReal.coe_zpow]
  unfold qR
  congr 1

theorem norm_eq_one_of_v (u : F) (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  have := norm_eq_qR_zpow p u 0 (by rw [hu, neg_zero, WithZero.exp_zero])
  rw [this, neg_zero, zpow_zero]

theorem isCompact_units_sphere : IsCompact {u : (F)ˣ | Valued.v (u : F) = 1} := by
  have hO : IsCompact ((p.adicCompletionIntegers ℚ : Set F)) := by
    rw [← LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
    exact (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ p).isCompact
  have hS : IsCompact {x : F | Valued.v x = 1} := by
    refine hO.of_isClosed_subset ?_ (fun x hx => by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]; exact le_of_eq hx)
    have ho : IsOpen {x : F | Valued.v x = 1}ᶜ := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hx
      by_cases hx0 : (Valued.v x : WithZero (Multiplicative ℤ)) = 0
      · have h0 : x = 0 := (Valuation.zero_iff _).1 hx0
        subst h0
        have hball : {y : F | Valued.v y ≤ WithZero.exp (-1 : ℤ)} ∈ nhds (0 : F) :=
          (KBKD.isOpen_ball (K := ℚ) (v := p) (-1)).mem_nhds (by simp)
        refine Filter.mem_of_superset hball fun y hy => ?_
        rw [Set.mem_compl_iff, Set.mem_setOf_eq]
        intro h1
        rw [Set.mem_setOf_eq, h1, ← WithZero.exp_zero, WithZero.exp_le_exp] at hy
        omega
      · have h := Valued.locally_const hx0
        refine Filter.mem_of_superset h fun y hy => ?_
        rw [Set.mem_compl_iff, Set.mem_setOf_eq]
        rw [Set.mem_setOf_eq] at hy
        rw [hy]; exact hx
    exact ⟨ho⟩
  have himage : (Units.val : (F)ˣ → F) '' {u : (F)ˣ | Valued.v (u : F) = 1} = {x : F | Valued.v x = 1} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx0 : x ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [(Units.isEmbedding_val₀ (G₀ := F)).isCompact_iff, himage]
  exact hS

def prinUnits (n : ℕ) : Subgroup (F)ˣ where
  carrier := {u | Valued.v ((u : F) - 1) ≤ KBKD.lvl n}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have hva : Valued.v (a : F) = 1 := KBKD.v_eq_one_of_sub_one ha
    have e : ((a * b : (F)ˣ) : F) - 1 = (a : F) * ((b : F) - 1) + ((a : F) - 1) := by rw [Units.val_mul]; ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ha)
    rw [Valuation.map_mul, hva, one_mul]; exact hb
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Units.val_inv_eq_inv_val]
    exact KBKD.v_inv_sub_one ha

theorem isOpen_prinUnits (n : ℕ) : IsOpen (prinUnits p n : Set (F)ˣ) := by
  have hset : (prinUnits p n : Set (F)ˣ) = (fun u : (F)ˣ => (u : F) - 1) ⁻¹' {x | Valued.v x ≤ KBKD.lvl n} := rfl
  rw [hset]
  exact (KBKD.isOpen_ball (K := ℚ) (v := p) _).preimage (Units.continuous_val.sub continuous_const)

theorem continuous_of_open_stabilizer' {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (f : G → ℂ) (hF : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, f (g * k) = f g) :
    Continuous f := by
  obtain ⟨U, hU, hinv⟩ := hF
  refine continuous_def.2 fun s _ => ?_
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (U : Set G), ?_, ?_, ⟨1, U.one_mem, mul_one g⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    show f (g * k) ∈ s
    rw [hinv k hk g]; exact hg
  · exact (Homeomorph.mulLeft g).isOpenMap _ hU

theorem norm_char_unit_eq_one (θ : (F)ˣ →* ℂˣ) (n : ℕ)
    (hθ : ∀ z : (F)ˣ, Valued.v ((z : F) - 1) ≤ KBKD.lvl n → θ z = 1)
    (u : (F)ˣ) (hu : Valued.v (u : F) = 1) : ‖((θ u : ℂˣ) : ℂ)‖ = 1 := by

  have hcont : Continuous fun t : (F)ˣ => ((θ t : ℂˣ) : ℂ) := by
    refine continuous_of_open_stabilizer' _ ⟨prinUnits p n, isOpen_prinUnits p n, fun k hk g => ?_⟩
    rw [map_mul, hθ k hk, mul_one]

  obtain ⟨M, hM⟩ := (isCompact_units_sphere p).exists_bound_of_continuousOn hcont.continuousOn

  have hpow : ∀ (w : (F)ˣ), Valued.v (w : F) = 1 → ∀ k : ℕ, ‖((θ w : ℂˣ) : ℂ)‖ ^ k ≤ M := by
    intro w hw k
    have hmem : w ^ k ∈ {u : (F)ˣ | Valued.v (u : F) = 1} := by
      show Valued.v (((w ^ k : (F)ˣ)) : F) = 1
      rw [Units.val_pow_eq_pow_val, map_pow, hw, one_pow]
    have := hM _ hmem
    rwa [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  have hle : ∀ (w : (F)ˣ), Valued.v (w : F) = 1 → ‖((θ w : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro w hw
    by_contra h
    push Not at h
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M h
    exact absurd (hpow w hw k) (not_le.2 hk)
  have h1 := hle u hu
  have h2 := hle u⁻¹ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((θ u : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (θ u).ne_zero
  have h3 : 1 ≤ ‖((θ u : ℂˣ) : ℂ)‖ := by rwa [inv_le_one₀ hpos] at h2
  exact le_antisymm h1 h3

theorem norm_char_zpow_mul_unit (θ : (F)ˣ →* ℂˣ) (n : ℕ)
    (hθ : ∀ z : (F)ˣ, Valued.v ((z : F) - 1) ≤ KBKD.lvl n → θ z = 1)
    (π : (F)ˣ) (m : ℤ) (u : (F)ˣ) (hu : Valued.v (u : F) = 1) :
    ‖((θ (π ^ m * u) : ℂˣ) : ℂ)‖ = ‖((θ π : ℂˣ) : ℂ)‖ ^ m := by
  rw [map_mul, map_zpow, Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow,
    norm_char_unit_eq_one p θ n hθ u hu, mul_one]

theorem zpow_eq_rpow (c : ℝ) (hc : 0 < c) (m : ℤ) :
    c ^ m = (qR p ^ (-m)) ^ (-Real.log c / Real.log (qR p)) := by
  have hq : 1 < qR p := one_lt_qR p
  have hq0 : 0 < qR p := zero_lt_one.trans hq
  have hlogq : Real.log (qR p) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hq0 hq.ne'
  rw [← Real.rpow_intCast (qR p) (-m), ← Real.rpow_mul hq0.le, Real.rpow_def_of_pos hq0,
    ← Real.rpow_intCast c m, Real.rpow_def_of_pos hc]
  congr 1
  field_simp
  push_cast
  ring

theorem exists_bound (C R : ℝ) (hC : 0 ≤ C) (hR : 0 < R) (N₁ : ℤ) :
    ∃ (C' : ℝ) (A : ℕ), 0 ≤ C' ∧ ∀ m : ℤ, N₁ ≤ m →
      C * R ^ m ≤ C' * max 1 (((qR p ^ (-m)) ^ A)⁻¹) := by
  have hq : 1 < qR p := one_lt_qR p
  have hq0 : 0 < qR p := zero_lt_one.trans hq
  obtain ⟨A, hA⟩ := pow_unbounded_of_one_lt (max R 1) hq
  refine ⟨C * max 1 (R ^ N₁), A, mul_nonneg hC (le_trans zero_le_one (le_max_left _ _)), fun m hm => ?_⟩
  have hRm : 0 < R ^ m := zpow_pos hR m
  have hmax1 : 1 ≤ max 1 (R ^ N₁) := le_max_left _ _
  have hmax2 : 1 ≤ max 1 (((qR p ^ (-m)) ^ A)⁻¹) := le_max_left _ _

  have key : R ^ m ≤ max 1 (R ^ N₁) * max 1 (((qR p ^ (-m)) ^ A)⁻¹) := by
    by_cases hm0 : 0 ≤ m
    ·
      have h1 : R ^ m ≤ (max R 1) ^ m := by
        rw [← Int.toNat_of_nonneg hm0, zpow_natCast, zpow_natCast]
        exact pow_le_pow_left₀ hR.le (le_max_left _ _) _
      have h2 : (max R 1) ^ m ≤ (qR p ^ A) ^ m := by
        rw [← Int.toNat_of_nonneg hm0, zpow_natCast, zpow_natCast]
        exact pow_le_pow_left₀ (le_trans zero_le_one (le_max_right _ _)) hA.le _
      have h3 : (qR p ^ A) ^ m = ((qR p ^ (-m)) ^ A)⁻¹ := by
        rw [← zpow_natCast (qR p ^ (-m)) A, ← zpow_mul, neg_mul, zpow_neg, inv_inv, ← zpow_natCast (qR p) A,
          ← zpow_mul, mul_comm]
      calc R ^ m ≤ (qR p ^ A) ^ m := h1.trans h2
        _ = ((qR p ^ (-m)) ^ A)⁻¹ := h3
        _ ≤ max 1 (((qR p ^ (-m)) ^ A)⁻¹) := le_max_right _ _
        _ ≤ max 1 (R ^ N₁) * max 1 (((qR p ^ (-m)) ^ A)⁻¹) := le_mul_of_one_le_left (le_trans zero_le_one hmax2) hmax1
    · push Not at hm0
      have h1 : R ^ m ≤ max 1 (R ^ N₁) := by
        by_cases hR1 : R ≤ 1
        ·
          have : R ^ m = R ^ N₁ * R ^ ((m - N₁).toNat : ℕ) := by
            rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ hR.ne']; congr 1; ring
          rw [this]
          calc R ^ N₁ * R ^ ((m - N₁).toNat : ℕ) ≤ R ^ N₁ * 1 :=
                mul_le_mul_of_nonneg_left (pow_le_one₀ hR.le hR1) (zpow_pos hR N₁).le
            _ = R ^ N₁ := mul_one _
            _ ≤ max 1 (R ^ N₁) := le_max_right _ _
        · push Not at hR1

          have : R ^ m = (R ^ ((-m).toNat : ℕ))⁻¹ := by
            rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_neg, inv_inv]
          rw [this]
          exact le_trans (inv_le_one_of_one_le₀ (one_le_pow₀ hR1.le)) (le_max_left _ _)
      calc R ^ m ≤ max 1 (R ^ N₁) := h1
        _ ≤ max 1 (R ^ N₁) * max 1 (((qR p ^ (-m)) ^ A)⁻¹) := le_mul_of_one_le_right (le_trans zero_le_one hmax1) hmax2
  calc C * R ^ m ≤ C * (max 1 (R ^ N₁) * max 1 (((qR p ^ (-m)) ^ A)⁻¹)) := mul_le_mul_of_nonneg_left key hC
    _ = C * max 1 (R ^ N₁) * max 1 (((qR p ^ (-m)) ^ A)⁻¹) := by ring

end WBGauge
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible.KBKD"

namespace WBC1

open NumberField.StandardAddChar WBGauge

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

theorem diagOne_eq_diagUnits2 (a : (F)ˣ) : (diagOne a : G2) = diagUnits2 a 1 := by
  apply Units.ext
  rw [coe_diagUnits2, Units.val_one]
  ext i j
  rw [NumberField.AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem diagOne_unit_mem (u : (F)ˣ) (hu : Valued.v (u : F) = 1) :
    (diagOne u : G2) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  rw [diagOne_eq_diagUnits2]; exact diagUnits2_unit_mem p u hu

theorem diagOne_zpow_eq_diagZ (π : (F)ˣ) (m : ℤ) :
    (diagOne (π ^ m) : G2) = diagZ (π : F) π.ne_zero m := by
  rw [diagOne_eq_diagUnits2, diagUnits2_zpow_eq_diagZ]

theorem continuous_diagOne : Continuous (fun t : (F)ˣ => (diagOne t : G2)) := by
  have h : (fun t : (F)ˣ => (diagOne t : G2)) = fun t => diagUnits2 t 1 := funext (diagOne_eq_diagUnits2 p)
  rw [h, Units.continuous_iff]
  constructor
  · show Continuous fun t : (F)ˣ => ((diagUnits2 t 1 : G2) : Matrix (Fin 2) (Fin 2) F)
    simp only [coe_diagUnits2, Units.val_one]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact Units.continuous_val
  · show Continuous fun t : (F)ˣ => (((diagUnits2 t 1 : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F)
    simp only [diagUnits2_unit_inv, coe_diagUnits2, Units.val_one]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact @Units.continuous_coe_inv (p.adicCompletion ℚ) _ _ | (simp_rw [← Units.val_inv_eq_inv_val]; exact @Units.continuous_coe_inv (p.adicCompletion ℚ) _ _)

theorem exists_level_of_isLocallyConstant (η : (F)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    ∃ n : ℕ, ∀ z : (F)ˣ, Valued.v ((z : F) - 1) ≤ KBKD.lvl n → η z = 1 := by
  obtain ⟨U, hU, h1, hconst⟩ := hη.exists_open 1

  have hdet : Continuous (Matrix.GeneralLinearGroup.det : G2 → (F)ˣ) := Matrix.GeneralLinearGroup.continuous_det
  obtain ⟨n, hn⟩ := KBKD.exists_congr_subset (K := ℚ) (v := p) (hU.preimage hdet) (by simpa using h1)
  refine ⟨n, fun z hz => ?_⟩
  have hmem : (diagOne z : G2) ∈ KBKD.congr ℚ p n := by
    show KBKD.IsCong n ((diagOne z : G2) : Matrix (Fin 2) (Fin 2) F)
    rw [diagOne_eq_diagUnits2, coe_diagUnits2, Units.val_one]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hz]
  have hdz : Matrix.GeneralLinearGroup.det (diagOne z : G2) = z := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, diagOne_eq_diagUnits2, coe_diagUnits2, Matrix.det_fin_two_of]
    simp
  have := hconst _ (hn hmem)
  rw [hdz, map_one] at this
  exact this

theorem continuous_char (η : (F)ˣ →* ℂˣ) (n : ℕ) (hη : ∀ z : (F)ˣ, Valued.v ((z : F) - 1) ≤ KBKD.lvl n → η z = 1) :
    Continuous fun t : (F)ˣ => ((η t : ℂˣ) : ℂ) := by
  refine continuous_of_open_stabilizer' _ ⟨prinUnits p n, isOpen_prinUnits p n, fun k hk g => ?_⟩
  rw [map_mul, hη k hk, mul_one]

theorem exists_level_central (θ : (F)ˣ →* ℂˣ) (w : G2 → ℂ) (hw : w ≠ 0)
    (hsm : ∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, w (g * k) = w g)
    (hcen : ∀ (z : (F)ˣ) (g : G2), w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ z : ℂˣ) : ℂ) * w g) :
    ∃ n : ℕ, ∀ z : (F)ˣ, Valued.v ((z : F) - 1) ≤ KBKD.lvl n → θ z = 1 := by
  obtain ⟨U, hUo, hUw⟩ := hsm
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : G2, w g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  obtain ⟨n, hn⟩ := KBKD.exists_congr_subset (K := ℚ) (v := p) hUo U.one_mem
  refine ⟨n, fun z hz => ?_⟩
  have hzc : (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) ∈ KBKD.congr ℚ p n := by
    show KBKD.IsCong n ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) : Matrix (Fin 2) (Fin 2) F)
    rw [scalar2_coe]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hz]
  have h1 := hUw _ (hn hzc) g₀
  rw [scalar_mul_comm, hcen] at h1
  exact Units.val_eq_one.1 ((mul_eq_right₀ hg₀).1 h1)

theorem borelSpace_units :
    letI := localBorel ℚ p
    BorelSpace (F)ˣ := by
  letI := localBorel ℚ p
  refine ⟨?_⟩
  show MeasurableSpace.comap Units.val (borel F) = borel (F)ˣ
  rw [← borel_comap]
  congr 1
  exact (Units.isEmbedding_val₀ (G₀ := F)).eq_induced.symm

theorem secondCountableTopology_units : SecondCountableTopology (F)ˣ :=
  (Units.isEmbedding_val₀ (G₀ := F)).isInducing.secondCountableTopology

theorem locallyCompactSpace_units : LocallyCompactSpace (F)ˣ := by
  refine (⟨Units.isEmbedding_val₀, ?_⟩ : Topology.IsOpenEmbedding (Units.val : (F)ˣ → F)).locallyCompactSpace
  have : Set.range (Units.val : (F)ˣ → F) = {x | x ≠ 0} := by
    ext x
    simp only [Set.mem_range, Set.mem_setOf_eq]
    exact ⟨by rintro ⟨u, rfl⟩; exact u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  rw [this]; exact isOpen_ne

theorem selfDualHaarAt_eq' :
    selfDualHaarAt ℚ p = @Measure.addHaarMeasure F _ _ _ (localBorel ℚ p)
      (borelSpace_localBorel ℚ p) (integersPositiveCompacts ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  unfold selfDualHaarAt
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p]
  simp

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  rw [selfDualHaarAt_eq' p]
  infer_instance

theorem isHaarMeasure_tau :
    letI := localBorel ℚ p
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (F)ˣ).IsHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := isAddHaarMeasure_selfDualHaarAt p
  haveI := borelSpace_units p
  exact LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)

theorem cpow_shell (q : ℝ) (hq : 0 < q) (j : ℤ) (s : ℂ) :
    (((q ^ (-j) : ℝ)) : ℂ) ^ (s - 1 / 2) = ((q : ℂ) ^ ((2 : ℂ)⁻¹)) ^ j * ((q : ℂ) ^ (-s)) ^ j := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqj : 0 < q ^ (-j) := zpow_pos hq _
  have hqj0 : (((q ^ (-j) : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hqj.ne'
  have hlog1 : Complex.log (((q ^ (-j) : ℝ)) : ℂ) = ((((-j : ℤ) : ℝ) * Real.log q : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hqj.le, Real.log_zpow]
  have hlogq : Complex.log (q : ℂ) = ((Real.log q : ℝ) : ℂ) := (Complex.ofReal_log hq.le).symm
  rw [Complex.cpow_def_of_ne_zero hqj0, hlog1, ← Complex.cpow_int_mul, ← Complex.cpow_int_mul,
    Complex.cpow_def_of_ne_zero hq0, Complex.cpow_def_of_ne_zero hq0, hlogq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem cpow_ne_zero' (q : ℝ) (hq : 0 < q) (z : ℂ) : (q : ℂ) ^ z ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq.ne')]; exact Complex.exp_ne_zero _

theorem comp_scale_ne_zero (Q : Polynomial ℂ) (hQ : Q ≠ 0) (α : ℂ) (hα : α ≠ 0) :
    Q.comp (Polynomial.C α * Polynomial.X) ≠ 0 := by
  intro h
  apply hQ
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hsub : Set.range (fun x : ℂ => α * x) ⊆ {x | Q.IsRoot x} := by
    rintro _ ⟨x, rfl⟩
    have := congrArg (fun R : Polynomial ℂ => R.eval x) h
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_zero] at this
    exact this
  exact Set.Infinite.mono hsub (Set.infinite_range_of_injective (mul_right_injective₀ hα))

theorem finsum_line (a : ℤ → ℂ) (t : ℤ) :
    (∑ᶠ n : ℤ × ℤ, if ((1 : ℕ) : ℤ) * n.1 + ((1 : ℕ) : ℤ) * n.2 = t then (if n.2 = 0 then a n.1 else 0) else 0) = a t := by
  rw [finsum_eq_single _ (t, 0)]
  · simp
  · intro n hn
    by_cases h2 : n.2 = 0
    · have h1 : n.1 ≠ t := by
        intro h1; apply hn; ext <;> simp [h1, h2]
      simp [h2, h1]
    · simp [h2]

theorem tsum_line_embed (a : ℤ → ℂ) (Y : ℂ) (h : Summable fun j : ℤ => a j * Y ^ j) :
    Summable (fun n : ℤ × ℤ => (if n.2 = 0 then a n.1 else 0) * Y ^ (((1 : ℕ) : ℤ) * n.1 + ((1 : ℕ) : ℤ) * n.2)) ∧
    (∑' n : ℤ × ℤ, (if n.2 = 0 then a n.1 else 0) * Y ^ (((1 : ℕ) : ℤ) * n.1 + ((1 : ℕ) : ℤ) * n.2)) =
      ∑' j : ℤ, a j * Y ^ j := by
  set g : ℤ → ℤ × ℤ := fun j => (j, 0) with hg
  have hinj : Function.Injective g := fun a b hab => by simpa [hg] using congrArg Prod.fst hab
  have hsupp : ∀ n ∉ Set.range g,
      (fun n : ℤ × ℤ => (if n.2 = 0 then a n.1 else 0) * Y ^ (((1 : ℕ) : ℤ) * n.1 + ((1 : ℕ) : ℤ) * n.2)) n = 0 := by
    intro n hn
    have h2 : n.2 ≠ 0 := by
      intro h2; apply hn; exact ⟨n.1, by ext <;> simp [hg, h2]⟩
    simp [h2]
  have hcomp : ((fun n : ℤ × ℤ => (if n.2 = 0 then a n.1 else 0) * Y ^ (((1 : ℕ) : ℤ) * n.1 + ((1 : ℕ) : ℤ) * n.2)) ∘ g) =
      fun j : ℤ => a j * Y ^ j := by
    funext j; simp [hg]
  refine ⟨(hinj.summable_iff hsupp).1 (by rw [hcomp]; exact h), ?_⟩
  have hsupp' : Function.support
      (fun n : ℤ × ℤ => (if n.2 = 0 then a n.1 else 0) * Y ^ (((1 : ℕ) : ℤ) * n.1 + ((1 : ℕ) : ℤ) * n.2)) ⊆ Set.range g := by
    intro n hn
    by_contra hh
    exact hn (hsupp n hh)
  rw [← hinj.tsum_eq hsupp']
  simp [hg]

theorem primal
    (V : Submodule ℂ (G2 → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : G2, (fun g => W (g * h)) ∈ V)
    (hlaw : ∀ W ∈ V, ∀ (x : F) (g : G2), W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g)
    (hsm : ∀ W ∈ V, ∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, W (g * k) = W g)
    (hadm : ∀ U : Subgroup G2, IsOpen (U : Set G2) →
      ∃ B : Finset (G2 → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : G2, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (G2 → ℂ)))
    (χ : (F)ˣ →* ℂˣ) (nχ : ℕ) (hχ : ∀ z : (F)ˣ, Valued.v ((z : F) - 1) ≤ KBKD.lvl nχ → χ z = 1)
    (W : G2 → ℂ) (hW : W ∈ V) :
    letI := localBorel ℚ p
    ∃ (P Q : Polynomial ℂ) (m : ℤ) (σ₀ : ℝ), Q ≠ 0 ∧
      (∀ s : ℂ, σ₀ < s.re →
        Integrable (fun y : (F)ˣ => W (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2))
          (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
      (∀ s : ℂ, σ₀ < s.re →
        (∫ y : (F)ˣ, W (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  letI iF : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := borelSpace_units p
  haveI := secondCountableTopology_units p
  haveI := locallyCompactSpace_units p
  haveI := isHaarMeasure_tau p

  set ϖu : (F)ˣ := NumberField.AdelicLevel.uniformizerUnit ℚ p with hϖudef
  have hvϖ : Valued.v (ϖu : F) = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit ℚ p
  have hϖmem : (ϖu : F) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hvϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  set ϖi : p.adicCompletionIntegers ℚ := ⟨(ϖu : F), hϖmem⟩ with hϖidef
  have hπ : algebraMap (p.adicCompletionIntegers ℚ) F ϖi ≠ 0 := ϖu.ne_zero
  have hϖ' : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) = WithZero.exp (-1 : ℤ) := hvϖ
  have hdiagZ : ∀ j : ℤ, diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ j = (diagOne (ϖu ^ j) : G2) := by
    intro j; rw [diagOne_zpow_eq_diagZ]; rfl

  obtain ⟨N₁, D, M, hD0, hK⟩ :=
    AutomorphicForm.WhittakerModel.exists_polynomial_forall_diagZ_mul_eq_zero_and_sum_coeff_mul_eq_zero_of_admissible
      p V hstab hlaw hsm hadm hπ hϖ' W hW
  obtain ⟨N₂, C, R, hC, hR, hG⟩ :=
    AutomorphicForm.WhittakerModel.exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible
      p V hstab hlaw hsm hadm hπ hϖ' W hW

  obtain ⟨hSmeas, huniq, hmass, hmod, hsum⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  set τ : Measure (F)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) with hτ
  set S : ℤ → Set (F)ˣ := fun n => {y : (F)ˣ | Valued.v (y : F) = WithZero.exp (-(n))} with hS
  have hS0 : S 0 = {u : (F)ˣ | Valued.v (u : F) = 1} := by
    ext u; simp [hS]
  have hmemS : ∀ (j : ℤ) (y : (F)ˣ), y ∈ S j ↔ Valued.v (y : F) = WithZero.exp (-j) := fun j y => Iff.rfl
  have hdec : ∀ (j : ℤ) (y : (F)ˣ), y ∈ S j → Valued.v ((((ϖu ^ j)⁻¹ * y : (F)ˣ)) : F) = 1 := by
    intro j y hy
    rw [hmemS] at hy
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_zpow_eq_zpow_val, map_zpow₀, hvϖ,
      ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, hy, inv_mul_cancel₀ WithZero.exp_ne_zero]
  have hysplit : ∀ (j : ℤ) (y : (F)ˣ), (diagOne y : G2) =
      diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ j * diagOne ((ϖu ^ j)⁻¹ * y) := by
    intro j y; rw [hdiagZ, ← map_mul, mul_inv_cancel_left]
  have hshell_mem : ∀ (j : ℤ) (u : (F)ˣ), u ∈ S 0 → ϖu ^ j * u ∈ S j := by
    intro j u hu
    rw [hS0] at hu
    rw [hmemS, Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hvϖ, ← WithZero.exp_zsmul, smul_eq_mul,
      mul_neg, mul_one]
    rw [Set.mem_setOf_eq] at hu
    rw [hu, mul_one]

  have hWcont : Continuous W := continuous_of_open_stabilizer' W (hsm W hW)
  have hχcont : Continuous fun t : (F)ˣ => ((χ t : ℂˣ) : ℂ) := continuous_char p χ nχ hχ
  have hmodeq : ∀ y : (F)ˣ, ((modulus (y : F) : ℝ)) = ‖(y : F)‖ := by
    intro y; rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]; rfl
  have hmodcont : Continuous fun y : (F)ˣ => ((modulus (y : F) : ℝ) : ℂ) := by
    have : (fun y : (F)ˣ => ((modulus (y : F) : ℝ) : ℂ)) = fun y : (F)ˣ => ((‖(y : F)‖ : ℝ) : ℂ) := by
      funext y; rw [hmodeq]
    rw [this]; exact Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val)
  have hfcont : ∀ s : ℂ, Continuous (fun y : (F)ˣ => W (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2)) := by
    intro s
    refine ((hWcont.comp (continuous_diagOne p)).mul hχcont).mul (hmodcont.cpow continuous_const fun y => ?_)
    rw [hmodeq]
    exact Complex.ofReal_mem_slitPlane.2 (norm_pos_iff.2 (Units.ne_zero y))

  set cχ : ℝ := ‖((χ ϖu : ℂˣ) : ℂ)‖ with hcχ
  have hcχ0 : 0 < cχ := norm_pos_iff.2 (χ ϖu).ne_zero
  have hχnorm : ∀ (j : ℤ) (y : (F)ˣ), y ∈ S j → ‖((χ y : ℂˣ) : ℂ)‖ = cχ ^ j := by
    intro j y hy
    have : y = ϖu ^ j * ((ϖu ^ j)⁻¹ * y) := (mul_inv_cancel_left _ _).symm
    rw [this, norm_char_zpow_mul_unit p χ nχ hχ ϖu j _ (hdec j y hy)]

  set q : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) with hq
  have hq1 : 1 < q := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
    rw [hq]
    have h' : (1 : ℝ) < ((Ideal.absNorm p.asIdeal : ℝ≥0) : ℝ) := by exact_mod_cast this
    simpa using h'
  have hq0 : 0 < q := one_pos.trans hq1
  have hqC : ((Ideal.absNorm p.asIdeal : ℂ)) = (q : ℂ) := by rw [hq]; push_cast; rfl

  set a : ℤ → ℂ := fun j => ∫ u in S 0, W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ j * diagOne u) *
      ((χ u : ℂˣ) : ℂ) ∂τ with ha
  have hS0cpt : IsCompact (S 0) := by rw [hS0]; exact isCompact_units_sphere p
  have hint0 : ∀ j : ℤ, IntegrableOn (fun u : (F)ˣ =>
      W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ j * diagOne u) * ((χ u : ℂˣ) : ℂ)) (S 0) τ := by
    intro j
    refine ContinuousOn.integrableOn_compact hS0cpt (Continuous.continuousOn ?_)
    exact (hWcont.comp (continuous_const.mul (continuous_diagOne p))).mul hχcont
  have hu1 : ∀ u : (F)ˣ, u ∈ S 0 → Valued.v (u : F) = 1 := by
    intro u hu; rw [hS0] at hu; exact hu
  have ha0 : ∀ j : ℤ, j < N₁ → a j = 0 := by
    intro j hj
    simp only [ha]
    refine (setIntegral_congr_fun (hSmeas 0) fun u hu => ?_).trans (integral_zero _ _)
    show _ = (0 : ℂ)
    rw [(hK _ (diagOne_unit_mem p u (hu1 u hu))).1 j hj, zero_mul]
  have harec : ∀ m : ℕ, M ≤ m →
      ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * a (N₁ + (m : ℤ) - (i : ℤ)) = 0 := by
    intro m hm
    have hpt : ∀ u ∈ S 0, ∑ i ∈ Finset.range (D.natDegree + 1),
        D.coeff i * (W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ (N₁ + (m : ℤ) - (i : ℤ)) * diagOne u) *
          ((χ u : ℂˣ) : ℂ)) = (0 : ℂ) := by
      intro u hu
      have := (hK _ (diagOne_unit_mem p u (hu1 u hu))).2 m hm
      calc _ = (∑ i ∈ Finset.range (D.natDegree + 1),
            D.coeff i * W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ (N₁ + (m : ℤ) - (i : ℤ)) * diagOne u)) *
              ((χ u : ℂˣ) : ℂ) := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [this, zero_mul]
    calc ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * a (N₁ + (m : ℤ) - (i : ℤ))
        = ∑ i ∈ Finset.range (D.natDegree + 1), ∫ u in S 0,
            D.coeff i * (W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ (N₁ + (m : ℤ) - (i : ℤ)) * diagOne u) *
              ((χ u : ℂˣ) : ℂ)) ∂τ := Finset.sum_congr rfl (fun i _ => by simp only [ha]; rw [integral_const_mul])
      _ = ∫ u in S 0, ∑ i ∈ Finset.range (D.natDegree + 1),
            D.coeff i * (W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ (N₁ + (m : ℤ) - (i : ℤ)) * diagOne u) *
              ((χ u : ℂˣ) : ℂ)) ∂τ := (integral_finset_sum _ (fun i _ => (hint0 _).const_mul _)).symm
      _ = ∫ u in S 0, (0 : ℂ) ∂τ := setIntegral_congr_fun (hSmeas 0) hpt
      _ = 0 := integral_zero _ _

  set β : ℂ := (q : ℂ) ^ ((2 : ℂ)⁻¹) with hβ
  set α : ℂ := ((χ ϖu : ℂˣ) : ℂ) * β with hα
  have hα0 : α ≠ 0 := mul_ne_zero (χ ϖu).ne_zero (cpow_ne_zero' q hq0 _)
  have hshell : ∀ (s : ℂ) (j : ℤ),
      ∫ y in S j, W (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2) ∂τ =
        a j * (α * (q : ℂ) ^ (-s)) ^ j := by
    intro s j
    have hmp : MeasurePreserving (fun u : (F)ˣ => ϖu ^ j * u) τ τ := measurePreserving_mul_left τ (ϖu ^ j)
    have hemb : MeasurableEmbedding (fun u : (F)ˣ => ϖu ^ j * u) := (MeasurableEquiv.mulLeft (ϖu ^ j)).measurableEmbedding
    have hpre : (fun u : (F)ˣ => ϖu ^ j * u) ⁻¹' (S j) = S 0 := by
      ext u
      rw [Set.mem_preimage, hmemS, hmemS, Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hvϖ,
        ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_zero, WithZero.exp_zero]
      exact mul_eq_left₀ WithZero.exp_ne_zero
    have h1 := hmp.setIntegral_preimage_emb hemb
      (fun y : (F)ˣ => W (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2)) (S j)
    rw [hpre] at h1
    rw [← h1]
    have hpt : ∀ u ∈ S 0,
        W (diagOne (ϖu ^ j * u)) * ((χ (ϖu ^ j * u) : ℂˣ) : ℂ) * ((modulus (((ϖu ^ j * u : (F)ˣ)) : F) : ℝ) : ℂ) ^ (s - 1 / 2) =
          ((((χ ϖu : ℂˣ) : ℂ)) ^ j * (((q ^ (-j) : ℝ)) : ℂ) ^ (s - 1 / 2)) *
            (W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ j * diagOne u) * ((χ u : ℂˣ) : ℂ)) := by
      intro u hu
      have h1 : (diagOne (ϖu ^ j * u) : G2) = diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ j * diagOne u := by
        rw [map_mul, hdiagZ]
      have h2 : ((χ (ϖu ^ j * u) : ℂˣ) : ℂ) = (((χ ϖu : ℂˣ) : ℂ)) ^ j * ((χ u : ℂˣ) : ℂ) := by
        rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val]
      rw [hmod j _ (hshell_mem j u hu), h1, h2]
      ring
    rw [setIntegral_congr_fun (hSmeas 0) hpt, integral_const_mul]
    rw [cpow_shell q hq0 j s, hα, mul_zpow, mul_zpow]
    simp only [ha]
    ring

  have hL : ∀ t : ℤ, (∑ᶠ n : ℤ × ℤ, if ((1 : ℕ) : ℤ) * n.1 + ((1 : ℕ) : ℤ) * n.2 = t then
      (if n.2 = 0 then a n.1 else 0) else 0) = a t := finsum_line a
  have hw2 : ∀ n : ℤ × ℤ, (n.1 < min N₁ 0 ∨ n.2 < min N₁ 0) → (if n.2 = 0 then a n.1 else 0) = 0 := by
    rintro n (h | h)
    · by_cases h2 : n.2 = 0
      · rw [if_pos h2]; exact ha0 _ (lt_of_lt_of_le h (min_le_left _ _))
      · rw [if_neg h2]
    · have : n.2 ≠ 0 := by
        intro h2; rw [h2] at h; exact absurd h (not_lt.2 (min_le_right _ _))
      rw [if_neg this]
  have hc : ∃ (N : ℤ) (E : Polynomial ℂ) (M' : ℕ), E.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N → (fun t : ℤ => ∑ᶠ n : ℤ × ℤ, if ((1 : ℕ) : ℤ) * n.1 + ((1 : ℕ) : ℤ) * n.2 = t then
        (if n.2 = 0 then a n.1 else 0) else 0) m = 0) ∧
      (∀ m : ℕ, M' ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i *
        (fun t : ℤ => ∑ᶠ n : ℤ × ℤ, if ((1 : ℕ) : ℤ) * n.1 + ((1 : ℕ) : ℤ) * n.2 = t then
          (if n.2 = 0 then a n.1 else 0) else 0) (N + (m : ℤ) - (i : ℤ)) = 0) := by
    refine ⟨N₁, D, M, hD0, fun m hm => ?_, fun m hm => ?_⟩
    · show (∑ᶠ n : ℤ × ℤ, _) = 0
      rw [hL]; exact ha0 m hm
    · simp only [hL]; exact harec m hm
  obtain ⟨P, Q, m₀, hQ, hres⟩ :=
    Polynomial.exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line
      (fun n : ℤ × ℤ => if n.2 = 0 then a n.1 else 0) (min N₁ 0) hw2 1 1 one_pos one_pos hc

  set σ₀ : ℝ := 1 / 2 + Real.log (R * cχ) / Real.log q with hσ₀

  have hint : ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun y : (F)ˣ => W (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2)) τ := by
    intro s hs
    set σ : ℝ := s.re with hσ
    set ρ : ℝ := R * cχ * q ^ (-(σ - 1 / 2)) with hρ
    have hρ0 : 0 < ρ := mul_pos (mul_pos hR hcχ0) (Real.rpow_pos_of_pos hq0 _)
    have hρ1 : ρ < 1 := by
      have hlogq : 0 < Real.log q := Real.log_pos hq1
      have h1 : Real.log (R * cχ) < (σ - 1 / 2) * Real.log q := by
        rw [hσ₀] at hs
        have := (div_lt_iff₀ hlogq).1 (by linarith : Real.log (R * cχ) / Real.log q < σ - 1 / 2)
        linarith
      have h2 : R * cχ < q ^ (σ - 1 / 2) := (Real.lt_rpow_iff_log_lt (mul_pos hR hcχ0) hq0).2 h1
      rw [hρ, Real.rpow_neg hq0.le, ← div_eq_mul_inv, div_lt_one (Real.rpow_pos_of_pos hq0 _)]
      exact h2
    refine ⟨(hfcont s).aestronglyMeasurable, ?_⟩

    set Cst : ℝ≥0∞ := ENNReal.ofReal (C * ρ ^ N₂) with hCst
    set r : ℝ≥0∞ := ENNReal.ofReal ρ with hr
    have hr1 : r < 1 := by rw [hr, ← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hρ1
    have hpt : ∀ y : (F)ˣ, ‖W (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ ≤
        ∑' n : ℕ, (S (N₂ + n)).indicator (fun _ => Cst * r ^ n) y := by
      intro y
      obtain ⟨j, hj, -⟩ := huniq y
      by_cases hjN : j < N₂
      · have : W (diagOne y) = 0 := by
          rw [hysplit j y, ((hG _ (diagOne_unit_mem p _ (hdec j y hj))) j).1 hjN]
        rw [this, zero_mul, zero_mul, enorm_zero]
        exact bot_le
      · push Not at hjN
        set n : ℕ := (j - N₂).toNat with hn
        have hjn : N₂ + (n : ℤ) = j := by rw [hn, Int.toNat_of_nonneg (by omega)]; ring
        refine le_trans ?_ (ENNReal.le_tsum n)
        rw [hjn, Set.indicator_of_mem hj]
        have hbd : ‖W (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2)‖ ≤ C * ρ ^ N₂ * ρ ^ n := by
          have hmody : (modulus (y : F) : ℝ) = q ^ (-j) := hmod j y hj
          have hmpos : 0 < (modulus (y : F) : ℝ) := by rw [hmody]; exact zpow_pos hq0 _
          rw [norm_mul, norm_mul, hχnorm j y hj, Complex.norm_cpow_eq_rpow_re_of_pos hmpos, hmody,
            hysplit j y]
          have hWle := ((hG _ (diagOne_unit_mem p _ (hdec j y hj))) j).2
          have hre : (s - 1 / 2).re = σ - 1 / 2 := by rw [hσ]; simp
          rw [hre]
          have hid : R ^ j * cχ ^ j * (q ^ (-j)) ^ (σ - 1 / 2) = ρ ^ N₂ * ρ ^ n := by
            rw [← zpow_natCast ρ n, ← zpow_add₀ hρ0.ne', hjn, hρ, mul_zpow, mul_zpow]
            congr 1
            rw [← Real.rpow_intCast (q ^ (-(σ - 1 / 2))), ← Real.rpow_mul hq0.le, ← Real.rpow_intCast q (-j),
              ← Real.rpow_mul hq0.le]
            congr 1; push_cast; ring
          calc ‖W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ j * diagOne ((ϖu ^ j)⁻¹ * y))‖ * cχ ^ j *
                (q ^ (-j)) ^ (σ - 1 / 2)
              ≤ C * R ^ j * cχ ^ j * (q ^ (-j)) ^ (σ - 1 / 2) := by
                gcongr
            _ = C * (R ^ j * cχ ^ j * (q ^ (-j)) ^ (σ - 1 / 2)) := by ring
            _ = C * ρ ^ N₂ * ρ ^ n := by rw [hid]; ring
        rw [← ofReal_norm, hCst, hr, ← ENNReal.ofReal_pow hρ0.le, ← ENNReal.ofReal_mul (mul_nonneg hC (zpow_pos hρ0 _).le)]
        exact ENNReal.ofReal_le_ofReal hbd
    have hmeasj : ∀ n : ℕ, Measurable fun y => (S (N₂ + n)).indicator (fun _ => Cst * r ^ n) y :=
      fun n => measurable_const.indicator (hSmeas _)
    calc ∫⁻ y, ‖W (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ ∂τ
        ≤ ∫⁻ y, ∑' n : ℕ, (S (N₂ + n)).indicator (fun _ => Cst * r ^ n) y ∂τ := lintegral_mono hpt
      _ = ∑' n : ℕ, ∫⁻ y, (S (N₂ + n)).indicator (fun _ => Cst * r ^ n) y ∂τ :=
          lintegral_tsum fun n => (hmeasj n).aemeasurable
      _ = ∑' n : ℕ, Cst * r ^ n * τ (S 0) := by
          refine tsum_congr fun n => ?_
          rw [lintegral_indicator_const (hSmeas _), (hmass (N₂ + n)).1]
      _ = Cst * τ (S 0) * ∑' n : ℕ, r ^ n := by
          rw [← ENNReal.tsum_mul_left]; refine tsum_congr fun n => ?_; ring
      _ < ⊤ := by
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hmass 0).2.2) ?_
          rw [ENNReal.tsum_geometric]
          exact ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 hr1)

  refine ⟨Polynomial.C (α ^ m₀) * P.comp (Polynomial.C α * Polynomial.X), Q.comp (Polynomial.C α * Polynomial.X), -m₀, σ₀,
    comp_scale_ne_zero Q hQ α hα0, hint, fun s hs => ?_⟩
  set X : ℂ := (q : ℂ) ^ (-s) with hX
  have hX0 : X ≠ 0 := cpow_ne_zero' q hq0 _
  have hHS := hsum _ (hint s hs)
  have hHS' : HasSum (fun j : ℤ => a j * (α * X) ^ j)
      (∫ y, W (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2) ∂τ) := by
    have : (fun n : ℤ => ∫ y in S n, W (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2) ∂τ) =
        fun j : ℤ => a j * (α * X) ^ j := funext (hshell s)
    rw [← this]; exact hHS
  obtain ⟨hsum2, htsum2⟩ := tsum_line_embed a (α * X) hHS'.summable
  have hmain := hres (α * X) (mul_ne_zero hα0 hX0) hsum2
  rw [htsum2, hHS'.tsum_eq] at hmain
  rw [hqC]
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [hmain, mul_zpow, hX, ← Complex.cpow_int_mul]
  have : ((m₀ : ℤ) : ℂ) * -s = (((-m₀ : ℤ)) : ℂ) * s := by push_cast; ring
  rw [this]
  ring

def revScale (R : Polynomial ℂ) (c : ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (R.natDegree + 1), Polynomial.C (R.coeff i * c ^ i) * Polynomial.X ^ (R.natDegree - i)

theorem revScale_eval (R : Polynomial ℂ) (c X : ℂ) (hX : X ≠ 0) :
    (revScale R c).eval X = X ^ R.natDegree * R.eval (c * X⁻¹) := by
  unfold revScale
  rw [Polynomial.eval_finset_sum, Polynomial.eval_eq_sum_range (p := R), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ R.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have : X ^ R.natDegree = X ^ (R.natDegree - i) * X ^ i := by rw [← pow_add, Nat.sub_add_cancel hi']
  rw [this, mul_pow]
  have hXi : X ^ i * X⁻¹ ^ i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hX, one_pow]
  linear_combination (-(R.coeff i * c ^ i * X ^ (R.natDegree - i))) * hXi

theorem revScale_ne_zero (R : Polynomial ℂ) (hR : R ≠ 0) (c : ℂ) (hc : c ≠ 0) : revScale R c ≠ 0 := by
  intro h
  apply hR
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hsub : (fun X : ℂ => c * X⁻¹) '' {X : ℂ | X ≠ 0} ⊆ {x | R.IsRoot x} := by
    rintro _ ⟨X, hX, rfl⟩
    have h1 := revScale_eval R c X hX
    rw [h, Polynomial.eval_zero] at h1
    have : R.eval (c * X⁻¹) = 0 := by
      rcases mul_eq_zero.1 h1.symm with h2 | h2
      · exact absurd h2 (pow_ne_zero _ hX)
      · exact h2
    exact this
  refine Set.Infinite.mono hsub ((Set.infinite_image_iff ?_).2 ?_)
  · intro x _ y _ hxy
    have hxy' : c * x⁻¹ = c * y⁻¹ := hxy
    exact inv_inj.1 (mul_left_cancel₀ hc hxy')
  · have : {X : ℂ | X ≠ 0} = ({0} : Set ℂ)ᶜ := by ext; simp
    rw [this]; exact (Set.finite_singleton 0).infinite_compl

theorem cpow_one_sub (q : ℝ) (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ (-(1 - s)) = (q : ℂ) ^ (-(1 : ℂ)) * ((q : ℂ) ^ (-s))⁻¹ := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [show (-(1 - s) : ℂ) = -1 + s by ring, Complex.cpow_add _ _ hq0, Complex.cpow_neg _ s, inv_inv]

theorem cpow_int_mul_one_sub (q : ℝ) (hq : 0 < q) (m : ℤ) (s : ℂ) :
    (q : ℂ) ^ ((m : ℂ) * (1 - s)) = (q : ℂ) ^ (m : ℂ) * ((q : ℂ) ^ (-s)) ^ m := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [show ((m : ℂ) * (1 - s) : ℂ) = (m : ℂ) + (m : ℂ) * (-s) by ring, Complex.cpow_add _ _ hq0, Complex.cpow_int_mul]

end WBC1
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible.KBKD"

open WBC1 in
theorem wbC1_main
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ))
    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    letI := localBorel ℚ p
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ (P Q Pd Qd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧
          (∀ s : ℂ, σ₀ < s.re →
            Integrable (fun y : (p.adicCompletion ℚ)ˣ => w (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          (∀ s : ℂ, σ₀ < s.re →
            (∫ y : (p.adicCompletion ℚ)ˣ, w (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, s.re < σ₁ →
            Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
              w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          (∀ s : ℂ, s.re < σ₁ →
            (∫ y : (p.adicCompletion ℚ)ˣ,
                w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  intro w hw

  have hNopen : IsOpen (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2
  have Vstab : ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      (fun g => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) :=
    fun W hW h => SSKD.translate_mem_span w₂base h hW
  have Vlaw : ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g :=
    fun W hW x => SSKD.law_of_mem_span w₂base (unipotent x) _ (hw₂law x) hW
  have Vsm : ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g :=
    fun W hW => SSKD.exists_open_stabilizer_of_mem_span w₂base _ hNopen hw₂K hW

  obtain ⟨nη, hnη⟩ := exists_level_of_isLocallyConstant p η hη
  obtain ⟨nθ, hnθ⟩ := exists_level_central p θ₀ w₂base hw₂ne ⟨_, hNopen, hw₂K⟩ hcentral

  obtain ⟨P, Q, m, σ₀, hQ, hint, hrat⟩ := primal p _ Vstab Vlaw Vsm hw₂adm η nη hnη w hw

  have hw' : (fun g => w (g * wJ)) ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) := Vstab w hw wJ
  have hlvl : ∀ z : (p.adicCompletion ℚ)ˣ, Valued.v ((z : p.adicCompletion ℚ) - 1) ≤ KBKD.lvl (max nη nθ) →
      (η⁻¹ * θ₀⁻¹) z = 1 := by
    intro z hz
    have h1 : KBKD.lvl (max nη nθ) ≤ KBKD.lvl nη := by
      unfold KBKD.lvl; rw [WithZero.exp_le_exp]; push_cast; omega
    have h2 : KBKD.lvl (max nη nθ) ≤ KBKD.lvl nθ := by
      unfold KBKD.lvl; rw [WithZero.exp_le_exp]; push_cast; omega
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, hnη z (hz.trans h1), hnθ z (hz.trans h2),
      inv_one, one_mul]
  obtain ⟨P', Q', m', σ₀', hQ', hint', hrat'⟩ :=
    primal p _ Vstab Vlaw Vsm hw₂adm (η⁻¹ * θ₀⁻¹) (max nη nθ) hlvl (fun g => w (g * wJ)) hw'

  have hfun : ∀ s : ℂ, (fun y : (p.adicCompletion ℚ)ˣ =>
        w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
          ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)) =
      fun y : (p.adicCompletion ℚ)ˣ => (fun g => w (g * wJ)) (diagOne y) * (((η⁻¹ * θ₀⁻¹) y : ℂˣ) : ℂ) *
        ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 - s) - 1 / 2) := by
    intro s
    funext y
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [show ((1 - s) - 1 / 2 : ℂ) = 1 / 2 - s by ring]
    ring

  set q : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) with hq
  have hq0 : 0 < q := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
    rw [hq]
    have h' : (1 : ℝ) < ((Ideal.absNorm p.asIdeal : ℝ≥0) : ℝ) := by exact_mod_cast this
    have : (1:ℝ) < ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := by simpa using h'
    linarith
  have hqC : ((Ideal.absNorm p.asIdeal : ℂ)) = (q : ℂ) := by rw [hq]; push_cast; rfl
  set c : ℂ := (q : ℂ) ^ (-(1 : ℂ)) with hc
  have hc0 : c ≠ 0 := cpow_ne_zero' q hq0 _
  refine ⟨P, Q, Polynomial.C ((q : ℂ) ^ ((m' : ℤ) : ℂ)) * revScale P' c, revScale Q' c, m,
    -((Q'.natDegree : ℤ) + m' - P'.natDegree), σ₀, 1 - σ₀', hQ, revScale_ne_zero Q' hQ' c hc0, hint, hrat,
    fun s hs => ?_, fun s hs => ?_⟩
  · rw [hfun s]
    exact hint' (1 - s) (by simp; linarith)
  · have hs' : σ₀' < (1 - s).re := by simp; linarith
    have h := hrat' (1 - s) hs'
    rw [hfun s, hqC]
    rw [hqC, cpow_one_sub q hq0 s, cpow_int_mul_one_sub q hq0 m' s] at h
    set X : ℂ := (q : ℂ) ^ (-s) with hX
    have hX0 : X ≠ 0 := cpow_ne_zero' q hq0 _
    rw [revScale_eval Q' c X hX0, Polynomial.eval_mul, Polynomial.eval_C, revScale_eval P' c X hX0]
    have hXpow : (q : ℂ) ^ (((-((Q'.natDegree : ℤ) + m' - P'.natDegree) : ℤ) : ℂ) * s) =
        X ^ ((Q'.natDegree : ℤ) + m' - P'.natDegree) := by
      rw [hX, ← Complex.cpow_int_mul]; congr 1; push_cast; ring
    rw [hXpow]
    calc _ = X ^ Q'.natDegree * ((∫ y : (p.adicCompletion ℚ)ˣ, (fun g => w (g * wJ)) (diagOne y) *
          (((η⁻¹ * θ₀⁻¹) y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 - s) - 1 / 2)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q'.eval (c * X⁻¹)) := by ring
      _ = X ^ Q'.natDegree * ((q : ℂ) ^ (m' : ℂ) * X ^ m' * P'.eval (c * X⁻¹)) := by rw [h]
      _ = X ^ ((Q'.natDegree : ℤ) + m' - P'.natDegree) *
            ((q : ℂ) ^ ((m' : ℤ) : ℂ) * (X ^ P'.natDegree * P'.eval (c * X⁻¹))) := by
          rw [zpow_sub₀ hX0, zpow_add₀ hX0, zpow_natCast, zpow_natCast]
          field_simp

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ (P Q Pd Qd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧
          (∀ s : ℂ, σ₀ < s.re →
            Integrable (fun y : (p.adicCompletion ℚ)ˣ => w (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          (∀ s : ℂ, σ₀ < s.re →
            (∫ y : (p.adicCompletion ℚ)ˣ, w (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, s.re < σ₁ →
            Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
              w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          (∀ s : ℂ, s.re < σ₁ →
            (∫ y : (p.adicCompletion ℚ)ˣ,
                w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) :=
  wbC1_main p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂adm hcentral wJ η hη

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible.KBKD"

end S_LanglandsTunnell_RankinSelberg_forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible (solution)
