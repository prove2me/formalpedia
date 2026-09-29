-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/642d7336-cd5c-5c74-bc9f-b15d1852265a

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
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Theorems.Thm_LocalGL2_Kirillov_exists_isBump
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

noncomputable section

section KBblock
open IsDedekindDomain NumberField
open scoped WithZero Pointwise

namespace KBE4a

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

end GLtwo

end KBE4a
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne.KBE4a"

end KBblock
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne.KBE4a"

namespace SSE4a

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne.KBE4a"

end SSE4a
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne.KBE4a"

namespace E4aBody

open LocalGL2.Kirillov

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

def etaDet (χ ξ : (Qp)ˣ →* ℂˣ) (g : G2) : ℂ :=
  ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹

theorem etaDet_mul (χ ξ : (Qp)ˣ →* ℂˣ) (g h : G2) :
    etaDet p χ ξ (g * h) = etaDet p χ ξ g * etaDet p χ ξ h := by
  simp only [etaDet, map_mul, Units.val_mul, mul_inv]
  ring

theorem det_unipotent_eq_one (x : Qp) : Matrix.GeneralLinearGroup.det (unipotent x : G2) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  show Matrix.det !![(1 : Qp), x; 0, 1] = 1
  rw [Matrix.det_fin_two_of]; ring

theorem etaDet_one (χ ξ : (Qp)ˣ →* ℂˣ) : etaDet p χ ξ 1 = 1 := by
  simp [etaDet]

theorem etaDet_unipotent (χ ξ : (Qp)ˣ →* ℂˣ) (x : Qp) : etaDet p χ ξ (unipotent x) = 1 := by
  simp [etaDet, det_unipotent_eq_one]

theorem scalar2_coe (z : (Qp)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) : Matrix (Fin 2) (Fin 2) Qp) = !![(z : Qp), 0; 0, (z : Qp)] := by
  show Matrix.scalar (Fin 2) (z : Qp) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar]

theorem det_scalar2 (z : (Qp)ˣ) : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) = z * z := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalar2_coe, Matrix.det_fin_two_of, Units.val_mul]
  ring

theorem etaDet_scalar (χ ξ : (Qp)ˣ →* ℂˣ) (z : (Qp)ˣ) :
    etaDet p χ ξ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      ((χ z : ℂˣ) : ℂ) * ((χ z : ℂˣ) : ℂ) * (((ξ z : ℂˣ) : ℂ) * ((ξ z : ℂˣ) : ℂ))⁻¹ := by
  simp only [etaDet, det_scalar2, map_mul, Units.val_mul]

def twist (χ ξ : (Qp)ˣ →* ℂˣ) : (G2 → ℂ) →ₗ[ℂ] (G2 → ℂ) where
  toFun w := fun g => etaDet p χ ξ g * w g
  map_add' w₁ w₂ := by funext g; simp only [Pi.add_apply]; ring
  map_smul' c w := by funext g; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem twist_apply (χ ξ : (Qp)ˣ →* ℂˣ) (w : G2 → ℂ) (g : G2) : twist p χ ξ w g = etaDet p χ ξ g * w g := rfl

theorem chv_zero' {δ : (WithZero (Multiplicative ℤ))ˣ} (u : UF p) : chv (0 : Ch p δ) u = 1 := by
  have h := chv_add (0 : Ch p δ) 0 u
  rw [add_zero] at h
  have hne := chv_ne_zero (0 : Ch p δ) u
  have h2 : chv (0 : Ch p δ) u * chv (0 : Ch p δ) u = chv (0 : Ch p δ) u * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ hne h2

theorem dg_eq_diagUnitGL2 (y : (Qp)ˣ) : dg p y = diagUnitGL2 y := Units.ext rfl

theorem unipotentGL2_eq_unipotent (x : Qp) : (AutomorphicForm.unipotentGL2 x : G2) = unipotent x := Units.ext rfl

theorem main
    (χ : (Qp)ˣ →* ℂˣ) (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)
    (ξ : (Qp)ˣ →* ℂˣ) (B : ℕ) (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p ξ B) (hBk : B < kp)
    (θ₀ : (Qp)ˣ →* ℂˣ)
    (w₂base : G2 → ℂ) (hw₂ne : w₂base ≠ 0)
    (V₀ : Submodule ℂ (G2 → ℂ))
    (V0stab : ∀ W ∈ V₀, ∀ h : G2, (fun g => W (g * h)) ∈ V₀)
    (V0law : ∀ W ∈ V₀, ∀ (x : Qp) (g : G2), W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g)
    (V0sm : ∀ W ∈ V₀, ∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, W (g * k) = W g)
    (V0cen : ∀ W ∈ V₀, ∀ (z : (Qp)ˣ) (g : G2),
      W (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * W g)
    (hgen : (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)) ⊆ V₀) :
    ∃ w' ∈ V₀,
      (∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ y : (Qp)ˣ,
        (fun g : G2 => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (diagUnitGL2 y) =
          if Valued.v (y : Qp) = WithZero.exp (((2 * kp : ℕ)) : ℤ) then c₀ else 0) ∧
      (∀ (x : Qp) (g : G2),
        (fun g : G2 => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (unipotent x * g) =
          NumberField.StandardAddChar.psiLocal ℚ p x *
            (fun g : G2 => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) ∧
      (∀ (z : (Qp)ˣ) (g : G2),
        (fun g : G2 => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
          (((θ₀ * (χ * ξ⁻¹) ^ 2) z : ℂˣ) : ℂ) *
            (fun g : G2 => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) ∧
      (∃ U : Subgroup G2, IsOpen (U : Set G2) ∧
        ∀ k ∈ U, ∀ g : G2,
          (fun g : G2 => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (g * k) =
          (fun g : G2 => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) := by
  classical

  set S : Submodule ℂ (G2 → ℂ) := V₀.map (twist p χ ξ) with hS

  have hη1 : ∀ k ∈ KBE4a.congr ℚ p kp, etaDet p χ ξ k = 1 := by
    intro k hk
    have hc : KBE4a.IsCong kp (k : Matrix (Fin 2) (Fin 2) Qp) := hk
    have hvdet : Valued.v ((Matrix.GeneralLinearGroup.det k : (Qp)ˣ) : Qp) = 1 := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]; exact hc.v_det
    have hvdet1 : Valued.v (((Matrix.GeneralLinearGroup.det k : (Qp)ˣ) : Qp) - 1) ≤ WithZero.exp (-((kp : ℤ) + 1)) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]; exact hc.v_det_sub_one
    have hmem : ∀ m : ℕ, m ≤ kp → Matrix.GeneralLinearGroup.det k ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m := by
      intro m hm
      refine ⟨hvdet, Or.inr (hvdet1.trans ?_)⟩
      rw [WithZero.exp_le_exp]; omega
    have h1 : χ (Matrix.GeneralLinearGroup.det k) = 1 := hkp.1 _ (hmem kp le_rfl)
    have h2 : ξ (Matrix.GeneralLinearGroup.det k) = 1 := hξB.1 _ (hmem B hBk.le)
    simp [etaDet, h1, h2]

  have Sstab : ∀ W ∈ S, ∀ k : G2, (fun g => W (g * k)) ∈ S := by
    intro W hW k
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hW
    refine Submodule.mem_map.2 ⟨etaDet p χ ξ k • (fun g => w (g * k)), V₀.smul_mem _ (V0stab w hw k), ?_⟩
    rw [map_smul]
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, twist_apply, etaDet_mul]
    ring

  have Ssm : ∀ W ∈ S, ∃ K₀ : Subgroup G2, IsOpen (K₀ : Set G2) ∧ ∀ k ∈ K₀, (fun g => W (g * k)) = W := by
    intro W hW
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hW
    obtain ⟨U, hU, hUw⟩ := V0sm w hw
    refine ⟨U ⊓ KBE4a.congr ℚ p kp, ?_, ?_⟩
    · rw [Subgroup.coe_inf]; exact hU.inter (KBE4a.isOpen_congr kp)
    · intro k hk
      rw [Subgroup.mem_inf] at hk
      funext g
      simp only [twist_apply]
      rw [etaDet_mul, hη1 k hk.2, mul_one, hUw k hk.1 g]

  have Slaw : ∀ U ∈ S, ∀ (x : Qp) (g : G2), U (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * U g := by
    intro U hU x g
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hU
    simp only [twist_apply]
    rw [etaDet_mul, etaDet_unipotent, one_mul, V0law u hu x g]
    ring

  have hψ : NumberField.StandardAddChar.psiLocal ℚ p ≠ 1 := LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p
  have hψ0 : ∀ᶠ t in nhds (0 : Qp), NumberField.StandardAddChar.psiLocal ℚ p t = 1 :=
    Filter.eventually_of_mem ((LocalGL2.Kirillov.isOpen_unit_ball p).mem_nhds (by simp))
      (fun t ht => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p t
        ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (le_of_lt ht)))

  obtain ⟨ϖ₀, hϖ₀⟩ := KBE4a.exists_uniformizer ℚ p
  set ϖ : (Qp)ˣ := Units.mk0 ϖ₀ (KBE4a.uniformizer_ne_zero hϖ₀) with hϖdef
  have hϖ : Valued.v (ϖ : Qp) = WithZero.exp (-1 : ℤ) := hϖ₀

  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : G2, w₂base h₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hw₂ne (funext h)
  set w₁ : G2 → ℂ := fun g => w₂base (g * h₀) with hw₁def
  have hw₁ : w₁ ∈ V₀ := hgen ⟨h₀, rfl⟩
  set ξ₀ : (G2 → ℂ) ⧸ defectSpan p (NumberField.StandardAddChar.psiLocal ℚ p) S :=
    (defectSpan p (NumberField.StandardAddChar.psiLocal ℚ p) S).mkQ (twist p χ ξ w₁) with hξ₀def
  have hξ₀ : ξ₀ ∈ coinv p (NumberField.StandardAddChar.psiLocal ℚ p) S :=
    Submodule.mem_map.2 ⟨_, Submodule.mem_map.2 ⟨w₁, hw₁, rfl⟩, rfl⟩

  obtain ⟨E, hES, hbump⟩ := LocalGL2.Kirillov.exists_isBump ℚ p (NumberField.StandardAddChar.psiLocal ℚ p) hψ hψ0
    S Sstab Ssm ϖ hϖ 1 (-((2 * kp : ℕ) : ℤ)) (0 : Ch p 1) ξ₀ hξ₀
  obtain ⟨w', hw', hw'E⟩ := Submodule.mem_map.1 hES
  have hEapp : ∀ g : G2, E g = etaDet p χ ξ g * w' g := fun g => by rw [← hw'E]; rfl

  have hker : defectSpan p (NumberField.StandardAddChar.psiLocal ℚ p) S ≤
      LinearMap.ker (LinearMap.proj (1 : G2) : (G2 → ℂ) →ₗ[ℂ] ℂ) := by
    apply Submodule.span_le.2
    rintro V ⟨U, hU, x, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    simp only [LinearMap.proj_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [unipotentGL2_eq_unipotent, show (unipotent x : G2) = unipotent x * 1 by rw [mul_one], Slaw U hU x 1, sub_self]
  set L := (defectSpan p (NumberField.StandardAddChar.psiLocal ℚ p) S).liftQ (LinearMap.proj (1 : G2)) hker with hLdef
  have hL : ∀ f : G2 → ℂ, L ((defectSpan p (NumberField.StandardAddChar.psiLocal ℚ p) S).mkQ f) = f 1 := fun f => rfl

  have hval : ∀ (k : ℤ) (u : UF p),
      E (dg p (ϖ ^ k * (u : (Qp)ˣ))) = if k = -((2 * kp : ℕ) : ℤ) then w₂base h₀ else 0 := by
    intro k u
    have h := congrArg L (hbump k u)
    have hs : shell p (NumberField.StandardAddChar.psiLocal ℚ p) S ϖ E k u =
        (defectSpan p (NumberField.StandardAddChar.psiLocal ℚ p) S).mkQ (rT p (dg p (ϖ ^ k * (u : (Qp)ˣ))) E) := rfl
    rw [hs, hL, rT_apply, one_mul] at h
    rw [h]
    by_cases hk : k = -((2 * kp : ℕ) : ℤ)
    · rw [if_pos hk, if_pos hk, map_smul, chv_zero', one_smul, hξ₀def, hL, twist_apply, etaDet_one, one_mul,
        hw₁def]
      show w₂base (1 * h₀) = w₂base h₀
      rw [one_mul]
    · rw [if_neg hk, if_neg hk, map_zero]

  refine ⟨w', hw', ⟨w₂base h₀, hh₀, fun y => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨k, u, rfl⟩ := exists_shell_decomp p ϖ hϖ y
    show etaDet p χ ξ (diagUnitGL2 (ϖ ^ k * (u : (Qp)ˣ))) * w' (diagUnitGL2 (ϖ ^ k * (u : (Qp)ˣ))) = _
    rw [← hEapp, ← dg_eq_diagUnitGL2, hval k u]
    have hv : Valued.v (((ϖ ^ k * (u : (Qp)ˣ) : (Qp)ˣ)) : Qp) = WithZero.exp (-k) := by
      rw [Units.val_mul, map_mul, v_pi_zpow p ϖ hϖ, v_coe_UF, mul_one]
    by_cases hk : k = -((2 * kp : ℕ) : ℤ)
    · rw [if_pos hk, if_pos (by rw [hv, WithZero.exp_inj]; omega)]
    · rw [if_neg hk, if_neg (by rw [hv, WithZero.exp_inj]; omega)]
  · intro x g
    show etaDet p χ ξ (unipotent x * g) * w' (unipotent x * g) =
      NumberField.StandardAddChar.psiLocal ℚ p x * (etaDet p χ ξ g * w' g)
    rw [← hEapp, ← hEapp]
    exact Slaw E hES x g
  · intro z g
    show etaDet p χ ξ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) * w' (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
      (((θ₀ * (χ * ξ⁻¹) ^ 2) z : ℂˣ) : ℂ) * (etaDet p χ ξ g * w' g)
    rw [etaDet_mul, etaDet_scalar, V0cen w' hw' z g]
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    ring
  · obtain ⟨K₀, hK₀, hK⟩ := Ssm E hES
    refine ⟨K₀, hK₀, fun k hk g => ?_⟩
    show etaDet p χ ξ (g * k) * w' (g * k) = etaDet p χ ξ g * w' g
    rw [← hEapp, ← hEapp]
    exact congrFun (hK k hk) g

end E4aBody
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne.KBE4a"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne.KBE4a"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)
    (ξ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (B : ℕ) (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p ξ B) (hBk : B < kp)
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g) :
    ∃ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      (∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ y : (p.adicCompletion ℚ)ˣ,
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (diagUnitGL2 y) =
          if Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (((2 * kp : ℕ)) : ℤ) then c₀ else 0) ∧

      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (unipotent x * g) =
          NumberField.StandardAddChar.psiLocal ℚ p x *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) ∧
      (∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
          (((θ₀ * (χ * ξ⁻¹) ^ 2) z : ℂˣ) : ℂ) *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) ∧
      (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (g * k) =
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g)  := by
  classical

  have hNopen : IsOpen (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2
  have V0stab : ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      (fun g => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) :=
    fun W hW h => SSE4a.translate_mem_span w₂base h hW
  have V0law : ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g :=
    fun W hW x => SSE4a.law_of_mem_span w₂base (unipotent x) _ (hw₂law x) hW
  have V0sm : ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g :=
    fun W hW => SSE4a.exists_open_stabilizer_of_mem_span w₂base _ hNopen hw₂K hW
  have V0cen : ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        W (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * W g :=
    fun W hW z => SSE4a.law_of_mem_span w₂base _ _ (hcentral z) hW
  exact E4aBody.main p χ kp hkp ξ B hξB hBk θ₀ w₂base hw₂ne _ V0stab V0law V0sm V0cen Submodule.subset_span

end S_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne (solution)
