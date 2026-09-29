-- Prove2me | solution 1 for LocalNewvector.isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2d1e028c-f49d-5868-9bca-128ada46e789

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_ReductionFunctor
import Theorems.Thm_CuspidalType_IsCuspidalOfType_of_linearEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType

set_option autoImplicit false

open FLT.SmoothVectors

noncomputable section

namespace LocalNewvector
p2m_export "LocalNewvector" "fixedSubmodule mem_fixedSubmodule_iff centralGL IsIrreducibleGLRep mem_gl2CongruenceSubgroup_zero_iff gl2ReductionHom gl2ReductionHom_apply_of_coe_eq gl2ReductionHom_surjective smul_mem_fixedSubmodule_gl2CongruenceSubgroup_one_of_mem gl2ReductionRep gl2ReductionRep_gl2ReductionHom_apply"
namespace CuspidalPartSpanS
p2m_open "LocalNewvector"

variable (q : ℕ) [Fact q.Prime]

private theorem q_ne_zero : (q : ℚ_[q]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

private theorem one_lt_q_real : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt

private theorem norm_natCast_le_one (a : ℕ) : ‖(a : ℚ_[q])‖ ≤ 1 := by
  exact_mod_cast Padic.norm_int_le_one (p := q) (a : ℤ)

private def qu : ℚ_[q]ˣ := Units.mk0 (q : ℚ_[q]) (q_ne_zero q)

@[scoped simp] private theorem val_qu : ((qu q : ℚ_[q]ˣ) : ℚ_[q]) = q := rfl

private theorem val_qu_zpow (m : ℤ) : ((qu q ^ m : ℚ_[q]ˣ) : ℚ_[q]) = (q : ℚ_[q]) ^ m := by
  rw [Units.val_zpow_eq_zpow_val, val_qu]

private theorem norm_q_zpow (m : ℤ) : ‖(q : ℚ_[q]) ^ m‖ = (q : ℝ) ^ (-m) := Padic.norm_p_zpow m

private abbrev uu (x : ℚ_[q]) : GL (Fin 2) ℚ_[q] := gl2UnipotentPadic q x

private def ul (x : ℚ_[q]) : GL (Fin 2) ℚ_[q] :=
  ⟨!![1, 0; x, 1], !![1, 0; -x, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

@[scoped simp] private theorem coe_ul (x : ℚ_[q]) :
    ((ul q x : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![1, 0; x, 1] :=
  rfl

@[scoped simp] private theorem coe_ul_inv (x : ℚ_[q]) :
    (((ul q x)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![1, 0; -x, 1] :=
  rfl

private def w0 : GL (Fin 2) ℚ_[q] :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

@[scoped simp] private theorem coe_w0 : ((w0 q : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![0, 1; 1, 0] := rfl

@[scoped simp] private theorem coe_w0_inv : (((w0 q)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![0, 1; 1, 0] :=
  rfl

private def dg (c : ℚ_[q]ˣ) : GL (Fin 2) ℚ_[q] :=
  ⟨!![(c : ℚ_[q]), 0; 0, 1], !![((c⁻¹ : ℚ_[q]ˣ) : ℚ_[q]), 0; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

@[scoped simp] private theorem coe_dg (c : ℚ_[q]ˣ) :
    ((dg q c : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![(c : ℚ_[q]), 0; 0, 1] :=
  rfl

@[scoped simp] private theorem coe_dg_inv (c : ℚ_[q]ˣ) :
    (((dg q c)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![((c⁻¹ : ℚ_[q]ˣ) : ℚ_[q]), 0; 0, 1] :=
  rfl

private def dq (m : ℤ) : GL (Fin 2) ℚ_[q] := dg q (qu q ^ m)

private theorem coe_centralGL_apply (z : ℚ_[q]ˣ) (i j : Fin 2) :
    ((LocalNewvector.centralGL q z : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j
      = if i = j then (z : ℚ_[q]) else 0 := by
  show (algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q]) (z : ℚ_[q])) i j = _
  rw [Matrix.algebraMap_matrix_apply]
  rfl

private theorem uu_mul_uu (x y : ℚ_[q]) : uu q x * uu q y = uu q (x + y) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem uu_zero : uu q 0 = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

private theorem uu_comm (x y : ℚ_[q]) : uu q x * uu q y = uu q y * uu q x := by
  rw [uu_mul_uu, uu_mul_uu, add_comm]

private theorem ul_mul_ul (x y : ℚ_[q]) : ul q x * ul q y = ul q (x + y) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem ul_comm (x y : ℚ_[q]) : ul q x * ul q y = ul q y * ul q x := by
  rw [ul_mul_ul, ul_mul_ul, add_comm]

private theorem coe_centralGL (z : ℚ_[q]ˣ) :
    ((LocalNewvector.centralGL q z : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q])
      = !![(z : ℚ_[q]), 0; 0, (z : ℚ_[q])] := by
  ext i j
  rw [coe_centralGL_apply]
  fin_cases i <;> fin_cases j <;> simp

private theorem centralGL_comm (z : ℚ_[q]ˣ) (g : GL (Fin 2) ℚ_[q]) :
    LocalNewvector.centralGL q z * g = g * LocalNewvector.centralGL q z := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_centralGL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem uu_mul_dg (j : ℚ_[q]) (c : ℚ_[q]ˣ) :
    uu q j * dg q c = dg q c * uu q (((c⁻¹ : ℚ_[q]ˣ) : ℚ_[q]) * j) := by
  refine Matrix.GeneralLinearGroup.ext fun i k => ?_
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem ul_mul_dg (j : ℚ_[q]) (c : ℚ_[q]ˣ) : ul q j * dg q c = dg q c * ul q ((c : ℚ_[q]) * j) := by
  refine Matrix.GeneralLinearGroup.ext fun i k => ?_
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem w0_mul_w0 : w0 q * w0 q = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem w0_inv : (w0 q)⁻¹ = w0 q :=
  inv_eq_of_mul_eq_one_right (w0_mul_w0 q)

private theorem w0_mul_uu_mul_w0 (x : ℚ_[q]) : w0 q * uu q x * w0 q = ul q x := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem dg_mul_dg (c d : ℚ_[q]ˣ) : dg q c * dg q d = dg q (c * d) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem dg_one : dg q 1 = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

private theorem dq_zero : dq q 0 = 1 := by
  rw [dq, zpow_zero, dg_one]

private def kC (x : ℚ_[q]ˣ) (c : ℚ_[q]ˣ) : GL (Fin 2) ℚ_[q] :=
  ⟨!![(c : ℚ_[q]) * ((x⁻¹ : ℚ_[q]ˣ) : ℚ_[q]), 1; -1, 0], !![0, -1; 1, (c : ℚ_[q]) * ((x⁻¹ : ℚ_[q]ˣ) : ℚ_[q])], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

@[scoped simp] private theorem coe_kC (x c : ℚ_[q]ˣ) : ((kC q x c : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q])
    = !![(c : ℚ_[q]) * ((x⁻¹ : ℚ_[q]ˣ) : ℚ_[q]), 1; -1, 0] := rfl

@[scoped simp] private theorem coe_kC_inv (x c : ℚ_[q]ˣ) : (((kC q x c)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q])
    = !![0, -1; 1, (c : ℚ_[q]) * ((x⁻¹ : ℚ_[q]ˣ) : ℚ_[q])] := rfl

private theorem uu_mul_dg_eq_lower (x c : ℚ_[q]ˣ) :
    uu q (x : ℚ_[q]) * dg q c
      = ul q ((x⁻¹ : ℚ_[q]ˣ) : ℚ_[q]) * LocalNewvector.centralGL q (c * x⁻¹) * dg q (x * x * c⁻¹) * kC q x c := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have hx : (x : ℚ_[q]) ≠ 0 := x.ne_zero
  have hc : (c : ℚ_[q]) ≠ 0 := c.ne_zero
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul, coe_centralGL, coe_ul, coe_dg, coe_kC, coe_gl2UnipotentPadic, coe_dg]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals ring

private theorem mem_K0_of_norm (g : GL (Fin 2) ℚ_[q]) (h1 : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j‖ ≤ 1)
    (h2 : ∀ i j, ‖((g⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j‖ ≤ 1) :
    g ∈ gl2CongruenceSubgroup q 0 :=
  (LocalNewvector.mem_gl2CongruenceSubgroup_zero_iff q g).2 ⟨h1, h2⟩

private theorem mem_K0_of_entries {g : GL (Fin 2) ℚ_[q]} {a b c d a' b' c' d' : ℚ_[q]}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![a, b; c, d])
    (hg' : ((g⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![a', b'; c', d'])
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (ha' : ‖a'‖ ≤ 1) (hb' : ‖b'‖ ≤ 1) (hc' : ‖c'‖ ≤ 1) (hd' : ‖d'‖ ≤ 1) :
    g ∈ gl2CongruenceSubgroup q 0 := by
  refine mem_K0_of_norm q g (fun i j => ?_) (fun i j => ?_)
  · rw [hg]
    fin_cases i <;> fin_cases j
    exacts [ha, hb, hc, hd]
  · rw [hg']
    fin_cases i <;> fin_cases j
    exacts [ha', hb', hc', hd']

private theorem norm_zero_le_one : ‖(0 : ℚ_[q])‖ ≤ 1 := by
  rw [norm_zero]
  exact zero_le_one

private theorem norm_neg_le_one {x : ℚ_[q]} (hx : ‖x‖ ≤ 1) : ‖-x‖ ≤ 1 := by
  rwa [norm_neg]

private theorem uu_mem_K0 {x : ℚ_[q]} (hx : ‖x‖ ≤ 1) : uu q x ∈ gl2CongruenceSubgroup q 0 :=
  mem_K0_of_entries q (coe_gl2UnipotentPadic q x) (coe_gl2UnipotentPadic_inv q x) norm_one.le hx
    (norm_zero_le_one q) norm_one.le norm_one.le (norm_neg_le_one q hx) (norm_zero_le_one q) norm_one.le

private theorem ul_mem_K0 {x : ℚ_[q]} (hx : ‖x‖ ≤ 1) : ul q x ∈ gl2CongruenceSubgroup q 0 :=
  mem_K0_of_entries q (coe_ul q x) (coe_ul_inv q x) norm_one.le (norm_zero_le_one q) hx norm_one.le norm_one.le
    (norm_zero_le_one q) (norm_neg_le_one q hx) norm_one.le

private theorem w0_mem_K0 : w0 q ∈ gl2CongruenceSubgroup q 0 :=
  mem_K0_of_entries q (coe_w0 q) (coe_w0_inv q) (norm_zero_le_one q) norm_one.le norm_one.le (norm_zero_le_one q)
    (norm_zero_le_one q) norm_one.le norm_one.le (norm_zero_le_one q)

private theorem dg_mem_K0 {c : ℚ_[q]ˣ} (hc : ‖(c : ℚ_[q])‖ = 1) : dg q c ∈ gl2CongruenceSubgroup q 0 := by
  have hc' : ‖((c⁻¹ : ℚ_[q]ˣ) : ℚ_[q])‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hc, inv_one]
  exact mem_K0_of_entries q (coe_dg q c) (coe_dg_inv q c) hc.le (norm_zero_le_one q) (norm_zero_le_one q)
    norm_one.le hc'.le (norm_zero_le_one q) (norm_zero_le_one q) norm_one.le

private theorem kC_mem_K0 {x c : ℚ_[q]ˣ} (h : ‖(c : ℚ_[q]) * ((x⁻¹ : ℚ_[q]ˣ) : ℚ_[q])‖ ≤ 1) :
    kC q x c ∈ gl2CongruenceSubgroup q 0 :=
  mem_K0_of_entries q (coe_kC q x c) (coe_kC_inv q x c) h norm_one.le (norm_neg_le_one q norm_one.le)
    (norm_zero_le_one q) (norm_zero_le_one q) (norm_neg_le_one q norm_one.le) norm_one.le h

omit [Fact q.Prime] in
private theorem q_inv_eq : ((q : ℝ) ^ (-((1 : ℕ) : ℤ)) : ℝ) = (q : ℝ)⁻¹ := by
  simp

private theorem uu_mem_K1 {x : ℚ_[q]} (hx : ‖x‖ ≤ (q : ℝ)⁻¹) : uu q x ∈ gl2CongruenceSubgroup q 1 :=
  gl2UnipotentPadic_mem_gl2CongruenceSubgroup q (by rwa [q_inv_eq])

private theorem ul_mem_K1 {x : ℚ_[q]} (hx : ‖x‖ ≤ (q : ℝ)⁻¹) : ul q x ∈ gl2CongruenceSubgroup q 1 := by
  have h := conj_mem_gl2CongruenceSubgroup q (w0_mem_K0 q) (uu_mem_K1 q hx)
  rwa [w0_inv, w0_mul_uu_mul_w0] at h

private theorem norm_q : ‖(q : ℚ_[q])‖ = (q : ℝ)⁻¹ := Padic.norm_p

private theorem norm_q_mul_natCast_le (a : ℕ) : ‖(q : ℚ_[q]) * a‖ ≤ (q : ℝ)⁻¹ := by
  rw [norm_mul, norm_q]
  exact mul_le_of_le_one_right (inv_nonneg.mpr (Nat.cast_nonneg _)) (norm_natCast_le_one q a)

private theorem exists_eq_qu_zpow_mul (y : ℚ_[q]ˣ) :
    ∃ (m : ℤ) (η : ℚ_[q]ˣ), ‖(η : ℚ_[q])‖ = 1 ∧ y = qu q ^ m * η := by
  have hy : (y : ℚ_[q]) ≠ 0 := y.ne_zero
  refine ⟨(y : ℚ_[q]).valuation, (qu q ^ (y : ℚ_[q]).valuation)⁻¹ * y, ?_, by rw [mul_inv_cancel_left]⟩
  rw [Units.val_mul, Units.val_inv_eq_inv_val, val_qu_zpow, norm_mul, norm_inv, norm_q_zpow,
    Padic.norm_eq_zpow_neg_valuation hy, inv_mul_cancel₀]
  exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)

private theorem exists_iwasawa_of_apply_one_zero_eq_zero (g : GL (Fin 2) ℚ_[q])
    (h : (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 = 0) :
    ∃ (x : ℚ_[q]) (z : ℚ_[q]ˣ) (m : ℤ) (k : GL (Fin 2) ℚ_[q]), k ∈ gl2CongruenceSubgroup q 0 ∧
      g = uu q x * LocalNewvector.centralGL q z * dq q m * k := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 ≠ 0 := by
    have hd : ((Matrix.GeneralLinearGroup.det g : ℚ_[q]ˣ) : ℚ_[q]) ≠ 0 := Units.ne_zero _
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h, mul_zero, sub_zero] at hd
    exact hd
  have ha : (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hd : (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  obtain ⟨m, η, hη, hsplit⟩ := exists_eq_qu_zpow_mul q (Units.mk0 _ ha * (Units.mk0 _ hd)⁻¹)
  refine ⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 1 / (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1, Units.mk0 _ hd, m,
    dg q η, dg_mem_K0 q hη, ?_⟩
  rw [mul_assoc (uu q _ * LocalNewvector.centralGL q _), dq, dg_mul_dg, ← hsplit]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_centralGL, coe_dg,
    coe_gl2UnipotentPadic]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  · simp [Matrix.mul_apply, Fin.sum_univ_two, h]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem norm_le_of_eq_zero_imp {c d : ℚ_[q]} (hcd : ‖c‖ ≤ ‖d‖) (hc : d = 0 → c = 0 → False) : d ≠ 0 := by
  intro hd0
  rw [hd0, norm_zero] at hcd
  exact hc hd0 (norm_le_zero_iff.mp hcd)

private theorem apply_one_ne_zero (g : GL (Fin 2) ℚ_[q]) :
    ¬ ((g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 = 0) := by
  rintro ⟨hd, hc⟩
  have hdet : ((Matrix.GeneralLinearGroup.det g : ℚ_[q]ˣ) : ℚ_[q]) ≠ 0 := Units.ne_zero _
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hd, hc] at hdet
  simp at hdet

private theorem exists_iwasawa (g : GL (Fin 2) ℚ_[q]) :
    ∃ (x : ℚ_[q]) (z : ℚ_[q]ˣ) (m : ℤ) (k : GL (Fin 2) ℚ_[q]), k ∈ gl2CongruenceSubgroup q 0 ∧
      g = uu q x * LocalNewvector.centralGL q z * dq q m * k := by
  by_cases hcd : ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0‖ ≤ ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1‖
  · have hd : (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 ≠ 0 :=
      norm_le_of_eq_zero_imp q hcd fun hd hc => apply_one_ne_zero q g ⟨hd, hc⟩
    set t : ℚ_[q] := (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 / (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 with ht
    have htn : ‖t‖ ≤ 1 := by
      rw [ht, norm_div]
      exact div_le_one_of_le₀ hcd (norm_nonneg _)
    have hT : ((g * (ul q t)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 = 0 := by
      rw [Matrix.GeneralLinearGroup.coe_mul, coe_ul_inv]
      simp [Matrix.mul_apply, Fin.sum_univ_two, ht]
      field_simp
      ring
    obtain ⟨x, z, m, k, hk, hgk⟩ := exists_iwasawa_of_apply_one_zero_eq_zero q _ hT
    refine ⟨x, z, m, k * ul q t, mul_mem hk (ul_mem_K0 q htn), ?_⟩
    rw [← mul_assoc, ← hgk, inv_mul_cancel_right]
  · rw [not_le] at hcd
    have hc : (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hcd
      exact (not_lt.mpr (norm_nonneg _)) hcd
    set g' : GL (Fin 2) ℚ_[q] := g * w0 q with hg'
    have h10 : (g' : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 = (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 := by
      rw [hg', Matrix.GeneralLinearGroup.coe_mul, coe_w0]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h11 : (g' : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 = (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 := by
      rw [hg', Matrix.GeneralLinearGroup.coe_mul, coe_w0]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    set t : ℚ_[q] := (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 / (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 with ht
    have htn : ‖t‖ ≤ 1 := by
      rw [ht, norm_div]
      exact div_le_one_of_le₀ hcd.le (norm_nonneg _)
    have hT : ((g' * (ul q t)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 = 0 := by
      rw [Matrix.GeneralLinearGroup.coe_mul, coe_ul_inv, hg', Matrix.GeneralLinearGroup.coe_mul, coe_w0]
      simp [Matrix.mul_apply, Fin.sum_univ_two, ht]
      field_simp
      ring
    obtain ⟨x, z, m, k, hk, hgk⟩ := exists_iwasawa_of_apply_one_zero_eq_zero q _ hT
    refine ⟨x, z, m, k * ul q t * w0 q, mul_mem (mul_mem hk (ul_mem_K0 q htn)) (w0_mem_K0 q), ?_⟩
    calc g = g' * w0 q := by rw [hg', mul_assoc, w0_mul_w0, mul_one]
      _ = g' * (ul q t)⁻¹ * ul q t * w0 q := by rw [inv_mul_cancel_right]
      _ = _ := by rw [hgk]; simp only [mul_assoc]

variable (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
  [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]

private theorem smul_eq_self_of_mem {g : GL (Fin 2) ℚ_[q]} (hg : g ∈ gl2CongruenceSubgroup q 1) {v : V}
    (hv : v ∈ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V) : g • v = v :=
  (LocalNewvector.mem_fixedSubmodule_iff.1 hv) g hg

private theorem smul_mem_fixed {k : GL (Fin 2) ℚ_[q]} (hk : k ∈ gl2CongruenceSubgroup q 0) {v : V}
    (hv : v ∈ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V) :
    k • v ∈ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V :=
  LocalNewvector.smul_mem_fixedSubmodule_gl2CongruenceSubgroup_one_of_mem q V hk hv

private theorem uu_natCast_smul_eq_of_dvd {a b : ℕ} (h : (q : ℤ) ∣ (a : ℤ) - b) {v : V}
    (hv : v ∈ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V) :
    uu q (a : ℚ_[q]) • v = uu q (b : ℚ_[q]) • v := by
  have hab : uu q (a : ℚ_[q]) = uu q (b : ℚ_[q]) * uu q (((a : ℤ) - b : ℤ) : ℚ_[q]) := by
    rw [uu_mul_uu]
    congr 1
    push_cast
    ring
  have hmem : uu q (((a : ℤ) - b : ℤ) : ℚ_[q]) ∈ gl2CongruenceSubgroup q 1 := by
    refine uu_mem_K1 q ?_
    have h1 := (Padic.norm_int_le_pow_iff_dvd (p := q) ((a : ℤ) - b) 1).2 (by simpa using h)
    simpa using h1
  rw [hab, mul_smul, smul_eq_self_of_mem q V hmem hv]

private def cuspSum (v : V) : V := ∑ b ∈ Finset.range q, uu q (b : ℚ_[q]) • v

private theorem cuspSum_mem_fixed {v : V} (hv : v ∈ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V) :
    cuspSum q V v ∈ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V :=
  Submodule.sum_mem _ fun b _ => smul_mem_fixed q V (uu_mem_K0 q (norm_natCast_le_one q b)) hv

private theorem uu_one_smul_cuspSum {v : V} (hv : v ∈ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V) :
    uu q 1 • cuspSum q V v = cuspSum q V v := by
  unfold cuspSum
  rw [Finset.smul_sum]
  have hshift : ∀ b : ℕ, uu q 1 • uu q (b : ℚ_[q]) • v = uu q ((b + 1 : ℕ) : ℚ_[q]) • v := by
    intro b
    rw [← mul_smul, uu_mul_uu]
    congr 2
    push_cast
    ring
  simp_rw [hshift]
  have hq : 0 < q := (Fact.out : q.Prime).pos
  obtain ⟨n, hn⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  have key : ∑ b ∈ Finset.range q, uu q ((b + 1 : ℕ) : ℚ_[q]) • v + uu q ((0 : ℕ) : ℚ_[q]) • v
      = ∑ b ∈ Finset.range q, uu q (b : ℚ_[q]) • v + uu q ((q : ℕ) : ℚ_[q]) • v := by
    rw [← Finset.sum_range_succ' (fun b => uu q ((b : ℕ) : ℚ_[q]) • v) q,
      Finset.sum_range_succ (fun b => uu q ((b : ℕ) : ℚ_[q]) • v) q]
  have h0q : uu q ((q : ℕ) : ℚ_[q]) • v = uu q ((0 : ℕ) : ℚ_[q]) • v :=
    uu_natCast_smul_eq_of_dvd q V (by simp) hv
  rw [h0q] at key
  exact add_right_cancel key

private theorem uu_natCast_smul_cuspSum {v : V} (hv : v ∈ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V)
    (n : ℕ) : uu q (n : ℚ_[q]) • cuspSum q V v = cuspSum q V v := by
  induction n with
  | zero => rw [Nat.cast_zero, uu_zero, one_smul]
  | succ n ih =>
    have : uu q ((n + 1 : ℕ) : ℚ_[q]) = uu q 1 * uu q (n : ℚ_[q]) := by
      rw [uu_mul_uu]
      congr 1
      push_cast
      ring
    rw [this, mul_smul, ih, uu_one_smul_cuspSum q V hv]

private theorem gl2ReductionHom_uu (t : ZMod q) :
    LocalNewvector.gl2ReductionHom q ⟨uu q ((t.val : ℕ) : ℚ_[q]), uu_mem_K0 q (norm_natCast_le_one q _)⟩
      = CuspidalType.unipotent q t := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · rw [LocalNewvector.gl2ReductionHom_apply_of_coe_eq q _ _ _ 1 (by simp)]
    simp [CuspidalType.unipotent]
  · rw [LocalNewvector.gl2ReductionHom_apply_of_coe_eq q _ _ _ ((t.val : ℕ) : ℤ_[q])
      (by rw [PadicInt.coe_natCast, coe_gl2UnipotentPadic]; simp [-ZMod.natCast_val]), map_natCast,
      ZMod.natCast_zmod_val, CuspidalType.unipotent_val]
    simp
  · rw [LocalNewvector.gl2ReductionHom_apply_of_coe_eq q _ _ _ 0 (by simp)]
    simp [CuspidalType.unipotent]
  · rw [LocalNewvector.gl2ReductionHom_apply_of_coe_eq q _ _ _ 1 (by simp)]
    simp [CuspidalType.unipotent]

variable {V}

private theorem cuspSum_eq_zero
    (S : Submodule ℂ V) (hS : S ≤ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V)
    (hK : ∀ k ∈ gl2CongruenceSubgroup q 0, ∀ s ∈ S, k • s ∈ S)
    (hcusp : ∀ v : ↥(LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V), (v : V) ∈ S →
      (∀ t : ZMod q, LocalNewvector.gl2ReductionRep q V (CuspidalType.unipotent q t) v = v) → v = 0)
    {v : V} (hv : v ∈ S) : cuspSum q V v = 0 := by
  have hmem : cuspSum q V v ∈ S := S.sum_mem fun b _ => hK _ (uu_mem_K0 q (norm_natCast_le_one q b)) _ hv
  have h := hcusp ⟨cuspSum q V v, cuspSum_mem_fixed q V (hS hv)⟩ hmem fun t => by
    rw [← gl2ReductionHom_uu q t]
    refine Subtype.ext ?_
    rw [LocalNewvector.gl2ReductionRep_gl2ReductionHom_apply]
    exact uu_natCast_smul_cuspSum q V (hS hv) _
  exact congrArg Subtype.val h

private theorem lowerCuspSum_eq_zero
    (S : Submodule ℂ V) (hS : S ≤ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V)
    (hK : ∀ k ∈ gl2CongruenceSubgroup q 0, ∀ s ∈ S, k • s ∈ S)
    (hcusp : ∀ v : ↥(LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V), (v : V) ∈ S →
      (∀ t : ZMod q, LocalNewvector.gl2ReductionRep q V (CuspidalType.unipotent q t) v = v) → v = 0)
    {v : V} (hv : v ∈ S) :
    ∑ b ∈ Finset.range q, ul q (b : ℚ_[q]) • v = 0 := by
  have h : ∀ b : ℕ, ul q (b : ℚ_[q]) • v = w0 q • uu q (b : ℚ_[q]) • w0 q • v := by
    intro b
    rw [← w0_mul_uu_mul_w0, mul_smul, mul_smul]
  simp_rw [h, ← Finset.smul_sum]
  have h0 : cuspSum q V (w0 q • v) = 0 := cuspSum_eq_zero q S hS hK hcusp (hK _ (w0_mem_K0 q) _ hv)
  unfold cuspSum at h0
  rw [h0, smul_zero]

private theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (c n : ℕ) :
    ∑ a ∈ Finset.range (c * n), f a = ∑ i ∈ Finset.range n, ∑ r ∈ Finset.range c, f (c * i + r) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

private theorem sum_uu_natCast_eq_zero
    (S : Submodule ℂ V) (hS : S ≤ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V)
    (hK : ∀ k ∈ gl2CongruenceSubgroup q 0, ∀ s ∈ S, k • s ∈ S)
    (hcusp : ∀ v : ↥(LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V), (v : V) ∈ S →
      (∀ t : ZMod q, LocalNewvector.gl2ReductionRep q V (CuspidalType.unipotent q t) v = v) → v = 0)
    {v : V} (hv : v ∈ S) (n : ℕ) :
    ∑ b ∈ Finset.range (q * n), uu q (b : ℚ_[q]) • v = 0 := by
  rw [sum_range_mul_eq]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h : ∀ r : ℕ, uu q ((q * i + r : ℕ) : ℚ_[q]) • v = uu q (r : ℚ_[q]) • v := fun r =>
    uu_natCast_smul_eq_of_dvd q V ⟨i, by push_cast; ring⟩ (hS hv)
  simp_rw [h]
  exact cuspSum_eq_zero q S hS hK hcusp hv

private theorem sum_ul_natCast_eq_zero
    (S : Submodule ℂ V) (hS : S ≤ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V)
    (hK : ∀ k ∈ gl2CongruenceSubgroup q 0, ∀ s ∈ S, k • s ∈ S)
    (hcusp : ∀ v : ↥(LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V), (v : V) ∈ S →
      (∀ t : ZMod q, LocalNewvector.gl2ReductionRep q V (CuspidalType.unipotent q t) v = v) → v = 0)
    {v : V} (hv : v ∈ S) (n : ℕ) :
    ∑ b ∈ Finset.range (q * n), ul q (b : ℚ_[q]) • v = 0 := by
  have h : ∀ b : ℕ, ul q (b : ℚ_[q]) • v = w0 q • uu q (b : ℚ_[q]) • w0 q • v := by
    intro b
    rw [← w0_mul_uu_mul_w0, mul_smul, mul_smul]
  simp_rw [h, ← Finset.smul_sum]
  rw [sum_uu_natCast_eq_zero q S hS hK hcusp (hK _ (w0_mem_K0 q) _ hv), smul_zero]

private theorem sum_uu_progression_eq_zero
    (S : Submodule ℂ V) (hS : S ≤ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V)
    (hK : ∀ k ∈ gl2CongruenceSubgroup q 0, ∀ s ∈ S, k • s ∈ S)
    (hcusp : ∀ v : ↥(LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V), (v : V) ∈ S →
      (∀ t : ZMod q, LocalNewvector.gl2ReductionRep q V (CuspidalType.unipotent q t) v = v) → v = 0)
    {v : V} (hv : v ∈ S) (e n : ℕ) :
    ∑ a ∈ Finset.range (q ^ e * (q * n)), uu q (((q : ℚ_[q]) ^ e)⁻¹ * a) • v = 0 := by
  rw [sum_range_mul_eq]
  have hqe : ((q : ℚ_[q]) ^ e) ≠ 0 := pow_ne_zero _ (q_ne_zero q)
  have h : ∀ i r : ℕ, uu q (((q : ℚ_[q]) ^ e)⁻¹ * ((q ^ e * i + r : ℕ) : ℚ_[q])) • v
      = uu q (((q : ℚ_[q]) ^ e)⁻¹ * r) • uu q (i : ℚ_[q]) • v := by
    intro i r
    rw [← mul_smul, uu_mul_uu]
    congr 2
    push_cast
    field_simp
    ring
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [← Finset.smul_sum, sum_uu_natCast_eq_zero q S hS hK hcusp hv, smul_zero]

private theorem sum_ul_progression_eq_zero
    (S : Submodule ℂ V) (hS : S ≤ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V)
    (hK : ∀ k ∈ gl2CongruenceSubgroup q 0, ∀ s ∈ S, k • s ∈ S)
    (hcusp : ∀ v : ↥(LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V), (v : V) ∈ S →
      (∀ t : ZMod q, LocalNewvector.gl2ReductionRep q V (CuspidalType.unipotent q t) v = v) → v = 0)
    {v : V} (hv : v ∈ S) (e n : ℕ) :
    ∑ a ∈ Finset.range (q ^ e * (q * n)), ul q (((q : ℚ_[q]) ^ e)⁻¹ * a) • v = 0 := by
  rw [sum_range_mul_eq]
  have hqe : ((q : ℚ_[q]) ^ e) ≠ 0 := pow_ne_zero _ (q_ne_zero q)
  have h : ∀ i r : ℕ, ul q (((q : ℚ_[q]) ^ e)⁻¹ * ((q ^ e * i + r : ℕ) : ℚ_[q])) • v
      = ul q (((q : ℚ_[q]) ^ e)⁻¹ * r) • ul q (i : ℚ_[q]) • v := by
    intro i r
    rw [← mul_smul, ul_mul_ul]
    congr 2
    push_cast
    field_simp
    ring
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [← Finset.smul_sum, sum_ul_natCast_eq_zero q S hS hK hcusp hv, smul_zero]

private theorem sum_uu_smul_eq_of_norm_le {c : ℚ_[q]} (hc : ‖c‖ ≤ (q : ℝ)⁻¹) {v : V}
    (hv : v ∈ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V) (n : ℕ) :
    ∑ a ∈ Finset.range n, uu q (c * a) • v = (n : ℂ) • v := by
  have h : ∀ a : ℕ, uu q (c * a) • v = v := fun a =>
    smul_eq_self_of_mem q V (uu_mem_K1 q ((norm_mul_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (norm_natCast_le_one q a)).trans hc))) hv
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]

private theorem sum_ul_smul_eq_of_norm_le {c : ℚ_[q]} (hc : ‖c‖ ≤ (q : ℝ)⁻¹) {v : V}
    (hv : v ∈ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V) (n : ℕ) :
    ∑ a ∈ Finset.range n, ul q (c * a) • v = (n : ℂ) • v := by
  have h : ∀ a : ℕ, ul q (c * a) • v = v := fun a =>
    smul_eq_self_of_mem q V (ul_mem_K1 q ((norm_mul_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (norm_natCast_le_one q a)).trans hc))) hv
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]

variable (V)

private def upperSum (c : ℚ_[q]) (n : ℕ) : V →ₗ[ℂ] V :=
  ∑ a ∈ Finset.range n, DistribSMul.toLinearMap ℂ V (uu q (c * a))

private def lowerSum (c : ℚ_[q]) (n : ℕ) : V →ₗ[ℂ] V :=
  ∑ a ∈ Finset.range n, DistribSMul.toLinearMap ℂ V (ul q (c * a))

private theorem upperSum_apply (c : ℚ_[q]) (n : ℕ) (v : V) :
    upperSum q V c n v = ∑ a ∈ Finset.range n, uu q (c * a) • v := by
  simp [upperSum, LinearMap.sum_apply]

private theorem lowerSum_apply (c : ℚ_[q]) (n : ℕ) (v : V) :
    lowerSum q V c n v = ∑ a ∈ Finset.range n, ul q (c * a) • v := by
  simp [lowerSum, LinearMap.sum_apply]

variable {V}

private theorem upperSum_uu_smul (c : ℚ_[q]) (n : ℕ) (x : ℚ_[q]) (t : V) :
    upperSum q V c n (uu q x • t) = uu q x • upperSum q V c n t := by
  rw [upperSum_apply, upperSum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_smul, uu_comm, mul_smul]

private theorem lowerSum_ul_smul (c : ℚ_[q]) (n : ℕ) (y : ℚ_[q]) (t : V) :
    lowerSum q V c n (ul q y • t) = ul q y • lowerSum q V c n t := by
  rw [lowerSum_apply, lowerSum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_smul, ul_comm, mul_smul]

private theorem upperSum_centralGL_smul (c : ℚ_[q]) (n : ℕ) (z : ℚ_[q]ˣ) (t : V) :
    upperSum q V c n (LocalNewvector.centralGL q z • t) = LocalNewvector.centralGL q z • upperSum q V c n t := by
  rw [upperSum_apply, upperSum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_smul, ← centralGL_comm, mul_smul]

private theorem lowerSum_centralGL_smul (c : ℚ_[q]) (n : ℕ) (z : ℚ_[q]ˣ) (t : V) :
    lowerSum q V c n (LocalNewvector.centralGL q z • t) = LocalNewvector.centralGL q z • lowerSum q V c n t := by
  rw [lowerSum_apply, lowerSum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_smul, ← centralGL_comm, mul_smul]

private theorem upperSum_dg_smul (c : ℚ_[q]) (n : ℕ) (d : ℚ_[q]ˣ) (t : V) :
    upperSum q V c n (dg q d • t) = dg q d • upperSum q V (((d⁻¹ : ℚ_[q]ˣ) : ℚ_[q]) * c) n t := by
  rw [upperSum_apply, upperSum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_smul, uu_mul_dg, mul_smul, mul_assoc]

private theorem lowerSum_dg_smul (c : ℚ_[q]) (n : ℕ) (d : ℚ_[q]ˣ) (t : V) :
    lowerSum q V c n (dg q d • t) = dg q d • lowerSum q V ((d : ℚ_[q]) * c) n t := by
  rw [lowerSum_apply, lowerSum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_smul, ul_mul_dg, mul_smul, mul_assoc]

private theorem upperSum_of_norm_le {c : ℚ_[q]} (hc : ‖c‖ ≤ (q : ℝ)⁻¹) (n : ℕ) {w : V}
    (hw : w ∈ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V) : upperSum q V c n w = (n : ℂ) • w := by
  rw [upperSum_apply, sum_uu_smul_eq_of_norm_le q hc hw]

private theorem lowerSum_of_norm_le {c : ℚ_[q]} (hc : ‖c‖ ≤ (q : ℝ)⁻¹) (n : ℕ) {w : V}
    (hw : w ∈ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V) : lowerSum q V c n w = (n : ℂ) • w := by
  rw [lowerSum_apply, sum_ul_smul_eq_of_norm_le q hc hw]

private theorem upperSum_progression_eq_zero
    (S : Submodule ℂ V) (hS : S ≤ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V)
    (hK : ∀ k ∈ gl2CongruenceSubgroup q 0, ∀ s ∈ S, k • s ∈ S)
    (hcusp : ∀ v : ↥(LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V), (v : V) ∈ S →
      (∀ t : ZMod q, LocalNewvector.gl2ReductionRep q V (CuspidalType.unipotent q t) v = v) → v = 0)
    (e n : ℕ) {w : V} (hw : w ∈ S) :
    upperSum q V (((q : ℚ_[q]) ^ e)⁻¹) (q ^ e * (q * n)) w = 0 := by
  rw [upperSum_apply, sum_uu_progression_eq_zero q S hS hK hcusp hw]

private theorem lowerSum_progression_eq_zero
    (S : Submodule ℂ V) (hS : S ≤ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V)
    (hK : ∀ k ∈ gl2CongruenceSubgroup q 0, ∀ s ∈ S, k • s ∈ S)
    (hcusp : ∀ v : ↥(LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V), (v : V) ∈ S →
      (∀ t : ZMod q, LocalNewvector.gl2ReductionRep q V (CuspidalType.unipotent q t) v = v) → v = 0)
    (e n : ℕ) {w : V} (hw : w ∈ S) :
    lowerSum q V (((q : ℚ_[q]) ^ e)⁻¹) (q ^ e * (q * n)) w = 0 := by
  rw [lowerSum_apply, sum_ul_progression_eq_zero q S hS hK hcusp hw]

private theorem val_qu_zpow_inv (m : ℤ) : (((qu q ^ m)⁻¹ : ℚ_[q]ˣ) : ℚ_[q]) = ((q : ℚ_[q]) ^ m)⁻¹ := by
  rw [Units.val_inv_eq_inv_val, val_qu_zpow]

private theorem step_upper_pos (e : ℕ) :
    (((qu q ^ ((e : ℤ) + 1))⁻¹ : ℚ_[q]ˣ) : ℚ_[q]) * (q : ℚ_[q]) = ((q : ℚ_[q]) ^ e)⁻¹ := by
  have hq := q_ne_zero q
  rw [val_qu_zpow_inv, zpow_add_one₀ hq, zpow_natCast, mul_inv, mul_assoc, inv_mul_cancel₀ hq, mul_one]

private theorem norm_step_upper_nonpos {m : ℤ} (hm : m ≤ 0) :
    ‖(((qu q ^ m)⁻¹ : ℚ_[q]ˣ) : ℚ_[q]) * (q : ℚ_[q])‖ ≤ (q : ℝ)⁻¹ := by
  rw [val_qu_zpow_inv, norm_mul, norm_inv, norm_q_zpow, norm_q, ← zpow_neg, neg_neg]
  exact mul_le_of_le_one_left (inv_nonneg.mpr (Nat.cast_nonneg _))
    (zpow_le_one_of_nonpos₀ (one_lt_q_real q).le hm)

private theorem step_lower_zero : ((qu q ^ (0 : ℤ) : ℚ_[q]ˣ) : ℚ_[q]) * (q : ℚ_[q]) = q := by
  rw [zpow_zero, Units.val_one, one_mul]

private theorem step_lower_neg (e : ℕ) :
    ((qu q ^ (-((e : ℤ) + 1)) : ℚ_[q]ˣ) : ℚ_[q]) * (q : ℚ_[q]) = ((q : ℚ_[q]) ^ e)⁻¹ := by
  have hq := q_ne_zero q
  rw [val_qu_zpow, zpow_neg, zpow_add_one₀ hq, zpow_natCast, mul_inv, mul_assoc, inv_mul_cancel₀ hq, mul_one]

omit [Fact q.Prime] in
private theorem pow_split {e N : ℕ} (h : e + 2 ≤ N) : q ^ (N - 1) = q ^ e * (q * q ^ (N - e - 2)) := by
  rw [← pow_succ', ← pow_add]
  congr 1
  omega

private theorem exists_lowerSum_upperSum_smul_mem
    (S : Submodule ℂ V) (hS : S ≤ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V)
    (hK : ∀ k ∈ gl2CongruenceSubgroup q 0, ∀ s ∈ S, k • s ∈ S)
    (hcusp : ∀ v : ↥(LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V), (v : V) ∈ S →
      (∀ t : ZMod q, LocalNewvector.gl2ReductionRep q V (CuspidalType.unipotent q t) v = v) → v = 0)
    (hZ : ∀ z : ℚ_[q]ˣ, ∀ s ∈ S, LocalNewvector.centralGL q z • s ∈ S)
    (g : GL (Fin 2) ℚ_[q]) {s : V} (hs : s ∈ S) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      lowerSum q V (q : ℚ_[q]) (q ^ (N - 1)) (upperSum q V (q : ℚ_[q]) (q ^ (N - 1)) (g • s)) ∈ S := by
  obtain ⟨x, z, m, k, hk, rfl⟩ := exists_iwasawa q g
  have hks : k • s ∈ S := hK k hk s hs
  rcases le_or_gt 1 m with hm | hm
  ·
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, m = (e : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
    refine ⟨e + 2, fun N hN => ?_⟩
    rw [mul_smul, mul_smul, mul_smul, dq, upperSum_uu_smul, upperSum_centralGL_smul, upperSum_dg_smul,
      step_upper_pos, pow_split q hN, upperSum_progression_eq_zero q S hS hK hcusp e _ hks, smul_zero, smul_zero,
      smul_zero, map_zero]
    exact zero_mem _
  · have hm0 : m ≤ 0 := by omega
    by_cases hx : ‖x‖ ≤ (q : ℝ) ^ (-m)
    ·
      have hy : ‖((q : ℚ_[q]) ^ m)⁻¹ * x‖ ≤ 1 := by
        rw [norm_mul, norm_inv, norm_q_zpow]
        have hpos : (0 : ℝ) < (q : ℝ) ^ (-m) := zpow_pos (by exact_mod_cast (Fact.out : q.Prime).pos) _
        rw [inv_mul_le_iff₀ hpos, mul_one]
        exact hx
      have hk' : uu q (((q : ℚ_[q]) ^ m)⁻¹ * x) * k ∈ gl2CongruenceSubgroup q 0 := mul_mem (uu_mem_K0 q hy) hk
      have hs₂ : (uu q (((q : ℚ_[q]) ^ m)⁻¹ * x) * k) • s ∈ S := hK _ hk' s hs
      have hrew : uu q x * LocalNewvector.centralGL q z * dq q m * k
          = LocalNewvector.centralGL q z * dg q (qu q ^ m) * (uu q (((q : ℚ_[q]) ^ m)⁻¹ * x) * k) := by
        rw [← val_qu_zpow_inv, ← mul_assoc, mul_assoc (LocalNewvector.centralGL q z), ← uu_mul_dg, ← mul_assoc,
          ← centralGL_comm, dq]
      obtain ⟨e, he⟩ : ∃ e : ℕ, m = -(e : ℤ) := ⟨(-m).toNat, by omega⟩
      refine ⟨e + 1, fun N hN => ?_⟩
      rw [hrew, mul_smul, mul_smul]
      rcases eq_or_lt_of_le hm0 with h0 | hneg
      ·
        subst h0
        rw [upperSum_centralGL_smul, upperSum_dg_smul, upperSum_of_norm_le q (norm_step_upper_nonpos q hm0) _ (hS hs₂),
          lowerSum_centralGL_smul, lowerSum_dg_smul, step_lower_zero,
          lowerSum_of_norm_le q (norm_q q).le _ (hS (S.smul_mem _ hs₂)), zpow_zero, dg_one, one_smul]
        exact hZ z _ (S.smul_mem _ (S.smul_mem _ hs₂))
      ·
        obtain ⟨e', rfl⟩ : ∃ e' : ℕ, m = -((e' : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
        have he' : e' + 2 ≤ N := by omega
        rw [pow_split q he', upperSum_centralGL_smul, upperSum_dg_smul,
          upperSum_of_norm_le q (norm_step_upper_nonpos q hm0) _ (hS hs₂), lowerSum_centralGL_smul, lowerSum_dg_smul,
          step_lower_neg, lowerSum_progression_eq_zero q S hS hK hcusp e' _ (S.smul_mem _ hs₂), smul_zero, smul_zero]
        exact zero_mem _
    ·
      rw [not_le] at hx
      have hqpos : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hx
        exact (not_lt.mpr (zpow_pos hqpos _).le) hx
      obtain ⟨xu, rfl⟩ : ∃ xu : ℚ_[q]ˣ, (xu : ℚ_[q]) = x := ⟨Units.mk0 x hx0, rfl⟩
      have hkC : kC q xu (qu q ^ m) ∈ gl2CongruenceSubgroup q 0 := by
        refine kC_mem_K0 q ?_
        rw [norm_mul, val_qu_zpow, norm_q_zpow, Units.val_inv_eq_inv_val, norm_inv, ← div_eq_mul_inv,
          div_le_one (norm_pos_iff.mpr xu.ne_zero)]
        exact hx.le
      obtain ⟨m', η, hη, hsplit⟩ := exists_eq_qu_zpow_mul q (xu * xu * (qu q ^ m)⁻¹)

      have hm' : m' < 0 := by
        have hnorm : ‖((qu q ^ m' : ℚ_[q]ˣ) : ℚ_[q])‖ = ‖(xu : ℚ_[q])‖ * (‖(xu : ℚ_[q])‖ / (q : ℝ) ^ (-m)) := by
          have h1 : qu q ^ m' = xu * xu * (qu q ^ m)⁻¹ * η⁻¹ := by rw [hsplit, mul_inv_cancel_right]
          rw [h1, Units.val_mul, Units.val_mul, Units.val_mul, norm_mul, norm_mul, norm_mul, val_qu_zpow_inv,
            norm_inv, norm_q_zpow, Units.val_inv_eq_inv_val, norm_inv, hη, inv_one, mul_one, mul_assoc,
            div_eq_mul_inv]
        have hone : (1 : ℝ) ≤ (q : ℝ) ^ (-m) := one_le_zpow₀ (one_lt_q_real q).le (by omega)
        have hgt : (1 : ℝ) < ‖((qu q ^ m' : ℚ_[q]ˣ) : ℚ_[q])‖ := by
          rw [hnorm]
          have h2 : (1 : ℝ) < ‖(xu : ℚ_[q])‖ := hone.trans_lt hx
          have h3 : (1 : ℝ) < ‖(xu : ℚ_[q])‖ / (q : ℝ) ^ (-m) := by
            rwa [one_lt_div (lt_of_lt_of_le one_pos hone)]
          nlinarith
        by_contra hge
        rw [not_lt] at hge
        rw [val_qu_zpow, norm_q_zpow] at hgt
        exact (not_lt.mpr (zpow_le_one_of_nonpos₀ (one_lt_q_real q).le (neg_nonpos.mpr hge))) hgt
      obtain ⟨e', rfl⟩ : ∃ e' : ℕ, m' = -((e' : ℤ) + 1) := ⟨(-m' - 1).toNat, by omega⟩

      have hlow : uu q (xu : ℚ_[q]) * LocalNewvector.centralGL q z * dg q (qu q ^ m)
          = ul q ((xu⁻¹ : ℚ_[q]ˣ) : ℚ_[q]) * LocalNewvector.centralGL q z
              * LocalNewvector.centralGL q (qu q ^ m * xu⁻¹) * dg q (qu q ^ (-((e' : ℤ) + 1)))
              * (dg q η * kC q xu (qu q ^ m)) := by
        rw [← centralGL_comm q z (uu q _), mul_assoc (LocalNewvector.centralGL q z) (uu q _) (dg q _),
          uu_mul_dg_eq_lower, hsplit, ← dg_mul_dg]
        simp only [← mul_assoc]
        rw [centralGL_comm q z (ul q _)]
      have hK' : dg q η * kC q xu (qu q ^ m) ∈ gl2CongruenceSubgroup q 0 := mul_mem (dg_mem_K0 q hη) hkC
      refine ⟨e' + 2, fun N hN => ?_⟩
      rw [pow_split q hN, mul_smul, mul_smul, mul_smul, dq, upperSum_uu_smul, upperSum_centralGL_smul,
        upperSum_dg_smul, upperSum_of_norm_le q (norm_step_upper_nonpos q hm0) _ (hS hks), ← mul_smul, ← mul_smul,
        hlow, mul_smul, mul_smul, mul_smul, mul_smul, lowerSum_ul_smul, lowerSum_centralGL_smul,
        lowerSum_centralGL_smul, lowerSum_dg_smul, step_lower_neg,
        lowerSum_progression_eq_zero q S hS hK hcusp e' _ (hK _ hK' _ (S.smul_mem _ hks)), smul_zero, smul_zero,
        smul_zero, smul_zero]
      exact zero_mem _

theorem fixed_inf_iSup_map_le
    (S : Submodule ℂ V) (hS : S ≤ LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V)
    (hK : ∀ k ∈ gl2CongruenceSubgroup q 0, ∀ s ∈ S, k • s ∈ S)
    (hcusp : ∀ v : ↥(LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V), (v : V) ∈ S →
      (∀ t : ZMod q, LocalNewvector.gl2ReductionRep q V (CuspidalType.unipotent q t) v = v) → v = 0)
    (hZ : ∀ z : ℚ_[q]ˣ, ∀ s ∈ S, LocalNewvector.centralGL q z • s ∈ S) :
    LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V ⊓
        (⨆ g : GL (Fin 2) ℚ_[q], S.map (DistribSMul.toLinearMap ℂ V g)) ≤ S := by
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hvF, hvU⟩ := hv
  have hP : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      lowerSum q V (q : ℚ_[q]) (q ^ (N - 1)) (upperSum q V (q : ℚ_[q]) (q ^ (N - 1)) v) ∈ S := by
    refine Submodule.iSup_induction (fun g : GL (Fin 2) ℚ_[q] => S.map (DistribSMul.toLinearMap ℂ V g))
      (motive := fun w => ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        lowerSum q V (q : ℚ_[q]) (q ^ (N - 1)) (upperSum q V (q : ℚ_[q]) (q ^ (N - 1)) w) ∈ S)
      hvU (fun g w hw => ?_) ⟨0, fun N _ => by rw [map_zero, map_zero]; exact zero_mem _⟩ ?_
    · obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.1 hw
      rw [DistribSMul.toLinearMap_apply]
      exact exists_lowerSum_upperSum_smul_mem q S hS hK hcusp hZ g hs
    · rintro w₁ w₂ ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
      refine ⟨max N₁ N₂, fun N hN => ?_⟩
      rw [map_add, map_add]
      exact add_mem (h₁ N (le_of_max_le_left hN)) (h₂ N (le_of_max_le_right hN))
  obtain ⟨N₀, hN₀⟩ := hP
  have h := hN₀ N₀ le_rfl
  rw [upperSum_of_norm_le q (norm_q q).le _ hvF, map_smul, lowerSum_of_norm_le q (norm_q q).le _ hvF,
    smul_smul] at h
  have hc : ((q ^ (N₀ - 1) : ℕ) : ℂ) * ((q ^ (N₀ - 1) : ℕ) : ℂ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast pow_ne_zero _ (Fact.out : q.Prime).ne_zero)
      (by exact_mod_cast pow_ne_zero _ (Fact.out : q.Prime).ne_zero)
  exact (Submodule.smul_mem_iff S hc).1 h

end LocalNewvector.CuspidalPartSpanS
p2m_reactivate "P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector.CuspidalPartSpanS"
p2m_reactivate "P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector"

end
p2m_reactivate "P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector.CuspidalPartSpanS"

namespace LocalNewvector p2m_export "LocalNewvector" "fixedSubmodule mem_fixedSubmodule_iff centralGL IsIrreducibleGLRep mem_gl2CongruenceSubgroup_zero_iff gl2ReductionHom gl2ReductionHom_apply_of_coe_eq gl2ReductionHom_surjective smul_mem_fixedSubmodule_gl2CongruenceSubgroup_one_of_mem gl2ReductionRep gl2ReductionRep_gl2ReductionHom_apply" end LocalNewvector
p2m_open_scoped "LocalNewvector" in

theorem LocalNewvector.fixedSubmodule_inf_iSup_map_le_of_cuspidal_on
    (q : ℕ) [Fact q.Prime]
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    (S : Submodule ℂ V)
    (hS : S ≤ LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)
    (hK : ∀ k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 0, ∀ s ∈ S, k • s ∈ S)
    (hcusp : ∀ v : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V), (v : V) ∈ S →
      (∀ t : ZMod q, LocalNewvector.gl2ReductionRep q V (CuspidalType.unipotent q t) v = v) → v = 0)
    (hZ : ∀ z : ℚ_[q]ˣ, ∀ s ∈ S, LocalNewvector.centralGL q z • s ∈ S) :
    LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V ⊓
        (⨆ g : GL (Fin 2) ℚ_[q], S.map (DistribSMul.toLinearMap (R := ℂ) (M := V) g)) ≤ S :=
  LocalNewvector.CuspidalPartSpanS.fixed_inf_iSup_map_le q S hS hK hcusp hZ

p2m_open "Polynomial CuspidalType P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.CuspidalType"

namespace CuspidalType
p2m_export "CuspidalType" "GL2 unipotent diagElem diagElem_val unipotent_val IsCuspidalOfType IsCuspidalOfType.toSubmodule_eq_bot_or_eq_top"
namespace CuspDim
p2m_open "CuspidalType"

variable {q : ℕ} [Fact q.Prime]

theorem unipotent_add (s t : ZMod q) :
    unipotent q (s + t) = unipotent q s * unipotent q t := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, unipotent_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipotent_zero : unipotent q 0 = 1 := by
  apply Units.ext
  ext i j
  simp only [unipotent_val, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp

theorem unipotent_nsmul (n : ℕ) (t : ZMod q) :
    unipotent q (n • t) = unipotent q t ^ n := by
  induction n with
  | zero => rw [zero_smul, unipotent_zero, pow_zero]
  | succ n ih => rw [add_smul, one_smul, unipotent_add, ih, pow_succ]

theorem unipotent_pow_eq_one (t : ZMod q) : unipotent q t ^ q = 1 := by
  rw [← unipotent_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, unipotent_zero]

theorem diagElem_mul_unipotent (a : (ZMod q)ˣ) (t : ZMod q) :
    diagElem q a * unipotent q t = unipotent q ((a : ZMod q) * t) * diagElem q a := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, unipotent_val, diagElem_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_units_mul (a : (ZMod q)ˣ) (t : ZMod q) :
    unipotent q ((a : ZMod q) * t) = diagElem q a * unipotent q t * (diagElem q a)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  exact (diagElem_mul_unipotent a t).symm

theorem aeval_conj {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (e e' x : A) (he : e * e' = 1) (he' : e' * e = 1) (p : R[X]) :
    aeval (e * x * e') p = e * aeval x p * e' := by
  have hpow : ∀ n : ℕ, (e * x * e') ^ n = e * x ^ n * e' := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, mul_one, he]
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc]
      rw [← mul_assoc e' e, he', one_mul]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, add_mul]
  | monomial n c =>
    simp only [aeval_monomial, hpow]
    simp only [← mul_assoc]
    rw [Algebra.commutes c e]

theorem sub_one_le_finrank_of_cuspidal {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) :
    q - 1 ≤ Module.finrank K V := by
  classical
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩
  set A : Module.End K V := ρ (unipotent q 1) with hA

  have hAq : A ^ q = 1 := by rw [hA, ← map_pow, unipotent_pow_eq_one, map_one]

  have hfix : ∀ v : V, A v = v → v = 0 := by
    intro v hv
    apply hcusp v
    intro s
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n • (1 : ZMod q) := ⟨s.val, by rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]⟩
    rw [unipotent_nsmul, map_pow]
    induction n with
    | zero => rw [pow_zero, Module.End.one_apply]
    | succ n ih => rw [pow_succ, Module.End.mul_apply, hv, ih]

  have hΦA : aeval A (cyclotomic q K) = 0 := by
    have hmul : (X - 1 : K[X]) * cyclotomic q K = X ^ q - 1 := by
      rw [mul_comm, cyclotomic_prime_mul_X_sub_one]
    have h1 : (A - 1) * aeval A (cyclotomic q K) = 0 := by
      have := congrArg (aeval A) hmul
      rwa [map_mul, map_sub, aeval_X, map_one, map_sub, map_pow, aeval_X, map_one, hAq,
        sub_self] at this
    ext v
    have hv := congrArg (fun f : Module.End K V => f v) h1
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply, sub_eq_zero] at hv
    rw [LinearMap.zero_apply]
    exact hfix _ hv

  have hAint : IsIntegral K A := Algebra.IsIntegral.isIntegral A
  set g : K[X] := minpoly K A with hg
  have hgΦ : g ∣ cyclotomic q K := minpoly.dvd K A hΦA
  have hgmon : g.Monic := minpoly.monic hAint
  have hexp : ∀ a : (ZMod q)ˣ, g ∣ expand K (a : ZMod q).val g := by
    intro a
    apply minpoly.dvd
    rw [expand_aeval]
    have hconj : A ^ (a : ZMod q).val = ρ (diagElem q a) * A * ρ (diagElem q a)⁻¹ := by
      rw [hA, ← map_pow, ← unipotent_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val,
        unipotent_units_mul a 1, map_mul, map_mul]
    rw [hconj, aeval_conj _ _ _ (by rw [← map_mul, mul_inv_cancel, map_one])
      (by rw [← map_mul, inv_mul_cancel, map_one]), hg, minpoly.aeval, mul_zero, zero_mul]

  have hdeg : q - 1 ≤ g.natDegree := by
    let L := AlgebraicClosure K
    set g' : L[X] := g.map (algebraMap K L) with hg'
    have hg'mon : g'.Monic := hgmon.map _
    have hg'0 : g' ≠ 0 := hg'mon.ne_zero
    obtain ⟨ζ, hζ⟩ : ∃ ζ, g'.IsRoot ζ := IsAlgClosed.exists_root g' (by
      rw [hg', degree_map]; exact (minpoly.degree_pos hAint).ne')
    have hζ1 : ζ ≠ 1 := by
      rintro rfl
      have h1 : g.IsRoot 1 := by
        rw [← isRoot_map_iff (algebraMap K L).injective, map_one]
        exact hζ
      obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_of_isRoot h1).exists_hasEigenvector
      exact hv.2 (hfix v (by rw [hv.apply_eq_smul, one_smul]))
    have hζq : ζ ^ q = 1 := by
      have hX : (X ^ q - 1 : L[X]).IsRoot ζ := by
        apply hζ.dvd
        calc g' ∣ (cyclotomic q K).map (algebraMap K L) := Polynomial.map_dvd _ hgΦ
          _ ∣ (X ^ q - 1 : K[X]).map (algebraMap K L) :=
            Polynomial.map_dvd _ (cyclotomic.dvd_X_pow_sub_one q K)
          _ = X ^ q - 1 := by rw [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
      have := hX.eq_zero
      rwa [eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] at this
    have hord : orderOf ζ = q := orderOf_eq_prime hζq hζ1
    have hprim : IsPrimitiveRoot ζ q := hord ▸ IsPrimitiveRoot.orderOf ζ
    let f : (ZMod q)ˣ → L := fun a => ζ ^ (a : ZMod q).val
    have hf_inj : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      exact Units.ext (ZMod.val_injective q (hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hab))
    have hf_root : ∀ a, f a ∈ g'.roots.toFinset := by
      intro a
      rw [Multiset.mem_toFinset, mem_roots hg'0]
      have hd : g' ∣ expand L (a : ZMod q).val g' := by
        rw [hg', ← map_expand]; exact Polynomial.map_dvd _ (hexp a)
      have := hζ.dvd hd
      rwa [IsRoot, expand_eval] at this
    calc q - 1 = Fintype.card (ZMod q)ˣ := (ZMod.card_units q).symm
      _ = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ]
      _ ≤ g'.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
        exact hf_root a
      _ ≤ Multiset.card g'.roots := Multiset.toFinset_card_le _
      _ ≤ g'.natDegree := card_roots' g'
      _ = g.natDegree := by rw [hg', natDegree_map]

  calc q - 1 ≤ g.natDegree := hdeg
    _ ≤ A.charpoly.natDegree :=
        natDegree_le_of_dvd (minpoly.dvd K A (LinearMap.aeval_self_charpoly A)) (LinearMap.charpoly_monic A).ne_zero
    _ = Module.finrank K V := LinearMap.charpoly_natDegree A

theorem toSubmodule_eq_bot_or_eq_top_of_cuspidal_of_finrank_eq {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (GL2 q) V)
    (hfin : Module.finrank K V = q - 1)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0)
    (W : Subrepresentation ρ) :
    W.toSubmodule = ⊥ ∨ W.toSubmodule = ⊤ := by
  classical
  by_cases hW : W.toSubmodule = ⊥
  · exact Or.inl hW
  right
  haveI : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hW
  have hcuspW : ∀ v : W.toSubmodule, (∀ t : ZMod q, W.toRepresentation (unipotent q t) v = v) → v = 0 := by
    intro v hv
    apply Subtype.ext
    apply hcusp
    intro t
    exact congrArg Subtype.val (hv t)
  have hle : q - 1 ≤ Module.finrank K W.toSubmodule := sub_one_le_finrank_of_cuspidal W.toRepresentation hcuspW
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  rw [hfin]; exact hle

private theorem _root_.CuspidalType.IsCuspidalOfType.toSubmodule_eq_bot_or_eq_top {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {ρ : Representation K (GL2 q) V} (h : IsCuspidalOfType θ ρ)
    (W : Subrepresentation ρ) :
    W.toSubmodule = ⊥ ∨ W.toSubmodule = ⊤ :=
  toSubmodule_eq_bot_or_eq_top_of_cuspidal_of_finrank_eq ρ h.finrank_eq h.cuspidal W

p2m_alias "P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.CuspidalType.IsCuspidalOfType.toSubmodule_eq_bot_or_eq_top" "CuspidalType.IsCuspidalOfType.toSubmodule_eq_bot_or_eq_top"
end CuspidalType.CuspDim
p2m_reactivate "P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector.CuspidalPartSpanS"
p2m_reactivate "P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector.CuspidalPartSpanS"

namespace LocalNewvector
p2m_export "LocalNewvector" "fixedSubmodule mem_fixedSubmodule_iff centralGL IsIrreducibleGLRep mem_gl2CongruenceSubgroup_zero_iff gl2ReductionHom gl2ReductionHom_apply_of_coe_eq gl2ReductionHom_surjective smul_mem_fixedSubmodule_gl2CongruenceSubgroup_one_of_mem gl2ReductionRep gl2ReductionRep_gl2ReductionHom_apply"
namespace TypeUniqueness
p2m_open "LocalNewvector"

p2m_open "FLT.SmoothVectors CuspidalType P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.CuspidalType"

noncomputable section

variable (q : ℕ) [Fact q.Prime]
variable (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
  [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]

local notation "Fix" => LocalNewvector.fixedSubmodule (gl2CongruenceSubgroup q 1) V
local notation "ρV" => LocalNewvector.gl2ReductionRep q V

def pu : ℚ_[q]ˣ := Units.mk0 (q : ℚ_[q]) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)

def zp : GL (Fin 2) ℚ_[q] := LocalNewvector.centralGL q (pu q)

theorem centralGL_mem_center (z : ℚ_[q]ˣ) :
    LocalNewvector.centralGL q z ∈ Subgroup.center (GL (Fin 2) ℚ_[q]) := by
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  exact ⟨(z : ℚ_[q]), rfl⟩

theorem centralGL_comm (z : ℚ_[q]ˣ) (g : GL (Fin 2) ℚ_[q]) :
    LocalNewvector.centralGL q z * g = g * LocalNewvector.centralGL q z :=
  ((Subgroup.mem_center_iff.1 (centralGL_mem_center q z)) g).symm

theorem centralGL_smul_mem_fixed (z : ℚ_[q]ˣ) {v : V} (hv : v ∈ Fix) :
    LocalNewvector.centralGL q z • v ∈ Fix := by
  rw [LocalNewvector.mem_fixedSubmodule_iff] at hv ⊢
  intro g hg
  rw [← mul_smul, ← centralGL_comm, mul_smul, hv g hg]

theorem centralGL_mem_K0 {u : ℚ_[q]ˣ} (hu : ‖(u : ℚ_[q])‖ = 1) :
    LocalNewvector.centralGL q u ∈ gl2CongruenceSubgroup q 0 := by
  rw [LocalNewvector.mem_gl2CongruenceSubgroup_zero_iff]
  have hval : ∀ (w : ℚ_[q]ˣ) (i j : Fin 2),
      ((LocalNewvector.centralGL q w : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j
        = if i = j then (w : ℚ_[q]) else 0 := by
    intro w i j
    show (algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q]) (w : ℚ_[q])) i j = _
    rw [Matrix.algebraMap_matrix_apply]
    rfl
  have hinv : ‖((u⁻¹ : ℚ_[q]ˣ) : ℚ_[q])‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]
  constructor
  · intro i j
    rw [hval]
    split_ifs
    · exact hu.le
    · rw [norm_zero]; exact zero_le_one
  · intro i j
    rw [← map_inv, hval]
    split_ifs
    · exact hinv.le
    · rw [norm_zero]; exact zero_le_one

theorem exists_eq_pu_zpow_mul (y : ℚ_[q]ˣ) :
    ∃ (m : ℤ) (u : ℚ_[q]ˣ), ‖(u : ℚ_[q])‖ = 1 ∧ y = pu q ^ m * u := by
  have hy : (y : ℚ_[q]) ≠ 0 := y.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℤ, ‖(y : ℚ_[q])‖ = (q : ℝ) ^ (-m) :=
    ⟨(y : ℚ_[q]).valuation, Padic.norm_eq_zpow_neg_valuation hy⟩
  refine ⟨m, (pu q ^ m)⁻¹ * y, ?_, by rw [mul_inv_cancel_left]⟩
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, norm_mul, norm_inv]
  show ‖(q : ℚ_[q]) ^ m‖⁻¹ * ‖(y : ℚ_[q])‖ = 1
  rw [Padic.norm_p_zpow, hm, inv_mul_cancel₀]
  exact (zpow_pos (by exact_mod_cast (Fact.out : q.Prime).pos) _).ne'

section Module

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (GL (Fin 2) (ZMod q)) W)

def homSpace : Submodule ℂ (W →ₗ[ℂ] Fix) where
  carrier := {φ | ∀ (g : GL (Fin 2) (ZMod q)) (w : W), φ (σ g w) = ρV g (φ w)}
  add_mem' := by
    intro φ ψ hφ hψ g w
    simp only [Set.mem_setOf_eq, LinearMap.add_apply, map_add] at *
    rw [hφ, hψ]
  zero_mem' := by
    intro g w
    simp
  smul_mem' := by
    intro c φ hφ g w
    simp only [Set.mem_setOf_eq, LinearMap.smul_apply, map_smul] at *
    rw [hφ]

theorem mem_homSpace {φ : W →ₗ[ℂ] Fix} :
    φ ∈ homSpace q V σ ↔ ∀ (g : GL (Fin 2) (ZMod q)) (w : W), φ (σ g w) = ρV g (φ w) :=
  Iff.rfl

def postZ : (W →ₗ[ℂ] Fix) →ₗ[ℂ] (W →ₗ[ℂ] Fix) where
  toFun φ :=
    { toFun := fun w => ⟨zp q • (φ w : V), centralGL_smul_mem_fixed q V (pu q) (φ w).2⟩
      map_add' := by intro a b; apply Subtype.ext; simp [smul_add]
      map_smul' := by
        intro c a; apply Subtype.ext
        simp only [map_smul, Submodule.coe_smul_of_tower, RingHom.id_apply]
        exact smul_comm _ _ _ }
  map_add' := by intro φ ψ; ext w; simp [smul_add]
  map_smul' := by
    intro c φ; ext w
    simp only [LinearMap.smul_apply, Submodule.coe_smul_of_tower, LinearMap.coe_mk, AddHom.coe_mk,
      RingHom.id_apply]
    exact smul_comm _ _ _

theorem coe_postZ_apply (φ : W →ₗ[ℂ] Fix) (w : W) :
    ((postZ q V φ w : Fix) : V) = zp q • (φ w : V) := rfl

theorem coe_gl2ReductionRep_centralGL_smul (z : ℚ_[q]ˣ) (g : GL (Fin 2) (ZMod q)) (v : Fix) :
    ((ρV g ⟨LocalNewvector.centralGL q z • (v : V), centralGL_smul_mem_fixed q V z v.2⟩ : Fix) : V)
      = LocalNewvector.centralGL q z • ((ρV g v : Fix) : V) := by
  obtain ⟨k, rfl⟩ := LocalNewvector.gl2ReductionHom_surjective q g
  rw [LocalNewvector.gl2ReductionRep_gl2ReductionHom_apply, LocalNewvector.gl2ReductionRep_gl2ReductionHom_apply]
  simp only
  rw [← mul_smul, ← centralGL_comm, mul_smul]

theorem postZ_mem_homSpace {φ : W →ₗ[ℂ] Fix} (hφ : φ ∈ homSpace q V σ) : postZ q V φ ∈ homSpace q V σ := by
  intro g w
  apply Subtype.ext
  rw [coe_postZ_apply, hφ g w, zp, ← coe_gl2ReductionRep_centralGL_smul]
  rfl

def T : Module.End ℂ (homSpace q V σ) :=
  (postZ q V).restrict fun φ hφ => postZ_mem_homSpace q V σ hφ

theorem coe_T_apply (φ : homSpace q V σ) (w : W) : (((T q V σ φ : homSpace q V σ) : W →ₗ[ℂ] Fix) w : V) = zp q • ((φ : W →ₗ[ℂ] Fix) w : V) :=
  rfl

end Module
p2m_reactivate "P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector.CuspidalPartSpanS"

theorem isCuspidalOfType_gl2ReductionRep
    [FiniteDimensional ℂ Fix]
    (hV : LocalNewvector.IsIrreducibleGLRep q V)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (GL (Fin 2) (ZMod q)) W) (θ : (GaloisField q 2)ˣ →* ℂˣ)
    (hσ : IsCuspidalOfType θ σ)
    (ι : W →ₗ[ℂ] Fix) (hι : Function.Injective ι)
    (hιeq : ∀ (g : GL (Fin 2) (ZMod q)) (w : W), ι (σ g w) = ρV g (ι w)) :
    IsCuspidalOfType θ (ρV) := by
  classical
  have hq : q.Prime := Fact.out

  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ℂ)
    (by rw [hσ.finrank_eq]; have := hq.two_le; omega)

  haveI : FiniteDimensional ℂ (homSpace q V σ) := FiniteDimensional.finiteDimensional_submodule _
  have hι_mem : ι ∈ homSpace q V σ := hιeq
  haveI : Nontrivial (homSpace q V σ) := by
    refine ⟨⟨⟨ι, hι_mem⟩, 0, ?_⟩⟩
    intro h
    have h' : ι = 0 := congrArg Subtype.val h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact hw (hι (by rw [h', LinearMap.zero_apply, map_zero]))

  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue (K := ℂ) (V := homSpace q V σ) (T q V σ)
  obtain ⟨φ₁, hφ₁⟩ := hlam.exists_hasEigenvector
  have hφ₁T : T q V σ φ₁ = lam • φ₁ := hφ₁.apply_eq_smul
  have hφ₁0 : (φ₁ : W →ₗ[ℂ] Fix) ≠ 0 := fun h => hφ₁.2 (Subtype.ext h)
  set φ : W →ₗ[ℂ] Fix := (φ₁ : W →ₗ[ℂ] Fix) with hφdef
  have hφeq : ∀ (g : GL (Fin 2) (ZMod q)) (w : W), φ (σ g w) = ρV g (φ w) := φ₁.2
  have hφz : ∀ w : W, zp q • (φ w : V) = lam • (φ w : V) := by
    intro w
    have := congrArg (fun ψ : homSpace q V σ => (((ψ : homSpace q V σ) : W →ₗ[ℂ] Fix) w : V)) hφ₁T
    simpa [coe_T_apply] using this

  have hφinj : Function.Injective φ := by
    let Kr : Subrepresentation σ :=
      { toSubmodule := LinearMap.ker φ
        apply_mem_toSubmodule := fun g w hw => by
          rw [LinearMap.mem_ker] at hw ⊢
          rw [hφeq, hw, map_zero] }
    rcases CuspidalType.CuspDim.toSubmodule_eq_bot_or_eq_top_of_cuspidal_of_finrank_eq σ hσ.finrank_eq hσ.cuspidal Kr with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exfalso
      apply hφ₁0
      ext w
      have : w ∈ LinearMap.ker φ := by rw [show LinearMap.ker φ = ⊤ from h]; trivial
      rw [LinearMap.mem_ker] at this
      rw [this]; rfl

  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hφ₁0
    ext w
    have h1 := hφz w
    rw [h0, zero_smul] at h1
    have h2 : (φ w : V) = 0 := by
      have := congrArg (fun v => (zp q)⁻¹ • v) h1
      simpa using this
    rw [LinearMap.zero_apply]
    exact_mod_cast h2

  let S : Submodule ℂ V := (LinearMap.range φ).map (Submodule.subtype Fix)
  have hS : S ≤ Fix := by
    rintro _ ⟨v, -, rfl⟩; exact v.2
  have hmemS : ∀ w : W, ((φ w : Fix) : V) ∈ S := fun w => ⟨φ w, ⟨w, rfl⟩, rfl⟩
  have hSex : ∀ {s : V}, s ∈ S → ∃ w : W, ((φ w : Fix) : V) = s := by
    rintro s ⟨v, ⟨w, rfl⟩, rfl⟩; exact ⟨w, rfl⟩
  have hK : ∀ k ∈ gl2CongruenceSubgroup q 0, ∀ s ∈ S, k • s ∈ S := by
    intro k hk s hs
    obtain ⟨w, rfl⟩ := hSex hs
    have := hφeq (LocalNewvector.gl2ReductionHom q ⟨k, hk⟩) w
    have h2 := congrArg Subtype.val this
    rw [LocalNewvector.gl2ReductionRep_gl2ReductionHom_apply] at h2
    rw [← h2]
    exact hmemS _
  have hZp : ∀ s ∈ S, zp q • s ∈ S := by
    intro s hs
    obtain ⟨w, rfl⟩ := hSex hs
    rw [hφz]
    exact S.smul_mem _ (hmemS w)
  have hZpinv : ∀ s ∈ S, (zp q)⁻¹ • s ∈ S := by
    intro s hs
    obtain ⟨w, rfl⟩ := hSex hs
    have h1 : (zp q)⁻¹ • ((φ w : Fix) : V) = lam⁻¹ • ((φ w : Fix) : V) := by
      rw [inv_smul_eq_iff, smul_comm, hφz, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    rw [h1]
    exact S.smul_mem _ (hmemS w)
  have hZpow : ∀ (m : ℤ), ∀ s ∈ S, (zp q) ^ m • s ∈ S := by
    intro m
    induction m using Int.induction_on with
    | zero => intro s hs; rwa [zpow_zero, one_smul]
    | succ n ih => intro s hs; rw [zpow_add_one, mul_smul]; exact ih _ (hZp s hs)
    | pred n ih => intro s hs; rw [zpow_sub_one, mul_smul]; exact ih _ (hZpinv s hs)
  have hZ : ∀ z : ℚ_[q]ˣ, ∀ s ∈ S, LocalNewvector.centralGL q z • s ∈ S := by
    intro z s hs
    obtain ⟨m, u, hu, rfl⟩ := exists_eq_pu_zpow_mul q z
    rw [map_mul, map_zpow, mul_smul]
    exact hZpow m _ (hK _ (centralGL_mem_K0 q hu) _ hs)
  have hcuspS : ∀ v : Fix, (v : V) ∈ S →
      (∀ t : ZMod q, ρV (CuspidalType.unipotent q t) v = v) → v = 0 := by
    intro v hv hfix
    obtain ⟨w, hw⟩ := hSex hv
    have hvw : φ w = v := Subtype.ext hw
    subst hvw
    have hw0 : w = 0 := hσ.cuspidal w fun t => hφinj (by rw [hφeq, hfix t])
    rw [hw0, map_zero]

  have hle := LocalNewvector.fixedSubmodule_inf_iSup_map_le_of_cuspidal_on q V S hS hK hcuspS hZ

  let Tsp : Submodule ℂ V := ⨆ g : GL (Fin 2) ℚ_[q], S.map (DistribSMul.toLinearMap (R := ℂ) (M := V) g)
  have hTst : ∀ (g : GL (Fin 2) ℚ_[q]) (v : V), v ∈ Tsp → g • v ∈ Tsp := by
    intro g v hv
    refine Submodule.iSup_induction (fun g' : GL (Fin 2) ℚ_[q] => S.map (DistribSMul.toLinearMap ℂ V g'))
      (motive := fun v => g • v ∈ Tsp) hv (fun g' v hv' => ?_)
      (by show g • (0 : V) ∈ Tsp; rw [smul_zero]; exact zero_mem _)
      (fun a b ha hb => by show g • (a + b) ∈ Tsp; rw [smul_add]; exact add_mem ha hb)
    show g • v ∈ Tsp
    obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.1 hv'
    rw [DistribSMul.toLinearMap_apply, ← mul_smul]
    exact Submodule.mem_iSup_of_mem (g * g') (Submodule.mem_map_of_mem (f := DistribSMul.toLinearMap ℂ V (g * g')) hs)
  have hST : S ≤ Tsp := by
    intro s hs
    have := Submodule.mem_iSup_of_mem (p := fun g' : GL (Fin 2) ℚ_[q] => S.map (DistribSMul.toLinearMap ℂ V g'))
      1 (Submodule.mem_map_of_mem (f := DistribSMul.toLinearMap ℂ V (1 : GL (Fin 2) ℚ_[q])) hs)
    rwa [DistribSMul.toLinearMap_apply, one_smul] at this
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  have hS0 : ((φ w₀ : Fix) : V) ≠ 0 := by
    intro h
    apply hw₀
    apply hφinj
    rw [map_zero]
    exact Subtype.ext h
  have hTtop : Tsp = ⊤ := by
    rcases hV.2 Tsp hTst with h | h
    · exfalso
      exact hS0 ((Submodule.eq_bot_iff _).1 h _ (hST (hmemS w₀)))
    · exact h
  have hFixS : ∀ v : Fix, (v : V) ∈ S := by
    intro v
    have hvT : (v : V) ∈ Tsp := by rw [hTtop]; exact Submodule.mem_top
    exact hle ⟨v.2, hvT⟩

  have hφsurj : Function.Surjective φ := by
    intro v
    obtain ⟨w, hw⟩ := hSex (hFixS v)
    exact ⟨w, Subtype.ext hw⟩
  let e : W ≃ₗ[ℂ] Fix := LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  exact hσ.of_linearEquiv e (fun g w => hφeq g w)

end
p2m_reactivate "P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector.CuspidalPartSpanS"

end LocalNewvector.TypeUniqueness
p2m_reactivate "P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector.CuspidalPartSpanS"
p2m_reactivate "P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.LocalNewvector.CuspidalPartSpanS"

theorem solution
    (q : ℕ) [Fact q.Prime]
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (hV : LocalNewvector.IsIrreducibleGLRep q V) (θ : (GaloisField q 2)ˣ →* ℂˣ)
    {X : Type*} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] {ρ : Representation ℂ (CuspidalType.GL2 q) X}
    (hρ : CuspidalType.IsCuspidalOfType θ ρ)
    (φ : X →ₗ[ℂ] ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V))
    (hφ : ∀ g x, φ (ρ g x) = LocalNewvector.gl2ReductionRep q V g (φ x)) (hφinj : Function.Injective φ) :
    CuspidalType.IsCuspidalOfType θ (LocalNewvector.gl2ReductionRep q V) :=
  LocalNewvector.TypeUniqueness.isCuspidalOfType_gl2ReductionRep q V hV ρ θ hρ φ hφinj hφ

end S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType
end P2MW
export P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType (solution)
