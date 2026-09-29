-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchR.eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/7eec26df-c795-5fd0-8f27-ed1fb0f15783

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchR_eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det

set_option autoImplicit false

noncomputable section

namespace Ws1
namespace P1

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm Matrix

def rot (p q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![p, q; -q, p]

theorem det_rot (p q : ℝ) (h : p ^ 2 + q ^ 2 = 1) : (rot p q).det = 1 := by
  rw [rot, Matrix.det_fin_two_of]; nlinarith [h]

def rotGL (p q : ℝ) (h : p ^ 2 + q ^ 2 = 1) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rot p q) (by rw [det_rot p q h]; exact one_ne_zero)

theorem coe_rotGL (p q : ℝ) (h : p ^ 2 + q ^ 2 = 1) : ((rotGL p q h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rot p q := rfl

theorem rotGL_mem (p q : ℝ) (h : p ^ 2 + q ^ 2 = 1) : rotGL p q h ∈ rowIsometrySubgroup₀ ℝ := by
  refine (mem_rowIsometrySubgroup₀_iff ℝ).mpr ⟨by rw [coe_rotGL, det_rot p q h], ?_, ?_⟩
  · rw [coe_rotGL, det_rot p q h, norm_one]
  · intro x y
    simp only [coe_rotGL, rot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    nlinarith [h]

theorem main (A B : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (k : ℤ) (e z : ℂ)
    (hAN : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → A (ArchR.unip t * x) = ArchR.psi t * A x)
    (hBN : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → B (ArchR.unip t * x) = ArchR.psi t * B x)
    (hAZ : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → A (t • x) = ((t : ℂ) ^ e) * A x)
    (hBZ : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → B (t • x) = ((t : ℂ) ^ e) * B x)
    (hAK : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      A ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * A (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hBK : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      B ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * B (x : Matrix (Fin 2) (Fin 2) ℝ))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (htor : ∀ y : ℝ, 0 < y →
      A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = z * B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < ε * x.det) :
    A x = z * B x := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεabs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hdet : x.det ≠ 0 := by intro h; rw [h, mul_zero] at hx; exact lt_irrefl _ hx

  set c := x 1 0 with hc
  set d := x 1 1 with hd
  set ρ := Real.sqrt (c ^ 2 + d ^ 2) with hρ
  have hcd : 0 < c ^ 2 + d ^ 2 := by
    by_contra h
    push Not at h
    have hc0 : c = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    have hd0 : d = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    apply hdet
    rw [Matrix.det_fin_two, ← hc, ← hd, hc0, hd0]; ring
  have hρpos : 0 < ρ := Real.sqrt_pos.mpr hcd
  have hρsq : ρ ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt hcd.le
  have hρ0 : ρ ≠ 0 := hρpos.ne'

  set p₁ := d / ρ with hp₁
  set q₁ := -c / ρ with hq₁
  have hpq : p₁ ^ 2 + q₁ ^ 2 = 1 := by
    rw [hp₁, hq₁]
    field_simp
    linarith [hρsq]
  have hc1 : c = -(ρ * q₁) := by rw [hq₁]; field_simp
  have hd1 : d = ρ * p₁ := by rw [hp₁]; field_simp
  set r := rotGL p₁ q₁ hpq with hr

  set a' := x 0 0 * p₁ + x 0 1 * q₁ with ha'
  set b' := x 0 1 * p₁ - x 0 0 * q₁ with hb'
  have hxr : x = (!![a', b'; 0, ρ] : Matrix (Fin 2) (Fin 2) ℝ) * rot p₁ q₁ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [rot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · rw [ha', hb']; linear_combination (-(x 0 0)) * hpq
    · rw [ha', hb']; linear_combination (-(x 0 1)) * hpq
    · show x 1 0 = _
      rw [← hc, hc1]; ring
    · show x 1 1 = _
      rw [← hd, hd1]; ring
  have hdetx : x.det = ρ * a' := by
    rw [Matrix.det_fin_two, ← hc, ← hd, hc1, hd1, ha']; ring

  have ha'pos : 0 < ε * a' := by
    have : 0 < ρ * (ε * a') := by rw [mul_left_comm, ← hdetx]; exact hx
    exact pos_of_mul_pos_right this hρpos.le

  have ha'0 : a' ≠ 0 := by intro h; rw [h, mul_zero] at ha'pos; exact lt_irrefl _ ha'pos
  have habs : |a'| = ε * a' := by
    rcases hε with rfl | rfl
    · rw [one_mul] at ha'pos ⊢; exact abs_of_pos ha'pos
    · have : a' < 0 := by linarith
      rw [abs_of_neg this]; ring
  set y := |a'| / ρ with hy
  have hypos : 0 < y := div_pos (abs_pos.mpr ha'0) hρpos
  set lam := Real.sqrt (|a'| * ρ) with hlam
  have hlampos : 0 < lam := Real.sqrt_pos.mpr (mul_pos (abs_pos.mpr ha'0) hρpos)
  have hsy : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hypos).ne'
  have h1 : lam * Real.sqrt y = |a'| := by
    rw [hlam, hy, ← Real.sqrt_mul (mul_nonneg (abs_nonneg _) hρpos.le), show |a'| * ρ * (|a'| / ρ) = |a'| ^ 2 by
      field_simp]
    exact Real.sqrt_sq (abs_nonneg _)
  have h2 : lam * (Real.sqrt y)⁻¹ = ρ := by
    have : lam * lam = |a'| * ρ := Real.mul_self_sqrt (mul_nonneg (abs_nonneg _) hρpos.le)
    field_simp
    nlinarith [h1, this, abs_pos.mpr ha'0]
  set s := b' / ρ with hs
  have hP : (!![a', b'; 0, ρ] : Matrix (Fin 2) (Fin 2) ℝ) =
      ArchR.unip s * (lam • (!![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [ArchR.unip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.zero_eta, Fin.mk_one, Fin.isValue]
    ·
      have : lam * (ε * Real.sqrt y) = a' := by
        rw [mul_left_comm, h1, habs, ← mul_assoc, hε2, one_mul]
      rw [this]; ring
    · rw [h2, hs]; field_simp; ring
    · ring
    · rw [h2]; ring

  have hray : (!![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; field_simp; rcases hε with rfl | rfl <;> norm_num
  have hsm : (lam • (!![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := by
    rw [Matrix.det_smul, Fintype.card_fin]; exact mul_ne_zero (pow_ne_zero _ hlampos.ne') hray
  have hPdet : (!![a', b'; 0, ρ] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; simp [ha'0, hρ0]

  set X := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hPdet with hX
  have hxGL : x = ((X * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Units.val_mul, hX, hr, coe_rotGL]; exact hxr

  have hA : A x = (archWeightCharℝ k ⟨r, rotGL_mem p₁ q₁ hpq⟩ : ℂ) * (ArchR.psi s * (((lam : ℂ) ^ e) *
      A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) := by
    rw [hxGL, hAK ⟨r, rotGL_mem p₁ q₁ hpq⟩ X]
    congr 1
    show A (!![a', b'; 0, ρ]) = _
    rw [hP, hAN s _ hsm, hAZ lam _ hlampos hray]
  have hB : B x = (archWeightCharℝ k ⟨r, rotGL_mem p₁ q₁ hpq⟩ : ℂ) * (ArchR.psi s * (((lam : ℂ) ^ e) *
      B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) := by
    rw [hxGL, hBK ⟨r, rotGL_mem p₁ q₁ hpq⟩ X]
    congr 1
    show B (!![a', b'; 0, ρ]) = _
    rw [hP, hBN s _ hsm, hBZ lam _ hlampos hray]
  rw [hA, hB, htor y hypos]
  ring

end Ws1.P1

end

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse

theorem solution
    (A B : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (k : ℤ) (e z : ℂ)
    (hAN : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → A (ArchR.unip t * x) = ArchR.psi t * A x)
    (hBN : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → B (ArchR.unip t * x) = ArchR.psi t * B x)
    (hAZ : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → A (t • x) = ((t : ℂ) ^ e) * A x)
    (hBZ : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → B (t • x) = ((t : ℂ) ^ e) * B x)
    (hAK : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      A ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * A (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hBK : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      B ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * B (x : Matrix (Fin 2) (Fin 2) ℝ))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (htor : ∀ y : ℝ, 0 < y →
      A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = z * B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < ε * x.det) :
    A x = z * B x :=
  Ws1.P1.main A B k e z hAN hBN hAZ hBZ hAK hBK ε hε htor x hx

end S_LanglandsTunnell_Converse_ArchR_eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchR_eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det (solution)
