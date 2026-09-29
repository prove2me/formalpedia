-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumR.continuousOn_and_exists_ne_zero_W_diagOne_of_weightZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/094b27c3-e32c-5670-a5e9-8d1b1d4aa6e1

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_continuousOn_and_exists_ne_zero_W_diagOne_of_weightZero

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

namespace Ws23TorusNZ

open LanglandsTunnell.Converse.ArchR

noncomputable def rotM (c d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![d / Real.sqrt (c ^ 2 + d ^ 2), -c / Real.sqrt (c ^ 2 + d ^ 2); c / Real.sqrt (c ^ 2 + d ^ 2), d / Real.sqrt (c ^ 2 + d ^ 2)]

theorem sqrt_pos_of {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : 0 < Real.sqrt (c ^ 2 + d ^ 2) := by
  apply Real.sqrt_pos.2
  rcases h with h | h
  · have := sq_pos_of_ne_zero h; positivity
  · have := sq_pos_of_ne_zero h; positivity

theorem det_rotM {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : (rotM c d).det = 1 := by
  have hr := sqrt_pos_of h
  have hr2 : Real.sqrt (c ^ 2 + d ^ 2) ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)
  rw [rotM, Matrix.det_fin_two_of]
  field_simp
  linarith [hr2]

noncomputable def rotGL {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotM c d) (by rw [det_rotM h]; exact one_ne_zero)

theorem rotGL_coe {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : ((rotGL h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM c d := rfl

theorem rotGL_mem {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : rotGL h ∈ rowIsometrySubgroup₀ ℝ := by
  have hr := sqrt_pos_of h
  have hr2 : Real.sqrt (c ^ 2 + d ^ 2) ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨by rw [rotGL_coe, det_rotM h], ?_, ?_⟩
  · rw [rotGL_coe, det_rotM h, norm_one]
  · intro x y
    simp only [rotGL_coe, rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    field_simp
    linear_combination (-(x ^ 2 + y ^ 2)) * hr2

theorem archWeightCharℝ_zero (r : rowIsometrySubgroup₀ ℝ) : ((archWeightCharℝ 0 r : ℂˣ) : ℂ) = 1 := by
  show ((((archWeightOneℝ r) ^ (0 : ℤ)) : ℂˣ) : ℂ) = 1
  rw [zpow_zero, Units.val_one]

theorem continuousOn_torus {P : RealArchParam} (D : ArchDatumR P) :
    ContinuousOn (fun τ : ℝ => D.W (diagOne τ)) {τ | τ ≠ 0} := by
  have hc : Continuous fun τ : ℝ => (fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j : Fin 2 → Fin 2 → ℝ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hmaps : Set.MapsTo (fun τ : ℝ => (fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j : Fin 2 → Fin 2 → ℝ))
      {τ | τ ≠ 0} glSet := by
    intro τ hτ
    show (Matrix.of fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j).det ≠ 0
    rw [Matrix.det_fin_two]
    simpa using hτ
  have h := D.smooth.continuousOn.comp hc.continuousOn hmaps
  refine h.congr fun τ _ => ?_
  show D.W (diagOne τ) = D.W (Matrix.of fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)
  rfl

theorem exists_torus_ne_zero {P : RealArchParam} (D : ArchDatumR P)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ 0 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) :
    ∃ τ : ℝ, τ ≠ 0 ∧ D.W (diagOne τ) ≠ 0 := by
  obtain ⟨g, hg⟩ := hDnz
  set G : Matrix (Fin 2) (Fin 2) ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) with hG
  set c : ℝ := G 1 0 with hc
  set d : ℝ := G 1 1 with hd
  have hdet : G.det ≠ 0 := by
    rw [hG]; exact (Matrix.isUnits_det_units g).ne_zero
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet
    rw [Matrix.det_fin_two, ← hc, ← hd, h.1, h.2]; ring
  set r : ℝ := Real.sqrt (c ^ 2 + d ^ 2) with hr
  have hr0 : 0 < r := sqrt_pos_of hcd
  have hr2 : r ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)

  set α : ℝ := (G 0 0 * d - G 0 1 * c) / r with hα
  set β : ℝ := (G 0 0 * c + G 0 1 * d) / r with hβ
  set Xm : Matrix (Fin 2) (Fin 2) ℝ := !![α, β; 0, r] with hXm
  have hXrot : Xm * rotM c d = G := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, hα, hβ, ← hr]
      field_simp
      linear_combination (-(G 0 0)) * hr2
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, hα, hβ, ← hr]
      field_simp
      linear_combination (-(G 0 1)) * hr2
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, ← hr, ← hc]
      field_simp
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, ← hr, ← hd]
      field_simp
  have hαr : α * r ≠ 0 := by
    have h1 : Xm.det = α * r := by rw [hXm, Matrix.det_fin_two_of]; ring
    have h2 : Xm.det * (rotM c d).det = G.det := by rw [← Matrix.det_mul, hXrot]
    rw [det_rotM hcd, mul_one, h1] at h2
    rw [h2]; exact hdet
  have hα0 : α ≠ 0 := fun h => hαr (by rw [h, zero_mul])
  set Xg : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero Xm
    (by rw [hXm, Matrix.det_fin_two_of]; simpa using hαr) with hXg
  have hXg_coe : ((Xg : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Xm := rfl

  have h1 : D.W G = D.W Xm := by
    have h := hDW ⟨rotGL hcd, rotGL_mem hcd⟩ Xg
    rw [archWeightCharℝ_zero, one_mul, hXg_coe] at h
    rw [← h]
    congr 1
    rw [Units.val_mul, hXg_coe]
    exact hXrot.symm

  have hXm_eq : Xm = r • (unip (β / r) * diagOne (α / r)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hXm, unip, diagOne, Matrix.smul_apply] <;>
      field_simp
  have h2 : D.W Xm = centralChar P r * ((|r| : ℝ) : ℂ) * (psi (β / r) * D.W (diagOne (α / r))) := by
    rw [hXm_eq, D.central_law r _ hr0.ne', D.unip_law]
  refine ⟨α / r, div_ne_zero hα0 hr0.ne', fun h0 => hg ?_⟩
  show D.W G = 0
  rw [h1, h2, h0, mul_zero, mul_zero]

end Ws23TorusNZ

open Ws23TorusNZ LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchR in
theorem solution
    {P : RealArchParam} (D : ArchDatumR P)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ 0 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) :
    ContinuousOn (fun τ : ℝ => D.W (ArchR.diagOne τ)) {τ : ℝ | τ ≠ 0} ∧
      (∃ τ : ℝ, τ ≠ 0 ∧ D.W (ArchR.diagOne τ) ≠ 0) ∧
      0 < MeasureTheory.volume {τ : ℝ | D.W (ArchR.diagOne τ) ≠ 0} := by
  have hcont := continuousOn_torus D
  obtain ⟨τ₀, hτ₀, hne⟩ := exists_torus_ne_zero D hDW hDnz
  refine ⟨hcont, ⟨τ₀, hτ₀, hne⟩, ?_⟩

  have hopen : IsOpen ({τ : ℝ | τ ≠ 0} ∩ (fun τ : ℝ => D.W (ArchR.diagOne τ)) ⁻¹' {z | z ≠ 0}) :=
    hcont.isOpen_inter_preimage isOpen_ne isOpen_ne
  refine lt_of_lt_of_le (hopen.measure_pos MeasureTheory.volume ⟨τ₀, hτ₀, hne⟩) (MeasureTheory.measure_mono ?_)
  exact fun τ hτ => hτ.2

#print axioms solution

end S_LanglandsTunnell_Converse_ArchDatumR_continuousOn_and_exists_ne_zero_W_diagOne_of_weightZero
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumR_continuousOn_and_exists_ne_zero_W_diagOne_of_weightZero (solution)
