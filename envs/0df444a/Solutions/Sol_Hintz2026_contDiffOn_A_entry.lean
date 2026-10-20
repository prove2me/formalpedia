-- Prove2me | solution 1 for Hintz2026.contDiffOn_A_entry
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:56:33.695986+00:00
-- url     : https://prove2.me/submissions/f5a34ef3-ef12-4d7e-a7cb-10202548ef20

import Definitions.Def_Hintz2026_AnalysisV2

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026
-- inlined private helpers (de-privatized)
variable (p : SubextremalKN)
theorem smooth_r : ContDiff ℝ ⊤ (fun x : Fin 2 → ℝ => x 0) :=
  contDiff_pi.mp contDiff_id 0

theorem smooth_th : ContDiff ℝ ⊤ (fun x : Fin 2 → ℝ => x 1) :=
  contDiff_pi.mp contDiff_id 1

theorem smooth_coe {f : (Fin 2 → ℝ) → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun x => (↑(f x) : ℂ)) := Complex.ofRealCLM.contDiff.comp hf

theorem smooth_complex_mk {f g : (Fin 2 → ℝ) → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) :
    ContDiff ℝ ⊤ (fun x => (⟨f x, g x⟩ : ℂ)) := by
  have : (fun x => (⟨f x, g x⟩ : ℂ)) = fun x => ↑(f x) + ↑(g x) * I := by
    ext x; exact Complex.mk_eq_add_mul_I (f x) (g x)
  rw [this]; exact (smooth_coe hf).add ((smooth_coe hg).mul contDiff_const)

theorem smooth_rhoBarStar : ContDiff ℝ ⊤ (rhoBarStar p) := by
  unfold rhoBarStar; exact smooth_complex_mk smooth_r (((Real.contDiff_cos.comp smooth_th).const_smul p.a).neg)

theorem smooth_rhoBar : ContDiff ℝ ⊤ (rhoBar p) := by
  unfold rhoBar; exact smooth_complex_mk smooth_r ((Real.contDiff_cos.comp smooth_th).const_smul p.a)

theorem cdoU_inv_rhoBar_sq : ContDiffOn ℝ ⊤ (fun x => ((rhoBar p x) ^ 2)⁻¹) (U p) :=
  ((smooth_rhoBar p).contDiffOn.pow 2).inv (fun x hx => pow_ne_zero 2 (rhoBar_ne_zero p hx))

theorem contDiffOn_A01 : ContDiffOn ℝ ⊤ (fun x => A p x 0 1) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x => -I * ↑p.Q * rhoBarStar p x / rhoBar p x ^ 2) (U p)
  exact ContDiffOn.mul (ContDiffOn.mul contDiffOn_const (smooth_rhoBarStar p).contDiffOn)
    (cdoU_inv_rhoBar_sq p)

theorem cdoU_inv_rhoBarStar_sq : ContDiffOn ℝ ⊤ (fun x => ((rhoBarStar p x) ^ 2)⁻¹) (U p) :=
  ((smooth_rhoBarStar p).contDiffOn.pow 2).inv (fun x hx => pow_ne_zero 2 (rhoBarStar_ne_zero p hx))

theorem contDiffOn_A10 : ContDiffOn ℝ ⊤ (fun x => A p x 1 0) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x => I * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2) (U p)
  exact ContDiffOn.mul (ContDiffOn.mul contDiffOn_const (smooth_rhoBar p).contDiffOn)
    (cdoU_inv_rhoBarStar_sq p)
end Hintz2026

open Hintz2026 in
theorem solution (p : SubextremalKN) (i j : Fin 2) : ContDiffOn ℝ ⊤ (fun x => A p x i j) (U p) :=
  by
    fin_cases i <;> fin_cases j
    · show ContDiffOn ℝ ⊤ (fun _ => (0 : ℂ)) (U p); exact contDiffOn_const
    · exact contDiffOn_A01 p
    · exact contDiffOn_A10 p
    · show ContDiffOn ℝ ⊤ (fun _ => (0 : ℂ)) (U p); exact contDiffOn_const

end
