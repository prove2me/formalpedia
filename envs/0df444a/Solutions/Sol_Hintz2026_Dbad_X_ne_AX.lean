-- Prove2me | solution 1 for Hintz2026.Dbad_X_ne_AX
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:53:05.146249+00:00
-- url     : https://prove2.me/submissions/b8f2e0bb-7332-4ae7-b2fc-75cf8b7169b9

import Definitions.Def_Hintz2026_AnalysisV2

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) {x : Fin 2 → ℝ} (hx : x ∈ U p) (ha : p.a ≠ 0) : (of fun i j => Dbad p (fun z => X p z i j) x) ≠ A p x * X p x :=
  by
    intro heq
    have h01 := congr_fun (congr_fun heq 0) 1
    simp only [of_apply] at h01
    have hDm : Dm p (fun z => X p z 0 1) x = (A p x * X p x) 0 1 := by
      have h := congr_fun (congr_fun (Dminus_X_eq_AX p hx) 0) 1
      simp only [of_apply] at h; exact h
    have hexp : Dbad p (fun z => X p z 0 1) x =
        (A p x * X p x) 0 1 + I * cpd 1 (fun z => X p z 0 1) x := by
      rw [Dbad_eq_Dm_add, hDm]
    have hzero : I * cpd 1 (fun z => X p z 0 1) x = 0 :=
      left_eq_add.mp (h01.symm.trans hexp)
    have hcpd0 : cpd 1 (fun z => X p z 0 1) x = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h I_ne_zero
      · exact h
    rw [cpd_X01_th p hx] at hcpd0
    have hQ2 : (↑(p.Q ^ 2) : ℂ) ≠ 0 := by
      rw [ofReal_pow]; exact pow_ne_zero 2 (by exact_mod_cast p.hQ)
    have hrho2 : (rhoBar p x) ^ 2 ≠ 0 := pow_ne_zero 2 (rhoBar_ne_zero p hx)
    have h_num : (-(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ)) ≠ 0 := by
      rw [neg_ne_zero]; intro habs
      have him : (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ).im = (0 : ℂ).im := congr_arg Complex.im habs
      simp at him
      rcases him with h | h
      · exact ha h
      · exact ne_of_gt (sin_pos_of_mem p hx) h
    exact absurd hcpd0 (mul_ne_zero (mul_ne_zero I_ne_zero hQ2) (div_ne_zero h_num hrho2))

end
