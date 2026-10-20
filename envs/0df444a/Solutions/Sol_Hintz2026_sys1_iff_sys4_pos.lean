-- Prove2me | solution 1 for Hintz2026.sys1_iff_sys4_pos
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T16:03:52.95303+00:00
-- url     : https://prove2.me/submissions/c06384fe-7180-44b2-bbb8-7431fcf8cd4f

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_ident_m0
import Theorems.Thm_Hintz2026_ident_m1
import Theorems.Thm_Hintz2026_ident_p0
import Theorems.Thm_Hintz2026_ident_p1

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (F : PosFields) (hF : PosDiff F x) : Sys1PosAt p om mm F x ↔ Sys4At p 1 om mm (yPos p 1 F) (yPos p (-1) F) x :=
  by
    have hpre : (↑(prePos p x) : ℂ) ≠ 0 := by exact_mod_cast (prePos_pos p hx).ne'
    have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hx.1)).ne'
    have hQ : (-2 * (↑p.Q : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast p.hQ)
    have m0 := ident_m0 p om mm hx F hF; have m1 := ident_m1 p om mm hx F hF
    have p0 := ident_p0 p om mm hx F hF; have p1 := ident_p1 p om mm hx F hF
    unfold Sys1PosAt Sys4At
    rw [vec2_eq_iff, vec2_eq_iff]
    simp only [Pi.sub_apply, Pi.add_apply]
    constructor
    · rintro ⟨ha, hb, hc, hd⟩
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rw [sub_eq_iff_sub_sub, m0, ha, hb]; simp
      · rw [sub_eq_iff_sub_sub, m1, hc, hd]; simp
      · rw [add_eq_iff_add_sub, p0, ha, hb]; simp
      · rw [add_eq_iff_add_sub, p1, hc, hd]; simp
    · rintro ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩
      rw [sub_eq_iff_sub_sub, m0] at h0
      rw [sub_eq_iff_sub_sub, m1] at h1
      rw [add_eq_iff_add_sub, p0] at h2
      rw [add_eq_iff_add_sub, p1] at h3
      have e0 : -I * res1a p om mm F x + res1b p om mm F x / ↑(Real.sqrt (Del p (x 0))) = 0 :=
        (mul_eq_zero.mp h0).resolve_left hpre
      have e2 : I * res1a p om mm F x + res1b p om mm F x / ↑(Real.sqrt (Del p (x 0))) = 0 :=
        (mul_eq_zero.mp h2).resolve_left hpre
      have e1 : I * res1c p om mm F x + res1d p om mm F x / ↑(Real.sqrt (Del p (x 0))) = 0 :=
        (mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hpre)).resolve_left hQ
      have e3 : -I * res1c p om mm F x + res1d p om mm F x / ↑(Real.sqrt (Del p (x 0))) = 0 :=
        (mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hpre)).resolve_left hQ
      obtain ⟨ha, hb⟩ := elim_pm hsD e0 e2
      obtain ⟨hc, hd⟩ := elim_pm hsD e3 e1
      exact ⟨ha, hb, hc, hd⟩

end
