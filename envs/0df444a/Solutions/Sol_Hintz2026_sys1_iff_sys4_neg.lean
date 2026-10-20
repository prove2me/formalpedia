-- Prove2me | solution 1 for Hintz2026.sys1_iff_sys4_neg
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T16:03:50.277982+00:00
-- url     : https://prove2.me/submissions/4f8177b8-7f36-4396-84b2-bab1ef2a7aac

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_identN_m0
import Theorems.Thm_Hintz2026_identN_m1
import Theorems.Thm_Hintz2026_identN_p0
import Theorems.Thm_Hintz2026_identN_p1

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (G : NegFields) (hG : NegDiff G x) : Sys1NegAt p om mm G x ↔ Sys4At p (-1) om mm (yNeg p 1 G) (yNeg p (-1) G) x :=
  by
    have hpre : (↑(preNeg p x) : ℂ) ≠ 0 := by exact_mod_cast (preNeg_pos p hx).ne'
    have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hx.1)).ne'
    have hQ : (2 * (↑p.Q : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast p.hQ)
    have m0 := identN_m0 p om mm hx G hG; have m1 := identN_m1 p om mm hx G hG
    have p0 := identN_p0 p om mm hx G hG; have p1 := identN_p1 p om mm hx G hG
    unfold Sys1NegAt Sys4At
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
      have e0 : -I * res1aN p om mm G x + ↑(Real.sqrt (Del p (x 0))) * res1bN p om mm G x = 0 :=
        (mul_eq_zero.mp h0).resolve_left hpre
      have e2 : I * res1aN p om mm G x + ↑(Real.sqrt (Del p (x 0))) * res1bN p om mm G x = 0 :=
        (mul_eq_zero.mp h2).resolve_left hpre
      have e1 : -I * res1cN p om mm G x - ↑(Real.sqrt (Del p (x 0))) * res1dN p om mm G x = 0 :=
        (mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hpre)).resolve_left hQ
      have e3 : I * res1cN p om mm G x - ↑(Real.sqrt (Del p (x 0))) * res1dN p om mm G x = 0 :=
        (mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hpre)).resolve_left hQ
      obtain ⟨ha, hb⟩ := elim_pm' hsD e0 e2
      obtain ⟨hc, hd⟩ := elim_pm_neg hsD e1 e3
      exact ⟨ha, hb, hc, hd⟩

end
