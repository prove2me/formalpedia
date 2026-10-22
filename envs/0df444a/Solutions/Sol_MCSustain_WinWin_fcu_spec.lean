-- Prove2me | solution 1 for MCSustain.WinWin.fcu_spec
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:09:39.580625+00:00
-- url     : https://prove2.me/submissions/4318ace1-15f1-47fc-9230-af5861cb6ed5

import Mathlib
import Definitions.Def_MCSustain_WinWin_Model

namespace MCSustain.WinWin
namespace Cex2

noncomputable def Pf (f : ℝ) : Params := ⟨1/2, 15, 1, 2, 1, 89/40, f, 1, 1, 0, 0, 0⟩

lemma mu_f (f : ℝ) : (Pf f).μ = 8 := by unfold Params.μ Pf; norm_num
lemma be_f (f : ℝ) : (Pf f).β = 8 := by unfold Params.β; rw [mu_f]; unfold Pf; norm_num

lemma standing_f (f : ℝ) (hf : 0 < f) : (Pf f).Standing := by
  unfold Params.Standing Params.Es Params.El
  rw [be_f]; unfold Pf; norm_num; exact hf

lemma rp (x : ℝ) (k : ℕ) (h : x = 2 ^ 3) : x ^ ((k : ℝ) / 3) = 2 ^ k := by
  subst h
  rw [← Real.rpow_natCast 2 3, ← Real.rpow_mul (by norm_num)]
  rw [show ((3 : ℕ) : ℝ) * ((k : ℝ) / 3) = (k : ℝ) by push_cast; ring, Real.rpow_natCast]

lemma k1_f (f : ℝ) : κ1 (Pf f) = 89/40 := by
  have b13 : (Pf f).β ^ ((1 : ℝ) / 3) = 2 := by
    have := rp (Pf f).β 1 (by rw [be_f]; norm_num); simpa using this
  have b23 : (Pf f).β ^ ((2 : ℝ) / 3) = 4 := by
    have := rp (Pf f).β 2 (by rw [be_f]; norm_num); norm_num at this; exact this
  have b43 : (Pf f).β ^ ((4 : ℝ) / 3) = 16 := by
    have := rp (Pf f).β 4 (by rw [be_f]; norm_num); norm_num at this; exact this
  unfold κ1; rw [b13, b23, b43, be_f]; unfold Pf; norm_num

lemma k2_f (f : ℝ) : 89/40 < κ2 (Pf f) := by
  unfold κ2; rw [be_f]
  have hs : Real.sqrt 8 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 < Real.sqrt 8 := by positivity
  unfold Pf; simp only
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

lemma rc_f (f : ℝ) : (Pf f).r / (Pf f).c = 89/40 := by unfold Pf; norm_num

lemma fH_f (f : ℝ) : fH (Pf f) = 343/16000 := by
  unfold fH lamH; rw [be_f, mu_f]; unfold Pf; norm_num

lemma fL_f (f : ℝ) : fL (Pf f) = 117649/1024000 := by
  unfold fL lamL; unfold Pf; norm_num

/-- On `(f_H, f_L]`, `Φ > 0` at this parameter point. -/
lemma Phi_pos (f g : ℝ) (h1 : fH (Pf f) < g) (h2 : g ≤ fL (Pf f)) : 0 < Φ (Pf f) g := by
  rw [fH_f] at h1; rw [fL_f] at h2
  have hg : 0 < g := by linarith
  set u := (g / (2 * (Pf f).mL * (Pf f).t)) ^ ((1 : ℝ) / 3) with hu
  have hu0 : 0 ≤ u := by
    rw [hu]; apply Real.rpow_nonneg; unfold Pf; simp only; positivity
  have hu3 : u ^ 3 = g / 4 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by unfold Pf; simp only; positivity)]
    unfold Pf; norm_num
  have hl : 7/40 < u := by
    by_contra hc; push_neg at hc
    have : u ^ 3 ≤ (7/40) ^ 3 := pow_le_pow_left₀ hu0 hc 3
    nlinarith
  have hr : u ≤ 49/160 := by
    by_contra hc; push_neg at hc
    have : (49/160) ^ 3 < u ^ 3 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    nlinarith
  have hPhi : Φ (Pf f) g = 49/80 - 3/2 * u - 2401/320000 / g := by
    unfold Φ lamL lamH; rw [be_f, mu_f, ← hu]; unfold Pf; norm_num; field_simp; ring
  rw [hPhi]
  have hq : 0 < -3/2 * u ^ 3 + 7/20 * u ^ 2 + 49/800 * u + 343/32000 := by
    nlinarith [mul_le_mul_of_nonneg_left hr (sq_nonneg u)]
  have hp : 0 < (u - 7/40) * (-3/2 * u ^ 3 + 7/20 * u ^ 2 + 49/800 * u + 343/32000) :=
    mul_pos (by linarith) hq
  rw [sub_pos, div_lt_iff₀ hg]
  have hg4 : g = 4 * u ^ 3 := by linarith
  rw [hg4]
  nlinarith

lemma fcu_f (f : ℝ) : fcu (Pf f) = 0 := by
  unfold fcu
  have : {g : ℝ | fH (Pf f) < g ∧ g ≤ fL (Pf f) ∧ Φ (Pf f) g = 0} = ∅ := by
    ext g; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2, h3⟩
    exact (Phi_pos f g h1 h2).ne' h3
  rw [this, Real.sInf_empty]

end Cex2
end MCSustain.WinWin

open MCSustain.WinWin in
theorem solution : ¬ (∀ (P : Params) (hP : P.Standing) (hκ1 : κ1 P ≤ P.r / P.c)
    (hκ2 : P.r / P.c < κ2 P),
    fH P < fcu P ∧ fcu P < fL P ∧ Φ P (fcu P) = 0 ∧
      ∀ g : ℝ, fH P < g → g ≤ fL P → Φ P g = 0 → g = fcu P) := by
  intro h
  have := (h (Cex2.Pf 1) (Cex2.standing_f 1 one_pos) (by rw [Cex2.k1_f, Cex2.rc_f])
    (by rw [Cex2.rc_f]; exact Cex2.k2_f 1)).1
  rw [Cex2.fcu_f, Cex2.fH_f] at this
  norm_num at this
