-- Prove2me | solution 1 for IPLicense3D.Pooling.lemma_1_vi
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:09:00.234321+00:00
-- url     : https://prove2.me/submissions/2a2b128d-630a-4a3d-8cff-5e6a555e6664

import Mathlib
import Definitions.Def_IPLicense3D_Pooling_Model

open IPLicense3D.Pooling IPLicense3D.Pooling.Model in
theorem solution {n : ℕ} (M : Model n) (hM : M.Standing) (i : Fin n) (f r : ℝ) :
    MonotoneOn (fun w' => surplusF M.h w' M.p M.kT M.kA M.ellT M.ellA M.z (M.lam i) f r) (Set.Ioi 0) ∧
    ConcaveOn ℝ (Set.Ioi 0)
      (fun w' => surplusF M.h w' M.p M.kT M.kA M.ellT M.ellA M.z (M.lam i) f r) := by
  obtain ⟨hh, hw, hp, hkA, hkAT, hellA, hellAT, hz, hlam⟩ := hM
  have hl : 0 < M.lam i := hlam i
  have hkT : 0 < M.kT := by linarith
  have hellT : 0 < M.ellT := by linarith
  set l := M.lam i with hldef
  set X := l * M.ellT + M.z * Real.sqrt (l * M.ellT) with hXdef
  have hX : 0 ≤ X := by
    have := Real.sqrt_nonneg (l * M.ellT)
    have := mul_pos hl hellT
    nlinarith
  set Kc := Real.sqrt (2 * M.h * l * M.kT) with hKc
  have hKc0 : 0 ≤ Kc := Real.sqrt_nonneg _
  have hc0 : 0 ≤ 2 * M.h * l * M.kT := by
    have := mul_pos (mul_pos (mul_pos (two_pos : (0:ℝ) < 2) hh) hl) hkT
    linarith
  have hsq : ∀ w : ℝ, 0 ≤ w → Real.sqrt (2 * M.h * w * l * M.kT) = Kc * Real.sqrt w := by
    intro w hw0
    rw [show 2 * M.h * w * l * M.kT = (2 * M.h * l * M.kT) * w by ring, Real.sqrt_mul hc0]
  set C := costAF M.h M.p M.kA M.ellA M.z l f r with hC
  have heq : ∀ w : ℝ, 0 < w →
      surplusF M.h w M.p M.kT M.kA M.ellT M.ellA M.z l f r =
        (M.h * X + l) * w + Kc * Real.sqrt w - C := by
    intro w hw0
    unfold surplusF costTF
    rw [hsq w hw0.le, ← hC, hXdef]
    ring
  have hA : 0 ≤ M.h * X + l := by
    have := mul_nonneg hh.le hX
    linarith
  constructor
  · intro a ha b hb hab
    simp only [Set.mem_Ioi] at ha hb
    simp only []
    rw [heq a ha, heq b hb]
    have hs := Real.sqrt_le_sqrt hab
    nlinarith [mul_le_mul_of_nonneg_left hs hKc0, mul_le_mul_of_nonneg_left hab hA]
  · refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
    simp only [Set.mem_Ioi] at hx hy
    simp only [smul_eq_mul]
    have hpos : 0 < a * x + b * y := by
      rcases ha.lt_or_eq with ha' | ha'
      · have := mul_pos ha' hx; have := mul_nonneg hb hy.le; linarith
      · have hb' : b = 1 := by linarith
        rw [← ha', hb']; linarith
    rw [heq x hx, heq y hy, heq (a * x + b * y) hpos]
    have hs := (Real.strictConcaveOn_sqrt.concaveOn).2 (Set.mem_Ici.mpr hx.le)
      (Set.mem_Ici.mpr hy.le) ha hb hab
    simp only [smul_eq_mul] at hs
    obtain rfl : b = 1 - a := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hs hKc0]
