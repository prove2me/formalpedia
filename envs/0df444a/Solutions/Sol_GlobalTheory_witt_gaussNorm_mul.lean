-- Prove2me | solution 1 for GlobalTheory.witt_gaussNorm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:38.043799+00:00
-- url     : https://prove2.me/submissions/7a7617d2-1cf5-4f46-b945-140658123ec9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormMul
import Theorems.Thm_GlobalTheory_WittGaussMul_exists_lt_bound
import Theorems.Thm_GlobalTheory_WittGaussMul_exists_first_max
import Theorems.Thm_GlobalTheory_T_witt_vector_gauss_norm_ultrametric


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WittGaussMul
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ x y, N (x * y) = N x * N y := by
  intro l hl R _ _ _ a h01 h0 h1 hmul hadd r hr0 hr1 N hN x y
  obtain ⟨Nadd, Nneg, Nmul⟩ := GlobalTheory.T.witt_vector_gauss_norm_ultrametric l R a h01 h0 h1 hmul hadd r hr0 hr1 N hN
  set T : WittVector l R → ℕ → ℝ := fun x n => a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n
    with hT
  have hN' : ∀ x, N x = ⨆ n, T x n := hN
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hexp : ∀ n : ℕ, (0 : ℝ) < 1 / (l : ℝ) ^ n := fun n => by positivity
  have hT0 : ∀ x n, 0 ≤ T x n := fun x n =>
    mul_nonneg (Real.rpow_nonneg (h01 _).1 _) (pow_pos hr0 n).le
  have hTr : ∀ x n, T x n ≤ r ^ n := fun x n =>
    mul_le_of_le_one_left (pow_pos hr0 n).le
      (Real.rpow_le_one (h01 _).1 (h01 _).2 (hexp n).le)
  have hTN : ∀ x n, T x n ≤ N x := fun x n => by
    rw [hN']
    exact le_ciSup (f := T x)
      ⟨1, by rintro _ ⟨n, rfl⟩; exact (hTr x n).trans (pow_le_one₀ hr0.le hr1.le)⟩ n
  have hN0 : ∀ x, 0 ≤ N x := fun x => (hT0 x 0).trans (hTN x 0)
  have hTz : ∀ x n, x.coeff n = 0 → T x n = 0 := fun x n h => by
    simp only [hT, h, h0, Real.zero_rpow (hexp n).ne', zero_mul]
  have hpow : ∀ w (n : ℕ), a (w ^ n) = a w ^ n := fun w n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hTp : ∀ (u : WittVector l R) (n : ℕ), T (u * (l : WittVector l R) ^ n) n
      = a (u.coeff 0) * r ^ n := fun u n => by
    have h := WittVector.mul_pow_charP_coeff_succ u (m := 0) (n := n)
    rw [zero_add] at h
    simp only [hT, h, hpow]
    congr 1
    have := Real.pow_rpow_inv_natCast (h01 (u.coeff 0)).1 (pow_pos hl.out.pos n).ne'
    simpa using this
  have key : ∀ x, 0 < N x → ∃ (i : ℕ) (x0 u : WittVector l R),
      x = x0 + u * (l : WittVector l R) ^ i ∧ N x0 < N x ∧
      N (u * (l : WittVector l R) ^ i) ≤ N x ∧ a (u.coeff 0) * r ^ i = N x := by
    intro x hx
    obtain ⟨i, hi, hlt⟩ := exists_first_max (T x) r hr0 hr1 (hTr x) (by rw [← hN']; exact hx)
    rw [← hN'] at hi hlt
    have hmem : WittVector.tail i x ∈ Ideal.span {((l : WittVector l R) ^ i)} := by
      rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero]
      intro m hm
      simp [WittVector.tail, WittVector.select, WittVector.coeff_mk, not_le.mpr hm]
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨i, WittVector.init i x, u, ?_, ?_, ?_, ?_⟩
    · rw [hu, WittVector.init_add_tail]
    · obtain ⟨c, hc0, hcB, hc⟩ := exists_lt_bound (T x) _ hx i hlt
      refine lt_of_le_of_lt ?_ hcB
      rw [hN']
      refine ciSup_le fun n => ?_
      rcases lt_or_ge n i with h | h
      · have : (WittVector.init i x).coeff n = x.coeff n := by
          simp [WittVector.init, WittVector.select, WittVector.coeff_mk, h]
        have h2 : T (WittVector.init i x) n = T x n := by simp only [hT, this]
        rw [h2]; exact hc n h
      · rw [hTz]
        · exact hc0
        · simp [WittVector.init, WittVector.select, WittVector.coeff_mk, not_lt.mpr h]
    · rw [hu, hN' (WittVector.tail i x)]
      refine ciSup_le fun n => ?_
      rcases lt_or_ge n i with h | h
      · rw [hTz]
        · exact hN0 x
        · simp [WittVector.tail, WittVector.select, WittVector.coeff_mk, not_le.mpr h]
      · have : (WittVector.tail i x).coeff n = x.coeff n := by
          simp [WittVector.tail, WittVector.select, WittVector.coeff_mk, h]
        have h2 : T (WittVector.tail i x) n = T x n := by simp only [hT, this]
        rw [h2]; exact hTN x n
    · rw [← hTp, hu, ← hi]
      have : (WittVector.tail i x).coeff i = x.coeff i := by
        simp [WittVector.tail, WittVector.select, WittVector.coeff_mk]
      simp only [hT, this]
  refine le_antisymm (Nmul x y) ?_
  rcases (hN0 x).eq_or_lt with hx | hx
  · rw [← hx, zero_mul]; exact hN0 _
  rcases (hN0 y).eq_or_lt with hy | hy
  · rw [← hy, mul_zero]; exact hN0 _
  obtain ⟨i, x0, u, hxe, hx0, hu, hui⟩ := key x hx
  obtain ⟨j, y0, v, hye, hy0, hv, hvj⟩ := key y hy
  have hmain : N x * N y ≤ N ((u * v) * (l : WittVector l R) ^ (i + j)) := by
    refine le_trans (le_of_eq ?_) (hTN _ (i + j))
    rw [hTp, WittVector.mul_coeff_zero, hmul, ← hui, ← hvj]
    ring
  have hrest : N (x0 * y + (u * (l : WittVector l R) ^ i) * y0) < N x * N y := by
    refine lt_of_le_of_lt (Nadd _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Nmul _ _) (mul_lt_mul_of_pos_right hx0 hy)
    · refine lt_of_le_of_lt (Nmul _ _) ?_
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hu (hN0 _)) (mul_lt_mul_of_pos_left hy0 hx)
  have heq : (u * v) * (l : WittVector l R) ^ (i + j)
      = x * y + -(x0 * y + (u * (l : WittVector l R) ^ i) * y0) := by
    have : x * y = x0 * y + (u * (l : WittVector l R) ^ i) * (y0 + v * (l : WittVector l R) ^ j) := by
      rw [← hye, ← add_mul, ← hxe]
    rw [this]; ring
  have h3 := Nadd (x * y) (-(x0 * y + (u * (l : WittVector l R) ^ i) * y0))
  rw [← heq, Nneg] at h3
  rcases le_max_iff.mp (hmain.trans h3) with h | h
  · exact h
  · exact absurd hrest (not_lt.mpr h)
end GlobalTheory
