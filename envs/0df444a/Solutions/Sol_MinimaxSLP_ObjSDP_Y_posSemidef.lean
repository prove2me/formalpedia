-- Prove2me | solution 1 for MinimaxSLP.ObjSDP.Y_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:25:05.131202+00:00
-- url     : https://prove2.me/submissions/a067d836-361b-4193-b22a-7cc0ad5b3498

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model

open MeasureTheory Matrix

open MinimaxSLP.ObjSDP in
theorem solution {n r d K : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (k : Fin K) (hαk : 0 ≤ α k)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty)
    (Y : Matrix (Fin d) (Fin d) ℝ) (hY : Y.IsSymm) (y : Fin d → ℝ) (y₀ : ℝ)
    (hC : ∀ q : Fin d → ℝ, α k * Qval W T h q x + β k ≤ q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀) :
    Y.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hY
  rw [star_trivial]
  by_contra hneg
  push_neg at hneg
  set a := -(v ⬝ᵥ (Y *ᵥ v)) with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  -- lower bound for v ⬝ w on the recourse set
  obtain ⟨π, hπ⟩ := hA3 v
  set L := π ⬝ᵥ (h - T *ᵥ x) with hL
  have hlow : ∀ w ∈ recourseSet W T h x, L ≤ v ⬝ᵥ w := by
    rintro w ⟨hw, hw0⟩
    have e : (Wᵀ *ᵥ π) ⬝ᵥ w = π ⬝ᵥ (W *ᵥ w) := by
      rw [mulVec_transpose, dotProduct_mulVec]
    rw [hL, ← hw, ← e]
    simp only [dotProduct]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hπ i) (hw0 i)
  have hQ : ∀ t : ℝ, 0 < t → t * L ≤ Qval W T h (t • v) x := by
    intro t ht
    unfold Qval
    apply le_csInf (hrec.image _)
    rintro _ ⟨w, hw, rfl⟩
    show t * L ≤ (t • v) ⬝ᵥ w
    rw [smul_dotProduct, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hlow w hw) ht.le
  set b := v ⬝ᵥ y with hb
  set C := |b - α k * L| + |y₀ - β k| + a with hCdef
  set t := C / a with ht
  have hCa : a ≤ C := by rw [hCdef]; linarith [abs_nonneg (b - α k * L), abs_nonneg (y₀ - β k)]
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ ha0]; linarith
  have ht0 : 0 < t := by linarith
  have hat : a * t = C := by rw [ht]; field_simp
  have key := hC (t • v)
  have hq1 : (t • v) ⬝ᵥ (Y *ᵥ (t • v)) = -a * t ^ 2 := by
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ha]
    ring
  have hq2 : (t • v) ⬝ᵥ y = t * b := by rw [smul_dotProduct, smul_eq_mul]
  rw [hq1, hq2] at key
  have hQt := mul_le_mul_of_nonneg_left (hQ t ht0) hαk
  have h1 : (b - α k * L) * t ≤ |b - α k * L| * t :=
    mul_le_mul_of_nonneg_right (le_abs_self _) ht0.le
  have h2 : y₀ - β k ≤ |y₀ - β k| * t := by
    have := le_abs_self (y₀ - β k)
    have : |y₀ - β k| ≤ |y₀ - β k| * t := le_mul_of_one_le_right (abs_nonneg _) ht1
    linarith
  have h3 : a * t ^ 2 = C * t := by rw [sq, ← mul_assoc, hat]
  nlinarith
