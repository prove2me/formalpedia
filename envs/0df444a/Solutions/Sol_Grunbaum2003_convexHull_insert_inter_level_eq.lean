-- Prove2me | solution 1 for Grunbaum2003.convexHull_insert_inter_level_eq
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:38:06.458324+00:00
-- url     : https://prove2.me/submissions/d4fa9f9d-0a2c-4444-ba76-67c7434d2a0d

import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

/-- Explicit vertex-figure hull identity for a hyperplane separating one generator from all others.
Private development for the boundary-refinement induction. No finiteness assumption on `W`. -/
theorem convexHull_insert_inter_level_eq (d : ℕ) (v : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α) :
    convexHull ℝ (insert v W) ∩ l ⁻¹' {α} =
      convexHull ℝ ((fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W) := by
  classical
  let q : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))
  have hD : 0 < l v - α := sub_pos.mpr hα
  have hq (w : Fin d → ℝ) (hw : w ∈ W) :
      q w ∈ convexHull ℝ (insert v W) ∧ l (q w) = α := by
    have hDen : 0 < l v - l w := sub_pos.mpr ((hBelow w hw).trans hα)
    have ht0 : 0 ≤ (l v - α) / (l v - l w) := (div_pos hD hDen).le
    have ht1 : (l v - α) / (l v - l w) ≤ 1 :=
      (div_le_one hDen).mpr (by linarith [hBelow w hw])
    constructor
    · exact (convex_convexHull ℝ _).lineMap_mem
        (subset_convexHull ℝ _ (Set.mem_insert v W))
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem v hw)) ⟨ht0, ht1⟩
    · have hMul : ((l v - α) / (l v - l w)) * (l v - l w) = l v - α :=
        div_mul_cancel₀ _ hDen.ne'
      dsimp [q]
      rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
      nlinarith [hMul]
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxLevel⟩
    change l x = α at hxLevel
    obtain ⟨ι, hι, a, z, ha, haSum, hz, haz⟩ := mem_convexHull_iff_exists_fintype.mp hx
    letI := hι
    obtain ⟨w₀, hw₀⟩ := hW
    let b : ι → ℝ := fun i => a i * (l v - l (z i)) / (l v - α)
    let u : ι → (Fin d → ℝ) := fun i => if z i = v then q w₀ else q (z i)
    have hzLe (i : ι) : l (z i) ≤ l v := by
      rcases hz i with h | h
      · simpa only [h] using le_refl (l v)
      · exact ((hBelow (z i) h).trans hα).le
    have hb (i : ι) : 0 ≤ b i := div_nonneg (mul_nonneg (ha i) (sub_nonneg.mpr (hzLe i))) hD.le
    have hlSum : ∑ i, a i * l (z i) = α := by
      have h := congrArg l haz
      simpa only [map_sum, map_smul, smul_eq_mul, hxLevel] using h
    have hbSum : ∑ i, b i = 1 := by
      calc
        ∑ i, b i = (∑ i, a i * (l v - l (z i))) / (l v - α) := by
          simp only [b, div_eq_mul_inv, Finset.sum_mul]
        _ = ((∑ i, a i) * l v - ∑ i, a i * l (z i)) / (l v - α) := by
          simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
        _ = 1 := by rw [haSum, hlSum, one_mul, div_self hD.ne']
    have hu (i : ι) : u i ∈ q '' W := by
      dsimp [u]
      split_ifs with hi
      · exact ⟨w₀, hw₀, rfl⟩
      · exact ⟨z i, (Set.mem_insert_iff.mp (hz i)).resolve_left hi, rfl⟩
    have hTerm (i : ι) : b i • u i = b i • v + a i • (z i - v) := by
      by_cases hi : z i = v
      · simp [u, b, hi]
      · have hzi : z i ∈ W := (Set.mem_insert_iff.mp (hz i)).resolve_left hi
        have hDen : l v - l (z i) ≠ 0 := (sub_pos.mpr ((hBelow (z i) hzi).trans hα)).ne'
        have hCoef : b i * ((l v - α) / (l v - l (z i))) = a i := by
          dsimp [b]
          field_simp [hD.ne', hDen] <;> ring
        dsimp [u]
        rw [if_neg hi]
        dsimp [q]
        rw [AffineMap.lineMap_apply_module', smul_add, smul_smul, hCoef, add_comm]
    apply mem_convexHull_of_exists_fintype b u hb hbSum hu
    calc
      ∑ i, b i • u i = ∑ i, (b i • v + a i • (z i - v)) := Finset.sum_congr rfl (fun i _ => hTerm i)
      _ = (∑ i, b i) • v + (∑ i, a i • z i - (∑ i, a i) • v) := by
        simp only [Finset.sum_add_distrib, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
      _ = x := by rw [hbSum, haSum, haz, one_smul]; abel
  · apply convexHull_min
    · rintro _ ⟨w, hw, rfl⟩
      exact hq w hw
    · apply (convex_convexHull ℝ _).inter
      intro x hx y hy a b ha hb hab
      change l x = α at hx
      change l y = α at hy
      change l (a • x + b • y) = α
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hx, hy]
      rw [← add_mul, hab, one_mul]

end Grunbaum2003


open Grunbaum2003
theorem solution (d : ℕ) (v : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α) :
    convexHull ℝ (insert v W) ∩ l ⁻¹' {α} =
      convexHull ℝ ((fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W) :=
  Grunbaum2003.convexHull_insert_inter_level_eq d v W hW l α hα hBelow
