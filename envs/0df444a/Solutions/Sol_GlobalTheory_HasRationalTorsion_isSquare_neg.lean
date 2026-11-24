-- Prove2me | solution 1 for GlobalTheory.HasRationalTorsion.isSquare_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:22.286683+00:00
-- url     : https://prove2.me/submissions/126aae33-3775-41a4-9d8a-9ba122f520d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Theorems.Thm_GlobalTheory_hasRationalTorsion_iff
import Theorems.Thm_P2M_GlobalTheory_splitCurve___21d0522b5d77
import Theorems.Thm_GlobalTheory_nonsingular_baseChange_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {K : Type*} [Field K] [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]
omit [CharZero K]
namespace GlobalTheory
namespace HasRationalTorsion
theorem _root_.solution {A B : K} [(splitCurve A B).IsElliptic]
    (h : HasRationalTorsion (splitCurve A B) L 4) : ∃ a : K, a ^ 2 = -A := by
  classical
  have hΔ := (splitCurve A B).isUnit_Δ.ne_zero
  rw [splitCurve_Δ] at hΔ
  have hA : A ≠ 0 := by rintro rfl; simp at hΔ
  have hB : B ≠ 0 := by rintro rfl; simp at hΔ
  have hAB : A ≠ B := by rintro rfl; simp at hΔ
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (-algebraMap K L A) two_pos
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (-algebraMap K L B) two_pos
  have hP : ((splitCurve A B).baseChange L).toAffine.Nonsingular (α * β) (α * β * (α + β)) := by
    rw [nonsingular_baseChange_iff, equation_iff]
    simp only [WeierstrassCurve.baseChange, splitCurve, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
      map_zero, map_neg, map_add, map_mul]
    rw [← neg_neg (algebraMap K L A), ← hα, ← neg_neg (algebraMap K L B), ← hβ]
    ring
  have hT : ((splitCurve A B).baseChange L).toAffine.Nonsingular 0 0 := by
    rw [nonsingular_baseChange_iff, equation_iff]
    simp [WeierstrassCurve.baseChange, splitCurve]
  have h2 : Point.some _ _ hT + Point.some _ _ hT = 0 := by
    apply Point.add_self_of_Y_eq
    simp [WeierstrassCurve.baseChange, splitCurve]
  have h3 : Point.some _ _ hP + Point.some _ _ hP + Point.some _ _ hT = 0 := by
    refine add_add_eq_zero_of_line hP hP hT (α + β) 0 (by ring) (by ring) (by ring) ?_ ?_
    all_goals
      simp only [WeierstrassCurve.baseChange, splitCurve, map_a₁, map_a₂, map_a₃, map_a₄,
        map_zero, map_neg, map_add, map_mul]
      rw [← neg_neg (algebraMap K L A), ← hα, ← neg_neg (algebraMap K L B), ← hβ]
      ring
  have h4 : 4 • Point.some _ _ hP = 0 := by
    have : 4 • Point.some _ _ hP = 2 • (Point.some _ _ hP + Point.some _ _ hP + Point.some _ _ hT)
      - (Point.some _ _ hT + Point.some _ _ hT) := by abel
    rw [this, h2, h3, smul_zero, sub_zero]
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hasRationalTorsion_iff.mp h _ _ hP h4
  have hα0 : α ≠ 0 := by rintro rfl; simp [hA] at hα
  have hβ0 : β ≠ 0 := by rintro rfl; simp [hB] at hβ
  have hαβ : α + β ≠ 0 := by
    intro h0
    apply hAB
    apply (algebraMap K L).injective
    linear_combination hα - hβ - (α - β) * h0
  refine ⟨(p - A) * p / q, (algebraMap K L).injective ?_⟩
  rw [map_pow, map_neg, ← hα]
  congr 1
  rw [map_div₀, map_mul, map_sub, hp, hq, ← neg_neg (algebraMap K L A), ← hα]
  field_simp
  ring
end HasRationalTorsion
end GlobalTheory
