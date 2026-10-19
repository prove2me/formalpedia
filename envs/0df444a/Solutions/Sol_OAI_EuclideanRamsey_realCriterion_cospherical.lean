-- Prove2me | solution 1 for OAI.EuclideanRamsey.realCriterion_cospherical
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:23:50.789631+00:00
-- url     : https://prove2.me/submissions/371bf5bd-0e14-4944-a495-d86ad20a55ab

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/TensorSphere.lean:L17-L89
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.realCriterion_cospherical. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical

-- ---- from OAI.Combinatorics.EuclideanRamsey.TensorSphere ----
namespace OAI

/-!
The real tensor criterion implies ordinary Euclidean cosphericity.
The two constant/spatial matrix blocks are added to obtain the linear coefficient;
no symmetry of the tensor matrix is assumed.
-/

noncomputable section
open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

/-- The real tensor criterion places every point on one ordinary Euclidean sphere. -/
theorem realCriterion_cospherical {s d : ℕ} (a : Fin s → Space d)
    (hs : 0 < s) (h : RealCriterion a) :
    EuclideanGeometry.Cospherical (Set.range a) := by
  classical
  obtain ⟨P, hzero, hidentity⟩ := h
  let H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ :=
    fun α β => Algebra.TensorProduct.lmul' ℚ (P α β)
  have hspatial (j k : Fin d) : H (some j) (some k) = if j = k then 1 else 0 := by
    have hentry := congrFun (congrFun hidentity j) k
    change Algebra.TensorProduct.lmul' ℚ (P (some j) (some k)) =
      (1 : Matrix (Fin d) (Fin d) ℝ) j k at hentry
    simpa only [H, Matrix.one_apply] using hentry

  -- Applying multiplication ℝ ⊗[ℚ] ℝ → ℝ yields an ordinary quadratic.
  have hquad (i : Fin s) :
      H none none +
        (∑ j, (H none (some j) + H (some j) none) * a i j) +
        (∑ j, (a i j) ^ 2) = 0 := by
    have htensor :
        (∑ α, ∑ β,
          ((realAugmented a i α) ⊗ₜ[ℚ] (1 : ℝ)) * P α β *
            ((1 : ℝ) ⊗ₜ[ℚ] (realAugmented a i β))) = 0 :=
      hzero i
    have hreal := congrArg (Algebra.TensorProduct.lmul' ℚ (S := ℝ)) htensor
    simp only [map_sum, map_mul, Algebra.TensorProduct.lmul'_apply_tmul,
      mul_one, one_mul, map_zero] at hreal
    change (∑ α, ∑ β,
      realAugmented a i α * H α β * realAugmented a i β) = 0 at hreal
    simp only [Fintype.sum_option, realAugmented, one_mul, mul_one,
      Finset.sum_add_distrib] at hreal
    have hdiagonal :
        (∑ j : Fin d, ∑ k : Fin d, a i j * H (some j) (some k) * a i k) =
          ∑ j : Fin d, (a i j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      simp [hspatial, mul_ite, ite_mul, pow_two]
    have hlinear :
        (∑ j : Fin d, H none (some j) * a i j) +
          (∑ j : Fin d, a i j * H (some j) none) =
          ∑ j : Fin d, (H none (some j) + H (some j) none) * a i j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hdiagonal] at hreal
    linarith [hlinear]

  -- Complete the square coordinatewise. This includes the zero-dimensional case.
  let center : Space d := WithLp.toLp 2
    (fun j => -((H none (some j) + H (some j) none) / 2))
  have hdist (i : Fin s) :
      dist (a i) center ^ 2 = (∑ j, (center j) ^ 2) - H none none := by
    rw [EuclideanSpace.dist_sq_eq]
    simp only [Real.dist_eq, sq_abs]
    calc
      (∑ j, (a i j - center j) ^ 2) =
          (∑ j, (a i j) ^ 2) +
            (∑ j, (H none (some j) + H (some j) none) * a i j) +
            (∑ j, (center j) ^ 2) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [center]
        ring
      _ = (∑ j, (center j) ^ 2) - H none none := by
        linarith [hquad i]

  -- Use an actual point's nonnegative distance as radius, avoiding a sqrt witness.
  let first : Fin s := ⟨0, hs⟩
  refine ⟨center, dist (a first) center, ?_⟩
  rintro p ⟨i, rfl⟩
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ((hdist i).trans (hdist first).symm)

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.realCriterion_cospherical := @_root_.OAI.EuclideanRamsey.realCriterion_cospherical
