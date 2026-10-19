-- Prove2me | solution 1 for OAI.EuclideanRamsey.congruent_linearIsometry
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:46:40.055665+00:00
-- url     : https://prove2.me/submissions/23aac891-fef8-43b2-b15f-b36f9d3c10e6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Congruence.lean:L74-L97
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.congruent_linearIsometry. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey

-- ---- from OAI.Combinatorics.EuclideanRamsey.Congruence ----
namespace OAI

universe uIndex uDomain uCodomain

noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

theorem linearIsometry_of_equal_gram {ι : Type uIndex} {E : Type uDomain} {F : Type uCodomain} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : ι → E) (y : ι → F)
    (hspan : Submodule.span ℝ (Set.range x) = ⊤)
    (hgram : ∀ i j, ⟪y i, y j⟫ = ⟪x i, x j⟫) :
    ∃ Q : E →ₗᵢ[ℝ] F, ∀ i, Q (x i) = y i := by
  classical
  let A := Fintype.linearCombination ℝ x
  let B := Fintype.linearCombination ℝ y
  have hinner (c e : ι → ℝ) : ⟪B c, B e⟫ = ⟪A c, A e⟫ := by
    simp only [A, B, Fintype.linearCombination_apply, sum_inner, inner_sum,
      real_inner_smul_left, inner_smul_right, hgram]
  have hnorm (c : ι → ℝ) : ‖B c‖ = ‖A c‖ := by
    have h := hinner c c
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (B c), norm_nonneg (A c)]
  have hsurj : LinearMap.range A = ⊤ := by
    rw [Fintype.range_linearCombination]
    exact hspan
  obtain ⟨R, hR⟩ := A.exists_rightInverse_of_surjective hsurj
  have hR' (z : E) : A (R z) = z := congrArg (fun L : E →ₗ[ℝ] E => L z) hR
  let L : E →ₗ[ℝ] F := B.comp R
  have hLnorm (z : E) : ‖L z‖ = ‖z‖ := by
    change ‖B (R z)‖ = ‖z‖
    rw [hnorm, hR']
  have hfactor (c : ι → ℝ) : L (A c) = B c := by
    have hzero : A (R (A c) - c) = 0 := by rw [map_sub, hR', sub_self]
    have : B (R (A c) - c) = 0 := by
      apply norm_eq_zero.mp
      rw [hnorm, hzero, norm_zero]
    simpa only [map_sub, L, LinearMap.comp_apply, sub_eq_zero] using this
  refine ⟨⟨L, hLnorm⟩, ?_⟩
  intro i
  simpa [A, B] using hfactor (Pi.single i 1)

theorem congruent_linearIsometry {s d D : ℕ} (a : Fin s → Space d)
    (b : Fin s → Space D) (i₀ : Fin s)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) (h : Congruent a b) :
    ∃ Q : Space d →ₗᵢ[ℝ] Space D, ∃ t : Space D, ∀ i, b i = t + Q (a i) := by
  have hv : vectorSpan ℝ (Set.range a) = ⊤ := by
    simpa only [direction_affineSpan, AffineSubspace.direction_top] using
      congrArg AffineSubspace.direction hspan
  have hs : Submodule.span ℝ (Set.range fun i => a i - a i₀) = ⊤ := by
    rw [vectorSpan_range_eq_span_range_vsub_right ℝ a i₀] at hv
    exact hv
  have hg (i j : Fin s) : ⟪b i - b i₀, b j - b i₀⟫ =
      ⟪a i - a i₀, a j - a i₀⟫ := by
    simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      sub_sub_sub_cancel_right, ← dist_eq_norm]
    rw [h i i₀, h j i₀, h i j]
  obtain ⟨Q, hQ⟩ := linearIsometry_of_equal_gram
    (fun i => a i - a i₀) (fun i => b i - b i₀) hs hg
  refine ⟨Q, b i₀ - Q (a i₀), fun i => ?_⟩
  have hi := hQ i
  rw [map_sub] at hi
  calc
    b i = (b i - b i₀) + b i₀ := (sub_add_cancel _ _).symm
    _ = (Q (a i) - Q (a i₀)) + b i₀ := by rw [hi]
    _ = b i₀ - Q (a i₀) + Q (a i) := by abel

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.congruent_linearIsometry := @_root_.OAI.EuclideanRamsey.congruent_linearIsometry
