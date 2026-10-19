-- Prove2me | solution 1 for OAI.MatchingSmoothing.pairWeight_overlap_square_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:00:03.22705+00:00
-- url     : https://prove2.me/submissions/6f9ac00a-09ad-44bd-afa9-93231d4b6cc2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TensorBounds.lean:L113-L132
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.pairWeight_overlap_square_moment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Theorems.Thm_OAI_MatchingSmoothing_common_pairColorings_moment
import Theorems.Thm_OAI_MatchingSmoothing_pairWeight_overlap_le

-- ---- from OAI.Combinatorics.MatchingPSD.TensorBounds ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix

variable {C : Type u_1} [Fintype C] [DecidableEq C]

lemma abs_eigenvalue_le_one_stochastic (W : Matrix C C ℝ)
    (hn : ∀ i j, 0 ≤ W i j) (hs : ∀ i, ∑ j, W i j = 1)
    (c : ℝ) (hc : Module.End.HasEigenvalue (Matrix.toLin' W) c) : |c| ≤ 1 := by
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hc
  rw [mem_closedBall_iff_norm] at hi
  simp only [Real.norm_eq_abs, abs_of_nonneg (hn _ _)] at hi
  have he := Finset.sum_erase_add (Finset.univ : Finset C) (fun j => W i j)
    (Finset.mem_univ i)
  rw [hs] at he
  calc
    |c| = |(c - W i i) + W i i| := by congr 1; ring
    _ ≤ |c - W i i| + |W i i| := abs_add_le _ _
    _ ≤ 1 := by rw [abs_of_nonneg (hn _ _)]; linarith

lemma abs_eigenvalue_le_one_positive_fixed (A : Matrix C C ℝ)
    (hn : ∀ i j, 0 ≤ A i j) (v : C → ℝ) (hv : ∀ i, 0 < v i)
    (hf : A *ᵥ v = v) (c : ℝ)
    (hc : Module.End.HasEigenvalue (Matrix.toLin' A) c) : |c| ≤ 1 := by
  let W : Matrix C C ℝ := fun i j => A i j * v j / v i
  apply abs_eigenvalue_le_one_stochastic W
  · intro i j; exact div_nonneg (mul_nonneg (hn i j) (hv j).le) (hv i).le
  · intro i
    change ∑ j, A i j * v j / v i = 1
    rw [← Finset.sum_div]
    change (A *ᵥ v) i / v i = 1
    rw [hf, div_self (ne_of_gt (hv i))]
  · obtain ⟨x, hx, hnx⟩ := hc.exists_hasEigenvector
    let y : C → ℝ := fun i => x i / v i
    have hy : y ≠ 0 := by
      intro h
      apply hnx
      ext i
      have he := congrFun h i
      change x i / v i = 0 at he
      exact (div_eq_zero_iff.mp he).resolve_right (ne_of_gt (hv i))
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hy⟩
    rw [Module.End.mem_eigenspace_iff]
    ext i
    change ∑ j, (A i j * v j / v i) * (x j / v j) = c * (x i / v i)
    have hh (j : C) : A i j * v j / v i * (x j / v j) = A i j * x j / v i := by
      field_simp [ne_of_gt (hv j), ne_of_gt (hv i)]
    simp_rw [hh]
    rw [← Finset.sum_div]
    have hhx := congrFun (Module.End.mem_eigenspace_iff.mp hx) i
    change ∑ j, A i j * x j = c * x i at hhx
    rw [hhx]
    ring

lemma exists_orthogonal_diagonalization_bounded (A : Matrix C C ℝ)
    (hA : A.IsHermitian) (hn : ∀ i j, 0 ≤ A i j)
    (v : C → ℝ) (hv : ∀ i, 0 < v i) (hf : A *ᵥ v = v) :
    ∃ U : Matrix C C ℝ, ∃ d : C → ℝ,
      U.transpose * U = 1 ∧ (∀ i, |d i| ≤ 1) ∧ A = U * diagonal d * U.transpose := by
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, ?_, ?_, ?_⟩
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hA.eigenvectorUnitary.property.1
  · intro i
    apply abs_eigenvalue_le_one_positive_fixed A hn v hv hf
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact hA.mulVec_eigenvectorBasis i
    · intro h
      have he : hA.eigenvectorBasis i = 0 := by
        exact PiLp.ext (fun j => congrFun h j)
      exact (hA.eigenvectorBasis.orthonormal.ne_zero i) he
  · simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hA.spectral_theorem

end MatchingSmoothing

namespace MatchingSmoothing
open Matrix
variable {H : Type u_2} {C : Type u_3} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

lemma commonColorings_square (σ : Equiv.Perm (H × Bool)) :
    (Fintype.card {f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)}) ^ 2 =
    Fintype.card {f : H × Bool → C × C // pairConstant f ∧ pairConstant (f ∘ σ)} := by
  rw [pow_two, ← Fintype.card_prod]
  exact Fintype.card_congr (commonColoringsProdEquiv σ)

omit [Fintype C] [DecidableEq H] [DecidableEq C] in
lemma pairWeight_nonneg (A : Matrix C C ℝ) (hn : ∀ i j, 0 ≤ A i j)
    (f : H × Bool → C) : 0 ≤ pairWeight A f := by
  exact Finset.prod_nonneg (fun _ _ => hn _ _)

lemma pairWeight_overlap_square_moment (A : Matrix C C ℝ)
    (hA : A.IsHermitian) (hn : ∀ i j, 0 ≤ A i j)
    (v : C → ℝ) (hv : ∀ i, 0 < v i) (hf : A *ᵥ v = v) :
    (∑ σ : Equiv.Perm (H × Bool),
      (∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ)) ^ 2) ≤
    (Fintype.card (Equiv.Perm (H × Bool)) : ℝ) *
      (Fintype.card H + 1 : ℝ) ^ (Fintype.card C) ^ 2 := by
  obtain ⟨U, d, hU, hd, he⟩ := exists_orthogonal_diagonalization_bounded A hA hn v hv hf
  have hp (σ : Equiv.Perm (H × Bool)) :
      (∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ)) ^ 2 ≤
      (Fintype.card {f : H × Bool → C × C // pairConstant f ∧ pairConstant (f ∘ σ)} : ℝ) := by
    rw [← commonColorings_square, Nat.cast_pow]
    apply pow_le_pow_left₀
    · exact Finset.sum_nonneg (fun f _ => mul_nonneg (pairWeight_nonneg A hn f)
        (pairWeight_nonneg A hn (f ∘ σ)))
    · rw [he]
      exact pairWeight_overlap_le U d hU hd σ
  have h := (Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => hp σ)).trans
    (common_pairColorings_moment (H := H) (β := C × C))
  simpa only [Fintype.card_prod, pow_two] using h

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open Matrix


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.pairWeight_overlap_square_moment := @_root_.OAI.MatchingSmoothing.pairWeight_overlap_square_moment
