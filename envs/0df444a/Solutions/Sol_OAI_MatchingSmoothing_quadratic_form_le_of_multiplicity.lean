-- Prove2me | solution 1 for OAI.MatchingSmoothing.quadratic_form_le_of_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:08:27.265645+00:00
-- url     : https://prove2.me/submissions/49741ed7-d2a3-4527-a4e2-2af6effe5230

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/SpectralMultiplicity.lean:L55-L72
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.quadratic_form_le_of_multiplicity. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels

-- ---- from OAI.Combinatorics.MatchingPSD.SpectralMultiplicity ----
namespace OAI

universe u_1

namespace MatchingSmoothing

open scoped RealInnerProductSpace

variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma trace_square_eq_sum_eigenvalue_sq (B : Module.End ℝ E) (hB : B.IsSymmetric) :
    LinearMap.trace ℝ E (B * B) =
      ∑ i, (hB.eigenvalues (n := Module.finrank ℝ E) rfl i) ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ (hB.eigenvectorBasis rfl)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Module.End.mul_apply, hB.apply_eigenvectorBasis rfl, map_smul,
    real_inner_smul_right, OrthonormalBasis.inner_eq_one, mul_one]
  simp [pow_two]

lemma eigenspace_dim_mul_sq_le_trace_square (B : Module.End ℝ E) (hB : B.IsSymmetric)
    (c : ℝ) :
    (Module.finrank ℝ (Module.End.eigenspace B c) : ℝ) * c ^ 2 ≤
      LinearMap.trace ℝ E (B * B) := by
  classical
  let ev :=  hB.eigenvalues (n := Module.finrank ℝ E) rfl
  let s := Finset.univ.filter fun i => ev i = c
  have hcard : s.card = Module.finrank ℝ (Module.End.eigenspace B c) :=
    hB.card_filter_eigenvalues_eq rfl c
  have he : ∑ i ∈ s, ev i ^ 2 = (s.card : ℝ) * c ^ 2 := by
    calc
      ∑ i ∈ s, ev i ^ 2 = ∑ _i ∈ s, c ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = _ := by simp
  rw [trace_square_eq_sum_eigenvalue_sq B hB, ← hcard, ← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun _ _ _ => sq_nonneg _)

lemma quadratic_form_le_of_eigenvalues_le (B : Module.End ℝ E) (hB : B.IsSymmetric)
    (a : ℝ) (ha : ∀ i, hB.eigenvalues (n := Module.finrank ℝ E) rfl i ≤ a)
    (x : E) : ⟪x, B x⟫ ≤ a * ‖x‖ ^ 2 := by
  let b := hB.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  rw [← b.sum_inner_mul_inner x (B x), ← b.sum_sq_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have he : B (b i) = (hB.eigenvalues rfl i) • b i := hB.apply_eigenvectorBasis rfl i
  rw [← hB (b i) x, he, real_inner_smul_left, real_inner_comm x (b i)]
  nlinarith [sq_nonneg (inner ℝ (b i) x), ha i]

lemma quadratic_form_le_of_multiplicity (B : Module.End ℝ E) (hB : B.IsSymmetric)
    (m H a : ℝ) (hm : 0 < m) (ha : 0 ≤ a)
    (hdim : ∀ c : ℝ, c ≠ 0 → Module.End.HasEigenvalue B c →
      m ≤ Module.finrank ℝ (Module.End.eigenspace B c))
    (htrace : LinearMap.trace ℝ E (B * B) ≤ H)
    (hHa : H ≤ m * a ^ 2) (x : E) : ⟪x, B x⟫ ≤ a * ‖x‖ ^ 2 := by
  apply quadratic_form_le_of_eigenvalues_le B hB a _ x
  intro i
  let c := hB.eigenvalues (n := Module.finrank ℝ E) rfl i
  by_cases hc : c = 0
  · simpa only [← show c = hB.eigenvalues rfl i from rfl, hc] using ha
  · have hd := hdim c hc (hB.hasEigenvalue_eigenvalues rfl i)
    have he := eigenspace_dim_mul_sq_le_trace_square B hB c
    have hsq : m * c ^ 2 ≤ m * a ^ 2 :=
      (mul_le_mul_of_nonneg_right hd (sq_nonneg c)).trans (he.trans (htrace.trans hHa))
    have hle : c ^ 2 ≤ a ^ 2 := (mul_le_mul_iff_right₀ hm).mp hsq
    change c ≤ a
    nlinarith

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.quadratic_form_le_of_multiplicity := @_root_.OAI.MatchingSmoothing.quadratic_form_le_of_multiplicity
