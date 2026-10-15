-- Prove2me | solution 1 for OAI.MatchingEntropy.covariance_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:20:48.669656+00:00
-- url     : https://prove2.me/submissions/538879dd-a59d-4a34-864d-54b8f70bb5a0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Covariance.lean:L57-L72
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.covariance_quadratic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Covariance

-- ---- from OAI.Combinatorics.PerfectMatching.Covariance ----
namespace OAI

/-!
Positive semidefinite covariance matrices, rank, trace, and a spectral inequality.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem covariance_entry {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) (i j : I) :
    covariance p b i j = ∑ a, p a*b a i*b a j := by
  unfold covariance
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [weightedColumns, Matrix.transpose_apply]
  calc
    _ = (Real.sqrt (p a))^2 * b a i * b a j := by ring
    _ = _ := by rw [Real.sq_sqrt (hp a)]

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_mulVec {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ)
    (u : I → ℝ) (i : I) :
    (covariance p b *ᵥ u) i = ∑ a, p a*b a i*(b a ⬝ᵥ u) := by
  simp only [Matrix.mulVec, dotProduct, covariance_entry hp, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_quadratic {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ)
    (u : I → ℝ) : u ⬝ᵥ (covariance p b *ᵥ u) = ∑ a, p a*(b a ⬝ᵥ u)^2 := by
  rw [dotProduct]
  simp_rw [covariance_mulVec hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ i, u i*(p a*b a i*(b a ⬝ᵥ u))) =
      (∑ i, b a i*u i)*(p a*(b a ⬝ᵥ u)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = p a*(b a ⬝ᵥ u)^2 := by rw [← dotProduct]; ring

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
open Matrix
variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

omit [DecidableEq A] [DecidableEq I] in
theorem solution {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ)
    (u : I → ℝ) : u ⬝ᵥ (covariance p b *ᵥ u) = ∑ a, p a*(b a ⬝ᵥ u)^2 := by
  first
    | exact OAI.MatchingEntropy.covariance_quadratic hp b u
    | exact OAI.MatchingEntropy.covariance_quadratic
    | (apply OAI.MatchingEntropy.covariance_quadratic <;> assumption)
    | (intros; apply OAI.MatchingEntropy.covariance_quadratic <;> assumption)
