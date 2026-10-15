-- Prove2me | solution 1 for OAI.MatchingEntropy.covariance_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:22:10.185222+00:00
-- url     : https://prove2.me/submissions/bd94c498-1d26-4ecb-841d-d0163cb0200a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Covariance.lean:L154-L193
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.covariance_rank_bound. The node keeps its source
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

/-- Spectral form of the second-variation step, using the full (possibly
singular) covariance rather than introducing an inverse on its image. -/
theorem covariance_rank_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {a : ℝ}
    (hsecond : ∀ u : ι → ℝ,
      (a - 1) * ((C *ᵥ u) ⬝ᵥ (C *ᵥ u)) + u ⬝ᵥ (C *ᵥ u) ≤ 0) :
    (C.rank : ℝ) ≤ (1-a) * C.trace := by
  let eig := hC.isHermitian.eigenvalues
  have heig : ∀ i, 0 ≤ eig i := hC.eigenvalues_nonneg
  have hone : ∀ i, eig i ≠ 0 → 1 ≤ (1-a) * eig i := by
    intro i hi
    let v : ι → ℝ := hC.isHermitian.eigenvectorBasis i
    have hv : v ⬝ᵥ v = 1 := by
      have hn := hC.isHermitian.eigenvectorBasis.orthonormal.1 i
      have hi : inner ℝ (hC.isHermitian.eigenvectorBasis i)
          (hC.isHermitian.eigenvectorBasis i) = 1 := by
        rw [real_inner_self_eq_norm_sq, hn]
        norm_num
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hi
    have he : C *ᵥ v = eig i • v := hC.isHermitian.mulVec_eigenvectorBasis i
    have hs := hsecond v
    rw [he] at hs
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hv, mul_one] at hs
    have hp : 0 < eig i := lt_of_le_of_ne (heig i) (Ne.symm hi)
    nlinarith
  rw [hC.isHermitian.rank_eq_card_non_zero_eigs,
    hC.isHermitian.trace_eq_sum_eigenvalues]
  change (Fintype.card {i // eig i ≠ 0} : ℝ) ≤ (1-a) * ∑ i, eig i
  rw [Finset.mul_sum]
  calc
    _ = ∑ i : {i // eig i ≠ 0}, (1 : ℝ) := by simp
    _ ≤ ∑ i : {i // eig i ≠ 0}, (1-a) * eig i := Finset.sum_le_sum fun i _ => hone i i.property
    _ = ∑ i, (1-a) * eig i := by
      have hz : (∑ i : {i // ¬ eig i ≠ 0}, (1-a) * eig i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [not_ne_iff.mp i.property, mul_zero]
      simpa only [hz, add_zero] using
        (Fintype.sum_subtype_add_sum_subtype (fun i => eig i ≠ 0)
          (fun i => (1-a) * eig i))

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
open Matrix
variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {a : ℝ}
    (hsecond : ∀ u : ι → ℝ,
      (a - 1) * ((C *ᵥ u) ⬝ᵥ (C *ᵥ u)) + u ⬝ᵥ (C *ᵥ u) ≤ 0) :
    (C.rank : ℝ) ≤ (1-a) * C.trace := by
  first
    | exact OAI.MatchingEntropy.covariance_rank_bound hC hsecond
    | exact OAI.MatchingEntropy.covariance_rank_bound
    | (apply OAI.MatchingEntropy.covariance_rank_bound <;> assumption)
    | (intros; apply OAI.MatchingEntropy.covariance_rank_bound <;> assumption)
