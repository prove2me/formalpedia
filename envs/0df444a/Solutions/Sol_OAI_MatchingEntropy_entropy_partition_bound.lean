-- Prove2me | solution 1 for OAI.MatchingEntropy.entropy_partition_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:39:56.735449+00:00
-- url     : https://prove2.me/submissions/71073169-c06c-4387-84f1-b796ac293940

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Duality.lean:L44-L73
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.entropy_partition_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality

-- ---- from OAI.Combinatorics.PerfectMatching.Optimizer ----
namespace OAI

/-!
Support and first-order identities for entropy-maximizing matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Supporting-line inequality for -x log x, with no positivity assumption
on the comparison probability x. -/
theorem negMulLog_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    Real.negMulLog x ≤ -x * Real.log y + y-x := by
  have h := mul_le_mul_of_nonneg_left
    (Real.negMulLog_le_one_sub_self (div_nonneg hx hy.le)) hy.le
  have he : Real.negMulLog x = -x * Real.log y + y * Real.negMulLog (x/y) := by
    calc
      Real.negMulLog x = Real.negMulLog (y * (x/y)) := by congr 1; field_simp
      _ = (x/y) * Real.negMulLog y + y * Real.negMulLog (x/y) := Real.negMulLog_mul _ _
      _ = _ := by unfold Real.negMulLog; field_simp
  rw [he]
  have hdiv : y * (x/y) = x := by field_simp
  nlinarith

/-- Gibbs' inequality on a finite set, with the exact support condition
needed on boundary faces. -/
theorem entropy_le_crossEntropy {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (hq : q ∈ probabilitySimplex ι)
    (hsupp : ∀ i, p i = 0 → q i = 0) :
    entropy q ≤ -∑ i, q i * Real.log (p i) := by
  have hterm : ∀ i, Real.negMulLog (q i) ≤
      -(q i * Real.log (p i)) + p i-q i := by
    intro i
    by_cases hi : p i = 0
    · simp [hi, hsupp i hi]
    · simpa only [neg_mul] using negMulLog_tangent (hq.1 i)
        (lt_of_le_of_ne (hp.1 i) (Ne.symm hi))
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, hp.2, hq.2, add_sub_cancel_right, entropy] using hh

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Duality ----
namespace OAI

/-!
Finite exponential tilts, partition functions, and entropy duality on a face.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem partition_pos {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) : 0 < partition p a t := by
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hp.1 i)).mp
    (show 0 < ∑ i, p i by rw [hp.2]; norm_num)
  exact (Finset.sum_pos_iff_of_nonneg (fun i _ => mul_nonneg (hp.1 i) (Real.exp_pos _).le)).mpr
    ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩

theorem tiltedLaw_mem_simplex {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) :
    tiltedLaw p a t ∈ probabilitySimplex ι := by
  refine ⟨fun i => div_nonneg (mul_nonneg (hp.1 i) (Real.exp_pos _).le)
    (partition_pos hp a t).le, ?_⟩
  simp only [tiltedLaw, ← Finset.sum_div]
  exact div_self (partition_pos hp a t).ne'

/-- Gibbs' variational inequality for the explicit finite partition function,
including all boundary laws supported on p. -/
theorem entropy_partition_bound {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (hq : q ∈ probabilitySimplex ι)
    (hsupp : ∀ i, p i = 0 → q i = 0) (a : ι → ℝ) (t : ℝ) :
    entropy q ≤ Real.log (partition p a t) - ∑ i, q i*Real.log (p i) -
      t * ∑ i, q i*a i := by
  have hlog : ∀ i, q i * Real.log (tiltedLaw p a t i) =
      q i * Real.log (p i) + t*(q i*a i) - q i*Real.log (partition p a t) := by
    intro i
    by_cases hi : p i = 0
    · simp [hsupp i hi]
    · rw [tiltedLaw, Real.log_div (mul_ne_zero hi (Real.exp_ne_zero _))
        (partition_pos hp a t).ne', Real.log_mul hi (Real.exp_ne_zero _), Real.log_exp]
      ring
  calc
    entropy q ≤ -∑ i, q i*Real.log (tiltedLaw p a t i) :=
      entropy_le_crossEntropy (tiltedLaw_mem_simplex hp a t) hq (by
        intro i hi
        have hii : p i = 0 := by
          have := (div_eq_zero_iff).mp hi
          rcases this with hh | hh
          · exact (mul_eq_zero.mp hh).resolve_right (Real.exp_ne_zero _)
          · exact ((partition_pos hp a t).ne' hh).elim
        exact hsupp i hii)
    _ = _ := by
      simp_rw [hlog]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, hq.2, one_mul]
      ring

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (hq : q ∈ probabilitySimplex ι)
    (hsupp : ∀ i, p i = 0 → q i = 0) (a : ι → ℝ) (t : ℝ) :
    entropy q ≤ Real.log (partition p a t) - ∑ i, q i*Real.log (p i) -
      t * ∑ i, q i*a i := by
  first
    | exact OAI.MatchingEntropy.entropy_partition_bound hp hq hsupp a t
    | exact OAI.MatchingEntropy.entropy_partition_bound
    | (apply OAI.MatchingEntropy.entropy_partition_bound <;> assumption)
    | (intros; apply OAI.MatchingEntropy.entropy_partition_bound <;> assumption)
