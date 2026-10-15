-- Prove2me | solution 1 for OAI.MatchingEntropy.matching_covariance_second_variation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:33:19.115734+00:00
-- url     : https://prove2.me/submissions/c681f2cb-870c-4c1b-8682-92e8952b35df

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean:L203-L243
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.matching_covariance_second_variation. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_PerfectMatching_MatchingCovariance
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_mem_polytope_iff
import Theorems.Thm_OAI_MatchingEntropy_covariance_quadratic
import Theorems.Thm_OAI_MatchingEntropy_matching_defect_second_variation

-- ---- from OAI.Combinatorics.PerfectMatching.Entropy ----
namespace OAI

/-!
Finite Shannon entropy and attainment of its supremum over feasible matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] [DecidableEq V] in
theorem coordinate_mem_Icc (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) (e : E) : y e ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  constructor
  · exact Finset.sum_nonneg (fun M _ ↦ mul_nonneg (hp.1 M) (G.indicator_nonneg M e))
  · calc
      ∑ M, p M * G.indicator M e ≤ ∑ M, p M * 1 :=
        Finset.sum_le_sum (fun M _ ↦ mul_le_mul_of_nonneg_left (G.indicator_le_one M e) (hp.1 M))
      _ = 1 := by simpa using hp.2

end LooplessGraph

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

omit [Fintype V] [DecidableEq V] in
theorem sum_mean_assoc (G : LooplessGraph V E) (p : G.Matching → ℝ) (u : E → ℝ) :
    (∑ M, p M * (∑ e, u e * G.indicator M e)) = ∑ e, u e * G.mean p e := by
  simp only [LooplessGraph.mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro M _
  ring

omit [Fintype V] [DecidableEq V] in
theorem linearScore_expectation (G : LooplessGraph V E) (p : G.Matching → ℝ)
    (u : E → ℝ) (c : ℝ) :
    (∑ M, p M * linearScore G u c M) =
      (∑ e, u e * G.mean p e) - c * ∑ M, p M := by
  simp only [linearScore, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [sum_mean_assoc]
  ring

end MatchingEntropy

end

end OAI

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

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.MatchingCovariance ----
namespace OAI

/-!
Normalized matching covariance: face rank, exact trace, and second variation.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
theorem sum_positive_support (x f : E → ℝ) (hf : ∀ e, ¬ 0 < x e → f e=0) :
    (∑ e, f e) = ∑ e : {e // 0 < x e}, f e.val := by
  classical
  have hz : (∑ e : {e // ¬ 0 < x e}, f e.val)=0 :=
    Finset.sum_eq_zero fun e _ => hf e.val e.property
  have hh := Fintype.sum_subtype_add_sum_subtype (fun e => 0 < x e) f
  rw [hz,add_zero] at hh
  exact hh.symm

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_score (G : LooplessGraph V E) (x : E → ℝ)
    (u : {e // 0 < x e} → ℝ) (M : G.Matching) :
    linearScore G (matchingScoreWeights x u) (∑ e, matchingScoreWeights x u e*x e) M =
      matchingNormalized G x M ⬝ᵥ u := by
  classical
  unfold linearScore
  rw [← Finset.sum_sub_distrib]
  rw [sum_positive_support x _ (fun e he => by simp [matchingScoreWeights,LooplessGraph.positiveExtension,he])]
  rw [dotProduct]
  apply Finset.sum_congr rfl
  intro e _
  simp only [matchingScoreWeights,LooplessGraph.positiveExtension_pos,matchingNormalized,normalizedCentered]
  ring

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_mulVec (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (u : {e // 0 < x e} → ℝ) (e : {e // 0 < x e}) :
    (covariance p (matchingNormalized G x) *ᵥ u) e =
      G.mean (fun M => p M * linearScore G (matchingScoreWeights x u)
        (∑ e, matchingScoreWeights x u e*x e) M) e.val / Real.sqrt (x e.val) := by
  let a := linearScore G (matchingScoreWeights x u) (∑ e, matchingScoreWeights x u e*x e)
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  calc
    _ = ∑ M, (p M*a M*G.indicator M e.val-x e.val*(p M*a M))/Real.sqrt (x e.val) := by
      rw [covariance_mulVec hp.1.1]
      apply Finset.sum_congr rfl
      intro M _
      rw [← matchingNormalized_score G x u M]
      change p M*((G.indicator M e.val-x e.val)/Real.sqrt (x e.val))*a M = _
      ring
    _ = _ := by
      rw [← Finset.sum_div,Finset.sum_sub_distrib,← Finset.mul_sum,hcenter,mul_zero,sub_zero]
      rfl

omit [Fintype V] [DecidableEq V] in
/-- Convert the genuine second variation into the covariance spectral inequality. -/
theorem matching_covariance_second_variation (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x) {m : ℝ} (hm : 0 < m)
    (hmax : ∀ y ∈ G.polytope, entropyDefect G m y ≤ entropyDefect G m x)
    (u : {e // 0 < x e} → ℝ) :
    (8*Real.exp (-entropy x/m)-1)*
        ((covariance p (matchingNormalized G x) *ᵥ u) ⬝ᵥ
          (covariance p (matchingNormalized G x) *ᵥ u)) +
      u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) ≤ 0 := by
  let w := matchingScoreWeights x u
  let c := ∑ e, w e*x e
  let a := linearScore G w c
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a,c]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  have hh := matching_defect_second_variation G hp hopt hm.ne' hmax w c hcenter
  have hnorm : (∑ e, (G.mean (fun M => p M*a M) e)^2/x e) =
      (covariance p (matchingNormalized G x) *ᵥ u) ⬝ᵥ
        (covariance p (matchingNormalized G x) *ᵥ u) := by
    have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
    rw [sum_positive_support x _ (fun e he => by
      have hz : x e=0 := le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1
      simp [hz])]
    rw [dotProduct]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,← sq,div_pow,Real.sq_sqrt e.property.le]
  have hquad : (∑ M, p M*(a M)^2) = u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) := by
    rw [covariance_quadratic hp.1.1]
    apply Finset.sum_congr rfl
    intro M _
    rw [← matchingNormalized_score G x u M]
  change (8*Real.exp (-entropy x/m)-1)*(∑ e, (G.mean (fun M => p M*a M) e)^2/x e)+
    (8*Real.exp (-entropy x/m)/m)*(entropyLineD x (G.mean (fun M => p M*a M)) 0)^2+
    (∑ M, p M*(a M)^2) ≤ 0 at hh
  rw [hnorm,hquad] at hh
  have hpterm : 0 ≤ (8*Real.exp (-entropy x/m)/m)*
      (entropyLineD x (G.mean (fun M => p M*a M)) 0)^2 := by positivity
  linarith

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
open Matrix
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem solution (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x) {m : ℝ} (hm : 0 < m)
    (hmax : ∀ y ∈ G.polytope, entropyDefect G m y ≤ entropyDefect G m x)
    (u : {e // 0 < x e} → ℝ) :
    (8*Real.exp (-entropy x/m)-1)*
        ((covariance p (matchingNormalized G x) *ᵥ u) ⬝ᵥ
          (covariance p (matchingNormalized G x) *ᵥ u)) +
      u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) ≤ 0 := by
  first
    | exact OAI.MatchingEntropy.matching_covariance_second_variation G hp hopt hm hmax u
    | exact OAI.MatchingEntropy.matching_covariance_second_variation
    | (apply OAI.MatchingEntropy.matching_covariance_second_variation <;> assumption)
    | (intros; apply OAI.MatchingEntropy.matching_covariance_second_variation <;> assumption)
