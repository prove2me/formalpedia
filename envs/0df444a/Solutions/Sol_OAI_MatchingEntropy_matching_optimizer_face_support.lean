-- Prove2me | solution 1 for OAI.MatchingEntropy.matching_optimizer_face_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:38:40.997567+00:00
-- url     : https://prove2.me/submissions/2bd49a40-8998-4b8d-9887-bdeaced1118c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean:L212-L239
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.matching_optimizer_face_support. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Theorems.Thm_OAI_MatchingEntropy_exists_pos_nonneg_perturb
import Theorems.Thm_OAI_MatchingEntropy_matching_optimizer_support

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

omit [Fintype V] [DecidableEq V] in
/-- The support of an optimizing law is a face: every law at a mean generated
by that support is itself supported there. This avoids assuming a face
representation of the marginal polytope in the entropy-optimization step. -/
theorem matching_optimizer_face_support (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {q r : G.Matching → ℝ} (hq : q ∈ probabilitySimplex G.Matching)
    (hr : r ∈ probabilitySimplex G.Matching) (hmean : G.mean q = G.mean r)
    (hrsupport : ∀ M, p M = 0 → r M = 0) :
    ∀ M, p M = 0 → q M = 0 := by
  obtain ⟨t, htp, ht⟩ := exists_pos_nonneg_perturb p (q-r) hp.1.1
    (fun M hM => by simpa [hrsupport M hM] using hq.1 M)
  have hsum : ∑ M, (p M+t*(q-r) M) = 1 := by
    simp only [Pi.sub_apply, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hp.1.2, hq.2, hr.2]
    ring
  have hmean' : G.mean (fun M => p M+t*(q-r) M) = y := by
    change G.meanLinear (p+t • (q-r)) = y
    rw [map_add, map_smul, map_sub]
    change G.mean p + t • (G.mean q-G.mean r) = y
    rw [hp.2, hmean, sub_self, smul_zero, add_zero]
  intro M hM
  by_contra hqM
  have hqMp : 0 < q M := lt_of_le_of_ne (hq.1 M) (Ne.symm hqM)
  have hpM := matching_optimizer_support G hp ⟨⟨ht, hsum⟩, hmean'⟩ hopt
    (M := M) (by simpa [hM, hrsupport M hM] using mul_pos htp hqMp)
  simp [hM] at hpM

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem solution (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {q r : G.Matching → ℝ} (hq : q ∈ probabilitySimplex G.Matching)
    (hr : r ∈ probabilitySimplex G.Matching) (hmean : G.mean q = G.mean r)
    (hrsupport : ∀ M, p M = 0 → r M = 0) :
    ∀ M, p M = 0 → q M = 0 := by
  first
    | exact OAI.MatchingEntropy.matching_optimizer_face_support G hp hopt hq hr hmean hrsupport
    | exact OAI.MatchingEntropy.matching_optimizer_face_support
    | (apply OAI.MatchingEntropy.matching_optimizer_face_support <;> assumption)
    | (intros; apply OAI.MatchingEntropy.matching_optimizer_face_support <;> assumption)
