-- Prove2me | solution 1 for OAI.MatchingSmoothing.mul_mem_lowDegree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:39:50.678704+00:00
-- url     : https://prove2.me/submissions/7327dba2-0399-43d8-b8c3-5fdc734d4852

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/EdgeProducts.lean:L29-L46
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.mul_mem_lowDegree. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts

-- ---- from OAI.Combinatorics.MatchingPSD.EdgeProducts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
variable {E : Type u_1} {X : Type u_2}

lemma mul_mem_lowDegree (x : E → X → ℝ) {d e : ℕ} {f g : X → ℝ}
    (hf : f ∈ lowDegree x d) (hg : g ∈ lowDegree x e) :
    f * g ∈ lowDegree x (d + e) := by
  refine Submodule.span_induction₂
    (p := fun f g _ _ => f * g ∈ lowDegree x (d + e)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf hg
  · rintro f g ⟨l, hl, rfl⟩ ⟨m, hm, rfl⟩
    apply Submodule.subset_span
    exact ⟨l ++ m, by simpa using Nat.add_le_add hl hm, by simp⟩
  · intro g _; simp
  · intro f _; simp
  · intro f g h _ _ _ hf hg
    simpa only [add_mul] using (lowDegree x (d + e)).add_mem hf hg
  · intro f g h _ _ _ hg hh
    simpa only [mul_add] using (lowDegree x (d + e)).add_mem hg hh
  · intro r f g _ _ h
    simpa only [smul_mul_assoc] using (lowDegree x (d + e)).smul_mem r h
  · intro r f g _ _ h
    simpa only [mul_smul_comm] using (lowDegree x (d + e)).smul_mem r h

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.mul_mem_lowDegree := @_root_.OAI.MatchingSmoothing.mul_mem_lowDegree
