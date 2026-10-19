-- Prove2me | solution 1 for OAI.MatchingSmoothing.mem_of_fiber_indicators
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:41:22.633241+00:00
-- url     : https://prove2.me/submissions/9b0dbadc-7f79-479e-a10e-fdbd9ffa5a24

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/EdgeProducts.lean:L69-L95
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.mem_of_fiber_indicators. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts

-- ---- from OAI.Combinatorics.MatchingPSD.EdgeProducts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
variable {E : Type u_1} {X : Type u_2}

lemma mem_of_fiber_indicators {I : Type u_4} [Fintype I] [DecidableEq I]
    (θ : X → I) (f : X → ℝ) (S : Submodule ℝ (X → ℝ))
    (hf : ∀ a b, θ a = θ b → f a = f b)
    (hind : ∀ a, (fun b => if θ b = θ a then (1 : ℝ) else 0) ∈ S) : f ∈ S := by
  classical
  let g (i : I) : ℝ := if h : ∃ a, θ a = i then f h.choose else 0
  let b (i : I) : X → ℝ := fun a => if θ a = i then 1 else 0
  have hm (i : I) : g i • b i ∈ S := by
    by_cases hi : ∃ a, θ a = i
    · have hb : b i = b (θ hi.choose) := by rw [hi.choose_spec]
      rw [hb]
      exact S.smul_mem _ (hind hi.choose)
    · have hb : b i = 0 := by
        ext a
        have hn : θ a ≠ i := by intro h; exact hi ⟨a, h⟩
        simp [b, hn]
      simp [hb]
  have he : ∑ i, g i • b i = f := by
    ext a
    simp only [Finset.sum_apply, Pi.smul_apply, b, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have ha : ∃ c, θ c = θ a := ⟨a, rfl⟩
    dsimp [g]
    rw [dite_eq_left ha]
    exact hf ha.choose a ha.choose_spec
  rw [← he]
  exact S.sum_mem (fun i _ => hm i)

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.mem_of_fiber_indicators := @_root_.OAI.MatchingSmoothing.mem_of_fiber_indicators
