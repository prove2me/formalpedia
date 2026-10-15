-- Prove2me | solution 1 for OAI.BufferedIsing.jointWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:31:02.2636+00:00
-- url     : https://prove2.me/submissions/33cfc7ae-23e2-459e-9c52-7cb1d076e325

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Basic.lean:L139-L154
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.jointWeight_pos. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic

-- ---- from OAI.Probability.Ising.Basic ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma weight_pos {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ : Spins n) : 0 < weight G h σ := Real.exp_pos _

lemma constrainedSum_pos {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (P : Spins n → Prop) (σ : Spins n) (hσ : P σ) :
    0 < constrainedSum G h P := by
  classical
  apply lt_of_lt_of_le (weight_pos G h σ)
  unfold constrainedSum
  exact Finset.single_le_sum (fun τ _ => by
    split_ifs
    · exact (weight_pos G h τ).le
    · exact le_rfl) (Finset.mem_univ σ) |>.trans' (by simp [hσ])

lemma jointWeight_pos {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (τ a b : Spins n) : 0 < jointWeight G h I J F τ a b := by
  classical
  apply constrainedSum_pos G h _ (fun v => if v ∈ I then a v else if v ∈ J then b v else τ v)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    simp [hv]
  · intro v hv
    have hi : v ∉ I := fun hvi => (Finset.disjoint_left.mp hIJ) hvi hv
    simp [hi, hv]
  · intro v hv
    have hi : v ∉ I := fun hvi => (Finset.disjoint_left.mp hIF) hvi hv
    have hj : v ∉ J := fun hvj => (Finset.disjoint_left.mp hJF) hvj hv
    simp [hi, hj]

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (τ a b : Spins n) : 0 < jointWeight G h I J F τ a b := by
  first
    | exact OAI.BufferedIsing.jointWeight_pos G h I J F hIJ hIF hJF τ a b
    | exact OAI.BufferedIsing.jointWeight_pos
    | (apply OAI.BufferedIsing.jointWeight_pos <;> assumption)
    | (intros; apply OAI.BufferedIsing.jointWeight_pos <;> assumption)
