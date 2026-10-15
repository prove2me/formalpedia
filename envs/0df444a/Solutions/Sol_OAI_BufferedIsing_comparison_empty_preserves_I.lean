-- Prove2me | solution 1 for OAI.BufferedIsing.comparison_empty_preserves_I
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:32:07.141216+00:00
-- url     : https://prove2.me/submissions/1622e4ca-19bd-4c4f-9283-c492d10a5ec6

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/RandomCluster.lean:L30-L44
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.comparison_empty_preserves_I. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic

-- ---- from OAI.Probability.Ising.RandomCluster ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma comparison_empty_preserves_I {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J) (x y : KeptVertex F)
    (hxy : (comparisonSetoid G I J F ∅).r x y) :
    x.val ∈ I ↔ y.val ∈ I := by
  induction hxy with
  | rel x y h =>
    rcases h with h | h | ⟨e, he, _⟩
    · exact iff_of_true h.1 h.2
    · exact iff_of_false
        (fun hx => Finset.disjoint_left.mp hIJ hx h.1)
        (fun hy => Finset.disjoint_left.mp hIJ hy h.2)
    · exact (Finset.notMem_empty e he).elim
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J) (x y : KeptVertex F)
    (hxy : (comparisonSetoid G I J F ∅).r x y) :
    x.val ∈ I ↔ y.val ∈ I := by
  first
    | exact OAI.BufferedIsing.comparison_empty_preserves_I G I J F hIJ x y hxy
    | exact OAI.BufferedIsing.comparison_empty_preserves_I
    | (apply OAI.BufferedIsing.comparison_empty_preserves_I <;> assumption)
    | (intros; apply OAI.BufferedIsing.comparison_empty_preserves_I <;> assumption)
