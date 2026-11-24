-- Prove2me | solution 1 for GlobalTheory.isLyndon_of_pairwise_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:36.089023+00:00
-- url     : https://prove2.me/submissions/1446eb8d-85b5-4b93-a673-02eb1b0f6228

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Shuffle
namespace GlobalTheory
theorem _root_.solution {A : Type} [LinearOrder A] {w : List A} (hw : w ≠ [])
    (h : w.Pairwise (· < ·)) : IsLyndon w := by
  refine ⟨hw, fun u v hu hv e => ?_⟩
  subst e
  obtain ⟨a, u, rfl⟩ := List.exists_cons_of_ne_nil hu
  obtain ⟨b, v, rfl⟩ := List.exists_cons_of_ne_nil hv
  exact List.Lex.rel ((List.pairwise_cons.1 h).1 b (by simp))
end GlobalTheory
