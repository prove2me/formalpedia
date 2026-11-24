-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.span_natCast_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:12.491858+00:00
-- url     : https://prove2.me/submissions/85bd9172-0186-4c5f-9080-3090597a97e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
namespace GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
theorem _root_.solution {K : Type} [Field K] [NumberField K] (n' : ℕ+) :
    Ideal.span {((n' : ℕ) : 𝓞 K)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast n'.ne_zero
end GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
