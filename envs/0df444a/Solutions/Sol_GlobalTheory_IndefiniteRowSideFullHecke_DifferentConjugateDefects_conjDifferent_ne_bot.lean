-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.conjDifferent_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:16.268802+00:00
-- url     : https://prove2.me/submissions/76d150f6-2d90-4a6a-9730-adef715cedb0

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
theorem _root_.solution {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) : conjDifferent σ ≠ ⊥ := by
  have hinj : Function.Injective (RingOfIntegers.mapRingHom σ) := by
    intro x y h
    apply RingOfIntegers.ext
    apply σ.injective
    simpa using congrArg (fun z : 𝓞 K => (z : K)) h
  unfold conjDifferent
  rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
  exact differentIdeal_ne_bot
end GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
