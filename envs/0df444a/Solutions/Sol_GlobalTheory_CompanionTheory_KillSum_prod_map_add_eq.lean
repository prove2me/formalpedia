-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KillSum.prod_map_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:40:51.071842+00:00
-- url     : https://prove2.me/submissions/e6ed49bd-0492-4a82-a116-8eda0581bc94

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorSumAnnihilator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KillSum
namespace GlobalTheory.CompanionTheory.KillSum
theorem _root_.solution {R α : Type*} [CommRing R] (P : Multiset α) (f : α → R) (w : R) :
    ∃ q, (P.map fun a => f a + w).prod = (P.map f).prod + w * q := by
  induction P using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons a s ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨(s.map f).prod + f a * q + w * q, ?_⟩
    simp only [Multiset.map_cons, Multiset.prod_cons, hq]
    ring
end GlobalTheory.CompanionTheory.KillSum
