-- Prove2me | solution 1 for GlobalTheory.Lyndon.aeval_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:41:22.753836+00:00
-- url     : https://prove2.me/submissions/8e082e73-d192-4b0d-98cd-6a650f166302

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_word_mem_of_lyndon_mem

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
open GlobalTheory.Lyndon
variable {A : Type} [LinearOrder A]
open ShuffleAlgebra
variable (K : Type) [Field K]
namespace GlobalTheory.Lyndon
theorem _root_.solution [CharZero K] : Function.Surjective
    (MvPolynomial.aeval (fun l : {w : List A // IsLyndon w} => word K l.1) :
      MvPolynomial {w : List A // IsLyndon w} K →ₐ[K] ShuffleAlgebra K A) := by
  intro x
  change x ∈ AlgHom.range _
  rw [← (wordBasis K A).linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Subalgebra.sum_mem _ fun v _ => Subalgebra.smul_mem _ ?_ _
  exact word_mem_of_lyndon_mem K _
    (fun l hl => (AlgHom.mem_range _).2 ⟨MvPolynomial.X ⟨l, hl⟩, MvPolynomial.aeval_X _ _⟩) v
end GlobalTheory.Lyndon
