-- Prove2me | solution 1 for GlobalTheory.RegularAscent.isRegularLocalRing_of_quotient_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:15:29.117909+00:00
-- url     : https://prove2.me/submissions/623d46bc-4cb5-4547-b9b5-34a667deae0a

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingOfRegularQuotient
import Theorems.Thm_GlobalTheory_RegularAscent_height_add_ringKrullDim_quotient_le
import Theorems.Thm_GlobalTheory_RegularAscent_spanFinrank_maximalIdeal_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.RegularAscent
namespace GlobalTheory.RegularAscent
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
      (r : ℕ) (f : Fin r → R), p = Ideal.span (Set.range f) → p.height = r →
      IsRegularLocalRing (R ⧸ p) → IsRegularLocalRing R := by
  intro R _ _ _ p _ r f hf hh hreg
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hfg : (maximalIdeal (R ⧸ p)).FG := IsNoetherian.noetherian _
  have hs := spanFinrank_maximalIdeal_le p r f hf hfg
  have hq : ((maximalIdeal (R ⧸ p)).spanFinrank : WithBot ℕ∞) = ringKrullDim (R ⧸ p) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hd := height_add_ringKrullDim_quotient_le p
  rw [hh, ← hq] at hd
  refine le_trans ?_ hd
  have : (((maximalIdeal R).spanFinrank : ℕ) : WithBot ℕ∞) ≤
      (((r + (maximalIdeal (R ⧸ p)).spanFinrank : ℕ)) : WithBot ℕ∞) := by exact_mod_cast hs
  refine this.trans (le_of_eq ?_)
  push_cast
  rfl
end GlobalTheory.RegularAscent
