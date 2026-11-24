-- Prove2me | solution 1 for GlobalTheory.finite_algHom_of_isFiniteSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:49:01.52777+00:00
-- url     : https://prove2.me/submissions/85956662-b43c-404d-b659-8460c0dfa922

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
import Theorems.Thm_GlobalTheory_exists_algEquiv_fin_points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
open GlobalTheory
variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field E]
  [Algebra R E] [IsFiniteSplit E (E ⊗[R] S)]
variable (R S)
namespace GlobalTheory
theorem _root_.solution : Finite (S →ₐ[R] E) := by
  obtain ⟨n, P, -⟩ := exists_algEquiv_fin_points R S E
  exact Finite.of_equiv _ P
end GlobalTheory
