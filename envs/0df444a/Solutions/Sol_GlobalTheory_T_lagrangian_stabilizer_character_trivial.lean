-- Prove2me | solution 1 for GlobalTheory.T.lagrangian_stabilizer_character_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:17:07.854986+00:00
-- url     : https://prove2.me/submissions/62f5f6f3-1ab4-43b1-a40f-f6a29df60c21

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrderStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_char_trivial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [Invertible (2 : F)] (E : Type) [CommRing E] [Algebra F E] (c : E →ₐ[F] E) (ξ : E) (β ν : Type) [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] (J : Matrix β β E) (Cy : Matrix β ν E), IsQuad c ξ → IsHerm c J → IsLagr c J Cy → ∀ lam : UG c J →* ℂˣ, (∀ (p : UG c J) (t : GL ν E), ((p : GL β E) : Matrix β β E) * Cy = Cy * (t : Matrix ν ν E) → lam p = 1) → lam = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelChar.char_trivial | exact GlobalTheory.CompanionTheory.SiegelChar.char_trivial | (intros; apply GlobalTheory.CompanionTheory.SiegelChar.char_trivial <;> assumption)
end _root_.GlobalTheory.T
