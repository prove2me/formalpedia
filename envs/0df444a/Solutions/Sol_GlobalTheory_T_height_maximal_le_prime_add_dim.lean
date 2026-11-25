-- Prove2me | solution 1 for GlobalTheory.T.height_maximal_le_prime_add_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:29.618814+00:00
-- url     : https://prove2.me/submissions/68692c6f-7199-4785-a3f2-30fe7d35a032

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeightMaximalLePrimeAddDim
import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeightMaximalLePrimeAddDimStatement
import Theorems.Thm_GlobalTheory_FinTypeIntCatenary_height_maximal_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] (P M : Ideal A) [P.IsPrime] [M.IsMaximal], (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by
  first | exact @GlobalTheory.FinTypeIntCatenary.height_maximal_le | exact GlobalTheory.FinTypeIntCatenary.height_maximal_le | (intros; apply GlobalTheory.FinTypeIntCatenary.height_maximal_le <;> assumption)
end _root_.GlobalTheory.T
