-- Prove2me | solution 1 for GlobalTheory.T.exists_rational_fock_projection_maximal_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:41:27.208069+00:00
-- url     : https://prove2.me/submissions/44ab9982-4c5b-478a-b2a0-f7669a1b10a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsRationalFockProjectionMaximalMinors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsRationalFockProjectionMaximalMinorsStatement
import Theorems.Thm_GlobalTheory_MinorFrame_RatProj_exists_rat_proj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℚ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), ∀ T : GlobalTheory.MinorFrame.Tup ι a d n,
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.prodMinors T)
      (MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (U p)) = 0 := by
  first | exact @GlobalTheory.MinorFrame.RatProj.exists_rat_proj | exact GlobalTheory.MinorFrame.RatProj.exists_rat_proj | (intros; apply GlobalTheory.MinorFrame.RatProj.exists_rat_proj <;> assumption)
end _root_.GlobalTheory.T
