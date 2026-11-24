-- Prove2me | solution 1 for GlobalTheory.T.linearIndependent_kaehlerD_of_algebraicIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:17:09.14081+00:00
-- url     : https://prove2.me/submissions/963d200e-a75a-4e35-a6f1-e195c9da562c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentKaehlerDOfAlgebraicIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentKaehlerDOfAlgebraicIndependentStatement
import Theorems.Thm_GlobalTheory_BertiniAlg_linearIndependent_D_of_algebraicIndependent


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
theorem _root_.solution : ∀ (k κ : Type) [Field k] [CharZero k] [Field κ] [Algebra k κ] [Algebra.EssFiniteType k κ] {σ : Type} (t : σ → κ), AlgebraicIndependent k t → LinearIndependent κ (fun s => KaehlerDifferential.D k κ (t s)) := by
  first | exact @GlobalTheory.BertiniAlg.linearIndependent_D_of_algebraicIndependent | exact GlobalTheory.BertiniAlg.linearIndependent_D_of_algebraicIndependent | (intros; apply GlobalTheory.BertiniAlg.linearIndependent_D_of_algebraicIndependent <;> assumption)
end _root_.GlobalTheory.T
