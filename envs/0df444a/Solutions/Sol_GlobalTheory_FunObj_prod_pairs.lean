-- Prove2me | solution 1 for GlobalTheory.FunObj.prod_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:54.653641+00:00
-- url     : https://prove2.me/submissions/f12cbcad-f147-4130-83ad-ce80f1bc34f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
import Theorems.Thm_GlobalTheory_FunObj_prod_even_succ_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat
namespace GlobalTheory.FunObj
theorem _root_.solution (q : ℕ) (a : Fin (2 * q + 1) → ℂ) :
    ∏ j : Fin (2 * q + 1), a j = (∏ j : Fin (2 * q), if Even j.1 then a ⟨j, by omega⟩ * a ⟨j + 1, by omega⟩ else 1) *
      a ⟨2 * q, by omega⟩ := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h := ih (fun j => a (j.succ.succ : Fin (2 * q + 3)))
    erw [prod_even_succ_succ (2 * q), Fin.prod_univ_succ (n := 2 * q + 2), Fin.prod_univ_succ (n := 2 * q + 1), h]
    simp only [← mul_assoc]
    rfl
end GlobalTheory.FunObj
