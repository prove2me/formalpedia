-- Prove2me | solution 1 for GlobalTheory.UnitCase.degL_eq_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:41:53.704261+00:00
-- url     : https://prove2.me/submissions/284424c9-3733-4d28-b5a1-faf0a5b64fad

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution {n : ℕ} {p : PVar n →₀ ℕ} {b : Fin n} (h : ∀ x ∈ p.support, rowOf x = b) :
    degL p = rowDegZ p b := by
  refine Finset.sum_eq_single b (fun b' _ hb => Finset.sum_eq_zero fun c _ => ?_) (by simp)
  by_contra h0
  exact hb (h _ (Finsupp.mem_support_iff.2 h0))
end GlobalTheory.UnitCase
