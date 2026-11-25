-- Prove2me | solution 1 for GlobalTheory.MinorGerm.monAl_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:15.802882+00:00
-- url     : https://prove2.me/submissions/13fcddcc-ec79-4fcd-ad99-43ce1b1999ff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type} {N N' : ℕ}
namespace GlobalTheory.MinorGerm
theorem _root_.solution (e : ℕ → ℕ) (ρ : ℕ) :
    monAl N N' e ρ = ∑ k ∈ Finset.Icc 1 (min N N'), if ρ < k then e k else 0 := by
  classical
  unfold monAl
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_Icc, Finset.mem_filter]
  omega
end GlobalTheory.MinorGerm
