-- Prove2me | solution 1 for GlobalTheory.Prism.Obj.crys_quot_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:05:27.233092+00:00
-- url     : https://prove2.me/submissions/0dc3f0c0-2d9a-4b34-8ef9-d76b74c636f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InvertibleSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Prism
attribute [instance] Obj.ring
variable {l : ℕ} {R : Type} [CommRing R]
attribute [instance] FCrys.acg FCrys.mod
attribute [instance] VBun.acg VBun.mod
namespace GlobalTheory.Prism
namespace Obj
theorem _root_.solution (l : ℕ) [Fact l.Prime] :
    Nontrivial ((Obj.crys l).A ⧸ (Obj.crys l).I) := by
  change Nontrivial (ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l])})
  rw [← PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.Quotient.nontrivial_iff.2 (IsLocalRing.maximalIdeal.isMaximal _).ne_top
end Obj
end GlobalTheory.Prism
