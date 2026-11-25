-- Prove2me | solution 1 for GlobalTheory.ofFn_prod_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:34:15.583978+00:00
-- url     : https://prove2.me/submissions/5a3606b6-e820-4566-9cad-ce83bf0c7368

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorIntertwiningApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ι : W →ₗ[ℂ] V) : ∀ (t : ℕ) (f : Fin t → Module.End ℂ V)
    (g : Fin t → Module.End ℂ W), (∀ k w, ι (g k w) = f k (ι w)) →
    ∀ w, ι ((List.ofFn g).prod w) = (List.ofFn f).prod (ι w) := by
  intro t
  induction t with
  | zero => intro f g _ w; simp
  | succ t ih =>
    intro f g h w
    simp only [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    rw [h, ih (fun i => f i.succ) (fun i => g i.succ) (fun k => h k.succ)]
end GlobalTheory
