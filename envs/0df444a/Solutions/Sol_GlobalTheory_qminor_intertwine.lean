-- Prove2me | solution 1 for GlobalTheory.qminor_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:18:55.823869+00:00
-- url     : https://prove2.me/submissions/326939e9-21a6-4036-985e-377f8cabdfad

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorIntertwiningApply
import Theorems.Thm_GlobalTheory_ofFn_prod_intertwine

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
theorem _root_.solution : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V), (∀ a b w, ι (E' a b w) = E a b (ι w)) → ∀ (a b : Fin t → Fin n) (u : ℂ) (w : W), ι (qminor E' a b u w) = qminor E a b u (ι w) := by
  intro V W _ _ _ _ n t E E' ι h a b u w
  have hT : ∀ (u : ℂ) (a b : Fin n) (w : W), ι (Tm E' u a b w) = Tm E u a b (ι w) := by
    intro u a b w
    unfold Tm
    split_ifs <;> simp [h, Module.algebraMap_end_apply]
  unfold qminor
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply,
    Module.End.intCast_apply, map_zsmul]
  congr 1
  exact ofFn_prod_intertwine ι t _ _ (fun k w => hT _ _ _ w) w
end GlobalTheory
