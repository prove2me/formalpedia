-- Prove2me | solution 1 for GlobalTheory.DI.kaehlerZ_span_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:09:24.381503+00:00
-- url     : https://prove2.me/submissions/abd722d2-1d5f-4a66-b66d-d51fcff7fa79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtDAlgebraMapPowCharMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {K : Type} [CommRing K]
namespace GlobalTheory.DI
theorem _root_.solution {P : Ω[K⁄ℤ] → Prop} (v : Ω[K⁄ℤ]) (hD : ∀ a, P (KaehlerDifferential.D ℤ K a))
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : K) x, P x → P (c • x)) : P v := by
  have hv : v ∈ Submodule.span K (Set.range (KaehlerDifferential.D ℤ K)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hD a
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx
end GlobalTheory.DI
