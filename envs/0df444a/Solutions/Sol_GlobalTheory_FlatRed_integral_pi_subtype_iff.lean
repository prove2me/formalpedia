-- Prove2me | solution 1 for GlobalTheory.FlatRed.integral_pi_subtype_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:37:12.631913+00:00
-- url     : https://prove2.me/submissions/d30530d3-6115-4889-9ac4-3353fae5200c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqZeroOfFlatMapColumnZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.FlatRed
open GlobalTheory.FlatFactor GlobalTheory.LocFlat
namespace GlobalTheory.FlatRed
theorem _root_.solution {k α : Type} [MeasurableSpace k] {P Q : α → Prop} {i1 : Fintype (Subtype P)}
    {i2 : Fintype (Subtype Q)} (h : ∀ a, P a ↔ Q a) (ν : Measure k) (F : (Subtype P → k) → ℂ)
    (G : (Subtype Q → k) → ℂ) (hFG : ∀ a, F a = G (fun e => a ⟨e.1, (h e.1).2 e.2⟩)) :
    ∫ a, F a ∂(Measure.pi fun _ => ν) = ∫ e, G e ∂(Measure.pi fun _ => ν) := by
  obtain rfl : P = Q := funext fun a => propext (h a)
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  obtain rfl : F = G := funext hFG
  rfl
end GlobalTheory.FlatRed
