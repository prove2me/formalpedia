-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place.conj_induces_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:53:04.272482+00:00
-- url     : https://prove2.me/submissions/6b068f3a-e4ef-4b43-be6c-204c01719965

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place
variable {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE]
namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place
theorem _root_.solution [StarRing OE] (w : Place p OE) {O : Type} [CommRing O]
    [Algebra ℤ_[p] O] (σ : OE →+* O) :
    w.conj.Induces σ ↔ w.Induces (σ.comp (starRingEnd OE)) := by
  have : ∀ x : Op p OE, extend σ (bar p OE x) = extend (σ.comp (starRingEnd OE)) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z a => rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  unfold Induces
  rw [← this]; rfl
end GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place
