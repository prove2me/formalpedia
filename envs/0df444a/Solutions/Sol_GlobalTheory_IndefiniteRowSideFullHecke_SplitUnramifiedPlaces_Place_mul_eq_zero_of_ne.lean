-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place.mul_eq_zero_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:53:08.031815+00:00
-- url     : https://prove2.me/submissions/49572477-8546-41a5-8d71-9728be270cf2

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
theorem _root_.solution {w u : Place p OE} (h : w ≠ u) : w.e * u.e = 0 := by
  have hi : IsIdempotentElem (w.e * u.e) := w.idem.mul u.idem
  rcases u.primitive _ hi (by rw [mul_assoc, u.idem.eq]) with h0 | h1
  · exact h0
  rcases w.primitive _ hi (by rw [mul_right_comm, w.idem.eq]) with h0 | h2
  · exact h0
  exact absurd (Place.ext (h2.symm.trans h1)) h
end GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place
