-- Prove2me | solution 1 for GlobalTheory.Pat.Example.exists_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:40.963601+00:00
-- url     : https://prove2.me/submissions/2bd0eab9-f2c7-4c76-81af-0e45c78628a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
noncomputable section
open IsLocalRing
noncomputable section
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.Pat GlobalTheory.Pat.Example
namespace GlobalTheory.Pat.Example
theorem _root_.solution : ∃ (Φ : Frame) (G : PolGp Φ), Φ.n = 2 ∧ Nonempty Φ.Vl ∧ Nonempty Φ.St ∧
    Nat.card G.Γ = 6 ∧ Nonempty (Pair G) :=
  ⟨frame, pol, rfl, ⟨()⟩, ⟨()⟩, DihedralGroup.nat_card (n := 3), ⟨pair⟩⟩
end GlobalTheory.Pat.Example
