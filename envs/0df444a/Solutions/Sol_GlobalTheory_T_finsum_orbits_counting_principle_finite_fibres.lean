-- Prove2me | solution 1 for GlobalTheory.T.finsum_orbits_counting_principle_finite_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:22:38.90937+00:00
-- url     : https://prove2.me/submissions/eafac3bb-d756-4640-ad51-e3d28b831cd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinsumOrbitsCountingPrincipleFiniteFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinsumOrbitsCountingPrincipleFiniteFibresStatement
import Theorems.Thm_GlobalTheory_OrbitCounting_counting_principle


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G X Y : Type) [CommGroup G] [MulAction G X] [MulAction G Y] (Gc : Subgroup G) (π : X → Y), (∀ (g : G) (x : X), π (g • x) = g • π x) → (∀ y, (π ⁻¹' {y}).Finite) → (∀ y : Y, MulAction.stabilizer G y ≤ Gc ∧ (MulAction.stabilizer G y).relIndex Gc ≠ 0) → Finite (MulAction.orbitRel.Quotient G Y) → ∀ w : Y → ℚ, (∀ (g : G) (y : Y), w (g • y) = w y) → ∑ᶠ o : MulAction.orbitRel.Quotient G X, w (π (Quotient.out o)) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) = ∑ᶠ o : MulAction.orbitRel.Quotient G Y, w (Quotient.out o) * ((π ⁻¹' {(Quotient.out o)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) := by
  first | exact @GlobalTheory.OrbitCounting.counting_principle | exact GlobalTheory.OrbitCounting.counting_principle | (intros; apply GlobalTheory.OrbitCounting.counting_principle <;> assumption)
end _root_.GlobalTheory.T
