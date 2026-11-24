-- Prove2me | solution 1 for GlobalTheory.apply_add_intCast_of_periodic_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:23:19.509439+00:00
-- url     : https://prove2.me/submissions/85fcee5f-0712-4f9f-93f8-056ab2339893

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {g : ℕ} {β : Type*} {A : (Fin g → ℝ) → β}
    (hA : ∀ (i : Fin g) x, A (x + Pi.single i 1) = A x) (n : Fin g → ℤ) (x : Fin g → ℝ) :
    A (x + fun i => (n i : ℝ)) = A x := by
  have h1 : (fun i => (n i : ℝ)) = ∑ i, n i • (Pi.single i 1 : Fin g → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h1]
  have h2 : ∀ s : Finset (Fin g),
      Function.Periodic A (∑ i ∈ s, n i • (Pi.single i 1 : Fin g → ℝ)) := fun s => by
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (Function.Periodic.zsmul (hA a) (n a)).add_period ih
  exact h2 _ x
end GlobalTheory
