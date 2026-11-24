-- Prove2me | solution 1 for GlobalTheory.BadShare.root_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:00:14.846615+00:00
-- url     : https://prove2.me/submissions/cb19cc39-7cae-417b-a9b2-b37ca919b4a6

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g}
open Polynomial Classical
variable (g : ℕ) [Fact g.Prime]
variable {g}
namespace GlobalTheory.BadShare
namespace _root_.GlobalTheory.BadShare
theorem _root_.solution {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) {x : AlgebraicClosure (ZMod g)}
    (hx : x ∈ f.aroots (AlgebraicClosure (ZMod g))) : x ≠ 0 := by
  rintro rfl
  rw [mem_aroots] at hx
  apply h0
  have h := hx.2
  rw [← coeff_zero_eq_aeval_zero'] at h
  exact (map_eq_zero_iff _ (algebraMap (ZMod g) (AlgebraicClosure (ZMod g))).injective).mp h
end _root_.GlobalTheory.BadShare
end GlobalTheory.BadShare
