-- Prove2me | solution 1 for GlobalTheory.UnitLemma.stabilizer_eq_of_mem_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:54:35.863373+00:00
-- url     : https://prove2.me/submissions/6920dd8d-a541-41a6-9a06-83458e0c68b8

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableLatticeOrbitCountEqSumOrbits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]
namespace GlobalTheory.UnitLemma
theorem _root_.solution (g : A) {x y : stLat O E g} (h : y ∈ MulAction.orbit Aˣ x) :
    MulAction.stabilizer Aˣ y = MulAction.stabilizer Aˣ x := by
  obtain ⟨t, rfl⟩ := h
  ext s
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, smul_smul, mul_comm, ← smul_smul,
    smul_left_cancel_iff]
end GlobalTheory.UnitLemma
