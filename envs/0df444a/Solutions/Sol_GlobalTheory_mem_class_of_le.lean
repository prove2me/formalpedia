-- Prove2me | solution 1 for GlobalTheory.mem_class_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:20:05.106304+00:00
-- url     : https://prove2.me/submissions/d77fcff8-fcd8-4038-a70d-3b022115a45b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Type} [AddCommGroup X] {n : ℕ} {α : ℕ → X}
    (hα : ∀ j, ∃ μ, α (j + 1) = α j + n ^ j • μ) {z : X} {j k : ℕ} (hjk : j ≤ k)
    (hz : ∃ μ, z = α k + n ^ k • μ) : ∃ μ, z = α j + n ^ j • μ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction d generalizing z with
  | zero => simpa using hz
  | succ d ih =>
    obtain ⟨μ, rfl⟩ := hz
    obtain ⟨ν, hν⟩ := hα (j + d)
    apply ih
    refine ⟨ν + n • μ, ?_⟩
    rw [← add_assoc, hν, pow_succ, mul_smul, smul_add]
    abel
end GlobalTheory
