-- Prove2me | solution 1 for GroundTheory.PAdicHodge.extendToClosure_coe_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:55.812366+00:00
-- url     : https://prove2.me/submissions/f21becc6-a06d-4772-abff-151b80e9c77b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open UniformSpace Topology Filter Set
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p))
variable (R : PadicAlgCl p → PadicAlgCl p)
variable {E R}
variable {c : ℝ} (hadd : ∀ y ∈ E, ∀ z ∈ E, R (y + z) = R y + R z)
  (hbound : ∀ y ∈ E, ‖R y‖ ≤ c * ‖y‖)
include hadd
include hbound
variable {k : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] k]
  (hkE : k ≤ E) (hmaps : ∀ y ∈ E, R y ∈ k) (hfix : ∀ a ∈ k, R a = a)
  (hmul : ∀ a ∈ k, ∀ y ∈ E, R (a * y) = a * R y)
omit [FiniteDimensional ℚ_[p] k]
include hkE hfix
namespace GroundTheory.PAdicHodge
theorem _root_.solution {a : PadicAlgCl p} (ha : a ∈ k) :
    extendToClosure E R (a : ℂ_[p]) = a := by
  rw [extendToClosure_coe hadd hbound (hkE ha), hfix a ha]
end GroundTheory.PAdicHodge
