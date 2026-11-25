-- Prove2me | solution 1 for GroundTheory.PAdicHodge.extendToClosure_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:02:55.416353+00:00
-- url     : https://prove2.me/submissions/3cd98f54-8ce5-4bee-a060-0912327bb3a9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Theorems.Thm_GroundTheory_PAdicHodge_isClosed_image_coe
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_induction

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
include hmaps
namespace GroundTheory.PAdicHodge
theorem _root_.solution {x : ℂ_[p]} (hx : x ∈ closureInCp E) :
    extendToClosure E R x ∈ ((↑) : PadicAlgCl p → ℂ_[p]) '' (k : Set (PadicAlgCl p)) :=
  extendToClosure_induction hadd hbound
    (P := fun _ v => v ∈ ((↑) : PadicAlgCl p → ℂ_[p]) '' (k : Set (PadicAlgCl p)))
    ((isClosed_image_coe k).preimage continuous_snd) (fun y hy => ⟨R y, hmaps y hy, rfl⟩) x hx
end GroundTheory.PAdicHodge
