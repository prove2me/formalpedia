-- Prove2me | solution 1 for GroundTheory.PAdicHodge.extendToClosure_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:27.149834+00:00
-- url     : https://prove2.me/submissions/42bb3bf2-d451-4c89-8365-bc00f2b4cad0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_continuous_extendOnClosure
import Theorems.Thm_GroundTheory_PAdicHodge_extendOnClosure_toClosureInCp

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
namespace GroundTheory.PAdicHodge
theorem _root_.solution {P : ℂ_[p] → ℂ_[p] → Prop}
    (hP : IsClosed {q : ℂ_[p] × ℂ_[p] | P q.1 q.2})
    (h : ∀ y ∈ E, P (y : ℂ_[p]) ((R y : PadicAlgCl p) : ℂ_[p])) :
    ∀ x ∈ closureInCp E, P x (extendToClosure E R x) := by
  intro x hx
  rw [extendToClosure_of_mem hx]
  have hcont : Continuous fun s : closureInCp E => ((s : ℂ_[p]), extendOnClosure E R s) :=
    continuous_subtype_val.prodMk (continuous_extendOnClosure hadd hbound)
  refine (denseRange_toClosureInCp E).induction_on (p := fun s : closureInCp E =>
    P (s : ℂ_[p]) (extendOnClosure E R s)) ⟨x, hx⟩ (hP.preimage hcont) fun y => ?_
  rw [extendOnClosure_toClosureInCp hadd hbound]
  exact h y y.2
end GroundTheory.PAdicHodge
