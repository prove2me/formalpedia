-- Prove2me | solution 1 for GroundTheory.PAdicHodge.extendToClosure_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:29.543807+00:00
-- url     : https://prove2.me/submissions/5b9ce1b5-b704-4337-bae4-60c0cad1baec

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_map_sub_of_add
import Theorems.Thm_GroundTheory_PAdicHodge_continuous_extendOnClosure
import Theorems.Thm_GroundTheory_PAdicHodge_extendOnClosure_toClosureInCp
import Theorems.Thm_GroundTheory_PAdicHodge_sub_mem_closureInCp

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
theorem _root_.solution {x x' : ℂ_[p]} (hx : x ∈ closureInCp E) (hx' : x' ∈ closureInCp E) :
    extendToClosure E R (x - x') = extendToClosure E R x - extendToClosure E R x' := by
  have hsub : ∀ s t : closureInCp E, (s : ℂ_[p]) - t ∈ closureInCp E := fun s t =>
    sub_mem_closureInCp s.2 t.2
  rw [extendToClosure_of_mem hx, extendToClosure_of_mem hx',
    extendToClosure_of_mem (hsub ⟨x, hx⟩ ⟨x', hx'⟩)]
  have he := continuous_extendOnClosure hadd hbound
  have hdiff : Continuous fun q : closureInCp E × closureInCp E =>
      (⟨(q.1 : ℂ_[p]) - q.2, hsub q.1 q.2⟩ : closureInCp E) :=
    ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  refine (denseRange_toClosureInCp E).induction_on₂ (p := fun s t : closureInCp E =>
    extendOnClosure E R ⟨(s : ℂ_[p]) - t, hsub s t⟩ = extendOnClosure E R s - extendOnClosure E R t)
    (isClosed_eq (he.comp hdiff) ((he.comp continuous_fst).sub (he.comp continuous_snd)))
    (fun y z => ?_) ⟨x, hx⟩ ⟨x', hx'⟩
  have hyz : (⟨((toClosureInCp E y : closureInCp E) : ℂ_[p]) - (toClosureInCp E z : closureInCp E),
      hsub _ _⟩ : closureInCp E) = toClosureInCp E (y - z) := by
    apply Subtype.ext
    change ((y : PadicAlgCl p) : ℂ_[p]) - ((z : PadicAlgCl p) : ℂ_[p]) =
      (((y : PadicAlgCl p) - z : PadicAlgCl p) : ℂ_[p])
    exact (UniformSpace.Completion.coe_sub _ _).symm
  rw [hyz, extendOnClosure_toClosureInCp hadd hbound, extendOnClosure_toClosureInCp hadd hbound,
    extendOnClosure_toClosureInCp hadd hbound]
  change ((R ((y : PadicAlgCl p) - z) : PadicAlgCl p) : ℂ_[p]) = _
  rw [map_sub_of_add hadd y.2 z.2, UniformSpace.Completion.coe_sub]
end GroundTheory.PAdicHodge
