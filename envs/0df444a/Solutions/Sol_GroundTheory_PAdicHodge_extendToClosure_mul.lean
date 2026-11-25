-- Prove2me | solution 1 for GroundTheory.PAdicHodge.extendToClosure_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:27.892086+00:00
-- url     : https://prove2.me/submissions/48e5f1b6-e68b-49f1-8cc2-a7855ca14a55

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_continuous_extendOnClosure
import Theorems.Thm_GroundTheory_PAdicHodge_extendOnClosure_toClosureInCp
import Theorems.Thm_GroundTheory_PAdicHodge_mul_mem_closureInCp

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
include hkE hmul
namespace GroundTheory.PAdicHodge
theorem _root_.solution {a : PadicAlgCl p} (ha : a ∈ k) {x : ℂ_[p]}
    (hx : x ∈ closureInCp E) :
    extendToClosure E R ((a : ℂ_[p]) * x) = (a : ℂ_[p]) * extendToClosure E R x := by
  have hmem := fun s : closureInCp E => mul_mem_closureInCp hkE ha s.2
  rw [extendToClosure_of_mem hx, extendToClosure_of_mem (hmem ⟨x, hx⟩)]
  have he := continuous_extendOnClosure hadd hbound
  have hcont : Continuous fun s : closureInCp E =>
      (⟨(a : ℂ_[p]) * s, hmem s⟩ : closureInCp E) :=
    (continuous_const.mul continuous_subtype_val).subtype_mk _
  refine (denseRange_toClosureInCp E).induction_on (p := fun s : closureInCp E =>
    extendOnClosure E R ⟨(a : ℂ_[p]) * s, hmem s⟩ = (a : ℂ_[p]) * extendOnClosure E R s)
    ⟨x, hx⟩ (isClosed_eq (he.comp hcont) (continuous_const.mul he)) fun y => ?_
  have : (⟨(a : ℂ_[p]) * (toClosureInCp E y : closureInCp E), hmem _⟩ : closureInCp E) =
      toClosureInCp E ⟨a * y, mul_mem (hkE ha) y.2⟩ := by
    apply Subtype.ext
    exact (UniformSpace.Completion.coe_mul a (y : PadicAlgCl p)).symm
  rw [this, extendOnClosure_toClosureInCp hadd hbound, extendOnClosure_toClosureInCp hadd hbound]
  change ((R (a * y) : PadicAlgCl p) : ℂ_[p]) = _
  rw [hmul a ha y y.2, UniformSpace.Completion.coe_mul]
end GroundTheory.PAdicHodge
