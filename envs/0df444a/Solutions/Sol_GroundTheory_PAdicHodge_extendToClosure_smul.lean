-- Prove2me | solution 1 for GroundTheory.PAdicHodge.extendToClosure_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:28.922321+00:00
-- url     : https://prove2.me/submissions/0ae6d80d-aebf-4fc4-b4ca-90d6d1bb46c1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_continuous_extendOnClosure
import Theorems.Thm_GroundTheory_PAdicHodge_extendOnClosure_toClosureInCp
import Theorems.Thm_GroundTheory_PAdicHodge_smul_mem_closureInCp

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
variable {K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (σ : Gal(PadicAlgCl p/K₀)) (hσ : ∀ y ∈ E, σ y ∈ E)
    (hσR : ∀ y ∈ E, R (σ y) = σ (R y)) {x : ℂ_[p]} (hx : x ∈ closureInCp E) :
    extendToClosure E R (σ • x) = σ • extendToClosure E R x := by
  have hmem := fun s : closureInCp E => smul_mem_closureInCp σ hσ s.2
  rw [extendToClosure_of_mem hx, extendToClosure_of_mem (hmem ⟨x, hx⟩)]
  have he := continuous_extendOnClosure hadd hbound
  have hcont : Continuous fun s : closureInCp E => (⟨σ • (s : ℂ_[p]), hmem s⟩ : closureInCp E) :=
    ((continuous_const_smul σ).comp continuous_subtype_val).subtype_mk _
  refine (denseRange_toClosureInCp E).induction_on (p := fun s : closureInCp E =>
    extendOnClosure E R ⟨σ • (s : ℂ_[p]), hmem s⟩ = σ • extendOnClosure E R s)
    ⟨x, hx⟩ (isClosed_eq (he.comp hcont) ((continuous_const_smul σ).comp he)) fun y => ?_
  have : (⟨σ • ((toClosureInCp E y : closureInCp E) : ℂ_[p]), hmem _⟩ : closureInCp E) =
      toClosureInCp E ⟨σ y, hσ y y.2⟩ := by
    apply Subtype.ext
    exact gal_smul_coe σ (y : PadicAlgCl p)
  rw [this, extendOnClosure_toClosureInCp hadd hbound, extendOnClosure_toClosureInCp hadd hbound]
  change ((R (σ y) : PadicAlgCl p) : ℂ_[p]) = _
  rw [hσR y y.2, gal_smul_coe]
end GroundTheory.PAdicHodge
