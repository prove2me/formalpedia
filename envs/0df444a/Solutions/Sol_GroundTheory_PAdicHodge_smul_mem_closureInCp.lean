-- Prove2me | solution 1 for GroundTheory.PAdicHodge.smul_mem_closureInCp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:47.707003+00:00
-- url     : https://prove2.me/submissions/2c3e59f3-7705-4741-a28a-cca9d1cf0684

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure

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
omit hadd hbound
namespace GroundTheory.PAdicHodge
theorem _root_.solution (σ : Gal(PadicAlgCl p/K₀)) (hσ : ∀ y ∈ E, σ y ∈ E) {x : ℂ_[p]}
    (hx : x ∈ closureInCp E) : σ • x ∈ closureInCp E :=
  map_mem_closure (continuous_const_smul σ) hx (by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨σ y, hσ y hy, (gal_smul_coe σ y).symm⟩)
end GroundTheory.PAdicHodge
