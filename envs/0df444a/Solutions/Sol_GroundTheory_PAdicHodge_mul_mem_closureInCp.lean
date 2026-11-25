-- Prove2me | solution 1 for GroundTheory.PAdicHodge.mul_mem_closureInCp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:06.20892+00:00
-- url     : https://prove2.me/submissions/c42e26ca-bf77-4885-b03e-5a1d3b06b0f5

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
variable {k : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] k]
  (hkE : k ≤ E) (hmaps : ∀ y ∈ E, R y ∈ k) (hfix : ∀ a ∈ k, R a = a)
  (hmul : ∀ a ∈ k, ∀ y ∈ E, R (a * y) = a * R y)
omit hadd hbound [FiniteDimensional ℚ_[p] k]
include hkE
namespace GroundTheory.PAdicHodge
theorem _root_.solution {a : PadicAlgCl p} (ha : a ∈ k) {x : ℂ_[p]}
    (hx : x ∈ closureInCp E) : (a : ℂ_[p]) * x ∈ closureInCp E :=
  map_mem_closure (continuous_const.mul continuous_id) hx (by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨a * y, mul_mem (hkE ha) hy, UniformSpace.Completion.coe_mul a y⟩)
end GroundTheory.PAdicHodge
