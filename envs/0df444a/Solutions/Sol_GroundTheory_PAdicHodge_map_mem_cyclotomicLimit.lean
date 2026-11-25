-- Prove2me | solution 1 for GroundTheory.PAdicHodge.map_mem_cyclotomicLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:29.481194+00:00
-- url     : https://prove2.me/submissions/076e16a0-d79f-4082-a66c-af8cc050a510

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_mem_cyclotomicLimit
import Theorems.Thm_GroundTheory_PAdicHodge_map_mem_cyclotomicLayer

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
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]
omit [FiniteDimensional ℚ_[p] K]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x ∈ K, σ x = x) {x : PadicAlgCl p} (hx : x ∈ cyclotomicLimit K) :
    σ x ∈ cyclotomicLimit K := by
  obtain ⟨n, hn⟩ := (mem_cyclotomicLimit K).1 hx
  exact (mem_cyclotomicLimit K).2 ⟨n, map_mem_cyclotomicLayer K σ hσ hn⟩
end GroundTheory.PAdicHodge
