-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_mul_conj_eq_one_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:52.327242+00:00
-- url     : https://prove2.me/submissions/60071680-6cd5-4e64-8eaa-f78ef327b298

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Theorems.Thm_GroundTheory_Automorphic_exists_not_mem_range
import Theorems.Thm_GroundTheory_Automorphic_conj_eq_self_iff
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
namespace GroundTheory.Automorphic
theorem _root_.solution [Algebra.IsSeparable F E] :
    ∃ l : E, l * conj F E l = 1 ∧ l ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := exists_not_mem_range (F := F) (E := E)
  have hζ0 : ζ ≠ 0 := fun h => hζ ⟨0, by rw [h, map_zero]⟩
  have hc : conj F E ζ ≠ ζ := fun h => hζ (conj_eq_self_iff.1 h)
  have hc0 : conj F E ζ ≠ 0 := by
    intro h
    apply hζ0
    rw [← conj_conj (F := F) ζ, h, map_zero]
  refine ⟨conj F E ζ * ζ⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv₀, conj_conj]
    field_simp
  · intro h
    apply hc
    field_simp at h
    exact h
end GroundTheory.Automorphic
