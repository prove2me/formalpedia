-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sigma_mem_doubleCoset_permGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:17.571863+00:00
-- url     : https://prove2.me/submissions/c0f6f4cf-75cf-4f26-8050-7a9f9794c8e4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_mem_borel
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_permGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)}
    (hg : g ∈ doubleCoset (permGL F w) (borel n F : Set (GL (Fin n) F)) (borel n F)) :
    sigma g ∈ doubleCoset (permGL F (Fin.revPerm * w⁻¹ * Fin.revPerm))
      (borel n F : Set (GL (Fin n) F)) (borel n F) := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_doubleCoset.1 hg
  refine mem_doubleCoset.2 ⟨sigma b₂, sigma_mem_borel hb₂, sigma b₁, sigma_mem_borel hb₁, ?_⟩
  rw [sigma_mul, sigma_mul, sigma_permGL, ← mul_assoc]
end GroundTheory.Automorphic.Whittaker
