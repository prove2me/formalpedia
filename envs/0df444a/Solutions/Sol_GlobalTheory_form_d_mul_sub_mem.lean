-- Prove2me | solution 1 for GlobalTheory.form_d_mul_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:57:35.586436+00:00
-- url     : https://prove2.me/submissions/01b23a31-290b-4ab3-aa06-abe66d8726b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Theorems.Thm_GlobalTheory_alternating_sub_mem_smul_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [AddCommGroup N] [Module A N] {D : ℕ}
variable (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)
namespace GlobalTheory
theorem _root_.solution (I : Ideal A) (h : A) (g : Fin D → A) (hg : ∀ k, g k ∈ I) :
    ω (fun k => d (h * g k)) - h ^ D • ω (fun k => d (g k)) ∈ I • (⊤ : Submodule A N) := by
  have : h ^ D • ω (fun k => d (g k)) = ω (fun k => h • d (g k)) := by
    rw [ω.map_smul_univ (fun _ => h)]
    simp
  rw [this]
  refine alternating_sub_mem_smul_top ω I _ _ fun k => ?_
  rw [Derivation.leibniz, add_sub_cancel_left]
  exact Submodule.smul_mem_smul (hg k) Submodule.mem_top
end GlobalTheory
