-- Prove2me | solution 1 for GlobalTheory.dWedge_mul_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:07:25.457049+00:00
-- url     : https://prove2.me/submissions/834d09f6-c824-4aac-8440-346fbec72b4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Theorems.Thm_GlobalTheory_form_d_mul_sub_mem

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
variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {D : ℕ}
open KaehlerDifferential
namespace GlobalTheory
theorem _root_.solution (I : Ideal A) (h : A) (g : Fin D → A) (hg : ∀ k, g k ∈ I) :
    dWedge R (fun k => h * g k) - h ^ D • dWedge R g ∈ I • (⊤ : Submodule A (⋀[A]^D Ω[A⁄R])) :=
  form_d_mul_sub_mem _ _ I h g hg
end GlobalTheory
