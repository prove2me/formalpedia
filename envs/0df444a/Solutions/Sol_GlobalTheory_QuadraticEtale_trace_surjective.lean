-- Prove2me | solution 1 for GlobalTheory.QuadraticEtale.trace_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:45:05.995911+00:00
-- url     : https://prove2.me/submissions/e647ef34-a602-4084-a1ea-95052f33599b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsUnitFormSelfOfNotMem
import Theorems.Thm_GlobalTheory_QuadraticEtale_exists_add_eq_one
import Theorems.Thm_GlobalTheory_QuadraticEtale_apply_apply
import Theorems.Thm_GlobalTheory_QuadraticEtale_exists_isUnit_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.QuadraticEtale
open Module
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
  [Module.Free R S] [Algebra.FormallyUnramified R S]
namespace GlobalTheory.QuadraticEtale
theorem _root_.solution (hrank : finrank R S = 2) :
    Function.Surjective (Algebra.trace R S) := by
  haveI : Nontrivial S := Module.nontrivial_of_finrank_pos (R := R) (by omega)
  obtain ⟨σ, hσ, -⟩ := existsUnique_ne_one hrank
  obtain ⟨t, ht⟩ := exists_add_eq_one (σ : S →+* S) (apply_apply hrank σ hσ)
    (exists_isUnit_sub hrank σ hσ)
  have h1 : Algebra.trace R S t = 1 := by
    apply FaithfulSMul.algebraMap_injective R S
    rw [← add_apply_eq_trace hrank σ hσ, map_one]
    exact ht
  intro r
  exact ⟨r • t, by rw [map_smul, h1, smul_eq_mul, mul_one]⟩
end GlobalTheory.QuadraticEtale
