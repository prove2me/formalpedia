-- Prove2me | solution 1 for GlobalTheory.QuadraticEtale.mem_range_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:06:30.783276+00:00
-- url     : https://prove2.me/submissions/cdb55492-9748-4f5b-9be2-2b28e76907cc

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
theorem _root_.solution (hrank : finrank R S = 2) (σ : S ≃ₐ[R] S) (hσ : σ ≠ 1) (x : S)
    (hx : σ x = x) : x ∈ (algebraMap R S).range := by
  obtain ⟨t, ht⟩ := exists_add_eq_one (σ : S →+* S) (apply_apply hrank σ hσ)
    (exists_isUnit_sub hrank σ hσ)
  refine ⟨Algebra.trace R S (t * x), ?_⟩
  rw [← add_apply_eq_trace hrank σ hσ, map_mul, hx]
  simp only [RingHom.coe_coe] at ht
  linear_combination x * ht
end GlobalTheory.QuadraticEtale
