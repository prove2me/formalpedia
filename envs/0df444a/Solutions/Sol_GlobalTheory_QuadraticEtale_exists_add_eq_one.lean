-- Prove2me | solution 1 for GlobalTheory.QuadraticEtale.exists_add_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:20.754822+00:00
-- url     : https://prove2.me/submissions/eca02ecf-5902-4731-8f71-c91abcf8040f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsUnitFormSelfOfNotMem

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
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →+* S)
variable [IsLocalRing R]
omit [IsLocalRing R] [Algebra R S] [CommRing R]
namespace GlobalTheory.QuadraticEtale
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hgal : ∃ ω, IsUnit (ω - σ ω)) :
    ∃ t, t + σ t = 1 := by
  obtain ⟨ω, hω⟩ := hgal
  obtain ⟨v, hv⟩ := hω.exists_right_inv
  have h2 := congrArg σ hv
  rw [map_mul, map_sub, hσ, map_one] at h2
  refine ⟨ω * v, ?_⟩
  rw [map_mul]
  have : σ v = -v := by linear_combination (-σ v) * hv - v * h2
  rw [this]
  linear_combination hv
end GlobalTheory.QuadraticEtale
