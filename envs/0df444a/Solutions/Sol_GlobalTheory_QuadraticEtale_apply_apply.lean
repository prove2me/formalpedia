-- Prove2me | solution 1 for GlobalTheory.QuadraticEtale.apply_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:38.530937+00:00
-- url     : https://prove2.me/submissions/17b27799-a4b9-4eeb-b390-f92986486abc

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
open Module
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
  [Module.Free R S] [Algebra.FormallyUnramified R S]
namespace GlobalTheory.QuadraticEtale
theorem _root_.solution (hrank : finrank R S = 2) (σ : S ≃ₐ[R] S) (hσ : σ ≠ 1) (x : S) :
    σ (σ x) = x := by
  have h := add_apply_eq_trace hrank σ hσ x
  have h2 := congrArg σ h
  rw [map_add, AlgEquiv.commutes] at h2
  linear_combination h2 - h
end GlobalTheory.QuadraticEtale
