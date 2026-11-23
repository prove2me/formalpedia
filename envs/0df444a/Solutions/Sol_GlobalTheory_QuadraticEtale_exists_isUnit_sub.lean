-- Prove2me | solution 1 for GlobalTheory.QuadraticEtale.exists_isUnit_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:38.747808+00:00
-- url     : https://prove2.me/submissions/0adc7263-84e8-4a3b-9a31-204ec38e0e09

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
theorem _root_.solution (hrank : finrank R S = 2) (σ : S ≃ₐ[R] S) (hσ : σ ≠ 1) :
    ∃ ω, IsUnit (ω - σ ω) := by
  obtain ⟨B, hB⟩ := exists_basis_one hrank
  have hab := eq_coord B hB (B 1 * B 1)
  refine ⟨B 1, ?_⟩
  rw [apply_eq_of_ne_one B hB hab σ hσ]
  convert isUnit_different B hB hab using 1
  ring
end GlobalTheory.QuadraticEtale
