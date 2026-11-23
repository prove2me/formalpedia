-- Prove2me | solution 1 for GlobalTheory.range_fst_residue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:04.052801+00:00
-- url     : https://prove2.me/submissions/3791d90d-e916-4c3c-91ac-eb9e6405dc95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {B : Type u} [CommRing B] [IsLocalRing B] (g : X ⟶ Spec (.of B)) :
    Set.range (pullback.fst g (Spec.map (CommRingCat.ofHom (residue B)))) =
      g ⁻¹' {closedPoint B} := by
  rw [Scheme.Pullback.range_fst]
  congr 1
  have key : ∀ z : Spec (.of (ResidueField B)),
      (Spec.map (CommRingCat.ofHom (residue B))).base z = closedPoint B := by
    intro z
    apply PrimeSpectrum.ext
    show Ideal.comap (residue B) z.asIdeal = maximalIdeal B
    haveI := z.isPrime
    rw [Ideal.eq_bot_of_prime z.asIdeal, ← RingHom.ker_eq_comap_bot, ker_residue]
  ext y
  constructor
  · rintro ⟨z, rfl⟩; exact key z
  · rintro rfl; exact ⟨⟨⊥, Ideal.isPrime_bot⟩, key _⟩
end _root_.GlobalTheory
end GlobalTheory
