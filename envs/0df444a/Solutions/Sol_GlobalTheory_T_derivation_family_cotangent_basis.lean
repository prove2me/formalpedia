-- Prove2me | solution 1 for GlobalTheory.T.derivation_family_cotangent_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:15:36.103934+00:00
-- url     : https://prove2.me/submissions/7a3b31b2-c0af-4f9a-aadc-27724e6e85bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivationFamilyCotangentBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivationFamilyCotangentBasisStatement
import Theorems.Thm_GlobalTheory_CoordsAlg_coords_of_derivation_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra R A] (e : A →+* R), (∀ r, e (algebraMap R A r) = r) → Module.Free R (RingHom.ker e).Cotangent → Module.Finite R (RingHom.ker e).Cotangent → ∀ (n : ℕ) (dv : Fin n → A → R), (∀ a x y, dv a (x + y) = dv a x + dv a y) → (∀ a x y, dv a (x * y) = e x * dv a y + e y * dv a x) → (∀ a r, dv a (algebraMap R A r) = 0) → (∀ D : A → R, (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = e x * D y + e y * D x) → (∀ r, D (algebraMap R A r) = 0) → ∃! c : Fin n → R, ∀ x, D x = ∑ a, c a * dv a x) → ∃ z : Fin n → A, (∀ i, e (z i) = 0) ∧ (∀ a i, dv a (z i) = if a = i then 1 else 0) ∧ maximalIdeal A = (maximalIdeal R).map (algebraMap R A) ⊔ Ideal.span (Set.range z) := by
  first | exact @GlobalTheory.CoordsAlg.coords_of_derivation_basis | exact GlobalTheory.CoordsAlg.coords_of_derivation_basis | (intros; apply GlobalTheory.CoordsAlg.coords_of_derivation_basis <;> assumption)
end _root_.GlobalTheory.T
