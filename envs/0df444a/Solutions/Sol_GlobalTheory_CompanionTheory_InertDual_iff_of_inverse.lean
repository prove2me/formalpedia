-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertDual.iff_of_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:42:37.027807+00:00
-- url     : https://prove2.me/submissions/716476f1-7b4f-45c2-9ba1-54cdf27c480f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DualPairingExists
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDual_int_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDual
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertDual
theorem _root_.solution {D E Q R Dg : Matrix (Fin N) (Fin N) L} (hED : E * D = 1) (hQ : IsInt (Q * E))
    (hR : IsInt (R * E)) (hDg : IsInt Dg) (hD : IsInt D) (e : D = Dg * R + D * Q) (B : Fin N → L) :
    (∀ i, (D *ᵥ B) i ∈ intL L) ↔ (∀ i, (Q *ᵥ B) i ∈ intL L) ∧ ∀ i, (R *ᵥ B) i ∈ intL L := by
  constructor
  · intro h
    have key : ∀ P : Matrix (Fin N) (Fin N) L, IsInt (P * E) → ∀ i, (P *ᵥ B) i ∈ intL L := by
      intro P hP i
      have hPB : P *ᵥ B = (P * E) *ᵥ (D *ᵥ B) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hED, Matrix.mul_one]
      rw [hPB]
      exact int_mulVec hP h i
    exact ⟨key Q hQ, key R hR⟩
  · rintro ⟨hq, hr⟩ i
    have hDB : D *ᵥ B = Dg *ᵥ (R *ᵥ B) + D *ᵥ (Q *ᵥ B) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← e]
    rw [hDB, Pi.add_apply]
    exact add_mem (int_mulVec hDg hr i) (int_mulVec hD hq i)
end GlobalTheory.CompanionTheory.InertDual
