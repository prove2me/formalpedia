-- Prove2me | solution 1 for GlobalTheory.StdAtPrime.bnd_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:11:19.726906+00:00
-- url     : https://prove2.me/submissions/6b56fce6-04a0-499f-bdae-7825f977fcc3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BndMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.StdAtPrime
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.StdAtPrime
theorem _root_.solution (p n : ℕ) (A B : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (hA : Bnd p A) (hB : Bnd p B) :
    Bnd p (A * B) := by
  obtain ⟨a, ha, hA⟩ := hA
  obtain ⟨b, hb, hB⟩ := hB
  refine ⟨a * b, Nat.Coprime.mul_left ha hb, fun i j Q => ?_⟩
  let φ : FiniteAdeleRing (𝓞 E) E →+* _ := RestrictedProduct.evalRingHom _ Q
  have hφ : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = φ x := fun _ => rfl
  rw [hφ, Matrix.mul_apply, Finset.mul_sum, map_sum]
  apply Valuation.map_sum_le
  intro k _
  have hsplit : ((a * b : ℕ) : FiniteAdeleRing (𝓞 E) E) * (A i k * B k j) =
      ((a : FiniteAdeleRing (𝓞 E) E) * A i k) * ((b : FiniteAdeleRing (𝓞 E) E) * B k j) := by
    push_cast; ring
  rw [hsplit, map_mul, Valuation.map_mul, ← hφ, ← hφ]
  exact mul_le_one' (hA i k Q) (hB k j Q)
end GlobalTheory.StdAtPrime
