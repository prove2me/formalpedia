-- Prove2me | solution 1 for GlobalTheory.TorusInteg.torus_integral_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:10.123619+00:00
-- url     : https://prove2.me/submissions/2ba85522-49e0-4fc9-a52b-0254a2c44dfe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValsAtApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusInvMulPowValuationNonnegIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma
open GlobalTheory GlobalTheory.TorusInteg
namespace GlobalTheory.TorusInteg
theorem _root_.solution : ∀ (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → ∀ (r : ℕ) (e : Fin r → ι), (∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) → ∀ α : G, τ α = α → (∀ i, 0 < Multiplicative.toAdd (w i α)) → ∀ (t : T) (k : ℕ), (∀ i, 0 ≤ Multiplicative.toAdd (w i ((t : G)⁻¹ * α ^ k))) ↔ ∀ j, |Multiplicative.toAdd ((valsAt w e).comp T.subtype t) j| ≤ ((k * (Multiplicative.toAdd (w (e j) α)).toNat : ℕ) : ℤ) := by
  intro G _ τ T hT ι s w hs r e hcov α hα hpos t k
  have hτt : τ (t : G) = (t : G)⁻¹ := eq_inv_of_mul_eq_one_right ((hT _).1 t.2)
  have val1 : ∀ i, Multiplicative.toAdd (w i ((t : G)⁻¹ * α ^ k))
      = - Multiplicative.toAdd (w i t) + k * Multiplicative.toAdd (w i α) := by
    intro i
    simp [map_mul, map_inv, map_pow, toAdd_mul, toAdd_inv, toAdd_pow, nsmul_eq_mul]
  have val2 : ∀ i, Multiplicative.toAdd (w i (τ ((t : G)⁻¹ * α ^ k)))
      = Multiplicative.toAdd (w i t) + k * Multiplicative.toAdd (w i α) := by
    intro i
    rw [map_mul, map_inv, map_pow, hτt, hα, inv_inv]
    simp [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul]
  have rhs : ∀ j, ((k * (Multiplicative.toAdd (w (e j) α)).toNat : ℕ) : ℤ)
      = k * Multiplicative.toAdd (w (e j) α) := by
    intro j
    push_cast
    rw [Int.toNat_of_nonneg (hpos _).le]
  have lhs : ∀ j, Multiplicative.toAdd ((valsAt w e).comp T.subtype t) j
      = Multiplicative.toAdd (w (e j) t) := fun j => rfl
  constructor
  · intro h j
    rw [lhs, rhs, abs_le]
    have h1 := h (e j)
    have h2 := (hs (e j) _).1 (h (s (e j)))
    rw [val1] at h1
    rw [val2] at h2
    constructor <;> linarith
  · intro h i
    rcases hcov i with hi | ⟨j, rfl | rfl⟩
    · have hz : Multiplicative.toAdd (w i t) = 0 := by
        have := hs i (t : G)
        rw [hi, hτt, map_inv, toAdd_inv] at this
        rcases lt_trichotomy (Multiplicative.toAdd (w i t)) 0 with h' | h' | h'
        · exact absurd (this.2 (by linarith)) (not_le.2 h')
        · exact h'
        · exact absurd (this.1 h'.le) (not_le.2 (by linarith))
      rw [val1, hz]
      have := (hpos i).le
      positivity
    · have := h j
      rw [lhs, rhs, abs_le] at this
      rw [val1]; linarith [this.1]
    · have := h j
      rw [lhs, rhs, abs_le] at this
      apply (hs (e j) _).2
      rw [val2]; linarith [this.1]
end GlobalTheory.TorusInteg
