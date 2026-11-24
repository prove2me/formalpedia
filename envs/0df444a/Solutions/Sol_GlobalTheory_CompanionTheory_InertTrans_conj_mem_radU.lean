-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertTrans.conj_mem_radU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:06:34.370742+00:00
-- url     : https://prove2.me/submissions/5a0b785d-e284-4d70-8151-9f236f33ae1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SphericalTransitiveOfLevi
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_mul_inv


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertTrans
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertTrans
theorem _root_.solution {n : ℕ} {β : Fin n → ℕ} {m u : GU σ n} (hm : m ∈ leviU σ β) (hu : u ∈ radU σ β) :
    m * u * m⁻¹ ∈ radU σ β := by
  have hA : ∀ i j, β i ≠ β j → mat m i j = 0 := hm
  have hC : ∀ i j, β i ≠ β j → mat m⁻¹ i j = 0 := inv_mem hm
  have hB : ∀ i j, β j ≤ β i → mat u i j = (1 : Matrix (Fin n) (Fin n) L) i j := hu
  show ∀ i j, β j ≤ β i → mat (m * u * m⁻¹) i j = (1 : Matrix (Fin n) (Fin n) L) i j
  intro i j h
  have e : (mat m * mat u * mat m⁻¹) i j = (mat m * mat m⁻¹) i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : β p = β j
    · congr 1
      rw [Matrix.mul_apply]
      calc _ = ∑ l, mat m i l * (1 : Matrix (Fin n) (Fin n) L) l p := Finset.sum_congr rfl fun l _ => by
              by_cases hl : β i = β l
              · rw [hB l p (by omega)]
              · rw [hA i l hl, zero_mul, zero_mul]
        _ = _ := by rw [← Matrix.mul_apply, Matrix.mul_one]
    · rw [hC p j hp, mul_zero, mul_zero]
  rw [mat_mul, mat_mul, e, mat_mul_inv]
end GlobalTheory.CompanionTheory.InertTrans
