-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BlockIwahoriUML.up_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:21:40.81943+00:00
-- url     : https://prove2.me/submissions/0f3cc60f-7092-427c-af53-2f718f4fcd7f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriBlockUpperLeviLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BlockIwahoriUML
variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]
namespace GlobalTheory.CompanionTheory.BlockIwahoriUML
theorem _root_.solution (v : Valuation k Γ) {r : Γ} (hr : r < 1) {n : ℕ} (β : Fin n → ℕ)
    (hβ : Monotone β) (u : Matrix (Fin n) (Fin n) k) (hu : Cong v r u)
    (hu0 : ∀ i j, j < i → u i j = 0) (hu1 : ∀ i, u i i = 1) :
    ∃ a m : Matrix (Fin n) (Fin n) k, a.det = 1 ∧ m.det = 1 ∧ Cong v r a ∧ Cong v r m ∧
      (∀ i j, β j ≤ β i → a i j = (1 : Matrix (Fin n) (Fin n) k) i j) ∧
      (∀ i j, β i ≠ β j → m i j = 0) ∧ u = a * m := by
  classical
  let m : Matrix (Fin n) (Fin n) k := fun i j => if β i = β j then u i j else 0
  have hmb : ∀ i j, β i ≠ β j → m i j = 0 := fun i j h => if_neg h
  have hmu : ∀ i j, β i = β j → m i j = u i j := fun i j h => if_pos h
  have hm0 : ∀ i j, j < i → m i j = 0 := by
    intro i j h
    by_cases hb : β i = β j
    · rw [hmu i j hb, hu0 i j h]
    · exact hmb i j hb
  have hm1 : ∀ i, m i i = 1 := fun i => by rw [hmu i i rfl, hu1]
  have hdet : ∀ A : Matrix (Fin n) (Fin n) k, (∀ i j, j < i → A i j = 0) → (∀ i, A i i = 1) →
      A.det = 1 := by
    intro A h0 h1
    rw [Matrix.det_of_upperTriangular (fun i j h => h0 i j h)]
    simp [h1]
  have hmd : m.det = 1 := hdet m hm0 hm1
  have hud : u.det = 1 := hdet u hu0 hu1
  have hmC : Cong v r m := by
    intro i j
    by_cases hb : β i = β j
    · rw [hmu i j hb]
      exact hu i j
    · have hij : i ≠ j := fun e => hb (by rw [e])
      rw [hmb i j hb, Matrix.one_apply_ne hij]
      simp
  have hmU : IsUnit m.det := by simp [hmd]
  have huU : IsUnit u.det := by simp [hud]
  haveI : Invertible m := Matrix.invertibleOfIsUnitDet m hmU
  have hmw : m * m⁻¹ = 1 := Matrix.mul_nonsing_inv m hmU
  have hwm : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m hmU
  have hbu : BlockTriangular u β := by
    intro i j h
    refine hu0 i j ?_
    by_contra hc
    exact absurd (hβ (not_lt.1 hc)) (not_le.2 h)
  have hbm : BlockTriangular m β := fun i j h => hmb i j h.ne'
  have hbw : BlockTriangular m⁻¹ β := Matrix.blockTriangular_inv_of_blockTriangular hbm
  have hK : Cong v r (u * m⁻¹) := by
    let ug : GL (Fin n) k := Matrix.nonsingInvUnit u huU
    let mg : GL (Fin n) k := Matrix.nonsingInvUnit m hmU
    have hugK : ug ∈ PrincipalCongruence.principalCongruence v r hr := hu
    have hmgK : mg ∈ PrincipalCongruence.principalCongruence v r hr := hmC
    have hag := mul_mem hugK (inv_mem hmgK)
    have hcoe : ((ug * mg⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = u * m⁻¹ := by
      rw [Units.val_mul, Matrix.coe_units_inv]
      rfl
    intro i j
    have := hag i j
    rwa [hcoe] at this
  refine ⟨u * m⁻¹, m, ?_, hmd, hK, hmC, ?_, hmb, ?_⟩
  · rw [Matrix.det_mul, hud, Matrix.det_nonsing_inv, hmd]
    simp
  · intro i j hij
    rcases hij.lt_or_eq with h | h
    · have hne : i ≠ j := fun e => h.ne (by rw [e])
      rw [Matrix.one_apply_ne hne]
      exact (hbu.mul hbw) h
    · have key : (u * m⁻¹) i j = (m * m⁻¹) i j := by
        simp only [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        rcases lt_trichotomy (β x) (β i) with hx | hx | hx
        · rw [hbu hx, hbm hx]
        · rw [hmu i x hx.symm]
        · have : m⁻¹ x j = 0 := hbw (by rw [h]; exact hx)
          rw [this, mul_zero, mul_zero]
      rw [key, hmw]
  · rw [Matrix.mul_assoc, hwm, Matrix.mul_one]
end GlobalTheory.CompanionTheory.BlockIwahoriUML
