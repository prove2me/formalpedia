-- Prove2me | solution 1 for KellyStochasticNetworks.CountableReversal.jump_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:52:25.407959+00:00
-- url     : https://prove2.me/submissions/af32cffd-651d-482b-87a0-364bfb50c8cb

import Mathlib

theorem solution {S : Type*} [Countable S] [Nonempty S]
    (q : S → S → ℝ) (π : S → ℝ)
    (hq : ∀ j k, 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hqsum : ∀ j, Summable (q j)) (hqpos : ∀ j, 0 < ∑' k, q j k)
    (hirr : ∀ j k, Relation.ReflTransGen (fun a b => 0 < q a b) j k)
    (hπpos : ∀ j, 0 < π j) (hπsum : HasSum π 1)
    (hbalance : ∀ j, HasSum (fun k => π k * q k j) (π j * ∑' k, q j k))
    (hG : Summable (fun j => π j * ∑' k, q j k)) :
    let G := ∑' j, π j * ∑' k, q j k
    let πJ := fun j => G⁻¹ * π j * (∑' k, q j k)
    let p := fun j k => q j k / (∑' l, q j l)
    0 < G ∧ (∀ j, 0 < πJ j) ∧ HasSum πJ 1 ∧
      (∀ j k, 0 ≤ p j k) ∧ (∀ j, HasSum (p j) 1) ∧
      (∀ j, HasSum (fun k => πJ k * p k j) (πJ j)) := by
  intro G πJ p
  have hpos : ∀ j, 0 < π j * ∑' k, q j k := fun j => mul_pos (hπpos j) (hqpos j)
  have hGpos : 0 < G := by
    obtain ⟨j0⟩ := (inferInstance : Nonempty S)
    exact hG.tsum_pos (fun j => (hpos j).le) j0 (hpos j0)
  refine ⟨hGpos, fun j => ?_, ?_, fun j k => ?_, fun j => ?_, fun j => ?_⟩
  · exact mul_pos (mul_pos (inv_pos.mpr hGpos) (hπpos j)) (hqpos j)
  · have := hG.hasSum.mul_left G⁻¹
    rw [inv_mul_cancel₀ hGpos.ne'] at this
    refine this.congr_fun fun j => ?_
    simp only [πJ]; ring
  · exact div_nonneg (hq j k) (hqpos j).le
  · have := (hqsum j).hasSum.div_const (∑' l, q j l)
    rwa [div_self (hqpos j).ne'] at this
  · have h1 := (hbalance j).mul_left G⁻¹
    have h2 : (fun k => πJ k * p k j) = fun k => G⁻¹ * (π k * q k j) := by
      funext k; simp only [πJ, p]; field_simp [(hqpos k).ne']
    have h3 : πJ j = G⁻¹ * (π j * ∑' k, q j k) := by simp only [πJ]; ring
    rw [h2, h3]; exact h1
