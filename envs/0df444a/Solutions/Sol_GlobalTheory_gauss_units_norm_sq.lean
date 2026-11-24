-- Prove2me | solution 1 for GlobalTheory.gauss_units_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:59:05.589692+00:00
-- url     : https://prove2.me/submissions/d73f6e22-7644-44dd-aab4-c92493e1bf16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussUnitsNormSq
import Theorems.Thm_GlobalTheory_GaussUnits_sum_ideal_of_exists
import Theorems.Thm_GlobalTheory_GaussUnits_sum_ideal_of_forall
import Theorems.Thm_GlobalTheory_GaussUnits_sum_units_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ComplexConjugate Finset
open GlobalTheory
open GaussUnits
namespace GlobalTheory
theorem _root_.solution : ∀ {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [Fintype Rˣ]
    (m : Ideal R), (∀ x : R, IsUnit x ↔ x ∉ m) → ∀ (ψ : AddChar R ℂ),
    (∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) → ∀ (χ : Rˣ → ℂ), (∀ u v, χ (u * v) = χ u * χ v) →
    (∀ u, ‖χ u‖ = 1) → ∀ (t₀ : Rˣ), (∀ x ∈ m, ((t₀ : R) - 1) * x = 0) → χ t₀ ≠ 1 →
    ‖∑ u : Rˣ, (χ u)⁻¹ * ψ u‖ ^ 2 = Fintype.card R := by
  intro R _ _ _ _ m hm ψ hψ χ hχ hχn t₀ ht₀ hχt₀
  classical
  have hχ0 : ∀ u, χ u ≠ 0 := fun u h => by simpa [h] using hχn u
  have hχ1 : χ 1 = 1 := by
    have h := hχ 1 1
    rw [mul_one] at h
    have h2 : χ 1 * (χ 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (hχ0 1)
    · exact sub_eq_zero.mp h3
  have hconj : conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u) = ∑ z : Rˣ, χ z * ψ (-(z : R)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [map_mul, Complex.inv_eq_conj (hχn z), Complex.conj_conj, AddChar.map_neg_eq_conj]
  have hexp : (∑ u : Rˣ, (χ u)⁻¹ * ψ u) * conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u)
      = ∑ t : Rˣ, (χ t)⁻¹ * ∑ z : Rˣ, ψ (((t : R) - 1) * z) := by
    rw [hconj, Finset.sum_mul_sum, Finset.sum_comm]
    have hz : ∀ z : Rˣ, ∑ y : Rˣ, (χ y)⁻¹ * ψ y * (χ z * ψ (-(z : R)))
        = ∑ t : Rˣ, (χ t)⁻¹ * ψ (((t : R) - 1) * z) := by
      intro z
      refine Fintype.sum_equiv (Equiv.mulRight z⁻¹) _ _ (fun y => ?_)
      have hzinv : χ z⁻¹ = (χ z)⁻¹ := by
        have h := hχ z z⁻¹
        rw [mul_inv_cancel, hχ1] at h
        exact eq_inv_of_mul_eq_one_right h.symm
      have harg : (((y * z⁻¹ : Rˣ) : R) - 1) * (z : R) = (y : R) + -(z : R) := by
        rw [sub_mul, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          mul_one, one_mul, sub_eq_add_neg]
      simp only [Equiv.coe_mulRight]
      rw [harg, AddChar.map_add_eq_mul, hχ, hzinv, mul_inv, inv_inv]
      ring
    rw [Finset.sum_congr rfl (fun z _ => hz z), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
  have hinner : ∀ t : Rˣ, ∑ z : Rˣ, ψ (((t : R) - 1) * z) =
      (if t = 1 then (Fintype.card R : ℂ) else 0) -
      (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then ((univ.filter (· ∈ m)).card : ℂ) else 0) := by
    intro t
    rw [sum_units_eq m hm (fun x => ψ (((t : R) - 1) * x))]
    congr 1
    · have htop : ∑ x, ψ (((t : R) - 1) * x)
          = ∑ x, (if x ∈ (⊤ : Ideal R) then ψ (((t : R) - 1) * x) else 0) := by simp
      rw [htop]
      split_ifs with h
      · subst h
        rw [sum_ideal_of_forall ⊤ ψ _ (by simp)]
        simp
      · apply sum_ideal_of_exists ⊤ ψ hψ
        refine ⟨1, Submodule.mem_top, ?_⟩
        rw [mul_one, sub_ne_zero]
        exact fun h' => h (Units.val_eq_one.mp h')
    · split_ifs with h
      · exact sum_ideal_of_forall m ψ _ h
      · push_neg at h
        exact sum_ideal_of_exists m ψ hψ _ h
  have hcond : ∀ t : Rˣ, (∀ x ∈ m, (((t₀ * t : Rˣ) : R) - 1) * x = 0) ↔
      (∀ x ∈ m, ((t : R) - 1) * x = 0) := by
    intro t
    constructor
    · intro h x hx
      have h1 := h x hx
      have h2 := ht₀ x hx
      rw [Units.val_mul] at h1
      have h3 : (t₀ : R) * (((t : R) - 1) * x) = 0 := by linear_combination h1 - h2
      exact t₀.isUnit.mul_right_eq_zero.mp h3
    · intro h x hx
      have h1 := h x hx
      have h2 := ht₀ x hx
      rw [Units.val_mul]
      linear_combination (t₀ : R) * h1 + h2
  have hS : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) = 0 := by
    have e := Fintype.sum_equiv (Equiv.mulLeft t₀)
      (fun t => if (∀ x ∈ m, (((t₀ * t : Rˣ) : R) - 1) * x = 0) then (χ (t₀ * t))⁻¹ else 0)
      (fun t => if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) (fun _ => rfl)
    have hS' : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0)
        = (χ t₀)⁻¹ * ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) := by
      conv_lhs => rw [← e]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only [hcond t, hχ, mul_inv, mul_ite, mul_zero]
    have hne : (χ t₀)⁻¹ ≠ 1 := fun h => hχt₀ (inv_eq_one.mp h)
    have h1 : (1 - (χ t₀)⁻¹) *
        ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) = 0 := by
      rw [sub_mul, one_mul, ← hS', sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  have hmain : (∑ u : Rˣ, (χ u)⁻¹ * ψ u) * conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u)
      = (Fintype.card R : ℂ) := by
    rw [hexp]
    simp_rw [hinner, mul_sub, mul_ite, mul_zero]
    rw [Finset.sum_sub_distrib]
    have h2 : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then
        (χ t)⁻¹ * ((univ.filter (· ∈ m)).card : ℂ) else 0)
        = (∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0)) *
          ((univ.filter (· ∈ m)).card : ℂ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs <;> simp
    rw [h2, hS, zero_mul, sub_zero]
    simp [hχ1]
  have hn : ((‖∑ u : Rˣ, (χ u)⁻¹ * ψ u‖ ^ 2 : ℝ) : ℂ) = (Fintype.card R : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hmain]
  exact_mod_cast hn
end GlobalTheory
