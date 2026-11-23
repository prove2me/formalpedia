-- Prove2me | solution 1 for GlobalTheory.card_le_pow_of_linearIndependent_theta_principal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:01.106411+00:00
-- url     : https://prove2.me/submissions/0e6b8e9e-c73b-42d4-9597-2b9fa2aaa70e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependentThetaPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Bijective Ef → ∃ (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ) (Q : (Fin g → ℂ) → ℂ) (b : Fin g → ℂ), τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ (∀ j, b j ≠ 0) ∧ (∀ (i : Fin g) (l : Λ) z, (l : Fin g → ℂ) = φ (Pi.single i 1) → (χ l * cexp (Real.pi * (φ z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) = cexp (Q (z + Pi.single i 1) - Q z)) ∧ (∀ (j : Fin g) (l : Λ) z, (l : Fin g → ℂ) = φ (τ.mulVec (Pi.single j 1)) → (χ l * cexp (Real.pi * (φ z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) = b j * cexp (-(2 * Real.pi * I) * z j) * cexp (Q (z + τ.mulVec (Pi.single j 1)) - Q z))) → (∀ (g n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ), 1 ≤ n → (∀ j, b j ≠ 0) → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, (Differentiable ℂ (f k) ∧ (∀ (i : Fin g) z, (f k) (z + Pi.single i 1) = (f k) z) ∧ ∀ (j : Fin g) z, (f k) (z + τ.mulVec (Pi.single j 1)) = b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k) z)) → LinearIndependent ℂ f → N ≤ n ^ g) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Bijective Ef → ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, Differentiable ℂ (f k) ∧ ∀ (l : Λ) z, f k (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ n * f k z) → LinearIndependent ℂ f → N ≤ n ^ g) := by
  intro H1 H2 g Λ hdisc hspan Hm χ Ef hH hpos hχ hEf hbij n hn N f hf hind
  obtain ⟨φ, τ, Q, b, -, -, hΛ, hQd, -, hb, hQ1, hQ2⟩ :=
    H1 g Λ hdisc hspan Hm χ Ef hH hpos hχ hEf hbij
  let T : ((Fin g → ℂ) → ℂ) →ₗ[ℂ] ((Fin g → ℂ) → ℂ) :=
    { toFun := fun h z => h (φ z) * cexp (-((n : ℂ) * Q z))
      map_add' := fun h h' => by funext z; simp [add_mul]
      map_smul' := fun c h => by funext z; simp [mul_assoc] }
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro h hh
    funext w
    have hw := congr_fun hh (φ.symm w)
    change h (φ (φ.symm w)) * cexp (-((n : ℂ) * Q (φ.symm w))) = 0 at hw
    rw [φ.apply_symm_apply] at hw
    exact (mul_eq_zero.mp hw).resolve_right (Complex.exp_ne_zero _)
  refine H2 g n τ b hn hb N (T ∘ f) (fun k => ⟨?_, fun i z => ?_, fun j z => ?_⟩) (hind.map' T hT)
  · change Differentiable ℂ (fun z => f k (φ z) * cexp (-((n : ℂ) * Q z)))
    have hφd : Differentiable ℂ (LinearMap.toContinuousLinearMap φ.toLinearMap) :=
      (LinearMap.toContinuousLinearMap φ.toLinearMap).differentiable
    exact ((hf k).1.comp hφd).mul ((hQd.const_mul _).neg.cexp)
  · change f k (φ (z + Pi.single i 1)) * cexp (-((n : ℂ) * Q (z + Pi.single i 1))) =
      f k (φ z) * cexp (-((n : ℂ) * Q z))
    have hs : (fun j => (((Pi.single i 1 : Fin g → ℤ) j : ℤ) : ℂ)) = Pi.single i 1 := by
      ext j; by_cases hj : j = i <;> simp [Pi.single_apply, hj]
    have hmem : φ (Pi.single i 1) ∈ Λ := (hΛ _).mpr ⟨Pi.single i 1, 0, by
      rw [hs]; ext j; simp [Matrix.mulVec, dotProduct]⟩
    obtain ⟨l, hl⟩ : ∃ l : Λ, (l : Fin g → ℂ) = φ (Pi.single i 1) := ⟨⟨_, hmem⟩, rfl⟩
    rw [map_add, ← hl, (hf k).2 l, hQ1 i l z hl, ← Complex.exp_nat_mul]
    have key : cexp (↑n * (Q (z + Pi.single i 1) - Q z)) * cexp (-(↑n * Q (z + Pi.single i 1))) =
        cexp (-(↑n * Q z)) := by
      rw [← Complex.exp_add]; congr 1; ring
    linear_combination f k (φ z) * key
  · change f k (φ (z + τ *ᵥ Pi.single j 1)) * cexp (-((n : ℂ) * Q (z + τ *ᵥ Pi.single j 1))) =
      b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k (φ z) * cexp (-((n : ℂ) * Q z)))
    have hs : (fun i => (((Pi.single j 1 : Fin g → ℤ) i : ℤ) : ℂ)) = Pi.single j 1 := by
      ext i; by_cases hi : i = j <;> simp [Pi.single_apply, hi]
    have hmem : φ (τ *ᵥ Pi.single j 1) ∈ Λ := (hΛ _).mpr ⟨0, Pi.single j 1, by
      rw [hs]; ext i; simp⟩
    obtain ⟨l, hl⟩ : ∃ l : Λ, (l : Fin g → ℂ) = φ (τ *ᵥ Pi.single j 1) := ⟨⟨_, hmem⟩, rfl⟩
    rw [map_add, ← hl, (hf k).2 l, hQ2 j l z hl, mul_pow, mul_pow, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul]
    have key : cexp (↑n * (-(2 * ↑Real.pi * I) * z j)) *
        cexp (↑n * (Q (z + τ *ᵥ Pi.single j 1) - Q z)) *
        cexp (-(↑n * Q (z + τ *ᵥ Pi.single j 1))) =
        cexp (-(2 * ↑Real.pi * I) * ↑n * z j) * cexp (-(↑n * Q z)) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    linear_combination (b j ^ n * f k (φ z)) * key
end _root_.GlobalTheory
end GlobalTheory
