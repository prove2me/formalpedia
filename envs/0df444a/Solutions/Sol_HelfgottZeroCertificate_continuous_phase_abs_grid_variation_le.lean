-- Prove2me | solution 1 for HelfgottZeroCertificate.continuous_phase_abs_grid_variation_le
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-18T12:00:48.462811+00:00
-- url     : https://prove2.me/submissions/3c2601da-319d-40ef-b2a9-779a047f9e0a

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace HelfgottZeroCertificate
open Set

/-- A continuous phase cannot cross more equally spaced levels than the
number of available points representing those levels. -/
theorem continuous_phase_grid_variation_le {θ : ℝ → ℝ} {a b c p : ℝ}
    (hp : 0 < p) (hc : ContinuousOn θ (uIcc a b)) (Z : Finset ℝ)
    (hZ : ∀ t ∈ uIcc a b, ∀ k : ℤ, θ t = c+(k:ℝ)*p → t ∈ Z) :
    θ b-θ a ≤ p*((Z.card:ℝ)+1) := by
  classical
  by_contra! hlarge
  let k : ℤ := ⌊(θ a-c)/p⌋+1
  have hfloor := Int.floor_le ((θ a-c)/p)
  have hceil := Int.lt_floor_add_one ((θ a-c)/p)
  have hklo : θ a < c+(k:ℝ)*p := by
    dsimp [k]
    push_cast
    have := (div_lt_iff₀ hp).mp hceil
    nlinarith
  have hkhi : c+(k:ℝ)*p ≤ θ a+p := by
    dsimp [k]
    push_cast
    have := (le_div_iff₀ hp).mp hfloor
    nlinarith
  have hab : θ a ≤ θ b := by
    have := Nat.cast_nonneg (α:=ℝ) Z.card
    nlinarith
  have hex (i : Fin (Z.card+1)) :
      ∃ t ∈ uIcc a b, θ t = c+((k+(i.val:ℤ):ℤ):ℝ)*p := by
    apply intermediate_value_uIcc hc
    rw [uIcc_of_le hab]
    have hi : (i.val:ℝ) ≤ (Z.card:ℝ) := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    have hi0 : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
    push_cast
    constructor <;> nlinarith
  choose t ht he using hex
  let f : Fin (Z.card+1) → Z := fun i => ⟨t i,hZ _ (ht i) _ (he i)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have htij : t i = t j := congrArg Subtype.val hij
    have hi := he i
    have hj := he j
    rw [htij] at hi
    have hijval : (i.val:ℝ) = (j.val:ℝ) := by
      push_cast at hi hj
      nlinarith
    apply Fin.ext
    exact_mod_cast hijval
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

theorem continuous_phase_abs_grid_variation_le {θ : ℝ → ℝ} {a b c p : ℝ}
    (hp : 0 < p) (hc : ContinuousOn θ (uIcc a b)) (Z : Finset ℝ)
    (hZ : ∀ t ∈ uIcc a b, ∀ k : ℤ, θ t = c+(k:ℝ)*p → t ∈ Z) :
    |θ b-θ a| ≤ p*((Z.card:ℝ)+1) := by
  apply abs_le.mpr
  constructor
  · have h := continuous_phase_grid_variation_le hp
      (show ContinuousOn θ (uIcc b a) by simpa only [uIcc_comm] using hc) Z
      (fun t ht k hk => hZ t (by simpa only [uIcc_comm] using ht) k hk)
    linarith
  · exact continuous_phase_grid_variation_le hp hc Z hZ





end HelfgottZeroCertificate


open Set
open scoped BigOperators
theorem solution :
∀ {θ : ℝ → ℝ} {a b c p : ℝ},
  0 < p →
    ContinuousOn θ (Set.uIcc a b) →
      ∀ (Z : Finset ℝ), (∀ t ∈ Set.uIcc a b, ∀ (k : ℤ), θ t = c + ↑k * p → t ∈ Z) → |θ b - θ a| ≤ p * (↑Z.card + 1) := @HelfgottZeroCertificate.continuous_phase_abs_grid_variation_le
