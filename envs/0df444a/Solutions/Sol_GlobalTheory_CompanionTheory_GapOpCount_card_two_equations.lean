-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpCount.card_two_equations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:32.683162+00:00
-- url     : https://prove2.me/submissions/78224110-68f5-436c-ba0e-a21ae590aea8

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanes
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpCount_pairMap_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpCount
namespace GlobalTheory.CompanionTheory.GapOpCount
theorem _root_.solution (k : Type) [Field k] [Fintype k] (n : ℕ) (a b : Fin (n + 1) → k)
    (ha : a ≠ 0) (hb : ∀ s : k, b ≠ s • a) :
    Fintype.card k ^ 2 * (Finset.univ.filter
      (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  have hr := pairMap_range a b ha hb
  obtain ⟨x0, hx0⟩ : ∃ x0, pairMap a b x0 = ((1, 1) : k × k) := by
    have : ((1, 1) : k × k) ∈ LinearMap.range (pairMap a b) := by rw [hr]; trivial
    exact this
  have hx1 : a ⬝ᵥ x0 = 1 := congrArg Prod.fst hx0
  have hx2 : b ⬝ᵥ x0 = 1 := congrArg Prod.snd hx0
  have hker : ∀ y, y ∈ LinearMap.ker (pairMap a b) ↔ a ⬝ᵥ y = 0 ∧ b ⬝ᵥ y = 0 := by
    intro y
    rw [LinearMap.mem_ker]
    exact Prod.ext_iff
  let e : LinearMap.ker (pairMap a b) ≃ {x : Fin (n + 1) → k // a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1} :=
    { toFun := fun y => ⟨y.1 + x0, by
        have h := (hker y.1).1 y.2
        simp [dotProduct_add, h.1, h.2, hx1, hx2]⟩
      invFun := fun x => ⟨x.1 - x0, by
        rw [hker]
        simp [dotProduct_sub, x.2.1, x.2.2, hx1, hx2]⟩
      left_inv := fun y => by simp
      right_inv := fun x => by simp }
  have hcard : (Finset.univ.filter
      (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card
      = Fintype.card k ^ Module.finrank k (LinearMap.ker (pairMap a b)) := by
    rw [← Module.card_eq_pow_finrank (K := k) (V := LinearMap.ker (pairMap a b)),
      Fintype.card_congr e, Fintype.card_subtype]
  have hrank := LinearMap.finrank_range_add_finrank_ker (pairMap a b)
  rw [hr, finrank_top] at hrank
  have h2 : Module.finrank k (k × k) = 2 := by simp
  have hV : Module.finrank k (Fin (n + 1) → k) = n + 1 := by simp
  rw [h2, hV] at hrank
  rw [hcard, ← pow_add, hrank]
end GlobalTheory.CompanionTheory.GapOpCount
