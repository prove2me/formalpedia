-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CharLattice.annihilator_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:22:50.589977+00:00
-- url     : https://prove2.me/submissions/19e5dc1c-1954-4b42-9ab6-5e33c825c823

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CharacterAnnihilatorIntegerLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharLattice
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.CharLattice
theorem _root_.solution (ψ : AddChar k Circle) (n : ℕ) (b : k) (hb : b ≠ 0) (y₀ : k)
    (hy : ψ y₀ ≠ 1) :
    (annihilator ψ n b : Set (Fin n → k)) ⊆
      Set.univ.pi (fun _ => {y : k | valuation k y ≤ valuation k (y₀ / b)}) := by
  intro x hx j _
  have hx' : ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1 := hx
  show valuation k (x j) ≤ valuation k (y₀ / b)
  by_contra hlt'
  have hlt := lt_of_not_ge hlt'
  have hxj : x j ≠ 0 := by
    intro h
    rw [h, map_zero] at hlt
    exact not_lt_zero hlt
  have ht : ∀ i, (Pi.single j (y₀ / b / x j) : Fin n → k) i ∈ 𝒪[k] := by
    intro i
    rw [Valuation.mem_integer_iff]
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same, map_div₀]
      exact (div_le_one₀ ((valuation k).pos_iff.2 hxj)).2 hlt.le
    · rw [Pi.single_eq_of_ne hij, map_zero]
      exact zero_le_one
  have h := hx' _ ht
  have e : b * ((Pi.single j (y₀ / b / x j) : Fin n → k) ⬝ᵥ x) = y₀ := by
    rw [single_dotProduct]
    field_simp
  rw [e] at h
  exact hy h
end GlobalTheory.CompanionTheory.CharLattice
