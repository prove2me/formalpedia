-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:22:49.586271+00:00
-- url     : https://prove2.me/submissions/d8d0c27f-5a25-423d-a488-2536a33b5dca

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorCompactWithinNhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharDual
namespace GlobalTheory.CompanionTheory.CharDual
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (S : Set (Fin n → k)), S ∈ nhds (0 : Fin n → k) →
    ∃ Ξ : AddSubgroup (Fin n → k), IsCompact (Ξ : Set (Fin n → k)) ∧
      ∀ t : Fin n → k, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → t ∈ S := by
  intro k _ _ _ _ ψ _ hψ n S hS
  obtain ⟨x₁, hx₁⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (by ext x; simp [h x])
  rw [nhds_pi] at hS
  obtain ⟨⟨I, γ⟩, ⟨-, hγ⟩, hsub⟩ :=
    (Filter.hasBasis_pi fun _ : Fin n => IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.1 hS
  let ε : Fin n → ValueGroupWithZero k := fun i => valuation k x₁ / γ i
  let Ξ : AddSubgroup (Fin n → k) :=
    { carrier := {ξ | ∀ i, valuation k (ξ i) ≤ ε i}
      zero_mem' := fun i => by simp
      add_mem' := fun {a b} ha hb i =>
        ((valuation k).map_add_le (ha i) (hb i))
      neg_mem' := fun {a} ha i => by
        simpa [Valuation.map_neg] using ha i }
  refine ⟨Ξ, ?_, fun t ht => hsub ?_⟩
  · have hc := isCompact_univ_pi fun i : Fin n =>
      IsNonarchimedeanLocalField.isCompact_closedBall k (ε i)
    convert hc using 1
    ext ξ
    simp [Ξ, Set.mem_pi]
  · intro i hi
    by_contra hlt
    have hle : γ i ≤ valuation k (t i) := not_lt.1 hlt
    have hγi : γ i ≠ 0 := hγ i hi
    have hpos : 0 < γ i := zero_lt_iff.2 hγi
    have hti : t i ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hle
      exact hγi (le_antisymm hle zero_le')
    have hmem : (Pi.single i (x₁ / t i) : Fin n → k) ∈ Ξ := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.single_eq_same, map_div₀, ε]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        gcongr
      · simp [Pi.single_eq_of_ne hj]
    have h1 := ht _ hmem
    rw [single_dotProduct, div_mul_cancel₀ _ hti] at h1
    exact hx₁ h1
end GlobalTheory.CompanionTheory.CharDual
