-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:33:20.416092+00:00
-- url     : https://prove2.me/submissions/d9e38c35-2d37-447d-9750-703b4a303f94

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeAnnihilatorWithinNhds
import Theorems.Thm_GlobalTheory_CompanionTheory_AnnihShrink_exists_ne_zero_valuation_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_AnnihShrink_isCompact_box
import Theorems.Thm_GlobalTheory_CompanionTheory_AnnihShrink_isOpen_box

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnnihShrink
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.AnnihShrink
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (U : Set (Fin n → k)),
      U ∈ nhds (0 : Fin n → k) → ∃ A : AddSubgroup (Fin n → k),
        IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧
        {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ⊆ U := by
  intro k _ _ _ _ ψ _ hne n U hU
  obtain ⟨y₀, hy⟩ : ∃ y : k, ψ y ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne (AddChar.ext _ _ fun t => by simpa using hall t)
  have hy0 : y₀ ≠ 0 := by
    rintro rfl
    exact hy (by simp)

  obtain ⟨I, V, hV, hIV⟩ : ∃ (I : Set (Fin n)) (V : Fin n → Set k),
      (∀ i, V i ∈ nhds (0 : k)) ∧ I.pi V ⊆ U := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, _, V, hV, hIV⟩ := hU
    exact ⟨I, V, hV, hIV⟩
  have hball : ∀ i, ∃ γ : (ValueGroupWithZero k)ˣ, {y : k | valuation k y < γ} ⊆ V i := fun i =>
    (IsValuativeTopology.mem_nhds_zero_iff (V i)).1 (hV i)
  choose g hg using hball
  obtain ⟨γ, hγ0, hγ⟩ : ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ i, γ ≤ (g i : ValueGroupWithZero k) := by
    obtain ⟨m, hm⟩ := Finite.exists_ge g
    exact ⟨m, m.ne_zero, fun i => Units.val_le_val.2 (hm i)⟩
  obtain ⟨t, ht0, ht⟩ := exists_ne_zero_valuation_lt k γ hγ0
  refine ⟨box n (y₀ / t), isCompact_box n _, isOpen_box n _ (div_ne_zero hy0 ht0), ?_⟩
  intro ξ hξ
  apply hIV
  intro i _
  apply hg i
  show valuation k (ξ i) < g i
  refine lt_of_lt_of_le ?_ (hγ i)
  by_contra hlt
  have hle : γ ≤ valuation k (ξ i) := not_lt.mp hlt
  have hvξ : valuation k (ξ i) ≠ 0 := (lt_of_lt_of_le (zero_lt_iff.mpr hγ0) hle).ne'
  have hξi : ξ i ≠ 0 := (Valuation.ne_zero_iff _).1 hvξ
  have hmem : (Pi.single i (y₀ / ξ i) : Fin n → k) ∈ box n (y₀ / t) := by
    intro j
    by_cases h : j = i
    · subst h
      have he : y₀ / ξ j = (y₀ / t) * (t / ξ j) := by field_simp
      rw [Pi.single_eq_same, he, map_mul]
      refine mul_le_of_le_one_right' ?_
      rw [map_div₀]
      exact (div_le_one₀ (zero_lt_iff.mpr hvξ)).2 (ht.le.trans hle)
    · simp [Pi.single_eq_of_ne h]
  have h1 := hξ _ hmem
  rw [dotProduct_single, mul_div_cancel₀ _ hξi] at h1
  exact hy h1
end GlobalTheory.CompanionTheory.AnnihShrink
