-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.comm_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:26:30.01126+00:00
-- url     : https://prove2.me/submissions/9fae2b06-540d-4cb4-8fbb-23e39bf8967c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_comm_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_nz_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RootExch
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RootExch
theorem _root_.solution {Φ Ψ : ι → ι → Prop} {E : ι → ι → K} (ψ₀ : AddChar K ℂ) (hΦ : IsPat Φ)
    (hsupp : ∀ i j, E i j ≠ 0 → Φ i j) (p q r t : ι)
    (hcomp : ∀ i j k, Φ i j → Φ j k → E i k ≠ 0 → i = p ∧ k = q)
    (g : GL ι K) (hg : g ∈ patSet K Φ) (hgi : g⁻¹ ∈ patSet K Φ) (hrt : Φ r t)
    (hΨ : ∀ i j, (i = r ∨ Φ i r) → (t = j ∨ Φ t j) → ¬ (i = r ∧ j = t) → Ψ i j)
    (hErt : E r t = 0) (h : r ≠ t) (s : K) :
    tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹ ∈ patSet K Ψ ∧
      patChar E ψ₀ (tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹) =
        ψ₀ (-(s * E p q * (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)) := by
  have htr : (g : Matrix ι ι K) t r = 0 := by
    by_contra hc
    rcases nz_of_mem hg hc with h' | h'
    · exact h h'.symm
    · exact hΦ.1 _ (hΦ.2 _ _ _ h' hrt)
  have hirr : ∀ i, (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t i = 0 := by
    intro i
    by_contra hc
    have h1 := nz_of_mem hg (left_ne_zero_of_mul hc)
    have h2 := nz_of_mem hgi (right_ne_zero_of_mul hc)
    have hΦrr : Φ r r ∨ r = t := by
      rcases h1 with rfl | h1 <;> rcases h2 with h2 | h2
      · exact Or.inr h2.symm
      · exact Or.inl (hΦ.2 _ _ _ hrt h2)
      · subst h2; exact Or.inl (hΦ.2 _ _ _ hrt h1)
      · exact Or.inl (hΦ.2 _ _ _ hrt (hΦ.2 _ _ _ h2 h1))
    rcases hΦrr with h3 | h3
    · exact hΦ.1 _ h3
    · exact h h3
  constructor
  · intro i j
    constructor
    · intro hij
      subst hij
      have hh : ¬ (i = r ∧ i = t) := fun h' => h (h'.1.symm.trans h'.2)
      rw [comm_entry g r t h s htr, if_neg hh, mul_assoc, hirr]
      simp
    · intro hij hn
      rw [comm_entry g r t h s htr]
      by_cases hrt' : i = r ∧ j = t
      · obtain ⟨rfl, rfl⟩ := hrt'
        rw [(hg i i).1 rfl, (hgi j j).1 rfl]
        simp [Matrix.one_apply, hij]
      · have hz : (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j = 0 := by
          by_contra hc
          exact hn (hΨ i j (nz_of_mem hg (left_ne_zero_of_mul hc))
            (nz_of_mem hgi (right_ne_zero_of_mul hc)) hrt')
        rw [if_neg hrt', mul_assoc, hz]
        simp [Matrix.one_apply, hij]
  · unfold patChar
    congr 1
    have hterm : ∀ i j, E i j * ((tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹ : GL ι K) : Matrix ι ι K) i j =
        if i = p ∧ j = q then
          -(s * E p q * (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q) else 0 := by
      intro i j
      by_cases hE : E i j = 0
      · rw [hE, zero_mul]
        split_ifs with hpq
        · obtain ⟨rfl, rfl⟩ := hpq
          rw [hE]; simp
        · rfl
      · have hΦij := hsupp i j hE
        have hij : i ≠ j := fun h' => hΦ.1 j (h' ▸ hΦij)
        have hrt' : ¬ (i = r ∧ j = t) := by
          rintro ⟨rfl, rfl⟩
          exact hE hErt
        rw [comm_entry g r t h s htr, if_neg hrt']
        by_cases hz : (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j = 0
        · split_ifs with hpq
          · obtain ⟨rfl, rfl⟩ := hpq
            have : s * E i j * (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j =
              s * E i j * ((g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j) := by ring
            rw [this, hz, mul_assoc, hz]
            simp [Matrix.one_apply, hij]
          · rw [mul_assoc, hz]
            simp [Matrix.one_apply, hij]
        · have h1 := nz_of_mem hg (left_ne_zero_of_mul hz)
          have h2 := nz_of_mem hgi (right_ne_zero_of_mul hz)
          have hpq : i = p ∧ j = q := by
            rcases h1 with h1 | h1
            · rcases h2 with h2 | h2
              · exact absurd ⟨h1, h2.symm⟩ hrt'
              · subst h1; exact hcomp _ _ _ hrt h2 hE
            · rcases h2 with h2 | h2
              · subst h2; exact hcomp _ _ _ h1 hrt hE
              · exact hcomp _ _ _ h1 (hΦ.2 _ _ _ hrt h2) hE
          obtain ⟨rfl, rfl⟩ := hpq
          rw [if_pos ⟨rfl, rfl⟩]
          simp only [Matrix.one_apply, if_neg hij]
          ring
    simp only [hterm]
    by_cases hp : True
    · rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
      · simp
      · intro b _ hb; simp [hb]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · exact absurd trivial hp
end GlobalTheory.CompanionTheory.RootExch
