-- Prove2me | solution 1 for GlobalTheory.eq_of_perm_inv_invariant_of_multiset_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:37:10.575525+00:00
-- url     : https://prove2.me/submissions/9eddd414-c03d-4b24-b60d-3134c0dd59c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymmetricFunctionInverseInvariant
import Theorems.Thm_GlobalTheory_exists_perm_of_univ_map_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (m : ℕ) (f : (Fin m → ℂ) → ℂ), (∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) → (∀ π : Equiv.Perm (Fin m), f (α ∘ π) = f α) ∧ ∀ i, f (Function.update α i (α i)⁻¹) = f α) → ∀ α α' : Fin m → ℂ, (∀ i, α i ≠ 0) → Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) = Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹) → f α = f α' := by
  classical
  intro m f hf α α' hα h
  have hα' : ∀ i, α' i ≠ 0 := by
    intro i hi
    have hmem : (0 : ℂ) ∈ Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹) :=
      Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, hi⟩))
    rw [← h] at hmem
    rcases Multiset.mem_add.1 hmem with h1 | h1
    · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h1
      exact hα j hj
    · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h1
      exact hα j (inv_eq_zero.1 hj)
  have h2 := congrArg (Multiset.map (fun x : ℂ => x + x⁻¹)) h
  simp only [Multiset.map_add, Multiset.map_map, Function.comp_def, inv_inv] at h2
  have e1 : ∀ γ : Fin m → ℂ, (fun i => (γ i)⁻¹ + γ i) = fun i => γ i + (γ i)⁻¹ :=
    fun γ => funext fun i => add_comm _ _
  rw [e1 α, e1 α'] at h2
  have h3 : Finset.univ.val.map (fun i => α i + (α i)⁻¹)
      = Finset.univ.val.map (fun i => α' i + (α' i)⁻¹) := by
    ext c
    have := congrArg (Multiset.count c) h2
    simp only [Multiset.count_add] at this
    omega
  obtain ⟨π, hπ⟩ := exists_perm_of_univ_map_eq _ _ h3
  have hor : ∀ i, α' i = α (π i) ∨ α' i = (α (π i))⁻¹ := by
    intro i
    have h4 := hπ i
    have ha := hα (π i)
    have hb := hα' i
    have h5 : (α' i - α (π i)) * (α' i * α (π i) - 1) = 0 := by
      field_simp at h4
      linear_combination -h4
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact Or.inl (sub_eq_zero.1 h6)
    · exact Or.inr (eq_inv_of_mul_eq_one_left (sub_eq_zero.1 h6))
  have hβ : ∀ i, (α ∘ π) i ≠ 0 := fun i => hα _
  have key : ∀ s : Finset (Fin m),
      f (fun i => if i ∈ s then α' i else (α ∘ π) i) = f (α ∘ π) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Function.comp_def]
    | insert j s hj ih =>
      rw [← ih]
      have hne : ∀ i, (fun i => if i ∈ s then α' i else (α ∘ π) i) i ≠ 0 := by
        intro i
        by_cases hi : i ∈ s
        · simpa [hi] using hα' i
        · simpa [hi] using hα (π i)
      rcases hor j with h6 | h6
      · congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
      · rw [← (hf _ hne).2 j]
        congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  rw [← (hf α hα).1 π, ← this]
end GlobalTheory
