-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.chain_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:26:02.113426+00:00
-- url     : https://prove2.me/submissions/92981a7b-dd2f-4b5a-97e9-1880da18464c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchangeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChainIndependence
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_chainUnion_isPat
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_chainUnion_remove_right
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_chainUnion_remove_left
import Theorems.Thm_P2M_GlobalTheory_T_root_exchange__809cf020be98


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution (K : Type) [Field K] [Fintype K] [DecidableEq K] (m k t : ℕ) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin m ⊕ Fin k) K → ℂ) (hψ : ψ₀ ≠ 1) (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g)
    (ht : t + 1 < m) :
    wh (chainPat m k (t + 1)) (chainE K m k) ψ₀ χ = wh (chainPat m k t) (chainE K m k) ψ₀ χ := by
  have hE : ∀ i j, chainE K m k i j ≠ 0 →
      (∃ a b : Fin m, i = Sum.inl a ∧ j = Sum.inl b ∧ (b : ℕ) = a + 1) ∨
      (∃ w v : Fin k, i = Sum.inr w ∧ j = Sum.inr v ∧ (v : ℕ) = w + 1) := by
    rintro (a | w) (b | v) h
    · left
      by_cases hab : (b : ℕ) = a + 1
      · exact ⟨a, b, rfl, rfl, hab⟩
      · simp [chainE, hab] at h
    · simp [chainE] at h
    · simp [chainE] at h
    · right
      by_cases hab : (v : ℕ) = w + 1
      · exact ⟨w, v, rfl, rfl, hab⟩
      · simp [chainE, hab] at h
  have h := GlobalTheory.T.root_exchange' K (Fin m ⊕ Fin k) (chainUnion m k t) (chainE K m k) ψ₀
    (fun x => Sum.isRight x = true) (Sum.inl ⟨t, by omega⟩) (Sum.inl ⟨t + 1, ht⟩) χ
    (chainUnion_isPat m k t) hψ hχ
    (by
      rintro (a | w) hw
      · simp at hw
      · simp [chainUnion])
    (by simp [chainE])
    (by
      intro i j hij
      rcases hE i j hij with ⟨a, b, rfl, rfl, hab⟩ | ⟨w, v, rfl, rfl, hab⟩ <;>
        simp only [chainUnion, Fin.lt_def] <;> omega)
    (by
      rintro (a | w) hw
      · simp at hw
      · simp [chainE])
    (by
      rintro (a | w) (b | v) hw h1 h2
      · simp at hw
      · simp at hw
      · simp only [chainUnion, Fin.lt_def] at h1 h2
        omega
      · rfl)
    (by
      rintro (a | w) (b | v) hw h1 h2
      · simp at hw
      · simp at hw
      · simp only [chainUnion, Fin.lt_def] at h1 h2
        omega
      · rfl)
    (by
      intro i j l hij hjl hil
      rcases hE i l hil with ⟨a, b, rfl, rfl, hab⟩ | ⟨w, v, rfl, rfl, hab⟩
      · rcases j with c | u
        · simp only [chainUnion, Fin.lt_def] at hij hjl
          omega
        · simp only [chainUnion] at hij hjl
          have h1 : (a : ℕ) = t := by omega
          refine ⟨?_, ?_, by simp⟩
          · simp [Fin.ext_iff, h1]
          · simp [Fin.ext_iff]; omega
      · rcases j with c | u
        · simp only [chainUnion] at hij hjl
          omega
        · simp only [chainUnion, Fin.lt_def] at hij hjl
          omega)
  rw [chainUnion_remove_right m k t ⟨t + 1, ht⟩ rfl,
    chainUnion_remove_left m k t ⟨t, by omega⟩ rfl] at h
  exact h
end GlobalTheory.CompanionTheory.TyFin
