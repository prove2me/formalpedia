-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.centralIdemAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:08:15.393643+00:00
-- url     : https://prove2.me/submissions/bc3285a8-97cd-4a08-953c-3c7a6a66232e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentAction
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_asAlgebraHom_centralIdem
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_isIrreducible_of
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_schur_scalar


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.CentralIdemAct := by
  intro Γ _ _ V _ _ _ W _ _ _ ρ σ hρ hσ
  obtain ⟨hVn, hρ'⟩ := hρ
  obtain ⟨hWn, hσ'⟩ := hσ
  haveI := hVn
  haveI := hWn
  haveI hirrρ : ρ.IsIrreducible := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.isIrreducible_of ρ hρ'
  haveI hirrσ : σ.IsIrreducible := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.isIrreducible_of σ hσ'
  have hc0 : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  haveI : Invertible (Nat.card Γ : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hV0 : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hW0 : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  obtain ⟨μ, hμ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.schur_scalar σ hσ'
    (fun g => (Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ g⁻¹)) (by
      intro g k
      have e : (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹ := by group
      have := Representation.char_conj ρ g⁻¹ k
      simp only [Representation.character] at this
      simp only [e, this])
  have hT : σ.asAlgebraHom (centralIdem ρ) = μ • (1 : Module.End ℂ W) := by
    rw [asAlgebraHom_centralIdem]; exact hμ
  have htr : μ * (Module.finrank ℂ W : ℂ) = (Module.finrank ℂ V : ℂ) *
      ((Nat.card Γ : ℂ)⁻¹ * ∑ g, σ.character g * ρ.character g⁻¹) := by
    have h1 := congrArg (LinearMap.trace ℂ W) hμ
    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.trace_one] at h1
    rw [← h1, Finset.mul_sum, Finset.mul_sum, Nat.card_eq_fintype_card]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Representation.character]
    field_simp
  rw [Representation.char_orthonormal σ ρ] at htr
  rw [hT]
  by_cases h : Nonempty (Representation.Equiv ρ σ)
  · rw [if_pos h] at htr ⊢
    obtain ⟨φ⟩ := h
    have hd : Module.finrank ℂ V = Module.finrank ℂ W := φ.toLinearEquiv.finrank_eq
    rw [hd] at htr
    have : μ = 1 := by
      apply mul_right_cancel₀ hW0
      simpa using htr
    rw [this, one_smul]
  · rw [if_neg h] at htr ⊢
    have : μ = 0 := by
      have h0 : μ * (Module.finrank ℂ W : ℂ) = 0 := by simpa using htr
      exact (mul_eq_zero.mp h0).resolve_right hW0
    rw [this, zero_smul]
end GlobalTheory.CompanionTheory.TyFin
