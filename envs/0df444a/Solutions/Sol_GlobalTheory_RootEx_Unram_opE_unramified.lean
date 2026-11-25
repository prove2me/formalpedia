-- Prove2me | solution 1 for GlobalTheory.RootEx.Unram.opE_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:09:12.014174+00:00
-- url     : https://prove2.me/submissions/b48fca39-4eb4-4843-bf8e-ee1f7759e75e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Theorems.Thm_GlobalTheory_RootEx_Unram_mem_coset
import Theorems.Thm_GlobalTheory_RootEx_Unram_intM_affPt
import Theorems.Thm_GlobalTheory_RootEx_Unram_intM_colE
import Theorems.Thm_GlobalTheory_RootEx_Unram_mem_of_psi
import Theorems.Thm_GlobalTheory_RootEx_Unram_opE_of_ite
import Theorems.Thm_GlobalTheory_RootEx_Unram_psi_ch_eq_one
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_MaxM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Unram
open GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.RootEx.Unram
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (_ : Φ = Set.indicator {x | ∀ r s, valuation k (x r s) ≤ 1} 1), (∀ (h : GL (n ⊕ Fin c) k) (x₀ : Matrix n n' k), opE ψ ν p (om μ 1 h Φ) x₀ ≠ 0 → ∃ r ∈ R k n c p, ∃ w ∈ KO k (n ⊕ Fin c), h = r * w) ∧ opE ψ ν p Φ = Set.indicator {x | ∀ r s, valuation k (x r s) ≤ 1} 1 ∧ ∀ β : n → k, p + 1 ≤ c → opE ψ ν (p + 1) (om μ 1 (colE c (p + 1) β) Φ) = Set.indicator {x | (∀ r s, valuation k (x r s) ≤ 1) ∧ ∀ r, valuation k (β r) ≤ 1} 1 := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ hψ ν hν μ Φ hΦ
  classical
  have hΦ' : ∀ x, Φ x = if IntM x then 1 else 0 := fun x => by
    rw [hΦ, Set.indicator_apply]; exact if_congr Iff.rfl rfl rfl
  refine ⟨fun h x₀ hne => ?_, ?_, fun β hp => ?_⟩
  · have := hν.1
    have hA : ∃ e, IntM ((h⁻¹).val * affPt (c := c) p x₀ e) := by
      by_contra hn
      push Not at hn
      apply hne
      simp only [opE, om, hΦ', Units.val_one, Matrix.mul_one, hn, if_false, mul_zero, zero_mul, integral_zero]
    obtain ⟨e, he⟩ := hA
    refine mem_coset h x₀ e he fun D hD hI => mem_of_psi hψ fun t ht => ?_
    have := psi_ch_eq_one ψ ν _ x₀ hne ((-t) • D) (fun r s hf => by simp [hD r s hf]) fun x => by
      have h1 : IntM ((h⁻¹).val * ((-t) • D)) := by
        rw [Matrix.mul_smul]
        exact fun r s => mul_mem (neg_mem ht) (hI r s)
      have h2 : IntM ((h⁻¹).val * (x + (-t) • D)) ↔ IntM ((h⁻¹).val * x) := by
        rw [Matrix.mul_add]
        exact ⟨fun h => by simpa using h.add h1.neg, fun h => h.add h1⟩
      simp only [om, hΦ', Units.val_one, Matrix.mul_one, h2]
    simpa [ch, Finset.mul_sum] using this
  · funext x₀
    rw [opE_of_ite hψ hν Φ x₀ (IntM x₀) fun e => by simp only [hΦ', intM_affPt], Set.indicator_apply]
    exact if_congr Iff.rfl rfl rfl
  · funext x₀
    have hdet : Matrix.GeneralLinearGroup.det (colE c (p + 1) β) = 1 := by
      ext
      simp [colE, upU]
    rw [opE_of_ite hψ hν _ x₀ (IntM x₀ ∧ ∀ r, β r ∈ 𝒪[k]) fun e => by
      simp only [om, hΦ', hdet, Units.val_one, Matrix.mul_one, intM_colE hp, intM_affPt, and_right_comm]
      simp [nabs], Set.indicator_apply]
    exact @if_congr _ _ _ (_) (_) _ _ _ _ Iff.rfl rfl rfl
end GlobalTheory.RootEx.Unram
