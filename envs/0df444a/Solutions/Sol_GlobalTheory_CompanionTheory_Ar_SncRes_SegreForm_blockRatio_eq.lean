-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.blockRatio_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:56:07.086091+00:00
-- url     : https://prove2.me/submissions/42e550ee-1d65-4a2b-9e13-aee7bc616618

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StandardSmoothChartOfNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncRes GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {N : ℕ} (y : (Σ k, ι k) → Ω) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
namespace GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
theorem _root_.solution (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (p : Σ k, ι k) [DecidableEq K] :
    y p / y ⟨p.1, E c₀ p.1⟩ =
      (∏ k, y ⟨k, E (E.symm (Function.update (E c₀) p.1 p.2)) k⟩) / ∏ k, y ⟨k, E c₀ k⟩ := by
  obtain ⟨k₀, i⟩ := p
  simp only [Equiv.apply_symm_apply]
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  rw [div_eq_div_iff (hc k₀) h0,
    ← Finset.mul_prod_erase Finset.univ (fun k => y ⟨k, E c₀ k⟩) (Finset.mem_univ k₀),
    ← Finset.mul_prod_erase Finset.univ (fun k => y ⟨k, Function.update (E c₀) k₀ i k⟩) (Finset.mem_univ k₀)]
  have e : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, Function.update (E c₀) k₀ i k⟩ =
      ∏ k ∈ Finset.univ.erase k₀, y ⟨k, E c₀ k⟩ :=
    Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [e, Function.update_self]
  ring
end GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
