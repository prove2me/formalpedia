-- Prove2me | solution 1 for GlobalTheory.SW.EisConv.norm_embAll_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:12.005801+00:00
-- url     : https://prove2.me/submissions/6d581fbe-0277-46dc-9f57-0530714a1f5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
import Theorems.Thm_GlobalTheory_SW_EisConv_embAll_apply
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisConv
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
namespace GlobalTheory.SW.EisConv
theorem _root_.solution {m : Type} [Fintype m] {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ)
    (w : m → 𝓞 E) : ‖embAll E m w‖ ^ 2 ≤ ∑ τ : Ψ, ∑ j, ‖τ.1 (w j : E)‖ ^ 2 := by
  refine (Real.le_sqrt (norm_nonneg _) (by positivity)).1 ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun σ => ?_
  obtain ⟨τ, hτ⟩ : ∃ τ : Ψ, ‖σ (w j : E)‖ = ‖τ.1 (w j : E)‖ := by
    by_cases h : σ ∈ Ψ
    · exact ⟨⟨σ, h⟩, rfl⟩
    · refine ⟨⟨ComplexEmbedding.conjugate σ, ?_⟩, by simp⟩
      by_contra hc
      exact h ((hΨ σ).2 hc)
  refine Real.le_sqrt_of_sq_le ?_
  rw [embAll_apply, hτ]
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ : Ψ => ∑ j, ‖τ.1 (w j : E)‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ τ))
  exact Finset.single_le_sum (f := fun j => ‖τ.1 (w j : E)‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ j)
end GlobalTheory.SW.EisConv
