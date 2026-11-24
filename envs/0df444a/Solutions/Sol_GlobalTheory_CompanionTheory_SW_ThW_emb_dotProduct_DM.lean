-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.emb_dotProduct_DM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:53:26.316909+00:00
-- url     : https://prove2.me/submissions/7aeb4ffa-7e79-4020-8399-879e58ad2800

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicCharacterExponentialFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_DM_mulVec_emb_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker
namespace GlobalTheory.CompanionTheory.SW.ThW
theorem _root_.solution {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (a y : ι → F) :
    emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) = ∑ w, ρ w (a ⬝ᵥ (B *ᵥ y)) := by
  have h : ∀ w, ρ w (a ⬝ᵥ (B *ᵥ y)) = ∑ i, ρ w (a i) * ρ w ((B *ᵥ y) i) := by
    intro w
    simp [dotProduct, map_sum, map_mul]
  simp only [h]
  rw [dotProduct, Fintype.sum_prod_type_right]
  simp only [DM_mulVec_emb_apply, emb]
end GlobalTheory.CompanionTheory.SW.ThW
