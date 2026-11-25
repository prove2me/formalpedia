-- Prove2me | solution 1 for GlobalTheory.DoublingLength.summable_pairTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:22.77548+00:00
-- url     : https://prove2.me/submissions/8933d42a-c9e9-48ef-9425-2f50c2c052b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
import Theorems.Thm_GlobalTheory_DoublingLength_hasSum_pairTerm_fiber
import Theorems.Thm_GlobalTheory_DoublingLength_hasSum_pairTerm_total
import Theorems.Thm_GlobalTheory_DoublingLength_norm_pairTerm
import Theorems.Thm_GlobalTheory_DoublingLength_isBorelSph_norm
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.DoublingLength
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.DoublingLength
theorem _root_.solution {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (hγ : ∀ i, γ i ≠ 0)
    {X : ℂ} (hX1 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1)
    (hX2 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) : Summable (pairTerm X φ) := by
  have hψ := isBorelSph_norm hφ
  have hγ' : ∀ i, (‖γ i‖ : ℂ) ≠ 0 := fun i => by simpa using hγ i
  have hX1' : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * (‖γ i‖ : ℂ) * (‖X‖ : ℂ)‖ < 1 := fun i => by
    simpa using hX1 i
  have hX2' : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * ((‖γ i‖ : ℂ))⁻¹ * (‖X‖ : ℂ)‖ < 1 := fun i => by
    simpa using hX2 i
  refine Summable.of_norm ((summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨fun h => ?_, ?_⟩)
  · have := (hasSum_pairTerm_fiber hψ hγ' hX1' h).summable
    simp_rw [← norm_pairTerm] at this
    exact Complex.summable_ofReal.1 this
  · refine Complex.summable_ofReal.1 ((hasSum_pairTerm_total hψ hγ' hX2'
      (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * (‖γ i‖ : ℂ) * (‖X‖ : ℂ))⁻¹)).summable.congr
        fun h => ?_)
    rw [Complex.ofReal_tsum]
    simp_rw [norm_pairTerm]
    exact (hasSum_pairTerm_fiber hψ hγ' hX1' h).tsum_eq.symm
end GlobalTheory.DoublingLength
