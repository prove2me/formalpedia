-- Prove2me | solution 1 for GlobalTheory.SW.isHeat_thH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:39.015258+00:00
-- url     : https://prove2.me/submissions/da193327-3875-4bb7-9fcb-e7800f8f4010

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
import Theorems.Thm_GlobalTheory_SW_ExpSum_differentiableOn
import Theorems.Thm_GlobalTheory_SW_ExpSum_isOpen_dom
import Theorems.Thm_GlobalTheory_SW_ExpSum_add_smul_dir
import Theorems.Thm_GlobalTheory_SW_ExpSum_heat_dir
import Theorems.Thm_GlobalTheory_SW_thH_summable_and_inj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory.SW.ExpSum
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → IsHeat Ψ (thH Ψ φ) := by
  intro E _ _ _ Ψ hΨ n N φ hφ
  have hs : ∀ p ∈ {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N},
      Summable fun x => ‖φ x * cexp (form Ψ x p)‖ := fun p hp =>
    (GlobalTheory.SW.thH_summable_and_inj E Ψ hΨ n N φ hφ _ hp).1 _ _
  refine ⟨differentiableOn (isOpen_dom Ψ) φ (form Ψ) hs, fun Z hZ z z' τ a b => ?_⟩
  simp only [add_smul_dir]
  exact heat_dir Ψ φ hs Z hZ z z' τ a b
end GlobalTheory.SW
