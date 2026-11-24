-- Prove2me | solution 1 for GlobalTheory.SmGL.IndDual.vol_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:36.185379+00:00
-- url     : https://prove2.me/submissions/ba73eb44-c2db-4e5d-aac2-0d6dd5d36e37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralIntegralGLMulRightComplexProductSigma
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Theorems.Thm_GlobalTheory_SmGL_IndDual_isOpen_cell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W'] {P : Subgroup G}
variable [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G}
  (hK : IsCompact (K : Set G)) (σ : Representation ℂ P W) (τ : Representation ℂ P W')
  (B : W' →ₗ[ℂ] Module.Dual ℂ W)
include hK
namespace GlobalTheory.SmGL.IndDual
theorem _root_.solution (hKo : IsOpen (K : Set G)) {J : Subgroup G} (hJ : IsOpen (J : Set G)) :
    (μ.real (K ∩ cell P J) : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero, Ne, measureReal_eq_zero_iff
    ((measure_mono Set.inter_subset_left).trans_lt hK.measure_lt_top).ne]
  exact ((hKo.inter (isOpen_cell hJ)).measure_pos μ ⟨1, one_mem K, 1, by simp⟩).ne'
end GlobalTheory.SmGL.IndDual
