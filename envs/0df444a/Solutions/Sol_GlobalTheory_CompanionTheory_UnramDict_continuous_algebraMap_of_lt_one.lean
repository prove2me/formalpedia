-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnramDict.continuous_algebraMap_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:54:50.363631+00:00
-- url     : https://prove2.me/submissions/87f2dba8-09cf-4fd5-947e-036d3233b53a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_exists_pow_lt_value
import Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_value_algebraMap_le_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnramDict
variable {k E : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra k E]
namespace GlobalTheory.CompanionTheory.UnramDict
theorem _root_.solution [ValuativeExtension k E] {π : k}
    (h0 : valuation E (algebraMap k E π) ≠ 0) (h1 : valuation E (algebraMap k E π) < 1) :
    Continuous (algebraMap k E) := by
  refine continuous_of_continuousAt_zero (algebraMap k E) ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero' E).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt_value E h1 hγ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at h0
  have hmem : {a : k | valuation k a < valuation k (π ^ m)} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem (by simpa using pow_ne_zero m hπ0)
  filter_upwards [hmem] with a ha
  have h2 : valuation E (algebraMap k E a) < valuation E (algebraMap k E (π ^ m)) := by
    rw [← not_le, value_algebraMap_le_iff, not_le]
    exact ha
  show valuation E (algebraMap k E a) < γ
  refine h2.trans_le ?_
  rw [map_pow, map_pow]
  exact hm.le
end GlobalTheory.CompanionTheory.UnramDict
