-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnramDict.tendsto_pow_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:14.687892+00:00
-- url     : https://prove2.me/submissions/6f8a1d82-4bd5-419a-b0d0-7b5b14365d45

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_exists_pow_lt_value

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
theorem _root_.solution {x : E} (hx : valuation E x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' E).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt_value E hx hγ
  filter_upwards [eventually_ge_atTop m] with n hn
  show valuation E (x ^ n) < γ
  rw [map_pow]
  exact (pow_le_pow_right_of_le_one' hx.le hn).trans_lt hm
end GlobalTheory.CompanionTheory.UnramDict
