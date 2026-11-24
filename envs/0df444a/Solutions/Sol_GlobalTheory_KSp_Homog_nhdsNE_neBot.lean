-- Prove2me | solution 1 for GlobalTheory.KSp.Homog.nhdsNE_neBot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:24:46.98405+00:00
-- url     : https://prove2.me/submissions/a97ed046-1212-44f3-abca-1da073ed463f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.Homog
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.KSp.Homog
theorem _root_.solution : (𝓝[≠] (0 : F)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
  intro t ht
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset ht
  exact ⟨s, hs (show valuation F (s : F) ≤ valuation F (s : F) from le_refl _), s.ne_zero⟩
end GlobalTheory.KSp.Homog
