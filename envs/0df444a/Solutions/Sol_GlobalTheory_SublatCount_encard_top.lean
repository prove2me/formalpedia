-- Prove2me | solution 1 for GlobalTheory.SublatCount.encard_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:03:15.214879+00:00
-- url     : https://prove2.me/submissions/787f6ac2-b4f2-4d12-9873-7e26067abcda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSublatticesQuotientProdDegreeOnePrimes
import Theorems.Thm_GlobalTheory_SublatCount_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.SublatCount
variable {O N : Type} [CommRing O] [AddCommGroup N] [Module O N]
namespace GlobalTheory.SublatCount
theorem _root_.solution : (Ker (⊤ : Ideal O) N).encard = 1 := by
  rw [Set.encard_eq_one]
  refine ⟨⊤, Set.eq_singleton_iff_unique_mem.2 ⟨⟨0, fun y => ⟨0, Subsingleton.elim _ _⟩, by simp⟩, ?_⟩⟩
  intro L hL
  rw [eq_top_iff]
  intro x _
  simpa using smul_mem hL (c := 1) trivial x
end GlobalTheory.SublatCount
