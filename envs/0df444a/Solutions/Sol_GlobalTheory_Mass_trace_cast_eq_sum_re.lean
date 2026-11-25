-- Prove2me | solution 1 for GlobalTheory.Mass.trace_cast_eq_sum_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:43:01.482806+00:00
-- url     : https://prove2.me/submissions/182c99e5-6a1f-43c1-ae4b-8a94ab9fd8f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardShortVectorsLe
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass
namespace GlobalTheory.Mass
theorem _root_.solution {K : Type} [Field K] [NumberField K] (z : K) :
    ((Algebra.trace ℚ K z : ℚ) : ℝ) = ∑ τ : K →ₐ[ℚ] ℂ, (τ z).re := by
  have key := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := z)
  have hre := congrArg Complex.re key
  rw [Complex.re_sum] at hre
  rw [← hre]
  simp
end GlobalTheory.Mass
