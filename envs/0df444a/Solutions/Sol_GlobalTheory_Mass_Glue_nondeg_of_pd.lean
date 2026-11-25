-- Prove2me | solution 1 for GlobalTheory.Mass.Glue.nondeg_of_pd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:06:40.306871+00:00
-- url     : https://prove2.me/submissions/5ba2b38c-df4e-48d0-a0e5-d4263c9cc1d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedSubspaceComplement

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Glue
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.Glue
theorem _root_.solution [NumberField K] (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  constructor
  · intro x hx
    by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this
  · intro x hx
    by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this
end GlobalTheory.Mass.Glue
