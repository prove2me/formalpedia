-- Prove2me | solution 1 for GlobalTheory.RankFibreKer.continuousOn_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:23:29.511694+00:00
-- url     : https://prove2.me/submissions/3d41b2e9-6b27-429c-97f4-9369f914a2ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoinvariantOfLocallyConstantTwistStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitalIntegralVanishesOfFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankIffNonzeroMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFirstMaximalMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionInverseIntoSliceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FirstMaximalMinorLocallyConstantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SliceStabilizerTrivialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSliceSectionMeasureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSliceSectionIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SliceSectionHaarDecompositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactCoveredByOpenCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarIntegralOverCosetRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreZeroMemCoinvariants
import Theorems.Thm_GlobalTheory_RankFibreKer_sec_val
import Theorems.Thm_GlobalTheory_T_exists_first_maximal_minor
import Theorems.Thm_GlobalTheory_T_first_maximal_minor_locally_constant
import Theorems.Thm_GlobalTheory_T_full_rank_iff_nonzero_minor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.RankFibreKer
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RankFibreKer
theorem _root_.solution {a d : ℕ} : ContinuousOn (sec (k := k) (a := a) (d := d)) {Y | Y.rank = a} := by
  intro Y hY
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_first_maximal_minor k a d Y ((GlobalTheory.T.full_rank_iff_nonzero_minor k a d Y).1 hY)
  rw [isEmbedding_val_GL.isInducing.continuousWithinAt_iff]
  refine ContinuousAt.continuousWithinAt ?_
  have hc : Continuous fun Y : Matrix (Fin a) (Fin d) k => Y.submatrix id J :=
    (continuous_id.matrix_submatrix id J)
  refine hc.continuousAt.congr ?_
  filter_upwards [GlobalTheory.T.first_maximal_minor_locally_constant k a d Y J hJ] with Y' hY'
  exact (sec_val hY').symm
end GlobalTheory.RankFibreKer
