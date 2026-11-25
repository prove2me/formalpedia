-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.PsiVolume.measurableSet_IIset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:15.144803+00:00
-- url     : https://prove2.me/submissions/4091b129-fc60-4ae4-97be-28700bc1685a

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_WeilIntegralUnipotentLeviFormula
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_main
import Theorems.Thm_GlobalTheory_T_localField_topology_norm_balls
import Theorems.Thm_GlobalTheory_T_matrix_additive_haar_normalized
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.PsiVolume
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.PsiVolume
theorem _root_.solution (hLF : LF O ϖ nrm q) (t a : ℕ) :
    MeasurableSet (IIset O ϖ : Set (Matrix (Fin t) (Fin a) F)) := by
  haveI := (GlobalTheory.T.matrix_additive_haar_normalized hLF t a).1
  obtain ⟨-, -, -, hc, -, -⟩ := GlobalTheory.T.localField_topology_norm_balls hLF
  obtain ⟨-, -, -, hlt, -⟩ := NormalisedValue.main hLF
  have he : (IIset O ϖ : Set (Matrix (Fin t) (Fin a) F)) =
      ⋂ i, ⋂ j, {y : Matrix (Fin t) (Fin a) F | nrm (y i j) < 1} := by
    ext y
    simp only [IIset, Set.mem_setOf_eq, Set.mem_iInter, hlt]
  rw [he]
  refine IsOpen.measurableSet (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  exact isOpen_lt (hc.comp (continuous_id.matrix_elem i j)) continuous_const
end GlobalTheory.CompanionTheory.QL.PsiVolume
