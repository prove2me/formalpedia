-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.PsiVolume.blocks_mul_pEl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:37:25.176744+00:00
-- url     : https://prove2.me/submissions/ca5853df-b764-440f-92d0-131d5faf6836

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_WeilIntegralUnipotentLeviFormula
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CompanionTheory_QLB_bAA_reindex
import Theorems.Thm_GlobalTheory_CompanionTheory_QLB_bAD_reindex
import Theorems.Thm_GlobalTheory_CompanionTheory_QLB_bDA_reindex
import Theorems.Thm_GlobalTheory_CompanionTheory_QLB_bDD_reindex
import Theorems.Thm_GlobalTheory_CompanionTheory_QLB_pEl_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_BlockMul_blocks_mul
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
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.PsiVolume
theorem _root_.solution {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F)
    (B : Matrix (Fin r) (Fin c) F) (m : GL (Fin c) F) :
    bAA (x * (pEl 1 B m : GL (Fin (r + c)) F).val) = bAA x ∧
    bDA (x * (pEl 1 B m : GL (Fin (r + c)) F).val) = bDA x ∧
    bAD (x * (pEl 1 B m : GL (Fin (r + c)) F).val) =
      bAA x * B + bAD x * (m : Matrix (Fin c) (Fin c) F) ∧
    bDD (x * (pEl 1 B m : GL (Fin (r + c)) F).val) =
      bDA x * B + bDD x * (m : Matrix (Fin c) (Fin c) F) := by
  obtain ⟨h1, h2, h3, h4⟩ := BlockMul.blocks_mul r d c c x (pEl 1 B m : GL (Fin (r + c)) F).val
  have a1 : bAA (pEl 1 B m : GL (Fin (r + c)) F).val = 1 := by
    rw [QLB.pEl_coe, QLB.bAA_reindex]; rfl
  have a2 : bAD (pEl 1 B m : GL (Fin (r + c)) F).val = B := by
    rw [QLB.pEl_coe, QLB.bAD_reindex]
  have a3 : bDA (pEl 1 B m : GL (Fin (r + c)) F).val = 0 := by
    rw [QLB.pEl_coe, QLB.bDA_reindex]
  have a4 : bDD (pEl 1 B m : GL (Fin (r + c)) F).val = (m : Matrix (Fin c) (Fin c) F) := by
    rw [QLB.pEl_coe, QLB.bDD_reindex]
  rw [a1, a3] at h1 h3
  rw [a2, a4] at h2 h4
  refine ⟨?_, ?_, h2, h4⟩
  · rw [h1]; simp
  · rw [h3]; simp
end GlobalTheory.CompanionTheory.QL.PsiVolume
