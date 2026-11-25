-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.PsiVolume.unramifiedCharExt_inv_mul_conj_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:25.391357+00:00
-- url     : https://prove2.me/submissions/1dfa3e25-4fed-4bd9-8dd1-d5beb9d856a4

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_WeilIntegralUnipotentLeviFormula
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
theorem _root_.solution {δ : Fˣ →* ℂˣ} (hδ : ∀ x, ‖((δ x : ℂˣ) : ℂ)‖ = 1) {a : F} (ha : a ≠ 0) :
    (chi0 δ a)⁻¹ * conj ((chi0 δ a)⁻¹) = 1 := by
  have hn : ‖chi0 δ a‖ = 1 := by simp [chi0, ha, hδ]
  have hi : ‖(chi0 δ a)⁻¹‖ = 1 := by rw [norm_inv, hn, inv_one]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hi]; simp
end GlobalTheory.CompanionTheory.QL.PsiVolume
