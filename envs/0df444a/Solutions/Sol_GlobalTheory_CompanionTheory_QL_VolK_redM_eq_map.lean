-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.VolK.redM_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:44:45.631354+00:00
-- url     : https://prove2.me/submissions/39c20701-8cbe-41c6-9372-7ee099597682

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatrices
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_VolK_red_of_mem
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.VolK
variable {F : Type} [Field F] [ValuativeRel F]
namespace GlobalTheory.CompanionTheory.QL.VolK
theorem _root_.solution {r : ℕ} {x : Matrix (Fin r) (Fin r) F} (h : x ∈ intMat 𝒪[F] r r) :
    redM x = (IsLocalRing.residue 𝒪[F]).mapMatrix (toO h) := by
  ext i j
  simp [redM, toO, red_of_mem (h i j)]
end GlobalTheory.CompanionTheory.QL.VolK
