-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.VolK.red_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:49.284907+00:00
-- url     : https://prove2.me/submissions/c27449ea-b4d5-434c-b274-a780299abbe2

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatrices
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
theorem _root_.solution {x : F} (h : x ∈ 𝒪[F]) : red x = IsLocalRing.residue 𝒪[F] ⟨x, h⟩ := by
  simp [red, h]
end GlobalTheory.CompanionTheory.QL.VolK
