-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Eigen.extendedCharacter_congr_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:55:21.432483+00:00
-- url     : https://prove2.me/submissions/35782d57-0c2e-42c5-9264-518de44d8602

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicTestFunctionEquivariant
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_unramifiedCharExt_mul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Eigen
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.Eigen
theorem _root_.solution (nrm : AbsoluteValue F ℝ) (δ : Fˣ →* ℂˣ)
    (tame : ∀ x : Fˣ, nrm ((x : F) - 1) < 1 → δ x = 1) {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : nrm (u - v) < nrm v) : chi0 δ u = chi0 δ v := by
  have hw : u / v ≠ 0 := div_ne_zero hu hv
  have h1 : chi0 δ (u / v) = 1 := by
    simp only [chi0, dif_neg hw]
    have : δ (Units.mk0 (u / v) hw) = 1 := by
      apply tame
      have e : ((Units.mk0 (u / v) hw : Fˣ) : F) - 1 = (u - v) / v := by
        simp only [Units.val_mk0]; field_simp
      rw [e, map_div₀]
      exact (div_lt_one (nrm.pos hv)).2 h
    rw [this]; rfl
  have h2 : u = (u / v) * v := by field_simp
  calc chi0 δ u = chi0 δ ((u / v) * v) := by rw [← h2]
    _ = chi0 δ v := by rw [unramifiedCharExt_mul δ hw hv, h1, one_mul]
end GlobalTheory.CompanionTheory.QL.Eigen
