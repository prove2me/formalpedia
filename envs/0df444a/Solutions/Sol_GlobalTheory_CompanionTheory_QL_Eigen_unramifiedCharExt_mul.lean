-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Eigen.unramifiedCharExt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:36.095544+00:00
-- url     : https://prove2.me/submissions/1ef2f61f-5afb-4557-b3d4-4899ffeaed2c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicTestFunctionEquivariant
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
theorem _root_.solution (δ : Fˣ →* ℂˣ) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    chi0 δ (x * y) = chi0 δ x * chi0 δ y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  simp only [chi0, dif_neg hx, dif_neg hy, dif_neg hxy]
  rw [show Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy from Units.ext rfl, map_mul,
    Units.val_mul]
end GlobalTheory.CompanionTheory.QL.Eigen
