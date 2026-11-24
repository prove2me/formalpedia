-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Eigen.Jset_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:45:22.843115+00:00
-- url     : https://prove2.me/submissions/fb2412cf-ca2d-4bb6-b89e-6109a46e86e5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicTestFunctionEquivariant
import Theorems.Thm_GlobalTheory_T_mem_integralGL_iff_integral_unit_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Eigen
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.Eigen
theorem _root_.solution (hLF : LF O ϖ nrm q) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    M ∈ Jset (GLint O n) ↔ M ∈ intMat O n n ∧ nrm M.det = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (GlobalTheory.T.mem_integralGL_iff_integral_unit_det hLF n g).1 hg
  · rintro ⟨h, hd⟩
    have hne : M.det ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hd; exact zero_ne_one hd
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hne, ?_, rfl⟩
    exact (GlobalTheory.T.mem_integralGL_iff_integral_unit_det hLF n _).2 ⟨h, hd⟩
end GlobalTheory.CompanionTheory.QL.Eigen
