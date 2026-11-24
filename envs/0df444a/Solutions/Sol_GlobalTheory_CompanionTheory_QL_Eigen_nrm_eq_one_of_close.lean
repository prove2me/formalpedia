-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Eigen.nrm_eq_one_of_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:58:59.889717+00:00
-- url     : https://prove2.me/submissions/1599bdfb-4e1d-40b7-a59b-1e1a4911152f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicTestFunctionEquivariant

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
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.Eigen
theorem _root_.solution {nrm : AbsoluteValue F ℝ}
    (hna : ∀ x y : F, nrm (x + y) ≤ max (nrm x) (nrm y)) {u v : F} (hv : nrm v = 1)
    (h : nrm (u - v) < 1) : nrm u = 1 := by
  apply le_antisymm
  · have := hna (u - v) v
    rw [sub_add_cancel, hv] at this
    exact this.trans (max_le h.le le_rfl)
  · have := hna u (v - u)
    rw [add_sub_cancel, hv, nrm.map_sub v u] at this
    rcases le_max_iff.1 this with h' | h'
    · exact h'
    · exact absurd h (not_lt.2 h')
end GlobalTheory.CompanionTheory.QL.Eigen
