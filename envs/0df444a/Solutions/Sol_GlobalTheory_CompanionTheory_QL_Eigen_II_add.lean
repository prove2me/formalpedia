-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Eigen.II_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:55:15.1952+00:00
-- url     : https://prove2.me/submissions/92028c20-7ab6-4a18-adac-bb38fdae66fc

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
theorem _root_.solution {O : Subring F} {ϖ : F} {a b : ℕ} {X Y : Matrix (Fin a) (Fin b) F}
    (hX : X ∈ IIset O ϖ) (hY : Y ∈ IIset O ϖ) : X + Y ∈ IIset O ϖ := fun i j => by
  obtain ⟨o, ho, e⟩ := hX i j
  obtain ⟨p, hp, f⟩ := hY i j
  exact ⟨o + p, O.add_mem ho hp, by rw [Matrix.add_apply, e, f, mul_add]⟩
end GlobalTheory.CompanionTheory.QL.Eigen
