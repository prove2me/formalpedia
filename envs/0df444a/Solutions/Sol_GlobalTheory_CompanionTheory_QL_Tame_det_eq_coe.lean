-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Tame.det_eq_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:39.398726+00:00
-- url     : https://prove2.me/submissions/dc9532b4-f102-497b-88fa-826264c63942

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusProperties

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Tame
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.Tame
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring F) (X : Matrix ι ι F)
    (hX : ∀ i j, X i j ∈ O) :
    X.det = ((Matrix.det (fun i j => (⟨X i j, hX i j⟩ : O)) : O) : F) := by
  have h := RingHom.map_det O.subtype (fun i j => (⟨X i j, hX i j⟩ : O))
  have h2 : O.subtype.mapMatrix (fun i j => (⟨X i j, hX i j⟩ : O) : Matrix ι ι O) = X := by
    ext i j; rfl
  rw [h2] at h
  exact h.symm
end GlobalTheory.CompanionTheory.QL.Tame
