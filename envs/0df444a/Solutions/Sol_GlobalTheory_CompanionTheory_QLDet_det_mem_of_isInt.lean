-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLDet.det_mem_of_isInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:36.866273+00:00
-- url     : https://prove2.me/submissions/fecceb93-75a8-48f3-98c1-57f5ae880521

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLDet
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QLDet
theorem _root_.solution (O : Subring F) {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsInt O M) :
    M.det ∈ O := by
  let M' : Matrix (Fin n) (Fin n) O := fun a b => ⟨M a b, h a b⟩
  have hM : M = O.subtype.mapMatrix M' := by
    ext a b
    rfl
  rw [hM, ← RingHom.map_det]
  exact (M'.det).2
end GlobalTheory.CompanionTheory.QLDet
