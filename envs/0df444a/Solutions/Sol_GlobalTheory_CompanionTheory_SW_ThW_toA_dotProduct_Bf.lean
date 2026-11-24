-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.toA_dotProduct_Bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:35:02.203075+00:00
-- url     : https://prove2.me/submissions/b14835a9-70e8-40e3-bcc2-46c0505d3976

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicCharacterExponentialFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker
namespace GlobalTheory.CompanionTheory.SW.ThW
theorem _root_.solution {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (B : Matrix ι ι F) (a y : ι → F) :
    toA a ⬝ᵥ (Bf B *ᵥ toA y) = algebraMap F (A F) (a ⬝ᵥ (B *ᵥ y)) := by
  simp only [dotProduct, mulVec, toA, Bf, map_sum, map_mul, Matrix.map_apply]
end GlobalTheory.CompanionTheory.SW.ThW
