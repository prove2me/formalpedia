-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.blockChar_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:37.441173+00:00
-- url     : https://prove2.me/submissions/dc673f32-5b48-4992-b720-9ac72b6a5280

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
variable {F : Type} [Field F] {r t : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
theorem _root_.solution (μ : Fˣ →* ℂˣ) (P : Subgroup (GL (Fin r) F)) (lam : P →* ℂˣ) (k : P) :
    blockChar μ P lam k = lam k * (μ (GeneralLinearGroup.det (k : GL (Fin r) F)))⁻¹ := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
