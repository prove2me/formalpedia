-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.weilPair_one_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:38.470306+00:00
-- url     : https://prove2.me/submissions/46711628-8016-40da-98f7-c3281637dd20

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
theorem _root_.solution (μ η : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (g : GL (Fin r) F)
    (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) F → ℂ) :
    weilPair μ η nrm g 1 Φ = omegaS (μ * η) nrm g Φ := by
  funext x
  simp [weilPair, omegaS]
end GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
