-- Prove2me | solution 1 for GlobalTheory.SingleBlock.measurableSet_suppSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:35.004685+00:00
-- url     : https://prove2.me/submissions/e5e94450-4c60-4d9d-9cf0-b05f075934a0

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_GlobalTheory_SingleBlock_measurableSet_Jset
import Theorems.Thm_P2M_GlobalTheory_SingleBlock_measurable_toRows__1516c29dbd57
import Theorems.Thm_P2M_GlobalTheory_SingleBlock_measurable_toRows__be0362a1a7c9
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_meas_ii


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {r t : ℕ}
  {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
variable [MeasurableSpace F] [BorelSpace F]
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hO : IsOpen (O : Set F)) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) [Finite (kF O ϖ hϖ)] (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) :
    MeasurableSet (suppSet t O ϖ P) :=
  (measurable_toRows₁ (measurableSet_Jset hO hϖ hϖ0 hloc hKP hP)).inter
    (measurable_toRows₂ (Vol.meas_ii O hO ϖ hϖ0 t r))
end GlobalTheory.SingleBlock
