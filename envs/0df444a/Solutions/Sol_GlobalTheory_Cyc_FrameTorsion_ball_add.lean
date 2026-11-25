-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.ball_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:24:49.53205+00:00
-- url     : https://prove2.me/submissions/2e5c0f64-c58f-49d1-b367-7d62559626fd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTateMaximalIdealKillsFirstCohomologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGeneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGeneratorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleTwistCoboundaryOnBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FrameTorsion
variable {l : ℕ} [Fact l.Prime] {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
  {χ : GQ l →* ℚ_[l]ˣ} {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {i : ℤ}
namespace GlobalTheory.Cyc.FrameTorsion
theorem _root_.solution {x y : Fin r → PadicComplex l} (hx : x ∈ ball l r) (hy : y ∈ ball l r) :
    x + y ∈ ball l r := by
  intro a
  calc ‖(x + y) a‖ = ‖x a + y a‖ := rfl
    _ ≤ max ‖x a‖ ‖y a‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (hx a) (hy a)
end GlobalTheory.Cyc.FrameTorsion
