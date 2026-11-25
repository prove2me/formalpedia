-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.tw_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:17:06.013015+00:00
-- url     : https://prove2.me/submissions/95df6f07-a1c6-4c66-836d-15a2e09afab8

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
theorem _root_.solution (σ : GQ l) (x y : Fin r → PadicComplex l) :
    twAct act χ i U σ (x - y) = twAct act χ i U σ x - twAct act χ i U σ y := by
  have hv : (fun a => act σ ((x - y) a)) = (fun a => act σ (x a)) - (fun a => act σ (y a)) := by
    funext a
    simp only [Pi.sub_apply, map_sub]
  simp only [twAct, hv, Matrix.mulVec_sub, smul_sub]
end GlobalTheory.Cyc.FrameTorsion
