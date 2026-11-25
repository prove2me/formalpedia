-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.tw_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:17:03.862174+00:00
-- url     : https://prove2.me/submissions/ae565cfa-27ea-4a7e-a875-91a835c7e4b3

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
theorem _root_.solution (σ : GQ l) (n : ℕ) (x : Fin r → PadicComplex l) :
    twAct act χ i U σ ((l : PadicComplex l) ^ n • x)
      = (l : PadicComplex l) ^ n • twAct act χ i U σ x := by
  have hl : ∀ z : PadicComplex l, act σ ((l : PadicComplex l) ^ n * z) = (l : PadicComplex l) ^ n * act σ z := by
    intro z
    rw [map_mul, map_pow, map_natCast]
  have hv : (fun a => act σ (((l : PadicComplex l) ^ n • x) a)) = (l : PadicComplex l) ^ n • (fun a => act σ (x a)) := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, hl]
  simp only [twAct, hv, Matrix.mulVec_smul, smul_comm (chiC χ i σ)]
end GlobalTheory.Cyc.FrameTorsion
