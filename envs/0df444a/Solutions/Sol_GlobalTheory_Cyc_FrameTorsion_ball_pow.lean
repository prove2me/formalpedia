-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.ball_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:54.028465+00:00
-- url     : https://prove2.me/submissions/5dce5c14-3dce-45df-9b1b-5da51933da21

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
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_norm_l_lt
import Theorems.Thm_GlobalTheory_CycEigen_norm_l_lt
import Theorems.Thm_GlobalTheory_TateDecomp_norm_l_lt


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
theorem _root_.solution (n : ℕ) {x : Fin r → PadicComplex l} (hx : x ∈ ball l r) :
    (l : PadicComplex l) ^ n • x ∈ ball l r := by
  intro a
  have hl1 : ‖(l : PadicComplex l)‖ ≤ 1 := le_of_lt norm_l_lt
  calc ‖((l : PadicComplex l) ^ n • x) a‖ = ‖(l : PadicComplex l)‖ ^ n * ‖x a‖ := by
        rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (norm_nonneg _) hl1) (hx a) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1
end GlobalTheory.Cyc.FrameTorsion
