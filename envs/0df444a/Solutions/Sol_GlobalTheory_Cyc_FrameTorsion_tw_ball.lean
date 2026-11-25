-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.tw_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:42:18.818394+00:00
-- url     : https://prove2.me/submissions/2bd598c5-4a2f-49d5-a696-cd9d9198bef6

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
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_norm_chiC
import Theorems.Thm_GlobalTheory_CycEigen_norm_chiC


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
variable {K : FinExt l} {m : ℕ} {g : GQ l}
namespace GlobalTheory.Cyc.FrameTorsion
theorem _root_.solution (ha : IsActC act) (hχ : IsCyc χ) (hU : Frame χ K m U g) {σ : GQ l}
    (hσ : σ ∈ Gj K m) {x : Fin r → PadicComplex l} (hx : x ∈ ball l r) :
    twAct act χ i U σ x ∈ ball l r := by
  intro a
  have hU1 : ∀ b, ‖U σ a b‖ ≤ 1 := fun b => (hU.2.2.1 σ hσ a b).2
  have hs : ‖∑ b, U σ a b * act σ (x b)‖ ≤ 1 := by
    refine Finset.sum_induction _ (fun z : PadicComplex l => ‖z‖ ≤ 1) ?_ ?_ ?_
    · intro u v hu hv
      exact (IsUltrametricDist.norm_add_le_max u v).trans (max_le hu hv)
    · rw [norm_zero]
      exact zero_le_one
    · intro b _
      rw [norm_mul, ha.2]
      exact mul_le_one₀ (hU1 b) (norm_nonneg _) (hx b)
  have e : twAct act χ i U σ x a = chiC χ i σ * ∑ b, U σ a b * act σ (x b) := by
    simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  rw [e, norm_mul, norm_chiC hχ, one_mul]
  exact hs
end GlobalTheory.Cyc.FrameTorsion
