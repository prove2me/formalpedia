-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.tw_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:13:51.764063+00:00
-- url     : https://prove2.me/submissions/52f22c47-d5c0-41f9-acdd-29a8161d3395

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
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_continuous_chiC
import Theorems.Thm_GlobalTheory_Cyc_IsActC_continuous_orbit
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_continuous_chiC


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
theorem _root_.solution (ha : IsActC act) (hχ : IsCyc χ) (hU : Frame χ K m U g)
    (x : Fin r → PadicComplex l) : ContinuousOn (fun σ => twAct act χ i U σ x) (Gj K m) := by
  apply continuousOn_pi.2
  intro a
  have h1 : ∀ b, ContinuousOn (fun σ => U σ a b * act σ (x b)) (Gj K m) :=
    fun b => (hU.2.1 a b).mul (IsActC.continuous_orbit l act ha (x b)).continuousOn
  have h2 : ContinuousOn (fun σ => ∑ b, U σ a b * act σ (x b)) (Gj K m) :=
    continuousOn_finsetSum _ (fun b _ => h1 b)
  have h3 : ContinuousOn (fun σ => chiC χ i σ * ∑ b, U σ a b * act σ (x b)) (Gj K m) :=
    (continuous_chiC hχ i).continuousOn.mul h2
  refine h3.congr ?_
  intro σ _
  simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
end GlobalTheory.Cyc.FrameTorsion
