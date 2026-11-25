-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.tw_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:18:50.853186+00:00
-- url     : https://prove2.me/submissions/30f8322b-9738-4e14-bfe6-b53083a44e4a

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
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_act_inC
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_act_algebraMap
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_chiC_mul
import Theorems.Thm_GlobalTheory_CycEigen_act_inC


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
theorem _root_.solution (ha : IsActC act) (hU : Frame χ K m U g) {σ τ : GQ l} (hσ : σ ∈ Gj K m)
    (hτ : τ ∈ Gj K m) (x : Fin r → PadicComplex l) :
    twAct act χ i U (σ * τ) x = twAct act χ i U σ (twAct act χ i U τ x) := by
  have hσF : σ ∈ (Ks K m).fixingSubgroup := hσ
  have hfix : ∀ a b, act σ (U τ a b) = U τ a b := fun a b => act_inC ha hσF (hU.2.2.1 τ hτ a b).1
  have hc : act σ (chiC χ i τ) = chiC χ i τ := act_algebraMap ha σ _
  have hv : (fun a => act σ (twAct act χ i U τ x a))
      = chiC χ i τ • (U τ).mulVec (fun b => act σ (act τ (x b))) := by
    funext a
    simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, map_mul, map_sum, hfix, hc]
  have hστ : (fun b => act (σ * τ) (x b)) = fun b => act σ (act τ (x b)) := by
    funext b
    rw [map_mul]
    rfl
  show chiC χ i (σ * τ) • (U (σ * τ)).mulVec (fun b => act (σ * τ) (x b))
    = chiC χ i σ • (U σ).mulVec (fun a => act σ (twAct act χ i U τ x a))
  rw [hv, hστ, chiC_mul, hU.2.2.2.1 σ hσ τ hτ, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, smul_smul]
end GlobalTheory.Cyc.FrameTorsion
