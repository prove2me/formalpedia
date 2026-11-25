-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.tw_hinf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:59:32.271882+00:00
-- url     : https://prove2.me/submissions/e46b8f6b-899b-4266-a818-78cd0cb674a7

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
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_chiC_hinf
import Theorems.Thm_GlobalTheory_CycEigen_chiC_hinf


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
theorem _root_.solution (hχ : IsCyc χ) (hU : Frame χ K m U g) {h : GQ l} (hh : h ∈ Hinf K)
    (x : Fin r → PadicComplex l) : twAct act χ i U h x = fun a => act h (x a) := by
  have hU1 : U h = 1 := hU.2.2.2.2.1 h hh
  rw [twAct, hU1, Matrix.one_mulVec, chiC_hinf hχ K i hh, one_smul]
end GlobalTheory.Cyc.FrameTorsion
