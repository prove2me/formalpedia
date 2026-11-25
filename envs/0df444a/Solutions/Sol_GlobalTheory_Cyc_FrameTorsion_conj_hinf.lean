-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.conj_hinf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:01:51.962595+00:00
-- url     : https://prove2.me/submissions/bed609d9-bf49-4f6c-8867-c5dff6282caf

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
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_hinf_le_gj
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_gj_le
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_chi_hinf
import Theorems.Thm_GlobalTheory_CycEigen_gj_le
import Theorems.Thm_GlobalTheory_CycEigen_hinf_le_gj
import Theorems.Thm_GlobalTheory_Cyc_cyc_basic


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
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.FrameTorsion
theorem _root_.solution {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) (s : ℕ) {g h : GQ l}
    (hg : g ∈ Gj K s) (hh : h ∈ Hinf K) : g⁻¹ * h * g ∈ Hinf K := by
  have hg0 : g ∈ (K0 K).fixingSubgroup := gj_le K s hg
  have hh0 : h ∈ (K0 K).fixingSubgroup := gj_le K 0 (hinf_le_gj K 0 hh)
  have hx0 : g⁻¹ * h * g ∈ (K0 K).fixingSubgroup :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg0) hh0) hg0
  rw [((cyc_basic l χ hχ).2.2 K _ hx0).2]
  rw [map_mul, map_mul, chi_hinf hχ K hh, mul_one, map_inv, inv_mul_cancel]
end GlobalTheory.Cyc.FrameTorsion
