-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.twHom_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:56.477731+00:00
-- url     : https://prove2.me/submissions/ad849889-2294-453b-84c8-4419ecc50032

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_act_eq_of_mem_intC
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_chiC_mem_intC
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_twHom_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Filter Topology
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Procyclic
variable {l : ℕ} [Fact l.Prime]
variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
variable {K : FinExt l} {m r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}
namespace GlobalTheory.Cyc.Procyclic
theorem _root_.solution (hact : IsActC act) (hχ : IsCyc χ) (hF : Frame χ K m U g) (i : ℤ) :
    ∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, ∀ y,
      twHom act χ i U (σ * τ) y = twHom act χ i U σ (twHom act χ i U τ y) := by
  intro σ hσ τ hτ y
  ext a
  have h1 : chiC χ i (σ * τ) = chiC χ i σ * chiC χ i τ := by
    simp only [chiC, map_mul, mul_zpow, Units.val_mul]
  have h2 : act σ (chiC χ i τ) = chiC χ i τ :=
    act_eq_of_mem_intC hact hσ (chiC_mem_intC hχ (Ks K m) i τ)
  have h3 : ∀ a b, act σ (U τ a b) = U τ a b := fun a b =>
    act_eq_of_mem_intC hact hσ (hF.2.2.1 τ hτ a b)
  simp only [twHom_apply, h1, hF.2.2.2.1 σ hσ τ hτ, Matrix.mul_apply, map_mul, map_sum, h2, h3,
    RingAut.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring
end GlobalTheory.Cyc.Procyclic
