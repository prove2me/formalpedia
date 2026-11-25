-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.continuousOn_twHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:32:33.352802+00:00
-- url     : https://prove2.me/submissions/33fa117c-51ea-40e8-abc1-468e6900bd23

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_continuous_chiC
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_twHom_apply
import Theorems.Thm_GlobalTheory_Cyc_IsActC_continuous_orbit


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
theorem _root_.solution (hact : IsActC act) (hχ : IsCyc χ) (hF : Frame χ K m U g) (i : ℤ)
    (y : Fin r → PadicComplex l) : ContinuousOn (fun σ => twHom act χ i U σ y) (Gj K m) := by
  refine continuousOn_pi.2 fun a => ?_
  simp only [twHom_apply]
  exact (continuous_chiC hχ i).continuousOn.mul (continuousOn_finsetSum _ fun b _ =>
    (hF.2.1 a b).mul (IsActC.continuous_orbit l act hact _).continuousOn)
end GlobalTheory.Cyc.Procyclic
