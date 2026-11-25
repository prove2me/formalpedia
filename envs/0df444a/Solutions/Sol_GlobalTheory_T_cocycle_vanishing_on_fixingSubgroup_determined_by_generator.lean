-- Prove2me | solution 1 for GlobalTheory.T.cocycle_vanishing_on_fixingSubgroup_determined_by_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:59:59.377744+00:00
-- url     : https://prove2.me/submissions/ae600414-a104-4560-be37-a6a75ff36368

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGeneStatement
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_procyclic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ i : ℤ, (∀ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) Set.univ c → (∀ h ∈ Hinf K, c h = 0) → c g = 0 → ∀ σ ∈ Gj K m, c σ = 0) ∧ ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Ohat K) → ∃ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) {y | ∀ a, y a ∈ Ohat K} c ∧ (∀ h ∈ Hinf K, c h = 0) ∧ c g = w := by
  first | exact @GlobalTheory.Cyc.Procyclic.procyclic | exact GlobalTheory.Cyc.Procyclic.procyclic | (intros; apply GlobalTheory.Cyc.Procyclic.procyclic <;> assumption)
end _root_.GlobalTheory.T
