-- Prove2me | solution 1 for GlobalTheory.Cyc.AveragingRankOne.average
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:23.107571+00:00
-- url     : https://prove2.me/submissions/4f5bf25a-31e0-490a-8ab6-3849972561eb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerTraceAlmostSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsRest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTateMaximalIdealKillsFirstCohomology
import Theorems.Thm_GlobalTheory_PermutationExistence_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.AveragingRankOne
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.AveragingRankOne
theorem _root_.solution {G C : Type*} [Group G] [NormedField C] [IsUltrametricDist C]
    (act : G →* (C ≃+* C)) (hn : ∀ g y, ‖act g y‖ = ‖y‖) (H V : Subgroup G) (S : Finset G)
    (hS : ∀ s ∈ S, s ∈ H) (hS' : ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ V)
    (a b : C) (hb : ‖b‖ ≤ 1) (hbV : ∀ g ∈ V, act g b = b) (hab : ∑ s ∈ S, act s b = a)
    (c : G → C) (hc : ∀ g ∈ H, ∀ h ∈ H, c (g * h) = c g + act g (c h))
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε : 0 ≤ ε) (ht : ∀ g ∈ H, ‖c g‖ ≤ t)
    (hV : ∀ g ∈ H, g ∈ V → ‖c g‖ ≤ ε) :
    ∃ x : C, ‖x‖ ≤ t ∧ ∀ h ∈ H, ‖a * c h - (act h x - x)‖ ≤ ε := by
  first
  | exact @_root_.GlobalTheory.PermutationExistence.main
  | exact _root_.GlobalTheory.PermutationExistence.main
  | (apply _root_.GlobalTheory.PermutationExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PermutationExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PermutationExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PermutationExistence.main ..)
end GlobalTheory.Cyc.AveragingRankOne
