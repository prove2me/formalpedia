-- Prove2me | solution 1 for GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:37.182717+00:00
-- url     : https://prove2.me/submissions/cfcab5ec-0293-442c-b2c1-907e807ed907

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatSweepSmoothlyInduced
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatSweepSmoothlyInducedStatement
import Theorems.Thm_GlobalTheory_SBInduced_sb_induced


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G X Y W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [AddCommGroup W] [Module ℂ W] (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) → Continuous (fun p : X × G => r p.1 p.2) → ∀ (j : Y → X), IsClosedEmbedding j → ∀ (P : Subgroup G) (K : Set G), IsCompact K → (∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) → ∀ (s : Y → P → Y), (∀ y (p : P), r (j y) p = j (s y p)) → (∀ y y' g, r (j y) g = j y' → g ∈ P) → ∀ (χ : G →* ℂˣ), IsSmoothChar χ → ∀ (σ : Representation ℂ P W) (ev : W ≃ₗ[ℂ] SB Y), (∀ (p : P) w y, (ev (σ p w)).1 y = (χ p : ℂ) * (ev w).1 (s y p)) → ∃ E : SB X ≃ₗ[ℂ] smoothPart (ind P σ), ∀ Φ g y, (ev ((E Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := by
  first | exact @GlobalTheory.SBInduced.sb_induced | exact GlobalTheory.SBInduced.sb_induced | (intros; apply GlobalTheory.SBInduced.sb_induced <;> assumption)
end _root_.GlobalTheory.T
