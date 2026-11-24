-- Prove2me | solution 1 for GlobalTheory.JR.exists_selfDual_of_dual_subgroups
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:19:54.941691+00:00
-- url     : https://prove2.me/submissions/db60a922-f711-4afc-add3-0276ad5bf065

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Theorems.Thm_GlobalTheory_JR_AbsInv_exists_selfDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open MeasureTheory Filter Topology Pointwise
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [MeasurableSpace V] [BorelSpace V]
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
namespace _root_.GlobalTheory.JR
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (B : V → V → ℂ), Continuous (fun p : V × V => B p.1 p.2) → (∀ x y, B x y = B y x) → (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ y, B 0 y = 1) → (∀ U ∈ 𝓝 (0 : V), ∃ M N : AddSubgroup V, (M : Set V) ⊆ U ∧ IsOpen (M : Set V) ∧ IsCompact (M : Set V) ∧ IsOpen (N : Set V) ∧ IsCompact (N : Set V) ∧ (∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1) ∧ (∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)) → ∃ μ : MeasureTheory.Measure V, _root_.GlobalTheory.JR.SelfDual μ B := by
  intro V _ _ _ _ _ _ _ _ B hB hs ha _ H
  exact _root_.GlobalTheory.JR.AbsInv.exists_selfDual B hB hs ha H
end _root_.GlobalTheory.JR
