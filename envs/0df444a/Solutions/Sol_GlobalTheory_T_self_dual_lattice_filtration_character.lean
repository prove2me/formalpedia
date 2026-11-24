-- Prove2me | solution 1 for GlobalTheory.T.self_dual_lattice_filtration_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:22:27.119434+00:00
-- url     : https://prove2.me/submissions/24b47f62-edc8-4248-b0e9-70014671f47e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpan
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpanStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SDPadic_exists_selfDual
import Theorems.Thm_GlobalTheory_JR_AbsInv_exists_selfDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (χ : V → V → ℂ) (L : ℤ → AddSubgroup V) (D : ℤ → AddSubgroup V), (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → (∀ x y, χ x y = χ y x) → (∀ x y, ‖χ x y‖ = 1) → Continuous (fun p : V × V => χ p.1 p.2) → (∀ n, IsOpen (L n : Set V) ∧ IsCompact (L n : Set V) ∧ IsOpen (D n : Set V) ∧ IsCompact (D n : Set V)) → Antitone L → (∀ U ∈ nhds (0 : V), ∃ n, (L n : Set V) ⊆ U) → (∀ x, ∃ n, x ∈ L n) → (∀ x, ∃ n, x ∈ D n) → (∀ n y, y ∈ D n ↔ ∀ x ∈ L n, χ x y = 1) → (∀ n x, x ∈ L n ↔ ∀ y ∈ D n, χ x y = 1) → ∃ μ : Measure V, SelfDual μ χ := by
  first | exact @GlobalTheory.CompanionTheory.SDPadic.exists_selfDual | exact GlobalTheory.CompanionTheory.SDPadic.exists_selfDual | (intros; apply GlobalTheory.CompanionTheory.SDPadic.exists_selfDual <;> assumption)
end _root_.GlobalTheory.T
