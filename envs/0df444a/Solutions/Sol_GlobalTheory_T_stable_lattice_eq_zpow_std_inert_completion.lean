-- Prove2me | solution 1 for GlobalTheory.T.stable_lattice_eq_zpow_std_inert_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:15:35.498075+00:00
-- url     : https://prove2.me/submissions/bc78625d-0047-48f6-bb26-a4f129a779ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableLatticeEqZpowStdInertCompletion
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableLatticeEqZpowStdInertCompletionStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_LocLatInert_stable_lattice_eq_zpow_std


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (σ : P.adicCompletion E →+* P.adicCompletion E), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) → ∀ (ϖ : P.adicCompletion E), Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ (n : ℕ) (L : AddSubgroup (Fin n → P.adicCompletion E)) (N : P.adicCompletion E), N ≠ 0 → (∀ a : P.adicCompletion E, Valued.v a ≤ 1 → ∀ w ∈ L, a • w ∈ L) → (∀ w : Fin n → P.adicCompletion E, (∀ i, Valued.v (w i) ≤ 1) → N • w ∈ L) → (∀ w ∈ L, ∀ i, Valued.v (N * w i) ≤ 1) → (∀ U : GL (Fin n) (P.adicCompletion E), U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) → (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L) → ∃ k : ℤ, ∀ w, w ∈ L ↔ ∀ i, Valued.v (ϖ ^ k * w i) ≤ 1 := by
  first | exact @GlobalTheory.LocLatInert.stable_lattice_eq_zpow_std | exact GlobalTheory.LocLatInert.stable_lattice_eq_zpow_std | (intros; apply GlobalTheory.LocLatInert.stable_lattice_eq_zpow_std <;> assumption)
end _root_.GlobalTheory.T
