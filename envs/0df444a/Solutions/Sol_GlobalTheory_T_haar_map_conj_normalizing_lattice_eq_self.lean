-- Prove2me | solution 1 for GlobalTheory.T.haar_map_conj_normalizing_lattice_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:00:07.851007+00:00
-- url     : https://prove2.me/submissions/49f47d3b-73c9-429e-8cb3-54556d94261a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMapConjNormalizingLatticeEqSelf
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMapConjNormalizingLatticeEqSelfStatement
import Theorems.Thm_GlobalTheory_UnfoldNormal_map_conj_eq_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Function
open scoped Pointwise
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) := by
  first | exact @GlobalTheory.UnfoldNormal.map_conj_eq_self | exact GlobalTheory.UnfoldNormal.map_conj_eq_self | (intros; apply GlobalTheory.UnfoldNormal.map_conj_eq_self <;> assumption)
end _root_.GlobalTheory.T
