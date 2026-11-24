-- Prove2me | solution 1 for GlobalTheory.WeilM.IsUWeilPair.isWeilPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:15:46.99745+00:00
-- url     : https://prove2.me/submissions/d9d4b16a-bf03-4f59-90cd-b5ac840fb82e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Theorems.Thm_GlobalTheory_WeilM_IsUWeilB_isWeilB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
variable (c)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]
variable [TopologicalSpace R] [TopologicalSpace E]
variable {c} [IsModuleTopology R E] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
  {κ : Type} [Fintype κ] {d : Darboux (symp c ξ JA JB) κ}
variable {χA χB : Eˣ →* Circle} {om : UG c JA × UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
namespace GlobalTheory.WeilM
namespace IsUWeilPair
theorem _root_.solution (h : IsUWeilPair c C ψ ξ JA JB d χA χB om) : IsWeilPair c C ψ ξ JA JB d χA χB om := by
  obtain ⟨h1, ⟨d', h2, h3⟩, -⟩ := h
  exact ⟨h1.isWeilB, d', h2, h3.isWeilB⟩
end IsUWeilPair
end GlobalTheory.WeilM
