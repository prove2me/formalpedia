-- Prove2me | solution 1 for GlobalTheory.WeilM.IsUWeilB.isWeilB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:52.423699+00:00
-- url     : https://prove2.me/submissions/38c36f17-42e0-493e-9d07-44322cda219c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff

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
namespace GlobalTheory.WeilM
namespace IsUWeilB
theorem _root_.solution {χ : Eˣ →* Circle} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUWeilB c C ψ ξ JA JB d χ om) : IsWeilB c C ψ ξ JA JB d χ om := by
  obtain ⟨h1, dd, omd, h2, ⟨-, h3, h4⟩, h5⟩ := h
  exact ⟨h1.toIsSplitting, dd, omd, h2, h3.toIsSplitting, h4, h5⟩
end IsUWeilB
end GlobalTheory.WeilM
