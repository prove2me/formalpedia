-- Prove2me | solution 1 for GlobalTheory.HermClass.exists_finite_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:21.005354+00:00
-- url     : https://prove2.me/submissions/eea24d30-1704-4267-8684-107c21f67e9a

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteOrthogonalLengths_208b36ca428fb8e7
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteRepresentatives_c0b95eec68dc9003

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField
namespace GlobalTheory.HermClass
theorem _root_.solution {α : Type*} {β : Type*} (f : α → β)
    (hf : (Set.range f).Finite) : ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, f s = f a := by
  classical
  have : Finite (Set.range f) := hf.to_subtype
  refine ⟨Set.range (fun b : Set.range f => b.2.choose), Set.finite_range _, fun a => ?_⟩
  exact ⟨(⟨f a, a, rfl⟩ : Set.range f).2.choose, ⟨⟨f a, a, rfl⟩, rfl⟩,
    (⟨f a, a, rfl⟩ : Set.range f).2.choose_spec⟩
end GlobalTheory.HermClass
