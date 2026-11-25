-- Prove2me | solution 1 for GlobalTheory.T.locally_trivial_unit_cocycle_faithfully_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:23:42.552113+00:00
-- url     : https://prove2.me/submissions/30d7403e-a4d3-4780-96d8-22b492a689d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlatStatement
import Theorems.Thm_GlobalTheory_UnitCocycle_exists_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R B C D : CommRingCat.{0}) (f : R ⟶ B) (j₁ j₂ : B ⟶ C) (d₁₂ d₂₃ d₁₃ : C ⟶ D), IsPushout f f j₁ j₂ → IsPushout j₂ j₁ d₁₂ d₂₃ → j₁ ≫ d₁₃ = j₁ ≫ d₁₂ → j₂ ≫ d₁₃ = j₂ ≫ d₂₃ → f.hom.FaithfullyFlat → ∀ c : Cˣ, d₁₃.hom (c : C) = d₁₂.hom (c : C) * d₂₃.hom (c : C) → ∀ P : Ideal R, P.IsPrime → ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = f.hom s ∧ j₂.hom x = (c : C) * j₁.hom x := by
  first | exact @GlobalTheory.UnitCocycle.exists_local | exact GlobalTheory.UnitCocycle.exists_local | (intros; apply GlobalTheory.UnitCocycle.exists_local <;> assumption)
end _root_.GlobalTheory.T
