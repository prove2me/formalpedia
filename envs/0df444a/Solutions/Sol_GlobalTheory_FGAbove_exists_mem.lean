-- Prove2me | solution 1 for GlobalTheory.FGAbove.exists_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:15:31.740221+00:00
-- url     : https://prove2.me/submissions/7c7e2bbd-1625-4985-b94c-17f45cacd4ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C]
variable {R₀ : Subalgebra k C}
namespace GlobalTheory
namespace FGAbove
theorem _root_.solution (h : R₀.FG) (x : C) : ∃ R : FGAbove R₀, x ∈ R.1 :=
  ⟨⟨R₀ ⊔ Algebra.adjoin k {x}, h.sup (Subalgebra.fg_def.2 ⟨{x}, Set.finite_singleton x, rfl⟩), le_sup_left⟩,
    (le_sup_right : Algebra.adjoin k {x} ≤ _) (Algebra.self_mem_adjoin_singleton k x)⟩
end FGAbove
end GlobalTheory
