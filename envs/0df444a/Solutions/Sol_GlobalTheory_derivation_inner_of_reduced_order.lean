-- Prove2me | solution 1 for GlobalTheory.derivation_inner_of_reduced_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:44:44.436005+00:00
-- url     : https://prove2.me/submissions/b8e1fefc-d9d0-40c5-9efa-8127b22cf145

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_DerivationInnerOfSeparabilityElement
import Theorems.Thm_GlobalTheory_derivation_inner_of_separability_element

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O], ∃ (N : ℕ) (e : TensorProduct ℤ O O), 0 < N ∧ Algebra.TensorProduct.lmul' ℤ e = (N : O) ∧ ∀ c : O, (TensorProduct.tmul ℤ c (1 : O) - TensorProduct.tmul ℤ (1 : O) c) * e = 0) → ∀ (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (V : Type) [AddCommGroup V] [Module ℚ V] (l r : O →+* Module.End ℚ V), (∀ a b, Commute (l a) (r b)) → ∀ δ : O →+ V, (∀ a b, δ (a * b) = l b (δ a) + r a (δ b)) → ∃ v : V, ∀ a, δ a = l a v - r a v := by
  intro H O _ _ _ _ V _ _ l r hlr δ hδ
  obtain ⟨N, e, hN, he, hc⟩ := H O
  exact derivation_inner_of_separability_element O N e hN he hc V l r hlr δ hδ
end GlobalTheory
