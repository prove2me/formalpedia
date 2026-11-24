-- Prove2me | solution 1 for GlobalTheory.SqZero.IsAway.ker_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:27.815723+00:00
-- url     : https://prove2.me/submissions/ea066484-28e9-4c83-8526-a8cfaa42b40b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one')
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {S S' S'' T : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing S''] [Algebra R S''] [CommRing T] [Algebra R T]
open GlobalTheory.SqZero.IsAway
variable {ρ : S →ₐ[R] S'} {g : S}
namespace GlobalTheory.SqZero.IsAway
theorem _root_.solution (h : IsAway ρ g) {κ : Type} [Finite κ] {a : κ → S} (ha : ∀ i, ρ (a i) = 0) :
    ∃ N : ℕ, ∀ i, g ^ N * a i = 0 := by
  choose N hN using fun i => h.ker (ha i)
  obtain ⟨M, hM⟩ := (Set.finite_range N).bddAbove
  refine ⟨M, fun i => ?_⟩
  rw [← Nat.sub_add_cancel (hM ⟨i, rfl⟩), pow_add, mul_assoc, hN, mul_zero]
end GlobalTheory.SqZero.IsAway
