-- Prove2me | solution 1 for GlobalTheory.SqZero.IsAway.surj_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:13.511816+00:00
-- url     : https://prove2.me/submissions/6998f0e6-ca57-43f2-a802-be229fbbd827

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
theorem _root_.solution (h : IsAway ρ g) {κ : Type} [Finite κ] (z : κ → S') :
    ∃ (N : ℕ) (a : κ → S), ∀ i, z i * ρ g ^ N = ρ (a i) := by
  choose N a hNa using fun i => h.surj (z i)
  obtain ⟨M, hM⟩ := (Set.finite_range N).bddAbove
  refine ⟨M, fun i => a i * g ^ (M - N i), fun i => ?_⟩
  rw [map_mul, ← hNa, map_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' (hM ⟨i, rfl⟩)]
end GlobalTheory.SqZero.IsAway
