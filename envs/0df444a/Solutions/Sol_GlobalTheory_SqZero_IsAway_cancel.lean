-- Prove2me | solution 1 for GlobalTheory.SqZero.IsAway.cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:13.505558+00:00
-- url     : https://prove2.me/submissions/7da61e5f-2edb-42f3-bc34-390da0e9a6c1

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
theorem _root_.solution (h : IsAway ρ g) {ρ' : S' →ₐ[R] S''} {g' : S}
    (h' : IsAway (ρ'.comp ρ) (g * g')) : IsAway ρ' (ρ g') := by
  have hu := h'.unit
  rw [map_mul] at hu
  obtain ⟨w, hw⟩ := h.unit.exists_right_inv
  refine (isAway_iff _ _).2 ⟨isUnit_of_mul_isUnit_right hu, fun z => ?_, fun b hb => ?_⟩
  · obtain ⟨N, a, ha⟩ := h'.surj z
    refine ⟨N, ρ a * w ^ N, ?_⟩
    simp only [AlgHom.comp_apply, map_mul, map_pow] at ha ⊢
    have hw' : (ρ' (ρ g) * ρ' w) ^ N = 1 := by rw [← map_mul, hw, map_one, one_pow]
    rw [← ha]
    linear_combination (-(z * ρ' (ρ g') ^ N)) * hw'
  · obtain ⟨N, a, ha⟩ := h.surj b
    obtain ⟨M, hM⟩ := h'.ker (a := a) (by rw [AlgHom.comp_apply, ← ha, map_mul, hb, zero_mul])
    refine ⟨M, ?_⟩
    have := congrArg ρ hM
    simp only [map_mul, map_pow, map_zero, ← ha] at this
    have hw' : (ρ g * w) ^ (M + N) = 1 := by rw [hw, one_pow]
    linear_combination w ^ (M + N) * this - (ρ g' ^ M * b) * hw'
end GlobalTheory.SqZero.IsAway
