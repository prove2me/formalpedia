-- Prove2me | solution 1 for GlobalTheory.SqZero.IsAway.ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:49.672495+00:00
-- url     : https://prove2.me/submissions/52eaa015-ee1a-4bc5-aa10-2bae88c9d255

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
theorem _root_.solution (h : IsAway ρ g) {ψ ψ' : S' →ₐ[R] T} (e : ψ.comp ρ = ψ'.comp ρ) : ψ = ψ' := by
  ext z
  obtain ⟨N, a, hz⟩ := h.surj z
  have e' : ∀ a, ψ (ρ a) = ψ' (ρ a) := fun a => AlgHom.congr_fun e a
  have hu : IsUnit (ψ (ρ g) ^ N) := (h.unit.map ψ).pow N
  apply hu.mul_right_cancel
  rw [← map_pow, ← map_mul, hz, map_pow, e', e', ← map_pow, ← map_mul, hz]
end GlobalTheory.SqZero.IsAway
