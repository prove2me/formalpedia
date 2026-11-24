-- Prove2me | solution 1 for GlobalTheory.SqZero.IsAway.lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:49.72193+00:00
-- url     : https://prove2.me/submissions/3a655f27-d13d-4900-9753-00a71ba24100

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
theorem _root_.solution (h : IsAway ρ g) (φ : S →ₐ[R] T) (hφ : IsUnit (φ g)) :
    ∃ ψ : S' →ₐ[R] T, ψ.comp ρ = φ := by
  letI := (ρ : S →+* S').toAlgebra
  haveI : IsLocalization.Away g S' := h
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun r => (ρ.commutes r).symm
  exact ⟨IsLocalization.Away.liftAlgHom g hφ,
    AlgHom.ext fun a => IsLocalization.Away.lift_eq g hφ a⟩
end GlobalTheory.SqZero.IsAway
