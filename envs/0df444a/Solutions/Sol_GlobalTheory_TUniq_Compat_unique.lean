-- Prove2me | solution 1 for GlobalTheory.TUniq.Compat.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:49:06.508594+00:00
-- url     : https://prove2.me/submissions/688c7dcb-1110-4a15-a935-d2e0dc9a093a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftClosedImmersionOfDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCompatOfLocal
import Theorems.Thm_GlobalTheory_TUniq_GeoGood_symm
import Theorems.Thm_GlobalTheory_TUniq_ext_of_geoGood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.TUniq
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}
namespace GlobalTheory.TUniq
namespace Compat
theorem _root_.solution {t t' : TObj g k J b s} {Sg : Set S} (hd : Dense Sg) (hg : GeoGood t t' Sg) {X : Scheme.{0}}
    [IsReduced X] {c₀ : X ⟶ t.A.left} [Flat (c₀ ≫ t.A.hom)] [LocallyOfFinitePresentation (c₀ ≫ t.A.hom)]
    {f f' : X ⟶ t'.A.left} (h : Compat t t' c₀ f) (h' : Compat t t' c₀ f') : f = f' := by
  have := t'.ab.proper
  refine ext_of_geoGood hd hg (c₀ ≫ t.A.hom) t'.A.hom h.1 h'.1 fun K _ _ su u x ψ ψ' h₁ h₂ y hy => ?_
  have w : (y ≫ c₀) ≫ t.A.hom = 𝟙 _ ≫ x := by rw [Category.assoc, hy, Category.id_comp]
  have e := (h₁.1.1.lift_fst _ _ w).symm
  exact (h.2 K su u x ψ ψ' h₁ h₂ K _ y e).trans (h'.2 K su u x ψ ψ' h₁ h₂ K _ y e).symm
end Compat
end GlobalTheory.TUniq
