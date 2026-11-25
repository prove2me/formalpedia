-- Prove2me | solution 1 for GlobalTheory.TUniq.Compat.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:59:03.439396+00:00
-- url     : https://prove2.me/submissions/59f2b6cf-8ad6-4429-ad16-bc9bdbed6fa5

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
theorem _root_.solution {t t' : TObj g k J b s} {X Y : Scheme.{0}} {c₀ : X ⟶ t.A.left} {f : X ⟶ t'.A.left}
    (h : Compat t t' c₀ f) (j : Y ⟶ X) : Compat t t' (j ≫ c₀) (j ≫ f) :=
  ⟨by rw [Category.assoc, Category.assoc, h.1], fun K _ _ su u x ψ ψ' h₁ h₂ B _ z y e => by
    rw [← Category.assoc] at e ⊢
    exact h.2 K su u x ψ ψ' h₁ h₂ B z _ e⟩
end Compat
end GlobalTheory.TUniq
