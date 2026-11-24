-- Prove2me | solution 1 for GlobalTheory.LatticeTorsion.eq_prod_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:40:05.556847+00:00
-- url     : https://prove2.me/submissions/fe503354-91fa-4e85-b9cb-8aedea84b8dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteEtaleLatticeTorsionHom

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
open GlobalTheory GlobalTheory.LatticeTorsion
variable {S : Scheme.{0}}
namespace GlobalTheory.LatticeTorsion
theorem _root_.solution {La I A : Type} [AddCommGroup La] [Fintype I] [CommGroup A]
    (b : Module.Basis I ℤ La) (f : La → A) (hf : ∀ a c, f (a + c) = f a * f c) (a : La) :
    f a = ∏ i, f (b i) ^ (b.repr a i) := by
  let φ : Multiplicative La →* A := MonoidHom.mk' (fun x => f x.toAdd) fun x y => hf _ _
  have h : ∀ x, f x = φ (Multiplicative.ofAdd x) := fun _ => rfl
  conv_lhs => rw [← b.sum_repr a]
  simp only [h, ofAdd_sum, ofAdd_zsmul, map_prod, map_zpow]
end GlobalTheory.LatticeTorsion
