-- Prove2me | solution 1 for GlobalTheory.TorsionFieldExt.comp_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:43.780064+00:00
-- url     : https://prove2.me/submissions/f0efda6c-972d-4ded-b9c8-c2a7dfb11b82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionPointsFieldExtension

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TorsionFieldExt
variable {S : Scheme.{0}}
namespace GlobalTheory.TorsionFieldExt
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] {x : Sp K ⟶ S} {x' : Sp Ω ⟶ S}
    (u : Over.mk x' ⟶ Over.mk x) (A : Over S) : Function.Injective (fun y : Over.mk x ⟶ A => u ≫ y) := by
  let v : Sp Ω ⟶ Sp K := u.left
  have : Surjective v := ⟨fun z => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : Epi v := Flat.epi_of_flat_of_surjective v
  intro a b h
  have h' : v ≫ a.left = v ≫ b.left := congrArg (fun q => q.left) h
  exact Over.OverMorphism.ext ((cancel_epi v).1 h')
end GlobalTheory.TorsionFieldExt
