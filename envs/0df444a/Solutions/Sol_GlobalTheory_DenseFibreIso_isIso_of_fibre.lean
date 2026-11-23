-- Prove2me | solution 1 for GlobalTheory.DenseFibreIso.isIso_of_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:08.69365+00:00
-- url     : https://prove2.me/submissions/b925c44e-a265-48d0-9b38-22bac6a48817

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective

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
open GlobalTheory GlobalTheory.DenseFibreIso
variable {R : Type} [CommRing R] {Γ' X : Scheme.{0}} (s : X ⟶ Sp R) (f : Γ' ⟶ X)
namespace GlobalTheory.DenseFibreIso
theorem _root_.solution {S : Scheme.{0}} (t : S ⟶ Sp R)
    [IsIso (pullback.snd f (pullback.fst s t))] {T T' : Scheme.{0}} {g : T ⟶ X} {g' : T' ⟶ Γ'}
    {f' : T' ⟶ T} (H : IsPullback f' g' g f) (u : T ⟶ S) (hu : g ≫ s = u ≫ t) : IsIso f' := by
  have H₀ := (IsPullback.of_hasPullback f (pullback.fst s t)).flip
  have e : pullback.lift g u hu ≫ pullback.fst s t = g := pullback.lift_fst _ _ _
  have H₁ := IsPullback.of_bot' (h₁₁ := f') (v₁₂ := pullback.lift g u hu) (by rw [e]; exact H) H₀
  exact (MorphismProperty.isomorphisms Scheme.{0}).of_isPullback H₁.flip
    (inferInstanceAs (IsIso _))
end GlobalTheory.DenseFibreIso
