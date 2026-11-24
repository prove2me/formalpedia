-- Prove2me | solution 1 for GlobalTheory.TorusNil.spm_left_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:36:07.930986+00:00
-- url     : https://prove2.me/submissions/4c97b464-3668-408e-aee5-9782784a3a3d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
variable {C D E : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
  [CommRing E] [Algebra A E]
namespace GlobalTheory.TorusNil
theorem _root_.solution (π : C →ₐ[A] D) (hs : Function.Surjective π)
    (hn : ∀ x, π x = 0 → IsNilpotent x) : Function.Surjective (spm π).left := by
  have h := range_comap_of_surjective D π.toRingHom hs
  have h2 : PrimeSpectrum.zeroLocus (RingHom.ker π.toRingHom : Set C) = Set.univ := by
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    exact hn x hx
  rw [h2, Set.range_eq_univ] at h
  exact h
end GlobalTheory.TorusNil
