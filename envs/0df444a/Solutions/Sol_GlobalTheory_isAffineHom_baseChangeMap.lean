-- Prove2me | solution 1 for GlobalTheory.isAffineHom_baseChangeMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:28:09.555506+00:00
-- url     : https://prove2.me/submissions/6fd62adf-3490-4711-86ac-509dda34be0c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C]
variable {R₀ : Subalgebra k C}
variable {B : Scheme.{0}} (pB : B ⟶ Sp k)
variable {A A' A'' : Type} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] [CommRing A''] [Algebra k A'']
namespace GlobalTheory
theorem _root_.solution (f : A →ₐ[k] A') : IsAffineHom (baseChangeMap pB f) := by
  have : IsAffineHom (pullback.fst pB (spMap (algebraMap k A))) :=
    (isAffineHom_isStableUnderBaseChange).of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have : IsAffineHom (baseChangeMap pB f ≫ pullback.fst _ _) := by
    rw [baseChangeMap_fst]
    exact (isAffineHom_isStableUnderBaseChange).of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  exact IsAffineHom.of_comp _ (pullback.fst _ _)
end GlobalTheory
