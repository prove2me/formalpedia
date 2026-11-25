-- Prove2me | solution 1 for GlobalTheory.T.exists_fg_subalgebra_grpObj_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:17:54.759628+00:00
-- url     : https://prove2.me/submissions/18884448-a484-4168-8830-c71166ab9ebc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToFgSubalgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToFgSubalgebraStatement
import Theorems.Thm_GlobalTheory_grpObj_descends_to_fg_subalgebra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (X : Scheme.{0}) (p : X ⟶ Sp k) (φ : A.left ⟶ X) (F : Finset V), Smooth p → IsSeparated p → QuasiCompact p → IsPullback φ A.hom p (spMap (algebraMap k V)) → ∃ (R : Subalgebra k V) (A₀ : Over (Sp R)) (_ : GrpObj A₀) (_ : IsCommMonObj A₀) (ψ : A.left ⟶ A₀.left), (F : Set V) ⊆ R ∧ R.FG ∧ Smooth A₀.hom ∧ IsSeparated A₀.hom ∧ QuasiCompact A₀.hom ∧ IsGrpPullback A A₀ (spMap R.val.toRingHom) ψ := by
  first | exact @GlobalTheory.grpObj_descends_to_fg_subalgebra | exact GlobalTheory.grpObj_descends_to_fg_subalgebra | (intros; apply GlobalTheory.grpObj_descends_to_fg_subalgebra <;> assumption)
end _root_.GlobalTheory.T
