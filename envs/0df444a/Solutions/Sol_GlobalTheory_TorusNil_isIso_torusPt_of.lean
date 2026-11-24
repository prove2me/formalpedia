-- Prove2me | solution 1 for GlobalTheory.TorusNil.isIso_torusPt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:14.788551+00:00
-- url     : https://prove2.me/submissions/fdd76c53-4e83-4d19-bec6-b05cff3d6b29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Theorems.Thm_GlobalTheory_TorusNil_torusPt_fst
import Theorems.Thm_GlobalTheory_TorusNil_ringHom_ext_int_torus

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
variable (A) (X : Type) [AddCommGroup X]
open scoped AlgebraMonoidAlgebra
namespace GlobalTheory.TorusNil
theorem _root_.solution :
    IsIso (torusPt A X (AddMonoidAlgebra.of A X)).left := by
  letI : Algebra ZU.{0} A := ULift.algebra' ℤ A
  haveI : IsScalarTower ZU.{0} (AddMonoidAlgebra ZU.{0} X) (AddMonoidAlgebra A X) :=
    ⟨fun r a b => by
      obtain ⟨n⟩ := r
      show (n • a) • b = n • (a • b)
      simp only [Algebra.smul_def, map_mul, _root_.mul_assoc, eq_intCast, map_intCast]⟩
  have hp := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout ZU.{0} (AddMonoidAlgebra ZU.{0} X) A (AddMonoidAlgebra A X))
  have hz : Spec.map (CommRingCat.ofHom (algebraMap ZU.{0} A)) = toZ (Spec (.of A)) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [hz] at hp
  obtain ⟨φ, h1, h2⟩ := torusPt_fst A X (AddMonoidAlgebra.of A X)
  have : (torusPt A X (AddMonoidAlgebra.of A X)).left = hp.isoPullback.hom := by
    apply pullback.hom_ext
    · refine h2.trans (Eq.trans ?_ hp.isoPullback_hom_fst.symm)
      congr 2
      apply ringHom_ext_int_torus
      intro y
      rw [h1]
      simp
    · exact (Over.w _).trans hp.isoPullback_hom_snd.symm
  rw [this]
  exact hp.isoPullback.isIso_hom
end GlobalTheory.TorusNil
