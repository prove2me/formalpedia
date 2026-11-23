-- Prove2me | solution 1 for GlobalTheory.AbLaw.MulN.surjective_of_geomFibres
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:26.755429+00:00
-- url     : https://prove2.me/submissions/f1e1f422-9445-49f6-b7ee-58526ada01fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Theorems.Thm_GlobalTheory_AbLaw_MulN_isPullback_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.MulN
namespace GlobalTheory.AbLaw.MulN
theorem _root_.solution {S : Scheme.{0}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Surjective ((Over.pullback t).map f).left) : Surjective f.left := by
  refine ⟨fun y => ?_⟩
  let K := AlgebraicClosure (Y.left.residueField y)
  let u : Spec (CommRingCat.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
      Y.left.fromSpecResidueField y
  let t := u ≫ Y.hom
  have hs := h K t
  let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  let v : Spec (CommRingCat.of K) ⟶ pullback Y.hom t := pullback.lift u (𝟙 _) (by simp [t])
  obtain ⟨x, hx⟩ := ((Over.pullback t).map f).left.surjective (v p)
  refine ⟨pullback.fst X.hom t x, ?_⟩
  have e := (isPullback_baseChange t f).w
  have e1 : f.left (pullback.fst X.hom t x) =
      pullback.fst Y.hom t (((Over.pullback t).map f).left x) := by
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  rw [e1, hx, ← Scheme.Hom.comp_apply]
  have : v ≫ pullback.fst Y.hom t = u := pullback.lift_fst _ _ _
  rw [this]
  exact (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply y _)
end GlobalTheory.AbLaw.MulN
