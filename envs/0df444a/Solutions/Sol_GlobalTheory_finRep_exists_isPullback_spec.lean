-- Prove2me | solution 1 for GlobalTheory.finRep_exists_isPullback_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:01:36.427201+00:00
-- url     : https://prove2.me/submissions/8ad129ac-dad0-4bbb-8e60-665c3e2ef369

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinRepExistsIsPullbackSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{0}} (m : X ⟶ Y) [IsFinite m] [Flat m]
    (O : CommRingCat.{0}) (u : Spec O ⟶ Y) :
    ∃ (A : CommRingCat.{0}) (φ : O ⟶ A) (y : Spec A ⟶ X),
      φ.hom.Finite ∧ φ.hom.Flat ∧ IsPullback y (Spec.map φ) m u := by
  let N := Limits.pullback m u
  haveI : IsAffine N := isAffine_of_isAffineHom (Limits.pullback.snd m u)
  let f : Spec Γ(N, ⊤) ⟶ Spec O := N.isoSpec.inv ≫ Limits.pullback.snd m u
  have hf : Spec.map (Spec.preimage f) = f := Spec.map_preimage f
  refine ⟨Γ(N, ⊤), Spec.preimage f, N.isoSpec.inv ≫ Limits.pullback.fst m u, ?_, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff, hf]
    infer_instance
  · rw [← HasRingHomProperty.Spec_iff (P := @Flat), hf]
    infer_instance
  · rw [hf]
    refine (IsPullback.of_hasPullback m u).of_iso N.isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_ <;> simp [f]
end GlobalTheory
