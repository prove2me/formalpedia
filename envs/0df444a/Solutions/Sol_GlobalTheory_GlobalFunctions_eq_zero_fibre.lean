-- Prove2me | solution 1 for GlobalTheory.GlobalFunctions.eq_zero_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:28:23.744412+00:00
-- url     : https://prove2.me/submissions/3696c854-0738-424e-b1a4-60f4378ee5f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Theorems.Thm_GlobalTheory_GlobalFunctions_eq_zero_of_surjective
import Theorems.Thm_GlobalTheory_GlobalFunctions_isPullback_pr
import Theorems.Thm_GlobalTheory_GlobalFunctions_bc_apply
import Theorems.Thm_GlobalTheory_GlobalFunctions_bc_prR
import Theorems.Thm_GlobalTheory_GlobalFunctions_bc_prL
import Theorems.Thm_GlobalTheory_GlobalFunctions_specMap_algHom
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_field


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
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GlobalFunctions
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  {X : Scheme.{0}}
namespace GlobalTheory.GlobalFunctions
theorem _root_.solution (p : X ⟶ Spec (.of R)) [UniversallyClosed p] [GeometricallyIntegral p]
    (i : Spec (.of B) ⟶ X) [Flat i] [Surjective i] [QuasiCompact i] (f g : B →ₐ[R] C)
    (H : IsPullback (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) i i)
    (hφ : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R B))) (r : B →ₐ[R] R)
    (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] B)
    (hx : f.toLinearMap.baseChange k x = g.toLinearMap.baseChange k x)
    (hr : r.toLinearMap.baseChange k x = 0) : x = 0 := by
  let t : Spec (.of k) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R k))
  have hX := IsPullback.of_hasPullback p t
  have hB := isPullback_pr R k B
  have hC := isPullback_pr R k C
  let j : Spec (.of (k ⊗[R] B)) ⟶ pullback p t :=
    pullback.lift (prR R k B ≫ i) (prL R k B) (by rw [Category.assoc, hφ]; exact hB.w)
  have hj1 : j ≫ pullback.fst p t = prR R k B ≫ i := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd p t = prL R k B := pullback.lift_snd _ _ _
  have hj : IsPullback (prR R k B) j i (pullback.fst p t) :=
    IsPullback.of_bot (by rw [hj2, hφ]; exact hB) hj1.symm hX
  have hg : IsPullback (prR R k C) (Spec.map (bc k g)) (Spec.map (CommRingCat.ofHom g.toRingHom))
      (prR R k B) :=
    IsPullback.of_bot (by rw [bc_prL, specMap_algHom]; exact hC) (bc_prR k g).symm hB
  have hK : IsPullback (Spec.map (bc k f)) (Spec.map (bc k g)) j j := by
    refine IsPullback.of_right ?_ ?_ hj
    · rw [bc_prR, hj1]
      exact hg.paste_horiz H
    · apply pullback.hom_ext
      · simp only [Category.assoc, hj1]
        rw [← Category.assoc, ← Category.assoc, bc_prR, bc_prR, Category.assoc, Category.assoc, H.w]
      · simp only [Category.assoc, hj2, bc_prL]
  have : Flat j := MorphismProperty.of_isPullback hj ‹_›
  have : Surjective j := MorphismProperty.of_isPullback hj ‹_›
  have : QuasiCompact j := MorphismProperty.of_isPullback hj ‹_›
  have := ProperFunctions.isIso_appTop_of_field (pullback.snd p t)
  refine eq_zero_of_surjective (p := pullback.snd p t) (ConcreteCategory.bijective_of_isIso _).2
    j hK hj2 (bc k r) ?_ x ?_ ?_
  · have : Nontrivial (k ⊗[R] R) := (TensorProduct.rid R k).toEquiv.nontrivial
    exact RingHom.injective _
  · rw [bc_apply, bc_apply, hx]
  · rw [bc_apply, hr]
end GlobalTheory.GlobalFunctions
