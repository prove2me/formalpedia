-- Prove2me | solution 1 for GlobalTheory.FlatPoints.affine_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:15:22.83913+00:00
-- url     : https://prove2.me/submissions/b9279c58-18d1-46cc-9286-8ef2d5590f90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorEqZeroOfForallGeometricPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SectionEqZeroOfForallGeometricPoint
import Theorems.Thm_GlobalTheory_FlatPoints_isPullback_whiskerRight_left
import Theorems.Thm_GlobalTheory_FlatPoints_section_eq_zero_of_cover
import Theorems.Thm_GlobalTheory_FlatPoints_eq_zero_of_forall_point
import Theorems.Thm_GlobalTheory_FlatPoints_finite_algHom
import Theorems.Thm_GlobalTheory_ExtUnique_isSchemeTheoreticallyDominant_spec_of_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FlatPoints
namespace GlobalTheory.FlatPoints
theorem _root_.solution (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F]
    (hinj : Function.Injective (algebraMap O F)) (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Flat O A] [_root_.IsReduced (TensorProduct O F A)]
    (H Y : Over (Spec (CommRingCat.of O))) (e : specO O A ≅ H) [Flat Y.hom]
    (W : (H ⊗ Y).left.Opens) (f : Γ((H ⊗ Y).left, W))
    (h : ∀ c : specO O F ⟶ H, ((c ▷ Y).left.app W).hom f = 0) : f = 0 := by
  have := finite_algHom O F A
  let Φ : A →ₐ[O] ((A →ₐ[O] F) → F) := Pi.algHom O (fun _ => F) (fun φ => φ)
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact eq_zero_of_forall_point O F hinj A a fun φ => congrFun ha φ
  let q : specO O ((A →ₐ[O] F) → F) ⟶ H := ptMap Φ ≫ e.hom
  have h1 : IsSchemeTheoreticallyDominant (ptMap Φ).left :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hΦ
  have h2 : QuasiCompact (ptMap Φ).left :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom Φ.toRingHom)))
  have h0 : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h3 : IsSchemeTheoreticallyDominant q.left := by
    change IsSchemeTheoreticallyDominant ((ptMap Φ).left ≫ e.hom.left)
    infer_instance
  have h4 : QuasiCompact q.left := by
    change QuasiCompact ((ptMap Φ).left ≫ e.hom.left)
    infer_instance
  have hp := isPullback_whiskerRight_left q Y
  have h5 : IsSchemeTheoreticallyDominant (q ▷ Y).left := .of_isPullback hp
  have h6 : QuasiCompact (q ▷ Y).left := MorphismProperty.of_isPullback hp h4
  apply (q ▷ Y).left.app_injective W
  rw [map_zero]
  let u : (A →ₐ[O] F) → (specO O F ⟶ specO O ((A →ₐ[O] F) → F)) :=
    fun φ => ptMap (Pi.evalAlgHom O (fun _ => F) φ)
  have hu : ∀ φ, IsOpenImmersion (u φ).left := fun φ =>
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : A →ₐ[O] F => CommRingCat.of F) φ))))
  have hu' : ∀ φ, IsOpenImmersion (u φ ▷ Y).left := fun φ =>
    MorphismProperty.of_isPullback (isPullback_whiskerRight_left (u φ) Y) (hu φ)
  refine section_eq_zero_of_cover (fun φ => (u φ ▷ Y).left) (fun x => ?_) _ _ (fun φ => ?_)
  · obtain ⟨φ, p, hp⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
      (R := fun _ : A →ₐ[O] F => F) (pullback.fst (specO O ((A →ₐ[O] F) → F)).hom Y.hom x)
    obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_whiskerRight_left (u φ) Y) p x hp
    exact ⟨φ, z, hz⟩
  · have := h (u φ ≫ q)
    rw [MonoidalCategory.comp_whiskerRight] at this
    exact this
end GlobalTheory.FlatPoints
