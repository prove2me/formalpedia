-- Prove2me | solution 1 for GlobalTheory.finRep_kernel_mul_finite_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:12:24.056256+00:00
-- url     : https://prove2.me/submissions/a5203ae5-2abb-492f-bc1a-092274d34b87

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinRepExistsIsPullbackSpec
import Theorems.Thm_GlobalTheory_finRep_exists_isPullback_spec
import Theorems.Thm_GlobalTheory_finRep_one_left

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
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (p : ℕ), IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Smooth G.hom →
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra (O : Type) A) (_ : Algebra R₀ A) (_ : IsScalarTower R₀ (O : Type) A),
      Module.Free (O : Type) A ∧ Module.Finite (O : Type) A ∧ ∃ y : sp (R₀ := R₀) A ⟶ G, y ^ p = 1 ∧
      ∀ (S : Type) [CommRing S] [Algebra (O : Type) S] [Algebra R₀ S] [IsScalarTower R₀ (O : Type) S] (z : sp (R₀ := R₀) S ⟶ G), z ^ p = 1 →
        ∃! φ : A →ₐ[(O : Type)] S, spMap (φ.restrictScalars R₀) ≫ y = z) := by
  intro R₀ _ G _ _ O p hfin hflat _
  obtain ⟨A, φ, y, hφf, hφl, hpb⟩ := finRep_exists_isPullback_spec ((𝟙 G) ^ p : G ⟶ G).left
    (CommRingCat.of (O : Type)) (1 : sp (R₀ := R₀) (O : Type) ⟶ G).left
  letI : Algebra (O : Type) A := φ.hom.toAlgebra
  letI : Algebra R₀ A := (φ.hom.comp (algebraMap R₀ (O : Type))).toAlgebra
  haveI : IsScalarTower R₀ (O : Type) A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite (O : Type) A := hφf
  haveI : Module.Flat (O : Type) A := hφl
  have hpow : ∀ {T : Over (Spec (CommRingCat.of R₀))} (z : T ⟶ G),
      z.left ≫ ((𝟙 G) ^ p : G ⟶ G).left = (z ^ p).left := by
    intro T z
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hy : y ≫ G.hom = (sp (R₀ := R₀) A).hom := by
    rw [← Over.w ((𝟙 G) ^ p : G ⟶ G), ← Category.assoc, hpb.w, Category.assoc,
      Over.w (1 : sp (R₀ := R₀) (O : Type) ⟶ G)]
    simp only [sp, Over.mk_hom]
    rw [← Spec.map_comp]
    rfl
  let y' : sp (R₀ := R₀) A ⟶ G := Over.homMk y hy
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.free_of_flat_of_isLocalRing, inferInstance, y', ?_, ?_⟩
  · apply Over.OverMorphism.ext
    rw [← hpow, finRep_one_left G (IsScalarTower.toAlgHom R₀ (O : Type) A)]
    exact hpb.w
  · intro S _ _ _ _ z hz
    have hw : z.left ≫ ((𝟙 G) ^ p : G ⟶ G).left =
        Spec.map (CommRingCat.ofHom (algebraMap (O : Type) S)) ≫
          (1 : sp (R₀ := R₀) (O : Type) ⟶ G).left := by
      rw [hpow, hz, finRep_one_left G (IsScalarTower.toAlgHom R₀ (O : Type) S)]
      rfl
    let l : Spec (CommRingCat.of S) ⟶ Spec A := hpb.lift _ _ hw
    have hl : Spec.map (Spec.preimage l) = l := Spec.map_preimage l
    have h1 : φ ≫ Spec.preimage l = CommRingCat.ofHom (algebraMap (O : Type) S) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hl]
      exact hpb.lift_snd _ _ hw
    refine ⟨⟨(Spec.preimage l).hom, fun r => congrArg (fun f => f.hom r) h1⟩, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      change Spec.map (Spec.preimage l) ≫ y = z.left
      rw [hl]
      exact hpb.lift_fst _ _ hw
    · intro ψ hψ
      have h2 : Spec.map (CommRingCat.ofHom ψ.toRingHom : A ⟶ CommRingCat.of S) = l := by
        apply hpb.hom_ext
        · rw [hpb.lift_fst _ _ hw, ← hψ]
          rfl
        · rw [hpb.lift_snd _ _ hw, ← Spec.map_comp]
          congr 1
          ext r
          exact ψ.commutes r
      have h3 := Spec.map_injective (h2.trans hl.symm)
      ext a
      exact congrArg (fun f => f.hom a) h3
end GlobalTheory
