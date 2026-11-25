-- Prove2me | solution 1 for GlobalTheory.torsion_invariant_descends_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:26:40.932787+00:00
-- url     : https://prove2.me/submissions/3ce35514-74b4-4e0c-8533-0547fec2fc23

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TorsionInvariantDescendsFibre
import Theorems.Thm_GlobalTheory_GrpTangent_etale_id_pow
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_TorsionLift_ptsEquiv_left
import Theorems.Thm_GlobalTheory_existsUnique_descend_of_torsion_invariant
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_torusCoord_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.torusCoord_apply


section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
private theorem fibreDescent_transport {X : Scheme.{0}} {m m' : X ⟶ X} (e : m = m')
    (P : (X ⟶ X) → Prop)
    (H : ∀ (V : X.Opens) (a : Γ(X, m' ⁻¹ᵁ V)),
      (∀ t, P t → ∀ h : m' ⁻¹ᵁ V ≤ t ⁻¹ᵁ (m' ⁻¹ᵁ V), (t.appLE _ _ h).hom a = a) →
      ∃! a' : Γ(X, V), (m'.app V).hom a' = a) :
    ∀ (V : X.Opens) (a : Γ(X, m ⁻¹ᵁ V)),
      (∀ t, P t → ∀ h : m ⁻¹ᵁ V ≤ t ⁻¹ᵁ (m ⁻¹ᵁ V), (t.appLE _ _ h).hom a = a) →
      ∃! a' : Γ(X, V), (m.app V).hom a' = a := by
  subst e; exact H
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (V : (G ⊗ Over.mk f).left.Opens) (a : Γ((G ⊗ Over.mk f).left, (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V)),
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ h : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V ≤ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left ⁻¹ᵁ ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V), ((lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left.appLE _ _ h).hom a = a) →
    ∃! a' : Γ((G ⊗ Over.mk f).left, V), ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left.app V).hom a' = a) := by
  intro S G _ _ K _ _ f N hN hsm hfin _ hsurj V a ha
  let A : Over (Spec (CommRingCat.of K)) := (Over.pullback f).obj G
  let ρ : ∀ (T : Over (Spec (CommRingCat.of K))) (t : T.left ⟶ S) (ht : T.hom ≫ f = t),
      (T ⟶ A) ≃* (Over.mk t ⟶ G) := fun T t ht => TorsionLift.ptsEquiv f G T t ht
  have hρ : ∀ T t ht x, (ρ T t ht x).left = x.left ≫ Limits.pullback.fst G.hom f :=
    fun T t ht x => TorsionLift.ptsEquiv_left f G T t ht x
  have hA : A.hom ≫ f = (G ⊗ Over.mk f).hom := Limits.pullback.condition.symm
  have hid : ρ A _ hA (𝟙 A) = fst G (Over.mk f) := Over.OverMorphism.ext (by
    rw [hρ]; exact Category.id_comp _)
  have ext : ∀ (u : A ⟶ A) (v : G ⊗ Over.mk f ⟶ G ⊗ Over.mk f),
      v ≫ fst _ _ = ρ A _ hA u → v ≫ snd _ _ = snd _ _ → v.left = u.left := by
    intro u v h1 h2
    apply Limits.pullback.hom_ext
    · exact (congrArg (·.left) h1).trans (hρ _ _ _ _)
    · exact (congrArg (·.left) h2).trans (Over.w u).symm
  have hm : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left = ((𝟙 A) ^ N : A ⟶ A).left := by
    refine ext _ _ ?_ (whiskerRight_snd _ _)
    rw [map_pow, hid, whiskerRight_fst, MonObj.comp_pow, Category.comp_id]
  have hpb : IsPullback (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left (Limits.pullback.fst G.hom f)
      (Limits.pullback.fst G.hom f) ((𝟙 G) ^ N : G ⟶ G).left := by
    refine IsPullback.of_right (h₁₂ := Limits.pullback.snd G.hom f) (v₁₃ := f) (h₂₂ := G.hom) ?_ ?_
      (IsPullback.of_hasPullback G.hom f).flip
    · rw [Over.w]
      have : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ Limits.pullback.snd G.hom f =
        Limits.pullback.snd G.hom f := congrArg (·.left) (whiskerRight_snd ((𝟙 G) ^ N) (Over.mk f))
      rw [this]
      exact (IsPullback.of_hasPullback G.hom f).flip
    · exact congrArg (·.left) (whiskerRight_fst ((𝟙 G) ^ N) (Over.mk f))
  have hsmA : Smooth A.hom := inferInstanceAs (Smooth (Limits.pullback.snd G.hom f))
  have h1 : Etale ((𝟙 A) ^ N : A ⟶ A).left := GrpTangent.etale_id_pow A (by
    simpa using (Ne.isUnit hN).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have h2 : Surjective ((𝟙 A) ^ N : A ⟶ A).left :=
    hm ▸ MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hsurj
  have h3 : IsFinite ((𝟙 A) ^ N : A ⟶ A).left :=
    hm ▸ MorphismProperty.of_isPullback (P := @IsFinite) hpb.flip hfin
  refine fibreDescent_transport hm (fun t => ∃ y : Over.mk f ⟶ G, y ^ N = 1 ∧
    t = (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) ?_ V a ?_
  · intro V a ha
    refine existsUnique_descend_of_torsion_invariant A N V a fun y hy => ?_
    refine ha _ ⟨ρ (𝟙_ _) f (Category.id_comp _) y, by rw [← map_pow, hy, map_one], ?_⟩
    refine (ext _ _ ?_ (lift_snd _ _)).symm
    rw [lift_fst, map_mul, hid, _root_.mul_comm]
    congr 1
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hρ, hρ, Over.comp_left, Category.assoc]
    rfl
  · rintro _ ⟨y, hy, rfl⟩
    exact ha y hy
end GlobalTheory
