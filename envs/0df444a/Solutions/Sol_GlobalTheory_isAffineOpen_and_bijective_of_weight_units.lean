-- Prove2me | solution 1 for GlobalTheory.isAffineOpen_and_bijective_of_weight_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:49:48.975669+00:00
-- url     : https://prove2.me/submissions/ea32c807-0959-4ec1-ac04-72a69c95b054

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Theorems.Thm_GlobalTheory_TorusTrivial_exists_isPullback
import Theorems.Thm_GlobalTheory_TorusTrivial_isAffine_and_bijective
import Theorems.Thm_GlobalTheory_TorusTrivial_app_comp_topIso_inv
import Theorems.Thm_GlobalTheory_TorusTrivial_cover_of_isPullback
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_appLE_of_eq


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
open GlobalTheory
open TorusTrivial
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G B : Over S) [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → ∀ (V : B.left.Opens), IsAffineOpen V → ∀ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, (∀ (χ : X) (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)), (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom (u (Multiplicative.ofAdd χ)).val = t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom (u (Multiplicative.ofAdd χ)).val) → IsAffineOpen (q.left ⁻¹ᵁ V) ∧ Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom ((Units.coeHom _).comp u) (fun _ _ => Commute.all _ _)) := by
  intro S X _ G B _ _ q i _ _ hfl hsu hqc hk V hV u hu
  let U : G.left.Opens := q.left ⁻¹ᵁ V
  let W : Over S := Over.mk (U.ι ≫ G.hom)
  let V' : Over S := Over.mk (V.ι ≫ B.hom)
  let j : W ⟶ G := Over.homMk U.ι rfl
  let k : V' ⟶ B := Over.homMk V.ι rfl
  let q' : W ⟶ V' := Over.homMk (q.left ∣_ V) (by
    change (q.left ∣_ V) ≫ V.ι ≫ B.hom = U.ι ≫ G.hom
    rw [morphismRestrict_ι_assoc, Over.w])
  have hW₀ : IsPullback U.ι (q.left ∣_ V) q.left V.ι := (isPullback_morphismRestrict q.left V).flip
  have hW : IsPullback j q' q k :=
    IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext hW₀.w) hW₀
  have : Mono j.left := inferInstanceAs (Mono U.ι)
  have : Mono j := Over.mono_of_mono_left j
  let τ : W ⟶ splitTorus S X := (splitTorusPointsEquiv S X W).symm
    ((Units.map U.topIso.inv.hom.toMonoidHom).comp u)
  have hτ₀ : ∀ χ : X, τ.left.appTop.hom (charUnit S X χ).val =
      U.topIso.inv.hom (u (Multiplicative.ofAdd χ)).val := by
    intro χ
    rw [← splitTorusPointsEquiv_val, MulEquiv.apply_symm_apply]
    rfl
  have hle : ∀ {Z : Over S} (g : Z ⟶ W), ⊤ ≤ (g ≫ j).left ⁻¹ᵁ U := by
    intro Z g x _
    exact (g.left x).2
  have hτ₁ : ∀ {Z : Over S} (g : Z ⟶ W) (χ : X), (g ≫ τ).left.appTop.hom (charUnit S X χ).val =
      ((g ≫ j).left.appLE U ⊤ (hle g)).hom (u (Multiplicative.ofAdd χ)).val := by
    intro Z g χ
    let g' : Z.left ⟶ U := g.left
    have h : U.topIso.inv ≫ g'.appTop = (g' ≫ U.ι).appLE U ⊤ (hle g) := by
      rw [← Scheme.Hom.appLE_comp_appLE g' U.ι U ⊤ ⊤ (by simp) (by simp), Scheme.Hom.appTop,
        Scheme.Hom.app_eq_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
      rfl
    change g'.appTop.hom (τ.left.appTop.hom (charUnit S X χ).val) = _
    rw [hτ₀]
    exact congrArg (fun f => f.hom (u (Multiplicative.ofAdd χ)).val) h
  obtain ⟨a, ha⟩ := exists_isPullback q i hk hW τ (by
    intro Z t g g' hg
    apply (splitTorusPointsEquiv S X Z).injective
    rw [map_mul]
    ext χ
    change (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val =
      (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val *
      (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val
    rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, hτ₁, hτ₁,
      TorusInj.appLE_of_eq (congrArg Over.Hom.left hg)]
    exact hu χ Z t (g ≫ j) _ _)
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) q'.left :=
    cover_of_isPullback hW₀ ⟨⟨hsu, hfl⟩, hqc⟩
  have hT : IsPullback (snd (splitTorus S X) W) (splitTorus S X ◁ q') q'
      (snd (splitTorus S X) V') := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => lift (c.snd ≫ fst _ _) c.fst)
      (fun c => by simp) (fun c => ?_) (fun c m h₁ h₂ => ?_)⟩⟩
    · ext <;> simp [c.condition]
    · ext <;> simp [← h₁, ← h₂]
  have hQ' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
      (splitTorus S X ◁ q').left :=
    cover_of_isPullback (hT.map (Over.forget S)) hQ
  have : IsIso (lift τ q').left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := .isomorphisms Scheme.{0})
      (ha.map (Over.forget S)) hQ' (MorphismProperty.isomorphisms.infer_property _)
  have : IsIso ((Over.forget S).map (lift τ q')) := this
  have : IsIso (lift τ q') := isIso_of_reflects_iso _ (Over.forget S)
  have : IsAffine V'.left := hV
  obtain ⟨h₁, h₂⟩ := isAffine_and_bijective τ q' (A := Γ(B.left, V)) V.topIso.symm
    (U.topIso.inv.hom.comp (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom
      ((Units.coeHom _).comp u) (fun _ _ => Commute.all _ _)))
    (fun a => by
      refine Eq.trans ?_ (congrArg (fun f => f.hom a) (app_comp_topIso_inv q.left V))
      refine congrArg U.topIso.inv.hom ?_
      refine (AddMonoidAlgebra.liftNC_single _ _ 0 a).trans ?_
      exact (congrArg (_ * ·) (((Units.coeHom _).comp u).map_one)).trans (_root_.mul_one _))
    (fun χ => by
      rw [hτ₀]
      simp [AddMonoidAlgebra.liftNCRingHom])
  refine ⟨h₁, ?_⟩
  exact (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso U.topIso.inv) _).mp h₂
end GlobalTheory
