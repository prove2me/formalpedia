-- Prove2me | solution 1 for GlobalTheory.CubTrivTorus.existsUnique_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:11:45.305791+00:00
-- url     : https://prove2.me/submissions/ba28eb79-1337-48ad-a5fa-629559e8e051

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Theorems.Thm_GlobalTheory_existsUnique_character_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.CubTrivTorus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
private lemma global_units_ext_of_gm_id_eq {Z : Scheme.{0}} {u v : Γ(Z, ⊤)ˣ}
    (h : ∀ z : Z, gm (𝟙 Z) z ⊤ u = gm (𝟙 Z) z ⊤ v) : u = v := by
  ext
  apply fn_ext
  intro x _
  rw [gs_unit (𝟙 Z) x ⊤ (by simp) u, gs_unit (𝟙 Z) x ⊤ (by simp) v, h x]
private lemma scheme_appTop_comp_apply {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (a : Γ(C, ⊤)) :
    f.appTop.hom (g.appTop.hom a) = (f ≫ g).appTop.hom a := by
  rw [Scheme.Hom.comp_appTop]
  rfl
private lemma global_val_eq_of_gm_eq {A B : Scheme.{0}} (r : A ⟶ B) (ρ : Γ(B, ⊤)ˣ) (c : Γ(A, ⊤)ˣ)
    (h : ∀ z, gm r z ⊤ ρ = gm (𝟙 A) z ⊤ c) : r.appTop.hom ρ.val = c.val := by
  have e : Units.map (r.appTop.hom : Γ(B, ⊤) →* Γ(A, ⊤)) ρ = c :=
    global_units_ext_of_gm_id_eq fun z => by rw [← h z, gm_top r]; rfl
  rw [← e]
  rfl
private lemma global_val_eq_mul_of_gm_eq_mul {A B : Scheme.{0}} (r r₁ r₂ : A ⟶ B) (ρ : Γ(B, ⊤)ˣ)
    (h : ∀ z, gm r z ⊤ ρ = gm r₁ z ⊤ ρ * gm r₂ z ⊤ ρ) :
    r.appTop.hom ρ.val = r₁.appTop.hom ρ.val * r₂.appTop.hom ρ.val := by
  have e := global_val_eq_of_gm_eq r ρ (Units.map (r₁.appTop.hom : Γ(B, ⊤) →* Γ(A, ⊤)) ρ *
    Units.map (r₂.appTop.hom : Γ(B, ⊤) →* Γ(A, ⊤)) ρ) (fun z => by rw [map_mul, h z, gm_top r₁, gm_top r₂]; rfl)
  rw [e]
  rfl
section
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (i : H ⟶ G)
variable {i} [IsMonHom i] {L : RigLB G} {c : CubicalStr G L}
end
variable [ConnectedSpace S] [Module.Free ℤ X] {G : Over S} [GrpObj G] [IsCommMonObj G] {i : splitTorus S X ⟶ G}
  [IsMonHom i]
end GlobalTheory.CubTrivTorus
end
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubTrivTorus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
namespace GlobalTheory.CubTrivTorus
theorem _root_.solution {Y : Over S} [ConnectedSpace Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (hρ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (z : Z.left),
      gm (lift (t * t') y).left z ⊤ ρ = gm (lift t y).left z ⊤ ρ * gm (lift t' y).left z ⊤ ρ) :
    ∃! χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (z : Z.left),
      gm (lift t y).left z ⊤ ρ = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
  have hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ρ.val =
        (lift t y).left.appTop.hom ρ.val * (lift t' y).left.appTop.hom ρ.val :=
    fun Z t t' y => global_val_eq_mul_of_gm_eq_mul _ _ _ ρ (hρ Z t t' y)
  obtain ⟨χ, hχ, huniq⟩ := GlobalTheory.existsUnique_character_of_mul S X Y ρ hm
  refine ⟨χ, fun Z t y z => ?_, fun χ' hχ' => huniq χ' ?_⟩
  · rw [gm_top]
    congr 1
    ext
    simp only [Units.coe_map, hχ, chV_val]
    show (lift t y).left.appTop.hom ((fst (splitTorus S X) Y).left.appTop.hom _) = _
    rw [scheme_appTop_comp_apply, ← Over.comp_left, lift_fst]
  · have e := global_val_eq_of_gm_eq (𝟙 _) ρ (chV (fst (splitTorus S X) Y) χ') (fun z => by
      have := hχ' (splitTorus S X ⊗ Y) (fst _ _) (snd _ _) z
      rwa [lift_fst_snd, Over.id_left] at this)
    rw [chV_val] at e
    simpa using e
end GlobalTheory.CubTrivTorus
