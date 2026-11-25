-- Prove2me | solution 1 for GlobalTheory.CubTrivTorus.eq_one_of_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:13:51.856466+00:00
-- url     : https://prove2.me/submissions/0dc020d9-f6b0-4b27-a0ef-b64c243e3e4e

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
import Theorems.Thm_GlobalTheory_CubTrivTorus_existsUnique_char
import Theorems.Thm_GlobalTheory_CubTrivTorus_eq_one_of_mul
import Theorems.Thm_GlobalTheory_CubTrivTorus_connectedSpace_torus
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

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
private lemma gm_units_map_global_eq_gm_comp {A B C : Scheme.{0}} (r : A ⟶ B) (g : B ⟶ C) (v : Γ(C, ⊤)ˣ) (z : A) :
    gm r z ⊤ (Units.map (g.appTop.hom : Γ(C, ⊤) →* Γ(B, ⊤)) v) = gm (r ≫ g) z ⊤ v := by
  rw [gm_top, gm_top (r ≫ g)]
  congr 1
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
theorem _root_.solution [ConnectedSpace S] [Module.Free ℤ X] (u : Γ((splitTorus S X).left, ⊤)ˣ)
    (h₃ : ∀ (Z : Over S) (x y w : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y * w).left z ⊤ u * gm x.left z ⊤ u * gm y.left z ⊤ u * gm w.left z ⊤ u =
        gm (x * y).left z ⊤ u * gm (x * w).left z ⊤ u * gm (y * w).left z ⊤ u)
    (h₁ : ∀ (Z : Over S) (z : Z.left), gm (1 : Z ⟶ splitTorus S X).left z ⊤ u = 1)
    (he : ∀ (Z : Over S) (x : Z ⟶ splitTorus S X) (z : Z.left), gm (x⁻¹).left z ⊤ u = gm x.left z ⊤ u) : u = 1 := by
  haveI : ConnectedSpace (splitTorus S X).left := connectedSpace_torus
  haveI hS : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›

  obtain ⟨ρ, hρ⟩ : ∃ ρ : Γ((splitTorus S X ⊗ splitTorus S X).left, ⊤)ˣ, ∀ (Z : Over S) (x y : Z ⟶ splitTorus S X)
      (z : Z.left), gm (lift x y).left z ⊤ ρ = gm (x * y).left z ⊤ u * (gm x.left z ⊤ u)⁻¹ * (gm y.left z ⊤ u)⁻¹ := by
    refine ⟨Units.map ((fst (splitTorus S X) (splitTorus S X) * snd _ _).left.appTop.hom :
        Γ((splitTorus S X).left, ⊤) →* Γ((splitTorus S X ⊗ splitTorus S X).left, ⊤)) u *
      (Units.map ((fst (splitTorus S X) (splitTorus S X)).left.appTop.hom :
        Γ((splitTorus S X).left, ⊤) →* Γ((splitTorus S X ⊗ splitTorus S X).left, ⊤)) u)⁻¹ *
      (Units.map ((snd (splitTorus S X) (splitTorus S X)).left.appTop.hom :
        Γ((splitTorus S X).left, ⊤) →* Γ((splitTorus S X ⊗ splitTorus S X).left, ⊤)) u)⁻¹, fun Z x y z => ?_⟩
    rw [map_mul, map_mul, map_inv, map_inv, gm_units_map_global_eq_gm_comp, gm_units_map_global_eq_gm_comp, gm_units_map_global_eq_gm_comp, ← Over.comp_left,
      ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
  have hmulρ : ∀ (Z : Over S) (t t' y : Z ⟶ splitTorus S X) (z : Z.left),
      gm (lift (t * t') y).left z ⊤ ρ = gm (lift t y).left z ⊤ ρ * gm (lift t' y).left z ⊤ ρ := by
    intro Z t t' y z
    rw [hρ, hρ, hρ]
    have alg : ∀ a b c d e f g : (Z.left.presheaf.stalk z)ˣ, a * b * c * d = e * f * g →
        a * e⁻¹ * d⁻¹ = f * b⁻¹ * d⁻¹ * (g * c⁻¹ * d⁻¹) := by
      intro a b c d e f g h
      have ha : a = e * f * g * b⁻¹ * c⁻¹ * d⁻¹ := by
        calc a = a * (b * b⁻¹) * (c * c⁻¹) * (d * d⁻¹) := by simp
          _ = a * b * c * d * b⁻¹ * c⁻¹ * d⁻¹ := by ac_rfl
          _ = e * f * g * b⁻¹ * c⁻¹ * d⁻¹ := by rw [h]
      rw [ha]
      calc e * f * g * b⁻¹ * c⁻¹ * d⁻¹ * e⁻¹ * d⁻¹ = f * b⁻¹ * d⁻¹ * (g * c⁻¹ * d⁻¹) * (e * e⁻¹) := by ac_rfl
        _ = f * b⁻¹ * d⁻¹ * (g * c⁻¹ * d⁻¹) := by simp
    exact alg _ _ _ _ _ _ _ (h₃ Z t t' y z)
  have honeρ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left),
      gm (lift t (1 : Z ⟶ splitTorus S X)).left z ⊤ ρ = 1 := by
    intro Z t z
    rw [hρ, _root_.mul_one, h₁ Z z, inv_one, _root_.mul_one, _root_.mul_inv_cancel]

  have hmul : ∀ (Z : Over S) (x y : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y).left z ⊤ u = gm x.left z ⊤ u * gm y.left z ⊤ u := by
    intro Z x y z
    have e := eq_one_of_mul ρ hmulρ honeρ Z x y z
    rw [hρ] at e
    calc gm (x * y).left z ⊤ u
        = gm (x * y).left z ⊤ u * (gm x.left z ⊤ u)⁻¹ * (gm y.left z ⊤ u)⁻¹ * (gm y.left z ⊤ u * gm x.left z ⊤ u) := by
          group
      _ = gm x.left z ⊤ u * gm y.left z ⊤ u := by rw [e, _root_.one_mul, _root_.mul_comm]

  have germ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ 𝟙_ (Over S)) (z : Z.left),
      gm (lift t y).left z ⊤ (Units.map ((fst (splitTorus S X) (𝟙_ (Over S))).left.appTop.hom :
        Γ((splitTorus S X).left, ⊤) →* Γ((splitTorus S X ⊗ 𝟙_ (Over S)).left, ⊤)) u) = gm t.left z ⊤ u := by
    intro Z t y z
    rw [gm_units_map_global_eq_gm_comp, ← Over.comp_left, lift_fst]
  obtain ⟨ψ, hψ, -⟩ := existsUnique_char (Y := 𝟙_ (Over S)) (Units.map ((fst (splitTorus S X) (𝟙_ (Over S))).left.appTop.hom :
        Γ((splitTorus S X).left, ⊤) →* Γ((splitTorus S X ⊗ 𝟙_ (Over S)).left, ⊤)) u)
    (fun Z t t' y z => by rw [germ, germ, germ]; exact hmul Z t t' z)
  have hψ' : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left), gm t.left z ⊤ u = gm (𝟙 Z.left) z ⊤ (chV t ψ) :=
    fun Z t z => by rw [← germ Z t (toUnit Z) z]; exact hψ Z t (toUnit Z) z

  have two : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), chV t (ψ + ψ) = 1 := by
    intro Z t
    apply global_units_ext_of_gm_id_eq
    intro z
    have e1 : gm (t⁻¹).left z ⊤ u = (gm t.left z ⊤ u)⁻¹ := by rw [hψ' Z t⁻¹ z, hψ' Z t z, chV_inv, map_inv]
    rw [chV_add, map_mul, map_one, ← hψ' Z t z]
    nth_rewrite 1 [← he Z t z]
    rw [e1, _root_.inv_mul_cancel]
  obtain ⟨χ₀, -, h₀⟩ := existsUnique_char (Y := 𝟙_ (Over S)) (1 : Γ((splitTorus S X ⊗ 𝟙_ (Over S)).left, ⊤)ˣ)
    (fun Z t t' y z => by simp)
  have e0 := h₀ 0 (fun Z t y z => by rw [chV_zero, map_one, map_one])
  have e2 := h₀ (ψ + ψ) (fun Z t y z => by rw [two Z t, map_one, map_one])
  have h2 : (2 : ℤ) • ψ = 0 := by rw [two_smul]; exact e2.trans e0.symm
  have hψ0 : ψ = 0 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
  apply global_units_ext_of_gm_id_eq
  intro z
  have e := hψ' (splitTorus S X) (𝟙 _) z
  rw [Over.id_left, hψ0, chV_zero] at e
  exact e
end GlobalTheory.CubTrivTorus
