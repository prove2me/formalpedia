-- Prove2me | solution 1 for GlobalTheory.CoordToExt.bijective_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:46:01.047803+00:00
-- url     : https://prove2.me/submissions/fb0df998-aabc-466b-8bcb-2619386ba9fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
import Theorems.Thm_GlobalTheory_CoordToExt_gm_appLE
import Theorems.Thm_GlobalTheory_isAffineOpen_and_bijective_of_weight_units
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CoordToExt
variable {S : Scheme.{0}}
namespace GlobalTheory.CoordToExt
theorem _root_.solution {X : Type} [AddCommGroup X] {κ : Type} (b : Module.Basis κ ℤ X) {G B : Over S}
    [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G) (hq : IsMonHom q) (hi : IsMonHom i)
    (hf : Flat q.left) (hs : Surjective q.left) (ha : IsAffineHom q.left)
    (hk : IsPullback i (toUnit _) q (η[B])) (V : B.left.Opens) (hV : IsAffineOpen V)
    (u : κ → Γ(G.left, q.left ⁻¹ᵁ V)ˣ)
    (hu : ∀ (k : κ) (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), q.left (g.left z) ∈ V →
      gm ((t ≫ i) * g).left z _ (u k) = gm t.left z ⊤ (charUnit S X (b k)) * gm g.left z _ (u k)) :
    Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom
      ((Units.coeHom _).comp (AddMonoidHom.toMultiplicativeLeft
        (b.constr ℤ (fun k => Additive.ofMul (u k))).toAddMonoidHom)) (fun _ _ => Commute.all _ _)) := by
  refine (isAffineOpen_and_bijective_of_weight_units S X G B q i hq hi hf hs inferInstance hk V hV _ ?_).2
  intro χ Z t g h₁ h₂
  let v : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ := AddMonoidHom.toMultiplicativeLeft
    (b.constr ℤ (fun k => Additive.ofMul (u k))).toAddMonoidHom
  have hv : ∀ k, v (Multiplicative.ofAdd (b k)) = u k := fun k =>
    congrArg Additive.toMul (b.constr_basis ℤ (fun k => Additive.ofMul (u k)) k)
  let F₁ : Multiplicative X →* Γ(Z.left, ⊤)ˣ :=
    (Units.map (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom.toMonoidHom).comp v
  let F₂ : Multiplicative X →* Γ(Z.left, ⊤)ˣ := splitTorusPointsEquiv S X Z t *
    (Units.map (g.left.appLE _ ⊤ h₂).hom.toMonoidHom).comp v
  have e : (MonoidHom.toAdditiveRight F₁).toIntLinearMap = (MonoidHom.toAdditiveRight F₂).toIntLinearMap := by
    refine b.ext fun k => congrArg Additive.ofMul (unit_ext fun z _ => ?_)
    change gm _ z ⊤ (Units.map _ (v (Multiplicative.ofAdd (b k)))) =
      gm _ z ⊤ (splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd (b k)) * Units.map _ (v (Multiplicative.ofAdd (b k))))
    have a : splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd (b k)) = pullU t.left ⊤ (charUnit S X (b k)) :=
      Units.ext (splitTorusPointsEquiv_val _ _ _ t _)
    rw [map_mul, hv, gm_appLE, gm_appLE, hu k Z t g z (h₂ trivial), a]
    congr 1
    exact ((gm_pull (𝟙 _) t.left z ⊤ trivial _).trans (by rw [Category.id_comp])).symm
  have e' : F₁ (Multiplicative.ofAdd χ) = F₂ (Multiplicative.ofAdd χ) :=
    congrArg Additive.toMul (LinearMap.congr_fun e χ)
  rw [← splitTorusPointsEquiv_val]
  exact congrArg Units.val e'
end GlobalTheory.CoordToExt
