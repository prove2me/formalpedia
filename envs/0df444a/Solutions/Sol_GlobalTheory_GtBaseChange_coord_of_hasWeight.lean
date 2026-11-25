-- Prove2me | solution 1 for GlobalTheory.GtBaseChange.coord_of_hasWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:11:31.430853+00:00
-- url     : https://prove2.me/submissions/a83aea63-6f60-4197-a0ad-9e9598039fc3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackPullbackMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Theorems.Thm_GlobalTheory_isAffineOpen_and_bijective_of_weight_units
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] SplitExt.free SplitExt.finite
noncomputable section
open GlobalTheory
open GlobalTheory.GtBaseChange
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
namespace GlobalTheory.GtBaseChange
theorem _root_.solution {K : Type} (b : Module.Basis K ℤ X) (q : G ⟶ B) (i : splitTorus S X ⟶ G)
    [hq : IsMonHom q] [hi : IsMonHom i] (hf : Flat q.left) (hs : Surjective q.left) (ha : IsAffineHom q.left)
    (hk : IsPullback i (toUnit _) q η[B]) (W : B.left.Opens) (u : K → Γ(G.left, q.left ⁻¹ᵁ W)ˣ)
    (hu : ∀ k, HasWeight i _ (u k) (b k)) (V : B.left.Opens) (hV : IsAffineOpen V) (h : V ≤ W) :
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom
        ((Units.coeHom _).comp (AddMonoidHom.toMultiplicativeLeft
          (b.constr ℤ (fun k => Additive.ofMul
            (res (Scheme.Hom.preimage_mono q.left h) (u k)))).toAddMonoidHom))
        (fun _ _ => Commute.all _ _)) := by
  refine (isAffineOpen_and_bijective_of_weight_units S X G B q i hq hi hf hs inferInstance hk V hV _ ?_).2
  intro χ Z t g h₁ h₂
  set v := AddMonoidHom.toMultiplicativeLeft
    (b.constr ℤ (fun k => Additive.ofMul (res (Scheme.Hom.preimage_mono q.left h) (u k)))).toAddMonoidHom with hv
  let A : Multiplicative X →* Γ(Z.left, ⊤)ˣ := ((res h₁).comp (pullU ((t ≫ i) * g).left _)).comp v
  let C : Multiplicative X →* Γ(Z.left, ⊤)ˣ :=
    splitTorusPointsEquiv S X Z t * ((res h₂).comp (pullU g.left _)).comp v
  have hAC : (MonoidHom.toAdditiveRight A).toIntLinearMap = (MonoidHom.toAdditiveRight C).toIntLinearMap := by
    refine b.ext fun k => ?_
    have hvk : v (Multiplicative.ofAdd (b k)) = res (Scheme.Hom.preimage_mono q.left h) (u k) := by
      simp [hv]
    have hT : (⊤ : Z.left.Opens) ≤ t.left ⁻¹ᵁ ⊤ := fun _ _ => trivial
    have hc : splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd (b k)) =
        res hT (pullU t.left ⊤ (charUnit S X (b k))) := by
      refine Units.ext ((splitTorusPointsEquiv_val S X Z t (b k)).trans ?_)
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    refine congrArg Additive.ofMul ?_
    change res h₁ (pullU _ _ (v (Multiplicative.ofAdd (b k)))) =
      splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd (b k)) *
        res h₂ (pullU _ _ (v (Multiplicative.ofAdd (b k))))
    rw [hvk, hc]
    refine unit_ext fun z hz => ?_
    rw [map_mul, gm_res_pullU' _ z h₁ hz, gm_res_pullU' _ z h₂ hz, gm_res ((t ≫ i) * g).left z _ (h₁ hz),
      gm_res g.left z _ (h₂ hz),
      hu k Z t g z (h (h₂ hz)), gm_res_pullU' _ z hT hz]
  have := congrArg (fun φ => (Additive.toMul (φ χ)).val) hAC
  rw [← splitTorusPointsEquiv_val]
  exact this
end GlobalTheory.GtBaseChange
