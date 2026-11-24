-- Prove2me | solution 1 for GlobalTheory.ToSplit.hasWeight_of_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:25.334891+00:00
-- url     : https://prove2.me/submissions/257591ca-fbca-40ef-8859-71e93f86477f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Theorems.Thm_GlobalTheory_ToSplit_gm_comp
import Theorems.Thm_GlobalTheory_ToSplit_charGerm_eq
import Theorems.Thm_GlobalTheory_ToSplit_act_apply
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val


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
open GlobalTheory.ToSplit
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
variable {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q]
  (hk : IsPullback i (toUnit _) q (η[B]))
include hk
namespace GlobalTheory.ToSplit
theorem _root_.solution {χ : X} {V : B.left.Opens} {u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ}
    (hu : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)),
      (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom u.val =
        t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u.val) :
    HasWeight q i χ V u := by
  intro Z t g z hz
  let W : Z.left.Opens := g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)
  let Z' : Over S := Over.mk (W.ι ≫ Z.hom)
  let κ : Z' ⟶ Z := Over.homMk W.ι rfl
  have h₂ : ⊤ ≤ (κ ≫ g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) := fun x _ => x.2
  have h₁ : ⊤ ≤ (((κ ≫ t) ≫ i) * (κ ≫ g)).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) := fun x hx => by
    change q.left _ ∈ V
    rw [act_apply hk]
    exact h₂ hx
  have e : res h₁ (pullU _ _ u) =
      splitTorusPointsEquiv S X Z' (κ ≫ t) (Multiplicative.ofAdd χ) * res h₂ (pullU _ _ u) :=
    Units.ext ((hu Z' (κ ≫ t) (κ ≫ g) h₁ h₂).trans (by rw [← splitTorusPointsEquiv_val]; rfl))
  let z' : Z'.left := (⟨z, hz⟩ : W)
  have e' := (gm_id_res_pull _ z' h₁ trivial u).symm.trans
    ((congrArg (gm (𝟙 _) z' ⊤) e).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (charGerm_eq z' (κ ≫ t) χ) (gm_id_res_pull _ z' h₂ trivial _))))
  have e₁ : ((κ ≫ t) ≫ i) * (κ ≫ g) = κ ≫ ((t ≫ i) * g) := by
    rw [MonObj.comp_mul, Category.assoc]
  have hz' : q.left (((t ≫ i) * g).left z) ∈ V := by rwa [act_apply hk]
  rw [e₁] at e'
  have e'' := (gm_comp W.ι ((t ≫ i) * g).left ⟨z, hz⟩ (q.left ⁻¹ᵁ V) hz' u).symm.trans
    (e'.trans ((congrArg₂ (· * ·) (gm_comp W.ι t.left ⟨z, hz⟩ ⊤ trivial _)
      (gm_comp W.ι g.left ⟨z, hz⟩ (q.left ⁻¹ᵁ V) hz u)).trans (map_mul _ _ _).symm))
  rw [charGerm_eq]
  have : IsIso (W.ι.stalkMap ⟨z, hz⟩) := IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
  exact Units.ext ((ConcreteCategory.bijective_of_isIso (W.ι.stalkMap ⟨z, hz⟩)).1
    (congrArg Units.val e''))
end GlobalTheory.ToSplit
