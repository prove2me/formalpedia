-- Prove2me | solution 1 for GlobalTheory.TorusGrading.exists_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:57:15.763527+00:00
-- url     : https://prove2.me/submissions/5a66a3c0-a185-4c0e-8a7e-7c17ced1d921

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Theorems.Thm_P2M_GlobalTheory_TorusGrading_toSpec__appLE_fromSpec_57347db5ee06
import Theorems.Thm_GlobalTheory_TorusGrading_appLE_comp_top
import Theorems.Thm_GlobalTheory_TorusGrading_chV_comp
import Theorems.Thm_GlobalTheory_TorusGrading_top_le_act
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorusGrading
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {V : G.left.Opens}
namespace GlobalTheory.TorusGrading
theorem _root_.solution (hV : IsAffineOpen V)
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    (u : Γ(G.left, V)) : ∃ a : X →₀ Γ(G.left, V), ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u =
        ∑ χ ∈ a.support, (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ) := by
  let B : CommRingCat.{0} := TorusInj.GA (X := X) (V := V)
  let P : Over S := Over.mk (TorusInj.ptY (X := X) hV ≫ G.hom)
  let g₀ : P ⟶ G := Over.homMk (TorusInj.ptY (X := X) hV) rfl
  let ε : Γ(P.left, ⊤) ≅ B := Scheme.ΓSpecIso B
  let t₀ : P ⟶ splitTorus S X := (splitTorusPointsEquiv S X P).symm
    (ε.inv.hom.toMonoidHom.comp (AddMonoidAlgebra.of Γ(G.left, V) X)).toHomUnits
  have ht₀ : ∀ χ, (chV t₀ χ).val = ε.inv.hom (AddMonoidAlgebra.single χ 1) := fun χ => by
    rw [chV, MulEquiv.apply_symm_apply]; rfl
  have hg₀ : ⊤ ≤ g₀.left ⁻¹ᵁ V := (TorusInj.ptY_preimage hV).ge
  let f : AddMonoidAlgebra Γ(G.left, V) X :=
    ε.hom.hom ((((t₀ ≫ i) * g₀).left.appLE V ⊤ (top_le_act hst t₀ hg₀)).hom u)
  refine ⟨f.coeff, fun Z t g h₁ h₂ => ?_⟩
  letI : Algebra Γ(G.left, V) Γ(Z.left, ⊤) := (g.left.appLE V ⊤ h₂).hom.toAlgebra
  let φ₀ : AddMonoidAlgebra Γ(G.left, V) X →ₐ[Γ(G.left, V)] Γ(Z.left, ⊤) :=
    AddMonoidAlgebra.lift Γ(G.left, V) Γ(Z.left, ⊤) X ((Units.coeHom _).comp (splitTorusPointsEquiv S X Z t))
  let φ : B ⟶ Γ(Z.left, ⊤) := CommRingCat.ofHom φ₀.toRingHom
  have hφ : ∀ χ c, φ.hom (AddMonoidAlgebra.single χ c) = (chV t χ).val * (g.left.appLE V ⊤ h₂).hom c := fun χ c => by
    change φ₀ (AddMonoidAlgebra.single χ c) = _
    rw [AddMonoidAlgebra.lift_single, Algebra.smul_def, mul_comm]; rfl
  have hσ : (Z.left.toSpecΓ ≫ Spec.map φ) ≫ TorusInj.ptY (X := X) hV = g.left := by
    rw [TorusInj.ptY, Category.assoc, ← Spec.map_comp_assoc]
    refine Eq.trans ?_ (toSpecΓ_appLE_fromSpec hV g.left h₂)
    congr 3
    exact CommRingCat.hom_ext (RingHom.ext fun c => φ₀.commutes c)
  let σ : Z ⟶ P := Over.homMk (Z.left.toSpecΓ ≫ Spec.map φ)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) hσ).trans (Over.w g)))
  have hσa : ∀ x : Γ(P.left, ⊤), σ.left.appTop.hom x = φ.hom (ε.hom.hom x) := fun x => by
    have : (Z.left.toSpecΓ ≫ Spec.map φ).appTop = ε.hom ≫ φ := by
      rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
    exact congrArg (fun q => q.hom x) this
  have hε : ∀ x : B, ε.hom.hom (ε.inv.hom x) = x := fun x => congrArg (fun q => q.hom x) ε.inv_hom_id
  have eg : σ ≫ g₀ = g := Over.OverMorphism.ext hσ
  have et : σ ≫ t₀ = t := (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun χ => Units.ext (by
    change (chV (σ ≫ t₀) χ.toAdd).val = (chV t χ.toAdd).val
    rw [chV_comp, ht₀, hσa, hε, hφ, map_one, _root_.mul_one]))
  have ea : σ ≫ ((t₀ ≫ i) * g₀) = (t ≫ i) * g := by
    rw [MonObj.comp_mul, ← Category.assoc, et, eg]
  rw [appLE_comp_top σ.left _ (top_le_act hst t₀ hg₀) (congrArg (fun q => q.left) ea) h₁ u, hσa]
  change φ.hom f = _
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  rw [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun χ _ => hφ χ _
end GlobalTheory.TorusGrading
