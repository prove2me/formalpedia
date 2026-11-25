-- Prove2me | solution 1 for GlobalTheory.LocTriv.exists_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:36:19.564478+00:00
-- url     : https://prove2.me/submissions/bef339bc-63cc-4a46-82f5-36ec6ac0d596

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGradedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Theorems.Thm_GlobalTheory_LocTriv_hom_ext_appLE
import Theorems.Thm_GlobalTheory_LocTriv_stable
import Theorems.Thm_GlobalTheory_LocTriv_exists_sum
import Theorems.Thm_GlobalTheory_LocTriv_appLE_app
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
open GlobalTheory GlobalTheory.LocTriv
variable {S : Scheme.{0}}
variable {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {q : G ⟶ B}
variable [IsMonHom i] [IsAffineHom q.left] {V : B.left.Opens} (hV : IsAffineOpen V)
  (h₀ : ∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a)
  (hU : (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤
    ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V))
  (u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ) (hu : ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ)
include hV h₀ hU
include hu
namespace GlobalTheory.LocTriv
theorem _root_.solution {Z : Over S} {g g' : Z ⟶ G} (hg : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) (h : g ≫ q = g' ≫ q) :
    ∃ t : Z ⟶ splitTorus S X, g' = (t ≫ i) * g :=  by
  have hg' : ⊤ ≤ g'.left ⁻¹ᵁ (q.left ⁻¹ᵁ V) := by
    have : ⊤ ≤ (g ≫ q).left ⁻¹ᵁ V := hg
    rw [h] at this
    exact this
  let φ : Multiplicative X →* Γ(Z.left, ⊤)ˣ :=
    (Units.map (g'.left.appLE _ ⊤ hg').hom.toMonoidHom).comp u /
      (Units.map (g.left.appLE _ ⊤ hg).hom.toMonoidHom).comp u
  refine ⟨(splitTorusPointsEquiv S X Z).symm φ, ?_⟩
  set t := (splitTorusPointsEquiv S X Z).symm φ with ht
  have hχ : ∀ χ, (chV t χ).val * (g.left.appLE _ ⊤ hg).hom (u (Multiplicative.ofAdd χ)).val =
      (g'.left.appLE _ ⊤ hg').hom (u (Multiplicative.ofAdd χ)).val := by
    intro χ
    have h3 : chV t χ = φ (Multiplicative.ofAdd χ) := by
      show (splitTorusPointsEquiv S X Z) t (Multiplicative.ofAdd χ) = _
      rw [ht]
      simp
    have h4 : φ (Multiplicative.ofAdd χ) *
        Units.map (g.left.appLE _ ⊤ hg).hom.toMonoidHom (u (Multiplicative.ofAdd χ)) =
        Units.map (g'.left.appLE _ ⊤ hg').hom.toMonoidHom (u (Multiplicative.ofAdd χ)) := by
      simp only [φ, MonoidHom.div_apply, MonoidHom.comp_apply, div_mul_cancel]
    rw [h3]
    exact congrArg Units.val h4
  have e3 : ∀ (s s' : Z ⟶ B) (hs : ⊤ ≤ s.left ⁻¹ᵁ V) (hs' : ⊤ ≤ s'.left ⁻¹ᵁ V), s = s' →
      s.left.appLE V ⊤ hs = s'.left.appLE V ⊤ hs' := by
    rintro s _ hs hs' rfl; rfl
  have hq : ∀ r, (g.left.appLE _ ⊤ hg).hom ((q.left.app V).hom r) =
      (g'.left.appLE _ ⊤ hg').hom ((q.left.app V).hom r) := by
    intro r
    have e1 := appLE_app (q := q) g hg
    have e2 := appLE_app (q := q) g' hg'
    have := congrArg (fun f => f.hom r) (e1.trans ((e3 _ _ hg hg' h).trans e2.symm))
    simpa using this
  have hA : IsAffineOpen (q.left ⁻¹ᵁ V) := hV.preimage q.left
  have h₁ := stable hU t hg
  apply Over.OverMorphism.ext
  refine hom_ext_appLE hA hg' h₁ ?_
  apply CommRingCat.hom_ext
  ext a
  obtain ⟨c, rfl⟩ := exists_sum hV h₀ hU u hu a
  simp only [Finsupp.sum, map_sum, map_mul]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [(h₀ _).2 ⟨c χ, rfl⟩ Z t g h₁ hg, hu χ Z t g h₁ hg, ← chV_val t (0 : X), chV_zero, Units.val_one,
    _root_.one_mul, ← chV_val t χ, hq, ← hχ]
end GlobalTheory.LocTriv
