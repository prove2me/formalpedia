-- Prove2me | solution 1 for GlobalTheory.CubTrivTorus.eq_of_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:52:44.952076+00:00
-- url     : https://prove2.me/submissions/a0a5186b-a20b-40c6-8b5a-b8f0897aa182

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
import Theorems.Thm_GlobalTheory_CubTrivTorus_eq_one_of_even
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubTrivTorus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable [ConnectedSpace S] [Module.Free ℤ X] {G : Over S} [GrpObj G] [IsCommMonObj G] {i : splitTorus S X ⟶ G}
  [IsMonHom i]
namespace GlobalTheory.CubTrivTorus
theorem _root_.solution {P : CP G} {σ σ' : CubTriv P.c i} (h : σ.Even) (h' : σ'.Even) : σ = σ' := by
  classical
  obtain ⟨u, hu⟩ := GlobalTheory.TorusCoord.exists_ratio P.L.isLB (fun U _ h => rfl) σ.s σ.gen σ'.s σ'.gen
  have h3 : ∀ (Z : Over S) (x y w : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y * w).left z ⊤ u * gm x.left z ⊤ u * gm y.left z ⊤ u * gm w.left z ⊤ u =
        gm (x * y).left z ⊤ u * gm (x * w).left z ⊤ u * gm (y * w).left z ⊤ u := by
    intro Z x y w z
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    have hc := σ.cub Z x y w z J hJ
    have hc' := σ'.cub Z x y w z J hJ
    simp only [hu Z.left _ z J hJ] at hc
    have alg : ∀ a b c d e f g S₁ S₂ S₃ S₄ C S₅ S₆ S₇ : (Z.left.presheaf.stalk z)ˣ,
        a * S₁ * (b * S₂) * (c * S₃) * (d * S₄) = C * (e * S₅) * (f * S₆) * (g * S₇) →
        S₁ * S₂ * S₃ * S₄ = C * S₅ * S₆ * S₇ → a * b * c * d = e * f * g := by
      intro a b c d e f g S₁ S₂ S₃ S₄ C S₅ S₆ S₇ h h'
      apply mul_right_cancel (b := S₁ * S₂ * S₃ * S₄)
      calc a * b * c * d * (S₁ * S₂ * S₃ * S₄) = a * S₁ * (b * S₂) * (c * S₃) * (d * S₄) := by ac_rfl
        _ = C * (e * S₅) * (f * S₆) * (g * S₇) := h
        _ = e * f * g * (C * S₅ * S₆ * S₇) := by ac_rfl
        _ = e * f * g * (S₁ * S₂ * S₃ * S₄) := by rw [h']
    exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hc'
  have h1 : ∀ (Z : Over S) (z : Z.left), gm (1 : Z ⟶ splitTorus S X).left z ⊤ u = 1 := by
    intro Z z
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    have e := hu Z.left (1 : Z ⟶ splitTorus S X).left z J hJ
    rw [CubTriv.val_one σ hJ, CubTriv.val_one σ' hJ, _root_.mul_one] at e
    exact e.symm
  have he : ∀ (Z : Over S) (x : Z ⟶ splitTorus S X) (z : Z.left), gm (x⁻¹).left z ⊤ u = gm x.left z ⊤ u := by
    intro Z x z
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    have e := h Z x z J hJ
    have e' := h' Z x z J hJ
    rw [hu Z.left _ z J hJ, hu Z.left _ z J hJ, e'] at e
    apply mul_right_cancel (b := val P.sym (x ≫ i).left z J * val σ'.s x.left z J)
    exact e.trans (by ac_rfl)
  have hu1 := eq_one_of_even u h3 h1 he
  have hs : σ.s = σ'.s := GlobalTheory.TorusCoord.gen_eq_of_corr P.L.isLB σ.gen σ'.gen (corr_of_val P.L.isLB fun y J hJ => by
    rw [hu _ _ y J hJ, hu1, map_one, _root_.one_mul])
  obtain ⟨s₁, g₁, c₁⟩ := σ
  obtain ⟨s₂, g₂, c₂⟩ := σ'
  cases hs
  rfl
end GlobalTheory.CubTrivTorus
