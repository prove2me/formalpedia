-- Prove2me | solution 1 for GlobalTheory.TauPull.val_psiW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:50:26.616505+00:00
-- url     : https://prove2.me/submissions/9b957b32-2db3-4660-8729-77c36ea7ea5f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
noncomputable section
open GlobalTheory
open GlobalTheory.TauPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
namespace GlobalTheory.TauPull
theorem _root_.solution (hD : IsPullDeg φ D D') {y : (TK R').left} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
    (χ : D'.X) : val (hD.psiW.psi (hD.xe χ)) hD.g y J =
      (gw hD.w (D'.xK χ) y (J (D'.xK χ ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (J' (D'.xK χ)))⁻¹ *
        val (D'.psi χ) (𝟙 _) y J' := by
  obtain ⟨b, hb, hc⟩ := hD.psi_pr χ
  have e₂ := (val_corr hJ hc (𝟙 _)).trans (val_pull hJ _ _ _)
  rw [Category.id_comp] at e₂
  rw [← e₂]
  obtain ⟨p, hp⟩ : ∃ p, p = J (D'.xK χ ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = J' (D'.xK χ) := ⟨_, rfl⟩
  rw [← hp, ← hq, val_of b _ y J (fun _ => p) (fun _ => by rw [Category.id_comp, hp]),
    val_of (D'.psi χ) _ y J' (fun _ => q) (fun _ => by rw [Category.id_comp, hq])]
  have m₁ : (𝟙 (TK R').left : _ ⟶ _) y ∈ D'.xK χ ⁻¹ᵁ ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U
      (fun _ => p) ⊓ D'.P.L.U q) := ⟨mem_pull.2 (hp ▸ hJ _), hq ▸ hJ' _⟩
  have e₁ := congrArg (gm (𝟙 (TK R').left) y
    (D'.xK χ ⁻¹ᵁ ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U (fun _ => p) ⊓ D'.P.L.U q)))
    (hb (fun _ => p) q)
  refine (gm_res _ y _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans ((congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK χ) y
      ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U (fun _ => p) ⊓ D'.P.L.U q) m₁ _)).trans ?_))
      (gm_res _ y _ m₁ _))))
  rw [Category.id_comp]
  exact zpow_neg_one _
end GlobalTheory.TauPull
