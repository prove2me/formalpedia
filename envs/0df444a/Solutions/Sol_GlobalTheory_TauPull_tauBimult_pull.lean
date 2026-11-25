-- Prove2me | solution 1 for GlobalTheory.TauPull.tauBimult_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:33:10.052362+00:00
-- url     : https://prove2.me/submissions/56d32be7-0c50-4625-8fcc-2654cfcc8aa0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Theorems.Thm_GlobalTheory_TauPull_val_tau
import Theorems.Thm_GlobalTheory_TauPull_val_tauW
import Theorems.Thm_GlobalTheory_TauPull_tauW_mul
import Theorems.Thm_GlobalTheory_TauPull_val_psiW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cub_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubeMap_comp_proj_three
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_hom_ext_triple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
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
set_option maxHeartbeats 1000000
namespace GlobalTheory.TauPull
theorem _root_.solution (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') (hB : D.TauBimult) : D'.TauBimult := by
  intro a a' b
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  choose J hJ₀ using fun χ : (TK R').left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ₀
  have gp := pull_grp hD
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TW hD.W := Over.homMk hD.g hD.g_comm
  let β : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ Φ = ((TK R').hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, Category.assoc])
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : TK R' ⟶ D'.P.A, θ (β a) (β b) (β c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' y J' a b c := by
    intro a b c
    have e := cub_pull hG hD (T' := TK R') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))) rfl)
  have vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) hD.g y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' :=
    fun χ => val_psiW hD hJ hJ' χ
  have vρ : val (D.rigW hD.W) hD.g y J = Ω 1 * val D'.rigK (𝟙 _) y J' := by
    have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le Φ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
    have a₂ : ((TK R').hom ≫ specOf φ) ≫ eSec D.P.A = (1 : TK R' ⟶ D'.P.A).left ≫ Φ :=
      congrArg (fun q => q.left) (map_one (pushHom gp (TK R'))).symm
    have e := pm _ (TK R').hom y (fun _ => J ((1 : TK R' ⟶ D'.P.A).left ≫ Φ))
      (fun _ => J' (1 : TK R' ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)
    rw [Fintype.prod_unique, zpow_one] at e
    have b₁ : hD.g ≫ (toUnit (TW hD.W)).left = (TK R').hom ≫ specOf φ := hD.g_comm
    have b₂ : 𝟙 _ ≫ (toUnit (TK R')).left = (TK R').hom := Category.id_comp _
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
    rw [b₁, b₂]
    exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e
  have key : val (hD.psiW.tau (hD.xe a + hD.xe a') (hD.xe b)) hD.g y J *
      θ (cP D T (hD.xe a)) (cP D T (hD.xe a')) (cP D T (hD.xe b)) =
      val (hD.psiW.tau (hD.xe a) (hD.xe b)) hD.g y J * val (hD.psiW.tau (hD.xe a') (hD.xe b)) hD.g y J :=
    tauW_mul hB hD.psiW κ hJ _ _ _
  rw [← βc, ← βc, ← βc, cub, val_tauW _ _ hJ, val_tauW _ _ hJ, val_tauW _ _ hJ, ← map_add, ← map_add, ← map_add,
    ← map_add, vψ, vψ, vψ, vψ, vψ, vψ, vψ, vρ, cPoint_add, cPoint_add, cPoint_add, cPoint_add] at key
  refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  refine (congrArg₂ (· * ·) rfl (val_cub D'.cub (𝟙 (TK R')) hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b))).trans ?_
  rw [Category.id_comp, Category.id_comp, Category.id_comp, val_tau _ hJ', val_tau _ hJ', val_tau _ hJ']
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'
end GlobalTheory.TauPull
