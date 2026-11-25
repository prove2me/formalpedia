-- Prove2me | solution 1 for GlobalTheory.PsiWZeroPull.traceFormTwistIso_of_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:36:08.247826+00:00
-- url     : https://prove2.me/submissions/fd57970a-43c7-4eb0-8903-6a0a11fd548a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TraceFormTwistIsoOfPullback
import Theorems.Thm_GlobalTheory_PsiWZeroPull_rel_on
import Theorems.Thm_GlobalTheory_PsiWZeroPull_prod_four
import Theorems.Thm_GlobalTheory_DegPull_exists_pmaps
import Theorems.Thm_GlobalTheory_DegPull_pmaps_val
import Theorems.Thm_GlobalTheory_TauPull_val_psiW
import Theorems.Thm_GlobalTheory_TauPull_val_tau
import Theorems.Thm_GlobalTheory_TauPull_val_tauW
import Theorems.Thm_P2M_GlobalTheory_DegPull_exists_good__8835be56d0ec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
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
open GlobalTheory.PsiWZeroPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull GlobalTheory.DegPull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
set_option maxHeartbeats 1000000
namespace GlobalTheory.PsiWZeroPull
theorem _root_.solution (hD : IsPullDeg φ D D') {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X]
    (ιD : D.OAct O) (ιD' : D'.OAct O) (hx : ∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y)
    (hact : ∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a))
    (w0 : O) (h : TraceFormTwistIso D ιD w0) : TraceFormTwistIso D' ιD' w0 := by
  obtain ⟨u, hu, hn, hrel⟩ := h
  have gp := pull_grp hD
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  have ha : (ιD'.onB.act w0).left ≫ Φ = Φ ≫ (ιD.onB.act w0).left := by
    have a₂ : ((Over.pullback (specOf φ)).map (ιD.onB.act w0)).left ≫ pullback.fst D.P.A.hom (specOf φ) =
        pullback.fst _ _ ≫ (ιD.onB.act w0).left := pullback.lift_fst _ _ _
    show _ ≫ hD.e.hom.left ≫ _ = (hD.e.hom.left ≫ _) ≫ _
    rw [← Category.assoc, ← Over.comp_left, hact, Over.comp_left, Category.assoc, a₂, Category.assoc]
  have hψ : ∀ k : Fin 4, (![(padd D'.P.A (𝟙 _) (ιD'.onB.act w0)).left, 𝟙 D'.P.A.left, (ιD'.onB.act w0).left,
      (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → _) k ≫ Φ =
      Φ ≫ (![(padd D.P.A (𝟙 _) (ιD.onB.act w0)).left, 𝟙 D.P.A.left, (ιD.onB.act w0).left,
      (toUnit D.P.A ≫ η[D.P.A]).left] : Fin 4 → _) k := by
    have p1 : (pushPt gp.1.w (𝟙 D'.P.A)).left = Φ := Category.id_comp _
    intro k
    fin_cases k
    · have m : pushPt gp.1.w (𝟙 D'.P.A * ιD'.onB.act w0) =
          pushPt gp.1.w (𝟙 D'.P.A) * pushPt gp.1.w (ιD'.onB.act w0) := map_mul (pushHom gp D'.P.A) _ _
      have q : pushPt gp.1.w (ιD'.onB.act w0) = pushPt gp.1.w (𝟙 D'.P.A) ≫ ιD.onB.act w0 :=
        Over.OverMorphism.ext (by rw [Over.comp_left, p1]; exact ha)
      have m' : pushPt gp.1.w (𝟙 D'.P.A * ιD'.onB.act w0) =
          pushPt gp.1.w (𝟙 D'.P.A) ≫ (𝟙 D.P.A * ιD.onB.act w0) := by
        rw [m, q, MonObj.comp_mul, Category.comp_id]
      have := congrArg (fun q => q.left) m'
      simp only [Over.comp_left, p1] at this
      exact this
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact ha
    · have m : pushPt gp.1.w (1 : D'.P.A ⟶ D'.P.A) = pushPt gp.1.w (𝟙 D'.P.A) ≫ (1 : D.P.A ⟶ D.P.A) := by
        rw [MonObj.comp_one]; exact map_one (pushHom gp D'.P.A)
      have := congrArg (fun q => q.left) m
      simp only [Over.comp_left, p1] at this
      exact this
  obtain ⟨u', hu', pmu⟩ := exists_pmaps ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB Φ hψ u hu
  have vu : ∀ {T : Over (Spec (CommRingCat.of R'))} (x : T ⟶ D'.P.A) (z : T.left) J J', Good D.P.L z J →
      Good D'.P.L z J' → ∀ Ω : (T ⟶ D'.P.A) → (T.left.presheaf.stalk z)ˣ,
      (∀ x, Ω x = gw hD.w x.left z (J (x.left ≫ Φ)) (J' x.left)) → val u (x.left ≫ Φ) z J =
        Ω (x * (x ≫ ιD'.onB.act w0)) * (Ω x ^ 2)⁻¹ * (Ω (x ≫ ιD'.onB.act w0))⁻¹ * Ω 1 ^ 2 * val u' x.left z J' :=
    fun x z J J' hJ hJ' Ω hΩ => by
      rw [hΩ, hΩ, hΩ, hΩ]
      exact (pmaps_val hψ pmu x.left z hJ hJ').trans (congrArg₂ (· * ·)
        (prod_four (ιD'.onB.act w0) x (fun q => gw hD.w q z (J (q ≫ Φ)) (J' q))) rfl)
  refine ⟨u', hu', corr_of_val D'.P.isLB fun y J' hJ' => ?_, fun a => corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
    have := ιD'.onB.hom w0
    have e := vu (1 : 𝟙_ _ ⟶ D'.P.A) y J J' hJ hJ' _ (fun _ => rfl)
    have e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ D'.P.A).left = eSec D'.P.A := Category.id_comp _
    have b := val_corr hJ hn (specOf φ)
    rw [val_pull hJ, val_one, ← hD.he] at b
    rw [MonObj.one_comp, _root_.mul_one, e₁] at e
    rw [val_pull hJ', val_one, Category.id_comp]
    have e' := congrArg Additive.ofMul (b.symm.trans e)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
    let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ :=
      fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
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
    have cW : hD.g ≫ (cP D (TW hD.W) (hD.xe a)).left = (cP D' (TK R') a).left ≫ Φ := by
      have hx : (cP D' (TK R') a).left ≫ Φ = jK R' ≫ specOf φ ≫ (D.c (hD.xe a)).left := by
        rw [← hD.c_pr a, ← Category.assoc]; rfl
      rw [hx, ← Category.assoc (jK R'), ← hD.g_comm, Category.assoc]; rfl
    have cl : cP D' (TK R') a ≫ ιD'.onB.act w0 = cP D' (TK R') (w0 • a) := by
      rw [cP, cP, ιD'.c_lin, Category.assoc]
    have key := (val_mul hJ _ _ _).symm.trans ((val_corr hJ
      (rel_on hD.psiW ⟨_, (hD.g y).2⟩ u _ _ (hrel (hD.xe a))) hD.g).trans (val_mul hJ _ _ _))
    rw [val_pull hJ, cW, vu (cP D' (TK R') a) y J J' hJ hJ' Ω (fun _ => rfl), cl, val_tauW _ _ hJ, ← hx, ← map_add,
      vψ, vψ, vψ, vρ, cPoint_add] at key
    refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
    have b : val (LB.pullGen D'.P.L _ _ u' (D'.xK a)) (𝟙 _) y J' = val u' (cP D' (TK R') a).left y J' := by
      rw [val_pull hJ', Category.id_comp]; rfl
    rw [b, val_tau _ hJ']
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul key
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ⊢
    linear_combination (norm := abel) e'
end GlobalTheory.PsiWZeroPull
