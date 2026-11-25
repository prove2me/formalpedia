-- Prove2me | solution 1 for GlobalTheory.TauBalPull.tauBal_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:25:33.127573+00:00
-- url     : https://prove2.me/submissions/15a94690-7cc7-46f6-8d24-e4380577c7f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBalOfIsPullDeg
import Theorems.Thm_GlobalTheory_TauBalPull_tauW_bal
import Theorems.Thm_GlobalTheory_TauBalPull_push_comp
import Theorems.Thm_GlobalTheory_TauBalPull_push_inj
import Theorems.Thm_GlobalTheory_TauBalPull_ros_pull
import Theorems.Thm_GlobalTheory_TauPull_val_psiW
import Theorems.Thm_GlobalTheory_TauPull_val_tau
import Theorems.Thm_GlobalTheory_TauPull_val_tauW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_ros
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_ros
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
open GlobalTheory.TauBalPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
set_option maxHeartbeats 1000000
namespace GlobalTheory.TauBalPull
theorem _root_.solution (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {f g : D.P.A ⟶ D.P.A} {f' g' : D'.P.A ⟶ D'.P.A}
    [IsMonHom f] [IsMonHom g] (hr : RosatiAdj D.P.A D.P.L f g)
    (hf : f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f)
    (hg : g' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map g)
    {a b : D.X → D.X} {a' b' : D'.X → D'.X} (ha : ∀ y, hD.xe (a' y) = a (hD.xe y))
    (hb : ∀ y, hD.xe (b' y) = b (hD.xe y)) (ca : ∀ y, D.c (a y) = D.c y ≫ f) (cb : ∀ y, D.c (b y) = D.c y ≫ g)
    (hB : D.TauBal f g a b) : D'.TauBal f' g' a' b' := by
  intro u' hu' h₀' s s'
  obtain ⟨u, hu, h₀⟩ := exists_ros hG D.P.isAb D.P.isLB f g hr
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
  have ca' : cP D' (TK R') (a' s) = cP D' (TK R') s ≫ f' := push_inj hD (by
    rw [push_comp hD hf]
    refine (βc _).trans (Eq.trans ?_ (congrArg (· ≫ f) (βc s)).symm)
    rw [ha, cP, ca]; exact (Category.assoc _ _ _).symm)
  have cb' : cP D' (TK R') (b' s') = cP D' (TK R') s' ≫ g' := push_inj hD (by
    rw [push_comp hD hg]
    refine (βc _).trans (Eq.trans ?_ (congrArg (· ≫ g) (βc s')).symm)
    rw [hb, cP, cb]; exact (Category.assoc _ _ _).symm)
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
  let υ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := val₂ u (T := T) y J
  have ros : ∀ p q : TK R' ⟶ D'.P.A, υ (β p) (β q) =
      Ω ((p ≫ f') * q) * (Ω (p ≫ f'))⁻¹ * (Ω q)⁻¹ * (Ω (p * (q ≫ g')))⁻¹ * Ω p * Ω (q ≫ g') * val₂ u' y J' p q :=
    fun p q => (ros_pull hG hD hf hg u hu h₀ u' hu' h₀' (T := TK R') hJ hJ' p q).trans
      (congrArg₂ (· * ·) (prod_ros f' g' p q (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))) rfl)
  have vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) hD.g y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' :=
    fun χ => val_psiW hD hJ hJ' χ
  have key : val (hD.psiW.tau (a (hD.xe s)) (hD.xe s')) hD.g y J * υ (cP D T (hD.xe s)) (cP D T (hD.xe s')) =
      val (hD.psiW.tau (hD.xe s) (b (hD.xe s'))) hD.g y J :=
    tauW_bal hD.psiW u _ _ _ _ _ _ (hB u hu h₀ _ _) κ hJ
  rw [← βc, ← βc, ros, ← ha, ← hb, val_tauW _ _ hJ, val_tauW _ _ hJ, ← map_add, ← map_add,
    vψ, vψ, vψ, vψ, vψ, vψ, cPoint_add, cPoint_add, ca', cb'] at key
  refine (val_mul hJ' _ _ _).trans ?_
  have vu : val (LB.pullGen D'.P.L _ _ u' (D'.pt2 s s')) (𝟙 _) y J' =
      val₂ u' (T := TK R') y J' (cP D' _ s) (cP D' _ s') := by
    rw [val_pull hJ', Category.id_comp]; rfl
  rw [vu, val_tau _ hJ', val_tau _ hJ']
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'
end GlobalTheory.TauBalPull
