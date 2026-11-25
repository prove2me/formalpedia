-- Prove2me | solution 1 for GlobalTheory.PhiSpec.special_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:11:27.393412+00:00
-- url     : https://prove2.me/submissions/6f7e09f6-9fc5-49ed-9fba-fc2f04b34013

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiSpecialises
import Theorems.Thm_GlobalTheory_PhiSpec_liftB_fst
import Theorems.Thm_GlobalTheory_PhiSpec_liftB_pr
import Theorems.Thm_GlobalTheory_PhiSpec_liftB_pt
import Theorems.Thm_GlobalTheory_PhiSpec_liftB_tr
import Theorems.Thm_GlobalTheory_PhiSpec_sval_rel
import Theorems.Thm_GlobalTheory_PhiSpec_secMaps_of_sval
import Theorems.Thm_GlobalTheory_PhiSpec_gt_comm
import Theorems.Thm_GlobalTheory_PhiSpec_line_comm
import Theorems.Thm_GlobalTheory_DegPull_pmaps_val
import Theorems.Thm_GlobalTheory_PhiPull_cub_rel
import Theorems.Thm_GlobalTheory_PhiPull_liftB_fst
import Theorems.Thm_GlobalTheory_PhiPull_liftB_pr
import Theorems.Thm_GlobalTheory_PhiPull_liftB_pt
import Theorems.Thm_GlobalTheory_PhiPull_liftB_tr
import Theorems.Thm_GlobalTheory_PhiPull_push_cP
import Theorems.Thm_GlobalTheory_PhiPull_sval_rel
import Theorems.Thm_GlobalTheory_PhiPull_units_rel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_pr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_gt


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
open GlobalTheory.PhiSpec
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {T : Over (Spec (CommRingCat.of R))} {F : Type} [Field F] [Algebra (FractionRing R') F]
  (hD : IsPullDeg φ D D') {h : (TF (R := R') F).left ⟶ T.left} (hT : (TF (R := R') F).hom ≫ spMap φ = h ≫ T.hom)
  {Θ : (DegPre.BF D' F).left ⟶ (T ⊗ D.P.A).left}
  (hΘ₁ : Θ ≫ (fst T D.P.A).left = (fst (TF (R := R') F) D'.P.A).left ≫ h)
  (hΘ₂ : Θ ≫ (snd T D.P.A).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  {T' : Over (Spec (CommRingCat.of R'))}
set_option maxHeartbeats 1000000
include hT hΘ₁ hΘ₂
namespace GlobalTheory.PhiSpec
theorem _root_.solution (hG : GlobalFnsSt) {k : ℕ} (y : D.X) (gp : GtPt D T) (p : QkPt D' F k)
    (hy : p.y = hD.xe.symm y) (hb : p.g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ gp.b.left)
    (hg : ∀ χ, PMaps hD.w (DegPre.gtφ D' F p.g.b χ) (DegPre.gtφT D T gp.b (hD.xe χ)) DegPre.gtε (p.g.s χ)
      (gp.s (hD.xe χ)) h)
    (w : LB.Gen (LB.LinComb D.P.L (lineT D gp.b) (DegPre.lineε k)))
    (ν' : LB.Gen (LB.LinComb D'.P.L (DegPre.lineφ D' F p.g.b) (DegPre.lineε k)))
    (hν : PMaps hD.w (DegPre.lineφ D' F p.g.b) (lineT D gp.b) (DegPre.lineε k) ν' w h)
    (g g₂ : ∀ α, SecT D T k α) (s' s₂' : Fam D' F k)
    (H₁ : ∀ x, SecMaps hD Θ x (g (hD.xe x)) (s'.s x)) (HT : PhiT y gp w g g₂) (H : PhiVal p ν' s'.s s₂'.s)
    (β : D'.X) : SecMaps hD Θ β (g₂ (hD.xe β)) (s₂'.s β) := by
  obtain ⟨α, rfl⟩ : ∃ α, α + p.y = β := ⟨β - p.y, sub_add_cancel _ _⟩
  refine secMaps_of_sval hD hT hΘ₁ hΘ₂ _ _ _ fun T' ρ z J J' hJ hJ' Ω hΩ => ?_
  have e := HT (hD.xe α) (hD.xe (α + p.y)) (by rw [map_add, hy, AddEquiv.apply_symm_apply]) _ (liftB hT hΘ₁ ρ) z J hJ
  have e' := H α _ rfl T' ρ z J' hJ'
  have v₁ := sval_rel hD hT hΘ₁ hΘ₂ _ _ _ (H₁ α) (ρ ≫ DegPre.trPt D' F p.g.b) hJ hJ' Ω hΩ
  let σ : T' ⟶ TF (R := R') F := ρ ≫ fst _ _
  have m₁ : ρ ≫ fst (TF (R := R') F) D'.P.A ≫ p.g.b = σ ≫ p.g.b := (Category.assoc _ _ _).symm
  have cy : cP D' T' (α + p.y) = cP D' T' α * (σ ≫ p.g.b) ^ k := by
    rw [cPoint_add, ← comp_cP D' σ p.y, cPoint_y]
    exact congrArg _ (map_pow (preHom σ) _ _)
  have tp : (ρ ≫ DegPre.trPt D' F p.g.b) ≫ DegPre.prB D' F = (ρ ≫ DegPre.prB D' F) * (σ ≫ p.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, m₁]
  rw [cy]
  rw [tp, ← liftB_tr hD hT hΘ₁ hΘ₂ ρ hb] at v₁
  have vu : @Eq (T'.left.presheaf.stalk z)ˣ (uT D k (hD.xe α) gp.b (liftB hT hΘ₁ ρ) z J)
      (cubN (th D (T := Over.mk (T'.hom ≫ spMap φ)) z J) k (pushHom (pull_grp hD) T' (cP D' T' α))
        (pushHom (pull_grp hD) T' (σ ≫ p.g.b)) (pushHom (pull_grp hD) T' (ρ ≫ DegPre.prB D' F)) *
      (th D (T := Over.mk (T'.hom ≫ spMap φ)) z J (pushHom (pull_grp hD) T' (cP D' T' α))
        (pushHom (pull_grp hD) T' (ρ ≫ DegPre.prB D' F)) (pushHom (pull_grp hD) T' (σ ≫ p.g.b)))⁻¹) := by
    rw [uT, liftB_pt hD hT hΘ₁ ρ hb, liftB_pr hD hT hΘ₁ hΘ₂, PhiPull.push_cP, m₁]
  have vg : @Eq (T'.left.presheaf.stalk z)ˣ (val (gp.s (hD.xe α)) (liftB hT hΘ₁ ρ ≫ fst _ _).left z J)
      ((Ω (cP D' T' α * (σ ≫ p.g.b)))⁻¹ * Ω (cP D' T' α) * Ω (σ ≫ p.g.b) * (Ω 1)⁻¹ *
        val (p.g.s α) σ.left z J') := by
    have c := DegPull.pmaps_val (gt_comm hD hT hb α) (hg α) σ.left z hJ hJ'
    have pr := prod_gt p.g.b α (fun q => gw hD.w (σ.left ≫ q) z (J ((σ.left ≫ q) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' (σ.left ≫ q)))
    rw [liftB_fst]
    refine c.trans (congrArg₂ (· * ·) (pr.trans ?_) rfl)
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, comp_cP,
      MonObj.comp_one, hΩ]
  have vν : @Eq (T'.left.presheaf.stalk z)ˣ (val w (liftB hT hΘ₁ ρ ≫ fst _ _).left z J)
      (Ω 1 ^ (k : ℤ) * Ω (σ ≫ p.g.b) ^ (-(k : ℤ)) * val ν' σ.left z J') := by
    have c := DegPull.pmaps_val (line_comm hD hT hb) hν σ.left z hJ hJ'
    rw [liftB_fst]
    refine c.trans (congrArg₂ (· * ·) ((Fin.prod_univ_two _).trans ?_) rfl)
    have e₀ : σ.left ≫ DegPre.lineφ D' F p.g.b 0 = (1 : T' ⟶ D'.P.A).left :=
      congrArg (fun q : T' ⟶ D'.P.A => q.left) (MonObj.comp_one (M := D'.P.A) σ)
    have e₁ : σ.left ≫ DegPre.lineφ D' F p.g.b 1 = (σ ≫ p.g.b).left := rfl
    rw [e₀, e₁, hΩ]
    rfl
  have key := PhiPull.units_rel (pushHom (pull_grp hD) T') Ω (PhiPull.cub_rel hG hD hJ hJ' Ω hΩ) k (cP D' T' α)
    (σ ≫ p.g.b) (ρ ≫ DegPre.prB D' F) (val (p.g.s α) σ.left z J') (val ν' σ.left z J')
  have fin := e.trans (congrArg₂ (· * ·) v₁ (congrArg Units.val
    (congrArg₂ (· * ·) vu (congrArg₂ (· * ·) vg vν))))
  have alg : ∀ {S : Type} [CommRing S] (A₁ A₂ u u' : Sˣ) (a : S), A₁ * u = A₂ * u' →
      A₁.val * a * u.val = A₂.val * (a * u'.val) := by
    intro S _ A₁ A₂ u u' a h₁
    rw [mul_right_comm, ← Units.val_mul, h₁, Units.val_mul, _root_.mul_assoc, mul_comm a]
  rw [val_mul hJ', uVal, m₁] at e'
  refine fin.trans ((alg _ _ _ _ _ key).trans ?_)
  rw [e']
end GlobalTheory.PhiSpec
