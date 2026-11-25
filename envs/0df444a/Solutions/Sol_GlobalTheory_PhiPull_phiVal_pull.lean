-- Prove2me | solution 1 for GlobalTheory.PhiPull.phiVal_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:00.262131+00:00
-- url     : https://prove2.me/submissions/e29ba844-dd50-44eb-9a57-d16cb9bb3e88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Theorems.Thm_GlobalTheory_PhiPull_units_rel
import Theorems.Thm_GlobalTheory_PhiPull_push_cP
import Theorems.Thm_GlobalTheory_PhiPull_cub_rel
import Theorems.Thm_GlobalTheory_PhiPull_liftB_fst
import Theorems.Thm_GlobalTheory_PhiPull_liftB_pr
import Theorems.Thm_GlobalTheory_PhiPull_liftB_pt
import Theorems.Thm_GlobalTheory_PhiPull_liftB_tr
import Theorems.Thm_GlobalTheory_PhiPull_sval_rel
import Theorems.Thm_GlobalTheory_DegPull_pmaps_val
import Theorems.Thm_P2M_GlobalTheory_DegPull_exists_good__8835be56d0ec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_pr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
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
open GlobalTheory.PhiPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
variable (hD : IsPullDeg φ D D') (hT : (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom)
  {Θ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left}
  (hΘ₁ : Θ ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R') F) D'.P.A).left)
  (hΘ₂ : Θ ≫ (DegPre.prB D F).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  {T' : Over (Spec (CommRingCat.of R'))}
set_option maxHeartbeats 1000000
include hT hΘ₁ hΘ₂
namespace GlobalTheory.PhiPull
theorem _root_.solution (hG : GlobalFnsSt) {k : ℕ} (p₀ : QkPt D F k) (p₀' : QkPt D' F k) (hy : p₀'.y = hD.xe.symm p₀.y)
    (hg : IsPullGtF φ hD F p₀.g p₀'.g)
    (ν : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₀.g.b) (DegPre.lineε k)))
    (ν' : LB.Gen (LB.LinComb D'.P.L (DegPre.lineφ D' F p₀'.g.b) (DegPre.lineε k)))
    (hl : ∀ i, DegPre.lineφ D' F p₀'.g.b i ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = 𝟙 _ ≫ DegPre.lineφ D F p₀.g.b i)
    (hν : PMaps hD.w (DegPre.lineφ D' F p₀'.g.b) (DegPre.lineφ D F p₀.g.b) (DegPre.lineε k) ν' ν (𝟙 _))
    (s s₂ : Fam D F k) (s' s₂' : Fam D' F k)
    (H₁ : (∀ x : D'.X, ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι)
      (q : Fin 4 → D'.P.L.ι), (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) →
      (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) →
      gs (r ≫ Θ) z (LB.wchart D.P.L (DegPre.famφ D F (hD.xe x)) p) ((s.s (hD.xe x)).f p) =
        (∏ κ, gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
          gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) ((s'.s x).f q)))
    (H₂ : (∀ x : D'.X, ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι)
      (q : Fin 4 → D'.P.L.ι), (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) →
      (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) →
      gs (r ≫ Θ) z (LB.wchart D.P.L (DegPre.famφ D F (hD.xe x)) p) ((s₂.s (hD.xe x)).f p) =
        (∏ κ, gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
          gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) ((s₂'.s x).f q)))
    (H : PhiVal p₀ ν s.s s₂.s) : PhiVal p₀' ν' s'.s s₂'.s := by
  rintro α _ rfl T' ρ z J' hJ'
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB z
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk z)ˣ,
      Ω = fun x => gw hD.w x.left z (J (x.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' x.left) := ⟨_, rfl⟩
  have hb := hg.1
  have e := H (hD.xe α) (hD.xe (α + p₀'.y)) (by rw [map_add, hy, AddEquiv.apply_symm_apply]) _ (liftB hT hΘ₁ ρ) z J hJ
  have v₂ := sval_rel hD hT hΘ₁ hΘ₂ _ _ _ (H₂ (α + p₀'.y)) ρ hJ hJ' Ω hΩ
  have v₁ := sval_rel hD hT hΘ₁ hΘ₂ _ _ _ (H₁ α) (ρ ≫ DegPre.trPt D' F p₀'.g.b) hJ hJ' Ω hΩ
  let σ : T' ⟶ TF (R := R') F := ρ ≫ fst _ _
  have m₁ : ρ ≫ fst (TF (R := R') F) D'.P.A ≫ p₀'.g.b = σ ≫ p₀'.g.b := (Category.assoc _ _ _).symm
  have cy : cP D' T' (α + p₀'.y) = cP D' T' α * (σ ≫ p₀'.g.b) ^ k := by
    rw [cPoint_add, ← comp_cP D' σ p₀'.y, cPoint_y]
    exact congrArg _ (map_pow (preHom σ) _ _)
  have tp : (ρ ≫ DegPre.trPt D' F p₀'.g.b) ≫ DegPre.prB D' F = (ρ ≫ DegPre.prB D' F) * (σ ≫ p₀'.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, m₁]
  rw [cy] at v₂
  rw [tp, ← liftB_tr hD hT hΘ₁ hΘ₂ ρ hb] at v₁
  have vu : @Eq (T'.left.presheaf.stalk z)ˣ (uVal D F k (hD.xe α) p₀.g.b (liftB hT hΘ₁ ρ) z J)
      (cubN (th D (T := Over.mk (T'.hom ≫ spMap φ)) z J) k (pushHom (pull_grp hD) T' (cP D' T' α))
        (pushHom (pull_grp hD) T' (σ ≫ p₀'.g.b)) (pushHom (pull_grp hD) T' (ρ ≫ DegPre.prB D' F)) *
      (th D (T := Over.mk (T'.hom ≫ spMap φ)) z J (pushHom (pull_grp hD) T' (cP D' T' α))
        (pushHom (pull_grp hD) T' (ρ ≫ DegPre.prB D' F)) (pushHom (pull_grp hD) T' (σ ≫ p₀'.g.b)))⁻¹) := by
    rw [uVal, liftB_pt hD hT hΘ₁ ρ hb, liftB_pr hD hT hΘ₁ hΘ₂, push_cP, m₁]
  have vg : @Eq (T'.left.presheaf.stalk z)ˣ (val (p₀.g.s (hD.xe α)) σ.left z J)
      ((Ω (cP D' T' α * (σ ≫ p₀'.g.b)))⁻¹ * Ω (cP D' T' α) * Ω (σ ≫ p₀'.g.b) * (Ω 1)⁻¹ *
        val (p₀'.g.s α) σ.left z J') := by
    obtain ⟨hψ, hm⟩ := hg.2 α
    have pm := (maps_iff hD.w _ _ _ (p₀'.g.s α) (p₀.g.s (hD.xe α)) (𝟙 _) _
      (GeneratorPullback.pullAlong_le D.P.L _ (𝟙 _) _ _ hψ) (fun _ => rfl)).1 hm
    have c := DegPull.pmaps_val hψ pm σ.left z hJ hJ'
    erw [Category.comp_id] at c
    have p := prod_gt p₀'.g.b α (fun q => gw hD.w (σ.left ≫ q) z (J ((σ.left ≫ q) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' (σ.left ≫ q)))
    refine c.trans (congrArg₂ (· * ·) (p.trans ?_) rfl)
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, comp_cP,
      MonObj.comp_one, hΩ]
  have vν : @Eq (T'.left.presheaf.stalk z)ˣ (val ν σ.left z J)
      (Ω 1 ^ (k : ℤ) * Ω (σ ≫ p₀'.g.b) ^ (-(k : ℤ)) * val ν' σ.left z J') := by
    have c := DegPull.pmaps_val hl hν σ.left z hJ hJ'
    erw [Category.comp_id] at c
    refine c.trans (congrArg₂ (· * ·) ((Fin.prod_univ_two _).trans ?_) rfl)
    have e₀ : σ.left ≫ DegPre.lineφ D' F p₀'.g.b 0 = (1 : T' ⟶ D'.P.A).left :=
      congrArg (fun q : T' ⟶ D'.P.A => q.left) (MonObj.comp_one (M := D'.P.A) σ)
    have e₁ : σ.left ≫ DegPre.lineφ D' F p₀'.g.b 1 = (σ ≫ p₀'.g.b).left := rfl
    rw [e₀, e₁, hΩ]
    rfl
  have vm : @Eq (T'.left.presheaf.stalk z)ˣ
      (val (LB.mulGen D.P.L _ _ _ _ (p₀.g.s (hD.xe α)) ν) (liftB hT hΘ₁ ρ ≫ fst _ _).left z J)
      (val (p₀.g.s (hD.xe α)) σ.left z J * val ν σ.left z J) := by
    rw [liftB_fst]; exact val_mul hJ _ _ _
  have key := units_rel (pushHom (pull_grp hD) T') Ω (cub_rel hG hD hJ hJ' Ω hΩ) k (cP D' T' α) (σ ≫ p₀'.g.b)
    (ρ ≫ DegPre.prB D' F) (val (p₀'.g.s α) σ.left z J') (val ν' σ.left z J')
  have fin := v₂.symm.trans (e.trans (congrArg₂ (· * ·) v₁ (congrArg Units.val
    (congrArg₂ (· * ·) vu (vm.trans (congrArg₂ (· * ·) vg vν))))))
  have alg : ∀ {S : Type} [CommRing S] (A₁ A₂ u u' : Sˣ) (a b : S), A₁ * u = A₂ * u' →
      A₂.val * b = A₁.val * a * u.val → b = a * u'.val := by
    intro S _ A₁ A₂ u u' a b h₁ h₂
    rw [mul_right_comm, ← Units.val_mul, h₁, Units.val_mul, _root_.mul_assoc] at h₂
    rw [(Units.mul_right_inj _).1 h₂, mul_comm]
  refine (alg _ _ _ _ _ _ key fin).trans ?_
  rw [val_mul hJ', uVal, m₁]
end GlobalTheory.PhiPull
