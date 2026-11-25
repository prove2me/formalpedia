-- Prove2me | solution 1 for GlobalTheory.FamPull.fe_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:12:36.99609+00:00
-- url     : https://prove2.me/submissions/f97926a0-237e-4bd5-a099-9438521852dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
import Theorems.Thm_P2M_GlobalTheory_FamPull_comp_fam_B_04005a41a3d0
import Theorems.Thm_GlobalTheory_FamPull_prod_famB
import Theorems.Thm_GlobalTheory_FamPull_fe_on
import Theorems.Thm_GlobalTheory_FamPull_val_psiW
import Theorems.Thm_GlobalTheory_FamPull_cubN_twist
import Theorems.Thm_GlobalTheory_FamPull_cancel_units
import Theorems.Thm_GlobalTheory_TauPull_val_psiW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cub_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubeMap_comp_proj_three
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_hom_ext_triple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of
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
open GlobalTheory.FamPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
set_option maxHeartbeats 1000000
namespace GlobalTheory.FamPull
theorem _root_.solution (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {k : ℕ} (F : Fam D (FractionRing R) k) (f : ∀ α, D.SecB k α)
    (f' : ∀ α, D'.SecB k α)
    (hs : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F.s α) (D.famφB α)
      (DegPre.famε k) (f α) (DegPre.prB D (FractionRing R)).left 1)
    (hf : ∀ (x : D'.X) (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι),
      (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.P.L.U (p κ)) →
      (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) →
      gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) z (LB.wchart D.P.L (D.famφB (hD.xe x)) p)
          ((f (hD.xe x)).f p) = (∏ κ, gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
        gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' x).f q))
    (mu α : D'.X) {T' : Over (Spec (CommRingCat.of R'))} (σ : T' ⟶ TK R') (x : T' ⟶ D'.P.A) {y : T'.left} {J'}
    (hJ' : Good D'.P.L y J') :
    sval (f' (α + k • mu)) x.left y J' = sval (f' α) (x * cP D' T' mu).left y J' *
      (feUnit D' k mu α x y J' (fun χ => val (D'.psi χ) σ.left y J') (val D'.rigK σ.left y J')).val := by
  choose J hJ₀ using fun χ : T'.left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ₀
  have gp := pull_grp hD
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (T'.hom ≫ spMap φ)
  have hσ : σ.left ≫ jK R' = T'.hom := Over.w σ
  have hκ : (σ.left ≫ hD.g) ≫ hD.W.ι = T'.hom ≫ spMap φ := by
    rw [Category.assoc, hD.g_comm, ← Category.assoc, hσ]
  let κ : T ⟶ TW hD.W := Over.homMk (σ.left ≫ hD.g) hκ
  let β : (T' ⟶ D'.P.A) →* (T ⟶ D.P.A) := pushHom gp T'
  have βl : ∀ x, (β x).left = x.left ≫ Φ := fun _ => rfl
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show (T'.hom ≫ (D'.c χ).left) ≫ Φ = (T'.hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, Category.assoc])
  let Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk y)ˣ := fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T'.left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : T' ⟶ D'.P.A, θ (β a) (β b) (β c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' y J' a b c := by
    intro a b c
    have e := cub_pull hG hD (T' := T') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))) rfl)
  have vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) (σ.left ≫ hD.g) y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) σ.left y J' :=
    fun χ => by
      have a₁ : σ.left ≫ D'.xK χ = (cP D' T' χ).left := congrArg (fun q => q.left) (comp_cP D' σ χ)
      rw [val_psiW hD σ.left hJ hJ' χ, a₁]
  have vρ : val (D.rigW hD.W) (σ.left ≫ hD.g) y J = Ω 1 * val D'.rigK σ.left y J' := by
    have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le Φ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
    have a₂ : (T'.hom ≫ specOf φ) ≫ eSec D.P.A = (1 : T' ⟶ D'.P.A).left ≫ Φ :=
      congrArg (fun q => q.left) (map_one β).symm
    have e := pm _ T'.hom y (fun _ => J ((1 : T' ⟶ D'.P.A).left ≫ Φ))
      (fun _ => J' (1 : T' ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)
    rw [Fintype.prod_unique, zpow_one] at e
    have b₁ : (σ.left ≫ hD.g) ≫ (toUnit (TW hD.W)).left = T'.hom ≫ specOf φ := hκ
    have b₂ : σ.left ≫ (toUnit (TK R')).left = T'.hom := hσ
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
    rw [b₁, b₂]
    exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e
  have vf : ∀ χ (x : T' ⟶ D'.P.A), sval (f (hD.xe χ)) (x.left ≫ Φ) y J =
      (Ω x ^ ((k : ℤ) - 1) * Ω (cP D' T' χ * x) * (Ω (cP D' T' χ))⁻¹ * Ω 1).val * sval (f' χ) x.left y J' := fun χ x => by
    have c : ∀ i, (x.left ≫ Φ) ≫ D.famφB (hD.xe χ) i = (x.left ≫ D'.famφB χ i) ≫ Φ := fun i => by
      refine (comp_famφB D (β x) (hD.xe χ) i).trans ?_
      rw [comp_famφB, ← βl, ← βc, ← map_mul, ← map_one β]
      fin_cases i <;> rfl
    rw [sval_of _ _ y J (fun i => J ((x.left ≫ D'.famφB χ i) ≫ Φ)) (fun i => congrArg J (c i))]
    refine (hf χ _ x.left y _ (fun i => J' (x.left ≫ D'.famφB χ i)) (fun i => hJ ((x.left ≫ D'.famφB χ i) ≫ Φ))
      (fun i => hJ' (x.left ≫ D'.famφB χ i))).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
    exact prod_famB D' x χ k (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))
  have cN : cubN θ k (β (cP D' T' α)) (β (cP D' T' mu)) (β x) =
      cubN (fun a b c => θ (β a) (β b) (β c)) k (cP D' T' α) (cP D' T' mu) x :=
    Finset.prod_congr rfl fun i _ => by simp only [map_mul, map_pow]
  have key₀ := fe_on hG hD.psiW F f hs (hD.xe mu) (hD.xe α) κ (β x) (z := y) hJ
  rw [← map_nsmul, ← map_add, ← βc, ← map_mul, feUnit, ← βc, ← βc, ← map_add] at key₀
  have key : sval (f (hD.xe (α + k • mu))) (x.left ≫ Φ) y J = sval (f (hD.xe α)) ((x * cP D' T' mu).left ≫ Φ) y J *
      (cubN θ k (β (cP D' T' α)) (β (cP D' T' mu)) (β x) * (θ (β (cP D' T' α)) (β x) (β (cP D' T' mu)))⁻¹ *
        (val (hD.psiW.psi (hD.xe (mu + α))) (σ.left ≫ hD.g) y J * (val (hD.psiW.psi (hD.xe mu)) (σ.left ≫ hD.g) y J)⁻¹ *
          (val (hD.psiW.psi (hD.xe α)) (σ.left ≫ hD.g) y J)⁻¹ * (val (D.rigW hD.W) (σ.left ≫ hD.g) y J)⁻¹ *
          (val (hD.psiW.psi (hD.xe mu)) (σ.left ≫ hD.g) y J ^ k * val (D.rigW hD.W) (σ.left ≫ hD.g) y J ^ k))).val := key₀
  rw [vf, vf, cN, cubN_twist _ _ Ω cub, cub, vψ, vψ, vψ, vρ] at key
  refine cancel_units key ?_
  rw [feUnit, cPoint_add, cPoint_add, cPoint_nsmul, mul_comm (cP D' T' mu) (cP D' T' α), ← _root_.mul_assoc (cP D' T' α),
    mul_comm (cP D' T' mu) x]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
  module
end GlobalTheory.FamPull
