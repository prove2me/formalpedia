-- Prove2me | solution 1 for GlobalTheory.ConstFam.val_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:26:38.165987+00:00
-- url     : https://prove2.me/submissions/2f04c2b9-6be8-4ce9-8127-36264c37b292

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
import Theorems.Thm_GlobalTheory_ConstFam_gs_comp_stalkMap
import Theorems.Thm_GlobalTheory_ConstFam_gm_comp_stalkMap
import Theorems.Thm_GlobalTheory_ConstFam_stalkMap_injective_of_flat
import Theorems.Thm_GlobalTheory_ConstFam_toStk_eq
import Theorems.Thm_GlobalTheory_ConstFam_xUnit_zpow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_genRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)
variable [Algebra (FractionRing k) F]
  (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) = constF k F x)
  {y : Sp F} {J₀ : (Sp F ⟶ a.D₀.P.A.left) → a.D₀.P.L.ι} {J : (Sp F ⟶ P.toPre.P.A.left) → P.toPre.P.L.ι}
  (hJ₀ : Good a.D₀.P.L y J₀) (hJ : Good P.toPre.P.L y J)
include hW hF hJ₀ hJ
namespace GlobalTheory.ConstFam
theorem _root_.solution (χ : a.D₀.X) : val (L := P.toPre.P.L) (P.toPre.psi (e χ)) (jFK (R := PowerSeries k) F) y J =
    wVal w y J₀ J (cP P.toPre (TF (R := PowerSeries k) F) (e χ)).left *
      (xUnit k F y ^ (a.be χ χ / 2) * val (L := a.D₀.P.L) (a.D₀.psi χ) (jFK (R := k) F) y J₀) := by
  let F' := AlgebraicClosure F
  let σ : Sp F' ⟶ Sp F := spMap (algebraMap F F')
  have : Flat σ := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField F) _
  have z : Sp F' := (default : PrimeSpectrum F')
  have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain rfl : y = σ z := Subsingleton.elim _ _
  have s₁ : jFK (R := PowerSeries k) F' = σ ≫ jFK (R := PowerSeries k) F := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have s₂ : jFK (R := k) F' = σ ≫ jFK (R := k) F := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨hp, hv⟩ := (genRel_iff w _ _ _ z).1 (hW.2.2.2.2.2 F' _ (fun x => by
    rw [IsScalarTower.algebraMap_apply (FractionRing k) F F', hF,
      IsScalarTower.algebraMap_apply (FractionRing (PowerSeries k)) F F']; rfl) rfl χ)
  let m : Sp F ⟶ P.toPre.P.A.left := (cP P.toPre (TF (R := PowerSeries k) F) (e χ)).left
  have a₁ : jFK (R := PowerSeries k) F ≫ P.toPre.xK (e χ) = m := (Category.assoc _ _ _).symm
  have a₁' : jFK (R := PowerSeries k) F' ≫ ptK (P.toPre.c (e χ)) = σ ≫ m := by rw [s₁, Category.assoc, a₁]
  have a₂ : jFK (R := k) F ≫ a.D₀.xK χ = m ≫ φ := by
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (a.D₀.c χ).left) ?_)).trans
      (congrArg (fun q => q.left) (push_cP hW (TF (R := PowerSeries k) F) χ)).symm
    show (TF (R := k) F).hom = (TF (R := PowerSeries k) F).hom ≫ _
    rw [TF_hom, TF_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext hF)
  have m₁ : jFK (R := PowerSeries k) F (σ z) ∈ LB.wchart P.toPre.P.L (K := PUnit) (fun _ => ptK (P.toPre.c (e χ)))
      (fun _ => J m) := Set.mem_iInter.2 fun _ => by have := hJ m; rw [← a₁] at this ⊢; exact this
  have m₂ : jFK (R := k) F (σ z) ∈ LB.wchart a.D₀.P.L (K := PUnit) (fun _ => ptK (a.D₀.c χ))
      (fun _ => J₀ (m ≫ φ)) := Set.mem_iInter.2 fun _ => by have := hJ₀ (m ≫ φ); rw [← a₂] at this ⊢; exact this
  have H := hv (fun _ => J m) (fun _ => J₀ (m ≫ φ)) (fun _ => by rw [a₁']; exact hJ₀ (m ≫ φ))
    (fun _ => by rw [a₁']; exact hJ m)
  rw [gm_pullGen _ _ _ _ _ _ _ _ (Set.mem_iInter.2 fun _ => by
      show (jFK (R := PowerSeries k) F' ≫ ptK (P.toPre.c (e χ))) z ∈ P.toPre.P.L.U (J m)
      rw [a₁']; exact hJ m),
    gm_pullGen _ _ _ _ _ _ _ _ (Set.mem_iInter.2 fun _ => by
      show (jFK (R := k) F' ≫ ptK (a.D₀.c χ)) z ∈ a.D₀.P.L.U (J₀ (m ≫ φ))
      rw [s₂, Category.assoc, a₂]; exact hJ₀ (m ≫ φ)),
    Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp, a₁', s₁, s₂] at H
  have g₁ := gm_comp_stalkMap σ _ z _ m₁ ((P.toPre.psi (e χ)).s fun _ => J m)
  have g₂ := gm_comp_stalkMap σ _ z _ m₂ ((a.D₀.psi χ).s fun _ => J₀ (m ≫ φ))
  have g₃ := gm_comp_stalkMap σ m z ((a.D₀.P.L.pull φ).U (fun _ => J₀ (m ≫ φ)) ⊓ P.toPre.P.L.U (J m))
    ⟨mem_pull.2 (hJ₀ (m ≫ φ)), hJ m⟩ (w.s (fun _ => J₀ (m ≫ φ), J m))
  replace H := (congrArg Units.val (congrArg₂ (· * ·) (congrArg (·⁻¹) g₃) g₁)).symm.trans
    (H.trans (congrArg₂ (· * ·) rfl (congrArg Units.val g₂)))
  have hx : toStk z (algebraMap (FractionRing (PowerSeries k)) F' (algebraMap (PowerSeries k) _ PowerSeries.X) ^
      (a.be χ χ / 2)) = (σ.stalkMap z).hom (xUnit k F (σ z) ^ (a.be χ χ / 2)).val := by
    rw [xUnit_zpow, toStk_eq, toStk_eq, IsScalarTower.algebraMap_apply (FractionRing (PowerSeries k)) F F',
      ← map_zpow₀, ← constVal_specMap, Category.id_comp]
    exact (congrArg (fun q => gs q z ⊤ _) (Category.comp_id σ).symm).trans (gs_comp_stalkMap σ (𝟙 _) z ⊤ trivial _)
  rw [hx] at H
  rw [val_of _ _ _ J (fun _ => J m) (fun _ => congrArg J a₁),
    val_of _ _ _ J₀ (fun _ => J₀ (m ≫ φ)) (fun _ => congrArg J₀ a₂), ← inv_mul_eq_iff_eq_mul]
  refine Units.ext (stalkMap_injective_of_flat σ z ?_)
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul]
  rw [← map_inv, Units.val_mul] at H
  exact H
end GlobalTheory.ConstFam
