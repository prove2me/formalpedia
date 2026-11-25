-- Prove2me | solution 1 for GlobalTheory.ConstFam.val_rig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:38:59.068269+00:00
-- url     : https://prove2.me/submissions/47ddd13a-32a7-4ada-b714-c41efdfa7181

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
import Theorems.Thm_GlobalTheory_ConstFam_pmaps_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
theorem _root_.solution : val (L := a.D₀.P.L) a.D₀.rigK (jFK (R := k) F) y J₀ =
    wVal w y J₀ J (1 : TF (R := PowerSeries k) F ⟶ P.toPre.P.A).left *
      val (L := P.toPre.P.L) P.toPre.rigK (jFK (R := PowerSeries k) F) y J := by
  have pm := (maps_iff w _ (fun _ => eSec a.D₀.P.A) _ P.toPre.rig a.D₀.rig (spMap (PowerSeries.C (R := k))) _
    (rigPull_le φ (spMap (PowerSeries.C (R := k))) he a.D₀.P.L) (fun _ => rfl)).1 hW.2.2.1
  have e₁ := pmaps_val (fun _ => he) pm (TF (R := PowerSeries k) F).hom hJ₀ hJ
  have hT : (TF (R := PowerSeries k) F).hom ≫ spMap (PowerSeries.C (R := k)) = (TF (R := k) F).hom := by
    rw [TF_hom, TF_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext hF).symm
  rw [Fintype.prod_unique, zpow_one] at e₁
  refine (val_pull hJ₀ _ _ _).trans (Eq.trans ?_ (e₁.trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _).symm)))
  exact congrArg (fun q => val (L := a.D₀.P.L) a.D₀.rig q y J₀) hT.symm
end GlobalTheory.ConstFam
