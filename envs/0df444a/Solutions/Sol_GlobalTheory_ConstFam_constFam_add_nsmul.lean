-- Prove2me | solution 1 for GlobalTheory.ConstFam.constFam_add_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:16:45.269802+00:00
-- url     : https://prove2.me/submissions/47e16166-d3ee-4914-9999-9f46b034b670

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
import Theorems.Thm_P2M_GlobalTheory_ConstFam_trF_comp___3c073c7656a0
import Theorems.Thm_P2M_GlobalTheory_ConstFam_delta__comp_465ccaa85cbb
import Theorems.Thm_GlobalTheory_ConstFam_val_fe
import Theorems.Thm_GlobalTheory_ConstFam_constFam_self
import Theorems.Thm_GlobalTheory_ConstFam_exists_gen_through
import Theorems.Thm_GlobalTheory_ConstFam_secThrough_pullF
import Theorems.Thm_GlobalTheory_ConstFam_sval_feTranslate
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_smul__9bcebbd1d3c5
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff


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
namespace GlobalTheory.ConstFam
theorem _root_.solution (α mu : a.D₀.X) (s₀ : SecBMod a.D₀ j α) :
    famComp P.toPre F j (e (α + j • mu)) (constFam hW F hG hj α s₀) =
      toF (R := PowerSeries k) F PowerSeries.X ^ expo a j α mu •
        pullF hW F j (α + j • mu) (feTranslate a.D₀ j mu α s₀) := by
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := P.toPre) (F := F) hG j (e mu) (e α)
  obtain ⟨u', hu', hv⟩ := exists_gen_through hW.2.1 a.D₀.P.isLB P.toPre.P.isLB (deltaφ_comp hW F α mu)
    (feGen a.D₀ j mu α) (feGen_isGen a.D₀ j mu α)
  refine sec_ext' P.toPre.P.isLB fun y J hJ => ?_
  obtain ⟨J₀, hJ₀⟩ := exists_good' a.D₀.P.isLB y
  have key : ∀ χ, e α + j • e mu = χ → sval ((constFam hW F hG hj α s₀).s χ) (𝟙 _) y J =
      sval ((constFam hW F hG hj α s₀).s (e α)) (𝟙 _ ≫ (DegPre.trF P.toPre F (e mu)).left) y J *
        (val u (𝟙 _) y J).val := by
    rintro _ rfl
    exact (secRel_iff P.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 ((constFam hW F hG hj α s₀).fe _ _ u hu hc) _ _ y J hJ
  have hi : e α + j • e mu = e (α + j • mu) := by rw [map_add, map_nsmul]
  refine (key _ hi).trans (Eq.trans ?_ (sval_smul' hJ _ _ _).symm)
  rw [show (constFam hW F hG hj α s₀).s (e α) = pullF hW F j α s₀ from constFam_self hW F hG hj α s₀,
    val_fe hW F hG α mu u u' hu hc hu' hv _ hJ, mul_left_comm]
  refine congrArg _ ?_
  have a₁ := (secThrough_pullF hW F j (α + j • mu) (feTranslate a.D₀ j mu α s₀)).sval (famφ_comp hW F _) (𝟙 _) hJ₀ hJ
  have a₂ := (secThrough_pullF hW F j α s₀).sval (famφ_comp hW F _)
    (𝟙 _ ≫ (DegPre.trF P.toPre F (e mu)).left) hJ₀ hJ
  have a₃ := hv _ (𝟙 _) y J₀ J hJ₀ hJ
  have a₄ := sval_feTranslate a.D₀ j mu α s₀ (𝟙 _ ≫ (DegPre.prB P.toPre F).left ≫ φ) hJ₀
  rw [Category.assoc, trF_comp_φ hW, ← Category.assoc] at a₂
  have a₅ := prod_sum₂ (K := Fin 4) (K' := Fin 4) (fun i => wVal w y J₀ J (𝟙 _ ≫
    DegPre.deltaφ P.toPre F j (e α) (e mu) i) ^ DegPre.deltaε j i)
    (c := ∏ i, wVal w y J₀ J (𝟙 _ ≫ DegPre.famφ P.toPre F (e (α + j • mu)) i) ^ DegPre.famε j i) (by rw [← hi]; rfl)
    (prod_neg _ _ (c := ∏ i, wVal w y J₀ J ((𝟙 _ ≫ (DegPre.trF P.toPre F (e mu)).left) ≫
      DegPre.famφ P.toPre F (e α) i) ^ DegPre.famε j i) (by simp only [Category.assoc]; rfl))
  rw [a₁, a₂, a₃, a₅] at a₄
  refine (Units.mul_right_inj (∏ i, wVal w y J₀ J (𝟙 _ ≫ DegPre.famφ P.toPre F (e (α + j • mu)) i) ^
    DegPre.famε j i)).1 (Eq.trans ?_ a₄.symm)
  generalize (∏ i, wVal w y J₀ J ((𝟙 _ ≫ (DegPre.trF P.toPre F (e mu)).left) ≫
      DegPre.famφ P.toPre F (e α) i) ^ DegPre.famε j i) = W
  simp only [Units.val_mul]
  linear_combination (-(sval (pullF hW F j α s₀) (𝟙 _ ≫ (DegPre.trF P.toPre F (e mu)).left) y J *
    (val u' (𝟙 _) y J).val * (∏ i, wVal w y J₀ J (𝟙 _ ≫ DegPre.famφ P.toPre F (e (α + j • mu)) i) ^
    DegPre.famε j i).val)) * W.mul_inv
end GlobalTheory.ConstFam
