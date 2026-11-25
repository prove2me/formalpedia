-- Prove2me | solution 1 for GlobalTheory.ConstFam.resF_pullB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:41:05.720937+00:00
-- url     : https://prove2.me/submissions/8837ac5e-2046-4139-b37a-ea76ec2a0ad9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Theorems.Thm_GlobalTheory_ConstFam_sval_resF
import Theorems.Thm_GlobalTheory_ConstFam_secThrough_pullB
import Theorems.Thm_GlobalTheory_ConstFam_secThrough_pullF
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam__eq_3a137bedd551
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
include hW
variable (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F]
namespace GlobalTheory.ConstFam
theorem _root_.solution (j : ℕ) (α : a.D₀.X) (s : SecBMod a.D₀ j α) :
    resF P.toPre F j (e α) (pullB hW j α s) = pullF hW F j α s := sec_ext' P.toPre.P.isLB fun y J' hJ' => by
  obtain ⟨J, hJ⟩ := exists_good' a.D₀.P.isLB y
  have e₁ := (secThrough_pullB hW j α s).sval (famφB_comp hW α) (𝟙 _ ≫ (DegPre.prB P.toPre F).left) hJ hJ'
  have e₂ := (secThrough_pullF hW F j α s).sval (famφ_comp hW F α) (𝟙 _) hJ hJ'
  simp only [GC.famφ_eq, ← Category.assoc] at e₂
  rw [sval_resF _ _ _ _ hJ']
  exact (Units.mul_right_inj _).1 (e₁.symm.trans e₂)
end GlobalTheory.ConstFam
