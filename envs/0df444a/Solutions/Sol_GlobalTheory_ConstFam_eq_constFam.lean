-- Prove2me | solution 1 for GlobalTheory.ConstFam.eq_constFam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:10:59.996601+00:00
-- url     : https://prove2.me/submissions/6a0e294f-5982-4dfb-ac73-e5b731320570

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Theorems.Thm_GlobalTheory_ConstFam_constFam_self
import Theorems.Thm_GlobalTheory_ConstFam_constFam_off
import Theorems.Thm_GlobalTheory_FamFree_eq_of_eq_add_nsmul
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
variable (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)
namespace GlobalTheory.ConstFam
theorem _root_.solution {α : a.D₀.X} {s₀ : SecBMod a.D₀ j α} {s : Fam P.toPre F j}
    (h₁ : famComp P.toPre F j (e α) s = pullF hW F j α s₀)
    (h₂ : ∀ χ, (∀ mu, e α + j • mu ≠ χ) → famComp P.toPre F j χ s = 0) : s = constFam hW F hG hj α s₀ := by
  refine fam_ext fun χ i => congrArg (fun q => LB.Sec.f q i) (?_ : s.s χ = (constFam hW F hG hj α s₀).s χ)
  by_cases hχ : ∃ mu, e α + j • mu = χ
  · exact FamFree.eq_of_eq_add_nsmul hG _ _ hχ (h₁.trans (constFam_self hW F hG hj α s₀).symm)
  · exact (h₂ χ fun mu h => hχ ⟨mu, h⟩).trans (constFam_off hW F hG hj α s₀ χ fun mu h => hχ ⟨mu, h⟩).symm
end GlobalTheory.ConstFam
