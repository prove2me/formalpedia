-- Prove2me | solution 1 for GlobalTheory.ConstFam.finite_expo_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:26:36.606906+00:00
-- url     : https://prove2.me/submissions/604ad9a2-a404-4896-9452-04c60dca9067

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsBasisOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSmulMemSpanOfExpandsAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstFamComponentsBasisExpansion
import Theorems.Thm_GlobalTheory_ConstFam_finite_form_le
import Theorems.Thm_GlobalTheory_ConstFam_two_mul_expo


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
include hj
namespace GlobalTheory.ConstFam
theorem _root_.solution (α : a.D₀.X) (n : ℤ) : {mu | expo a j α mu < n}.Finite := by
  refine Set.Finite.subset ((finite_form_le a.be a.be_pos (2 * n + a.be α α).toNat).preimage
    (add_left_injective α).injOn) fun mu h => ?_
  have h₁ : expo a j α mu < n := h
  have h₂ := two_mul_expo a j α mu
  have h₃ := a.be_symm α mu
  have h₄ : 0 ≤ a.be mu mu := by
    by_cases h : mu = 0
    · simp [h]
    · exact (a.be_pos mu h).le
  have h₅ : a.be mu mu ≤ j * a.be mu mu := le_mul_of_one_le_left h₄ (by exact_mod_cast hj)
  show a.be (mu + α) (mu + α) ≤ _
  simp only [map_add, LinearMap.add_apply]
  omega
end GlobalTheory.ConstFam
