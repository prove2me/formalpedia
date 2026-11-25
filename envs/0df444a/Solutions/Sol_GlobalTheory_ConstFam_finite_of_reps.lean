-- Prove2me | solution 1 for GlobalTheory.ConstFam.finite_of_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:25:39.747097+00:00
-- url     : https://prove2.me/submissions/641b861f-8f08-4292-87fd-99edf2e1f615

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsBasisOfIsExtension
import Theorems.Thm_GlobalTheory_ConstFam_IsFETranslate_unique
import Theorems.Thm_GlobalTheory_ConstFam_SecThrough_unique


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
theorem _root_.solution {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {j : ℕ} (hj : 1 ≤ j) {C : Type}
    (rep : C → X) (hrep : ∀ α, ∃! x, ∃ mu, rep x + j • mu = α) : Finite C := by
  have : AddGroup.FG X := Module.Finite.iff_addGroup_fg.1 inferInstance
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg X (show j ≠ 0 by omega)
  refine Finite.of_injective
    (fun x => (QuotientAddGroup.mk (rep x) : X ⧸ (nsmulAddMonoidHom j : X →+ X).range)) fun x y h => ?_
  obtain ⟨mu, hmu⟩ := QuotientAddGroup.eq.1 h
  refine (hrep (rep y)).unique ⟨mu, ?_⟩ ⟨0, by rw [smul_zero, add_zero]⟩
  rw [show j • mu = -rep x + rep y from hmu, add_neg_cancel_left]
end GlobalTheory.ConstFam
