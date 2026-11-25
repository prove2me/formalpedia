-- Prove2me | solution 1 for GlobalTheory.ConstFam.finite_form_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:11:52.571138+00:00
-- url     : https://prove2.me/submissions/c5bcd344-2246-4f30-90b3-f2961a32fae5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsBasisOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSmulMemSpanOfExpandsAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstFamComponentsBasisExpansion

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
theorem _root_.solution {Y : Type} [AddCommGroup Y] [Module.Finite ℤ Y] (q : LinearMap.BilinForm ℤ Y)
    (hq : ∀ y, y ≠ 0 → 0 < q y y) (n : ℕ) : {y | q y y ≤ n}.Finite := by
  have h0 : ∀ y, 0 ≤ q y y := fun y => by
    by_cases h : y = 0
    · simp [h]
    · exact (hq y h).le
  have : AddGroup.FG Y := Module.Finite.iff_addGroup_fg.1 inferInstance
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg Y (n := 4 * n + 1) (by omega)
  refine Set.Finite.of_finite_image (f := fun y => (QuotientAddGroup.mk y :
    Y ⧸ (nsmulAddMonoidHom (4 * n + 1) : Y →+ Y).range)) (Set.toFinite _) fun y hy y' hy' h => ?_
  obtain ⟨v, hv⟩ := QuotientAddGroup.eq.1 h
  obtain rfl : y' = y + (4 * n + 1) • v := by rw [show (4 * n + 1) • v = -y + y' from hv, add_neg_cancel_left]
  by_contra hne
  have hv0 : v ≠ 0 := fun e => hne (by rw [e, smul_zero, add_zero])
  have a₁ := hq v hv0
  have a₂ := h0 (y + (y + (4 * n + 1) • v))
  have a₃ : q y y ≤ n := hy
  have a₄ : q (y + (4 * n + 1) • v) (y + (4 * n + 1) • v) ≤ n := hy'
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at a₂ a₄
  push_cast at a₂ a₄
  have a₅ : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  nlinarith [mul_nonneg (mul_nonneg a₅ a₅) a₁.le, mul_nonneg a₅ a₁.le, mul_nonneg a₅ (sub_nonneg.2 (Int.add_one_le_of_lt a₁))]
end GlobalTheory.ConstFam
