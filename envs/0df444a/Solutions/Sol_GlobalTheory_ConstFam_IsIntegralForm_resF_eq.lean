-- Prove2me | solution 1 for GlobalTheory.ConstFam.IsIntegralForm.resF_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:35:53.03959+00:00
-- url     : https://prove2.me/submissions/68aaa9dd-e0d1-487a-8592-e7fc4e7c7855

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsBasisOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSmulMemSpanOfExpandsAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstFamComponentsBasisExpansion
import Theorems.Thm_GlobalTheory_ConstFam_eq_or_off
import Theorems.Thm_GlobalTheory_ConstFam_constFam_add_nsmul
import Theorems.Thm_GlobalTheory_ConstFam_constFam_off
import Theorems.Thm_GlobalTheory_ConstFam_resF_pullB


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
variable {hW}
namespace GlobalTheory.ConstFam
namespace IsIntegralForm
theorem _root_.solution {α : a.D₀.X} {s₀ : SecBMod a.D₀ j α} {m : ℕ} {f : ∀ χ, SecBMod P.toPre j χ}
    (h : IsIntegralForm hW j α s₀ m f) (χ : P.toPre.X) : resF P.toPre F j χ (f χ) =
      toF (R := PowerSeries k) F (PowerSeries.X ^ m) • famComp P.toPre F j χ (constFam hW F hG hj α s₀) := by
  rcases eq_or_off e j α χ with ⟨mu, rfl⟩ | hχ
  · rw [(h.1 mu).2, map_smulₛₗ, resF_pullB, constFam_add_nsmul, smul_smul, map_pow, map_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (h.1 mu).1, zpow_add₀ (toF_X_ne_zero F), zpow_natCast]
  · rw [h.2 χ hχ, map_zero, constFam_off hW F hG hj α s₀ χ hχ, smul_zero]
end IsIntegralForm
end GlobalTheory.ConstFam
