-- Prove2me | solution 1 for GlobalTheory.ConstFam.exists_isIntegralForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:57:38.423233+00:00
-- url     : https://prove2.me/submissions/691b590d-0608-4b36-b8bb-77053adbb0c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsBasisOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSmulMemSpanOfExpandsAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstFamComponentsBasisExpansion
import Theorems.Thm_GlobalTheory_ConstFam_map_add_nsmul
import Theorems.Thm_GlobalTheory_ConstFam_eq_or_off
import Theorems.Thm_GlobalTheory_FamFree_add_nsmul_inj
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
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)
include hj
namespace GlobalTheory.ConstFam
theorem _root_.solution (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) {m : ℕ}
    (hm : ∀ mu, 0 ≤ (m : ℤ) + expo a j α mu) : ∃ f, IsIntegralForm hW j α s₀ m f := by
  have ex : ∀ χ, ∃ t : SecBMod P.toPre j χ, (∀ mu, e (α + j • mu) = χ → HEq t
      ((PowerSeries.X : PowerSeries k) ^ ((m : ℤ) + expo a j α mu).toNat •
        pullB hW j (α + j • mu) (feTranslate a.D₀ j mu α s₀))) ∧ ((∀ mu, e α + j • mu ≠ χ) → t = 0) := fun χ => by
    rcases eq_or_off e j α χ with ⟨mu, rfl⟩ | h
    · refine ⟨(PowerSeries.X : PowerSeries k) ^ ((m : ℤ) + expo a j α mu).toNat •
        pullB hW j (α + j • mu) (feTranslate a.D₀ j mu α s₀), fun mu' h => ?_, fun h => absurd (map_add_nsmul e α mu).symm (h _)⟩
      obtain rfl := FamFree.add_nsmul_inj hj α _ _ (e.injective h)
      rfl
    · exact ⟨0, fun mu h' => absurd ((map_add_nsmul e α mu).symm.trans h') (h _), fun _ => rfl⟩
  choose f h₁ h₂ using ex
  exact ⟨f, fun mu => ⟨hm mu, eq_of_heq (h₁ _ mu rfl)⟩, h₂⟩
end GlobalTheory.ConstFam
