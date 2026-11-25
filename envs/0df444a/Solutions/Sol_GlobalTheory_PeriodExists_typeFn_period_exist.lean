-- Prove2me | solution 1 for GlobalTheory.PeriodExists.typeFn_period_exist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:07:58.406519+00:00
-- url     : https://prove2.me/submissions/a7a5dac0-53de-4baf-9a1a-3f236e76b301

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TypeFnPeriodExistModuliNonempty
import Theorems.Thm_GlobalTheory_PeriodExists_exists_typeFn_period
import Theorems.Thm_GlobalTheory_PeriodExists_period_of_isTypeFn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodExists
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PeriodExists
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty) ∧ (∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P) ∧ (N1c → 1 ≤ D.p + D.q → ∀ (l : Level H) (Xo : Moduli D l) (c : Coeff l), Nonempty (Xo.XF c)) := by
  intro E _ _ _ H D
  obtain ⟨g, ty, h, -⟩ := exists_typeFn_period H D
  refine ⟨⟨g, ty, h⟩, period_of_isTypeFn H D, fun hN hr l Xo c => ?_⟩
  obtain ⟨U⟩ := hN E H D l Xo (KA l).val.toRingHom g ty hr rfl h
  let i : Fin U.n := ⟨0, U.n_pos⟩
  obtain ⟨-, P, hP⟩ := period_of_isTypeFn H (U.Di i) g ty (by rw [(U.sig i).1, (U.sig i).2]; exact h)
  have hw : CategoryTheory.CategoryStruct.comp (U.u i P) Xo.s =
      CategoryTheory.CategoryStruct.comp (spMap c.F.val.toRingHom)
        (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    rw [U.over_σ i P hP]
    exact AlgebraicGeometry.Spec.map_comp (CommRingCat.ofHom (IntermediateField.inclusion c.le).toRingHom)
      (CommRingCat.ofHom c.F.val.toRingHom)
  exact ⟨(CategoryTheory.Limits.pullback.lift _ _ hw).base (IsLocalRing.closedPoint ℂ)⟩
end GlobalTheory.PeriodExists
