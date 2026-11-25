-- Prove2me | solution 1 for GlobalTheory.DatumCoord.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:42:13.408641+00:00
-- url     : https://prove2.me/submissions/886fb281-c068-42f6-9eae-615bcf160bf4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DatumCoord
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.DatumCoord
theorem _root_.solution (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
    (r : ℕ) (hr : Module.finrank (𝓞 E) M = r) :
    ∃ φ : M →ₗ[𝓞 E] (Fin r → E), IsBaseChange E φ := by
  have hb := TensorProduct.isBaseChange (𝓞 E) M E
  have hl := (isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E _).2 hb
  have h1 : Module.finrank E (E ⊗[𝓞 E] M) = r := by
    rw [IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl,
      IsLocalizedModule.finrank_eq (𝓞 E)⁰ (TensorProduct.mk (𝓞 E) E M 1) le_rfl, hr]
  let e := (Module.finBasisOfFinrankEq E (E ⊗[𝓞 E] M) h1).equivFun
  exact ⟨e.toLinearMap.restrictScalars (𝓞 E) ∘ₗ TensorProduct.mk (𝓞 E) E M 1,
    IsBaseChange.of_equiv e fun _ => rfl⟩
end GlobalTheory.DatumCoord
