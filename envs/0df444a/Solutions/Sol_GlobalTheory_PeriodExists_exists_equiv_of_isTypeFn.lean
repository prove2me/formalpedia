-- Prove2me | solution 1 for GlobalTheory.PeriodExists.exists_equiv_of_isTypeFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:22:59.54378+00:00
-- url     : https://prove2.me/submissions/29f337dd-f829-4279-8058-16517b8f4c3b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TypeFnPeriodExistModuliNonempty

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
theorem _root_.solution {H : Host E} {p q g g' : ℕ} {ty : Fin g → (E →+* ℂ)}
    {ty' : Fin g' → (E →+* ℂ)} (h : IsTypeFn H p q ty) (h' : IsTypeFn H p q ty') :
    ∃ e : Fin g ≃ Fin g', ∀ k, ty' (e k) = ty k := by
  have hc : ∀ τ, Nonempty ({i // ty i = τ} ≃ {i // ty' i = τ}) := by
    intro τ
    rw [← Finite.card_eq]
    by_cases hτ : τ (H.rt : E) = H.rt0
    · rw [(h τ).1 hτ, (h' τ).1 hτ]
    · rw [(h τ).2 hτ, (h' τ).2 hτ]
  exact ⟨Equiv.ofFiberEquiv fun τ => (hc τ).some, Equiv.ofFiberEquiv_map _⟩
end GlobalTheory.PeriodExists
