-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.exists_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:22:54.539803+00:00
-- url     : https://prove2.me/submissions/c2fd7de6-863b-400a-b565-fc90fd5baaf7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
import Theorems.Thm_GlobalTheory_ExistsSmulMemRange_exists_coeffs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.PeriodOnto
theorem _root_.solution {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {r : ℕ} (φ : Λ →ₗ[𝓞 E] (Fin r → E))
    (hinj : Function.Injective φ) (hsp : Submodule.span E (Set.range φ) = ⊤) (σ : E →+* ℂ) (f : Λ →+ ℂ)
    (hf : ∀ (a : 𝓞 E) x, f (a • x) = σ (a : E) * f x) :
    ∃ c : Fin r → ℂ, ∀ v, f v = ∑ j, c j * σ (φ v j) := by
  first
  | exact @_root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs
  | exact _root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs
  | (apply _root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs ..)
end GlobalTheory.PeriodOnto
