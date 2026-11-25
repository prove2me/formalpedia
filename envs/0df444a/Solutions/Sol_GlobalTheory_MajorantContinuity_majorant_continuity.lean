-- Prove2me | solution 1 for GlobalTheory.MajorantContinuity.majorant_continuity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:40:30.274078+00:00
-- url     : https://prove2.me/submissions/207d71b9-82b7-4ab2-a394-ab708206a90c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EventuallyComparable
import Theorems.Thm_GlobalTheory_MajorantContinuity_eventually_comparable
import Theorems.Thm_GlobalTheory_MajorantContinuity_compact_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate ComplexOrder
open GlobalTheory GlobalTheory.MajorantContinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.MajorantContinuity
theorem _root_.solution :
    ((∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v) ∧ (∀ (r : ℕ) (X : Data E r) (K : Set (Frame X.Ψ r)), IsCompact K → K ⊆ X.dom → ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ (τ : X.Ψ) (v : Fin r → ℂ), c * ‖v‖ ^ 2 ≤ X.maj x τ v ∧ X.maj x τ v ≤ C * ‖v‖ ^ 2)) := ⟨fun _ X _ hx _ hε => eventually_comparable X hx hε,
    fun _ X _ hK hKd => compact_bounds X hK hKd⟩
end GlobalTheory.MajorantContinuity
