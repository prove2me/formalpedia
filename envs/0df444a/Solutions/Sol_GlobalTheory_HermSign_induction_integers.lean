-- Prove2me | solution 1 for GlobalTheory.HermSign.induction_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:47:26.303991+00:00
-- url     : https://prove2.me/submissions/86de41b5-c9cb-40c3-b85a-b5b017669fa1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
import Theorems.Thm_GlobalTheory_HermSign_span_integers_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.HermSign
theorem _root_.solution (Φ : CMType E) (P : (Φ → ℂ) → Prop)
    (h : ∀ a : 𝓞 E, P fun τ => τ.1 (a : E)) (hadd : ∀ c c', P c → P c' → P (c + c'))
    (hsmul : ∀ (t : ℝ) c, P c → P (t • c)) (c : Φ → ℂ) : P c := by
  have hc : c ∈ Submodule.span ℝ (Set.range fun a : 𝓞 E => fun τ : Φ => τ.1 (a : E)) := by
    rw [span_integers_eq_top]; trivial
  induction hc using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
  | zero => simpa using hsmul 0 _ (h 0)
  | add x y _ _ hx hy => exact hadd _ _ hx hy
  | smul t x _ hx => exact hsmul _ _ hx
end GlobalTheory.HermSign
