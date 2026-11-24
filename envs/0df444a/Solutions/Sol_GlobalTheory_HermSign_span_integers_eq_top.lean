-- Prove2me | solution 1 for GlobalTheory.HermSign.span_integers_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:29:23.990537+00:00
-- url     : https://prove2.me/submissions/dd504986-0f39-4cb4-8670-bc47095ae189

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
import Theorems.Thm_GlobalTheory_CMType_eq_zero_of_sum_re_eq_zero


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
theorem _root_.solution (Φ : CMType E) :
    Submodule.span ℝ (Set.range fun a : 𝓞 E => fun τ : Φ => τ.1 (a : E)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let δ : Φ → ℂ := fun τ => f (Pi.single τ 1) - Complex.I * f (Pi.single τ Complex.I)
  have key : ∀ z : Φ → ℂ, f z = ∑ τ, (z τ * δ τ).re := by
    intro z
    conv_lhs => rw [← Finset.univ_sum_single z, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have : (Pi.single τ (z τ) : Φ → ℂ) =
        (z τ).re • (Pi.single τ 1 : Φ → ℂ) + (z τ).im • (Pi.single τ Complex.I : Φ → ℂ) := by
      rw [← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]
      congr 1
      simp
    rw [this, map_add, map_smul, map_smul]
    simp [δ]
  have hδ : δ = 0 := Φ.eq_zero_of_sum_re_eq_zero δ fun a => by
    rw [← key (fun τ => τ.1 (a : E))]
    exact hf (Submodule.subset_span ⟨a, rfl⟩)
  refine hf0 (LinearMap.ext fun z => ?_)
  simp [key, hδ]
end GlobalTheory.HermSign
