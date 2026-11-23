-- Prove2me | solution 1 for GlobalTheory.SW.SiegelSum.exists_int_of_intM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:58.489805+00:00
-- url     : https://prove2.me/submissions/958a996a-548f-4d3a-9b2f-30a3b9558eb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableProdPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SiegelSum
namespace GlobalTheory.SW.SiegelSum
theorem _root_.solution {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (hR : 0 < R)
    {x : Matrix κ ι ℚ} (hx : IntM ((R : ℚ) • x)) :
    ∃ n : κ → ι → ℤ, x = Matrix.of fun k i => (n k i : ℚ) / R := by
  have : ∀ k i, ∃ n : ℤ, (n : ℚ) = R * x k i := fun k i => by
    have := IsIntegrallyClosed.isIntegral_iff.1 (hx k i)
    simpa using this
  choose n hn using this
  refine ⟨n, ?_⟩
  ext k i
  have : (R : ℚ) ≠ 0 := by positivity
  simp only [of_apply, hn]
  field_simp
end GlobalTheory.SW.SiegelSum
