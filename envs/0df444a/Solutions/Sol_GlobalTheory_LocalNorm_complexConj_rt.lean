-- Prove2me | solution 1 for GlobalTheory.LocalNorm.complexConj_rt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:06:45.386888+00:00
-- url     : https://prove2.me/submissions/a7a5df5f-6b15-44e5-8ea1-324befc6654e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LocalNorm
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LocalNorm
theorem _root_.solution (H : Host E) : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have hsq' : IsCMField.complexConj E (H.rt : E) ^ 2 = (H.rt : E) ^ 2 := by
    rw [← map_pow, hsq]; simp
  refine (sq_eq_sq_iff_eq_or_eq_neg.1 hsq').resolve_left fun h => ?_
  let φ : E →+* ℂ := Classical.choice inferInstance
  have h1 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
  rw [h] at h1
  obtain ⟨t, ht⟩ := Complex.conj_eq_iff_real.1 h1.symm
  have h2 := congrArg φ hsq
  rw [map_pow, ht, map_neg, map_natCast] at h2
  have h3 : t ^ 2 = -(H.d : ℝ) := by exact_mod_cast h2
  have h4 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg t]
end GlobalTheory.LocalNorm
