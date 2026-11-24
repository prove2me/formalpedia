-- Prove2me | solution 1 for GlobalTheory.LocalNorm.exists_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:15.361233+00:00
-- url     : https://prove2.me/submissions/756939f4-b8fc-4baa-aee1-32df8230a963

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
import Theorems.Thm_GlobalTheory_LocalNorm_complexConj_rt

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
theorem _root_.solution (H : Host E) (z : E) : ∃ α β : maximalRealSubfield E,
    ((2 * α : maximalRealSubfield E) : E) = z + IsCMField.complexConj E z ∧
    ((α ^ 2 + H.d * β ^ 2 : maximalRealSubfield E) : E) = z * IsCMField.complexConj E z := by
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have hd : (H.d : E) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have hrt : (H.rt : E) ≠ 0 := fun h => hd (by simpa [h] using hsq)
  refine ⟨⟨(z + IsCMField.complexConj E z) / 2, (IsCMField.complexConj_eq_self_iff E _).1 ?_⟩,
    ⟨(z - IsCMField.complexConj E z) / (2 * H.rt), (IsCMField.complexConj_eq_self_iff E _).1 ?_⟩,
    ?_, ?_⟩
  · simp only [map_div₀, map_add, map_ofNat, IsCMField.complexConj_apply_apply, add_comm]
  · simp only [map_div₀, map_sub, map_mul, map_ofNat, IsCMField.complexConj_apply_apply,
      complexConj_rt]
    field_simp
    ring
  · push_cast
    change (2 : E) * _ = _
    ring
  · push_cast
    rw [← neg_neg (H.d : E), ← hsq]
    field_simp
    ring
end GlobalTheory.LocalNorm
