-- Prove2me | solution 1 for GlobalTheory.T.unit_real_of_sub_one_mem_span_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:35.124889+00:00
-- url     : https://prove2.me/submissions/74481d8e-d245-450b-ad0e-d7e99dd3559b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitRealOfCongrOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitRealOfCongrOneStatement
import Theorems.Thm_GlobalTheory_UnitReal_unit_real_of_congr_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ), q.Prime →
    ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} →
    ∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E) := by
  first | exact @GlobalTheory.UnitReal.unit_real_of_congr_one | exact GlobalTheory.UnitReal.unit_real_of_congr_one | (intros; apply GlobalTheory.UnitReal.unit_real_of_congr_one <;> assumption)
end _root_.GlobalTheory.T
