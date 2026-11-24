-- Prove2me | solution 1 for GlobalTheory.ChowHt.isChowFormCycle_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:46.520512+00:00
-- url     : https://prove2.me/submissions/fa50799c-887c-4efc-a41a-bbaa649e4187

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type} [Field k] {N : ℕ}
namespace GlobalTheory.ChowHt
theorem _root_.solution {e dl : ℕ} {f : MvPolynomial (Fin (e + 1) × Fin N) k} :
    IsChowFormCycle 0 e dl f ↔ dl = 0 ∧ ∃ c : k, c ≠ 0 ∧ f = C c := by
  constructor
  · rintro ⟨c, hc, d, g, -, rfl, rfl⟩
    exact ⟨by simp, c, hc, by simp⟩
  · rintro ⟨rfl, c, hc, rfl⟩
    exact ⟨c, hc, 0, 0, by simp, by simp, by simp⟩
end GlobalTheory.ChowHt
