-- Prove2me | solution 1 for GlobalTheory.ChowHt.IsChowFormCycle.zero_iff_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:31.202217+00:00
-- url     : https://prove2.me/submissions/4516c385-6337-412a-bf6f-71c18ff8babd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Theorems.Thm_GlobalTheory_ChowHt_IsChowFormInt_zero_iff_of_isAlgClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type} [Field k] {N : ℕ}
open GlobalTheory.ChowHt.IsChowFormCycle
variable {Z Z' : Ideal (MvPolynomial (Fin N) k) →₀ ℕ} {e dl dl' : ℕ}
  {f f' : MvPolynomial (Fin (e + 1) × Fin N) k}
namespace GlobalTheory.ChowHt.IsChowFormCycle
theorem _root_.solution (h : IsChowFormCycle Z e dl f)
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] (u : Fin (e + 1) × Fin N → Ω) :
    MvPolynomial.aeval u f = 0 ↔ ∃ P ∈ Z.support,
      ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ P, MvPolynomial.aeval y g = 0) ∧
        ∀ i, ∑ j, u (i, j) * y j = 0 := by
  obtain ⟨c, hc, d, g, hg, -, rfl⟩ := h
  rw [map_mul, aeval_C, mul_eq_zero, map_eq_zero, or_iff_right hc, Finsupp.prod, map_prod,
    Finset.prod_eq_zero_iff]
  refine exists_congr fun P => and_congr_right fun hP => ?_
  rw [map_pow, pow_eq_zero_iff (Finsupp.mem_support_iff.1 hP)]
  exact (hg P hP).2.2.zero_iff_of_isAlgClosed (hg P hP).2.1 u
end GlobalTheory.ChowHt.IsChowFormCycle
