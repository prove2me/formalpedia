-- Prove2me | solution 1 for GlobalTheory.algHom_mem_pow_of_le_order
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:52.294707+00:00
-- url     : https://prove2.me/submissions/0612eb7e-9bb8-4e95-a101-0776b44fca66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Theorems.Thm_GlobalTheory_germIdeal_eq_span
import Theorems.Thm_GlobalTheory_mem_germIdeal_pow_iff_le_order


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open MvPowerSeries
variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable [Finite σ]
namespace GlobalTheory
theorem _root_.solution (φ : MvPowerSeries σ A →ₐ[A] S) {K : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ K) {n : ℕ} {g : MvPowerSeries σ A} (hg : (n : ℕ∞) ≤ g.order) :
    φ g ∈ K ^ n := by
  have h : (germIdeal σ A).map φ ≤ K := by
    rw [germIdeal_eq_span, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hφ i
  have := Ideal.mem_map_of_mem φ (mem_germIdeal_pow_iff_le_order.2 hg)
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h n this
end GlobalTheory
