-- Prove2me | solution 1 for GlobalTheory.KilledFin.pow_mem_powSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:29.938916+00:00
-- url     : https://prove2.me/submissions/080331c0-c2ff-4deb-883d-783c59101a88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KilledFin
open Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.KilledFin
theorem _root_.solution (t : Module.End ℂ V) (q : ℂ[X]) (hq : q ≠ 0) (N : Submodule ℂ V)
    (hkill : ∀ n ∈ N, aeval t q n = 0) (n : V) (hn : n ∈ N) :
    (t ^ q.natDegree) n ∈ powSpan t q.natDegree N := by
  set d := q.natDegree with hd
  have hlc : q.coeff d ≠ 0 := by
    rw [hd, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hq
  have h0 := hkill n hn
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, LinearMap.add_apply,
    LinearMap.sum_apply] at h0
  have h1 := eq_neg_of_add_eq_zero_right h0
  have h2 : q.coeff d • (t ^ d) n ∈ powSpan t d N := by
    rw [← LinearMap.smul_apply, h1]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
    rw [LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨j, Finset.mem_range.mp hj, n, hn, rfl⟩
  exact (Submodule.smul_mem_iff _ hlc).mp h2
end GlobalTheory.KilledFin
