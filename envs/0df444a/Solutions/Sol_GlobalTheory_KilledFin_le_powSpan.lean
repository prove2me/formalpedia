-- Prove2me | solution 1 for GlobalTheory.KilledFin.le_powSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:27.796744+00:00
-- url     : https://prove2.me/submissions/b77e1597-7f1d-43a8-a37d-98769839cffe

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
    (hkill : ∀ n ∈ N, aeval t q n = 0) : N ≤ powSpan t q.natDegree N := by
  intro n hn
  rcases Nat.eq_zero_or_pos q.natDegree with h | h
  · have hC := Polynomial.eq_C_of_natDegree_eq_zero h
    have h0 := hkill n hn
    rw [hC, Polynomial.aeval_C, Module.algebraMap_end_apply] at h0
    have hc0 : q.coeff 0 ≠ 0 := by
      intro hc; apply hq; rw [hC, hc, map_zero]
    rw [(smul_eq_zero.mp h0).resolve_left hc0]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨0, h, n, hn, by simp⟩
end GlobalTheory.KilledFin
