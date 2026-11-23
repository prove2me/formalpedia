-- Prove2me | solution 1 for GlobalTheory.jetWedge_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:43.269862+00:00
-- url     : https://prove2.me/submissions/30ce7127-694d-4bdb-a987-057704be8bbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {D : ℕ}
namespace GlobalTheory
theorem _root_.solution (ω : M [⋀^Fin D]→ₗ[A] N) (v : Fin (D + 1) → A × M) :
    jetWedge ω v =
      ∑ i : Fin (D + 1), ((-1 : A) ^ (i : ℕ) * (v i).1) • ω (fun k => (v (i.succAbove k)).2) := by
  rw [jetWedge, AlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul, ← Int.cast_smul_eq_zsmul A]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
  rfl
end GlobalTheory
