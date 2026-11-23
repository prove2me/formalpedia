-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SemilinearResidue.solve_of_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:59.558224+00:00
-- url     : https://prove2.me/submissions/fe9dc5f1-af4d-4509-b619-9b03d6f8a6a4

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module Finset
open GroundTheory.PAdicHodge.SemilinearResidue
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] {e : ℕ} {φ : V →+ V}
omit hp [CharP k p]
namespace GroundTheory.PAdicHodge.SemilinearResidue
theorem _root_.solution (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p ^ e • φ x) (z : V) (n : ℕ)
    (c : ℕ → k) (hrel : (⇑φ)^[n + 1] z = ∑ i ∈ range (n + 1), c i • (⇑φ)^[i] z) (ε y : k)
    (hy : (recPoly (p ^ e) c ε n).eval y = y) :
    φ (∑ i ∈ range (n + 1), (recPoly (p ^ e) c ε i).eval y • (⇑φ)^[i] z) =
      (∑ i ∈ range (n + 1), (recPoly (p ^ e) c ε i).eval y • (⇑φ)^[i] z) + ε • z := by
  have hit : ∀ i, φ ((⇑φ)^[i] z) = (⇑φ)^[i + 1] z := fun i =>
    (Function.iterate_succ_apply' _ _ _).symm
  rw [map_sum]
  simp_rw [hφ, hit]
  rw [Finset.sum_range_succ, hy, hrel, Finset.smul_sum, Finset.sum_range_succ' _ n,
    Finset.sum_range_succ' (fun i => (recPoly (p ^ e) c ε i).eval y • (⇑φ)^[i] z) n]
  simp only [recPoly, eval_add, eval_pow, eval_mul, eval_C, eval_X, eval_sub,
    Function.iterate_zero, id, smul_smul, add_smul, sub_smul, Finset.sum_add_distrib]
  simp only [mul_comm (y ^ p ^ e)]
  abel
end GroundTheory.PAdicHodge.SemilinearResidue
