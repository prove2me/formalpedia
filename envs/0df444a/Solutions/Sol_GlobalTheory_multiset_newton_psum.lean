-- Prove2me | solution 1 for GlobalTheory.multiset_newton_psum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:00.14518+00:00
-- url     : https://prove2.me/submissions/8974c51a-f4ed-42ea-b906-697269b53188

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MultisetPowerSumNewtonIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory
private theorem sum_antidiagonal_filter_ioo_eq_sum_ioo (k : ℕ) (g : ℕ → ℕ → ℂ) :
    ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k, g a.1 a.2
      = ∑ i ∈ Finset.Ioo 0 k, g i (k - i) := by
  rw [Finset.sum_filter,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if i ∈ Set.Ioo 0 k then g i j else 0),
    ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ioo, Finset.mem_Ioo]
  omega
private theorem aeval_psum_eq_sum_map_pow (s : Multiset ℂ) (n : ℕ) :
    MvPolynomial.aeval (fun x : s => (x : ℂ)) (MvPolynomial.psum s ℂ n) = (s.map (· ^ n)).sum := by
  classical
  rw [MvPolynomial.psum, map_sum]
  simp only [map_pow, MvPolynomial.aeval_X]
  conv_rhs => rw [← Multiset.map_univ_coe s]
  rw [Multiset.map_map]
  rfl
end GlobalTheory
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (s : Multiset ℂ) (r : ℕ) (hr : 0 < r) :
    (s.map (· ^ r)).sum = (-1) ^ (r + 1) * (r : ℂ) * s.esymm r
      - ∑ i ∈ Finset.Ioo 0 r, (-1) ^ i * s.esymm i * (s.map (· ^ (r - i))).sum := by
  classical
  have key := congrArg (MvPolynomial.aeval (fun x : s => (x : ℂ)))
    (MvPolynomial.psum_eq_mul_esymm_sub_sum s ℂ r hr)
  simp only [map_sub, map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe,
    aeval_psum_eq_sum_map_pow] at key
  rw [key, sum_antidiagonal_filter_ioo_eq_sum_ioo r (fun i j => (-1) ^ i * s.esymm i * (s.map (· ^ j)).sum)]
end GlobalTheory
