-- Prove2me | solution 1 for GlobalTheory.LOneLower.lambert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:35:09.073559+00:00
-- url     : https://prove2.me/submissions/f84c8597-3bde-4118-a4bb-023d73c74231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LOneLower
namespace GlobalTheory.LOneLower
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q) {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ+ => zetaMul χ n * t ^ (n : ℕ))
      (∑' d : ℕ+, χ ((d : ℕ) : ZMod q) * (t ^ (d : ℕ) / (1 - t ^ (d : ℕ)))) := by
  have hs : Summable fun c : ℕ+ × ℕ+ => χ ((c.1 : ℕ) : ZMod q) * t ^ (c.1 * c.2 : ℕ) := by
    refine Summable.of_norm_bounded (summable_prod_mul_pow 0 ht).norm fun c => ?_
    rw [pow_zero, one_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have e : ∑' d : ℕ+, χ ((d : ℕ) : ZMod q) * (t ^ (d : ℕ) / (1 - t ^ (d : ℕ)))
      = ∑' c : ℕ+ × ℕ+, χ ((c.1 : ℕ) : ZMod q) * t ^ (c.1 * c.2 : ℕ) := by
    rw [hs.tsum_prod]
    refine tsum_congr fun d => ?_
    simp only
    rw [tsum_mul_left]
    congr 1
    have h1 : ‖t ^ (d : ℕ)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) ht d.ne_zero
    simp only [pow_mul]
    rw [tsum_pnat_eq_tsum_succ (f := fun m => (t ^ (d : ℕ)) ^ m)]
    simp only [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one h1, div_eq_mul_inv]
  rw [e]
  have h2 := sigmaAntidiagonalEquivProd.hasSum_iff.2 hs.hasSum
  refine h2.sigma fun n => ?_
  refine (congrArg (HasSum _) ?_).mpr (hasSum_fintype _)
  simp only [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors,
    PNat.mk_coe, Equiv.coe_fn_mk, Finset.univ_eq_attach]
  rw [(n : ℕ).divisorsAntidiagonal.sum_attach
    (fun x : ℕ × ℕ => χ ((x.1 : ℕ) : ZMod q) * t ^ (x.1 * x.2)),
    Nat.sum_divisorsAntidiagonal (fun x y => χ ((x : ℕ) : ZMod q) * t ^ (x * y)),
    zetaMul, coe_zeta_mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hi)]
  simp [toArithmeticFunction, (Nat.pos_of_mem_divisors hi).ne']
end GlobalTheory.LOneLower
