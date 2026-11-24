-- Prove2me | solution 1 for GlobalTheory.SimpleRoots.exists_norm_root_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:49.00487+00:00
-- url     : https://prove2.me/submissions/3c4bfdf8-4085-46cd-a717-7f21749acce8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
import Theorems.Thm_GlobalTheory_SimpleRoots_exists_norm_eval_le
import Theorems.Thm_GlobalTheory_SimpleRoots_norm_root_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
open GlobalTheory GlobalTheory.SimpleRoots
variable {d : ℕ}
namespace GlobalTheory.SimpleRoots
theorem _root_.solution {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ (x : Fin d → ℂ) (y : ℂ),
      (p.map (MvPolynomial.eval x)).eval y = 0 → ‖y‖ ≤ C * (1 + ‖x‖) ^ m := by
  choose C m hC h using fun i => exists_norm_eval_le (p.coeff i)
  set s := Finset.range p.natDegree
  have hs : 0 ≤ ∑ i ∈ s, C i := Finset.sum_nonneg fun i _ => hC i
  refine ⟨∑ i ∈ s, C i + 1, ∑ i ∈ s, m i, by positivity, fun x y hy => ?_⟩
  have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have h2 := norm_root_le (hp.map _) (M := (∑ i ∈ s, C i) * (1 + ‖x‖) ^ (∑ i ∈ s, m i))
    (by positivity) (fun i hi => ?_) hy
  · rw [add_mul, one_mul]
    linarith [one_le_pow₀ h1 (n := ∑ i ∈ s, m i)]
  · rw [hp.natDegree_map] at hi
    have hi' : i ∈ s := Finset.mem_range.mpr hi
    rw [coeff_map]
    refine (h i x).trans (mul_le_mul (Finset.single_le_sum (fun j _ => hC j) hi')
      (pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le _) hi'))
      (by positivity) hs)
end GlobalTheory.SimpleRoots
