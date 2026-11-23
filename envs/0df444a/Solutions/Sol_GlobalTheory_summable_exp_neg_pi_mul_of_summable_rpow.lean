-- Prove2me | solution 1 for GlobalTheory.summable_exp_neg_pi_mul_of_summable_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:35.31245+00:00
-- url     : https://prove2.me/submissions/d51a631f-6581-4ab1-803f-d4192e49075a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptoticsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open GlobalTheory
open Set MeasureTheory
open scoped Topology
namespace GlobalTheory
theorem _root_.solution {ι : Type*} {q : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hs : Summable fun i => q i ^ (-(2 : ℝ))) {t : ℝ} (ht : 0 < t) :
    Summable fun i => Real.exp (-Real.pi * t * q i) := by
  refine Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le) (fun i => ?_)
    (hs.mul_left (2 / (Real.pi * t) ^ 2))
  have hx : 0 < Real.pi * t * q i := by have := hq i; positivity
  have h1 := Real.pow_div_factorial_le_exp _ hx.le 2
  have h2 : -Real.pi * t * q i = -(Real.pi * t * q i) := by ring
  have h3 : (2 / (Real.pi * t) ^ 2) * q i ^ (-(2 : ℝ))
      = ((Real.pi * t * q i) ^ 2 / (Nat.factorial 2 : ℕ))⁻¹ := by
    have := hq i
    rw [Real.rpow_neg (hq i).le, Real.rpow_two]
    simp only [Nat.factorial_two, Nat.cast_ofNat]
    field_simp
  rw [h2, h3, Real.exp_neg]
  exact inv_anti₀ (by positivity) h1
end GlobalTheory
