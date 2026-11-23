-- Prove2me | solution 1 for GroundTheory.Automorphic.ArchWhittaker.exp_growth_false
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:44.30656+00:00
-- url     : https://prove2.me/submissions/202ca96d-0af3-4648-9aee-db14d7b01d48

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_WronskianEqZeroOfModerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ArchWhittaker
open Filter Topology Set
namespace GroundTheory.Automorphic.ArchWhittaker
theorem _root_.solution {A b K Y : ℝ} {M : ℕ} (hA : 0 < A) (hb : 0 < b)
    (h : ∀ y ≥ Y, A * Real.exp (b * y) ≤ K * y ^ M) : False := by
  have ht : Tendsto (fun y => Real.exp (b * y) / (b * y) ^ M) atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop M).comp (tendsto_id.const_mul_atTop hb)
  have hbM : 0 < A * b ^ M := mul_pos hA (pow_pos hb M)
  obtain ⟨y, hy1, hy2, hy3⟩ := ((ht.eventually_ge_atTop (K / (A * b ^ M) + 1)).and
    ((eventually_ge_atTop Y).and (eventually_gt_atTop 0))).exists
  have hpos : 0 < (b * y) ^ M := pow_pos (mul_pos hb hy3) M
  have h1 : (K / (A * b ^ M) + 1) * (b * y) ^ M ≤ Real.exp (b * y) := by
    rwa [le_div_iff₀ hpos] at hy1
  have h2 := h y hy2
  have hyM : 0 < y ^ M := pow_pos hy3 M
  have e : A * ((K / (A * b ^ M) + 1) * (b * y) ^ M) = K * y ^ M + A * b ^ M * y ^ M := by
    rw [mul_pow]; field_simp
  have h3 := mul_le_mul_of_nonneg_left h1 hA.le
  rw [e] at h3
  nlinarith [mul_pos hbM hyM]
end GroundTheory.Automorphic.ArchWhittaker
