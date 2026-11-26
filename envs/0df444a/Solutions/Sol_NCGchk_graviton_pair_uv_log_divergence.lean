-- Prove2me | solution 1 for NCGchk.graviton_pair_uv_log_divergence
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:41:47.892391+00:00
-- url     : https://prove2.me/submissions/dbe7fd45-0782-4693-8f18-63251dc31208

import Mathlib
namespace NCGchk
theorem _root_.solution :
    Filter.Tendsto (fun N : ℕ => Finset.sum (Finset.range N) (fun k : ℕ => (1 : ℝ) / (k + 1)) / Real.log N) Filter.atTop (nhds 1) := by
  have h := Real.tendsto_harmonic_sub_log
  have hl : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h0 := h.div_atTop hl
  have h1 := h0.add_const 1
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  have : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have e : ∑ k ∈ Finset.range N, (1:ℝ)/(k+1) = (harmonic N : ℝ) := by
    simp [harmonic, one_div]
  rw [e]; field_simp; ring

end NCGchk
