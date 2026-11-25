-- Prove2me | solution 1 for Kyprianou.Ch04.WHRatioLimitRegularNonzeroExponentV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:41:52.217025+00:00
-- url     : https://prove2.me/submissions/b46da6a9-51ec-4540-8b6c-646b74543f9c

import Mathlib.Topology.Filter
import Mathlib.Topology.Instances.Real.Lemmas
open Filter
open scoped Topology
set_option autoImplicit false

/-- Pass to the limit in the nonsingular Wiener–Hopf rational factor. -/
theorem solution
    (q r : ℕ → ℝ) (beta m psiBeta : ℝ)
    (hpsi : psiBeta ≠ 0)
    (hq0 : Tendsto q atTop (𝓝 0))
    (hr0 : Tendsto r atTop (𝓝 0))
    (hquot : Tendsto (fun n => q n / r n) atTop (𝓝 m)) :
    Tendsto (fun n => (q n / r n) * ((r n - beta) / (q n - psiBeta)))
      atTop (𝓝 (m * beta / psiBeta)) := by
  have hb : Tendsto (fun _ : ℕ => beta) atTop (𝓝 beta) :=
    tendsto_const_nhds
  have hp : Tendsto (fun _ : ℕ => psiBeta) atTop (𝓝 psiBeta) :=
    tendsto_const_nhds
  have hnum := hr0.sub hb
  have hden := hq0.sub hp
  have hratio := hnum.div hden (by simpa using hpsi)
  have hprod := hquot.mul hratio
  have hgoal :
      Tendsto (fun n : ℕ => (q n / r n) * ((r n - beta) / (q n - psiBeta)))
        atTop (𝓝 (m * ((0 - beta) / (0 - psiBeta)))) := by
    simpa only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply] using hprod
  have hlim : m * ((0 - beta) / (0 - psiBeta)) = m * beta / psiBeta := by
    field_simp [hpsi]
    ring
  rw [hlim] at hgoal
  exact hgoal
