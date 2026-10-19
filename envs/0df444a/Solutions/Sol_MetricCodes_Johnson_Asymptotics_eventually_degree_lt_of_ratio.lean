-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.eventually_degree_lt_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/b5e16988-bf81-4dfe-9956-ec0481943fca

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.Asymptotics
theorem _root_.solution
    {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hg : Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, f n < g n := by
  have hnegative : a - b < 0 := sub_neg.mpr hab
  have hratio :=
    (hf.sub hg).eventually (gt_mem_nhds hnegative)
  filter_upwards [hratio, eventually_gt_atTop (0 : ℕ)]
    with n hdiff hn
  have hnreal : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hquot : (f n : ℝ) / (n : ℝ) <
      (g n : ℝ) / (n : ℝ) := by
    linarith
  have hreal : (f n : ℝ) < (g n : ℝ) :=
    (div_lt_div_iff_of_pos_right hnreal).mp hquot
  exact_mod_cast hreal
end MetricCodes.Johnson.Asymptotics
