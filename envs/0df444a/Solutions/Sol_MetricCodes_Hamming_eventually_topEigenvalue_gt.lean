-- Prove2me | solution 1 for MetricCodes.Hamming.eventually_topEigenvalue_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/492a42b3-ae6d-4531-842f-1c39735d9770

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_eventually_transverse_add_le_longitudinal
import Theorems.Thm_MetricCodes_Hamming_tendsto_terminalEdgeRayleigh
import Theorems.Thm_MetricCodes_Hamming_terminalEdgeRayleigh_le_top

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {a b s : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ (1 : ℝ) / 2)
    (hs : s < MetricCodes.hammingGamma a b) :
    ∀ᶠ n : ℕ in atTop,
      s < topEigenvalue n
        (transverseDegree b n) (longitudinalDegree a n) := by
  have ha0 : 0 < a := lt_of_le_of_lt hb hba
  have ha1 : a < 1 := lt_of_le_of_lt ha (by norm_num)
  have hsecond : 0 < 1 - a - b := by linarith
  have hgamma : 0 < MetricCodes.hammingGamma a b := by
    unfold MetricCodes.hammingGamma
    apply div_pos
    · exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hba)) hsecond
    · exact Real.sqrt_pos.2 (mul_pos ha0 (sub_pos.mpr ha1))
  let ε : ℝ := (MetricCodes.hammingGamma a b - s) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (MetricCodes.hammingGamma a b / ε)
  have hprod : MetricCodes.hammingGamma a b < (m : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hm
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hrem : MetricCodes.hammingGamma a b / ((m : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hidentity :
      ((m : ℝ) / ((m : ℝ) + 1)) * MetricCodes.hammingGamma a b =
        MetricCodes.hammingGamma a b -
          MetricCodes.hammingGamma a b / ((m : ℝ) + 1) := by
    field_simp [hden.ne']
    ; ring
  have hbelow :
      s < ((m : ℝ) / ((m : ℝ) + 1)) * MetricCodes.hammingGamma a b := by
    rw [hidentity]
    dsimp [ε] at hrem
    linarith
  have hquot := (tendsto_terminalEdgeRayleigh ha0 ha1 hb m).eventually
    (lt_mem_nhds hbelow)
  filter_upwards [hquot,
    eventually_transverse_add_le_longitudinal hb hba m] with n hn hfit
  exact hn.trans_le (terminalEdgeRayleigh_le_top a b m n hfit)
end MetricCodes.Hamming
