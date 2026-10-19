-- Prove2me | solution 1 for MetricCodes.Spherical.GeneralSpectral.eventually_topEigenvalue_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/31e46077-c8d8-4146-8c77-3930f4cc0593

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_eventually_transverse_add_le_longitudinal
import Theorems.Thm_MetricCodes_Hamming_tendsto_terminalEdgeRayleigh
import Theorems.Thm_MetricCodes_Hamming_terminalEdgeRayleigh_le_top
import Theorems.Thm_MetricCodes_Gamma_pos
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_eventually_transverse_add_le_longitudinal
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_tendsto_terminalEdgeRayleigh
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_terminalEdgeRayleigh_le_top

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped BigOperators Nat Topology InnerProductSpace
open MetricCodes.Spherical.GeneralSpectral
namespace MetricCodes.Spherical.GeneralSpectral
theorem _root_.solution {a b s : ℝ}
    (hb : 0 ≤ b) (hba : b < a)
    (hs : s < 2 * MetricCodes.Gamma a b) :
    ∀ᶠ n : ℕ in atTop,
      s < SpherePacking.Jacobi.topEigenvalue
        n (transverseDegree b n) (longitudinalDegree a n) := by
  have ha : 0 < a := lt_of_le_of_lt hb hba
  have hgamma : 0 < 2 * MetricCodes.Gamma a b := by
    exact mul_pos (by norm_num) (MetricCodes.Gamma_pos hb hba)
  let g : ℝ := 2 * MetricCodes.Gamma a b
  let ε : ℝ := (g - s) / 2
  have hε : 0 < ε := by
    dsimp [ε, g]
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (g / ε)
  have hprod : g < (m : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hm
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hrem : g / ((m : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ hden).2
    nlinarith [hgamma]
  have hidentity :
      ((m : ℝ) / ((m : ℝ) + 1)) * g =
        g - g / ((m : ℝ) + 1) := by
    field_simp [hden.ne']
    ; ring
  have hbelow :
      s < ((m : ℝ) / ((m : ℝ) + 1)) * g := by
    rw [hidentity]
    dsimp [ε] at hrem
    linarith
  have hquot :=
    (tendsto_terminalEdgeRayleigh ha hb m).eventually
      (lt_mem_nhds (show
        s < ((m : ℝ) / ((m : ℝ) + 1)) *
          (2 * MetricCodes.Gamma a b) by
        simpa [g] using hbelow))
  filter_upwards [hquot,
    eventually_transverse_add_le_longitudinal hb hba m]
      with n hn hfit
  exact hn.trans_le (terminalEdgeRayleigh_le_top a b m n hfit)
end MetricCodes.Spherical.GeneralSpectral
