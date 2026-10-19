-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_le_compactified_boundary_datum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/50d40790-8243-4e08-918b-a3c4558b7558

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_Gamma_lt_half
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_antitone_level
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_le_compactified_datum
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_le_of_non_strict_spectral

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
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r j : ℕ} {s c : ℝ}
    (hs : 0 < s) (hs' : s < 1)
    (hc : 0 < c) (hc' : c ≤ 1)
    (a : Fin (j + 1) → ℝ) (b : Fin j → ℝ)
    (h : Interlacing a b)
    (hscaled : s ≤ 1 - c ^ 2 * (1 - 2 * Gamma a b))
    (hlevels : (c = 1 ∧ j ≤ r) ∨ (c < 1 ∧ j + 1 ≤ r)) :
    levelRate r s ≤ Phi a b - Real.logb 2 c := by
  rcases hlevels with ⟨rfl, hjr⟩ | ⟨hc_lt, hjr⟩
  · have hboundary : s ≤ 2 * Gamma a b := by
      norm_num at hscaled ⊢
      linarith
    simpa using
      (levelRate_antitone_level hs hs' hjr).trans
        (levelRate_le_of_non_strict_spectral hs a b h hboundary)
  · have hpositive : 0 < 1 - 2 * Gamma a b := by
      linarith [h.Gamma_lt_half]
    have hlog :
        Tendsto (fun d : ℝ => Phi a b - Real.logb 2 d)
          (𝓝[<] c) (𝓝 (Phi a b - Real.logb 2 c)) := by
      exact tendsto_const_nhds.sub
        ((Real.continuousAt_logb hc.ne').tendsto.mono_left
          nhdsWithin_le_nhds)
    apply le_of_forall_pos_le_add
    intro ε hε
    have hcost := hlog.eventually
      (Iio_mem_nhds
        (lt_add_of_pos_right (Phi a b - Real.logb 2 c) hε))
    have hpos : ∀ᶠ d : ℝ in 𝓝[<] c, 0 < d :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
        (Ioi_mem_nhds hc)
    have hside : ∀ᶠ d : ℝ in 𝓝[<] c, d < c :=
      self_mem_nhdsWithin
    letI : (𝓝[<] c).NeBot := nhdsWithin_Iio_neBot le_rfl
    obtain ⟨d, hd_lt, hd_pos, hd_cost⟩ :=
      (hside.and (hpos.and hcost)).exists
    have hd_one : d < 1 := hd_lt.trans hc_lt
    have hsquare : d ^ 2 < c ^ 2 := by
      nlinarith [mul_pos hd_pos (sub_pos.mpr hd_lt),
        mul_pos hc (sub_pos.mpr hd_lt)]
    have hstrict : s < 1 - d ^ 2 * (1 - 2 * Gamma a b) := by
      nlinarith [mul_pos (sub_pos.mpr hsquare) hpositive]
    exact
      (levelRate_le_compactified_datum hs hs' hd_pos a b h hstrict
        (Or.inr ⟨hd_one, hjr⟩)).trans hd_cost.le
end MetricCodes.Spherical.HigherHierarchy
