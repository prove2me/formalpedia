-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_le_of_non_strict_spectral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/5a9d636b-09f2-47b2-8c2f-788d2293a44f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_scale_gt
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_le
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_sameLevel_opening_strict_refinement
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_continuous_Phi_common_scale

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
    {j : ℕ} {s : ℝ} (hs : 0 < s)
    (a : Fin (j + 1) → ℝ) (b : Fin j → ℝ)
    (h : Interlacing a b) (hboundary : s ≤ 2 * Gamma a b) :
    levelRate j s ≤ Phi a b := by
  by_cases hlast : 0 < a (Fin.last j)
  · have honeA : scaleAmbient 1 a = a := by
      funext i
      exact scaleCoordinate_one (h.ambient_nonneg i)
    have honeB : scaleStabilizer 1 b = b := by
      funext i
      exact scaleCoordinate_one (h.stabilizer_pos i).le
    have hlimit :
        Tendsto
          (fun t : ℝ => Phi (scaleAmbient t a) (scaleStabilizer t b))
          (𝓝[>] (1 : ℝ)) (𝓝 (Phi a b)) := by
      have htend :=
        (continuous_Phi_common_scale a b).continuousAt (x := (1 : ℝ)) |>.tendsto
      rw [honeA, honeB] at htend
      exact htend.mono_left nhdsWithin_le_nhds
    apply le_of_forall_pos_le_add
    intro ε hε
    have hcost := hlimit.eventually
      (Iio_mem_nhds (lt_add_of_pos_right (Phi a b) hε))
    have hside : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), 1 < t :=
      self_mem_nhdsWithin
    letI : (𝓝[>] (1 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
    obtain ⟨t, ht, hPhi⟩ :=
      (hside.and hcost).exists
    have htpos : 0 < t := by linarith
    have hinter :
        Interlacing (scaleAmbient t a) (scaleStabilizer t b) :=
      h.scale htpos
    have hgain := Gamma_scale_gt h hlast ht
    have hgap :
        s < 2 * Gamma (scaleAmbient t a) (scaleStabilizer t b) := by
      linarith
    exact (levelRate_le hinter hgap).trans hPhi.le
  · have hzero : a (Fin.last j) = 0 :=
      le_antisymm (le_of_not_gt hlast) h.1
    cases j with
    | zero =>
        have ha0 : a 0 = 0 := by simpa using hzero
        rw [Gamma_zero, ha0] at hboundary
        norm_num [spectralAtom, quadraticCoordinate] at hboundary
        linarith
    | succ j =>
        obtain ⟨A, _, hA, hGamma, hPhi⟩ :=
          exists_sameLevel_opening_strict_refinement
            (Nat.succ_pos j) h hzero
        exact (levelRate_le hA (by linarith)).trans hPhi.le
end MetricCodes.Spherical.HigherHierarchy
