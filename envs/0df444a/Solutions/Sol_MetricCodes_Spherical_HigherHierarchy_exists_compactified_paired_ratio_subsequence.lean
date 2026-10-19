-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_compactified_paired_ratio_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/435152c6-f412-473d-9e10-dd1006a86cab

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_quadraticCoordinate_ratio_of_tendsto_degree_ratio
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_interlacing_paired_degree_ratio_mem_Icc
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_paired_ratio_limit_pos_of_ambient_tendsto_atTop

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
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ}
    (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ)
    {C : ℝ}
    (h : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C) :
    ∃ (d : Fin r → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ i, d i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto
        (fun n => b (φ n) i / a (φ n) i.castSucc)
        atTop (nhds (d i))) ∧
      (∀ i, Tendsto (fun n => a (φ n) i.castSucc) atTop atTop →
        0 < d i) ∧
      (∀ i, Tendsto (fun n => a (φ n) i.castSucc) atTop atTop →
        Tendsto (fun n =>
          quadraticCoordinate (b (φ n) i) /
            quadraticCoordinate (a (φ n) i.castSucc))
          atTop (nhds (d i ^ 2))) := by
  let K : Set (Fin r → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)
  have hcompact : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  let f : ℕ → Fin r → ℝ := fun n i => b n i / a n i.castSucc
  have hmem : ∀ n, f n ∈ K := by
    intro n i _
    exact interlacing_paired_degree_ratio_mem_Icc (h n) i
  obtain ⟨d, hd, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmem
  have hratios : ∀ i : Fin r, Tendsto
      (fun n => b (φ n) i / a (φ n) i.castSucc)
      atTop (nhds (d i)) := by
    intro i
    exact (tendsto_pi_nhds.mp hlim) i
  refine ⟨d, φ, hφ, fun i => hd i (Set.mem_univ i), hratios, ?_, ?_⟩
  · intro i hai
    exact paired_ratio_limit_pos_of_ambient_tendsto_atTop
      h hPhi i hai (hratios i)
  · intro i hai
    exact tendsto_quadraticCoordinate_ratio_of_tendsto_degree_ratio
      hai (hratios i)
end MetricCodes.Spherical.HigherHierarchy
