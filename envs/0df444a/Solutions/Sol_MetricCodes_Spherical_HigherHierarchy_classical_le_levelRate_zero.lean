-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.classical_le_levelRate_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/2c27129d-de65-453b-898e-d966c41e6d96

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_classicalThreshold_pos
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_strictMono
import Theorems.Thm_MetricCodes_Spherical_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_classicalThreshold_spectral
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_strictMonoOn

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
theorem _root_.solution {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) :
    MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) ≤
      levelRate 0 s := by
  have ha₀ : 0 < MetricCodes.classicalThreshold s :=
    MetricCodes.classicalThreshold_pos hs hs'
  let a : Fin 1 → ℝ := fun _ => MetricCodes.classicalThreshold s + 1
  let b : Fin 0 → ℝ := Fin.elim0
  have ha : Interlacing a b := by
    constructor
    · dsimp [a]
      linarith
    · intro i
      exact Fin.elim0 i
  have hboundary : spectralAtom (MetricCodes.classicalThreshold s) = s / 2 := by
    have h := MetricCodes.Spherical.classicalThreshold_spectral hs hs'
    rw [MetricCodes.Spherical.Gamma_zero ha₀] at h
    change 2 * spectralAtom (MetricCodes.classicalThreshold s) = s at h
    linarith
  have hgap : s < 2 * Gamma a b := by
    rw [Gamma_zero]
    have hmono := spectralAtom_strictMonoOn ha₀.le
      (show 0 ≤ a 0 by dsimp [a]; linarith)
      (show MetricCodes.classicalThreshold s < a 0 by dsimp [a]; linarith)
    linarith
  have hnonempty : (levelRateSet 0 s).Nonempty :=
    ⟨Phi a b, a, b, ha, hgap, rfl⟩
  unfold levelRate
  apply le_csInf hnonempty
  rintro R ⟨A, B, hA, hgapA, rfl⟩
  rw [Gamma_zero] at hgapA
  rw [Phi_zero]
  have hAnonneg : 0 ≤ A 0 := hA.ambient_nonneg 0
  have hstrict : MetricCodes.classicalThreshold s < A 0 := by
    by_contra hnot
    have hle : A 0 ≤ MetricCodes.classicalThreshold s := le_of_not_gt hnot
    have hmono := spectralAtom_strictMonoOn.monotoneOn
      hAnonneg ha₀.le hle
    linarith
  exact (MetricCodes.Spherical.sphericalEntropy_strictMono
    ha₀.le hAnonneg hstrict).le
end MetricCodes.Spherical.HigherHierarchy
