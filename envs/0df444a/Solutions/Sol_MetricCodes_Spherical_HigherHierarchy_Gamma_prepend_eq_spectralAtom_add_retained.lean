-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Gamma_prepend_eq_spectralAtom_add_retained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/ae6b2ea3-9496-4b42-9c9a-1522c6f259d4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_sum_lagrangeWeight

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
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (u v : ℝ)
    (h : Interlacing (prependAmbient u a) (prependStabilizer v b)) :
    Gamma (prependAmbient u a) (prependStabilizer v b) =
      spectralAtom u +
        ∑ i : Fin (r + 1),
          lagrangeWeight (prependAmbient u a)
              (prependStabilizer v b) i.succ *
            (spectralAtom (a i) - spectralAtom u) := by
  have hweights :
      lagrangeWeight (prependAmbient u a)
          (prependStabilizer v b) 0 +
        ∑ i : Fin (r + 1),
          lagrangeWeight (prependAmbient u a)
            (prependStabilizer v b) i.succ = 1 := by
    simpa [Fin.sum_univ_succ] using h.sum_lagrangeWeight
  unfold Gamma
  rw [Fin.sum_univ_succ]
  simp only [prependAmbient, Fin.cons_zero, Fin.cons_succ]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change lagrangeWeight (Fin.cons u a) (prependStabilizer v b) 0 +
    ∑ i : Fin (r + 1), lagrangeWeight (Fin.cons u a)
      (prependStabilizer v b) i.succ = 1 at hweights
  nlinarith [congrArg (fun z : ℝ => z * spectralAtom u) hweights]
end MetricCodes.Spherical.HigherHierarchy
