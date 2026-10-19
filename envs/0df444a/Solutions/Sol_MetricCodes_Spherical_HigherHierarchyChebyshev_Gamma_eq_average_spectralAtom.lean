-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Gamma_eq_average_spectralAtom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/7d691484-694e-47cd-a81a-455cfcfb368f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_lagrangeWeight_eq_residue

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R)
    (r : ℕ) :
    MetricCodes.Spherical.HigherHierarchy.Gamma
      (ambient R r) (stabilizer R r) =
      (∑ ℓ : Fin (r + 1),
        MetricCodes.Spherical.HigherHierarchy.spectralAtom
          (ambient R r ℓ)) / ((r + 1 : ℕ) : ℝ) := by
  unfold MetricCodes.Spherical.HigherHierarchy.Gamma
  simp_rw [lagrangeWeight_eq_residue hR r]
  unfold residue
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  ring
end MetricCodes.Spherical.HigherHierarchyChebyshev
