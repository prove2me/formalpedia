-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.lagrangeDenominator_eq_prod_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/37a5d9eb-5104-45b0-92a0-f7e67503d068

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    (a : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) :
    lagrangeDenominator a ℓ =
      ∏ j ∈ Finset.univ.erase ℓ,
        (quadraticCoordinate (a ℓ) - quadraticCoordinate (a j)) := by
  unfold lagrangeDenominator
  classical
  refine Finset.prod_bij (fun j _ => ℓ.succAbove j)
    (fun j _ => ?_) (fun i _ j _ hij => ?_) (fun j hj => ?_)
    (fun _ _ => rfl)
  · simp [Fin.succAbove_ne]
  · exact Fin.succAbove_right_injective hij
  · obtain ⟨hj', _⟩ := Finset.mem_erase.mp hj
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hj'
    exact ⟨i, Finset.mem_univ i, hi⟩
end MetricCodes.Spherical.HigherHierarchy
