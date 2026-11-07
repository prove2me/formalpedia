-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.basis_density_bounds_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T00:41:19.187032+00:00
-- url     : https://prove2.me/submissions/120c1fea-cdf7-4e7e-957e-d9f5f51fcbd5

import Mathlib
import Definitions.Def_OAIQ098E126
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_amplitude_endpoints_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_uAmplitude_bound_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_u_norm_amplitude_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_v_norm_amplitude_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha


lemma basis_density_bounds_e_oai (n : ℕ) (hn : n%12 ∈ residues) (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖u n j.val t‖ ≤ densityCap j ∧ ‖v n j.val t‖ ≤ densityCap j := by
  rw [u_norm_amplitude_e,v_norm_amplitude_e]
  exact ⟨uAmplitude_bound_e n hn j ht,(amplitude_endpoints_e n hn j).2.2⟩

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.basis_density_bounds_e_oai := @OAI.SharpPlanar.IntegerBasis.basis_density_bounds_e_oai
