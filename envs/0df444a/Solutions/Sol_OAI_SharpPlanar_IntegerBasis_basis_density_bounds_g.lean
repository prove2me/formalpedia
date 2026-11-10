-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.basis_density_bounds_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:11:58.040332+00:00
-- url     : https://prove2.me/submissions/ef3feccc-abff-4739-8eea-d9ad9ddf0de8

import Mathlib
import Definitions.Def_OAIQ098G235
import Definitions.Def_OAIQ098G322
import Definitions.Def_OAIQ098G365
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_amplitude_endpoints_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_uAmplitude_bound_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_u_norm_amplitude_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_v_norm_amplitude_g

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


lemma basis_density_bounds_g_oai (n : ℕ) (hn : n%12 ∈ residues) (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖u n j.val t‖ ≤ densityCap j ∧ ‖v n j.val t‖ ≤ densityCap j := by
  rw [u_norm_amplitude_g,v_norm_amplitude_g]
  exact ⟨uAmplitude_bound_g n hn j ht,(amplitude_endpoints_g n hn j).2.2⟩

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.basis_density_bounds_g_oai := @OAI.SharpPlanar.IntegerBasis.basis_density_bounds_g_oai
