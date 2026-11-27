-- Prove2me | solution 1 for GroundTheory.LocalField.natDegree_monicOfCoeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:07.374189+00:00
-- url     : https://prove2.me/submissions/94141136-b66a-4420-8bae-286d8eda7ae6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_ExtensionsOfDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Polynomial IntermediateField ValuativeRel
open GroundTheory GroundTheory.LocalField
variable {R : Type*} [CommRing R]
namespace GroundTheory.LocalField
theorem _root_.solution [Nontrivial R] {n : ℕ} (c : Fin n → R) :
    (monicOfCoeffs c).natDegree = n := by
  rw [monicOfCoeffs, natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt c),
    natDegree_X_pow]
end GroundTheory.LocalField
