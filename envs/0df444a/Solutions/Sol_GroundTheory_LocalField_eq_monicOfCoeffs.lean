-- Prove2me | solution 1 for GroundTheory.LocalField.eq_monicOfCoeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:48:10.844798+00:00
-- url     : https://prove2.me/submissions/dcb4600b-7240-4409-aaac-20a3d918d849

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
theorem _root_.solution {g : R[X]} (hg : g.Monic) {n : ℕ} (hn : g.natDegree = n) :
    g = monicOfCoeffs (fun i : Fin n ↦ g.coeff i) := by
  conv_lhs => rw [hg.as_sum, hn]
  rw [monicOfCoeffs, Fin.sum_univ_eq_sum_range (fun i ↦ C (g.coeff i) * X ^ i) n]
end GroundTheory.LocalField
