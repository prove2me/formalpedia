-- Prove2me | solution 1 for GlobalTheory.JR.CompanionCharpoly.companion_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:31.982007+00:00
-- url     : https://prove2.me/submissions/9b979762-e0ba-4f7d-a7cc-ae1d2f12b2b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsCharpolyCoeffEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.CompanionCharpoly
namespace GlobalTheory.JR.CompanionCharpoly
theorem _root_.solution {k k' : Type} [CommRing k] [CommRing k'] (f : k →+* k') {r : ℕ} (p : Fin r → k) :
    (companion p).map f = companion (fun i => f (p i)) := by
  ext i j
  simp only [Matrix.map_apply, companion, Matrix.of_apply]
  split_ifs <;> simp
end GlobalTheory.JR.CompanionCharpoly
