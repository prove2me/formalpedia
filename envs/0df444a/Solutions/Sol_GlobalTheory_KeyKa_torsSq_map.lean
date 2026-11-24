-- Prove2me | solution 1 for GlobalTheory.KeyKa.torsSq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:43:20.136314+00:00
-- url     : https://prove2.me/submissions/d5aeb5da-d3c5-4061-b579-8c627a5e3cdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TorsSqMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
theorem _root_.solution : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) (R' : Type) [CommRing R'] (f : R →+* R') (t : R), TorsSq deg D t → TorsSq deg (D.map f) (f t) := by
  intro R Ix _ _ _ deg D R' _ f t H
  obtain ⟨h, h1, h2, e, h3⟩ := H
  refine ⟨h.map f, ?_, ?_, e, ?_⟩
  · intro p q hpq
    simp [Matrix.map_apply, h1 p q hpq]
  · have := congrArg (f.mapMatrix : Matrix Ix Ix R →+* Matrix Ix Ix R') h2
    rw [map_add, map_mul, map_mul, map_one] at this
    exact this
  · rw [h3, map_pow, RingHom.map_det]
    congr 2
    ext p q
    simp [Matrix.map_apply]
end GlobalTheory.KeyKa
