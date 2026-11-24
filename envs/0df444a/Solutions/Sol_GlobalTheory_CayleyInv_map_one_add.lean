-- Prove2me | solution 1 for GlobalTheory.CayleyInv.map_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:26.424545+00:00
-- url     : https://prove2.me/submissions/4b437db2-858a-4b90-b25b-0453553b5d24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.CayleyInv
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.CayleyInv
theorem _root_.solution (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    (1 + M).map σ = 1 + M.map σ := by
  rw [Matrix.map_add σ (map_add σ), Matrix.map_one σ (map_zero σ) (map_one σ)]
end GlobalTheory.CayleyInv
