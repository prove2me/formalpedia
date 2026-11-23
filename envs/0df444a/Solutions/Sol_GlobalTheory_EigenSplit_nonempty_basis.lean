-- Prove2me | solution 1 for GlobalTheory.EigenSplit.nonempty_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:48.264822+00:00
-- url     : https://prove2.me/submissions/1b089612-b110-4f52-b27f-71620b6eb69f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
omit [DecidableEq ι]
namespace GlobalTheory.EigenSplit
theorem _root_.solution (hc : Fintype.card ι = Module.finrank ℚ E) :
    Nonempty (Module.Basis ι ℤ (𝓞 E)) :=
  ⟨(Module.finBasis ℤ (𝓞 E)).reindex (Fintype.equivFinOfCardEq
    (by rw [hc, NumberField.RingOfIntegers.rank])).symm⟩
end GlobalTheory.EigenSplit
