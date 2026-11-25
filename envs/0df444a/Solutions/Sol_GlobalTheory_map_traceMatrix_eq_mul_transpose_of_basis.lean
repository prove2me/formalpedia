-- Prove2me | solution 1 for GlobalTheory.map_traceMatrix_eq_mul_transpose_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:18.502249+00:00
-- url     : https://prove2.me/submissions/8b576882-f133-410b-9417-9b96ff57c422

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_algebraMap_trace_eq_sum_algHom_of_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable {R S L ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing L] [IsDomain L]
  [Algebra R L] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {κ : Type*} (e : Basis ι R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (v : κ → S) :
    (Algebra.traceMatrix R v).map (algebraMap R L) =
      (Matrix.of fun i j => P j (v i)) * (Matrix.of fun i j => P j (v i)).transpose := by
  ext i k
  simp [algebraMap_trace_eq_sum_algHom_of_basis e hP, Matrix.mul_apply]
end GlobalTheory
