-- Prove2me | solution 1 for GlobalTheory.genval_residue_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:10:07.491367+00:00
-- url     : https://prove2.me/submissions/5aa4e3b4-d00b-4427-a707-a52cdb1d9b6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAlgClosedTranscendentalSpecialisingEverywh
import Theorems.Thm_GlobalTheory_genval_descent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] {L : Type} [Field L]
    (V : ValuationSubring L) (ιV : K →+* V) (sV : V) (a : K)
    (hsa : sV - ιV a ∈ maximalIdeal V) (hne : sV - ιV a ≠ 0)
    (halg : ∀ v : V, ∃ p : Polynomial (Polynomial K), p ≠ 0 ∧
      p.eval₂ (eval₂RingHom ιV sV) v = 0) :
    Function.Bijective ((residue V).comp ιV) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  intro x
  obtain ⟨v, rfl⟩ := residue_surjective x
  obtain ⟨p, hp, hpv⟩ := halg v
  obtain ⟨q, hq, hqv⟩ := genval_descent ιV sV v a hsa hne _ p rfl hp hpv
  refine ⟨q * C (q.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hq, ?_⟩
  rw [eval₂_mul, hqv, zero_mul]
end GlobalTheory
