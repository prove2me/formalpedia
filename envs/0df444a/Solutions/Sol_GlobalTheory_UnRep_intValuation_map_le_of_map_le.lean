-- Prove2me | solution 1 for GlobalTheory.UnRep.intValuation_map_le_of_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:45:07.419595+00:00
-- url     : https://prove2.me/submissions/54008262-918b-4b46-a1c1-ec738cbd9d78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved

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
open GlobalTheory GlobalTheory.UnRep
namespace GlobalTheory.UnRep
theorem _root_.solution {R : Type} [CommRing R] [IsDedekindDomain R] (σ : R →+* R)
    (P : HeightOneSpectrum R) (h : P.asIdeal.map σ ≤ P.asIdeal) (a : R) :
    P.intValuation (σ a) ≤ P.intValuation a := by
  by_cases ha : a = 0
  · simp [ha]
  have h1 : P.intValuation a = WithZero.exp (-((Associates.mk P.asIdeal).count
      (Associates.mk (Ideal.span {a} : Ideal R)).factors : ℕ) : ℤ) := P.intValuation_if_neg ha
  set k := (Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal R)).factors
  have h2 : a ∈ P.asIdeal ^ k := (P.intValuation_le_pow_iff_mem a k).1 h1.le
  rw [h1, P.intValuation_le_pow_iff_mem]
  have h3 : (P.asIdeal ^ k).map σ ≤ P.asIdeal ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h k
  exact h3 (Ideal.mem_map_of_mem σ h2)
end GlobalTheory.UnRep
