-- Prove2me | solution 1 for GlobalTheory.WittGauss.coeff_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:52.397661+00:00
-- url     : https://prove2.me/submissions/d45d509b-1630-4704-905b-7aaeb4b8b71e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittGauss
open WittVector
namespace GlobalTheory.WittGauss
theorem _root_.solution (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    [PerfectRing R p] (x y : WittVector p R) (n : ℕ)
    (h : (p : WittVector p R) ^ (n + 1) ∣ x - y) : x.coeff n = y.coeff n := by
  have h1 := (mem_span_p_pow_iff_le_coeff_eq_zero (x - y) (n + 1)).1 (Ideal.mem_span_singleton.2 h)
  have h2 := (mem_ker_truncate (n + 1) (x - y)).2 h1
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h2
  have h3 := congrArg (TruncatedWittVector.coeff (Fin.last n)) h2
  rwa [coeff_truncate, coeff_truncate, Fin.val_last] at h3
end GlobalTheory.WittGauss
