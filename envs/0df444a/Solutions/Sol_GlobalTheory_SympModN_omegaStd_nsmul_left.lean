-- Prove2me | solution 1 for GlobalTheory.SympModN.omegaStd_nsmul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:02:43.38664+00:00
-- url     : https://prove2.me/submissions/1d9c64c9-5afb-4d36-b80b-c3fb36f9f381

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticSimilitudeInvertibleModN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SympModN
namespace GlobalTheory.SympModN
theorem _root_.solution {h : ℕ} (N : ℕ) (a b : Fin h ⊕ Fin h → ℤ) :
    omegaStd (N • a) b = N * omegaStd a b := by
  unfold omegaStd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, nsmul_eq_mul]
  ring
end GlobalTheory.SympModN
