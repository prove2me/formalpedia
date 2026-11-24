-- Prove2me | solution 1 for GlobalTheory.Mem.FewPrimes.ncard_absNorm_eq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:44.321558+00:00
-- url     : https://prove2.me/submissions/9afbf84d-ea4f-4f62-8f1a-870e55beb3f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeMemHeightOneSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds
import Theorems.Thm_GlobalTheory_Mem_FewPrimes_prod_absNorm_dvd
import Theorems.Thm_GlobalTheory_Mem_FewPrimes_finite_absNorm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.FewPrimes
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.FewPrimes
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (p : ℕ) (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal = p}.ncard ≤ 2 := by
  have hf : {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal = p}.Finite :=
    (finite_absNorm_le (K := K) p).subset (fun v hv => by
      have hv' : Ideal.absNorm v.asIdeal = p := hv
      show (Ideal.absNorm v.asIdeal : ℝ) ≤ p
      rw [hv'])
  have h := prod_absNorm_dvd hf.toFinset (Ideal.span {(p : 𝓞 K)}) (fun v hv => by
    have hv' : Ideal.absNorm v.asIdeal = p := by simpa using hv
    rw [Ideal.dvd_span_singleton, ← hv']
    exact Ideal.absNorm_mem _)
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK,
    Finset.prod_congr rfl (g := fun _ => p) (fun v hv => by simpa using hv),
    Finset.prod_const] at h
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h
end GlobalTheory.Mem.FewPrimes
