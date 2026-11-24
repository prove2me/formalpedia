-- Prove2me | solution 1 for GlobalTheory.Idele.exists_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:12:15.484101+00:00
-- url     : https://prove2.me/submissions/df42318b-cc01-43ec-9a59-9f825ccb7d31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_isClosed_valued_le
import Theorems.Thm_GlobalTheory_Idele_exists_exp_neg_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing
noncomputable section
open GlobalTheory GlobalTheory.Idele
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace GlobalTheory.Idele
theorem _root_.solution (v : HeightOneSpectrum R) (u : ℕ → v.adicCompletion K)
    (hu : ∀ m n : ℕ, n ≤ m → Valued.v (u m - u n) ≤ exp (-(n : ℤ))) :
    ∃ t : v.adicCompletion K, ∀ n : ℕ, Valued.v (t - u n) ≤ exp (-(n : ℤ)) := by
  have hc : CauchySeq u := by
    rw [(Valued.hasBasis_uniformity (v.adicCompletion K) ℤᵐ⁰).cauchySeq_iff']
    intro γ _
    obtain ⟨n, hn⟩ := exists_exp_neg_lt
      (γ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1) (by simp)
    refine ⟨n, fun m hm => ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    rw [Valuation.map_sub_swap]
    exact (hu m n hm).trans_lt hn
  obtain ⟨t, ht⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨t, fun n => ?_⟩
  refine (isClosed_valued_le (K := K) v (-(n : ℤ))).mem_of_tendsto (ht.sub_const (u n)) ?_
  filter_upwards [Filter.eventually_ge_atTop n] with m hm using hu m n hm
end GlobalTheory.Idele
