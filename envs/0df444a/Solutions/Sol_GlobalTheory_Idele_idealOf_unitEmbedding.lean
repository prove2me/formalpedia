-- Prove2me | solution 1 for GlobalTheory.Idele.idealOf_unitEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:55:22.214576+00:00
-- url     : https://prove2.me/submissions/8b9ce939-f6e4-4448-ae4f-9d0ba4965e68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_AdicValuationCountFactors_valuation_eq_exp_neg_count


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
theorem _root_.solution (x : Kˣ) :
    idealOf (FiniteAdeleRing.unitEmbedding R K x) = FractionalIdeal.spanSingleton R⁰ (x : K) :=
  eq_of_count_eq (idealOf_ne_zero _) (FractionalIdeal.spanSingleton_ne_zero_iff.2 x.ne_zero)
    fun v => by
      have := valued_idele (FiniteAdeleRing.unitEmbedding R K x) v
      rw [FiniteAdeleRing.unitEmbedding_apply, adele_algebraMap_apply, valued_algebraMap,
        valuation_eq_exp_neg_count v x.ne_zero, exp_inj] at this
      rw [count_idealOf]
      omega
end GlobalTheory.Idele
