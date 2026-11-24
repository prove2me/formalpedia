-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.eval_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:19:24.486117+00:00
-- url     : https://prove2.me/submissions/2fb64769-2741-40cf-963e-544f46e5ecec

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishes
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_evalCoef_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_eval_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SubsetSum
namespace GlobalTheory.CompanionTheory.SubsetSum
theorem _root_.solution {U : Type} [CommRing U] [IsDomain U] (r : ℕ) (hr : 0 < r) (P Q : U[X])
    (hP : P.Monic) (hQ : Q.Monic) (hd : P.natDegree = r) {n : ℕ} (hn : n = r + Q.natDegree) {Φ} (hΦ : IsUniv n r Φ) :
    (Φ.map (evalCoef n (P * Q))).eval (P.coeff (r - 1)) = 0 := by
  let K := AlgebraicClosure (FractionRing U)
  let ι : U →+* K := (algebraMap (FractionRing U) K).comp (algebraMap U (FractionRing U))
  have hι : Function.Injective ι :=
    (algebraMap (FractionRing U) K).injective.comp (IsFractionRing.injective U (FractionRing U))
  have hdQ : (Q.map ι).natDegree = Q.natDegree := hQ.natDegree_map ι
  obtain ⟨M, hc, hM, he⟩ := eval_field r hr (P.map ι) (Q.map ι) (hP.map ι) (hQ.map ι)
    (by rw [hP.natDegree_map ι, hd])
  apply hι
  rw [map_zero, ← eval_map_apply, Polynomial.map_map, evalCoef_comp, Polynomial.map_mul, hM,
    ← coeff_map, hΦ K M (by rw [hc, hdQ, hn])]
  exact he
end GlobalTheory.CompanionTheory.SubsetSum
