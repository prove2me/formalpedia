-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PatGrp.pair_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:55:26.675961+00:00
-- url     : https://prove2.me/submissions/713b4381-3dc5-4873-88ba-2b386a540d27

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PatGrp
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}
namespace GlobalTheory.CompanionTheory.PatGrp
theorem _root_.solution {E : ι → ι → K} (hE : IsPatChar Φ E) {A B : Matrix ι ι K}
    (hA : Supp Φ A) (hB : Supp Φ B) : pair E (A * B) = 0 := by
  unfold pair
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hAk : A i k = 0
  · rw [hAk, zero_mul, mul_zero]
  by_cases hBk : B k j = 0
  · rw [hBk, mul_zero, mul_zero]
  rw [hE.2 i k j (hA i k hAk) (hB k j hBk), zero_mul]
end GlobalTheory.CompanionTheory.PatGrp
