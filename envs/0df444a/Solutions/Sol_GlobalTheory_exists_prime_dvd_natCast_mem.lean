-- Prove2me | solution 1 for GlobalTheory.exists_prime_dvd_natCast_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:45:50.586748+00:00
-- url     : https://prove2.me/submissions/6ae5b215-0b37-45ae-b48d-1ee68f5649bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNatCastMemDifferentIdealPowLe
import Theorems.Thm_GlobalTheory_CuspFormEvaluationSupplement_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Pointwise
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] {P : Ideal R} (hP : P.IsPrime) :
    ∀ N : ℕ, N ≠ 0 → (N : R) ∈ P → ∃ p : ℕ, p.Prime ∧ p ∣ N ∧ (p : R) ∈ P := by
  first
  | exact @_root_.GlobalTheory.CuspFormEvaluationSupplement.main
  | exact _root_.GlobalTheory.CuspFormEvaluationSupplement.main
  | (apply _root_.GlobalTheory.CuspFormEvaluationSupplement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CuspFormEvaluationSupplement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CuspFormEvaluationSupplement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CuspFormEvaluationSupplement.main ..)
end GlobalTheory
