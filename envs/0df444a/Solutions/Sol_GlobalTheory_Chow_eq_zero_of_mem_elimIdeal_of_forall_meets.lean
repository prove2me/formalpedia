-- Prove2me | solution 1 for GlobalTheory.Chow.eq_zero_of_mem_elimIdeal_of_forall_meets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:10:46.013869+00:00
-- url     : https://prove2.me/submissions/432bffc5-f8ab-4cf6-b27b-680c9c855e4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeSaturationGenericHyperplaneSection
import Theorems.Thm_GlobalTheory_Chow_aeval_eq_zero_of_mem_elimIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
namespace GlobalTheory.Chow
theorem _root_.solution {K : Type} [Field K] {N : ℕ}
    {P : Ideal (MvPolynomial (Fin N) K)}
    (hP : ∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K,
      y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0)
    {f : MvPolynomial (Unit × Fin N) K} (hf : f ∈ elimIdeal Unit P) : f = 0 := by
  apply map_injective (algebraMap K (AlgebraicClosure K)) (algebraMap K _).injective
  rw [map_zero]
  apply MvPolynomial.funext
  intro t
  obtain ⟨y, hy, hyP, hs⟩ := hP (fun j => t ((), j))
  have := aeval_eq_zero_of_mem_elimIdeal (β := Unit) hyP hy (t := t) (fun _ => hs) hf
  rw [map_zero, eval_map, ← aeval_def, this]
end GlobalTheory.Chow
