-- Prove2me | solution 1 for GlobalTheory.FlagHook.Degree.multinomial_permExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:45:26.038478+00:00
-- url     : https://prove2.me/submissions/5d108d72-0bba-4bb1-a4d3-945543ecd54f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_AltCoeffRho
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagDegreeVandermonde
import Theorems.Thm_GlobalTheory_FlagHook_Degree_prod_rho_factorial
import Theorems.Thm_GlobalTheory_FlagHook_Degree_sum_permExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
noncomputable section
open GlobalTheory GlobalTheory.FlagHook GlobalTheory.FlagHook.Degree
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
omit [DecidableEq ι]
namespace GlobalTheory.FlagHook.Degree
theorem _root_.solution (σ : ι → Equiv.Perm (Fin N)) :
    ((permExp σ).multinomial : ℝ) =
      ((dimFl ι N).factorial : ℝ) / ∏ _τ : ι, ∏ m ∈ range N, (m.factorial : ℝ) := by
  have hne : (∏ _τ : ι, ∏ m ∈ range N, (m.factorial : ℝ)) ≠ 0 := by positivity
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), eq_div_iff hne, ← sum_permExp σ,
    ← Nat.multinomial_spec, Nat.cast_mul, mul_comm, Fintype.prod_prod_type]
  congr 1
  push_cast
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← prod_rho_factorial]
  exact (Fintype.prod_equiv (σ τ) _ _ (fun i => by simp [permExp])).symm
end GlobalTheory.FlagHook.Degree
