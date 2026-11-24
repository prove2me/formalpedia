-- Prove2me | solution 1 for GlobalTheory.FlagHook.Degree.flagDeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:17:11.679876+00:00
-- url     : https://prove2.me/submissions/f018a0dd-a613-41fa-b725-68729791e92b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_AltCoeffRho
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagDegreeVandermonde
import Theorems.Thm_GlobalTheory_FlagHook_Degree_signed_sum
import Theorems.Thm_GlobalTheory_FlagHook_Degree_eval_detE_rho
import Theorems.Thm_GlobalTheory_FlagHook_Degree_sum_permExp
import Theorems.Thm_GlobalTheory_FlagHook_Degree_multinomial_permExp

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
namespace GlobalTheory.FlagHook.Degree
theorem _root_.solution (u : ι → Fin N → ℝ) :
    flagDeg ι N u = ((dimFl ι N).factorial : ℝ) * ∏ τ, eval (u τ) (detE (rho N)) := by
  have hl : linRoot u = ∑ x : ι × Fin N, (-u x.1 x.2) • (X x : MvPolynomial (ι × Fin N) ℝ) := by
    simp [linRoot, smul_eq_C_mul]
  have hc : ∀ σ : ι → Equiv.Perm (Fin N), (linRoot u ^ dimFl ι N).coeff (permExp σ) =
      (((dimFl ι N).factorial : ℝ) / ∏ _τ : ι, ∏ m ∈ range N, (m.factorial : ℝ)) * ((-1) ^ dimFl ι N *
        ∏ τ, ∏ i, u τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ))) := by
    intro σ
    rw [hl, coeff_linearCombination_X_pow_of_fintype, Finsupp.sum_fintype _ _ (fun _ => rfl),
      if_pos (sum_permExp σ), multinomial_permExp, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finset.prod_congr rfl (fun x _ => neg_pow (u x.1 x.2) (permExp σ x)), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, sum_permExp, Fintype.prod_prod_type]
    simp [permExp]
  have hs : ((-1 : ℝ) ^ dimFl ι N) * (-1) ^ dimFl ι N = 1 := by
    rw [← mul_pow]; simp
  simp only [eval_detE_rho]
  rw [Finset.prod_div_distrib, ← mul_div_assoc, mul_div_right_comm]
  simp only [← signed_sum]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, flagDeg, degFl, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hc, Finset.prod_mul_distrib]
  linear_combination ((((dimFl ι N).factorial : ℝ) / ∏ _τ : ι, ∏ m ∈ range N, (m.factorial : ℝ)) *
    (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * ∏ τ, ∏ i, u τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ))) * hs
end GlobalTheory.FlagHook.Degree
