-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.psi_sub_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:43:46.37324+00:00
-- url     : https://prove2.me/submissions/4bba9742-46fd-4ccf-984c-4ab3325b0fea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)
namespace GlobalTheory.Lin.PsiToPi
theorem _root_.solution (P : ℕ → Prop) {u : ℝ} (hu : 1 ≤ u) :
    |(∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, wt P k| ≤ 2 * √u * Real.log u := by
  refine le_trans ?_ (Chebyshev.psi_sub_theta_le hu)
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), show wt P 0 = 0 by simp [wt], zero_add,
    show Finset.Icc 1 ⌊u⌋₊ = Finset.Ioc 0 ⌊u⌋₊ from rfl, Finset.sum_filter, ← Finset.sum_sub_distrib,
    Chebyshev.psi, Chebyshev.theta, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  have h0 : 0 ≤ Λ n := vonMangoldt_nonneg
  unfold wt
  by_cases hp : n.Prime <;> by_cases hP : P n <;> simp [hp, hP, vonMangoldt_apply_prime, abs_of_nonneg h0, h0]
end GlobalTheory.Lin.PsiToPi
