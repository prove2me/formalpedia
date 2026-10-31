-- Prove2me | solution 1 for HubSpokePricing.Lagrangian.theorem_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:06:48.182993+00:00
-- url     : https://prove2.me/submissions/e817548d-a1d1-47e6-a098-429d26eba7cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MarkovChain
import Definitions.Def_HubSpokePricing_Lagrangian_Model
import Theorems.Thm_HubSpokePricing_Lagrangian_theorem_4_1_feasible
import Theorems.Thm_HubSpokePricing_Lagrangian_proposition_3_1
import Theorems.Thm_HubSpokePricing_Lagrangian_lemma_4_2
import Theorems.Thm_HubSpokePricing_Lagrangian_lemma_4_3

open HubSpokePricing.Lagrangian

theorem solution (N : Network) (hN : N.Standing) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδm : δ < N.m)
    (lam : ℝ) (hlam : IsDualOpt N δ lam)
    (sol : Fin N.n → SpokeSol N.m) (hsol : ∀ i, SpokeOptimal N lam i (sol i))
    (μ : OrigState N → ℝ) (hμ : MarkovChain.IsStationary (origKernel N sol) μ)
    (x0 : Fin N.n → ℕ) (hx0 : InX N x0) :
    Vpi N sol μ ≤ VOPT N x0 ∧ VOPT N x0 ≤ VRstar N ∧
      VRstar N ≤ Vpi N sol μ + N.rbar * δ / ((N.m : ℝ) - δ) +
        (N.rbar + N.omega) * hubEmptyProb N μ := by
  refine ⟨theorem_4_1_feasible N hN lam hlam.1 sol hsol μ hμ x0 hx0, ?_, ?_⟩
  · -- Proposition 3.1: `V^OPT ≤ V̄^λ` for every `λ ≥ 0`, hence `V^OPT ≤ V^R`.
    have hxbar : InXbar N x0 := by
      intro i
      exact le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (x0 j)) (Finset.mem_univ i))
        hx0
    unfold VRstar VR
    apply le_ciInf
    intro l
    obtain ⟨h1, h2⟩ := proposition_3_1 N hN l.1 l.2
    rw [zero_mul, sub_zero, ← h1 x0 hxbar]
    exact h2 x0 hx0
  · obtain ⟨-, h42⟩ := lemma_4_2 N hN δ hδ0 hδm
    obtain ⟨h43a, h43b⟩ := lemma_4_3 N hN δ hδ0 hδm lam hlam sol hsol μ hμ
    linarith
