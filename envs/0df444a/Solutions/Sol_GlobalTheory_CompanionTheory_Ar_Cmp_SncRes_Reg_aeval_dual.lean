-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.aeval_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:05:22.120979+00:00
-- url     : https://prove2.me/submissions/94159d51-dc67-47bc-b664-8c428ecb401c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
theorem _root_.solution (σ : Type) [Fintype σ] (w v : σ → ℂ) (g : MvPolynomial σ ℚ) :
    (aeval (fun q => (TrivSqZeroExt.inl (w q) + TrivSqZeroExt.inr (v q) : TrivSqZeroExt ℂ ℂ)) g).fst =
        eval w (map (algebraMap ℚ ℂ) g) ∧
    (aeval (fun q => (TrivSqZeroExt.inl (w q) + TrivSqZeroExt.inr (v q) : TrivSqZeroExt ℂ ℂ)) g).snd =
        ∑ q, eval w (pderiv q (map (algebraMap ℚ ℂ) g)) * v q := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a =>
    constructor
    · rw [aeval_C, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_inl, map_C, eval_C]
    · rw [aeval_C, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, map_C]
      simp
  | add p q hp hq =>
    constructor
    · simp only [map_add, TrivSqZeroExt.fst_add, hp.1, hq.1]
    · simp only [map_add, TrivSqZeroExt.snd_add, hp.2, hq.2, add_mul, Finset.sum_add_distrib]
  | mul_X p s hp =>
    constructor
    · rw [map_mul, aeval_X, TrivSqZeroExt.fst_mul, hp.1]
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul, map_X,
        eval_X]
    · rw [map_mul, aeval_X, TrivSqZeroExt.snd_mul, hp.2, hp.1]
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      have h : ∀ q, eval w (pderiv q (map (algebraMap ℚ ℂ) (p * X s))) * v q =
          (if q = s then eval w (map (algebraMap ℚ ℂ) p) * v q else 0) +
            w s * (eval w (pderiv q (map (algebraMap ℚ ℂ) p)) * v q) := by
        intro q
        rw [map_mul, map_X, Derivation.leibniz]
        by_cases hq : q = s
        · subst hq
          simp
          ring
        · simp [pderiv_X_of_ne (Ne.symm hq), hq]
          ring
      simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.mul_sum]
      ring
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
