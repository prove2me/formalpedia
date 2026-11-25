-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.aeval_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:39:52.648772+00:00
-- url     : https://prove2.me/submissions/1d53e24d-f059-4657-8204-351c55dd56d9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StandardSmoothChartOfNonzero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncRes GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
theorem _root_.solution {σ R : Type} [Fintype σ] [CommRing R] [Algebra ℤ R] {G : MvPolynomial σ ℤ} {n : ℕ}
    (hG : G.IsHomogeneous n) (κ : R) (a : σ → R) :
    aeval (fun j => κ * a j) G = κ ^ n * aeval a G := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = n := by
    have h := hG (mem_support_iff.1 hm)
    have e : Finsupp.weight (1 : σ → ℕ) m = ∑ i, m i := by
      simp [Finsupp.weight_apply, Finsupp.sum_fintype]
    rw [← e]
    exact h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring
end GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
