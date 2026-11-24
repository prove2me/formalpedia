-- Prove2me | solution 1 for GlobalTheory.ThetaCone.isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:30:02.252214+00:00
-- url     : https://prove2.me/submissions/4a999578-504a-43b6-86b8-38ea6c428082

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ThetaConeIdealIsPrimeAndRingKrullDimLe
import Theorems.Thm_GlobalTheory_ThetaCone_eval_mul_of_isHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ThetaCone
open MvPolynomial Filter Topology Module ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
attribute [local instance] MvPolynomial.gradedAlgebra
variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
omit [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.ThetaCone
theorem _root_.solution {φ : ι → E → ℂ} {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) :
    I.IsHomogeneous (homogeneousSubmodule ι ℂ) := by
  intro i F hF
  have hdec : ((DirectSum.decompose (homogeneousSubmodule ι ℂ) F) i : MvPolynomial ι ℂ) =
      homogeneousComponent i F := decomposition.decompose'_apply F i
  rw [hdec]
  refine (hI _).mpr fun t z => ?_
  rw [eval_mul_of_isHomogeneous (fun c => φ c z) t (homogeneousComponent_isHomogeneous i F)]
  suffices hz : eval (fun c => φ c z) (homogeneousComponent i F) = 0 by rw [hz, mul_zero]

  have hn : F.totalDegree + 1 ≤ F.totalDegree + i + 1 := by omega
  have hsum : ∑ m ∈ Finset.range (F.totalDegree + i + 1), homogeneousComponent m F = F := by
    rw [← Finset.sum_subset (Finset.range_mono hn) (fun m _ hm => by
      apply homogeneousComponent_eq_zero
      simp only [Finset.mem_range, not_lt] at hm
      omega)]
    exact sum_homogeneousComponent F
  have hP : ∀ s : ℂ, (∑ m ∈ Finset.range (F.totalDegree + i + 1),
      Polynomial.C (eval (fun c => φ c z) (homogeneousComponent m F)) * Polynomial.X ^ m).eval s
        = (0 : Polynomial ℂ).eval s := by
    intro s
    have h0 := (hI F).mp hF s z
    rw [← hsum, map_sum] at h0
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h0]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [eval_mul_of_isHomogeneous (fun c => φ c z) s (homogeneousComponent_isHomogeneous m F)]
    ring
  have hc := congrArg (fun p => Polynomial.coeff p i) (Polynomial.funext hP)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero,
    Finset.sum_ite_eq, Finset.mem_range] at hc
  simpa [show i < F.totalDegree + i + 1 by omega] using hc
end GlobalTheory.ThetaCone
