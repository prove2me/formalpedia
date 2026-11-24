-- Prove2me | solution 1 for GlobalTheory.ThetaCone.isPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:42:24.417005+00:00
-- url     : https://prove2.me/submissions/032fb239-8261-4b73-a5ae-08968879b7f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ThetaConeIdealIsPrimeAndRingKrullDimLe
import Theorems.Thm_GlobalTheory_ThetaCone_differentiable_eval
import Theorems.Thm_GlobalTheory_ThetaCone_eq_zero_or_eq_zero_of_mul

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
namespace GlobalTheory.ThetaCone
theorem _root_.solution [FiniteDimensional ℂ E] {φ : ι → E → ℂ} (hφ : ∀ c, Differentiable ℂ (φ c))
    {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) : I.IsPrime := by
  refine Ideal.isPrime_iff.mpr ⟨fun htop => ?_, fun {F G} hFG => ?_⟩
  · have h1 := (hI 1).mp ((Ideal.eq_top_iff_one I).mp htop) 1 0
    simp at h1

  have hmul := (hI _).mp hFG
  have hψ : ∀ c, Differentiable ℂ (fun p : ℂ × E => p.1 * φ c p.2) := fun c =>
    differentiable_fst.mul ((hφ c).comp differentiable_snd)
  rcases eq_zero_or_eq_zero_of_mul (differentiable_eval hψ F) (differentiable_eval hψ G)
      (fun p => by simpa only [map_mul] using hmul p.1 p.2) with h | h
  · exact Or.inl ((hI F).mpr fun t z => h (t, z))
  · exact Or.inr ((hI G).mpr fun t z => h (t, z))
end GlobalTheory.ThetaCone
