-- Prove2me | solution 1 for GroundTheory.Global.prod_one_add_rpow_neg_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:53.520348+00:00
-- url     : https://prove2.me/submissions/01e782fd-5715-4199-8e19-81fd6d6a3c33

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Global
theorem _root_.solution (P : Finset (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    ∏ w ∈ P, (1 + (absNorm w.asIdeal : ℝ) ^ (-s)) =
      ∑ I ∈ P.powerset.image (fun A => ∏ w ∈ A, w.asIdeal), (absNorm I : ℝ) ^ (-s) := by
  classical
  have hinj : Set.InjOn (fun A : Finset (HeightOneSpectrum (𝓞 K)) => ∏ w ∈ A, w.asIdeal)
      P.powerset := by
    have key : ∀ A B : Finset (HeightOneSpectrum (𝓞 K)),
        ∏ w ∈ A, w.asIdeal = ∏ w ∈ B, w.asIdeal → A ⊆ B := by
      intro A B hAB w hw
      have hle : ∏ w ∈ B, w.asIdeal ≤ w.asIdeal := by
        rw [← hAB]
        exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hw)
      obtain ⟨w', hw', hle'⟩ := (Ideal.IsPrime.prod_le w.isPrime).mp hle
      have : w' = w := HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top hle')
      exact this ▸ hw'
    intro A _ B _ hAB
    exact le_antisymm (key A B hAB) (key B A hAB.symm)
  rw [Finset.prod_one_add, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [map_prod, Nat.cast_prod, Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
end GroundTheory.Global
