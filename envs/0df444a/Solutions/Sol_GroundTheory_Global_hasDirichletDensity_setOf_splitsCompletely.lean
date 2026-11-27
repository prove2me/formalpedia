-- Prove2me | solution 1 for GroundTheory.Global.hasDirichletDensity_setOf_splitsCompletely
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:45:49.664581+00:00
-- url     : https://prove2.me/submissions/bb0736cc-5e50-4762-9250-a3c8366b857e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_hasDirichletDensity_iff_of_subset_of_isBoundedUnder
import Theorems.Thm_GroundTheory_Global_hasDirichletDensity_degreeOnePrimes
import Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_of_isGalois
import Theorems.Thm_GroundTheory_Global_hasDirichletDensity_primesAbove_iff
import Theorems.Thm_GroundTheory_Global_isBoundedUnder_primeIdealZetaSum_of_finite
import Theorems.Thm_GroundTheory_Global_finite_setOf_ramificationIdx_ne_one

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
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (K L)
namespace GroundTheory.Global
theorem _root_.solution [IsGalois K L] :
    {v : HeightOneSpectrum (𝓞 K) | SplitsCompletely L v}.HasDirichletDensity
      (1 / Module.finrank K L) := by
  set Spl := {v : HeightOneSpectrum (𝓞 K) | SplitsCompletely L v}
  have hT : ∀ v ∈ Spl, SplitsCompletely L v := fun v hv => hv
  have hsub : primesAbove L Spl ⊆ degreeOnePrimes K L := by
    intro w hw
    have hlies : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
    exact (hT _ hw w hlies).2
  have hdiff : degreeOnePrimes K L \ primesAbove L Spl ⊆
      {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.ramificationIdx (𝓞 K) ≠ 1} := by
    rintro w ⟨hw1, hw2⟩ he
    have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
    exact hw2 ((splitsCompletely_iff_of_isGalois L (w.under (𝓞 K)) w).mpr ⟨he, hw1⟩)
  have h1 : (primesAbove L Spl).HasDirichletDensity 1 :=
    (hasDirichletDensity_iff_of_subset_of_isBoundedUnder hsub
      (isBoundedUnder_primeIdealZetaSum_of_finite
        ((finite_setOf_ramificationIdx_ne_one K L).subset hdiff)) 1).mpr
      (hasDirichletDensity_degreeOnePrimes K L)
  have hn : (Module.finrank K L : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := L)).ne'
  refine (hasDirichletDensity_primesAbove_iff hT _).mp ?_
  rwa [mul_one_div_cancel hn]
end GroundTheory.Global
