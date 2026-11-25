-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuReduce.isSm_ds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:01:15.379525+00:00
-- url     : https://prove2.me/submissions/64a4f4ce-ccd1-4080-b9ce-164295dfc5fb

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ReductionOfDerivedSeries
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuReduce_lieW_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuReduce
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
namespace GlobalTheory.CompanionTheory.BmuReduce
theorem _root_.solution {Hm : Mat n} (h : RepOn (UH Hm) σ) {X : Mat n} (hX : Lie Hm X) {u : H} (hu : IsSm (UH Hm) σ u) :
    IsSm (UH Hm) σ (ds σ X u) :=
  hu.dsW h (W := [X]) (lieW_of fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX)
end GlobalTheory.CompanionTheory.BmuReduce
