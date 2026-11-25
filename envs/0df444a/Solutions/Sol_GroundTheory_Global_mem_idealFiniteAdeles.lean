-- Prove2me | solution 1 for GroundTheory.Global.mem_idealFiniteAdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:29:36.6184+00:00
-- url     : https://prove2.me/submissions/06a0aaeb-fa51-4516-b400-7e587903ce67

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure

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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure WithZero
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
namespace GroundTheory.Global
theorem _root_.solution {x : 𝔸ᶠ[K]} :
    x ∈ idealFiniteAdeles I ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (x v) ≤ exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) :=
  Iff.rfl
end GroundTheory.Global
