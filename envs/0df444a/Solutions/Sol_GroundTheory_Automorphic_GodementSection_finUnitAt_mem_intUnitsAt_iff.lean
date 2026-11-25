-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSection.finUnitAt_mem_intUnitsAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:23.195889+00:00
-- url     : https://prove2.me/submissions/477cfe2d-151a-4e6f-bab3-6a0fc83fcb12

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_FiniteIdeleDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology GroundTheory.Global GroundTheory.LocalField
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Automorphic.GodementSection
theorem _root_.solution (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    finUnitAt v b ∈ intUnitsAt v ↔ (b : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
      ((b⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈
        v.adicCompletionIntegers K :=
  Iff.rfl
end GroundTheory.Automorphic.GodementSection
