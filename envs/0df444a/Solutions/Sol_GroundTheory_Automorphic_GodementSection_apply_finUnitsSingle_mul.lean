-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSection.apply_finUnitsSingle_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:44:27.17864+00:00
-- url     : https://prove2.me/submissions/013b1a95-8f3b-4753-b2bf-bb0d053b38dd

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_FiniteIdeleDecomp
import Theorems.Thm_GroundTheory_Automorphic_GodementSection_finUnitAt_finUnitsSingle_of_notMem

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
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
namespace GroundTheory.Automorphic.GodementSection
theorem _root_.solution {E : Type*} {G : (FiniteAdeleRing (𝓞 K) K)ˣ → E}
    (hG : ∀ b b', (∀ w ∉ S, finUnitAt w b = finUnitAt w b') → G b = G b')
    (a : (v : S) → (v.1.adicCompletion K)ˣ) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    G (finUnitsSingle S a * b) = G b :=
  hG _ _ fun w hw ↦ by rw [map_mul, finUnitAt_finUnitsSingle_of_notMem S a hw, one_mul]
end GroundTheory.Automorphic.GodementSection
