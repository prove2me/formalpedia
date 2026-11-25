-- Prove2me | solution 1 for GroundTheory.Global.eventually_coe_mem_localIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:51.266354+00:00
-- url     : https://prove2.me/submissions/6ed6d83d-65d0-401f-ba9e-58d632b10008

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Theorems.Thm_GroundTheory_Global_mem_localIdeal_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (x : K) :
    ∀ᶠ v in Filter.cofinite, (x : v.adicCompletion K) ∈ localIdeal I v := by
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, count K v I = 0 :=
    FractionalIdeal.finite_factors (K := K) I
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) x).2
  filter_upwards [h1, h2] with v hv1 hv2
  rw [mem_localIdeal_iff hI, hv1, neg_zero, exp_zero]
  exact hv2
end GroundTheory.Global
