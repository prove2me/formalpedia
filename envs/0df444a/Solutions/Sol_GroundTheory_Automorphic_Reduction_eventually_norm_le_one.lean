-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.eventually_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:42.135313+00:00
-- url     : https://prove2.me/submissions/bc939b13-4c1c-4a2c-a0dd-a192df20ff37

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_le_one_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (k : K) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(k : v.adicCompletion K)‖ ≤ 1 := by
  filter_upwards [(algebraMap K 𝔸[K] k).2.2] with v hv
  exact norm_le_one_of_mem v hv
end GroundTheory.Automorphic.Reduction
