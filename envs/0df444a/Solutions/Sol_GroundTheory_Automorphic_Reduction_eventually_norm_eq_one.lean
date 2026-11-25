-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.eventually_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:09:42.067549+00:00
-- url     : https://prove2.me/submissions/fb9f58fc-2a99-41f4-8190-f5b6571f5394

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight

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
theorem _root_.solution {k : K} (hk : k ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(k : v.adicCompletion K)‖ = 1 := by
  filter_upwards [GroundTheory.Global.IdeleGroup.eventually_norm_eq_one
    (GroundTheory.Global.IdeleGroup.diagonal K (Units.mk0 k hk))] with v hv
  exact hv
end GroundTheory.Automorphic.Reduction
