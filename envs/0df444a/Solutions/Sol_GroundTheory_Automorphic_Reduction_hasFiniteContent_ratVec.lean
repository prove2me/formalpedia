-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.hasFiniteContent_ratVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:38:53.154862+00:00
-- url     : https://prove2.me/submissions/3e4e0654-32a9-47b2-b0b0-4d68702b3c3d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_eventually_norm_le_one
import Theorems.Thm_GroundTheory_Automorphic_Reduction_eventually_norm_eq_one

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
theorem _root_.solution {x : Fin n → K} (hx : x ≠ 0) : HasFiniteContent (ratVec x) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hx
  filter_upwards [eventually_all.2 fun i => eventually_norm_le_one (x i),
    eventually_norm_eq_one hi₀] with v h1 h2
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => h1 i) ?_
  rw [← h2]
  exact norm_le_pi_norm (finComp v (ratVec x)) i₀
end GroundTheory.Automorphic.Reduction
