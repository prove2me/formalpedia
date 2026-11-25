-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.HasFiniteContent.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:27:03.210519+00:00
-- url     : https://prove2.me/submissions/a29877b6-9649-4178-9470-3f18ded2602a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finComp_smul

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
namespace HasFiniteContent
theorem _root_.solution {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (s : GroundTheory.Global.IdeleGroup K) : HasFiniteContent ((s : 𝔸[K]) • y) := by
  filter_upwards [hy, GroundTheory.Global.IdeleGroup.eventually_norm_eq_one s] with v h1 h2
  rw [finComp_smul, norm_smul, h1, h2, mul_one]
end HasFiniteContent
end GroundTheory.Automorphic.Reduction
