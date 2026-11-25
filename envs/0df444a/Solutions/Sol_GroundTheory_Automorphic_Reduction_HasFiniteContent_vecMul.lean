-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.HasFiniteContent.vecMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:54:59.788275+00:00
-- url     : https://prove2.me/submissions/83b7ed42-6ea7-4f23-9644-791ae3283f50

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finComp_vecMul_GL
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_vecMul_integralGL
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_eventually_mem_integralGL


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
    (g : AdelicGLn.AdelicGL K n) :
    HasFiniteContent (y ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  filter_upwards [hy, AdelicGLn.eventually_mem_integralGL K n g] with v h1 h2
  rw [finComp_vecMul_GL, finAt, norm_vecMul_integralGL v h2, h1]
end HasFiniteContent
end GroundTheory.Automorphic.Reduction
