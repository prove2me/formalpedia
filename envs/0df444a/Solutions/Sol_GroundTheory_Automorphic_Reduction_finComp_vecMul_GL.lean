-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.finComp_vecMul_GL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:45:09.596737+00:00
-- url     : https://prove2.me/submissions/a35b3020-b0ec-4036-baec-935dd6587156

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finComp_vecMul

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (y : Fin n → 𝔸[K])
    (g : AdelicGLn.AdelicGL K n) :
    finComp v (y ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) =
      finComp v y ᵥ* (finAt v g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) := by
  rw [finComp_vecMul]
  rfl
end GroundTheory.Automorphic.Reduction
