-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.isOpen_setOf_forall_not_mem_imp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:55.322861+00:00
-- url     : https://prove2.me/submissions/9e2f93c8-0cec-4c21-b3f7-eca184eff68c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite

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
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen {g : AdelicGLn.AdelicGL K n |
      ∀ v, v ∉ S → finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n} := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) => GL (Fin n) (v.adicCompletion K))
    (A := fun v => (GLnLocal.integralGL (v.adicCompletion K) n : Set _))
    (fun v => GLnLocal.isOpen_integralGL (v.adicCompletion K) n) (p := fun v => v ∉ S)
  exact (h.preimage continuous_snd).preimage (AdelicGLn.restrictedProductEquiv K n).continuous
end GroundTheory.Automorphic.Reduction
