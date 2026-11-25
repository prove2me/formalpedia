-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.norm_le_one_of_mem_integralFiniteAdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:41.740163+00:00
-- url     : https://prove2.me/submissions/51396761-0187-47da-aca1-8f2504bad0b4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
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
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {a : FiniteAdeleRing (𝓞 K) K}
    (ha : a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ‖a v‖ ≤ 1 :=
  norm_le_one_of_mem v (ha v)
end GroundTheory.Automorphic.Reduction
