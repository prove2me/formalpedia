-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.norm_mul_standardOpenSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:11.687172+00:00
-- url     : https://prove2.me/submissions/c63e261c-667e-42a0-88d1-db41b9f43da7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup


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
theorem _root_.solution (s : IdeleGroup K) {u : IdeleGroup K}
    (hu : u ∈ standardOpenSubgroup K) (v : HeightOneSpectrum (𝓞 K)) :
    ‖((s * u : IdeleGroup K) : 𝔸[K]).2 v‖ = ‖(s : 𝔸[K]).2 v‖ := by
  rw [Units.val_mul, adele_snd_mul_apply, norm_mul,
    norm_eq_one_of_mul_eq_one (finite_mul_inv u v) ((mem_standardOpenSubgroup K).1 hu v).1
      ((mem_standardOpenSubgroup K).1 hu v).2, mul_one]
end GroundTheory.Automorphic.Reduction
