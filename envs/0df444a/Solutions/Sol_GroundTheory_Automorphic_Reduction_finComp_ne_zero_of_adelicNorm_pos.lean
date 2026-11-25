-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.finComp_ne_zero_of_adelicNorm_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:50.993855+00:00
-- url     : https://prove2.me/submissions/d1e13a98-8e75-4511-9f06-4db69d53f4a0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
import Theorems.Thm_GroundTheory_Automorphic_Reduction_HasFiniteContent_finite_mulSupport


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
theorem _root_.solution {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (h : 0 < adelicNorm y) (v : HeightOneSpectrum (𝓞 K)) : finComp v y ≠ 0 := by
  intro h0
  apply h.ne'
  have hv : v ∈ hy.finite_mulSupport.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, h0, norm_zero]
    exact zero_ne_one
  rw [adelicNorm, finprod_eq_prod_of_mulSupport_subset _
    (s := hy.finite_mulSupport.toFinset) (fun u hu => hy.finite_mulSupport.mem_toFinset.2 hu),
    Finset.prod_eq_zero hv (by rw [h0, norm_zero]), mul_zero]
end GroundTheory.Automorphic.Reduction
