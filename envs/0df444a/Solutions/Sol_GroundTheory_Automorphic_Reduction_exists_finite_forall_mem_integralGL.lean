-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.exists_finite_forall_mem_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:21:40.372812+00:00
-- url     : https://prove2.me/submissions/ae8f46ac-6f77-4868-8cf7-77bab187d6ad

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
import Theorems.Thm_GroundTheory_Automorphic_Reduction_isOpen_setOf_forall_not_mem_imp
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
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {C : Set (AdelicGLn.AdelicGL K n)} (hC : IsCompact C) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ g ∈ C, ∀ v, v ∉ S →
      finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
  classical
  obtain ⟨T, hT⟩ := hC.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 K)) => {g : AdelicGLn.AdelicGL K n |
      ∀ v, v ∉ S → finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n})
    (fun S => isOpen_setOf_forall_not_mem_imp S) (fun g _ => by
      have hfin := Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL K n g)
      refine mem_iUnion.2 ⟨hfin.toFinset, fun v hv => ?_⟩
      by_contra h
      exact hv (hfin.mem_toFinset.2 h))
  refine ⟨T.sup id, fun g hg v hv => ?_⟩
  obtain ⟨S, hS, hgS⟩ := mem_iUnion₂.1 (hT hg)
  exact hgS v fun h => hv (Finset.mem_sup.2 ⟨S, hS, h⟩)
end GroundTheory.Automorphic.Reduction
