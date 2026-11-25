-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.localCoord_eq_sum_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:08:13.942049+00:00
-- url     : https://prove2.me/submissions/32e5f6a8-43a3-4c46-8f85-958e336c9030

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_trace_mul_traceDual
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_apply
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_SemiLocal_trace_one_tmul
import Theorems.Thm_GroundTheory_Global_SemiLocal_trace_pi
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (i : ι) (z : CompletionsOver L v) :
    localCoord b v i z = ∑ w : PlacesOver L v, Algebra.trace (v.adicCompletion K)
      (w.1.adicCompletion L) (z w * algebraMap L (w.1.adicCompletion L) (traceDual b i)) := by
  have key : (Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i =
      (Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)).comp
        (LinearMap.mulRight (v.adicCompletion K) (1 ⊗ₜ traceDual b i)) := by
    refine (Algebra.TensorProduct.basis (v.adicCompletion K) b).ext fun j ↦ ?_
    rw [Basis.coord_apply, Basis.repr_self, LinearMap.comp_apply, LinearMap.mulRight_apply,
      Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      trace_one_tmul, trace_mul_traceDual, Finsupp.single_apply]
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  change (Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i
    ((tensorEquiv L v).symm z) = _
  rw [key, LinearMap.comp_apply, LinearMap.mulRight_apply,
    ← Algebra.trace_eq_of_algEquiv (tensorEquiv L v), map_mul, AlgEquiv.apply_symm_apply,
    tensorEquiv_one_tmul, trace_pi]
  rfl
end GroundTheory.Global.AdeleBaseChange
