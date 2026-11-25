-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.sum_localCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:10.940218+00:00
-- url     : https://prove2.me/submissions/d2838644-fa75-4488-9768-4680425a7825

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
omit [DecidableEq ι]
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (z : CompletionsOver L v) :
    ∑ i, algebraMap (v.adicCompletion K) (CompletionsOver L v) (localCoord b v i z) *
      algebraMap L (CompletionsOver L v) (b i) = z := by
  have h := (Algebra.TensorProduct.basis (v.adicCompletion K) b).sum_repr
    ((tensorEquiv L v).symm z)
  have h2 := congrArg (tensorEquiv L v) h
  rw [AlgEquiv.apply_symm_apply, map_sum] at h2
  conv_rhs => rw [← h2]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.TensorProduct.basis_apply, map_smul, tensorEquiv_one_tmul, Algebra.smul_def]
  rfl
end GroundTheory.Global.AdeleBaseChange
