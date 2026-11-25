-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.localCoord_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:08.812317+00:00
-- url     : https://prove2.me/submissions/9428dc8c-aaa1-4796-8892-4a6e360d6495

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
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (i : ι) (l : L) :
    localCoord b v i (algebraMap L (CompletionsOver L v) l) =
      algebraMap K (v.adicCompletion K) (b.repr l i) := by
  have : (tensorEquiv L v).symm (algebraMap L (CompletionsOver L v) l) = 1 ⊗ₜ l := by
    rw [AlgEquiv.symm_apply_eq, tensorEquiv_one_tmul]
  change (Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i
    ((tensorEquiv L v).symm (algebraMap L (CompletionsOver L v) l)) = _
  rw [this, Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul, one_smul,
    Finsupp.mapRange_apply]
end GroundTheory.Global.AdeleBaseChange
