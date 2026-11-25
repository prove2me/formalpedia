-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.trace_mul_traceDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:15.803551+00:00
-- url     : https://prove2.me/submissions/11cc203b-31de-4d4b-8935-a949b9013df8

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
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (i j : ι) :
    Algebra.trace K L (b j * traceDual b i) = if j = i then 1 else 0 := by
  rw [mul_comm, ← Algebra.traceForm_apply]
  exact LinearMap.BilinForm.apply_dualBasis_left _ _ i j
end GroundTheory.Global.AdeleBaseChange
