-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.trace_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:03.959738+00:00
-- url     : https://prove2.me/submissions/783885f8-bcad-4568-959a-d411336d6c6b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace

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
open IsDedekindDomain NumberField TensorProduct Module Matrix
noncomputable section
open GroundTheory.Global.SemiLocal
variable {R : Type*} [Field R] {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, CommRing (S i)]
  [∀ i, Algebra R (S i)] [∀ i, Module.Finite R (S i)]
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (x : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        ((1 : v.adicCompletion K) ⊗ₜ[K] x) =
      algebraMap K (v.adicCompletion K) (Algebra.trace K L x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange]
end GroundTheory.Global.SemiLocal
