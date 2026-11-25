-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.algebraMap_trace_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:52:32.456921+00:00
-- url     : https://prove2.me/submissions/e07a76d5-e246-42b7-870a-b9fa62aa8adc

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Theorems.Thm_GroundTheory_Global_SemiLocal_trace_pi
import Theorems.Thm_GroundTheory_Global_SemiLocal_trace_one_tmul

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
    algebraMap K (v.adicCompletion K) (Algebra.trace K L x) =
      ∑ w : PlacesOver L v, Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L)
        (algebraMap L (w.1.adicCompletion L) x) := by
  rw [← trace_one_tmul, ← Algebra.trace_eq_of_algEquiv (tensorEquiv L v), tensorEquiv_one_tmul,
    trace_pi]
  rfl
end GroundTheory.Global.SemiLocal
