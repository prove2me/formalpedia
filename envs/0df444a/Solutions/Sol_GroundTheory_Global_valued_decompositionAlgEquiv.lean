-- Prove2me | solution 1 for GroundTheory.Global.valued_decompositionAlgEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:20.938897+00:00
-- url     : https://prove2.me/submissions/0429b742-bab1-437d-8a03-27dac4f628ac

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Degree
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Theorems.Thm_GroundTheory_Global_valued_adicCompletionRingHomOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
omit [w.asIdeal.LiesOver v.asIdeal]
namespace GroundTheory.Global
theorem _root_.solution (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (y : w.adicCompletion L) : Valued.v (decompositionAlgEquiv v w σ y) = Valued.v y :=
  valued_adicCompletionRingHomOf σ.1 (smul_asIdeal_of_mem_stabilizer w σ) y
end GroundTheory.Global
