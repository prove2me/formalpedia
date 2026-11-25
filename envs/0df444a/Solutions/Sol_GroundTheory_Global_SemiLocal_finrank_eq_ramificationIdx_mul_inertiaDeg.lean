-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.finrank_eq_ramificationIdx_mul_inertiaDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:25:02.844904+00:00
-- url     : https://prove2.me/submissions/366f18ac-e259-486c-8c35-521f043d3592

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Approximation
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Theorems.Thm_GroundTheory_Global_SemiLocal_ramificationIdx_mul_inertiaDeg_le_finrank


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
open IsDedekindDomain NumberField TensorProduct Module
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  have h := (Finset.sum_eq_sum_iff_of_le
    (fun (w : PlacesOver L v) _ ↦ ramificationIdx_mul_inertiaDeg_le_finrank v w.1)).1
    (by rw [sum_ramificationIdx_mul_inertiaDeg, sum_finrank_eq])
  exact (h ⟨w, inferInstance⟩ (Finset.mem_univ _)).symm
end GroundTheory.Global.SemiLocal
