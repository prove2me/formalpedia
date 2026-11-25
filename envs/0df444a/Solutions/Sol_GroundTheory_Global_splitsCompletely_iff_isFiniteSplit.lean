-- Prove2me | solution 1 for GroundTheory.Global.splitsCompletely_iff_isFiniteSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:11:53.917792+00:00
-- url     : https://prove2.me/submissions/eaf02f6b-0e86-4d5b-ac94-df119375c1ce

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Theorems.Thm_GroundTheory_Global_isFiniteSplit_pi_iff
import Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_forall_finrank

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
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Module
open scoped TensorProduct
open SemiLocal
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
variable {L} (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global
theorem _root_.solution :
    SplitsCompletely L v ↔
      Algebra.IsFiniteSplit (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) := by
  rw [splitsCompletely_iff_forall_finrank, ← isFiniteSplit_pi_iff]
  exact ⟨fun h ↦ .of_algEquiv (tensorEquiv L v).symm, fun h ↦ .of_algEquiv (tensorEquiv L v)⟩
end GroundTheory.Global
