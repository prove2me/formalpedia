-- Prove2me | solution 1 for GroundTheory.Global.splitsCompletely_iff_forall_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:47:41.293713+00:00
-- url     : https://prove2.me/submissions/356c7c50-1523-495d-af2f-6beea143c8f4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Theorems.Thm_GroundTheory_Global_SemiLocal_finrank_eq_ramificationIdx_mul_inertiaDeg


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
      ∀ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by
  constructor
  · intro h w
    obtain ⟨h1, h2⟩ := h w.1 w.2
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg L v w.1, h1, h2]
  · intro h w hw
    have := h ⟨w, hw⟩
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg L v w] at this
    exact mul_eq_one.mp this
end GroundTheory.Global
