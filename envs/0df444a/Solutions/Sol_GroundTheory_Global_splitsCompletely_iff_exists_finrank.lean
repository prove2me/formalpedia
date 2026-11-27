-- Prove2me | solution 1 for GroundTheory.Global.splitsCompletely_iff_exists_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:39.817306+00:00
-- url     : https://prove2.me/submissions/67353260-a52e-4b36-b1c8-4f7d6f0f4a89

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_forall_finrank
import Theorems.Thm_GroundTheory_Global_nonempty_placesOver
import Theorems.Thm_GroundTheory_Global_finrank_eq_of_isGalois

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
theorem _root_.solution [IsGalois K L] :
    SplitsCompletely L v ↔
      ∃ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by
  rw [splitsCompletely_iff_forall_finrank]
  refine ⟨fun h ↦ ?_, fun ⟨w, hw⟩ w' ↦ (finrank_eq_of_isGalois v w w').symm.trans hw⟩
  obtain ⟨w⟩ := nonempty_placesOver L v
  exact ⟨w, h w⟩
end GroundTheory.Global
