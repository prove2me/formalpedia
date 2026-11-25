-- Prove2me | solution 1 for GroundTheory.Global.finrank_eq_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:55.405611+00:00
-- url     : https://prove2.me/submissions/f75c5266-23af-4cb4-9ac9-8e695ba0963d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting

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
theorem _root_.solution [IsGalois K L] (w w' : PlacesOver L v) :
    finrank (v.adicCompletion K) (w.1.adicCompletion L) =
      finrank (v.adicCompletion K) (w'.1.adicCompletion L) := by
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L) w w'
  exact (galEquiv v σ w.1 w'.1 (congrArg Subtype.val hσ.symm)).toLinearEquiv.finrank_eq
end GroundTheory.Global
