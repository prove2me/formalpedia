-- Prove2me | solution 1 for GlobalTheory.Serre.iSupIndep_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:45:41.036447+00:00
-- url     : https://prove2.me/submissions/b9417221-faa0-4480-8e57-92ee8ae78713

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.Serre
namespace GlobalTheory.Serre
theorem _root_.solution {k V I : Type*} [Field k] [AddCommGroup V] [Module k V]
    (f : I → Module.End k V) (hf : ∀ i j, Commute (f i) (f j)) :
    iSupIndep fun χ : I → k ↦ ⨅ i, (f i).eigenspace (χ i) :=
  (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f fun i j φ ↦
    Module.End.mapsTo_maxGenEigenspace_of_comm (hf j i) φ).mono fun _ ↦
      iInf_mono fun i ↦ ((f i).genEigenspace _).monotone le_top
end GlobalTheory.Serre
