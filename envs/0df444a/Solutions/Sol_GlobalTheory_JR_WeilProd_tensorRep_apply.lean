-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.tensorRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:57:58.590103+00:00
-- url     : https://prove2.me/submissions/634b9627-68f7-4003-a381-5b6979a2a022

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilProd
namespace GlobalTheory.JR.WeilProd
theorem _root_.solution {G H X Y : Type} (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) (g : G × H)
    (f : X × Y → ℂ) (p : X × Y) :
    tensorRep W₁ W₂ g f p = W₁ g.1 (fun u => W₂ g.2 (fun v => f (u, v)) p.2) p.1 := rfl
end GlobalTheory.JR.WeilProd
