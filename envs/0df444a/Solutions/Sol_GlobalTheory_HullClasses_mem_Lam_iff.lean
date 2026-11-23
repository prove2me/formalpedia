-- Prove2me | solution 1 for GlobalTheory.HullClasses.mem_Lam_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:25.523329+00:00
-- url     : https://prove2.me/submissions/40aaf9ad-500b-4f49-8993-2459c31bd91e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.HullClasses
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.HullClasses
theorem _root_.solution (y : B.A) : y ∈ abelian₂ B ↔ IsIntegral K.O y := by
  simp [abelian₂, mem_integralClosure_iff]
end GlobalTheory.HullClasses
