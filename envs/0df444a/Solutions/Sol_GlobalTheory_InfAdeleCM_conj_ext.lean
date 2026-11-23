-- Prove2me | solution 1 for GlobalTheory.InfAdeleCM.conj_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:36.92265+00:00
-- url     : https://prove2.me/submissions/467af7c1-7ad5-493f-b338-f888f5f0e3e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Theorems.Thm_GlobalTheory_InfAdeleCM_ext_eq_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.InfAdeleCM
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.InfAdeleCM
theorem _root_.solution [IsTotallyReal F] (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    starRingEnd ℂ (ext σ a) = ext σ a := by
  rw [ext_eq_ofReal, Complex.conj_ofReal]
end GlobalTheory.InfAdeleCM
