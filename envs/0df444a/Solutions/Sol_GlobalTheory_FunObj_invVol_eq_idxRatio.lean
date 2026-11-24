-- Prove2me | solution 1 for GlobalTheory.FunObj.invVol_eq_idxRatio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:04.913472+00:00
-- url     : https://prove2.me/submissions/b7fc4470-f561-4ddf-ba82-ac1689272fdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InverseUnipotentVolumeConjDiagonalUnitsGLMul
import Theorems.Thm_GlobalTheory_FunObj_relIndex_congr_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.FunObj
theorem _root_.solution (C : Subgroup (GL (n ⊕ Fin c) k)) :
    invVol C = idxRatio (symN k n c ⊓ KO k _) (symN k n c ⊓ C) := by
  rw [invVol, idxRatio, relIndex_congr_inf (A := C) (B := symN k n c ⊓ C),
    relIndex_congr_inf (A := KO k _) (B := symN k n c ⊓ KO k _)]
  · ext x; simp only [Subgroup.mem_inf]; tauto
  · ext x; simp only [Subgroup.mem_inf]; tauto
end GlobalTheory.FunObj
