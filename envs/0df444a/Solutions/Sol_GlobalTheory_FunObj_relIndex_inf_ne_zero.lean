-- Prove2me | solution 1 for GlobalTheory.FunObj.relIndex_inf_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:52:37.187722+00:00
-- url     : https://prove2.me/submissions/6696e27f-a912-43d4-849c-a4af4677b878

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InverseUnipotentVolumeConjDiagonalUnitsGLMul
import Theorems.Thm_GlobalTheory_FunObj_relIndex_ne_zero_of_isOpen


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
variable {G : Type*} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.FunObj
theorem _root_.solution {N O C H : Subgroup G} (hO : IsOpen (O : Set G)) (hC : IsCompact (C : Set G))
    (hHN : H ≤ N) (hHC : H ≤ C) : (N ⊓ O).relIndex H ≠ 0 := by
  intro h
  have h1 : O ⊓ H ≤ N ⊓ O := fun x hx => Subgroup.mem_inf.2 ⟨hHN (Subgroup.mem_inf.1 hx).2, (Subgroup.mem_inf.1 hx).1⟩
  have h2 := Subgroup.relIndex_eq_zero_of_le_left h1 h
  rw [Subgroup.inf_relIndex_right] at h2
  exact relIndex_ne_zero_of_isOpen hO hC hHC h2
end GlobalTheory.FunObj
