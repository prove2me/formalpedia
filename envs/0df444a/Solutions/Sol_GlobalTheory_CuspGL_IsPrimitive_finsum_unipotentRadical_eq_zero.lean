-- Prove2me | solution 1 for GlobalTheory.CuspGL.IsPrimitive.finsum_unipotentRadical_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:02:26.549988+00:00
-- url     : https://prove2.me/submissions/4cc3dda4-d28c-46c2-9875-300a6949fd9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsStandardUnipotentRadicalBijOnNilradicalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumUnipotentRadicalEqZero
import Theorems.Thm_GlobalTheory_T_exists_standardUnipotentRadical_bijOn_nilradical


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
namespace IsPrimitive
theorem _root_.solution (F : Type) [Field F] [Finite F] (d : ℕ)
    (φ : Module.End F (Fin d → F) → ℂ) (hφ : IsPrimitive φ) (a : ℕ) (ha : 0 < a) (had : a < d) :
    ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d,
      (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)},
      φ (Matrix.toLin' (u : Matrix (Fin d) (Fin d) F)) = 0 := by
  obtain ⟨A, H, hA, hH, hbij⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F d a had.le
  have hbot : A ≠ ⊥ := by
    rintro rfl
    rw [finrank_bot] at hA
    omega
  have htop : A ≠ ⊤ := by
    rintro rfl
    rw [finrank_top, Module.finrank_fin_fun] at hA
    omega
  rw [← hH, ← hφ A hbot htop 1 (fun x hx => hx)]
  refine finsum_mem_eq_of_bijOn _ hbij fun u _ => ?_
  simp only [add_sub_cancel]
end IsPrimitive
end GlobalTheory.CuspGL
