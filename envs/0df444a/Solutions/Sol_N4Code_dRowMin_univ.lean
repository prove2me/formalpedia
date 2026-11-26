-- Prove2me | solution 1 for N4Code.dRowMin_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:59.607639+00:00
-- url     : https://prove2.me/submissions/d37d1eff-9315-4996-b57b-8b880cb88008

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_P2M_N4Code_min__proof_irrel_1e0402de89ff
import Theorems.Thm_N4Code_dCode_le_dRow


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (y : Word n) :
    dRowMin C (Finset.univ : Finset (Fin 4)) (Finset.univ_nonempty) y = dCode C y := by
  have hle_row : ∀ i : Fin 4, dRowMin C (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty y ≤
      dRow C i y := by
    intro i
    unfold dRowMin
    exact Finset.min'_le ((Finset.univ : Finset (Fin 4)).image fun i => dRow C i y) (dRow C i y)
      (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  apply le_antisymm
  · unfold dCode
    change dRowMin C (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty y ≤
        min (dRow C 0 y) (min (dRow C 1 y) (min (dRow C 2 y) (dRow C 3 y)))
    apply le_min
    · exact hle_row 0
    · apply le_min
      · exact hle_row 1
      · apply le_min
        · exact hle_row 2
        · exact hle_row 3
  · unfold dRowMin
    have hm := Finset.min'_mem ((Finset.univ : Finset (Fin 4)).image (fun i => dRow C i y))
      (Finset.univ_nonempty.image (fun i => dRow C i y))
    rcases (Finset.mem_image.mp hm) with ⟨i, hi, hfi⟩
    calc
      dCode C y ≤ dRow C i y := dCode_le_dRow C i y
      _ = (Finset.univ.image (fun i => dRow C i y)).min'
          (Finset.univ_nonempty.image (fun i => dRow C i y)) := by
            simpa [min'_proof_irrel] using hfi
end N4Code
