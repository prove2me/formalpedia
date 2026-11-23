-- Prove2me | solution 1 for GlobalTheory.PMonE.PrepBd.map_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:18.645342+00:00
-- url     : https://prove2.me/submissions/bb97c804-313b-43fc-88a2-eda44d19edee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne
import Theorems.Thm_GlobalTheory_PMonE_PrepBd_add
import Theorems.Thm_GlobalTheory_PMonE_PrepBd_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] {m : Type} [Fintype m]
variable [IsUltrametricDist F]
omit [Fintype m]
namespace GlobalTheory.PMonE
namespace PrepBd
theorem _root_.solution (p : ℕ) [Fact p.Prime] [CharP F p] (e n : ℕ) {A B : Matrix m m F} {ε : ℝ}
    (hA : PrepBd 1 A) (hB : PrepBd 1 B) (h : PrepBd ε (A - B)) :
    PrepBd ε (A.map (fun a => a ^ (p ^ e) ^ n) - B.map (fun a => a ^ (p ^ e) ^ n)) := by
  intro i j
  have h1 : ‖A i j - B i j‖ ≤ 1 := by
    have := (hA.add hB.neg) i j
    simpa [sub_eq_add_neg] using this
  have h2 : ‖A i j - B i j‖ ≤ ε := h i j
  rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← pow_mul, ← sub_pow_char_pow, norm_pow]
  exact (pow_le_of_le_one (norm_nonneg _) h1 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).trans h2
end PrepBd
end GlobalTheory.PMonE
