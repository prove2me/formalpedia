-- Prove2me | solution 1 for GlobalTheory.PMonE.prepV_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:22.821597+00:00
-- url     : https://prove2.me/submissions/a43539ef-7a76-40cb-9c78-1fb399bc5703

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne
import Theorems.Thm_GlobalTheory_PMonE_prepV_zero
import Theorems.Thm_GlobalTheory_PMonE_prepV_succ
import Theorems.Thm_GlobalTheory_PMonE_PrepBd_add
import Theorems.Thm_GlobalTheory_PMonE_PrepBd_mul
import Theorems.Thm_GlobalTheory_PMonE_PrepBd_map_pow

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
namespace GlobalTheory.PMonE
theorem _root_.solution {q D : ℕ} {M : ℕ → Matrix m m F} {δ : ℝ} (hδ : 0 ≤ δ)
    (hM : ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n)) {A : Matrix m m F} (hA : PrepBd 1 A) :
    ∀ k n, 1 ≤ n → n + k ≤ D → PrepBd δ (prepV q M A k n) := by
  intro k
  induction k with
  | zero => intro n _ _ i j; simpa [prepV_zero] using hδ
  | succ k ih =>
    intro n hn hk
    rw [prepV_succ]
    refine (hM _ (by omega) (by omega)).add ?_
    simpa using PrepBd.mul hδ zero_le_one (ih (n + 1) (by omega) (by omega)) (hA.map_pow _)
end GlobalTheory.PMonE
