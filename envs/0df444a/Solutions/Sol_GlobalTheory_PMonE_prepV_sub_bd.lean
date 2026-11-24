-- Prove2me | solution 1 for GlobalTheory.PMonE.prepV_sub_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:18:48.380823+00:00
-- url     : https://prove2.me/submissions/ca59d831-3a3d-40bd-9cf0-d19a217783dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne
import Theorems.Thm_GlobalTheory_PMonE_prepV_zero
import Theorems.Thm_GlobalTheory_PMonE_prepV_succ
import Theorems.Thm_GlobalTheory_PMonE_PrepBd_add
import Theorems.Thm_GlobalTheory_PMonE_PrepBd_mul
import Theorems.Thm_GlobalTheory_PMonE_PrepBd_map_pow
import Theorems.Thm_GlobalTheory_PMonE_prepV_bd
import Theorems.Thm_GlobalTheory_PMonE_PrepBd_map_pow_sub

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
theorem _root_.solution (p : ℕ) [Fact p.Prime] [CharP F p] {e D : ℕ} {M : ℕ → Matrix m m F} {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (hM : ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n)) {A B : Matrix m m F} (hA : PrepBd 1 A)
    (hB : PrepBd 1 B) (h : PrepBd ε (A - B)) :
    ∀ k n, 1 ≤ n → n + k ≤ D → PrepBd (δ * ε) (prepV (p ^ e) M A k n - prepV (p ^ e) M B k n) := by
  intro k
  induction k with
  | zero => intro n _ _ i j; simpa [prepV_zero] using mul_nonneg hδ hε
  | succ k ih =>
    intro n hn hk
    rw [prepV_succ, prepV_succ]
    have e1 : M (n + 1) + prepV (p ^ e) M A k (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)) -
        (M (n + 1) + prepV (p ^ e) M B k (n + 1) * B.map (fun a => a ^ (p ^ e) ^ (n + 1))) =
        (prepV (p ^ e) M A k (n + 1) - prepV (p ^ e) M B k (n + 1)) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)) +
        prepV (p ^ e) M B k (n + 1) *
          (A.map (fun a => a ^ (p ^ e) ^ (n + 1)) - B.map (fun a => a ^ (p ^ e) ^ (n + 1))) := by
      rw [Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e1]
    refine PrepBd.add ?_ ?_
    · simpa using PrepBd.mul (mul_nonneg hδ hε) zero_le_one (ih (n + 1) (by omega) (by omega)) (hA.map_pow _)
    · exact PrepBd.mul hδ hε (prepV_bd hδ hM hB k (n + 1) (by omega) (by omega))
        (PrepBd.map_pow_sub p e _ hA hB h)
end GlobalTheory.PMonE
