-- Prove2me | solution 1 for GlobalTheory.PMonE.preparation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:47:40.532301+00:00
-- url     : https://prove2.me/submissions/96e9775b-1988-498e-b966-7a5a4ee8527c

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
import Theorems.Thm_GlobalTheory_PMonE_prepV_sub_bd
import Theorems.Thm_GlobalTheory_PMonE_prep_fixed
import Theorems.Thm_GlobalTheory_PMonE_prep_identity

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
namespace GlobalTheory.PMonE
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (p : ℕ)
    [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → 1 ≤ D →
    ∀ M : ℕ → Matrix m m F, Normal 1 M → ∃ (A : Matrix m m F) (U : ℕ → Matrix m m F), (∀ i j, ‖A i j‖ ≤ 1) ∧
      (∀ i j, ‖(U 0 - 1) i j‖ < 1) ∧ (∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1) ∧ M 0 = -(U 0 * A) ∧
      ∀ x : m → F, gsum (p ^ e) D M x = gsum (p ^ e) D U (fun i => x i ^ p ^ e - A.mulVec x i) := by
  intro F _ _ _ p _ _ m _ _ e D _ hD M hM
  obtain ⟨δ, hδ, hδ1, hMδ⟩ : ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 ∧ ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n) := by
    let S : Finset (ℕ × m × m) := Icc 2 D ×ˢ univ
    refine ⟨((S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊ : NNReal) : ℝ), NNReal.coe_nonneg _, ?_, ?_⟩
    · have : (S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊) < 1 := by
        rw [Finset.sup_lt_iff (by simp)]
        intro t ht
        have h2 : 2 ≤ t.1 := (mem_Icc.1 (mem_product.1 ht).1).1
        exact_mod_cast hM.small t.1 (by omega) t.2.1 t.2.2
      exact_mod_cast this
    · intro n h2 hn i j
      have : ‖M n i j‖₊ ≤ S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊ :=
        Finset.le_sup (f := fun t : ℕ × m × m => ‖M t.1 t.2.1 t.2.2‖₊) (b := (n, i, j))
          (mem_product.2 ⟨mem_Icc.2 ⟨h2, hn⟩, mem_univ _⟩)
      exact_mod_cast this
  obtain ⟨k, rfl⟩ : ∃ k, D = k + 1 := ⟨D - 1, by omega⟩
  have hW : ∀ A : Matrix m m F, PrepBd 1 A →
      PrepBd δ (prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1)) := fun A hA => by
    have := PrepBd.mul hδ zero_le_one (prepV_bd (q := p ^ e) hδ hMδ hA k 1 le_rfl (by omega))
      (hA.map_pow ((p ^ e) ^ 1))
    rwa [mul_one] at this
  obtain ⟨A, hA, hfix⟩ := prep_fixed hδ hδ1 (M 0) (hM.int 0)
    (fun A => prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1)) hW (by
      intro A B ε hε hA hB h
      have e1 : prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1) -
          prepV (p ^ e) M B k 1 * B.map (fun a => a ^ (p ^ e) ^ 1) =
          (prepV (p ^ e) M A k 1 - prepV (p ^ e) M B k 1) * A.map (fun a => a ^ (p ^ e) ^ 1) +
          prepV (p ^ e) M B k 1 * (A.map (fun a => a ^ (p ^ e) ^ 1) - B.map (fun a => a ^ (p ^ e) ^ 1)) := by
        rw [Matrix.sub_mul, Matrix.mul_sub]; abel
      rw [e1]
      refine PrepBd.add ?_ ?_
      · have := PrepBd.mul (mul_nonneg hδ hε) zero_le_one
          (prepV_sub_bd p (e := e) hδ hε hMδ hA hB h k 1 le_rfl (by omega)) (hA.map_pow ((p ^ e) ^ 1))
        rwa [mul_one] at this
      · exact PrepBd.mul hδ hε (prepV_bd hδ hMδ hB k 1 le_rfl (by omega)) (PrepBd.map_pow_sub p e _ hA hB h))
  have hU0 : prepV (p ^ e) M A (k + 1 - 0) 0 = 1 + prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1) := by
    rw [Nat.sub_zero, prepV_succ, zero_add, hM.top]
  have h0 : M 0 = -(prepV (p ^ e) M A (k + 1 - 0) 0 * A) := by
    rw [hU0, Matrix.add_mul, Matrix.one_mul]
    have := eq_sub_iff_add_eq.1 hfix
    rw [this, neg_neg]
  refine ⟨A, fun n => prepV (p ^ e) M A (k + 1 - n) n, hA, ?_, ?_, h0, ?_⟩
  · intro i j
    beta_reduce
    rw [hU0, add_sub_cancel_left]
    exact (hW A hA i j).trans_lt hδ1
  · intro n hn i j
    beta_reduce
    by_cases h : n ≤ k + 1
    · exact (prepV_bd hδ hMδ hA _ n hn (by omega) i j).trans_lt hδ1
    · have : k + 1 - n = 0 := by omega
      simp [this, prepV_zero]
  · refine prep_identity p e (k + 1) M _ A (by simp [prepV_zero]) (fun n hn => ?_) h0
    have : k + 1 - n = (k + 1 - (n + 1)) + 1 := by omega
    beta_reduce
    rw [this, prepV_succ]
end GlobalTheory.PMonE
