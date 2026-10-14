-- Prove2me | solution 1 for GenericBudgets.MaximinShare.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:19:12.227854+00:00
-- url     : https://prove2.me/submissions/9f214ea0-6462-4019-b125-76dc47ca47d3

import Mathlib
import Definitions.Def_GenericBudgets_MaximinShare_Setting
import Theorems.Thm_GenericBudgets_MaximinShare_total_price_le
import Theorems.Thm_GenericBudgets_MaximinShare_exists_cheap_parts
import Theorems.Thm_GenericBudgets_MaximinShare_le_of_affordable

open GenericBudgets.MaximinShare

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (b : Fin n → ℝ) (hb : ∀ i, 0 < b i) (hsum : ∑ i, b i = 1)
    (σ : Fin m → Fin n) (p : Fin m → ℝ) (hCE : IsCE v b σ p)
    (i : Fin n) (ℓ d : ℕ) (hd : 0 < d) (hℓd : (ℓ : ℝ) / d ≤ b i) :
    GuaranteesMMS v σ i ℓ d := by
  classical
  have hb1 : b i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => (hb j).le) (Finset.mem_univ i)
  have hℓ : ℓ ≤ d := by
    have hd' : (0:ℝ) < d := by exact_mod_cast hd
    have h : (ℓ:ℝ) ≤ d := (div_le_one hd').mp (hℓd.trans hb1)
    exact_mod_cast h
  intro T
  obtain ⟨L,hcard,hcheap⟩ := exists_cheap_parts p T ℓ hd hℓ
  refine ⟨L,hcard,le_of_affordable _ _ _ _ _ (hCE.2 i) ?_⟩
  have htotal : GenericBudgets.AlmostEqual.price p Finset.univ ≤ 1 := by
    simpa [hsum] using total_price_le v b σ p hCE
  calc
    GenericBudgets.AlmostEqual.price p (partsUnion T L) ≤
        ((ℓ:ℝ)/d)*GenericBudgets.AlmostEqual.price p Finset.univ := hcheap
    _ ≤ (ℓ:ℝ)/d := by
      simpa using mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ (ℓ:ℝ)/d)
    _ ≤ b i := hℓd
