-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Bridge.val_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:52:02.345294+00:00
-- url     : https://prove2.me/submissions/99b8ab5d-f4a3-4960-af29-02eb42186bca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Bridge
open WithZero
namespace GlobalTheory.UnitLemma.Bridge
theorem _root_.solution {E : Type} [Field E] (v : Valuation E (WithZero (Multiplicative ℤ))) (π : E)
    (hπ : v π = exp (-1)) (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (hle : ∀ y, v y ≤ 1 → v (c y) ≤ 1) (y : E) :
    v (c y) = v y := by
  have hle2 : ∀ a b : E, b ≠ 0 → v a ≤ v b → v (c a) ≤ v (c b) := by
    intro a b hb h
    have hb' : c b ≠ 0 := by simpa using hb
    have h1 := hle (a / b) (by rw [map_div₀]; exact div_le_one_of_le₀ h zero_le')
    rw [map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 hb'))] at h1
    exact h1
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hcπ0 : c π ≠ 0 := by simpa using hπ0
  have h1 : v (c π) ≤ v π := by
    have : v (c π) < 1 := by
      by_contra h
      have := hle2 1 (c π) hcπ0 (by rw [map_one]; exact not_lt.1 h)
      rw [map_one, map_one, hc, hπ, ← exp_zero, exp_le_exp] at this
      omega
    rw [hπ]
    rw [← exp_log ((Valuation.ne_zero_iff v).2 hcπ0), ← exp_zero, exp_lt_exp] at this
    rw [← exp_log ((Valuation.ne_zero_iff v).2 hcπ0), exp_le_exp]
    omega
  have h2 : v (c π) = v π := by
    have := hle2 _ _ hπ0 h1
    rw [hc] at this
    exact le_antisymm h1 this
  by_cases hy : y = 0
  · simp [hy]
  have h3 : v y = v (π ^ (-log (v y))) := by
    rw [map_zpow₀, hπ, ← exp_zsmul]
    simp [exp_log ((Valuation.ne_zero_iff v).2 hy)]
  have h4 : v (c (π ^ (-log (v y)))) = v (π ^ (-log (v y))) := by
    rw [map_zpow₀, map_zpow₀, map_zpow₀, h2]
  refine le_antisymm ?_ ?_
  · exact (hle2 _ _ (zpow_ne_zero _ hπ0) h3.le).trans (h4.trans h3.symm).le
  · exact (h4.trans h3.symm).symm.le.trans (hle2 _ _ hy h3.ge)
end GlobalTheory.UnitLemma.Bridge
