-- Prove2me | solution 1 for GlobalTheory.HermSign.exists_perm_sgn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:29:21.89523+00:00
-- url     : https://prove2.me/submissions/d2ca7862-5bc9-4f45-b90d-c3728a222097

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
namespace GlobalTheory.HermSign
theorem _root_.solution {r m n : ℕ} (hr : r = m + n) (d : Fin r → ℂ) (hd : ∀ a, d a * d a = 1)
    (hs : ∑ a, d a = (m : ℂ) - n) :
    ∃ σ : Equiv.Perm (Fin r), ∀ a, d (σ a) = ((FD.sgn m (a : ℕ) : ℝ) : ℂ) := by
  classical
  have hd' : ∀ a, d a ≠ 1 → d a = -1 := fun a h => (mul_self_eq_one_iff.1 (hd a)).resolve_left h
  have h1 : ∑ a, d a = ∑ a, (2 * (if d a = 1 then (1 : ℂ) else 0) - 1) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · rw [h]; norm_num
    · rw [hd' a h]; norm_num
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, hs] at h1
  have h2 : ((Finset.univ.filter fun a => d a = 1).card : ℂ) = m := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h1
    have : (r : ℂ) = m + n := by exact_mod_cast hr
    linear_combination (-1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * this
  have h3 : Fintype.card {a : Fin r // (a : ℕ) < m} = Fintype.card {a // d a = 1} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt]
    have : (Finset.univ.filter fun a => d a = 1).card = m := by exact_mod_cast h2
    rw [this]; omega
  let e := Fintype.equivOfCardEq h3
  refine ⟨e.extendSubtype, fun a => ?_⟩
  by_cases ha : (a : ℕ) < m
  · have := e.extendSubtype_mem a ha
    simp [FD.sgn, ha, this]
  · have := hd' _ (e.extendSubtype_not_mem a ha)
    simp [FD.sgn, ha, this]
end GlobalTheory.HermSign
