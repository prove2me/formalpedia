-- Prove2me | solution 1 for OAI.SevenEighths.EisensteinTheta.cosetTheta_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:40:12.954059+00:00
-- url     : https://prove2.me/submissions/837d61d9-a0ff-4b09-b5f6-114dee2d4f72

import Definitions.Def_OAI_NumberTheory_DirichletL_ThetaProduct
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_normForm_parity
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_hasSum


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MeasureTheory
open OAI.SevenEighths OAI.SevenEighths.EisensteinTheta
open ThetaProduct
namespace OAI.SevenEighths.EisensteinTheta
theorem _root_.solution (a b L : ℝ) (hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ =>
      (Real.exp (-Real.pi * normForm (a + L * n.1) (b + L * n.2) * t) : ℂ))
      (∑ e : Fin 2, (parityPair a b L hL e).f t) := by
  let F : Fin 2 × (ℤ × ℤ) → ℝ := fun p =>
    Real.exp (-Real.pi * (L ^ 2 * (p.2.1 + xShift a b L p.1) ^ 2 +
      (3 * L ^ 2) * (p.2.2 + yShift b L p.1) ^ 2) * t)
  have hsum (e : Fin 2) : HasSum (fun n : ℤ × ℤ => (F (e, n) : ℂ))
      ((parityPair a b L hL e).f t) :=
    rectangularPair_hasSum (xShift a b L e) (yShift b L e) (L ^ 2) (3 * L ^ 2) (sq_pos_of_pos hL)
      (mul_pos (by norm_num) (sq_pos_of_pos hL)) ht
  have hreal (e : Fin 2) : Summable (fun n : ℤ × ℤ => F (e, n)) :=
    Complex.summable_ofReal.mp (hsum e).summable
  have hF : Summable F :=
    (summable_prod_of_nonneg (fun _ => (Real.exp_pos _).le)).2
      ⟨hreal, (hasSum_fintype _).summable⟩
  have hFC : Summable (fun p => (F p : ℂ)) := Complex.summable_ofReal.mpr hF
  have hid (p : Fin 2 × (ℤ × ℤ)) :
      Real.exp (-Real.pi * normForm
        (a + L * (parityEquiv.symm p).1) (b + L * (parityEquiv.symm p).2) * t) = F p := by
    change Real.exp (-Real.pi * normForm
      (a + L * ((p.2.1 + p.2.2 : ℤ) : ℝ))
      (b + L * ((p.2.2 * 2 + (p.1 : ℕ) : ℤ) : ℝ)) * t) = _
    push_cast
    rw [show (p.2.2 : ℝ) * 2 = 2 * p.2.2 from mul_comm _ _]
    rw [normForm_parity a b L hL.ne']
  apply parityEquiv.symm.hasSum_iff.mp
  change HasSum (fun p : Fin 2 × (ℤ × ℤ) =>
    (Real.exp (-Real.pi * normForm (a + L * (parityEquiv.symm p).1)
      (b + L * (parityEquiv.symm p).2) * t) : ℂ)) _
  simp_rw [hid]
  convert hFC.hasSum using 1
  rw [hFC.tsum_prod, tsum_fintype]
  exact (Finset.sum_congr rfl (fun e _ => (hsum e).tsum_eq)).symm
end OAI.SevenEighths.EisensteinTheta
