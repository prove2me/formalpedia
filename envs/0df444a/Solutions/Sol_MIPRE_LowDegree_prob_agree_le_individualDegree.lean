-- Prove2me | solution 1 for MIPRE.LowDegree.prob_agree_le_individualDegree
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:46:28.102235+00:00
-- url     : https://prove2.me/submissions/b3b380e3-dee5-4fa9-9206-95f24f215b8f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/SchwartzZippel.lean (solution of MIPRE.LowDegree.prob_agree_le_individualDegree);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
theorem _root_.solution {f g : MvPolynomial (Fin m) F} (hfg : f ≠ g) {d : ℕ}
    (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d) :
    ((agree f g).card : ℝ) / (Fintype.card F : ℝ) ^ m ≤ (m : ℝ) * d / Fintype.card F := by
  have h : ((agree f g).card : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ m
      ≤ ∑ i : Fin m, ((f - g).degreeOf i : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
    have h₀ := MvPolynomial.schwartz_zippel_sum_degreeOf (sub_ne_zero.mpr hfg)
      (fun _ : Fin m => (univ : Finset F))
    rw [agree_eq_filter]
    simpa [Finset.card_univ, Finset.prod_const] using h₀
  have hd : ∀ i, (f - g).degreeOf i ≤ d := fun i =>
    (MvPolynomial.degreeOf_sub_le i f g).trans (max_le (hf i) (hg i))
  have hstep : ∑ i : Fin m, ((f - g).degreeOf i : ℚ≥0) / (Fintype.card F : ℚ≥0)
      ≤ (m : ℚ≥0) * d / (Fintype.card F : ℚ≥0) := by
    calc ∑ i : Fin m, ((f - g).degreeOf i : ℚ≥0) / (Fintype.card F : ℚ≥0)
        ≤ ∑ _i : Fin m, (d : ℚ≥0) / (Fintype.card F : ℚ≥0) :=
          Finset.sum_le_sum fun i _ => by gcongr; exact_mod_cast hd i
      _ = (m : ℚ≥0) * d / (Fintype.card F : ℚ≥0) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_div_assoc]
  have h' := NNRat.cast_mono (K := ℝ) (h.trans hstep)
  push_cast at h'
  exact h'
end MIPRE.LowDegree
