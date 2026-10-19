-- Prove2me | solution 1 for MIPRE.LIDT.prod_pow_patch
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:34.400196+00:00
-- url     : https://prove2.me/submissions/da634f0e-ce6d-46fc-8df7-74b3fb43f8e9

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Coefficients.lean (solution of MIPRE.LIDT.prod_pow_patch);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Coefficients_B

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT
open Finset
variable {F : Type*} [Field F] {n d : ℕ}
theorem _root_.solution (T : Finset (Fin n)) (u : Point F n) {t e : Fin n → Fin (d + 1)}
    (he : ∀ k ∈ T, e k = 0) :
    (∏ k ∈ T, u k ^ (t k : ℕ)) * ∏ k, u k ^ (e k : ℕ)
      = ∏ k, u k ^ ((patch T t e k : Fin (d + 1)) : ℕ) := by
  classical
  have h1 : ∏ k, u k ^ (e k : ℕ) = ∏ k ∈ univ.filter (fun k => k ∉ T), u k ^ (e k : ℕ) := by
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun k => k ∈ T)]
    rw [Finset.prod_eq_one fun k hk => by rw [he k (Finset.mem_filter.mp hk).2]; simp, one_mul]
  have h2 : ∏ k, u k ^ ((patch T t e k : Fin (d + 1)) : ℕ)
      = (∏ k ∈ univ.filter (fun k => k ∈ T), u k ^ (t k : ℕ))
        * ∏ k ∈ univ.filter (fun k => k ∉ T), u k ^ (e k : ℕ) := by
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun k => k ∈ T)]
    congr 1
    · exact Finset.prod_congr rfl fun k hk => by rw [patch, if_pos (Finset.mem_filter.mp hk).2]
    · exact Finset.prod_congr rfl fun k hk => by rw [patch, if_neg (Finset.mem_filter.mp hk).2]
  have hT : univ.filter (fun k : Fin n => k ∈ T) = T := by
    ext k
    simp
  rw [h1, h2, hT]
end MIPRE.LIDT
