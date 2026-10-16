-- Prove2me | solution 1 for OAI.Paper256.cone_zero_slice
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:40:53.867754+00:00
-- url     : https://prove2.me/submissions/f1a22c36-a90b-4955-877c-e1324a2c925b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/ConeZero.lean:L31-L49
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.cone_zero_slice. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Theorems.Thm_OAI_Paper256_cone_iff_nonnegative_real_roots
import Theorems.Thm_OAI_Paper256_linePolynomial_zero_parameter

-- ---- from OAI.Analysis.HyperbolicCones.ConeZero ----
namespace OAI

noncomputable section

open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator

namespace Paper256

theorem charpoly_eval_eigenvalue (n : ℕ) (X : Sym n) (i : Fin n) :
    (X : Mat n ℝ).charpoly.eval ((sym_isHermitian X).eigenvalues i) = 0 := by
  rw [(sym_isHermitian X).charpoly_eq]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, RCLike.ofReal_real_eq_id, id_eq]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

theorem charpoly_real_roots_nonnegative (n : ℕ) (X : Sym n)
    (hX : (X : Mat n ℝ).PosSemidef) (t : ℝ)
    (ht : (X : Mat n ℝ).charpoly.eval t = 0) : 0 ≤ t := by
  rw [(sym_isHermitian X).charpoly_eq] at ht
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, RCLike.ofReal_real_eq_id, id_eq, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero] at ht
  obtain ⟨i, rfl⟩ := ht
  exact hX.eigenvalues_nonneg i

theorem cone_zero_slice (X Z : Sym 4) : ((X, Z), (0 : Fin 3 → ℝ)) ∈ cone ↔
    (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef := by
  rw [cone_iff_nonnegative_real_roots, linePolynomial_zero_parameter]
  constructor
  · intro h
    constructor
    · apply (sym_isHermitian X).posSemidef_iff_eigenvalues_nonneg.mpr
      intro i
      apply h ((sym_isHermitian X).eigenvalues i)
      simp [charpoly_eval_eigenvalue]
    · apply (sym_isHermitian Z).posSemidef_iff_eigenvalues_nonneg.mpr
      intro i
      apply h ((sym_isHermitian Z).eigenvalues i)
      simp [charpoly_eval_eigenvalue]
  · rintro ⟨hX, hZ⟩ t ht
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, mul_eq_zero,
      pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)] at ht
    exact ht.elim (charpoly_real_roots_nonnegative 4 X hX t)
      (charpoly_real_roots_nonnegative 4 Z hZ t)

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator


theorem solution : type_of% @_root_.OAI.Paper256.cone_zero_slice := @_root_.OAI.Paper256.cone_zero_slice
