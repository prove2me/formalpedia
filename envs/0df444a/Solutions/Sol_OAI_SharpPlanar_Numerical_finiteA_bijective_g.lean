-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.finiteA_bijective_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:24:18.660452+00:00
-- url     : https://prove2.me/submissions/1d07fa23-7a44-4bf9-ad3e-a89f2731ff64

import Mathlib
import Definitions.Def_OAIQ098G154
import Definitions.Def_OAIQ098G173
import Definitions.Def_OAIQ098G322
import Definitions.Def_OAIQ098G376
import Definitions.Def_OAIQ098G377
import Definitions.Def_OAIQ098G378
import Definitions.Def_OAIQ098G379
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_abs_bound_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_precision_pos_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_Lmat_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_centralIndex_injective_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectminus_lt_one_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectplus_lt_one_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_exteriorIndex_injective_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_exterior_exterior_norm_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_lowExteriorIndex_injective_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_signedVU_norm_g
import Theorems.Thm_OAI_SharpPlanar_finiteEmbedding_apply_g
import Theorems.Thm_OAI_SharpPlanar_finiteEmbedding_norm_g
import Theorems.Thm_OAI_SharpPlanar_finiteRestriction_bound_g
import Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_g
import Theorems.Thm_OAI_SharpPlanar_rowTable_bounds_g
import Theorems.Thm_OAI_SharpPlanar_sharp_S_tail_g
import Theorems.Thm_OAI_SharpPlanar_tailScalar_summable_g

section
-- module Solutions.OAIQ098_PP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite node coordinates

These coordinates enumerate the value and derivative data on the first
triangular shell nodes in the planar Fourier interpolation problem.
-/

namespace SharpPlanar.Numerical

open scoped BigOperators
lemma exteriorIndex_bound (i : Fin 48 × Fin 2) : 4 < (exteriorIndex i).1.val ∧ (exteriorIndex i).1.val ≤ 100 := by revert i; decide +kernel
lemma lowExteriorIndex_bound (i : Fin 12) : 4 < (lowExteriorIndex i).1.val ∧ (lowExteriorIndex i).1.val ≤ 16 := by revert i; decide +kernel
lemma lowExteriorIndex_cover_check : ∀ n : Fin 17, 4<n.val ∧ n.val%12∈residues → ∀ d : Bool,
    ∃ i : Fin 12, (lowExteriorIndex i).1.val=n.val ∧ (lowExteriorIndex i).2=d := by decide +kernel
lemma lowExteriorIndex_range (n : Node) (d : Bool) : (∃ i, lowExteriorIndex i = (n,d)) ↔ 4<n.val ∧ n.val ≤ 16 := by
  constructor
  · rintro ⟨i,hi⟩
    have hh := lowExteriorIndex_bound i
    simpa only [hi] using hh
  · rintro ⟨hn,hm⟩
    obtain ⟨i,hin,hid⟩ := lowExteriorIndex_cover_check ⟨n.val,Nat.lt_succ_of_le hm⟩ ⟨hn,n.prop.2⟩ d
    exact ⟨i,Prod.ext (Subtype.ext hin) hid⟩
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals
open scoped BigOperators

lemma column_bound_lt {n m : ℕ} {a : Matrix (Fin n) (Fin m) RBox}
    {A : Matrix (Fin n) (Fin m) ℝ} {u v : ℤ} (hv : 0 < v)
    (ha : ∀ i j, (a i j).Contains (A i j))
    (hc : ∀ j, (∑ i, (a i j).bound)*v < precision*u) :
    ∀ j, ∑ i, |A i j| < (u:ℝ)/v := by
  intro j
  have h₁ : (precision:ℝ)*(∑ i, |A i j|) ≤ (∑ i, ((a i j).bound:ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => RBox.abs_bound_g (ha i j)
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have h₂ : (∑ i, ((a i j).bound:ℝ))*(v:ℝ) < (precision:ℝ)*u := by
    exact_mod_cast hc j
  apply (mul_lt_mul_iff_right₀ precision_pos_g).mp
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hv').mpr
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h₁ hv'.le) h₂

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
open IntegerIntervals
open scoped BigOperators
lemma WplusBox_contains (i j : Fin 6) : (WplusBox i j).Contains (Wplus i j) := RBox.contains_rat_g _ _ (by norm_num)
lemma Wplus_column (j : Fin 6) : ∑ i, |Wplus i j| < (3084:ℝ)/100 := by
  apply column_bound_lt (u:=3084) (v:=100) (a:=WplusBox) (by norm_num) WplusBox_contains _ j
  intro k
  fin_cases k <;> decide +kernel
lemma WminusBox_contains (i j : Fin 6) : (WminusBox i j).Contains (Wminus i j) := RBox.contains_rat_g _ _ (by norm_num)
lemma Wminus_column (j : Fin 6) : ∑ i, |Wminus i j| < (183:ℝ)/100 := by
  apply column_bound_lt (u:=183) (v:=100) (a:=WminusBox) (by norm_num) WminusBox_contains _ j
  intro k
  fin_cases k <;> decide +kernel
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators

section
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

omit [DecidableEq ι] in
lemma matrixL1_apply (A : Matrix ι κ ℝ) (x : L1Finite κ) (i : ι) :
    matrixL1 A x i = ∑ j, A i j*x j := rfl

omit [DecidableEq ι] in
lemma matrixL1_mul (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) :
    matrixL1 (A*B) = (matrixL1 A).comp (matrixL1 B) := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toLpLin 1 1 (A*B) x = Matrix.toLpLin 1 1 A (Matrix.toLpLin 1 1 B x)
  rw [Matrix.toLpLin_mul (q:=1)]
  rfl
omit [DecidableEq ι] in
lemma matrixL1_sub (A B : Matrix ι κ ℝ) :
    matrixL1 (A-B) = matrixL1 A-matrixL1 B := by
  ext x i
  simp [matrixL1_apply,sub_mul,Finset.sum_sub_distrib]
lemma matrixL1_one : matrixL1 (1:Matrix ι ι ℝ) = 1 := by
  ext x i
  simp [matrixL1_apply,Matrix.one_apply]

omit [DecidableEq ι] in
lemma matrixL1_norm_le {A : Matrix ι κ ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ j, ∑ i, |A i j| ≤ b) : ‖matrixL1 A‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro x
  rw [l1Finite_norm_g,l1Finite_norm_g,Finset.mul_sum]
  calc
    ∑ i, |matrixL1 A x i| ≤ ∑ i, ∑ j, |A i j| * |x j| := by
      apply Finset.sum_le_sum
      intro i _
      rw [matrixL1_apply]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => A i j*x j) Finset.univ
    _ = ∑ j, (∑ i, |A i j|)* |x j| := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ ≤ ∑ j, b* |x j| := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hA j) (abs_nonneg _)

omit [DecidableEq ι] in
lemma matrixL1_norm_lt [Nonempty κ] {A : Matrix ι κ ℝ} {b : ℝ}
    (hA : ∀ j, ∑ i, |A i j| < b) : ‖matrixL1 A‖ < b := by
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun j : κ => ∑ i, |A i j|) Finset.univ_nonempty
  exact (matrixL1_norm_le (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    (fun k => hj k (Finset.mem_univ _))).trans_lt (hA j)
end

section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma approximate_inverse_estimate (A W : E →L[ℝ] E) {δ : ℝ}
    (hd : δ < 1) (h : ‖1-W*A‖ ≤ δ) (x : E) :
    ‖x‖ ≤ ‖W (A x)‖/(1-δ) := by
  have he : x = W (A x)+(1-W*A) x := by simp
  have hx : ‖x‖ ≤ ‖W (A x)‖+δ*‖x‖ := calc
    _ = ‖W (A x)+(1-W*A) x‖ := congrArg norm he
    _ ≤ ‖W (A x)‖+‖(1-W*A) x‖ := norm_add_le _ _
    _ ≤ ‖W (A x)‖+δ*‖x‖ := add_le_add le_rfl ((1-W*A).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right h (norm_nonneg _)))
  apply (le_div_iff₀ (by linarith : 0 < 1-δ)).mpr
  nlinarith
end Inverse
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteRestriction_apply (x : X) (i : ι) : finiteRestriction e he x i = x (e i) := rfl
end
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  (e : ι → Node × Bool) (he : Function.Injective e)
  (f : κ → Node × Bool)
lemma compressed_S_matrix :
    (finiteRestriction e he).comp (S.comp (finiteEmbedding f)) =
      matrixL1 (fun i j => S (lp.single 1 (f j) 1) (e i)) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply,finiteRestriction_apply]
  change S (∑ j, lp.single 1 (f j) (x j)) (e i) = _
  rw [map_sum]
  simp only [lp.coeFn_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (lp.single 1 (f j) (x j) : X) = (x j) • (lp.single 1 (f j) 1 : X) := by
    rw [← lp.single_smul]; simp
  rw [hs,map_smul]
  change x j * S (lp.single 1 (f j) 1) (e i) = S (lp.single 1 (f j) 1) (e i) * x j
  ring
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma certified_inverse_norm_le (A W : E →L[ℝ] E) {δ : ℝ}
    (hd : δ < 1) (h : ‖1-W*A‖ ≤ δ) :
    ‖(certifiedEquiv A W (h.trans_lt hd)).symm.toContinuousLinearMap‖ ≤ ‖W‖/(1-δ) := by
  have hd0 : 0 < 1-δ := sub_pos.mpr hd
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hd0.le)
  intro x
  have he : A ((certifiedEquiv A W (h.trans_lt hd)).symm x) = x :=
    (certifiedEquiv A W (h.trans_lt hd)).apply_symm_apply x
  calc
    ‖(certifiedEquiv A W (h.trans_lt hd)).symm x‖ ≤
        ‖W (A ((certifiedEquiv A W (h.trans_lt hd)).symm x))‖/(1-δ) :=
      approximate_inverse_estimate A W hd h _
    _ = ‖W x‖/(1-δ) := by rw [he]
    _ ≤ (‖W‖*‖x‖)/(1-δ) := div_le_div_of_nonneg_right (W.le_opNorm x) hd0.le
    _ = (‖W‖/(1-δ))*‖x‖ := by ring

end Inverse
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inverse bounds for the central interpolation block

Exact rational approximate inverses give bounds for the two central blocks.
-/

namespace SharpPlanar.Numerical
lemma defectplus_norm : ‖1-(matrixL1 Wplus)*(matrixL1 Aplus)‖ < (1:ℝ)/1000 := by
  have hh := matrixL1_norm_lt defectplus_column_g
  rw [matrixL1_sub,matrixL1_one,matrixL1_mul] at hh
  exact hh
lemma defectminus_norm : ‖1-(matrixL1 Wminus)*(matrixL1 Aminus)‖ < (1:ℝ)/1000 := by
  have hh := matrixL1_norm_lt defectminus_column_g
  rw [matrixL1_sub,matrixL1_one,matrixL1_mul] at hh
  exact hh
lemma Wplus_norm : ‖matrixL1 Wplus‖ < (3084:ℝ)/100 := matrixL1_norm_lt Wplus_column
lemma Wminus_norm : ‖matrixL1 Wminus‖ < (183:ℝ)/100 := matrixL1_norm_lt Wminus_column
lemma inversePlus_norm : ‖inversePlusEquiv.toContinuousLinearMap‖ < 32 := by
  have hh := certified_inverse_norm_le (matrixL1 Aplus) (matrixL1 Wplus)
    (by norm_num : (1:ℝ)/1000 < 1) defectplus_norm.le
  change ‖inversePlusEquiv.toContinuousLinearMap‖ ≤ _ at hh
  apply hh.trans_lt
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 1-1/1000)).mpr
  nlinarith [Wplus_norm]
lemma inverseMinus_norm : ‖inverseMinusEquiv.toContinuousLinearMap‖ < 32 := by
  have hh := certified_inverse_norm_le (matrixL1 Aminus) (matrixL1 Wminus)
    (by norm_num : (1:ℝ)/1000 < 1) defectminus_norm.le
  change ‖inverseMinusEquiv.toContinuousLinearMap‖ ≤ _ at hh
  apply hh.trans_lt
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 1-1/1000)).mpr
  nlinarith [Wminus_norm]
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Schur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

section Schur
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


omit [CompleteSpace F] in
theorem finite_schur_bound
    (V : E →L[ℝ] E) (U : F →L[ℝ] E) (L : E →L[ℝ] F) (D : F →L[ℝ] F)
    (hV : ‖V‖ ≤ 32) (hD : ‖D‖ ≤ 28/100) (hL : ‖L‖ ≤ 11/100)
    (hVU : ‖V.comp U‖ ≤ 37/10)
    {x rE : E} {y rF : F} (hx : x = V (rE + U y))
    (hy : y - L x - D y = rF) :
    ‖x‖ + ‖y‖ ≤ 90 * (‖rE‖ + ‖rF‖) := by
  have hxnorm : ‖x‖ ≤ 32 * ‖rE‖ + (37/10) * ‖y‖ := calc
    ‖x‖ = ‖V rE + (V.comp U) y‖ := by rw [hx]; simp
    _ ≤ ‖V rE‖ + ‖(V.comp U) y‖ := norm_add_le _ _
    _ ≤ ‖V‖ * ‖rE‖ + ‖V.comp U‖ * ‖y‖ := add_le_add (V.le_opNorm _) ((V.comp U).le_opNorm _)
    _ ≤ 32 * ‖rE‖ + (37/10) * ‖y‖ := by gcongr
  have hyrepr : y = rF + L x + D y := by rw [← hy]; abel
  have hynorm : ‖y‖ ≤ ‖rF‖ + (11/100) * ‖x‖ + (28/100) * ‖y‖ := calc
    ‖y‖ = ‖rF + L x + D y‖ := congrArg norm hyrepr
    _ ≤ ‖rF‖ + ‖L x‖ + ‖D y‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖rF‖ + ‖L‖ * ‖x‖ + ‖D‖ * ‖y‖ := by
      gcongr
      exacts [L.le_opNorm _, D.le_opNorm _]
    _ ≤ ‖rF‖ + (11/100) * ‖x‖ + (28/100) * ‖y‖ := by gcongr
  nlinarith [norm_nonneg rE, norm_nonneg rF]


end Schur
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite decompositions of ℓ¹ coordinates

The central and exterior coordinate blocks give an additive decomposition of the ℓ¹ norm.
-/

namespace SharpPlanar
open scoped BigOperators
section
variable {ι κ : Type*}
lemma l1Split_norm [Fintype ι] [Fintype κ] (x : L1Finite (ι ⊕ κ)) :
    ‖x‖ = ‖l1Left x‖+‖l1Right x‖ := by
  classical
  rw [l1Finite_norm_g, l1Finite_norm_g, l1Finite_norm_g, Fintype.sum_sum_type]
  rfl
end
end SharpPlanar
namespace SharpPlanar.Numerical
lemma finiteEmbedding_split (x : L1Finite FiniteIndex) :
    finiteEmbedding finiteIndex x = finiteEmbedding centralIndex (l1Left x) +
      finiteEmbedding exteriorIndex (l1Right x) := by
  ext k
  change finiteEmbedding finiteIndex x k = finiteEmbedding centralIndex (l1Left x) k + finiteEmbedding exteriorIndex (l1Right x) k
  simp only [finiteEmbedding_apply_g]
  change (∑ j, if finiteIndex j=k then x j else 0) =
    (∑ j, if centralIndex j=k then l1Left x j else 0)+
    (∑ j, if exteriorIndex j=k then l1Right x j else 0)
  rw [Fintype.sum_sum_type]
  rfl
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite coordinate projections

Restriction and extension identify the first shell coordinates with a finite
subspace of the absolutely summable interpolation space.
-/

namespace SharpPlanar
open scoped BigOperators
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteProjection_apply (x : X) (k : Node × Bool) :
    finiteEmbedding e (finiteRestriction e he x) k = if ∃ i, e i=k then x k else 0 := by
  classical
  rw [finiteEmbedding_apply_g]
  split_ifs with h
  · obtain ⟨i,rfl⟩ := h
    simp only [he.eq_iff, finiteRestriction_apply]
    simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (fun hh => h ⟨i,hh⟩)]
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tails of the interpolation operator

Coordinate projections and shell estimates bound the tails of the interpolation operator.
-/

namespace SharpPlanar
open scoped BigOperators
lemma tailScalar_eq (x : X) (N : ℕ) : tailScalar x N = rowTailNorm x N := by
  unfold tailScalar rowTailNorm
  rw [(tailScalar_summable_g x N).tsum_prod]
  change _ = ∑' n : {n : Node // n ∈ {n : Node | N<n.val}}, (fun n : Node => |x (n,false)|+|x (n,true)|) n.val
  rw [tsum_subtype {n : Node | N<n.val} (fun n : Node => |x (n,false)|+|x (n,true)|)]
  apply tsum_congr
  intro n
  simp only [tsum_fintype, Fintype.sum_bool, Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp [add_comm]
end SharpPlanar
namespace SharpPlanar.Numerical
open scoped BigOperators
lemma exterior_low_tail (x : X) : ‖RE x‖ ≤ ‖RL x‖ + rowTailNorm x 16 := by
  have hh := tsum_comp_le_tsum_of_inj (tailScalar_summable_g x 16)
    (fun k => by split_ifs <;> positivity) exteriorIndex_injective_g
  have hh' : (∑ i, if 16<(exteriorIndex i).1.val then |x (exteriorIndex i)| else 0)
      ≤ rowTailNorm x 16 := by
    rw [← tailScalar_eq]
    simpa only [Function.comp_apply,tsum_fintype,tailScalar] using hh
  have hi : ‖RE (IL (RL x))‖ ≤ ‖RL x‖ := by
    exact (finiteRestriction_bound_g _ exteriorIndex_injective_g _).trans_eq (by rw [one_mul,finiteEmbedding_norm_g _ lowExteriorIndex_injective_g])
  calc
    ‖RE x‖ ≤ ‖RE (IL (RL x))‖ +
        ∑ i, if 16<(exteriorIndex i).1.val then |x (exteriorIndex i)| else 0 := by
      rw [l1Finite_norm_g,l1Finite_norm_g,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      simp only [finiteRestriction_apply]
      rw [finiteProjection_apply]
      by_cases h : 16<(exteriorIndex i).1.val
      · simp only [h,ite_true, if_true]
        exact le_add_of_nonneg_left (abs_nonneg _)
      · have hmem : ∃ j, lowExteriorIndex j=exteriorIndex i :=
          (lowExteriorIndex_range (exteriorIndex i).1 (exteriorIndex i).2).mpr
            ⟨(exteriorIndex_bound i).1, Nat.le_of_not_gt h⟩
        rw [ite_eq_left hmem,ite_eq_right h,add_zero]
    _ ≤ ‖RL x‖ + rowTailNorm x 16 := add_le_add hi hh'
lemma compressed_low_L : RL.comp (S.comp IJ) = matrixL1 Lmat := by
  rw [compressed_S_matrix]
  rfl
lemma exterior_central_norm : ‖RE.comp (S.comp IJ)‖ ≤ (11:ℝ)/100 := by
  have hlow : ‖RL.comp (S.comp IJ)‖ ≤ (88:ℝ)/1000 := by
    rw [compressed_low_L]
    exact (matrixL1_norm_lt Lmat_column_g).le
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have h := exterior_low_tail (S (IJ x))
  have hL : ‖RL (S (IJ x))‖ ≤ (88:ℝ)/1000 * ‖x‖ :=
    ((RL.comp (S.comp IJ)).le_opNorm x).trans (mul_le_mul_of_nonneg_right hlow (norm_nonneg _))
  have ht := sharp_S_tail_g (IJ x) 16
  rw [finiteEmbedding_norm_g _ centralIndex_injective_g] at ht
  have ht' := mul_le_mul_of_nonneg_right rowTable_bounds_g.2.2.1.le (norm_nonneg x)
  change ‖RE (S (IJ x))‖ ≤ _
  nlinarith [norm_nonneg x]
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite interpolation system

Schur complements give existence, uniqueness and norm bounds for the finite system.
-/

namespace SharpPlanar.Numerical
lemma compressed_D : RJ.comp (S.comp IJ) = matrixL1 Dmat := by
  rw [compressed_S_matrix]; rfl
lemma centralV_norm (neg : Bool) : ‖centralV neg‖ ≤ 32 := by
  cases neg
  · exact inversePlus_norm.le
  · exact inverseMinus_norm.le
lemma signedL_norm (neg : Bool) : ‖signedL neg‖ ≤ (11:ℝ)/100 := by
  cases neg <;> simpa only [signedL,signedS,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,
    ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_neg,norm_neg] using exterior_central_norm
lemma signedE_norm (neg : Bool) : ‖signedE neg‖ ≤ (28:ℝ)/100 := by
  cases neg <;> simpa only [signedE,signedS,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,
    ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_neg,norm_neg] using exterior_exterior_norm_g
lemma centralV_left (neg : Bool) (x : L1Finite (Fin 6)) :
    centralV neg (x-RJ (signedS neg (IJ x))) = x := by
  have hD (y : L1Finite (Fin 6)) : RJ (S (IJ y)) = matrixL1 Dmat y :=
    congrArg (fun f => f y) compressed_D
  cases neg
  · change inversePlusEquiv (x-RJ (S (IJ x))) = x
    rw [hD]
    have hh := (certifiedEquiv (matrixL1 Aplus) (matrixL1 Wplus) defectplus_lt_one_g).symm_apply_apply x
    change inversePlusEquiv (matrixL1 Aplus x) = x at hh
    simpa only [Aplus,matrixL1_sub,matrixL1_one,sub_apply,one_apply_eq_self] using hh
  · change inverseMinusEquiv (x-RJ (-S (IJ x))) = x
    rw [map_neg,hD,sub_neg_eq_add]
    have hh := (certifiedEquiv (matrixL1 Aminus) (matrixL1 Wminus) defectminus_lt_one_g).symm_apply_apply x
    change inverseMinusEquiv (matrixL1 Aminus x) = x at hh
    have he : matrixL1 Aminus x = x+matrixL1 Dmat x := by
      ext i
      simp [Aminus,matrixL1_apply,Matrix.add_apply,Matrix.one_apply,add_mul,Finset.sum_add_distrib]
    rw [he] at hh
    exact hh
lemma finiteA_left (neg : Bool) (x : L1Finite FiniteIndex) :
    l1Left (finiteA neg x) = l1Left x - RJ (signedS neg (IJ (l1Left x))) - signedU neg (l1Right x) := by
  have hs := finiteEmbedding_split x
  change IF x = IJ (l1Left x)+IE (l1Right x) at hs
  ext i
  change x (Sum.inl i) - RF (signedS neg (IF x)) (Sum.inl i) = _
  rw [hs,map_add,map_add]
  change x (Sum.inl i) - (RJ (signedS neg (IJ (l1Left x))) i + RJ (signedS neg (IE (l1Right x))) i) = _
  change _ = x (Sum.inl i)-RJ (signedS neg (IJ (l1Left x))) i - RJ (signedS neg (IE (l1Right x))) i
  ring
lemma finiteA_right (neg : Bool) (x : L1Finite FiniteIndex) :
    l1Right (finiteA neg x) = l1Right x - signedL neg (l1Left x) - signedE neg (l1Right x) := by
  have hs := finiteEmbedding_split x
  change IF x = IJ (l1Left x)+IE (l1Right x) at hs
  ext i
  change x (Sum.inr i) - RF (signedS neg (IF x)) (Sum.inr i) = _
  rw [hs,map_add,map_add]
  change x (Sum.inr i) - (RE (signedS neg (IJ (l1Left x))) i + RE (signedS neg (IE (l1Right x))) i) = _
  change _ = x (Sum.inr i)-RE (signedS neg (IJ (l1Left x))) i - RE (signedS neg (IE (l1Right x))) i
  ring
lemma finiteA_coercive (neg : Bool) (x : L1Finite FiniteIndex) : ‖x‖ ≤ 90*‖finiteA neg x‖ := by
  rw [l1Split_norm x,l1Split_norm (finiteA neg x)]
  apply finite_schur_bound (centralV neg) (signedU neg) (signedL neg) (signedE neg)
    (centralV_norm neg) (signedE_norm neg) (signedL_norm neg) (signedVU_norm_g neg)
  · rw [finiteA_left,sub_add_cancel,centralV_left]
  · exact (finiteA_right neg x).symm
lemma finiteA_bijective_g_oai (neg : Bool) : Function.Bijective (finiteA neg) := by
  have hi : Function.Injective (finiteA neg) := by
    intro x y hxy
    have hb := finiteA_coercive neg (x-y)
    rw [map_sub,hxy,sub_self,norm_zero,mul_zero] at hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))
  exact ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.finiteA_bijective_g_oai := @OAI.SharpPlanar.Numerical.finiteA_bijective_g_oai
