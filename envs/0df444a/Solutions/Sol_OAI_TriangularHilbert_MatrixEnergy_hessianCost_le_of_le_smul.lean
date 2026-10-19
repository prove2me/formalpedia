-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.hessianCost_le_of_le_smul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:12:43.536481+00:00
-- url     : https://prove2.me/submissions/7c9b1f25-0277-4e30-b3a9-64d915c93efd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean:L1620-L1639
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.hessianCost_le_of_le_smul. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_rootCost_eq_of_solution

-- ---- from OAI.Analysis.TriangularHilbert.MatrixSupport ----
namespace OAI

universe uι uκ uX uμ

section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

theorem traceReal_mul_cycle (A B C : Matrix ι ι ℂ) :
    traceReal (A * B * C) = traceReal (C * A * B) := by
  unfold traceReal; rw [Matrix.trace_mul_cycle]
theorem traceReal_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : 0 ≤ traceReal A :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

theorem hsReal_symm (X Y : Matrix ι ι ℂ) : hsReal X Y = hsReal Y X := by
  unfold hsReal
  rw [← traceReal_star (Xᴴ * Y), Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem hsReal_sylv_symm {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) : hsReal X (sylv A Y) = hsReal (sylv A X) Y := by
  simp only [hsReal, sylv, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hA.eq, mul_add, add_mul, traceReal_add]
  rw [← Matrix.mul_assoc Xᴴ A Y, ← Matrix.mul_assoc Xᴴ Y A,
    traceReal_mul_cycle Xᴴ Y A]

theorem penalty_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (X : Matrix ι ι ℂ) : 0 ≤ penalty A X := by
  simp only [penalty, hsReal, sylv, mul_add, traceReal_add]
  have h₁ := traceReal_nonneg (hA.conjTranspose_mul_mul_same X)
  have h₂ := traceReal_nonneg (hA.mul_mul_conjTranspose_same X)
  rw [Matrix.mul_assoc] at h₁
  rw [← Matrix.mul_assoc Xᴴ X A, traceReal_mul_cycle Xᴴ X A,
    traceReal_mul_cycle A Xᴴ X]
  exact add_nonneg h₁ h₂

theorem penalty_sub {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) :
    penalty A (X - Y) = penalty A X + penalty A Y - 2 * hsReal (sylv A Y) X := by
  simp only [penalty, sylv_sub_right, hsReal_sub_left, hsReal_sub_right]
  rw [hsReal_symm Y (sylv A X), ← hsReal_sylv_symm hA, hsReal_symm X (sylv A Y)]
  ring

theorem penalty_mono {A B : Matrix ι ι ℂ} (hAB : A ≤ B) (X : Matrix ι ι ℂ) :
    penalty A X ≤ penalty B X := by
  have h := penalty_nonneg hAB X
  simpa only [penalty, sylv_sub_left, hsReal_sub_right, sub_nonneg] using h

theorem variation_sylv {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) :
    variation A (sylv A Y) X = penalty A Y - penalty A (X - Y) := by
  rw [variation, penalty_sub hA]
  ring

theorem variation_bddAbove {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) : BddAbove (Set.range (variation A K)) := by
  obtain ⟨Y, rfl⟩ := hsol
  refine ⟨penalty A Y, ?_⟩
  rintro _ ⟨X, rfl⟩
  rw [variation_sylv hA.isHermitian]
  exact sub_le_self _ (penalty_nonneg hA _)

theorem rootCost_antitone {A B K : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hsol : ∃ Y, sylv A Y = K) (hAB : A ≤ B) :
    rootCost B K ≤ rootCost A K := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨X, rfl⟩
  exact (sub_le_sub_left (penalty_mono hAB X) _).trans
    (le_csSup (variation_bddAbove hA hsol) ⟨X, rfl⟩)

theorem rootCost_scale {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) {c : ℝ} (hc : 0 < c) :
    rootCost (c • A) K = c⁻¹ * rootCost A K := by
  obtain ⟨Y, hY⟩ := hsol
  have hY' : sylv (c • A) (c⁻¹ • Y) = K := by
    simp [sylv_smul_left, sylv_smul_right, smul_smul, ne_of_gt hc, hY]
  rw [rootCost_eq_of_solution (hA.smul (le_of_lt hc)) hY',
    rootCost_eq_of_solution hA hY, hsReal_smul_right]
  ring

theorem hsReal_eq_sum (X Y : Matrix ι ι ℂ) :
    hsReal X Y = ∑ i, ∑ j, (star (X i j) * Y i j).re := by
  simp only [hsReal, traceReal, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  exact Finset.sum_comm

variable [DecidableEq ι]

theorem traceReal_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    traceReal (conjStarAlgAut ℂ _ U X) = traceReal X := by
  unfold traceReal
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

theorem hsReal_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X Y : Matrix ι ι ℂ) :
    hsReal (conjStarAlgAut ℂ _ U X) (conjStarAlgAut ℂ _ U Y) = hsReal X Y := by
  change traceReal (star (conjStarAlgAut ℂ _ U X) * conjStarAlgAut ℂ _ U Y) = _
  rw [← map_star, ← map_mul, traceReal_unitary_conj]
  rfl

theorem variation_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A K X : Matrix ι ι ℂ) :
    variation (conjStarAlgAut ℂ _ U A) (conjStarAlgAut ℂ _ U K)
      (conjStarAlgAut ℂ _ U X) = variation A K X := by
  simp only [variation, penalty, sylv_unitary_conj, hsReal_unitary_conj]

theorem hessianCost_antitone {P Q K : Matrix ι ι ℂ}
    (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K) (hPQ : P ≤ Q) :
    hessianCost Q K ≤ hessianCost P K := by
  exact rootCost_antitone (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) hsol (CFC.monotone_sqrt hPQ)

theorem sqrt_smul {P : Matrix ι ι ℂ} (hP : P.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt (c • P) = Real.sqrt c • CFC.sqrt P := by
  apply CFC.sqrt_unique
  · rw [smul_mul_smul_comm, Real.mul_self_sqrt hc, CFC.sqrt_mul_sqrt_self P hP.nonneg]
  · exact smul_nonneg (Real.sqrt_nonneg c) (CFC.sqrt_nonneg P)

theorem hsReal_single (K : Matrix ι ι ℂ) (i j : ι) (z : ℂ) :
    hsReal K (Matrix.single i j z) = (star (K i j) * z).re := by
  simp [hsReal_eq_sum, Matrix.single_apply, ite_and, apply_ite]

theorem sylv_diagonal_single (q : ι → ℝ) (i j : ι) (z : ℂ) :
    sylv (Matrix.diagonal (fun i => (q i : ℂ))) (Matrix.single i j z) =
      Matrix.single i j (((q i + q j : ℝ) : ℂ) * z) := by
  ext a b
  rw [sylv_diagonal_apply]
  by_cases ha : i = a
  · subst a
    by_cases hb : j = b
    · subst b; simp
    · simp [hb]
  · simp [ha]

theorem sylv_solvable_diagonal_of_bddAbove (q : ι → ℝ) (K : Matrix ι ι ℂ)
    (hb : BddAbove (Set.range (variation (Matrix.diagonal (fun i => (q i : ℂ))) K))) :
    ∃ Y, sylv (Matrix.diagonal (fun i => (q i : ℂ))) Y = K := by
  refine ⟨diagonalSolution q K, diagonalSolution_solves q K ?_⟩
  intro i j hij
  by_contra hK
  obtain ⟨b, hb⟩ := hb
  let X := Matrix.single i j (K i j)
  have hzero : sylv (Matrix.diagonal (fun i => (q i : ℂ))) X = 0 := by
    simp [X, sylv_diagonal_single, hij]
  have hhs : hsReal K X = ‖K i j‖^2 := by
    rw [hsReal_single]
    simp only [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hpos : 0 < ‖K i j‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hK)
  let t : ℝ := b / (2 * ‖K i j‖^2) + 1
  have ht := hb (Set.mem_range_self (t • X))
  change variation _ K (t • X) ≤ b at ht
  simp only [variation, penalty, sylv_smul_right, hzero, smul_zero,
    hsReal_zero_right, sub_zero, hsReal_smul_right, hhs] at ht
  have hcalc : 2 * (t * ‖K i j‖^2) = b + 2 * ‖K i j‖^2 := by
    dsimp [t]
    field_simp [ne_of_gt hpos]
  rw [hcalc] at ht
  linarith

theorem sylv_solvable_of_bddAbove {A K : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hb : BddAbove (Set.range (variation A K))) : ∃ Y, sylv A Y = K := by
  let U := hA.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  let K' := f K
  have hAd : f A = Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) :=
    hA.conjStarAlgAut_star_eigenvectorUnitary
  have hb' : BddAbove (Set.range (variation (f A) K')) := by
    obtain ⟨b, hb⟩ := hb
    refine ⟨b, ?_⟩
    rintro _ ⟨X, rfl⟩
    obtain ⟨Y, rfl⟩ := f.surjective X
    change variation (f A) (f K) (f Y) ≤ b
    exact (variation_unitary_conj (star U) A K Y) ▸ hb (Set.mem_range_self Y)
  rw [hAd] at hb'
  obtain ⟨Y, hY⟩ := sylv_solvable_diagonal_of_bddAbove _ K' hb'
  refine ⟨f.symm Y, ?_⟩
  apply f.injective
  change f (sylv A (f.symm Y)) = f K
  calc
    _ = sylv (f A) (f (f.symm Y)) := (sylv_unitary_conj (star U) A (f.symm Y)).symm
    _ = sylv (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) Y := by
      rw [f.apply_symm_apply, hAd]
    _ = _ := hY

theorem sylv_solvable_mono {A B K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hB : B.IsHermitian) (hsol : ∃ Y, sylv A Y = K) (hAB : A ≤ B) :
    ∃ Y, sylv B Y = K := by
  apply sylv_solvable_of_bddAbove hB
  obtain ⟨b, hb⟩ := variation_bddAbove hA hsol
  refine ⟨b, ?_⟩
  rintro _ ⟨X, rfl⟩
  exact (sub_le_sub_left (penalty_mono hAB X) _).trans (hb (Set.mem_range_self X))

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem hessianCost_le_of_le_smul {P Q K : Matrix ι ι ℂ}
    (hQ : Q.PosSemidef) (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K)
    {c : ℝ} (hc : 0 < c) (hPQ : P ≤ c • Q) :
    hessianCost Q K ≤ Real.sqrt c * hessianCost P K := by
  have hr : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hAs : (CFC.sqrt Q).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)
  have hps : (CFC.sqrt P).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  have hsolc := sylv_solvable_mono hps
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (c • Q))).isHermitian hsol
      (CFC.monotone_sqrt hPQ)
  rw [sqrt_smul hQ hc.le] at hsolc
  have hsolQ : ∃ Y, sylv (CFC.sqrt Q) Y = K := by
    obtain ⟨Y, hY⟩ := hsolc
    refine ⟨Real.sqrt c • Y, ?_⟩
    rwa [sylv_smul_right, ← sylv_smul_left]
  have hm := hessianCost_antitone hsol hPQ
  change rootCost (CFC.sqrt (c • Q)) K ≤ rootCost (CFC.sqrt P) K at hm
  rw [sqrt_smul hQ hc.le, rootCost_scale hAs hsolQ hr] at hm
  have hx := mul_le_mul_of_nonneg_left hm hr.le
  simpa only [hessianCost, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using hx

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

variable [DecidableEq κ]

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped BigOperators
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.hessianCost_le_of_le_smul.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.hessianCost_le_of_le_smul.{uι}
