-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.hessianCost_inserted_gram_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:11:02.737983+00:00
-- url     : https://prove2.me/submissions/59892a7e-f745-4372-bbfb-2b8dacb45036

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean:L1509-L1536
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.hessianCost_inserted_gram_le. The node keeps its source
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

theorem traceReal_mul_comm (A B : Matrix ι ι ℂ) : traceReal (A * B) = traceReal (B * A) := by
  unfold traceReal; rw [Matrix.trace_mul_comm]
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

theorem variation_le_rootCost {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) (X : Matrix ι ι ℂ) :
    (3 / 2 : ℝ) * variation A K X ≤ rootCost A K := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact le_csSup (variation_bddAbove hA hsol) ⟨X, rfl⟩

variable [DecidableEq ι]

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

omit [Fintype ι] in
theorem regularize_posDef {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    {η : ℝ} (hη : 0 < η) : (regularize P η).PosDef :=
  Matrix.PosDef.posSemidef_add hP (Matrix.PosDef.one.smul hη)

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

lemma hsReal_nonneg_of_posSemidef {X Y : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : 0 ≤ hsReal X Y := by
  let B := CFC.sqrt Y
  have hB : B.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Y)).isHermitian
  have hBB : B * B = Y := CFC.sqrt_mul_sqrt_self Y hY.nonneg
  have hn := traceReal_nonneg (hX.conjTranspose_mul_mul_same B)
  rw [hB.eq, traceReal_mul_cycle, hBB, traceReal_mul_comm] at hn
  simpa only [hsReal, hX.isHermitian.eq] using hn

omit [DecidableEq ι] in
lemma sylv_star {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (Y : Matrix ι ι ℂ) :
    sylv A Yᴴ = (sylv A Y)ᴴ := by
  simp only [sylv, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hA.eq]
  exact add_comm _ _

lemma sylv_solution_isHermitian {A K Y : Matrix ι ι ℂ} (hA : A.PosDef)
    (hK : K.IsHermitian) (hY : sylv A Y = K) : Y.IsHermitian := by
  change Yᴴ = Y
  apply (sylvEquiv hA).injective
  change sylv A Yᴴ = sylv A Y
  rw [sylv_star hA.isHermitian, hY, hK.eq]

lemma posSemidef_of_sylv_posSemidef {A Y : Matrix ι ι ℂ} (hA : A.PosDef)
    (hY : Y.IsHermitian) (hS : (sylv A Y).PosSemidef) : Y.PosSemidef := by
  apply hY.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  change 0 ≤ hY.eigenvalues i
  let U := hY.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  have hD : f Y = Matrix.diagonal (fun i => (hY.eigenvalues i : ℂ)) :=
    hY.conjStarAlgAut_star_eigenvectorUnitary
  have hAf : (f A).PosDef := by
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
      (Unitary.isUnit_coe (U := star U))).mpr hA
  have hSf : (f (sylv A Y)).PosSemidef := by
    exact hS.mul_mul_conjTranspose_same (star U : Matrix ι ι ℂ)
  have he : f (sylv A Y) = sylv (f A) (f Y) :=
    (sylv_unitary_conj (star U) A Y).symm
  rw [he, hD] at hSf
  have hn : 0 ≤ (sylv (f A) (Matrix.diagonal (fun i => (hY.eigenvalues i : ℂ))) i i).re :=
    (RCLike.nonneg_iff.mp hSf.diag_nonneg).1
  have hp : 0 < (f A i i).re := (RCLike.pos_iff.mp hAf.diag_pos).1
  simp only [sylv, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero] at hn
  nlinarith

lemma rootCost_le_of_order_posDef {A K : Matrix ι ι ℂ} (hA : A.PosDef)
    (hK : K.IsHermitian) (c : ℝ)
    (hm : (c • (A * A) - K).PosSemidef)
    (hp : (c • (A * A) + K).PosSemidef) :
    rootCost A K ≤ (3 / 4 : ℝ) * c^2 * traceReal (A * A * A) := by
  let Y := (sylvEquiv hA).symm K
  have hY : sylv A Y = K := (sylvEquiv hA).apply_symm_apply K
  have hYh : Y.IsHermitian := sylv_solution_isHermitian hA hK hY
  let Z : Matrix ι ι ℂ := (c / 2) • A
  have hZ : sylv A Z = c • (A * A) := by
    change A * ((c / 2) • A) + ((c / 2) • A) * A = _
    rw [Matrix.mul_smul, Matrix.smul_mul, ← add_smul]
    congr 1
    ring
  have hYZ : (Z + Y).PosSemidef := by
    apply posSemidef_of_sylv_posSemidef hA
      ((hA.isHermitian.smul (show IsSelfAdjoint (c / 2) from rfl)).add hYh)
    rwa [sylv_add_right, hZ, hY]
  have hn := hsReal_nonneg_of_posSemidef hm hYZ
  have hc : hsReal (sylv A Z) Y = hsReal K Z := by
    rw [← hsReal_sylv_symm hA.isHermitian, hY, hsReal_symm]
  have hb : hsReal K Y ≤ hsReal (sylv A Z) Z := by
    rw [← hZ, hsReal_sub_left, hsReal_add_right, hsReal_add_right, hc] at hn
    linarith
  rw [rootCost_eq_of_solution hA.posSemidef hY]
  calc
    _ ≤ (3 / 2 : ℝ) * hsReal (sylv A Z) Z := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by
      rw [hZ]
      change (3 / 2 : ℝ) * hsReal (c • (A * A)) ((c / 2) • A) = _
      rw [hsReal_smul_left, hsReal_smul_right]
      simp only [hsReal, Matrix.conjTranspose_mul, hA.isHermitian.eq]
      ring

lemma regularize_square (A : Matrix ι ι ℂ) (δ : ℝ) :
    regularize A δ * regularize A δ = A * A + (2 * δ) • A + δ^2 • 1 := by
  simp only [regularize, add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul,
    one_mul, mul_one, smul_smul]
  module

lemma regularize_square_le {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    {δ : ℝ} (hδ : 0 ≤ δ) : A * A ≤ regularize A δ * regularize A δ := by
  rw [regularize_square, add_assoc]
  exact le_add_of_nonneg_right
    (((hA.smul (mul_nonneg (by norm_num) hδ)).add
      (Matrix.PosSemidef.one.smul (sq_nonneg δ))).nonneg)

omit [DecidableEq ι] in
lemma continuous_variation_left (K X : Matrix ι ι ℂ) :
    Continuous (fun A : Matrix ι ι ℂ => variation A K X) := by
  exact continuous_const.sub (traceRealCLM.continuous.comp
    (continuous_const.mul ((continuous_id.mul continuous_const).add
      (continuous_const.mul continuous_id))))

theorem rootCost_le_of_order {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hK : K.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (hm : (c • (A * A) - K).PosSemidef)
    (hp : (c • (A * A) + K).PosSemidef) :
    rootCost A K ≤ (3 / 4 : ℝ) * c^2 * traceReal (A * A * A) := by
  have hb (δ : ℝ) (hδ : 0 < δ) (X : Matrix ι ι ℂ) :
      (3 / 2 : ℝ) * variation (regularize A δ) K X ≤
        (3 / 4 : ℝ) * c^2 * traceReal (regularize A δ * regularize A δ * regularize A δ) := by
    have hd := regularize_posDef hA hδ
    have ho := smul_le_smul_of_nonneg_left (regularize_square_le hA hδ.le) hc
    have hmd : (c • (regularize A δ * regularize A δ) - K).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (hm.nonneg.trans (sub_le_sub_right ho K))
    have hpd : (c • (regularize A δ * regularize A δ) + K).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (hp.nonneg.trans (add_le_add ho le_rfl))
    exact (variation_le_rootCost hd.posSemidef (exists_sylv_solution_posDef hd K) X).trans
      (rootCost_le_of_order_posDef hd hK c hmd hpd)
  have hv (X : Matrix ι ι ℂ) : variation A K X ≤ (1 / 2 : ℝ) * c^2 * traceReal (A * A * A) := by
    have hAc : Continuous (regularize A) := by unfold regularize; fun_prop
    have hf : Continuous (fun δ => (3 / 2 : ℝ) * variation (regularize A δ) K X) :=
      continuous_const.mul ((continuous_variation_left K X).comp hAc)
    have hg : Continuous (fun δ => (3 / 4 : ℝ) * c^2 *
        traceReal (regularize A δ * regularize A δ * regularize A δ)) :=
      continuous_const.mul (traceRealCLM.continuous.comp ((hAc.mul hAc).mul hAc))
    have hl := le_of_tendsto_of_tendsto
      (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto _ (𝓝[>] (0 : ℝ)) (𝓝 _))
      (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (show ∀ᶠ δ in 𝓝[>] (0 : ℝ), _ from by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact hb δ hδ X)
    simp only [regularize, zero_smul, add_zero] at hl
    linarith
  have hs : sSup (Set.range (variation A K)) ≤ (1 / 2 : ℝ) * c^2 * traceReal (A * A * A) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨X, rfl⟩
    exact hv X
  unfold rootCost
  nlinarith

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem hessianCost_inserted_gram_le (R L : Matrix ι ι ℂ) (hL : L.IsHermitian) :
    hessianCost (Rᴴ * R) (Rᴴ * L * R) ≤
      (3 / 4 : ℝ) * ‖L‖^2 * energy (Rᴴ * R) := by
  have hP := Matrix.posSemidef_conjTranspose_mul_self R
  have hA : (CFC.sqrt (Rᴴ * R)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Rᴴ * R))
  have hAA : CFC.sqrt (Rᴴ * R) * CFC.sqrt (Rᴴ * R) = Rᴴ * R :=
    CFC.sqrt_mul_sqrt_self (Rᴴ * R) hP.nonneg
  have hb : L ≤ ‖L‖ • (1 : Matrix ι ι ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (show IsSelfAdjoint L from hL).le_algebraMap_norm_self
  have ha : -(‖L‖ • (1 : Matrix ι ι ℂ)) ≤ L := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (show IsSelfAdjoint L from hL).neg_algebraMap_norm_le_self
  have hm : (‖L‖ • (Rᴴ * R) - Rᴴ * L * R).PosSemidef := by
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one] using
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hb)).conjTranspose_mul_mul_same R
  have hp : (‖L‖ • (Rᴴ * R) + Rᴴ * L * R).PosSemidef := by
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, add_comm] using
      (Matrix.nonneg_iff_posSemidef.mp (neg_le_iff_add_nonneg.mp ha)).conjTranspose_mul_mul_same R
  unfold hessianCost
  simpa only [hAA, energy] using rootCost_le_of_order hA
    (by
      change (Rᴴ * L * R)ᴴ = Rᴴ * L * R
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hL.eq, Matrix.mul_assoc]) (norm_nonneg L) (by simpa [hAA] using hm)
      (by simpa [hAA] using hp)

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

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


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.hessianCost_inserted_gram_le.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.hessianCost_inserted_gram_le.{uι}
