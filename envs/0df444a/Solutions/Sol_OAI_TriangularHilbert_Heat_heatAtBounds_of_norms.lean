-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.heatAtBounds_of_norms
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:36:26.390407+00:00
-- url     : https://prove2.me/submissions/847d2c8c-c106-4805-b1be-59e85e0e2f4d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/HeatBound.lean:L23-L78
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.heatAtBounds_of_norms. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_exists_kernel_projection
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_hessianCost_add_projection
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_hessianCost_inserted_gram_le
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_norm_energyGradient_inserted_gram_le
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_rootCost_eq_of_solution
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_two_hessianPairPD_le
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_vertexRoot_insert

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
theorem hsReal_symm (X Y : Matrix ι ι ℂ) : hsReal X Y = hsReal Y X := by
  unfold hsReal
  rw [← traceReal_star (Xᴴ * Y), Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem hsReal_sylv_symm {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) : hsReal X (sylv A Y) = hsReal (sylv A X) Y := by
  simp only [hsReal, sylv, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hA.eq, mul_add, add_mul, traceReal_add]
  rw [← Matrix.mul_assoc Xᴴ A Y, ← Matrix.mul_assoc Xᴴ Y A,
    traceReal_mul_cycle Xᴴ Y A]

variable [DecidableEq ι]

theorem traceReal_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    traceReal (conjStarAlgAut ℂ _ U X) = traceReal X := by
  unfold traceReal
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

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

theorem energy_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    energy (conjStarAlgAut ℂ _ U P) = energy P := by
  have hs : CFC.sqrt (conjStarAlgAut ℂ _ U P) =
      conjStarAlgAut ℂ _ U (CFC.sqrt P) := by
    apply CFC.sqrt_unique
    · rw [← map_mul, CFC.sqrt_mul_sqrt_self P hP.nonneg]
    · simpa only [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
        ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).mul_mul_conjTranspose_same
          (U : Matrix ι ι ℂ)).nonneg
  simp only [energy, hs, ← map_mul, traceReal_unitary_conj]

theorem sqrt_diagonal_nonneg (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    CFC.sqrt (Matrix.diagonal (fun i => (q i : ℂ))) =
      Matrix.diagonal (fun i => ((Real.sqrt (q i) : ℝ) : ℂ)) := by
  apply CFC.sqrt_unique
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact_mod_cast (Real.mul_self_sqrt (hq i))
  · exact (Matrix.PosSemidef.diagonal (fun i =>
      RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _))).nonneg

theorem energy_diagonal (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    energy (Matrix.diagonal (fun i => (q i : ℂ))) = ∑ i, q i * Real.sqrt (q i) := by
  simp [energy, sqrt_diagonal_nonneg q hq, Matrix.diagonal_mul_diagonal, traceReal]

theorem energy_spectral {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    energy P = ∑ i, hP.isHermitian.eigenvalues i * Real.sqrt (hP.isHermitian.eigenvalues i) := by
  rw [← energy_unitary_conj (star hP.isHermitian.eigenvectorUnitary) hP,
    hP.isHermitian.conjStarAlgAut_star_eigenvectorUnitary]
  exact energy_diagonal _ hP.eigenvalues_nonneg

theorem energy_eq_of_charpoly_eq {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hPQ : P.charpoly = Q.charpoly) :
    energy P = energy Q := by
  rw [energy_spectral hP, energy_spectral hQ,
    (hP.isHermitian.eigenvalues_eq_eigenvalues_iff hQ.isHermitian).mpr hPQ]

theorem energy_gram_flip (R : Matrix ι ι ℂ) : energy (Rᴴ * R) = energy (R * Rᴴ) :=
  energy_eq_of_charpoly_eq (Matrix.posSemidef_conjTranspose_mul_self R)
    (Matrix.posSemidef_self_mul_conjTranspose R) (Matrix.charpoly_mul_comm _ _)

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

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma sqrtInverse_solves {P : Matrix ι ι ℂ} (hP : P.PosDef) (K : Matrix ι ι ℂ) :
    sylv (CFC.sqrt P) (sqrtInverse hP K) = K := by
  exact (sylvEquiv (Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive))).apply_symm_apply K

lemma hessianPairPD_symm {P : Matrix ι ι ℂ} (hP : P.PosDef) (K L : Matrix ι ι ℂ) :
    hessianPairPD hP K L = hessianPairPD hP L K := by
  have hs := hsReal_sylv_symm
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
    (sqrtInverse hP K) (sqrtInverse hP L)
  rw [sqrtInverse_solves, sqrtInverse_solves, hsReal_symm _ L] at hs
  exact congrArg ((3 / 2 : ℝ) * ·) hs.symm

lemma hessianPairPD_self {P : Matrix ι ι ℂ} (hP : P.PosDef) (K : Matrix ι ι ℂ) :
    hessianPairPD hP K K = hessianCost P K := by
  exact (rootCost_eq_of_solution
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) (sqrtInverse_solves hP K)).symm

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

-- ---- from OAI.Analysis.TriangularHilbert.Support ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma hermitian_mul_zero_flip {P Q : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (h : P * Q = 0) : Q * P = 0 := by
  simpa only [Matrix.conjTranspose_mul, hP.eq, hQ.eq, Matrix.conjTranspose_zero] using
    congrArg Matrix.conjTranspose h

lemma hessianPair_eq_PD {P : Matrix ι ι ℂ} (hP : P.PosDef)
    (K L : Matrix ι ι ℂ) : hessianPair P K L = hessianPairPD hP K L := by
  have hs := hessianPairPD_symm hP K L
  unfold hessianPair
  rw [← hessianPairPD_self hP, ← hessianPairPD_self hP]
  simp only [hessianPairPD, map_add, map_sub, hsReal_add_left, hsReal_add_right,
    hsReal_sub_left, hsReal_sub_right] at hs ⊢
  linarith

lemma hessianPair_add_projection {P Q K L : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hKQ : K * Q = 0) (hQK : Q * K = 0) (hLQ : L * Q = 0) (hQL : Q * L = 0)
    (hPD : (P + Q).PosDef) : hessianPair (P + Q) K L = hessianPair P K L := by
  unfold hessianPair
  rw [hessianCost_add_projection hP hQ hQQ hPQ hQP
    (by simp [add_mul, hKQ, hLQ]) (by simp [mul_add, hQK, hQL]) hPD,
    hessianCost_add_projection hP hQ hQQ hPQ hQP
    (by simp [sub_mul, hKQ, hLQ]) (by simp [mul_sub, hQK, hQL]) hPD]

end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.WeightedGram ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weightedGram_posSemidef (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) : (weightedGram B w).PosSemidef :=
  (Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr (hw i))).conjTranspose_mul_mul_same B

lemma weightedGram_isHermitian (B : Matrix ι ι ℂ) (w : ι → ℝ) :
    (weightedGram B w).IsHermitian := by
  have hd : (Matrix.diagonal (fun i => (w i : ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    simp
  exact Matrix.isHermitian_conjTranspose_mul_mul B hd

lemma weightedGram_mul_zero {B Q : Matrix ι ι ℂ} {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hz : weightedGram B w * Q = 0) : B * Q = 0 := by
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (w i : ℂ))
  have hD : D.PosDef := Matrix.PosDef.diagonal (fun i => RCLike.ofReal_pos.mpr (hw i))
  have hs : (CFC.sqrt D).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg D)).isHermitian
  have hunit : IsUnit (CFC.sqrt D) :=
    (Matrix.isStrictlyPositive_iff_posDef.mp
      (IsStrictlyPositive.sqrt D hD.isStrictlyPositive)).isUnit
  have hgram : (CFC.sqrt D * B)ᴴ * (CFC.sqrt D * B) = weightedGram B w := by
    calc
      _ = Bᴴ * (CFC.sqrt D * CFC.sqrt D) * B := by
        rw [Matrix.conjTranspose_mul, hs.eq]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg]; rfl
  have hsq : (CFC.sqrt D * B * Q)ᴴ * (CFC.sqrt D * B * Q) = 0 := by
    calc
      _ = Qᴴ * ((CFC.sqrt D * B)ᴴ * (CFC.sqrt D * B)) * Q := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = Qᴴ * (weightedGram B w * Q) := by rw [hgram, Matrix.mul_assoc]
      _ = 0 := by rw [hz, mul_zero]
  have hzero := (CStarRing.star_mul_self_eq_zero_iff _).mp hsq
  apply hunit.mul_left_cancel
  simpa only [Matrix.mul_assoc, mul_zero] using hzero

lemma weightedGram_kernel_projection (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) :
    ∃ Q : Matrix ι ι ℂ, Q.PosSemidef ∧ Q * Q = Q ∧ B * Q = 0 ∧
      (weightedGram B w + Q).PosDef := by
  obtain ⟨Q, hQ, hQQ, hPQ, _, hPD⟩ :=
    exists_kernel_projection (weightedGram_posSemidef B (fun i => (hw i).le))
  exact ⟨Q, hQ, hQQ, weightedGram_mul_zero hw hPQ, hPD⟩

lemma weightedGram_mul_eq_zero (B Q : Matrix ι ι ℂ) (w : ι → ℝ) (hz : B * Q = 0) :
    weightedGram B w * Q = 0 := by
  simp only [weightedGram, Matrix.mul_assoc, hz, mul_zero]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianGram ----
namespace OAI

universe uι

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weight_pos {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ) (u p : ℝ) :
    0 < weight h u p σ := mul_pos hh (density_pos hσ _)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.WeightedStar ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma vertexRoot_star (g : Three → ι → ℝ) : (vertexRoot g)ᴴ = vertexRoot g := by
  unfold vertexRoot
  rw [Matrix.diagonal_conjTranspose]
  simp

lemma vertexRoot_sq (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    vertexRoot g * vertexRoot g = Matrix.diagonal (fun a => (g a.1 a.2 : ℂ)) := by
  rw [vertexRoot, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hg a.1 a.2)]

lemma vertexRoot_commute_vertexProj (g : Three → ι → ℝ) (v : Three) :
    vertexRoot g * vertexProj v = vertexProj v * vertexRoot g := by
  dsimp only [vertexRoot, vertexProj]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

lemma triangle_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) :
    triangle (weightedArray A g) = vertexRoot g * triangle A * vertexRoot g := by
  ext ⟨v,i⟩ ⟨w,j⟩
  fin_cases v <;> fin_cases w <;>
    simp [triangle, triangleBlocks, blocks, weightedArray, vertexRoot,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      mul_comm, mul_left_comm, mul_assoc] <;> first | exact Or.inl (mul_comm _ _) | ring

lemma rowStar_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) :
    rowStar (weightedArray A g) v = vertexRoot g * rowStar A v * vertexRoot g := by
  unfold rowStar
  rw [triangle_weightedArray]
  simp only [← Matrix.mul_assoc]
  rw [← vertexRoot_commute_vertexProj]

lemma starGram_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    starGram (weightedArray A g) v = weightedGram (rowBare A g v) (fun a => g a.1 a.2) := by
  have hr : rowStar (weightedArray A g) v = vertexRoot g * rowBare A g v := by
    rw [rowStar_weightedArray, rowBare, Matrix.mul_assoc]
  rw [starGram, hr, Matrix.conjTranspose_mul, vertexRoot_star]
  unfold weightedGram
  calc
    _ = (rowBare A g v)ᴴ * (vertexRoot g * vertexRoot g) * rowBare A g v := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [vertexRoot_sq g hg]

lemma centerGram_weightedArray_padded (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    rowStar (weightedArray A g) v * (rowStar (weightedArray A g) v)ᴴ =
      weightedGram (colBare A g v) (fun a => g a.1 a.2) := by
  rw [rowStar_weightedArray]
  unfold colBare weightedGram
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, vertexRoot_star]
  rw [← vertexRoot_sq g hg]
  simp only [Matrix.mul_assoc]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GroupedGaussian ----
namespace OAI

universe uι uν

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} {ν : Type uν} [Fintype ι] [DecidableEq ι] [DecidableEq ν]

omit [Fintype ι] [DecidableEq ι] [DecidableEq ν] in
lemma groupWeight_pos {h : ℝ} (hh : 0 < h) (u : ι → ℝ) (loc : ι → ν)
    (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (i : ι) :
    0 < groupWeight h u loc p σ i := weight_pos hh (hσ (loc i)) _ _

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HeatStar ----
namespace OAI

universe uι

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma heatEnergy_eq_localGram (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    heatEnergy A h u p σ v = energy (localGram A h u p σ v w) := by
  have hg : ∀ w i, 0 ≤ heatWeights h u p σ w i := fun w i =>
    (weight_pos hh (hσ w) (u i) (p w)).le
  unfold heatEnergy localGram fixedBase
  split_ifs
  · rw [heatArray, starGram_weightedArray A _ hg]
    rfl
  · rw [starGram, energy_gram_flip, heatArray, centerGram_weightedArray_padded A _ hg]
    rfl

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.StarInsertion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowBare_insert (A : Three → Matrix ι ι ℂ) (g d : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    weightedGram (rowBare A g v) (fun a => g a.1 a.2 * d a.1 a.2) =
      starInsert (weightedArray A g) (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) v := by
  unfold starInsert
  rw [rowStar_weightedArray]
  unfold weightedGram rowBare
  simp only [Complex.ofReal_mul]
  rw [← vertexRoot_insert g d hg]
  simp only [Matrix.conjTranspose_mul, vertexRoot_star, Matrix.mul_assoc]

lemma colBare_insert (A : Three → Matrix ι ι ℂ) (g d : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    weightedGram (colBare A g v) (fun a => g a.1 a.2 * d a.1 a.2) =
      rowStar (weightedArray A g) v *
        blockD (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) *
        (rowStar (weightedArray A g) v)ᴴ := by
  rw [rowStar_weightedArray]
  unfold weightedGram colBare
  simp only [Complex.ofReal_mul]
  rw [← vertexRoot_insert g d hg]
  simp only [Matrix.conjTranspose_mul, vertexRoot_star, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HeatCost ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma localGram_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    localGram A h u p σ v v = starGram (heatArray A h u p σ) v := by
  simp only [localGram, fixedBase, ite_true]
  exact (starGram_weightedArray A _ (fun w i => (weight_pos hh (hσ w) (u i) (p w)).le) v).symm

lemma localGram_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w : Three} (hw : w ≠ v) :
    localGram A h u p σ v w = rowStar (heatArray A h u p σ) v *
      (rowStar (heatArray A h u p σ) v)ᴴ := by
  simp only [localGram, fixedBase, ite_eq_right hw]
  exact (centerGram_weightedArray_padded A _
    (fun w i => (weight_pos hh (hσ w) (u i) (p w)).le) v).symm

omit [Fintype ι] [DecidableEq ι] in
lemma groupFirst_eq_insert (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (w : Three) :
    groupFirst h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w =
      fun a : BlockSpace ι => heatWeights h u p σ a.1 a.2 *
        (if a.1 = w then score (u a.2) (p a.1) (σ a.1) else 0) := by
  funext a
  simp only [groupFirst, heatWeights]
  split_ifs with ha
  · rw [ha, mul_comm]
  · rw [mul_zero]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.NormBounds ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma norm_sqrt_gram (R : Matrix ι ι ℂ) : ‖CFC.sqrt (Rᴴ * R)‖ = ‖R‖ := by
  rw [CFC.norm_sqrt _ (Matrix.posSemidef_conjTranspose_mul_self R).nonneg]
  rw [show ‖Rᴴ * R‖ = ‖R‖ * ‖R‖ from CStarRing.norm_star_mul_self,
    Real.sqrt_mul_self (norm_nonneg R)]

lemma norm_traceReal_le (X : Matrix ι ι ℂ) :
    ‖traceReal X‖ ≤ ‖traceRealCLM (ι := ι)‖ * ‖X‖ := by
  exact (traceRealCLM (ι := ι)).le_opNorm X

lemma norm_energy_gram_le (R : Matrix ι ι ℂ) :
    ‖energy (Rᴴ * R)‖ ≤ ‖traceRealCLM (ι := ι)‖ * ‖R‖^3 := by
  calc
    _ ≤ ‖traceRealCLM (ι := ι)‖ * ‖Rᴴ * R * CFC.sqrt (Rᴴ * R)‖ :=
      norm_traceReal_le _
    _ ≤ ‖traceRealCLM (ι := ι)‖ * (‖Rᴴ * R‖ * ‖CFC.sqrt (Rᴴ * R)‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by
      rw [norm_sqrt_gram,
        show ‖Rᴴ * R‖ = ‖R‖ * ‖R‖ from CStarRing.norm_star_mul_self]
      ring

lemma hessianCost_nonneg (P K : Matrix ι ι ℂ) : 0 ≤ hessianCost P K := by
  unfold hessianCost rootCost
  apply mul_nonneg (by norm_num)
  by_cases hb : BddAbove (Set.range (variation (CFC.sqrt P) K))
  · apply le_csSup hb
    exact ⟨0, by simp [variation, penalty]⟩
  · rw [Real.sSup_of_not_bddAbove hb]

lemma norm_hessianCost_inserted_gram_le (R L : Matrix ι ι ℂ) (hL : L.IsHermitian) :
    ‖hessianCost (Rᴴ * R) (Rᴴ * L * R)‖ ≤
      (3/4 : ℝ) * ‖traceRealCLM (ι := ι)‖ * ‖L‖^2 * ‖R‖^3 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (hessianCost_nonneg _ _)]
  calc
    _ ≤ (3/4 : ℝ) * ‖L‖^2 * energy (Rᴴ * R) := hessianCost_inserted_gram_le R L hL
    _ ≤ (3/4 : ℝ) * ‖L‖^2 * (‖traceRealCLM (ι := ι)‖ * ‖R‖^3) := by
      gcongr
      exact (le_abs_self _).trans (norm_energy_gram_le R)
    _ = _ := by ring

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HeatInsert ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma heatMask_eq_diagonal (d : Three → ι → ℝ) :
    heatMask d = Matrix.diagonal (fun a : BlockSpace ι => (d a.1 a.2 : ℂ)) := by
  ext ⟨v,i⟩ ⟨w,j⟩
  by_cases hv : v = w <;> by_cases hi : i = j <;>
    simp [heatMask, blockD, blocks, Matrix.diagonal, hv, hi, Prod.mk.injEq]

omit [Fintype ι] in
lemma heatMask_isHermitian (d : Three → ι → ℝ) : (heatMask d).IsHermitian := by
  rw [heatMask_eq_diagonal]
  exact Matrix.isHermitian_diagonal_iff.mpr (fun a => by change star (d a.1 a.2 : ℂ) = _; exact Complex.conj_ofReal _)

lemma localGram_eq_carrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    localGram A h u p σ v w =
      (heatCarrier A h u p σ v w)ᴴ * heatCarrier A h u p σ v w := by
  unfold heatCarrier
  split_ifs with hw
  · subst w
    exact localGram_center A hh u p hσ v
  · rw [Matrix.conjTranspose_conjTranspose]
    exact localGram_other A hh u p hσ hw

lemma localInsert_eq_carrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    (v w : Three) (d : Three → ι → ℝ) :
    weightedGram (fixedBase A (heatWeights h u p σ) v w)
      (fun a : BlockSpace ι => heatWeights h u p σ a.1 a.2 * d a.1 a.2) =
        (heatCarrier A h u p σ v w)ᴴ * heatMask d * heatCarrier A h u p σ v w := by
  simp only [fixedBase, heatCarrier]
  split_ifs
  · exact rowBare_insert A _ d (fun a j => (weight_pos hh (hσ a) (u j) (p a)).le) v
  · rw [Matrix.conjTranspose_conjTranspose]
    exact colBare_insert A _ d (fun a j => (weight_pos hh (hσ a) (u j) (p a)).le) v

lemma localFirst_eq_carrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    localFirst A h u p σ v w = (heatCarrier A h u p σ v w)ᴴ *
      heatMask (fun a i => if a = w then score (u i) (p a) (σ a) else 0) *
        heatCarrier A h u p σ v w := by
  rw [localFirst, groupFirst_eq_insert]
  exact localInsert_eq_carrier A hh u p hσ v w
    (fun a i => if a = w then score (u i) (p a) (σ a) else 0)

omit [Fintype ι] [DecidableEq ι] in
lemma groupSecond_eq_insert (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (w : Three) :
    groupSecond h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w =
      fun a : BlockSpace ι => heatWeights h u p σ a.1 a.2 *
        (if a.1 = w then score (u a.2) (p a.1) (σ a.1)^2 - (σ a.1)⁻¹ else 0) := by
  funext a
  simp only [groupSecond, heatWeights]
  split_ifs with ha
  · rw [ha, mul_comm]
  · rw [mul_zero]

lemma localSecond_eq_carrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    localSecond A h u p σ v w = (heatCarrier A h u p σ v w)ᴴ *
      heatMask (fun a i => if a = w then score (u i) (p a) (σ a)^2 - (σ a)⁻¹ else 0) *
        heatCarrier A h u p σ v w := by
  rw [localSecond, groupSecond_eq_insert]
  exact localInsert_eq_carrier A hh u p hσ v w
    (fun a i => if a = w then score (u i) (p a) (σ a)^2 - (σ a)⁻¹ else 0)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.AbsCost ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma two_abs_hessianPairPD_le {P : Matrix ι ι ℂ} (hP : P.PosDef) (K L : Matrix ι ι ℂ) :
    2 * |hessianPairPD hP K L| ≤ hessianCost P K + hessianCost P L := by
  have hp := two_hessianPairPD_le hP K L
  have hn := two_hessianPairPD_le hP (-K) L
  have hneg : hessianPairPD hP (-K) L = -hessianPairPD hP K L := by
    simp [hessianPairPD, hsReal, traceReal]
  have hc : hessianCost P (-K) = hessianCost P K := by
    rw [← hessianPairPD_self hP, ← hessianPairPD_self hP]
    simp [hessianPairPD, hsReal, traceReal]
  rw [hneg, hc] at hn
  rcases le_total 0 (hessianPairPD hP K L) with hh | hh
  · rwa [abs_of_nonneg hh]
  · rw [abs_of_nonpos hh]
    exact hn

lemma two_abs_hessianPair_le_of_projection {P Q K L : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hKQ : K * Q = 0) (hQK : Q * K = 0)
    (hLQ : L * Q = 0) (hQL : Q * L = 0) (hPD : (P + Q).PosDef) :
    2 * |hessianPair P K L| ≤ hessianCost P K + hessianCost P L := by
  rw [← hessianPair_add_projection hP hQ hQQ hPQ hQP hKQ hQK hLQ hQL hPD,
    ← hessianCost_add_projection hP hQ hQQ hPQ hQP hKQ hQK hPD,
    ← hessianCost_add_projection hP hQ hQQ hPQ hQP hLQ hQL hPD,
    hessianPair_eq_PD hPD]
  exact two_abs_hessianPairPD_le hPD K L

lemma two_abs_hessianPair_weightedGram_le (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (k l : ι → ℝ) :
    2 * |hessianPair (weightedGram B w) (weightedGram B k) (weightedGram B l)| ≤
      hessianCost (weightedGram B w) (weightedGram B k) +
      hessianCost (weightedGram B w) (weightedGram B l) := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw
  have hP := weightedGram_posSemidef B (fun i => (hw i).le)
  have hPQ := weightedGram_mul_eq_zero B Q w hBQ
  have hKQ := weightedGram_mul_eq_zero B Q k hBQ
  have hLQ := weightedGram_mul_eq_zero B Q l hBQ
  exact two_abs_hessianPair_le_of_projection hP hQ hQQ hPQ
    (hermitian_mul_zero_flip hP.isHermitian hQ.isHermitian hPQ) hKQ
    (hermitian_mul_zero_flip (weightedGram_isHermitian B k) hQ.isHermitian hKQ) hLQ
    (hermitian_mul_zero_flip (weightedGram_isHermitian B l) hQ.isHermitian hLQ) hPD
end
end TriangularHilbert.MatrixEnergy
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
lemma two_abs_heatMixed_le (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) :
    2 * |heatMixed A h u p σ v w z| ≤ heatCost A h u p σ v w + heatCost A h u p σ v z := by
  simp only [heatMixed, heatCost, localGram, localFirst, fixedBase, ite_eq_right hw, ite_eq_right hz]
  exact two_abs_hessianPair_weightedGram_le _ (groupWeight_pos hh _ _ p hσ) _ _
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HeatBound ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma heatAtBounds_of_norms (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {E L Q : ℝ} (hE : 0 ≤ E) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hr : ∀ v w, ‖heatCarrier A h u p σ v w‖^3 ≤ E)
    (hl : ∀ w, ‖heatMask (fun a j => if a = w then score (u j) (p a) (σ a) else 0)‖ ≤ L)
    (hq : ∀ w, ‖heatMask (fun a j => if a = w then score (u j) (p a) (σ a)^2-(σ a)⁻¹ else 0)‖ ≤ Q) :
    HeatAtBounds A h u p σ
      (‖traceRealCLM (ι := BlockSpace ι)‖ * E * (1 + (3/2:ℝ)*L + (3/4:ℝ)*L^2 + (3/2:ℝ)*Q)) := by
  let N := ‖traceRealCLM (ι := BlockSpace ι)‖
  have hN : 0 ≤ N := norm_nonneg _
  have he v : ‖heatEnergy A h u p σ v‖ ≤ N * E := by
    rw [heatEnergy_eq_localGram A hh u p hσ v v, localGram_eq_carrier A hh u p hσ v v]
    exact (norm_energy_gram_le _).trans (mul_le_mul_of_nonneg_left (hr v v) hN)
  have hf v w : ‖heatFirst A h u p σ v w‖ ≤ (3/2:ℝ)*N*L*E := by
    simp only [heatFirst, localGram_eq_carrier A hh u p hσ, localFirst_eq_carrier A hh u p hσ]
    apply (norm_energyGradient_inserted_gram_le _ _).trans
    gcongr
    · exact hl w
    · exact hr v w
  have hg v w : ‖energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)‖ ≤
      (3/2:ℝ)*N*Q*E := by
    simp only [localGram_eq_carrier A hh u p hσ, localSecond_eq_carrier A hh u p hσ]
    apply (norm_energyGradient_inserted_gram_le _ _).trans
    gcongr
    · exact hq w
    · exact hr v w
  have hc v w : ‖heatCost A h u p σ v w‖ ≤ (3/4:ℝ)*N*L^2*E := by
    simp only [heatCost, localGram_eq_carrier A hh u p hσ, localFirst_eq_carrier A hh u p hσ]
    apply (norm_hessianCost_inserted_gram_le _ _ (heatMask_isHermitian _)).trans
    gcongr
    · exact hl w
    · exact hr v w
  have hNE := mul_nonneg hN hE
  have hNLE := mul_nonneg (mul_nonneg hN hL) hE
  have hNL2E := mul_nonneg (mul_nonneg hN (sq_nonneg L)) hE
  have hNQE := mul_nonneg (mul_nonneg hN hQ) hE
  constructor
  · intro v; dsimp only [N] at *; nlinarith [he v]
  · intro v w; dsimp only [N] at *; nlinarith [hf v w]
  · intro v w
    have hp : ‖heatPure A h u p σ v w‖ ≤ ‖heatCost A h u p σ v w‖ +
        ‖energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)‖ := norm_add_le _ _
    dsimp only [N] at *; nlinarith [hc v w, hg v w]
  · intro v w
    have hv : ‖heatVariance A h u p σ v w‖ = (1/2:ℝ) *
        ‖energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)‖ := by
      simp [heatVariance, norm_mul]
    rw [hv]; dsimp only [N] at *; nlinarith [hg v w]
  · intro v w; dsimp only [N] at *; nlinarith [hc v w]
  · intro v w z hw hz
    have hx := two_abs_heatMixed_le A hh u p hσ hw hz
    rw [← Real.norm_eq_abs] at hx
    have hwle := le_abs_self (heatCost A h u p σ v w)
    have hzle := le_abs_self (heatCost A h u p σ v z)
    rw [← Real.norm_eq_abs] at hwle hzle
    dsimp only [N] at *; nlinarith [hc v w, hc v z]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.Heat.heatAtBounds_of_norms.{uι} := @_root_.OAI.TriangularHilbert.Heat.heatAtBounds_of_norms.{uι}
