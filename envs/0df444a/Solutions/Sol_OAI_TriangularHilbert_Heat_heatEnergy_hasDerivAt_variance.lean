-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.heatEnergy_hasDerivAt_variance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:28:16.111397+00:00
-- url     : https://prove2.me/submissions/88981d53-67c7-40b1-be5a-985f93b0ad23

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/HeatStar.lean:L117-L132
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.heatEnergy_hasDerivAt_variance. The node keeps its source
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
import Theorems.Thm_OAI_TriangularHilbert_Heat_weight_hasDerivAt_variance
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_energy_supported_path_hasDerivAt
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_exists_kernel_projection

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

omit [Fintype ι] [DecidableEq ι] in
lemma triangleBlocks_diag (W : Three → Matrix ι ι ℂ) (v : Three) :
    triangleBlocks W v v = 0 := by
  fin_cases v <;> simp [triangleBlocks]

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

lemma diagonal_real_hasDerivAt {w : ℝ → ι → ℝ} {w' : ι → ℝ} {x : ℝ}
    (hd : ∀ i, HasDerivAt (fun t => w t i) (w' i) x) :
    HasDerivAt (fun t => Matrix.diagonal (fun i => (w t i : ℂ)))
      (Matrix.diagonal (fun i => (w' i : ℂ))) x := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.diagonal_apply_eq] using (hd i).ofReal_comp
  · simpa only [Matrix.diagonal_apply_ne _ hij] using
      (hasDerivAt_const x (0 : ℂ))

lemma weightedGram_hasDerivAt (B : Matrix ι ι ℂ)
    {w : ℝ → ι → ℝ} {w' : ι → ℝ} {x : ℝ}
    (hd : ∀ i, HasDerivAt (fun t => w t i) (w' i) x) :
    HasDerivAt (fun t => weightedGram B (w t)) (weightedGram B w') x :=
  ((diagonal_real_hasDerivAt hd).const_mul Bᴴ).mul_const B

theorem energy_weightedGram_hasDerivAt (B : Matrix ι ι ℂ)
    {w : ℝ → ι → ℝ} {w' : ι → ℝ} {x : ℝ}
    (hw : ∀ᶠ t in 𝓝 x, ∀ i, 0 < w t i)
    (hd : ∀ i, HasDerivAt (fun t => w t i) (w' i) x) :
    HasDerivAt (fun t => energy (weightedGram B (w t)))
      (energyGradient (weightedGram B (w x)) (weightedGram B w')) x := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw.self_of_nhds
  exact energy_supported_path_hasDerivAt hQ hQQ hPD
    (hw.mono fun t ht => weightedGram_posSemidef B (fun i => (ht i).le))
    (Eventually.of_forall fun t => weightedGram_mul_eq_zero B Q (w t) hBQ)
    (weightedGram_hasDerivAt B hd)

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

lemma weightedGram_smul (B : Matrix ι ι ℂ) (c : ℝ) (w : ι → ℝ) :
    weightedGram B (fun i => c * w i) = c • weightedGram B w := by
  have he : Matrix.diagonal (fun i => ((c * w i : ℝ) : ℂ)) =
      c • Matrix.diagonal (fun i => (w i : ℂ)) := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    simp
  unfold weightedGram
  rw [he, Matrix.mul_smul, Matrix.smul_mul]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.WeightedStar ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

lemma rowStar_apply (A : Three → Matrix ι ι ℂ) (v : Three) (a b : BlockSpace ι) :
    rowStar A v a b = if a.1 = v then triangleBlocks A a.1 b.1 a.2 b.2 else 0 := by
  simp [rowStar, vertexProj, triangle, blocks, Matrix.diagonal_mul, ite_mul]

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

lemma rowBare_congr (A : Three → Matrix ι ι ℂ) (g g' : Three → ι → ℝ) (v : Three)
    (he : ∀ w, w ≠ v → ∀ i, g' w i = g w i) : rowBare A g' v = rowBare A g v := by
  ext a b
  dsimp only [rowBare, vertexRoot]
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal, rowStar_apply]
  by_cases ha : a.1 = v
  · rw [ite_eq_left ha]
    by_cases hb : b.1 = v
    · rw [ha, hb, triangleBlocks_diag, Matrix.zero_apply, zero_mul, zero_mul]
    · rw [he b.1 hb]
  · rw [ite_eq_right ha, zero_mul, zero_mul]

lemma colBare_congr (A : Three → Matrix ι ι ℂ) (g g' : Three → ι → ℝ) (v : Three)
    (he : ∀ i, g' v i = g v i) : colBare A g' v = colBare A g v := by
  ext a b
  dsimp only [colBare, vertexRoot]
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
  simp only [Matrix.conjTranspose_apply, rowStar_apply]
  by_cases hb : b.1 = v
  · rw [ite_eq_left hb, hb, he]
  · rw [ite_eq_right hb, star_zero, zero_mul, zero_mul]

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

omit [Fintype ι] [DecidableEq ι] in
lemma groupWeight_hasDerivAt_variance (h : ℝ) (u : ι → ℝ) (loc : ι → ν)
    (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) (i : ι) :
    HasDerivAt (fun q => groupWeight h u loc p (Function.update σ v q) i)
      ((1/2 : ℝ) * groupSecond h u loc p σ v i) (σ v) := by
  by_cases hi : loc i = v
  · simpa [groupWeight, groupSecond, hi, mul_assoc] using
      weight_hasDerivAt_variance h (u i) (p v) (σ v) (hσ v)
  · simpa [groupWeight, groupSecond, hi] using
      hasDerivAt_const (σ v) (weight h (u i) (p (loc i)) (σ (loc i)))

lemma groupEnergy_hasDerivAt_variance (B : Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (loc : ι → ν) (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) :
    HasDerivAt (fun q => energy (weightedGram B (groupWeight h u loc p (Function.update σ v q))))
      ((1/2 : ℝ) * energyGradient (weightedGram B (groupWeight h u loc p σ))
        (weightedGram B (groupSecond h u loc p σ v))) (σ v) := by
  have hw : ∀ᶠ q in 𝓝 (σ v), ∀ i, 0 < groupWeight h u loc p (Function.update σ v q) i := by
    filter_upwards [eventually_gt_nhds (hσ v)] with q hq
    apply groupWeight_pos hh u loc p
    intro w
    by_cases hw : w = v
    · simpa [hw] using hq
    · simpa [hw] using hσ w
  have hd := energy_weightedGram_hasDerivAt B hw (groupWeight_hasDerivAt_variance h u loc p hσ v)
  simpa only [Function.update_eq_self, weightedGram_smul, map_smul, smul_eq_mul] using hd

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

lemma fixedBase_update_variance (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) (q : ℝ) :
    fixedBase A (heatWeights h u p (Function.update σ w q)) v w =
      fixedBase A (heatWeights h u p σ) v w := by
  unfold fixedBase
  split_ifs with hw
  · subst w
    apply rowBare_congr
    intro w hw i
    simp only [heatWeights, Function.update_of_ne hw]
  · apply colBare_congr
    intro i
    simp only [heatWeights, Function.update_of_ne (Ne.symm hw)]

lemma heatEnergy_hasDerivAt_variance (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    HasDerivAt (fun q => heatEnergy A h u p (Function.update σ w q) v)
      (heatVariance A h u p σ v w) (σ w) := by
  have hd := groupEnergy_hasDerivAt_variance (fixedBase A (heatWeights h u p σ) v w)
    hh (fun a : BlockSpace ι => u a.2) Prod.fst p hσ w
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (hσ w)] with q hq
  have hσ' : ∀ a, 0 < Function.update σ w q a := by
    intro a
    by_cases ha : a = w
    · simpa [ha] using hq
    · simpa [ha] using hσ a
  rw [heatEnergy_eq_localGram A hh u _ hσ' v w]
  unfold localGram
  rw [fixedBase_update_variance]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.Heat.heatEnergy_hasDerivAt_variance.{uι} := @_root_.OAI.TriangularHilbert.Heat.heatEnergy_hasDerivAt_variance.{uι}
