-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.heatPlane_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:47:55.571973+00:00
-- url     : https://prove2.me/submissions/17cd87ec-fe04-46fc-81a7-a4f13be0f98b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/PlaneIntegral.lean:L84-L105
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.heatPlane_integrable. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Theorems.Thm_OAI_TriangularHilbert_Heat_continuous_heatMask
import Theorems.Thm_OAI_TriangularHilbert_Heat_exists_heat_uniform_majorant
import Theorems.Thm_OAI_TriangularHilbert_Heat_finite_variance_bounds
import Theorems.Thm_OAI_TriangularHilbert_Heat_rowStar_differentiableAt
import Theorems.Thm_OAI_TriangularHilbert_Heat_weight_hasDerivAt_center
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_energyGradient_supported_path_hasDerivAt
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_exists_kernel_projection
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_hessianCost_add_projection
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_rootCost_eq_of_solution
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_vertexRoot_insert

-- ---- from OAI.Analysis.TriangularHilbert.Gaussian ----
namespace OAI

section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TriangularHilbert.Heat

theorem score_hasDerivAt_center (u p σ : ℝ) :
    HasDerivAt (fun q => score u q σ) (-σ⁻¹) p := by
  convert! ((hasDerivAt_const p u).sub (hasDerivAt_id p)).div_const σ using 1
  simp [div_eq_mul_inv]

theorem weight_score_hasDerivAt_center (h u p σ : ℝ) (hσ : 0 < σ) :
    HasDerivAt (fun q => score u q σ * weight h u q σ)
      ((score u p σ ^ 2 - σ⁻¹) * weight h u p σ) p := by
  convert! (score_hasDerivAt_center u p σ).mul (weight_hasDerivAt_center h u p σ hσ) using 1
  ring

end TriangularHilbert.Heat
end
end

end OAI

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

theorem continuous_sqrt_matrix {X : Type uX} [TopologicalSpace X]
    {P : X → Matrix ι ι ℂ} (hP : _root_.Continuous P)
    (hn : ∀ x, (P x).PosSemidef) : _root_.Continuous (fun x => CFC.sqrt (P x)) :=
  CFC.continuousOn_sqrt.comp_continuous hP (fun x => (hn x).nonneg)

theorem continuous_energyGram : _root_.Continuous
    (fun R : Matrix ι ι ℂ => energy (Rᴴ * R)) := by
  unfold energy
  exact traceRealCLM.continuous.comp
    ((continuous_star.mul continuous_id).mul
      (continuous_sqrt_matrix (continuous_star.mul continuous_id)
        Matrix.posSemidef_conjTranspose_mul_self))

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

theorem energyGradient_weightedGram_hasDerivAt (B : Matrix ι ι ℂ)
    {w k : ℝ → ι → ℝ} {w' k' : ι → ℝ} {x : ℝ}
    (hw : ∀ᶠ t in 𝓝 x, ∀ i, 0 < w t i)
    (hdw : ∀ i, HasDerivAt (fun t => w t i) (w' i) x)
    (hdk : ∀ i, HasDerivAt (fun t => k t i) (k' i) x) :
    HasDerivAt (fun t => energyGradient (weightedGram B (w t)) (weightedGram B (k t)))
      (hessianPair (weightedGram B (w x)) (weightedGram B (k x)) (weightedGram B w') +
        energyGradient (weightedGram B (w x)) (weightedGram B k')) x := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw.self_of_nhds
  exact energyGradient_supported_path_hasDerivAt hQ hQQ hPD
    (hw.mono fun t ht => weightedGram_posSemidef B (fun i => (ht i).le))
    (Eventually.of_forall fun t => weightedGram_mul_eq_zero B Q (w t) hBQ)
    (Eventually.of_forall fun t => weightedGram_isHermitian B (k t))
    (Eventually.of_forall fun t => weightedGram_mul_eq_zero B Q (k t) hBQ)
    (weightedGram_hasDerivAt B hdw) (weightedGram_hasDerivAt B hdk)

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CostBlock ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma hessianPair_self_of_projection {P Q K : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hKQ : K * Q = 0) (hQK : Q * K = 0)
    (hPD : (P + Q).PosDef) : hessianPair P K K = hessianCost P K := by
  rw [← hessianPair_add_projection hP hQ hQQ hPQ hQP hKQ hQK hKQ hQK hPD,
    hessianPair_eq_PD hPD, hessianPairPD_self,
    hessianCost_add_projection hP hQ hQQ hPQ hQP hKQ hQK hPD]

lemma hessianPair_weightedGram_self (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (k : ι → ℝ) :
    hessianPair (weightedGram B w) (weightedGram B k) (weightedGram B k) =
      hessianCost (weightedGram B w) (weightedGram B k) := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw
  have hP := weightedGram_posSemidef B (fun i => (hw i).le)
  have hPQ := weightedGram_mul_eq_zero B Q w hBQ
  have hKQ := weightedGram_mul_eq_zero B Q k hBQ
  exact hessianPair_self_of_projection hP hQ hQQ hPQ
    (hermitian_mul_zero_flip hP.isHermitian hQ.isHermitian hPQ) hKQ
    (hermitian_mul_zero_flip (weightedGram_isHermitian B k) hQ.isHermitian hKQ) hPD

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
lemma groupWeight_hasDerivAt_center (h : ℝ) (u : ι → ℝ) (loc : ι → ν)
    (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) (i : ι) :
    HasDerivAt (fun q => groupWeight h u loc (Function.update p v q) σ i)
      (groupFirst h u loc p σ v i) (p v) := by
  by_cases hi : loc i = v
  · simpa [groupWeight, groupFirst, hi] using
      weight_hasDerivAt_center h (u i) (p v) (σ v) (hσ v)
  · simpa [groupWeight, groupFirst, hi] using
      hasDerivAt_const (p v) (weight h (u i) (p (loc i)) (σ (loc i)))

omit [Fintype ι] [DecidableEq ι] in
lemma groupFirst_hasDerivAt_center (h : ℝ) (u : ι → ℝ) (loc : ι → ν)
    (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) (i : ι) :
    HasDerivAt (fun q => groupFirst h u loc (Function.update p v q) σ v i)
      (groupSecond h u loc p σ v i) (p v) := by
  by_cases hi : loc i = v
  · simpa [groupFirst, groupSecond, hi] using
      weight_score_hasDerivAt_center h (u i) (p v) (σ v) (hσ v)
  · simpa [groupFirst, groupSecond, hi] using hasDerivAt_const (p v) (0 : ℝ)

omit [Fintype ι] [DecidableEq ι] in
lemma groupFirst_hasDerivAt_other (h : ℝ) (u : ι → ℝ) (loc : ι → ν)
    (p σ : ν → ℝ) {v w : ν} (hvw : v ≠ w) (i : ι) :
    HasDerivAt (fun q => groupFirst h u loc (Function.update p w q) σ v i) 0 (p w) := by
  simpa [groupFirst, Function.update_of_ne hvw] using
    hasDerivAt_const (p w) (groupFirst h u loc p σ v i)

lemma groupEnergyFirst_hasDerivAt_center (B : Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (loc : ι → ν) (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v) (v : ν) :
    HasDerivAt (fun q => energyGradient
        (weightedGram B (groupWeight h u loc (Function.update p v q) σ))
        (weightedGram B (groupFirst h u loc (Function.update p v q) σ v)))
      (hessianCost (weightedGram B (groupWeight h u loc p σ))
          (weightedGram B (groupFirst h u loc p σ v)) +
        energyGradient (weightedGram B (groupWeight h u loc p σ))
          (weightedGram B (groupSecond h u loc p σ v))) (p v) := by
  have hd := energyGradient_weightedGram_hasDerivAt B
    (Eventually.of_forall fun q i => groupWeight_pos hh u loc (Function.update p v q) hσ i)
    (groupWeight_hasDerivAt_center h u loc p hσ v)
    (groupFirst_hasDerivAt_center h u loc p hσ v)
  simp only [Function.update_eq_self] at hd
  rw [hessianPair_weightedGram_self B (groupWeight_pos hh u loc p hσ)] at hd
  exact hd

lemma groupEnergyFirst_hasDerivAt_other (B : Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (loc : ι → ν) (p : ν → ℝ) {σ : ν → ℝ} (hσ : ∀ v, 0 < σ v)
    {v w : ν} (hvw : v ≠ w) :
    HasDerivAt (fun q => energyGradient
        (weightedGram B (groupWeight h u loc (Function.update p w q) σ))
        (weightedGram B (groupFirst h u loc (Function.update p w q) σ v)))
      (hessianPair (weightedGram B (groupWeight h u loc p σ))
        (weightedGram B (groupFirst h u loc p σ v))
        (weightedGram B (groupFirst h u loc p σ w))) (p w) := by
  have hd := energyGradient_weightedGram_hasDerivAt B
    (Eventually.of_forall fun q i => groupWeight_pos hh u loc (Function.update p w q) hσ i)
    (groupWeight_hasDerivAt_center h u loc p hσ w)
    (groupFirst_hasDerivAt_other h u loc p σ hvw)
  simpa only [Function.update_eq_self, weightedGram, Complex.ofReal_zero,
    Matrix.diagonal_zero, mul_zero, zero_mul, map_zero, add_zero] using hd

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

lemma fixedBase_update_center (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) (q : ℝ) :
    fixedBase A (heatWeights h u (Function.update p w q) σ) v w =
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

lemma heatFirst_hasDerivAt_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    HasDerivAt (fun q => heatFirst A h u (Function.update p w q) σ v w)
      (heatPure A h u p σ v w) (p w) := by
  have hd := groupEnergyFirst_hasDerivAt_center (fixedBase A (heatWeights h u p σ) v w)
    hh (fun a : BlockSpace ι => u a.2) Prod.fst p hσ w
  apply hd.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro q
  dsimp only
  unfold heatFirst localGram localFirst
  rw [fixedBase_update_center]

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
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma fixedBase_update_other (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (q : ℝ) :
    fixedBase A (heatWeights h u (Function.update p z q) σ) v w =
      fixedBase A (heatWeights h u p σ) v w := by
  simp only [fixedBase, ite_eq_right hw]
  apply colBare_congr
  intro i
  simp only [heatWeights, Function.update_of_ne (Ne.symm hz)]

lemma heatFirst_hasDerivAt_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (hwz : w ≠ z) :
    HasDerivAt (fun q => heatFirst A h u (Function.update p z q) σ v w)
      (heatMixed A h u p σ v w z) (p z) := by
  have hd := groupEnergyFirst_hasDerivAt_other (colBare A (heatWeights h u p σ) v)
    hh (fun a : BlockSpace ι => u a.2) Prod.fst p hσ hwz
  simp only [heatMixed, localGram, localFirst, fixedBase, ite_eq_right hw, ite_eq_right hz]
  apply hd.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro q
  dsimp only
  unfold heatFirst localGram localFirst
  rw [fixedBase_update_other A h u p σ hw hz q]
  simp only [fixedBase, ite_eq_right hw]

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

-- ---- from OAI.Analysis.TriangularHilbert.HeatInsert ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

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

-- ---- from OAI.Analysis.TriangularHilbert.PlaneChart ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
open MatrixEnergy
noncomputable section

lemma chart_continuous (i : Three) : Continuous (fun q : ℝ × (ℝ × ℝ) => chart i q.1 q.2) := by
  unfold chart
  split_ifs <;> fun_prop

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HeatContinuous ----
namespace OAI

universe uι uE

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma heatArray_differentiableAt_centers (A : Three → Matrix ι ι ℂ) {h : ℝ}
    (hh : 0 < h) (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    (p : Three → ℝ) (v : Three) :
    DifferentiableAt ℝ (fun q => heatArray A h u q σ v) p := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have happ (w : Three) : DifferentiableAt ℝ (fun q : Three → ℝ => q w) p := by
    convert! (ContinuousLinearMap.proj w : (Three → ℝ) →L[ℝ] ℝ).differentiableAt
  have hw (a : Three) (k : ι) : DifferentiableAt ℝ
      (fun q : Three → ℝ => weight h (u k) (q a) (σ a)) p := by
    have hd := (weight_hasDerivAt_center h (u k) (p a) (σ a) (hσ a)).differentiableAt.comp p (happ a)
    exact hd
  have hleft := (hw v i).sqrt (weight_pos hh (hσ v) (u i) (p v)).ne'
  have hright := (hw (v+1) j).sqrt (weight_pos hh (hσ (v+1)) (u j) (p (v+1))).ne'
  exact ((Complex.ofRealCLM.differentiableAt.comp p hleft).mul_const (A v i j)).mul
    (Complex.ofRealCLM.differentiableAt.comp p hright)

lemma continuous_heatRow (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    Continuous (fun p => rowStar (heatArray A h u p σ) v) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (rowStar_differentiableAt (heatArray_differentiableAt_centers A hh u hσ p) v).continuousAt

lemma continuous_heatCarrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Continuous (fun p => heatCarrier A h u p σ v w) := by
  unfold heatCarrier
  split_ifs
  · exact continuous_heatRow A hh u hσ v
  · exact (continuous_heatRow A hh u hσ v).star

lemma continuous_heatEnergy (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    Continuous (fun p => heatEnergy A h u p σ v) := by
  exact continuous_energyGram.comp (continuous_heatRow A hh u hσ v)

omit [Fintype ι] in
lemma continuous_scoreMask (u : ι → ℝ) (σ : Three → ℝ) (w : Three) :
    Continuous (fun p : Three → ℝ => heatMask (fun a j => if a = w then score (u j) (p a) (σ a) else 0)) := by
  apply continuous_heatMask
  intro a j
  split_ifs
  · unfold score; fun_prop
  · exact continuous_const

omit [Fintype ι] in
lemma continuous_secondMask (u : ι → ℝ) (σ : Three → ℝ) (w : Three) :
    Continuous (fun p : Three → ℝ => heatMask (fun a j => if a = w then score (u j) (p a) (σ a)^2-(σ a)⁻¹ else 0)) := by
  apply continuous_heatMask
  intro a j
  split_ifs
  · unfold score; fun_prop
  · exact continuous_const

lemma continuous_energyGradient_insert {E : Type uE} [TopologicalSpace E]
    {R L : E → Matrix ι ι ℂ} (hr : Continuous R) (hl : Continuous L) :
    Continuous (fun x => energyGradient ((R x)ᴴ * R x) ((R x)ᴴ * L x * R x)) := by
  have hs := continuous_sqrt_matrix (hr.star.mul hr) (fun x => Matrix.posSemidef_conjTranspose_mul_self (R x))
  simp only [energyGradient_apply]
  exact continuous_const.mul (traceRealCLM.continuous.comp (hs.mul ((hr.star.mul hl).mul hr)))

lemma continuous_heatFirst (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Continuous (fun p => heatFirst A h u p σ v w) := by
  simp only [heatFirst, localGram_eq_carrier A hh u _ hσ, localFirst_eq_carrier A hh u _ hσ]
  exact continuous_energyGradient_insert (continuous_heatCarrier A hh u hσ v w)
    (continuous_scoreMask u σ w)

lemma continuous_heatSecondGradient (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Continuous (fun p => energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)) := by
  simp only [localGram_eq_carrier A hh u _ hσ, localSecond_eq_carrier A hh u _ hσ]
  exact continuous_energyGradient_insert (continuous_heatCarrier A hh u hσ v w)
    (continuous_secondMask u σ w)

lemma continuous_heatVariance (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Continuous (fun p => heatVariance A h u p σ v w) :=
  continuous_const.mul (continuous_heatSecondGradient A hh u hσ v w)

lemma measurable_heatPure (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Measurable (fun p => heatPure A h u p σ v w) := by
  have hc : Continuous (fun q : (Three → ℝ) × ℝ => heatFirst A h u (Function.update q.1 w q.2) σ v w) :=
    (continuous_heatFirst A hh u hσ v w).comp (by fun_prop)
  have hm := (measurable_deriv_with_param
    (f := fun p q => heatFirst A h u (Function.update p w q) σ v w) hc).comp
    (show Measurable (fun p : Three → ℝ => (p, p w)) by fun_prop)
  convert! hm using 1
  funext p
  exact (heatFirst_hasDerivAt_center A hh u p hσ v w).deriv.symm

lemma measurable_heatCost (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Measurable (fun p => heatCost A h u p σ v w) := by
  have hm := (measurable_heatPure A hh u hσ v w).sub
    (continuous_heatSecondGradient A hh u hσ v w).measurable
  convert! hm using 1
  funext p
  simp [heatPure, heatCost]

lemma measurable_heatMixed (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ a, 0 < σ a)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (hwz : w ≠ z) :
    Measurable (fun p => heatMixed A h u p σ v w z) := by
  have hc : Continuous (fun q : (Three → ℝ) × ℝ => heatFirst A h u (Function.update q.1 z q.2) σ v w) :=
    (continuous_heatFirst A hh u hσ v w).comp (by fun_prop)
  have hm := (measurable_deriv_with_param
    (f := fun p q => heatFirst A h u (Function.update p z q) σ v w) hc).comp
    (show Measurable (fun p : Three → ℝ => (p, p z)) by fun_prop)
  convert! hm using 1
  funext p
  exact (heatFirst_hasDerivAt_other A hh u p hσ hw hz hwz).deriv.symm

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.PlaneIntegral ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma measurable_chart (i : Three) (d : ℝ) : Measurable (chart i d) :=
  ((chart_continuous i).comp (continuous_const.prodMk continuous_id)).measurable

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma heatPlane_integrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) :
    HeatPlaneIntegrable A h u d σ := by
  obtain ⟨a,b,ha,hab,hla,hlb⟩ := finite_variance_bounds σ hσ
  obtain ⟨B,hB,_,hbound⟩ := exists_heat_uniform_majorant A hh ha hab (abs_nonneg d) u
  have hb i z := hbound i d z (le_refl |d|) σ hla hlb
  have hmono (f : (Three → ℝ) → ℝ) (hf : Measurable f) (i : Three)
      (hb : ∀ z, ‖f (chart i d z)‖ ≤ B z) : Integrable (fun z => f (chart i d z)) :=
    hB.mono' (hf.comp (measurable_chart i d)).aestronglyMeasurable (Eventually.of_forall hb)
  constructor
  · intro i v
    exact hmono _ (continuous_heatEnergy A hh u hσ v).measurable i (fun z => (hb i z).energy v)
  · intro i v w
    exact hmono _ (continuous_heatFirst A hh u hσ v w).measurable i (fun z => (hb i z).first v w)
  · intro i v w
    exact hmono _ (measurable_heatPure A hh u hσ v w) i (fun z => (hb i z).pure v w)
  · intro i v w
    exact hmono _ (continuous_heatVariance A hh u hσ v w).measurable i (fun z => (hb i z).variance v w)
  · intro i v w
    exact hmono _ (measurable_heatCost A hh u hσ v w) i (fun z => (hb i z).cost v w)
  · intro i v w z hw hz hwz
    exact hmono _ (measurable_heatMixed A hh u hσ hw hz hwz) i (fun x => (hb i x).mixed v w z hw hz)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.Heat.heatPlane_integrable.{uι} := @_root_.OAI.TriangularHilbert.Heat.heatPlane_integrable.{uι}
