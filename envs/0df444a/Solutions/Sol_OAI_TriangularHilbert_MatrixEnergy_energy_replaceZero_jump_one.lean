-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.energy_replaceZero_jump_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:12:09.918755+00:00
-- url     : https://prove2.me/submissions/21c5c9a6-d315-458f-a064-3ce3bedf1b3b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/StarJump.lean:L59-L88
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.energy_replaceZero_jump_one. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_energy_jump_le

-- ---- from OAI.Analysis.TriangularHilbert.WeightedStar ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowStar_apply (A : Three → Matrix ι ι ℂ) (v : Three) (a b : BlockSpace ι) :
    rowStar A v a b = if a.1 = v then triangleBlocks A a.1 b.1 a.2 b.2 else 0 := by
  simp [rowStar, vertexProj, triangle, blocks, Matrix.diagonal_mul, ite_mul]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.StarNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowNorm_rowStar (A : Three → Matrix ι ι ℂ) (v : Three) (i : ι) :
    rowNorm (rowStar A v) (v,i) = Real.sqrt (∑ w, ∑ j, ‖triangleBlocks A v w i j‖^2) := by
  simp only [rowNorm,Fintype.sum_prod_type,rowStar_apply,ite_true]

lemma colNorm_rowStar (A : Three → Matrix ι ι ℂ) (v w : Three) (j : ι) :
    colNorm (rowStar A v) (w,j) = Real.sqrt (∑ i, ‖triangleBlocks A v w i j‖^2) := by
  unfold colNorm
  simp only [Fintype.sum_prod_type,rowStar_apply]
  congr 1
  have he (a : Three) : (∑ i, ‖if a = v then triangleBlocks A a w i j else 0‖^2) =
      if a = v then (∑ i, ‖triangleBlocks A a w i j‖^2) else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  simp

lemma rowStar_norm_mono {A B : Three → Matrix ι ι ℂ}
    (h : ∀ v i j, ‖A v i j‖ ≤ ‖B v i j‖) (v : Three) (a b : BlockSpace ι) :
    ‖rowStar A v a b‖ ≤ ‖rowStar B v a b‖ := by
  simp only [rowStar_apply]
  by_cases hv : a.1 = v
  · simp only [ite_eq_left hv]
    unfold triangleBlocks
    split_ifs <;> first | exact le_rfl | exact h _ _ _ | simpa only [Matrix.conjTranspose_apply,norm_star] using h _ _ _
  · simp [hv]

omit [Fintype ι] [DecidableEq ι] in
lemma weightedArray_norm (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) (i j : ι) :
    ‖weightedArray A g v i j‖ = Real.sqrt (g v i)*‖A v i j‖*Real.sqrt (g (v+1) j) := by
  simp only [weightedArray,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

omit [Fintype ι] [DecidableEq ι] in
lemma weightedArray_norm_sq (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) (i j : ι) :
    ‖weightedArray A g v i j‖^2 = g v i*‖A v i j‖^2*g (v+1) j := by
  rw [weightedArray_norm,mul_pow,mul_pow,Real.sq_sqrt (hg v i),Real.sq_sqrt (hg (v+1) j)]

lemma rowNorm_weightedStar_one (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (j : ι) :
    rowNorm (rowStar (weightedArray A g) 1) (1,j) =
      Real.sqrt (g 1 j) * Real.sqrt ((∑ i, ‖A 0 i j‖^2*g 0 i)+(∑ i, ‖A 1 j i‖^2*g 2 i)) := by
  rw [rowNorm_rowStar,Fin.sum_univ_three]
  simp only [triangleBlocks,show (1:Three) ≠ 0 by decide,show (2:Three) ≠ 0 by decide,show (2:Three) ≠ 1 by decide,ite_true,ite_false,Matrix.zero_apply,Matrix.conjTranspose_apply,norm_star,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,add_zero]
  simp_rw [weightedArray_norm_sq A g hg]
  simp only [show (0:Three)+1=1 by decide,show (1:Three)+1=2 by decide]
  have he : (∑ i, g 0 i*‖A 0 i j‖^2*g 1 j)+(∑ i, g 1 j*‖A 1 j i‖^2*g 2 i) =
      g 1 j*((∑ i, ‖A 0 i j‖^2*g 0 i)+(∑ i, ‖A 1 j i‖^2*g 2 i)) := by
    simp only [mul_add,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  rw [he,Real.sqrt_mul (hg 1 j)]

lemma colNorm_weightedStar_one_zero (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (i : ι) :
    colNorm (rowStar (weightedArray A g) 1) (0,i) =
      Real.sqrt (g 0 i) * Real.sqrt (∑ j, ‖A 0 i j‖^2*g 1 j) := by
  rw [colNorm_rowStar]
  simp only [triangleBlocks,show (1:Three) ≠ 0 by decide,ite_true,ite_false,Matrix.conjTranspose_apply,norm_star]
  simp_rw [weightedArray_norm_sq A g hg]
  rw [show (0:Three)+1=1 by decide]
  have he : (∑ j, g 0 i*‖A 0 i j‖^2*g 1 j) = g 0 i*(∑ j, ‖A 0 i j‖^2*g 1 j) := by
    simp only [Finset.mul_sum,mul_assoc]
  rw [he,Real.sqrt_mul (hg 0 i)]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.ZeroStar ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma weightedArray_sub (A B : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) :
    weightedArray (A-B) g = weightedArray A g-weightedArray B g := by
  ext v i j
  simp [weightedArray,mul_sub,sub_mul]

lemma rowStar_sub (A B : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar (A-B) v = rowStar A v-rowStar B v := by
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [rowStar_apply,Matrix.sub_apply]
  by_cases hv : a = v
  · simp only [ite_eq_left hv]
    fin_cases a <;> fin_cases b <;> simp [triangleBlocks]
  · simp only [ite_eq_right hv,sub_self]

omit [Fintype ι] [DecidableEq ι] in
lemma replaceZero_sub (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ) :
    replaceZero A B-replaceZero A C = replaceZero 0 (B-C) := by
  ext v i j
  by_cases hv : v=0 <;> simp [replaceZero,hv]

omit [Fintype ι] [DecidableEq ι] in
lemma weightedArray_replaceZero_zero (B : Matrix ι ι ℂ) (g : Three → ι → ℝ) :
    weightedArray (replaceZero 0 B) g = replaceZero 0 (fun i j => (Real.sqrt (g 0 i):ℂ)*B i j*(Real.sqrt (g 1 j):ℂ)) := by
  ext v i j
  by_cases hv : v=0
  · subst v
    simp [weightedArray,replaceZero,show (0:Three)+1=1 by decide]
  · simp [weightedArray,replaceZero,hv]

lemma jump_sum_one (M : Three → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) :
    (∑ a, ∑ b, rowNorm (rowStar M 1) a*colNorm (rowStar M 1) b*‖rowStar (replaceZero 0 B) 1 a b‖) =
      ∑ i, ∑ j, rowNorm (rowStar M 1) (1,j)*colNorm (rowStar M 1) (0,i)*‖B i j‖ := by
  simp only [Fintype.sum_prod_type,rowStar_apply]
  simp only [Fin.sum_univ_three]
  simp only [show (1:Three) ≠ 0 by decide, show (2:Three) ≠ 1 by decide,show (0:Three) ≠ 1 by decide,ite_true,ite_false,triangleBlocks,replaceZero]
  simp
  rw [Finset.sum_comm]

lemma weightedStar_replaceZero_norm_le (A : Three → Matrix ι ι ℂ) (B : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (g : Three → ι → ℝ) (v : Three) (a b : BlockSpace ι) :
    ‖rowStar (weightedArray (replaceZero A B) g) v a b‖ ≤ ‖rowStar (weightedArray A g) v a b‖ := by
  apply rowStar_norm_mono _ v a b
  intro w i j
  simp only [weightedArray_norm]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  by_cases hw : w=0
  · subst w
    simpa only [replaceZero,ite_true] using hB i j
  · simp [replaceZero,hw]
end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.StarJump ----
namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma sqrt_weight_product_le {a b x y d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hd : 0 ≤ d) :
    (Real.sqrt a*Real.sqrt x)*(Real.sqrt b*Real.sqrt y)*(Real.sqrt a*d*Real.sqrt b) ≤ d*a*b*(x+y)/2 := by
  have hxy : Real.sqrt x*Real.sqrt y ≤ (x+y)/2 := by
    nlinarith [Real.sq_sqrt hx,Real.sq_sqrt hy,sq_nonneg (Real.sqrt x-Real.sqrt y)]
  calc
    _ = (Real.sqrt a*Real.sqrt a)*(Real.sqrt b*Real.sqrt b)*d*(Real.sqrt x*Real.sqrt y) := by ring
    _ = d*a*b*(Real.sqrt x*Real.sqrt y) := by rw [Real.mul_self_sqrt ha,Real.mul_self_sqrt hb]; ring
    _ ≤ d*a*b*((x+y)/2) := mul_le_mul_of_nonneg_left hxy (by positivity)
    _ = _ := by ring

lemma energy_replaceZero_jump_one (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    |energy (starGram (weightedArray (replaceZero A B) g) 1)-energy (starGram (weightedArray (replaceZero A C) g) 1)| ≤
      3/2 * ∑ i, ∑ j, ‖B i j-C i j‖*g 0 i*g 1 j*
        ((∑ m, ‖A 0 m j‖^2*g 0 m)+(∑ m, ‖A 1 j m‖^2*g 2 m)+(∑ m, ‖A 0 i m‖^2*g 1 m)) := by
  have hj := energy_jump_le (rowStar (weightedArray (replaceZero A C) g) 1)
    (rowStar (weightedArray (replaceZero A B) g) 1) (rowStar (weightedArray A g) 1)
    (weightedStar_replaceZero_norm_le A C hC g 1) (weightedStar_replaceZero_norm_le A B hB g 1)
  rw [← rowStar_sub,← weightedArray_sub,replaceZero_sub,weightedArray_replaceZero_zero,jump_sum_one (weightedArray A g) (fun i j => (Real.sqrt (g 0 i):ℂ)*(B-C) i j*(Real.sqrt (g 1 j):ℂ))] at hj
  apply hj.trans
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [rowNorm_weightedStar_one A g hg,colNorm_weightedStar_one_zero A g hg]
  have hnorm : ‖(Real.sqrt (g 0 i):ℂ)*(B-C) i j*(Real.sqrt (g 1 j):ℂ)‖ =
      Real.sqrt (g 1 j)*‖B i j-C i j‖*Real.sqrt (g 0 i) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Matrix.sub_apply]
    ring
  rw [hnorm]
  have h := sqrt_weight_product_le
    (x := (∑ m, ‖A 0 m j‖^2*g 0 m)+(∑ m, ‖A 1 j m‖^2*g 2 m))
    (y := ∑ m, ‖A 0 i m‖^2*g 1 m) (hg 1 j) (hg 0 i)
    (add_nonneg (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 0 m)))
      (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 2 m))))
    (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 1 m))) (norm_nonneg (B i j-C i j))
  nlinarith
end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.energy_replaceZero_jump_one.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.energy_replaceZero_jump_one.{uι}
