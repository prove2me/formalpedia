-- Prove2me | solution 1 for OAI.CKSLorentz.SourceCollarAtlas.eventually_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:48:54.855889+00:00
-- url     : https://prove2.me/submissions/ccc8e17d-d1ba-4d7f-ac7d-e98d09d3d772

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSMixedGeometry_source_actual_collar_coordinate_DEC
import Theorems.Thm_OAI_CKSAngularGeometry_physical_normalized_DEC_iff
import Theorems.Thm_OAI_CKSMixedGeometry_source_actual_collar_future_regions

set_option linter.all false

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma inverse_eq (q : Mat) : inverse q = q⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, ← determinant_eq]
  ext i j
  simp [inverse, div_eq_mul_inv, mul_comm]

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSCalculus
noncomputable section
open Filter Set
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma D_congr {f g : E → ℝ} {x : E} (h : f =ᶠ[𝓝 x] g) (e : E) : D e f x = D e g x := by
  unfold D
  rw [h.fderiv_eq]

lemma D_const (e x : E) (c : ℝ) : D e (fun _ => c) x = 0 := by simp [D]
lemma D_add (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f y + g y) x = D e f x + D e g x := by
  simp [D, fderiv_fun_add hf hg]
lemma D_sub (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f y - g y) x = D e f x - D e g x := by
  simp [D, fderiv_fun_sub hf hg]

lemma D_const_mul (e : E) {f : E → ℝ} {x : E} (c : ℝ)
    (hf : DifferentiableAt ℝ f x) : D e (fun y => c * f y) x = c * D e f x := by
  rw [D_mul e (differentiableAt_const c) hf, D_const]
  ring

lemma contDiffAt_D {f : E → ℝ} {x : E} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f x)
    {m : ℕ∞ω} (hmn : m + 1 ≤ n) (e : E) : ContDiffAt ℝ m (D e f) x :=
  (hf.fderiv_right hmn).clm_apply contDiffAt_const

lemma D_pow (e : E) {f : E → ℝ} {x : E} (n : ℕ)
    (hf : DifferentiableAt ℝ f x) :
    D e (fun y => f y ^ n) x = n * f x ^ (n - 1) * D e f x := by
  unfold D
  rw [fderiv_fun_pow n hf]
  simp

lemma D_D_const (e w x : E) (c : ℝ) : D w (D e (fun _ => c)) x = 0 := by
  have h : D e (fun _ : E => c) = fun _ => 0 := funext (fun y => D_const e y c)
  rw [h, D_const]

lemma D_comp_real (e : E) {f : ℝ → ℝ} {g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f (g y)) x = deriv f (g x) * D e g x := by
  unfold D
  change fderiv ℝ (f ∘ g) x e = _
  rw [(hf.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt).fderiv]
  simp

end
end CKSCalculus

end









end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma component_diff {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x) (i k : I) :
    ContDiffAt ℝ 2 (fun y => q y i k) x := by
  exact contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma first_diff {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x) (a i k : I) :
    DifferentiableAt ℝ (D (basis a) (fun y => q y i k)) x :=
  (contDiffAt_D (component_diff hq i k) (m := 1) (by norm_num) (basis a)).differentiableAt (by norm_num)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma actualScalarJet_const (c : ℝ) (x : Point) : actualScalarJet (fun _ => c) x = constantJet c := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a; exact D_const _ _ _
  · ext a b; exact D_D_const _ _ _ _

lemma actualScalarJet_add {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    actualScalarJet (fun y => f y+g y) x = actualScalarJet f x+actualScalarJet g x := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a
    exact D_add _ (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))
  · ext a b
    have heq : D (basis b) (fun y => f y+g y) =ᶠ[𝓝 x]
        (fun y => D (basis b) f y+D (basis b) g y) := by
      filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hyf hyg
      exact D_add _ (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
    change D (basis a) (D (basis b) (fun y => f y+g y)) x = _
    rw [D_congr heq]
    exact D_add _ ((contDiffAt_D hf (m := 1) (by norm_num) (basis b)).differentiableAt (by norm_num))
      ((contDiffAt_D hg (m := 1) (by norm_num) (basis b)).differentiableAt (by norm_num))

lemma actualScalarJet_smul (c : ℝ) {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 2 f x) :
    actualScalarJet (fun y => c*f y) x = c • actualScalarJet f x := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a
    exact D_const_mul _ c (hf.differentiableAt (by norm_num))
  · ext a b
    have heq : D (basis b) (fun y => c*f y) =ᶠ[𝓝 x]
        (fun y => c*D (basis b) f y) := by
      filter_upwards [hf.eventually (by norm_num)] with y hyf
      exact D_const_mul _ c (hyf.differentiableAt (by norm_num))
    change D (basis a) (D (basis b) (fun y => c*f y)) x = _
    rw [D_congr heq]
    exact D_const_mul _ c ((contDiffAt_D hf (m := 1) (by norm_num) (basis b)).differentiableAt (by norm_num))

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma actualJet_smul (c : ℝ) {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) :
    actualJet (fun y => c • q y) x = c • actualJet q x := by
  have hm (e : Point) {f : Point → ℝ} {y : Point} (hf : DifferentiableAt ℝ f y) :
      D e (fun z => c*f z) y = c*D e f y := by
    rw [D_mul _ (differentiableAt_const _) hf,D_const]
    ring
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a i k
    exact hm _ ((component_diff hq i k).differentiableAt (by norm_num))
  · ext a b i k
    have he : (fun y => D (basis b) (fun z => c*q z i k) y) =ᶠ[𝓝 x]
        (fun y => c*D (basis b) (fun z => q z i k) y) := by
      filter_upwards [hq.eventually (by norm_num)] with y hqy
      exact hm _ ((component_diff hqy i k).differentiableAt (by norm_num))
    change D (basis a) (fun y => D (basis b) (fun z => c*q z i k) y) x = _
    unfold D at he ⊢
    rw [he.fderiv_eq]
    exact hm _ (first_diff hq b i k)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma component_three {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 3 q x) (i k : I) :
    ContDiffAt ℝ 3 (fun y => q y i k) x :=
  contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k

lemma normalizedLie_diff {q : Point → Mat} {S : Point → Point} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hS : ContDiffAt ℝ 3 S x) (i k : I) :
    ContDiffAt ℝ 2 (fun y => normalizedLie q S y i k) x := by
  have hSa (a : I) := contDiffAt_pi.mp hS a
  have hqa := component_three hq
  have h23 : (2:ℕ∞ω) ≤ 3 := by norm_num
  apply ContDiffAt.sum
  intro a ha
  exact ((((hSa a).of_le h23).mul (contDiffAt_D (hqa i k) (by norm_num) (basis a))).add
      (((hqa a k).of_le h23).mul (contDiffAt_D (hSa a) (by norm_num) (basis i)))).add
      (((hqa i a).of_le h23).mul (contDiffAt_D (hSa a) (by norm_num) (basis k)))

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma actualScalarJet_congr {f g : Point → ℝ} {x : Point} (h : f =ᶠ[𝓝 x] g) :
    actualScalarJet f x = actualScalarJet g x := by
  apply Prod.ext
  · exact h.eq_of_nhds
  apply Prod.ext
  · ext a
    exact D_congr h (basis a)
  · ext a b
    have hd : D (basis b) f =ᶠ[𝓝 x] D (basis b) g := by
      filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
      exact congrArg (fun L : Point →L[ℝ] ℝ => L (basis b)) hy
    exact D_congr hd (basis a)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma component_diff {n : ℕ∞ω} {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ n q x) (i k : A) : ContDiffAt ℝ n (fun y => q y i k) x :=
  contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radiusPower_smooth (n : ℝ) : ContDiff ℝ ∞ (radiusPower n) := by unfold radiusPower; fun_prop
lemma radiusPower_diff (n : ℝ) (m : ℕ) (x : Point) : ContDiffAt ℝ m (radiusPower n) x :=
  ((radiusPower_smooth n).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt

lemma D_radiusPower (n : ℝ) (a : I) :
    D (basis a) (radiusPower n) = fun x => (n*basis a 0)*radiusPower n x := by
  funext x
  have hc : DifferentiableAt ℝ (fun y : Point => y 0) x := by fun_prop
  unfold radiusPower
  rw [D_comp_real (basis a) (Real.differentiableAt_exp) (hc.const_mul n),
    Real.deriv_exp,D_const_mul (basis a) n hc]
  change Real.exp (n*x 0) * (n*D (basis a) (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ) x) = _
  rw [D_clm]
  simp only [ContinuousLinearMap.proj_apply]
  ring

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def lapseCoefficientRegion : Set LapseCoefficientInput :=
  {p | 0 < (lapseRad p).1 ∧ (lapseD p).1 ≠ 0}

lemma lapseA_identity {p : LapseCoefficientInput} (hp : p ∈ lapseCoefficientRegion) :
    Real.sqrt ((lz p^2+(1+lz p^3*(lT p).1)^2-2*lz p^3*(lF p).1)/(1+lz p^2)) /
      (1+lz p^3*(lD p).1) = 1+lz p^3*(lapseA p).1 := by
  have hrad : (lz p^2+(1+lz p^3*(lT p).1)^2-2*lz p^3*(lF p).1)/(1+lz p^2) =
      (lapseRad p).1 := by
    simp only [lapseRad,lapseV,Prod.fst_add,Prod.fst_sub,Prod.smul_fst,smul_eq_mul,constantJet,productJet]
    have hz : 1+lz p^2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hrad]
  have hden : 1+lz p^3*(lD p).1 ≠ 0 := hp.2
  have hs : Real.sqrt (lapseRad p).1+1 ≠ 0 := by positivity
  have he : Real.sqrt (lapseRad p).1^2 = 1+lz p^3*(lapseV p).1 := Real.sq_sqrt hp.1.le
  change Real.sqrt (lapseRad p).1/(1+lz p^3*(lD p).1) =
    1+lz p^3*(((lapseV p).1*(1/(Real.sqrt (lapseRad p).1+1))-(lD p).1)*(1/(1+lz p^3*(lD p).1)))
  field_simp
  linear_combination he

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def traceProduct (q p : Mat) : ℝ := ∑ i, ∑ k, q i k*p k i

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma inverse_diff_at {n : ℕ} {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ n q x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ n (fun y => inverse (q y)) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  unfold inverse
  apply ContDiffAt.div
  · fin_cases i <;> fin_cases k <;> dsimp <;> first
      | exact contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _
      | exact (contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _).neg
  · exact (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt.comp x hq
  · exact h0

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma traceProduct_add (q p t : Mat) : traceProduct q (p+t) = traceProduct q p+traceProduct q t := by
  simp [traceProduct,mul_add,Finset.sum_add_distrib]
lemma traceProduct_smul (c : ℝ) (q p : Mat) : traceProduct q (c • p) = c*traceProduct q p := by
  simp [traceProduct]
  ring

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma metricBlock_submatrix (a : ℝ) (b : Point) (q : Mat) :
    (metricBlock a b q).submatrix Fin.succ Fin.succ = q := by
  ext i k
  fin_cases i <;> fin_cases k <;> rfl

lemma metricBlock_leaf_posDef {a : ℝ} {b : Point} {q : Mat} (h : (metricBlock a b q).PosDef) :
    q.PosDef := by
  have hi : Function.Injective (Fin.succ : I → Fin 3) := Fin.succ_injective 2
  simpa only [metricBlock_submatrix] using h.submatrix hi

lemma inverse_quadratic (q : Mat) (hq : determinant q ≠ 0) (b : Point) :
    (∑ i, ∑ k, q i k*(∑ a, inverse q i a*b a)*(∑ a, inverse q k a*b a)) =
      ∑ i, ∑ k, inverse q i k*(b i*b k) := by
  simp only [Fin.sum_univ_two,inverse]
  field_simp
  dsimp [determinant] at *
  ring

lemma inverse_mul_vector (q : Mat) (hq : determinant q ≠ 0) (b : Point) (i : I) :
    ∑ k, q i k*(∑ a, inverse q k a*b a) = b i := by
  fin_cases i <;> simp only [Fin.sum_univ_two,inverse] <;>
    field_simp <;> dsimp [determinant] at * <;> ring

lemma metricBlock_schur_positive {a : ℝ} {b : Point} {q : Mat}
    (h : (metricBlock a b q).PosDef) :
    0 < a-∑ i, ∑ k, inverse q i k*(b i*b k) := by
  have hq : determinant q ≠ 0 := by rw [determinant_eq]; exact (metricBlock_leaf_posDef h).det_pos.ne'
  let s : Point := fun i => ∑ k, inverse q i k*b k
  let v : Fin 3 → ℝ := ![1,-s 0,-s 1]
  have hv : v ≠ 0 := by
    intro hh
    have hh' := congrFun hh 0
    norm_num [v] at hh'
  have hp := h.dotProduct_mulVec_pos hv
  have hquad : (star v) ⬝ᵥ (metricBlock a b q *ᵥ v) = a-∑ i, ∑ k, inverse q i k*(b i*b k) := by
    have hmul0 : q 0 0*s 0+q 0 1*s 1=b 0 := by simpa [s,Fin.sum_univ_two] using inverse_mul_vector q hq b 0
    have hmul1 : q 1 0*s 0+q 1 1*s 1=b 1 := by simpa [s,Fin.sum_univ_two] using inverse_mul_vector q hq b 1
    have hbb : (∑ i, ∑ k, inverse q i k*(b i*b k)) = b 0*s 0+b 1*s 1 := by
      simp [s,Fin.sum_univ_two]
      ring
    rw [hbb]
    simp only [v,metricBlock,Matrix.of_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      star_trivial,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      one_mul,neg_mul,mul_neg]
    simp only [Matrix.tail_cons, Matrix.head_cons,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      mul_one]
    nlinarith [congrArg (fun t : ℝ => t * s 0) hmul0, congrArg (fun t : ℝ => t * s 1) hmul1]
  rwa [hquad] at hp

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radiusPower_nat (n : ℕ) (x : Point) : radiusPower n x = Real.exp (x 0)^n := by
  exact Real.exp_nat_mul (x 0) n

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix

lemma hermitian_real_symmetry {n : Type*} {q : Matrix n n ℝ} (h : q.IsHermitian) (i j : n) :
    q j i=q i j := by
  simpa only [conjTranspose_apply,star_trivial] using congrFun (congrFun h i) j

lemma metricBlock_hermitian (a : ℝ) (b : Point) {q : Mat} (hq : q.IsHermitian) :
    (metricBlock a b q).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTranspose_apply,metricBlock,hermitian_real_symmetry hq 0 1]

lemma foliationMetric_quadratic (U : ℝ) {γ : Mat} (hγ : γ.IsHermitian) (s : Point)
    (v : Fin 3 → ℝ) :
    star v ⬝ᵥ (foliationMetric U γ s *ᵥ v) =
      (v 0/U)^2+star (fun a : Fin 2 => v a.succ+s a*v 0) ⬝ᵥ
        (γ *ᵥ (fun a : Fin 2 => v a.succ+s a*v 0)) := by
  simp only [foliationMetric,metricBlock,Matrix.of_apply,mulVec,dotProduct,Fin.sum_univ_three,
    Fin.sum_univ_two,star_trivial,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
    Matrix.tail_cons]
  simp only [Fin.succ_zero_eq_one',Fin.succ_one_eq_two']
  rw [hermitian_real_symmetry hγ 0 1]
  ring

theorem foliationMetric_posDef {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.PosDef) (s : Point) :
    (foliationMetric U γ s).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (metricBlock_hermitian _ _ hγ.isHermitian)
  intro v hv
  change 0 < star v ⬝ᵥ (foliationMetric U γ s *ᵥ v)
  rw [foliationMetric_quadratic U hγ.isHermitian s v]
  let y : Point := fun a => v a.succ+s a*v 0
  have hy0 := hγ.posSemidef.dotProduct_mulVec_nonneg y
  by_cases h0 : v 0=0
  · have hy : y ≠ 0 := by
      intro hy
      apply hv
      ext i
      fin_cases i
      · exact h0
      · have hh := congrFun hy 0; simpa [y,h0] using hh
      · have hh := congrFun hy 1; simpa [y,h0] using hh
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (hγ.dotProduct_mulVec_pos hy)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (div_ne_zero h0 hU)) hy0

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse inverse_smul inverse_trace)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radiusPower_neg_nat (n : ℕ) (x : Point) : radiusPower (-(n:ℝ)) x = 1/Real.exp (x 0)^n := by
  rw [radiusPower,neg_mul,Real.exp_neg,Real.exp_nat_mul,one_div]
lemma radiusPower_inverse (x : Point) : radiusPower (-1) x = 1/Real.exp (x 0) := by
  simpa using radiusPower_neg_nat 1 x

lemma radiusPower_two (x : Point) : radiusPower 2 x = Real.exp (x 0)^2 := radiusPower_nat 2 x

lemma traceProduct_add (q p t : Mat) : traceProduct q (p+t) = traceProduct q p+traceProduct q t :=
  CKSAngularGeometry.traceProduct_add q p t
lemma traceProduct_smul (c : ℝ) (q p : Mat) : traceProduct q (c • p) = c*traceProduct q p :=
  CKSAngularGeometry.traceProduct_smul c q p

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal

lemma logRadiusChart_smooth : ContDiff ℝ ∞ logRadiusChart := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = 0
  · simp only [logRadiusChart,hi,ite_eq_left]; fun_prop
  · simp only [logRadiusChart,hi,ite_false]; fun_prop

theorem coordinate_continuousConstSMul : ContinuousConstSMul ℝ ℝ := inferInstance

theorem coordinate_smulCommClass :
    @SMulCommClass ℝ ℝ ℝ Algebra.toSMul
      (@instSMulOfMul ℝ (@Distrib.toMul ℝ
        (@instDistribOfSemiring ℝ (@CommSemiring.toSemiring ℝ Real.instCommSemiring)))) :=
  inferInstance

def chartDerivative (x : Point) : Point →L[ℝ] Point :=
  letI := pointDimension_neZero
  letI := coordinate_smulCommClass
  letI := coordinate_continuousConstSMul
  ContinuousLinearMap.pi (fun i => if i = 0 then Real.exp (x 0) • ContinuousLinearMap.proj 0
    else ContinuousLinearMap.proj i)

lemma logRadiusChart_hasFDerivAt (x : Point) : HasFDerivAt logRadiusChart (chartDerivative x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i = 0
  · subst i
    simpa [logRadiusChart,chartDerivative,Function.comp_def] using
      (Real.hasDerivAt_exp (x 0)).comp_hasFDerivAt x (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).hasFDerivAt
  · simp only [logRadiusChart,hi,ite_false]
    change HasFDerivAt (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) (ContinuousLinearMap.proj i) x
    exact (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).hasFDerivAt

lemma chartDerivative_basis (a : I) (x : Point) :
    chartDerivative x (basis a) = radialFactor a (logRadiusChart x) • basis a := by
  ext i
  by_cases ha : a = 0 <;> by_cases hi : i = 0
  · subst a; subst i; simp [chartDerivative,radialFactor,logRadiusChart,basis]
  · subst a; simp [chartDerivative,radialFactor,logRadiusChart,basis,hi]
  · subst i; simp [chartDerivative,radialFactor,basis,ha,Ne.symm ha]
  · simp [chartDerivative,radialFactor,basis,ha,hi]

lemma D_pullback (a : I) {f : Point → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f (logRadiusChart x)) :
    D (basis a) (fun y => f (logRadiusChart y)) x = scaledD a f (logRadiusChart x) := by
  unfold D
  change (fderiv ℝ (f ∘ logRadiusChart) x) (basis a) = _
  rw [fderiv_comp x hf (logRadiusChart_hasFDerivAt x).differentiableAt,
    (logRadiusChart_hasFDerivAt x).fderiv]
  simp only [ContinuousLinearMap.comp_apply,chartDerivative_basis,map_smul,smul_eq_mul,scaledD,D]

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma lapseVField_diff (z : ℝ) {T F : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) :
    ContDiffAt ℝ 2 (lapseVField z T F) x := by
  exact (((hT.const_smul (2:ℝ)).add ((hT.mul hT).const_smul (z^3))).sub
    (hF.const_smul (2:ℝ))).const_smul (1/(1+z^2))
lemma lapseRadField_diff (z : ℝ) {T F : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) :
    ContDiffAt ℝ 2 (lapseRadField z T F) x :=
  contDiffAt_const.add ((lapseVField_diff z hT hF).const_smul (z^3))
lemma lapseDField_diff (z : ℝ) {d : Point → ℝ} {x : Point} (hd : ContDiffAt ℝ 2 d x) :
    ContDiffAt ℝ 2 (lapseDField z d) x := contDiffAt_const.add (hd.const_smul (z^3))
lemma lapseAField_diff (z : ℝ) {T F d : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) (hd : ContDiffAt ℝ 2 d x)
    (hr : 0 < lapseRadField z T F x) (h0 : lapseDField z d x ≠ 0) :
    ContDiffAt ℝ 2 (lapseAField z T F d) x := by
  have hv := lapseVField_diff z hT hF
  have hs := ((lapseRadField_diff z hT hF).sqrt hr.ne').add (contDiffAt_const (c := (1:ℝ)))
  have hs0 : Real.sqrt (lapseRadField z T F x)+1 ≠ 0 := by positivity
  exact ((hv.mul (contDiffAt_const.div hs hs0)).sub hd).mul
    (contDiffAt_const.div (lapseDField_diff z hd) h0)

lemma lapseAField_identity (z : ℝ) (T F d : Point → ℝ) (x : Point)
    (hr : 0 < lapseRadField z T F x) (h0 : lapseDField z d x ≠ 0) :
    lapseNormalizedField z T F d x = 1+z^3*lapseAField z T F d x := by
  have hp : (z,constantJet (T x),constantJet (F x),constantJet (d x)) ∈ lapseCoefficientRegion := ⟨hr,h0⟩
  exact lapseA_identity hp

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma foliationMetric_contDiffAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => foliationMetric (U y) (γ y) (s y)) x := by
  have hγc (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have hsc (i) : ContDiffAt ℝ ∞ (fun y => s y i) x := contDiffAt_pi.mp hs i
  have hrr : ContDiffAt ℝ ∞
      (fun y => 1/(U y)^2+∑ a, ∑ b, γ y a b*s y a*s y b) x :=
    (contDiffAt_const.div (hU.pow 2) (pow_ne_zero _ h0)).add
      (ContDiffAt.sum (fun a _ => ContDiffAt.sum
        (fun b _ => ((hγc a b).mul (hsc a)).mul (hsc b))))
  have hm (a) : ContDiffAt ℝ ∞ (fun y => ∑ b, γ y a b*s y b) x :=
    ContDiffAt.sum (fun b _ => (hγc a b).mul (hsc b))
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hrr
  · exact hm 0
  · exact hm 1
  · exact hm 0
  · exact hγc 0 0
  · exact hγc 0 1
  · exact hm 1
  · exact hγc 1 0
  · exact hγc 1 1

end
end CKSAngularGeometry

end


end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def CollarCoefficientFields.RegularAt (f : CollarCoefficientFields) (x : Point) : Prop :=
  (ContDiffAt ℝ 3 (f.metric 0) x ∧ ContDiffAt ℝ 3 (f.metric 1) x ∧
    ContDiffAt ℝ 2 (f.metric 2) x) ∧ ContDiffAt ℝ 3 f.shift x ∧
  (∀ i, ContDiffAt ℝ 2 (f.scalar i) x) ∧ ContDiffAt ℝ 2 f.eta x ∧
    ContDiffAt ℝ 2 f.tau x

lemma fieldQ_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 3 (fieldQ b f) x := (hf.1.1).add ((hf.1.2.1).const_smul _)
lemma fieldQr_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldQr b f) x := (hf.1.2.2.const_smul _).sub ((hf.1.2.1.of_le (by norm_num)).const_smul _)
lemma fieldS_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 3 (fieldS b f) x := hf.2.1.const_smul _

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma angularProjection_basis_zero : angularProjection (basis 0) = 0 := by
  ext a
  simp [angularProjection,basis]

lemma D_angularLift {f : Angle → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f (angularProjection x)) : D (basis 0) (angularLift f) x = 0 := by
  unfold D angularLift
  change (fderiv ℝ (f ∘ angularProjection) x) (basis 0) = 0
  rw [fderiv_comp x hf angularProjection.differentiableAt,angularProjection.fderiv]
  simp only [ContinuousLinearMap.comp_apply,angularProjection_basis_zero,map_zero]

lemma angularLift_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Angle → E} {x : Point} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f (angularProjection x)) :
    ContDiffAt ℝ n (angularLift f) x := hf.comp x angularProjection.contDiff.contDiffAt

lemma radialMatrixD_angularLift {f : Angle → Mat} {x : Point}
    (hf : ContDiffAt ℝ 1 f (angularProjection x)) : radialMatrixD (angularLift f) x = 0 := by
  funext i k
  exact D_angularLift ((contDiffAt_pi.mp (contDiffAt_pi.mp hf i) k).differentiableAt (by norm_num))

lemma logGammaRadial_actual {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hs : radialMatrixD f.sigma x = 0) (hm : radialMatrixD f.mg x = 0) :
    logGammaRadial f x = (1/Real.exp (x 0)) • radialMatrixD (logGamma f) x := by
  funext i k
  have hσ := (component_diff hf.sigma i k).differentiableAt (by norm_num)
  have hmg := (component_diff hf.mg i k).differentiableAt (by norm_num)
  have heg := (component_diff hf.eg i k).differentiableAt (by norm_num)
  have hp := (radiusPower_diff 2 1 x).differentiableAt (by norm_num)
  have hz := (radiusPower_diff (-1) 1 x).differentiableAt (by norm_num)
  have hfun : (fun y => logGamma f y i k) = fun y =>
      radiusPower 2 y*f.sigma y i k+radiusPower (-1) y*f.mg y i k+f.eg y i k := by
    funext y
    simp [logGamma,radiusPower_two,radiusPower_inverse]
  have hσ0 : D (basis 0) (fun y => f.sigma y i k) x = 0 := congrArg (fun a : Mat => a i k) hs
  have hm0 : D (basis 0) (fun y => f.mg y i k) x = 0 := congrArg (fun a : Mat => a i k) hm
  change (2*Real.exp (x 0))*f.sigma x i k-(1/Real.exp (x 0)^2)*f.mg x i k+
    (1/Real.exp (x 0))*D (basis 0) (fun y => f.eg y i k) x =
      (1/Real.exp (x 0))*D (basis 0) (fun y => logGamma f y i k) x
  erw [hfun,D_add _ ((hp.mul hσ).add (hz.mul hmg)) heg,D_add _ (hp.mul hσ) (hz.mul hmg),
    D_mul _ hp hσ,D_mul _ hz hmg,hσ0,hm0,D_radiusPower,D_radiusPower]
  simp only [basis,Pi.single_eq_same,mul_one,radiusPower_two,radiusPower_inverse]
  have hr := Real.exp_ne_zero (x 0)
  field_simp
  ring

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma fieldC_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldC b f) x := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro k
  exact ((component_diff (fieldQr_diff b hf) i k).of_le (by norm_num)).sub
    ((normalizedLie_diff (fieldQ_diff b hf) (fieldS_diff b hf) i k).const_smul (b 0))

lemma matrixTraceField_diff {q t : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (ht : ContDiffAt ℝ 2 t x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ 2 (fun y => ∑ i, ∑ k, inverse (q y) i k*t y k i) x := by
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  have hi : ContDiffAt ℝ 2 (fun y => inverse (q y) i k) x := by
    unfold inverse
    apply ContDiffAt.div
    · fin_cases i <;> fin_cases k <;> dsimp <;>
        first | exact component_diff hq _ _ | exact (component_diff hq _ _).neg
    · exact (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq
    · exact h0
  exact hi.mul (component_diff ht k i)

lemma fieldD_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (fieldQ b f x) ≠ 0) : ContDiffAt ℝ 2 (fieldD b f) x :=
  (matrixTraceField_diff ((fieldQ_diff b hf).of_le (by norm_num)) (fieldC_diff b hf) h0).const_smul (1/4:ℝ)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma source_logFields_regular {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x)) : f.logFields.RegularAt x := by
  have hσ := hf.sigma
  have hmg := hf.mg
  have hmk := hf.mK
  have hmr := hf.mr
  rw [angularProjection_logRadiusChart] at hσ hmg hmk hmr
  have hc3 := ((logRadiusChart_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffAt (x := x))
  have hc2 := ((logRadiusChart_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt (x := x))
  exact ⟨angularLift_diff hσ,angularLift_diff hmg,hf.eg.comp x hc3,contDiffAt_const,
    angularLift_diff hmk,hf.ek.comp x hc2,hf.b.comp x hc3,angularLift_diff hmr,hf.err.comp x hc2⟩

lemma source_logGammaRadial_actual {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x)) :
    logGammaRadial f.logFields x = (1/Real.exp (x 0)) • radialMatrixD (logGamma f.logFields) x := by
  have hσ := hf.sigma
  have hmg := hf.mg
  rw [angularProjection_logRadiusChart] at hσ hmg
  exact logGammaRadial_actual (source_logFields_regular hf)
    (radialMatrixD_angularLift (hσ.of_le (by norm_num)))
    (radialMatrixD_angularLift (hmg.of_le (by norm_num)))

lemma sourceGamma_pullback (f : SourceMassFields) :
    (fun y => sourceGamma f (logRadiusChart y)) = logGamma f.logFields := by
  funext y
  simp [sourceGamma,logGamma,SourceMassFields.logFields,angularLift,
    angularProjection_logRadiusChart,logRadiusChart]

lemma sourceTangentialK_pullback (f : SourceMassFields) :
    (fun y => sourceTangentialK f (logRadiusChart y)) = logTangentialK f.logFields := by
  funext y
  simp [sourceTangentialK,logTangentialK,SourceMassFields.logFields,angularLift,
    angularProjection_logRadiusChart,logRadiusChart]

lemma sourceRadialMetric_pullback (f : SourceMassFields) :
    (fun y => sourceRadialMetric f (logRadiusChart y)) = logRadialMetric f.logFields := by
  funext y
  simp [sourceRadialMetric,logRadialMetric,SourceMassFields.logFields,angularLift,
    angularProjection_logRadiusChart,logRadiusChart]

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma fieldT_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldT b f) x := by
  unfold fieldT; exact contDiffAt_const.mul (hf.2.2.1 0)
lemma fieldF_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldF b f) x :=
by
  unfold fieldF
  exact ((contDiffAt_const.mul (hf.2.2.1 1)).add (contDiffAt_const.mul (hf.2.2.1 4))).add contDiffAt_const
lemma fieldL_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldL b f) x := by
  unfold fieldL; exact contDiffAt_const.mul (hf.2.2.1 2)
lemma fieldTr_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldTr b f) x := by
  unfold fieldTr; exact (contDiffAt_const.mul (hf.2.2.1 3)).sub (contDiffAt_const.mul (hf.2.2.1 0))

lemma lapse_radical_reconstruction {r T F : ℝ} (hr : 0 < r) :
    1+(r*(1+(1/r)^3*T))^2-2*F/r =
      (1+r^2)*(1+(1/r)^3*((2*T+(1/r)^3*T^2-2*F)/(1+(1/r)^2))) := by
  have hz : 1+(1/r)^2 ≠ 0 := by positivity
  field_simp
  ring

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma sourceGamma_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ 3 (sourceGamma f) y := by
  have hr : ContDiffAt ℝ 3 (fun z : Point => z 0) y := by fun_prop
  exact (((hr.pow 2).smul (angularLift_diff hf.sigma)).add
      ((contDiffAt_const.fun_div hr hy).smul (angularLift_diff hf.mg))).add hf.eg

def sourceGammaRadial (f : SourceMassFields) : Point → Mat := radialMatrixD (sourceGamma f)

def sourceExpansion (f : SourceMassFields) : Point → ℝ := fun y =>
  (y 0)/4*traceProduct (inverse (sourceGamma f y))
    (sourceGammaRadial f y-(show Mat from normalizedLie (sourceGamma f) (sourceShift f) y))

def sourcePhysicalMass (f : SourceMassFields) : Point → ℝ := fun y =>
  (y 0)/2*(1+((y 0)/2*traceProduct (inverse (sourceGamma f y)) (sourceTangentialK f y))^2-
    ((1/Real.sqrt (sourceSchur f y))*sourceExpansion f y)^2)

lemma sourceShift_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0)
    (h0 : determinant (sourceGamma f y) ≠ 0) : ContDiffAt ℝ 3 (sourceShift f) y := by
  have hi := inverse_diff_at (sourceGamma_regular hf hy) h0
  apply contDiffAt_pi.mpr
  intro a
  exact ContDiffAt.sum fun b _ => (component_diff hi a b).mul (contDiffAt_pi.mp hf.b b)

lemma sourceShift_pullback (f : SourceMassFields) :
    (fun y => sourceShift f (logRadiusChart y)) = logShift f.logFields := by
  funext x a
  unfold sourceShift logShift
  have hq := congrFun (sourceGamma_pullback f) x
  rw [hq]
  rfl

lemma sourceSchur_pullback (f : SourceMassFields) :
    (fun y => sourceSchur f (logRadiusChart y)) = logSchur f.logFields := by
  funext x
  unfold sourceSchur logSchur
  have hq := congrFun (sourceGamma_pullback f) x
  have hr := congrFun (sourceRadialMetric_pullback f) x
  rw [hq,hr]
  rfl

lemma normalizedLie_pullback {q : Point → Mat} {S : Point → Angle} {x : Point}
    (hq : ContDiffAt ℝ 1 q (logRadiusChart x)) (hS : ContDiffAt ℝ 1 S (logRadiusChart x)) (i k : A) :
    normalizedLie (fun y => q (logRadiusChart y)) (fun y => S (logRadiusChart y)) x i k =
      normalizedLie q S (logRadiusChart x) i k := by
  unfold normalizedLie
  apply Finset.sum_congr rfl
  intro a _
  have hqd (i k : A) := (component_diff hq i k).differentiableAt (by norm_num)
  have hSd (i : A) := (contDiffAt_pi.mp hS i).differentiableAt (by norm_num)
  erw [D_pullback a.succ (hqd i k),D_pullback i.succ (hSd a),D_pullback k.succ (hSd a)]
  simp [scaledD,radialFactor]

lemma sourceGammaRadial_pullback {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x)) :
    sourceGammaRadial f (logRadiusChart x) = logGammaRadial f.logFields x := by
  rw [source_logGammaRadial_actual hf,← sourceGamma_pullback]
  funext i k
  change D (basis 0) (fun y => sourceGamma f y i k) (logRadiusChart x) =
    (1/Real.exp (x 0))*D (basis 0) (fun y => sourceGamma f (logRadiusChart y) i k) x
  have hr : (logRadiusChart x) 0 ≠ 0 := by simp [logRadiusChart]
  have hd := (component_diff (sourceGamma_regular hf hr) i k).differentiableAt (by norm_num)
  erw [D_pullback 0 hd]
  simp [scaledD,radialFactor,logRadiusChart]

lemma sourceExpansion_pullback {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x))
    (h0 : determinant (sourceGamma f (logRadiusChart x)) ≠ 0) :
    sourceExpansion f (logRadiusChart x) = logExpansion f.logFields x := by
  have hr : (logRadiusChart x) 0 ≠ 0 := by simp [logRadiusChart]
  have hq := sourceGamma_regular hf hr
  have hS := sourceShift_regular hf hr h0
  have hLie : (show Mat from normalizedLie (sourceGamma f) (sourceShift f) (logRadiusChart x)) =
      (show Mat from normalizedLie (logGamma f.logFields) (logShift f.logFields) x) := by
    funext i k
    rw [← sourceGamma_pullback,← sourceShift_pullback]
    exact (normalizedLie_pullback (hq.of_le (by norm_num)) (hS.of_le (by norm_num)) i k).symm
  unfold sourceExpansion logExpansion
  rw [sourceGammaRadial_pullback hf,hLie]
  have hγ := congrFun (sourceGamma_pullback f) x
  rw [hγ]
  rfl

lemma sourcePhysicalMass_pullback {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x))
    (hp : (sourceMetric f (logRadiusChart x)).PosDef) :
    sourcePhysicalMass f (logRadiusChart x) = logPhysicalMass f.logFields x := by
  have h0 : determinant (sourceGamma f (logRadiusChart x)) ≠ 0 := by
    rw [determinant_eq]
    exact (CKSAngularGeometry.metricBlock_leaf_posDef hp).det_pos.ne'
  unfold sourcePhysicalMass logPhysicalMass
  rw [sourceExpansion_pullback hf h0]
  have hγ := congrFun (sourceGamma_pullback f) x
  have hk := congrFun (sourceTangentialK_pullback f) x
  have hs := congrFun (sourceSchur_pullback f) x
  rw [hγ,hk,hs]
  rfl

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma traceFreeField_diff {q t : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (ht : ContDiffAt ℝ 2 t x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ 2 (traceFreeField q t) x := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro k
  exact (component_diff ht i k).sub
    ((contDiffAt_const.mul (matrixTraceField_diff hq ht h0)).mul (component_diff hq i k))

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceAspect (f : SourceMassFields) (w : Angle) : ℝ :=
  traceProduct (inverse (f.sigma w)) (f.mg w+(2:ℝ) • f.mK w)+2*f.mr w

lemma source_leading_mass (f : SourceMassFields) : cksLeadingField f.logFields =
    fun y => sourceAspect f (angularProjection y)/4 := by
  funext y
  unfold cksLeadingField SourceMassFields.logFields angularLift sourceAspect
  rw [traceProduct_add,traceProduct_smul]
  ring

lemma SourceMassFields.RegularAt.eventually {f : SourceMassFields} {x : Point} (hf : f.RegularAt x) :
    ∀ᶠ y in 𝓝 x, f.RegularAt y := by
  have hc := angularProjection.continuous.continuousAt (x := x)
  filter_upwards [hc.tendsto.eventually (hf.sigma.eventually (by norm_num)),
    hc.tendsto.eventually (hf.mg.eventually (by norm_num)),
    hc.tendsto.eventually (hf.mK.eventually (by norm_num)),
    hc.tendsto.eventually (hf.mr.eventually (by norm_num)),
    hf.eg.eventually (by norm_num),hf.ek.eventually (by norm_num),
    hf.b.eventually (by norm_num),hf.err.eventually (by norm_num)]
    with y hs hm hk hmr he hek hb herr
  exact ⟨hs,hm,hk,hmr,he,hek,hb,herr⟩

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma injection_basis (a : A) : injection (CKSAngularGeometry.basis a)=CKSMixedGeometry.basis a.succ := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [CKSMixedGeometry.basis]
  · simp [CKSAngularGeometry.basis,CKSMixedGeometry.basis,Pi.single_apply]

lemma slice_hasFDerivAt (r : ℝ) (x : AP) : HasFDerivAt (slice r) injection x :=
  injection.hasFDerivAt.const_add _
lemma slice_smooth (r : ℝ) : ContDiff ℝ ∞ (slice r) :=
  contDiff_const.add injection.contDiff

lemma D_slice (a : A) (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : DifferentiableAt ℝ f (slice r x)) :
    D (CKSAngularGeometry.basis a) (fun y => f (slice r y)) x=
      D (CKSMixedGeometry.basis a.succ) f (slice r x) := by
  unfold D
  erw [fderiv_comp x hf (slice_hasFDerivAt r x).differentiableAt,
    (slice_hasFDerivAt r x).fderiv,ContinuousLinearMap.comp_apply,injection_basis]

 def restrictJet (p : CKSMixedGeometry.ScalarJet) : CKSAngularGeometry.ScalarJet :=
  (p.1,fun a => p.2.1 a.succ,fun a b => p.2.2 a.succ b.succ)

lemma actualScalarJet_slice (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : ContDiffAt ℝ 2 f (slice r x)) :
    CKSAngularGeometry.actualScalarJet (fun y => f (slice r y)) x=
      restrictJet (CKSMixedGeometry.actualScalarJet f (slice r x)) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext a; exact D_slice a r (hf.differentiableAt (by norm_num))
  · funext a b
    have he : D (CKSAngularGeometry.basis b) (fun y => f (slice r y)) =ᶠ[𝓝 x]
        (fun y => D (CKSMixedGeometry.basis b.succ) f (slice r y)) := by
      have hn := (slice_smooth r).continuous.continuousAt.tendsto.eventually (hf.eventually (by simp))
      filter_upwards [hn] with y hy
      exact D_slice b r (hy.differentiableAt (by norm_num))
    change D (CKSAngularGeometry.basis a) (D (CKSAngularGeometry.basis b) (fun y => f (slice r y))) x=_
    rw [D_congr he]
    exact D_slice a r ((contDiffAt_D hf (m:=1) (by norm_num) _).differentiableAt (by norm_num))

end
end CKSAngularSlice

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceT (f : SourceMassFields) : Point → ℝ := fun y =>
  (1/2:ℝ)*traceProduct (inverse (sourceGamma f y)) (sourceTangentialK f y)

lemma sourceT_pullback (f : SourceMassFields) :
    (fun y => sourceT f (logRadiusChart y)) = logT f.logFields := by
  funext y
  unfold sourceT logT
  rw [congrFun (sourceGamma_pullback f) y,congrFun (sourceTangentialK_pullback f) y]

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

structure LogCollarData.RegularAt (f : LogCollarData) (x : MP) : Prop where
  sigma : ContDiffAt ℝ 3 f.sigma x
  metricError : ContDiffAt ℝ 3 f.metricError x
  shift : ContDiffAt ℝ 3 f.shift x
  tError : ContDiffAt ℝ 2 f.tError x
  LError : ContDiffAt ℝ 2 f.LError x
  massError : ContDiffAt ℝ 2 f.massError x
  fstar : ContDiffAt ℝ 2 f.fstar x
  etaDivR : ContDiffAt ℝ 2 f.etaDivR x
  tauDivR2 : ContDiffAt ℝ 2 f.tauDivR2 x

end
end CKSAngularSlice

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma angular_regular {f : LogCollarData} {ρ : ℝ} {x : AP}
    (hf : f.RegularAt (slice ρ x))
    (ht : ContDiffAt ℝ 3 f.tError (slice ρ x)) : (f.angular ρ).RegularAt x := by
  have hc (n : ℕ) : ContDiffAt ℝ n (slice ρ) x :=
    (slice_smooth ρ).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ ⊤))
  have hs : ContDiffAt ℝ 3 (fun y => f.sigma (slice ρ y)) x := hf.sigma.comp x (hc 3)
  have hq : ContDiffAt ℝ 3 (fun y => Real.exp ρ^3 • f.metricError (slice ρ y)) x :=
    (hf.metricError.comp x (hc 3)).const_smul (Real.exp ρ^3)
  have hqr : ContDiffAt ℝ 2 (fun y a b => Real.exp ρ^3*
      D (CKSMixedGeometry.basis 0) (fun z => f.metricError z a b) (slice ρ y)) x := by
    apply contDiffAt_pi.mpr; intro a
    apply contDiffAt_pi.mpr; intro b
    simpa only [smul_eq_mul, Function.comp_apply] using
      ((contDiffAt_D (CKSMixedGeometry.component_diff hf.metricError a b)
      (m:=2) (by norm_num) (CKSMixedGeometry.basis 0)).comp x (hc 2)).const_smul (Real.exp ρ^3)
  refine ⟨⟨hs,hq,hqr⟩,?_,?_,?_,?_⟩
  · exact (hf.shift.comp x (hc 3)).const_smul (Real.exp ρ^5)
  · intro i
    fin_cases i
    · change ContDiffAt ℝ 2 (fun y => Real.exp ρ^3*f.tError (slice ρ y)) x
      exact contDiffAt_const.mul (hf.tError.comp x (hc 2))
    · exact (hf.fstar.comp x (hc 2)).add (hf.massError.comp x (hc 2))
    · change ContDiffAt ℝ 2 (fun y => Real.exp ρ^3*f.LError (slice ρ y)) x
      exact contDiffAt_const.mul (hf.LError.comp x (hc 2))
    · change ContDiffAt ℝ 2 (fun y => Real.exp ρ^3*D (CKSMixedGeometry.basis 0) f.tError (slice ρ y)) x
      exact contDiffAt_const.mul ((contDiffAt_D ht (m:=2) (by norm_num) (CKSMixedGeometry.basis 0)).comp x (hc 2))
    · exact hf.fstar.comp x (hc 2)
  · exact (hf.etaDivR.comp x (hc 2)).const_smul (Real.exp ρ^3)
  · exact (hf.tauDivR2.comp x (hc 2)).const_smul (Real.exp ρ^3)

end
end CKSAngularSlice

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceOriginalL (f : SourceTensorFields) : Point → ℝ := fun y =>
  (1/Real.sqrt (sourceSchur f.base y))^2*(sourceRadialK f y-
    2*∑ a, sourceShift f.base y a*f.kb y a+
    ∑ a, ∑ b, sourceTangentialK f.base y a b*(sourceShift f.base y a*sourceShift f.base y b))

def sourceOriginalEta (f : SourceTensorFields) : Point → A → ℝ := fun y a =>
  (1/Real.sqrt (sourceSchur f.base y))*(f.kb y a-∑ b, sourceShift f.base y b*sourceTangentialK f.base y b a)

def sourceOriginalTau (f : SourceTensorFields) : Point → Mat := fun y =>
  sourceTangentialK f.base y-
    (traceProduct (inverse (sourceGamma f.base y)) (sourceTangentialK f.base y)/2) • sourceGamma f.base y

lemma sourceOriginalL_pullback (f : SourceTensorFields) :
    (fun y => sourceOriginalL f (logRadiusChart y)) = logOriginalL f.logFields := by
  funext y
  unfold sourceOriginalL logOriginalL
  have hs := congrFun (sourceSchur_pullback f.base) y
  have hshift := congrFun (sourceShift_pullback f.base) y
  have hk := congrFun (sourceTangentialK_pullback f.base) y
  rw [hs,hshift,hk]
  rfl

lemma sourceOriginalEta_pullback (f : SourceTensorFields) :
    (fun y => sourceOriginalEta f (logRadiusChart y)) = logOriginalEta f.logFields := by
  funext y a
  unfold sourceOriginalEta logOriginalEta
  have hs := congrFun (sourceSchur_pullback f.base) y
  have hshift := congrFun (sourceShift_pullback f.base) y
  have hk := congrFun (sourceTangentialK_pullback f.base) y
  rw [hs,hshift,hk]
  rfl

lemma sourceOriginalTau_pullback (f : SourceTensorFields) :
    (fun y => sourceOriginalTau f (logRadiusChart y)) = logOriginalTau f.logFields := by
  funext y
  unfold sourceOriginalTau logOriginalTau
  have hq := congrFun (sourceGamma_pullback f.base) y
  have hk := congrFun (sourceTangentialK_pullback f.base) y
  rw [hq,hk]
  rfl

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI



noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix CKSAngularSlice
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma logQError_scaled (f : MassFields) (x : Point) :
    logQError f x=(1/Real.exp (x 0)^2) • logGamma f x-f.sigma x := by
  funext a b
  simp only [logQError,logGamma,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  rw [show (-3:ℝ)=-(3:ℕ) by norm_num,show (-2:ℝ)=-(2:ℕ) by norm_num,
    radiusPower_neg_nat,radiusPower_neg_nat]
  field_simp
  ring

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

lemma positive_uIcc {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : uIcc a r ⊆ Ioi 0 := by
  intro s hs
  exact lt_of_lt_of_le (lt_min ha hr) hs.1

lemma positive_interval_integrable {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : IntervalIntegrable q volume a r :=
  (hq.mono (positive_uIcc ha hr)).intervalIntegrable

lemma primitive_hasDerivAt {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : HasDerivAt (primitive a q) (q r) r := by
  exact intervalIntegral.integral_hasDerivAt_right (positive_interval_integrable hq ha hr)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hq r hr)
    (hq.continuousAt (isOpen_Ioi.mem_nhds hr))

lemma primitive_smooth {q : ℝ → ℝ} (hq : ContDiffOn ℝ ∞ q (Ioi 0))
    {a : ℝ} (ha : 0 < a) : ContDiffOn ℝ ∞ (primitive a q) (Ioi 0) := by
  apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
  constructor
  · intro r hr
    exact (primitive_hasDerivAt hq.continuousOn ha hr).differentiableAt.differentiableWithinAt
  · exact hq.congr (fun r hr => (primitive_hasDerivAt hq.continuousOn ha hr).deriv)

lemma paddingDensity_smooth : ContDiffOn ℝ ∞ paddingDensity (Ioi 0) := by
  exact contDiffOn_const.div (contDiffOn_id.mul (contDiffOn_id.sqrt (fun r hr => ne_of_gt hr)))
    (fun r hr => mul_ne_zero (ne_of_gt hr) (Real.sqrt_ne_zero'.mpr hr))

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

lemma paddingWeight_smooth (R : ℝ) : ContDiff ℝ ∞ (paddingWeight R) := by
  unfold paddingWeight
  fun_prop

lemma paddingWeight_zero {R r : ℝ} (hR : 0 < R) (hr : r ≤ R) : paddingWeight R r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : r/R ≤ 1 := (div_le_iff₀ hR).mpr (by simpa using hr)
  linarith

lemma paddingIntegrand_smooth (R : ℝ) :
    ContDiffOn ℝ ∞ (fun r => paddingWeight R r * paddingDensity r) (Ioi 0) :=
  (paddingWeight_smooth R).contDiffOn.mul paddingDensity_smooth
lemma paddingMass_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (paddingMass R) (Ioi 0) :=
  primitive_smooth (paddingIntegrand_smooth R) hR
lemma paddingMass_hasDerivAt {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    HasDerivAt (paddingMass R) (paddingWeight R r * paddingDensity r) r :=
  primitive_hasDerivAt (paddingIntegrand_smooth R).continuousOn hR hr
lemma paddingMass_initial {R r : ℝ} (hR : 0 < R) (hr : r ≤ R) : paddingMass R r = 0 := by
  apply intervalIntegral.integral_zero_ae
  filter_upwards [] with s hs
  rw [uIoc_of_ge hr] at hs
  simp only [paddingWeight_zero hR hs.2,zero_mul]

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma roundingWeight_smooth (R : ℝ) : ContDiff ℝ ∞ (roundingWeight R) := by
  unfold roundingWeight
  fun_prop
lemma roundingWeight_nonneg (R r : ℝ) : 0 ≤ roundingWeight R r := Real.smoothTransition.nonneg _

lemma roundingWeight_zero {R r : ℝ} (hR : 0 < R) (hr : r ≤ 2*R) : roundingWeight R r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h := (div_le_iff₀ hR).mpr hr
  linarith

lemma roundingWeight_deriv_initial {R r : ℝ} (hR : 0 < R) (hr : r ≤ 2*R) :
    deriv (roundingWeight R) r = 0 := by
  have hm : IsLocalMin (roundingWeight R) r := by
    apply Filter.Eventually.of_forall
    intro y
    rw [roundingWeight_zero hR hr]
    exact roundingWeight_nonneg R y
  exact hm.deriv_eq_zero

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open CKSMixedGeometry (basis radiusPower)
open CKSBending
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma paddingDensity_rpow {r : ℝ} (hr : 0 < r) :
    paddingDensity r=r^(-(3:ℝ)/2) := by
  rw [show -(3:ℝ)/2=-(1+1/2) by norm_num,Real.rpow_neg hr.le,
    Real.rpow_add hr,Real.rpow_one,← Real.sqrt_eq_rpow]
  simp [paddingDensity,one_div]

lemma radialLift_diff {h : ℝ → ℝ} {y : MP} (hh : DifferentiableAt ℝ h (Real.exp (y 0))) :
    DifferentiableAt ℝ (radialLift h) y := hh.comp y (by fun_prop)

lemma radialLift_D {h : ℝ → ℝ} {y : MP} (hh : DifferentiableAt ℝ h (Real.exp (y 0))) :
    D (basis 0) (radialLift h) y=Real.exp (y 0)*deriv h (Real.exp (y 0)) := by
  unfold radialLift
  rw [D_comp_real (g := fun y : MP => Real.exp (y 0)) _ hh (by fun_prop)]
  have he : (fun y : MP => Real.exp (y 0))=radiusPower 1 := by
    funext y; simp [radiusPower]
  rw [he,CKSMixedGeometry.D_radiusPower]
  simp [basis,radiusPower]
  ring

lemma collarQ_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    collarQ R f (slice ρ x)=CKSAngularGeometry.fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  ext a b
  simp [collarQ,radialLift,CKSAngularGeometry.fieldQ,collarParams,LogCollarData.angular]
  field_simp

lemma collarShift_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    Real.exp ρ^5 • collarShift R f (slice ρ x)=
      CKSAngularGeometry.fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  ext a
  simp [collarShift,radialLift,CKSAngularGeometry.fieldS,collarParams,LogCollarData.angular]
  ring

lemma collarT_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    Real.exp ρ^3*(collarT R f (slice ρ x)-1)=
      CKSAngularGeometry.fieldT (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  simp [collarT,radialLift,CKSAngularGeometry.fieldT,collarParams,LogCollarData.angular]
  ring

lemma collarLb_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    Real.exp ρ^3*(collarLb R f (slice ρ x)-1)=
      CKSAngularGeometry.fieldL (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  simp [collarLb,radialLift,CKSAngularGeometry.fieldL,collarParams,LogCollarData.angular]
  ring

lemma collarF_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    collarF R f (slice ρ x)=CKSAngularGeometry.fieldF (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  simp [collarF,radialLift,CKSAngularGeometry.fieldF,collarParams,LogCollarData.angular]
  ring

lemma collarEta_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    Real.exp ρ^3 • collarEtaDivR R f (slice ρ x)=
      CKSAngularGeometry.fieldEta (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  ext a
  simp [collarEtaDivR,radialLift,CKSAngularGeometry.fieldEta,collarParams,LogCollarData.angular]
  ring

lemma collarQ_radial (R ρ : ℝ) {f : LogCollarData} {x : AP}
    (hf : f.RegularAt (slice ρ x))
    (hσ : ∀ a b, D (basis 0) (fun y => f.sigma y a b) (slice ρ x)=0) (a b : Fin 2) :
    Real.exp ρ^3*D (basis 0) (fun y => collarQ R f y a b) (slice ρ x)=
      CKSAngularGeometry.fieldQr (collarParams R (Real.exp ρ)) (f.angular ρ) x a b := by
  have he := radialLift_diff ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt (y := slice ρ x)
  have hs := (CKSMixedGeometry.component_diff hf.sigma a b).differentiableAt (by norm_num)
  have hm := (CKSMixedGeometry.component_diff hf.metricError a b).differentiableAt (by norm_num)
  change Real.exp ρ^3*D (basis 0) (fun y => f.sigma y a b+
    (1-radialLift (roundingWeight R) y)*f.metricError y a b) (slice ρ x)=_
  erw [D_add _ hs (((differentiableAt_const (1:ℝ)).sub he).mul hm),D_mul _ ((differentiableAt_const (1:ℝ)).sub he) hm,
    D_sub _ (differentiableAt_const (1:ℝ)) he,D_const,hσ,
    radialLift_D ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt]
  change _ = (1-roundingWeight R (Real.exp ρ))*(Real.exp ρ^3*
    D (basis 0) (fun y => f.metricError y a b) (slice ρ x))-
      (Real.exp ρ*deriv (roundingWeight R) (Real.exp ρ))*(Real.exp ρ^3*f.metricError (slice ρ x) a b)
  dsimp only [Pi.sub_apply,radialLift]
  simp only [slice_zero]
  ring

lemma collarT_radial (R ρ : ℝ) {f : LogCollarData} {x : AP}
    (hf : f.RegularAt (slice ρ x)) :
    Real.exp ρ^3*D (basis 0) (collarT R f) (slice ρ x)=
      CKSAngularGeometry.fieldTr (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  have he := radialLift_diff ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt (y := slice ρ x)
  have ht := hf.tError.differentiableAt (by norm_num)
  unfold collarT
  erw [D_add _ (differentiableAt_const (1:ℝ)) (((differentiableAt_const (1:ℝ)).sub he).mul ht),D_const,
    D_mul _ ((differentiableAt_const (1:ℝ)).sub he) ht,D_sub _ (differentiableAt_const (1:ℝ)) he,D_const,
    radialLift_D ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt]
  simp [CKSAngularGeometry.fieldTr,collarParams,LogCollarData.angular,radialLift]
  ring

lemma collarF_radial {R : ℝ} (hR : 0 < R) (ρ : ℝ) {f : LogCollarData} {x : AP}
    (hf : f.RegularAt (slice ρ x)) (hstar : D (basis 0) f.fstar (slice ρ x)=0) :
    D (basis 0) (collarF R f) (slice ρ x)=
      (1/Real.exp ρ)*((1-roundingWeight R (Real.exp ρ))*(f.angular ρ).massRadial x-
        (Real.exp ρ*deriv (roundingWeight R) (Real.exp ρ))*(f.angular ρ).massGap x)+
      Real.exp ρ*(paddingWeight R (Real.exp ρ)*(Real.exp ρ)^(-(3:ℝ)/2)) := by
  have he := radialLift_diff ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt (y := slice ρ x)
  have hpad := paddingMass_hasDerivAt hR (Real.exp_pos ((slice ρ x) 0))
  have hc := radialLift_diff hpad.differentiableAt
  have hm := hf.massError.differentiableAt (by norm_num)
  have hs := hf.fstar.differentiableAt (by norm_num)
  unfold collarF
  erw [D_add _ (hs.add (((differentiableAt_const (1:ℝ)).sub he).mul hm)) hc,
    D_add _ hs (((differentiableAt_const (1:ℝ)).sub he).mul hm),hstar,
    D_mul _ ((differentiableAt_const (1:ℝ)).sub he) hm,D_sub _ (differentiableAt_const (1:ℝ)) he,D_const,
    radialLift_D ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt,
    radialLift_D hpad.differentiableAt,hpad.deriv]
  dsimp only [Pi.sub_apply,radialLift]
  simp only [LogCollarData.angular,slice_zero]
  rw [paddingDensity_rpow (Real.exp_pos ρ)]
  field_simp
  ring

lemma collarEta_radial (R ρ : ℝ) {f : LogCollarData} {x : AP}
    (hf : f.RegularAt (slice ρ x)) (a : Fin 2) :
    Real.exp ρ^3*(collarEtaDivR R f (slice ρ x) a+
      D (basis 0) (fun y => collarEtaDivR R f y a) (slice ρ x))=
      CKSAngularGeometry.fieldEr (collarParams R (Real.exp ρ)) (f.angular ρ) x a := by
  have he := radialLift_diff ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt (y := slice ρ x)
  have ht := (contDiffAt_pi.mp hf.etaDivR a).differentiableAt (by norm_num)
  change Real.exp ρ^3*((1-radialLift (roundingWeight R) (slice ρ x))*f.etaDivR (slice ρ x) a+
    D (basis 0) (fun y => (1-radialLift (roundingWeight R) y)*f.etaDivR y a) (slice ρ x))=_
  erw [D_mul _ ((differentiableAt_const (1:ℝ)).sub he) ht,D_sub _ (differentiableAt_const (1:ℝ)) he,D_const,
    radialLift_D ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt]
  simp [CKSAngularGeometry.fieldEr,collarParams,LogCollarData.angular,radialLift]
  ring

end
end CKSAngularSlice

end


end OAI
end

section
namespace OAI














































noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

lemma angularProjection_slice (r : ℝ) (θ : Angle) : angularProjection (slice r θ)=θ := by
  ext a
  exact slice_succ r θ a

end
end CKSLorentz

end
















noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

namespace SmoothAngularPatch

lemma param_fderiv_leftInverse (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) :
    (fderiv ℝ P.extension (P.param θ)).comp (fderiv ℝ P.param θ) =
      ContinuousLinearMap.id ℝ Angle := by
  have hφ := (P.param_contDiffAt hθ).differentiableAt (by simp)
  have hψ := (P.extension_contDiffAt_param hθ).differentiableAt (by simp)
  have hg : (fun η => P.extension (P.param η)) =ᶠ[𝓝 θ] id := by
    filter_upwards [P.chart.open_target.mem_nhds hθ] with η hη
    exact P.extension_param hη
  have ht := hg.fderiv_eq (𝕜:=ℝ)
  change fderiv ℝ (P.extension ∘ P.param) θ = fderiv ℝ id θ at ht
  rw [fderiv_comp θ hψ hφ,fderiv_id] at ht
  exact ht

lemma param_fderiv_injective (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) : Function.Injective (fderiv ℝ P.param θ) := by
  intro v w hvw
  have h := congrArg (fderiv ℝ P.extension (P.param θ)) hvw
  have hl := P.param_fderiv_leftInverse hθ
  have hv := congrArg (fun L : Angle →L[ℝ] Angle => L v) hl
  have hw := congrArg (fun L : Angle →L[ℝ] Angle => L w) hl
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
    hv.symm.trans (h.trans hw)

lemma roundMetric_posDef (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target) :
    (angularRoundMetric P.param θ).PosDef := by
  change (Matrix.gram ℝ (fun a => fderiv ℝ P.param θ (CKSAngularGeometry.basis a))).PosDef
  apply Matrix.posDef_gram_iff_linearIndependent.mpr
  have h := (Pi.basisFun ℝ (Fin 2)).linearIndependent.map'
    (fderiv ℝ P.param θ).toLinearMap
    (LinearMap.ker_eq_bot.mpr (P.param_fderiv_injective hθ))
  simpa only [Function.comp_def,Pi.basisFun_apply,CKSAngularGeometry.basis,
    ContinuousLinearMap.coe_coe] using h

end SmoothAngularPatch

end
end CKSLorentz

end



noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

lemma angularRadialTail_open (R : ℝ) {W : Set Angle} (hW : IsOpen W) :
    IsOpen (angularRadialTail R W) := by
  exact (isOpen_Ioi.preimage (continuous_apply 0)).inter
    (hW.preimage angularProjection.continuous)

end
end CKSLorentz

end



























noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafTensorTrace_contDiffAt {γ T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ ∞ γ x) (hT : ContDiffAt ℝ ∞ T x) (hp : (γ x).PosDef) :
    ContDiffAt ℝ ∞ (fun y => leafTensorTrace (γ y) (T y)) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have ht (i j) : ContDiffAt ℝ ∞ (fun y => T y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hT i) j
  have hd : ContDiffAt ℝ ∞ (fun y => determinant (γ y)) x := by
    change ContDiffAt ℝ ∞ (fun y => γ y 0 0 * γ y 1 1 - γ y 0 1 * γ y 1 0) x
    fun_prop
  have hd0 : determinant (γ x) ≠ 0 := by rw [determinant_eq]; exact hp.det_pos.ne'
  have hi (i j) : ContDiffAt ℝ ∞ (fun y => inverse (γ y) i j) x := by
    fin_cases i <;> fin_cases j
    · exact (hc 1 1).div hd hd0
    · exact (hc 0 1).neg.div hd hd0
    · exact (hc 1 0).neg.div hd hd0
    · exact (hc 0 0).div hd hd0
  simp only [leafTensorTrace, ← inverse_eq, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Fin.sum_univ_two]
  fun_prop

lemma leafTensorTraceFree_contDiffAt {γ T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ ∞ γ x) (hT : ContDiffAt ℝ ∞ T x) (hp : (γ x).PosDef) :
    ContDiffAt ℝ ∞ (fun y => leafTensorTraceFree (γ y) (T y)) x := by
  have hp' := leafTensorTrace_contDiffAt hγ hT hp
  unfold leafTensorTraceFree
  exact hT.sub ((hp'.div_const 2).smul hγ)

end
end CKSAngularGeometry

end












noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalBaseLapse_eq {r : ℝ} (hr : 0 < r) :
    physicalBaseLapse r = Real.sqrt (1+r^2) := by
  calc
    physicalBaseLapse r = Real.sqrt (r^2)*Real.sqrt (1+(1/r)^2) := by
      rw [Real.sqrt_sq hr.le]; rfl
    _ = Real.sqrt (r^2*(1+(1/r)^2)) := (Real.sqrt_mul (sq_nonneg r) _).symm
    _ = Real.sqrt (1+r^2) := by congr 1; field_simp; ring

variable (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ)

end
end CKSAngularGeometry

end














noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafTensorTrace_add (γ A B : Mat) :
    leafTensorTrace γ (A+B) = leafTensorTrace γ A+leafTensorTrace γ B := by
  simp [leafTensorTrace, Matrix.mul_add]

lemma leafTensorTrace_sub (γ A B : Mat) :
    leafTensorTrace γ (A-B) = leafTensorTrace γ A-leafTensorTrace γ B := by
  simp [leafTensorTrace, Matrix.mul_sub]

lemma leafTensorTrace_smul (γ A : Mat) (c : ℝ) :
    leafTensorTrace γ (c • A) = c*leafTensorTrace γ A := by
  simp [leafTensorTrace]

lemma leafTensorTrace_self {γ : Mat} (hp : γ.PosDef) : leafTensorTrace γ γ = 2 := by
  rw [leafTensorTrace, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne')]
  norm_num

lemma leafTensorTrace_traceFree {γ : Mat} (hp : γ.PosDef) (A : Mat) :
    leafTensorTrace γ (leafTensorTraceFree γ A) = 0 := by
  rw [leafTensorTraceFree, leafTensorTrace_sub, leafTensorTrace_smul,
    leafTensorTrace_self hp]
  ring

lemma sourceChi_radialRate (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (x : PhysicalPoint) :
    sourceChi U γ s x = (U x/2) • leafRadialRate γ s x := rfl

lemma sourceH_radialExpansion (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) {x : PhysicalPoint} (hr : x 0 ≠ 0) :
    sourceH U γ s x = 2*U x*radialExpansion γ s x/x 0 := by
  rw [sourceH, sourceChi_radialRate, leafTensorTrace_smul]
  unfold radialExpansion
  field_simp
  ring

lemma sourceP_radialTangential {γ : PhysicalPoint → Mat} {x : PhysicalPoint} (hp : (γ x).PosDef)
    (t : PhysicalPoint → ℝ) (τ : PhysicalPoint → Mat) :
    sourceP γ (radialTangential γ t τ) x = 2*t x := by
  rw [sourceP, radialTangential, leafTensorTrace_add, leafTensorTrace_smul,
    leafTensorTrace_self hp, leafTensorTrace_traceFree hp]
  ring

lemma radialMassLapse_pos {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hd : 0 < radialExpansion γ s x) (hf : 0 < radialMassRadical t F x) :
    0 < radialMassLapse γ s t F x :=
  div_pos (Real.sqrt_pos.mpr hf) hd

lemma sourceH_radialMassLapse (γ : PhysicalPoint → Mat) (s : PhysicalPoint → Point)
    (t F : PhysicalPoint → ℝ) {x : PhysicalPoint} (hr : x 0 ≠ 0)
    (hd : radialExpansion γ s x ≠ 0) :
    sourceH (radialMassLapse γ s t F) γ s x =
      2*Real.sqrt (radialMassRadical t F x)/x 0 := by
  rw [sourceH_radialExpansion _ _ _ hr, radialMassLapse]
  field_simp

theorem physical_radial_reconstruction
    (γ τ : PhysicalPoint → Mat) (s : PhysicalPoint → Point)
    (t F : PhysicalPoint → ℝ) (x : PhysicalPoint)
    (hr : 0 < x 0) (hp : (γ x).PosDef)
    (hd : 0 < radialExpansion γ s x) (hf : 0 < radialMassRadical t F x) :
    let U := radialMassLapse γ s t F
    let T := radialTangential γ t τ
    0 < U x ∧ sourceD U γ s x = radialExpansion γ s x ∧
      sourceH U γ s x = 2*Real.sqrt (radialMassRadical t F x)/x 0 ∧
      sourceP γ T x = 2*t x ∧ sourceMass U γ T s x = F x
    := by
  dsimp only
  have hU := radialMassLapse_pos hd hf
  have hH := sourceH_radialMassLapse γ s t F hr.ne' hd.ne'
  have hpT := sourceP_radialTangential hp t τ
  refine ⟨hU, ?_, hH, hpT, ?_⟩
  · rw [sourceD, hH]
    unfold radialMassLapse
    have hu := (Real.sqrt_pos.mpr hf).ne'
    field_simp
  · rw [sourceMass, CKSFrame.massField, hH, hpT]
    field_simp
    rw [Real.sq_sqrt hf.le]
    unfold radialMassRadical
    field_simp
    ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def logPointDerivative (x : PhysicalPoint) : PhysicalPoint →L[ℝ] PhysicalPoint :=
  ContinuousLinearMap.pi (fun i => if i=0 then (x 0)⁻¹ • ContinuousLinearMap.proj 0
    else ContinuousLinearMap.proj i)

lemma radiusLogPoint_smoothAt {x : PhysicalPoint} (hr : x 0 ≠ 0) :
    ContDiffAt ℝ ∞ radiusLogPoint x := by
  apply contDiffAt_pi.mpr
  intro i
  by_cases hi : i=0
  · subst i
    simp only [radiusLogPoint, ite_true]
    have hrad : ContDiffAt ℝ ∞ (fun y : PhysicalPoint => y 0) x := by fun_prop
    exact hrad.log hr
  · simp only [radiusLogPoint, hi, ite_false]
    fun_prop

lemma radiusLogPoint_hasFDerivAt {x : PhysicalPoint} (hr : x 0 ≠ 0) :
    HasFDerivAt radiusLogPoint (logPointDerivative x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i=0
  · subst i
    simpa [radiusLogPoint, logPointDerivative, Function.comp_def] using
      (Real.hasDerivAt_log hr).comp_hasFDerivAt x
        (ContinuousLinearMap.proj 0 : PhysicalPoint →L[ℝ] ℝ).hasFDerivAt
  · simp only [radiusLogPoint, hi, ite_false]
    exact (ContinuousLinearMap.proj i : PhysicalPoint →L[ℝ] ℝ).hasFDerivAt

lemma logPointDerivative_basis (i : Fin 3) (x : PhysicalPoint) :
    logPointDerivative x (CKSRealizedRound.basis i) =
      (if i=0 then (x 0)⁻¹ else 1) • CKSRealizedRound.basis i := by
  ext j
  by_cases hi : i=0 <;> by_cases hj : j=0
  · subst i; subst j; simp [logPointDerivative, CKSRealizedRound.basis]
  · subst i; simp [logPointDerivative, CKSRealizedRound.basis, hj]
  · subst j; simp [logPointDerivative, CKSRealizedRound.basis, hi, Ne.symm hi]
  · simp [logPointDerivative, CKSRealizedRound.basis, hi, hj]

lemma D_radiusLogPoint (i : Fin 3) {f : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : DifferentiableAt ℝ f (radiusLogPoint x)) :
    D (CKSRealizedRound.basis i) (fun y => f (radiusLogPoint y)) x =
      (if i=0 then (x 0)⁻¹ else 1)*D (CKSRealizedRound.basis i) f (radiusLogPoint x) := by
  unfold D
  change (fderiv ℝ (f ∘ radiusLogPoint) x) _ = _
  rw [fderiv_comp x hf (radiusLogPoint_hasFDerivAt hr).differentiableAt,
    (radiusLogPoint_hasFDerivAt hr).fderiv]
  simp only [ContinuousLinearMap.comp_apply, logPointDerivative_basis,
    map_smul, smul_eq_mul]

lemma physicalAngularScalarJet_slice {f : PhysicalPoint → ℝ} {r : ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f (slice r x)) :
    physicalAngularScalarJet f (slice r x) = actualScalarJet (fun y => f (slice r y)) x :=
  (actualScalarJet_slice r hf).symm

lemma physicalAngularJet_slice {γ : PhysicalPoint → Mat} {r : ℝ} {x : Point}
    (hγ : ContDiffAt ℝ 2 γ (slice r x)) :
    physicalAngularJet γ (slice r x) = actualJet (fun y => γ (slice r y)) x := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext a i j
    exact (D_slice a r ((contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j).differentiableAt (by norm_num))).symm
  · funext a b i j
    exact (congrFun (congrFun (congrArg (fun p : ScalarJet => p.2.2)
      (physicalAngularScalarJet_slice (contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j))) a) b)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

structure LogCollarData.SmoothAt (f : LogCollarData) (x : MP) : Prop where
  sigma : ContDiffAt ℝ ∞ f.sigma x
  metricError : ContDiffAt ℝ ∞ f.metricError x
  shift : ContDiffAt ℝ ∞ f.shift x
  tError : ContDiffAt ℝ ∞ f.tError x
  LError : ContDiffAt ℝ ∞ f.LError x
  massError : ContDiffAt ℝ ∞ f.massError x
  fstar : ContDiffAt ℝ ∞ f.fstar x
  etaDivR : ContDiffAt ℝ ∞ f.etaDivR x
  tauDivR2 : ContDiffAt ℝ ∞ f.tauDivR2 x

lemma LogCollarData.SmoothAt.regularAt {f : LogCollarData} {x : MP}
    (hf : f.SmoothAt x) : f.RegularAt x :=
  ⟨hf.sigma.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.metricError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.shift.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),
    hf.tError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.LError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.massError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),
    hf.fstar.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.etaDivR.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.tauDivR2.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)⟩

end
end CKSAngularSlice

end


noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Filter CKSBending Set
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma radialLift_smoothAt {h : ℝ → ℝ} {y : MP}
    (hh : ContDiffAt ℝ ∞ h (Real.exp (y 0))) : ContDiffAt ℝ ∞ (radialLift h) y :=
  hh.comp y (by fun_prop)

lemma collarWeight_smoothAt (R : ℝ) (y : MP) :
    ContDiffAt ℝ ∞ (radialLift (roundingWeight R)) y :=
  radialLift_smoothAt (roundingWeight_smooth R).contDiffAt

lemma collarQ_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarQ R f) y :=
  hf.sigma.add ((contDiffAt_const.sub (collarWeight_smoothAt R y)).smul hf.metricError)

lemma collarShift_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarShift R f) y :=
  (contDiffAt_const.sub (collarWeight_smoothAt R y)).smul hf.shift

lemma collarT_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarT R f) y :=
  contDiffAt_const.add ((contDiffAt_const.sub (collarWeight_smoothAt R y)).mul hf.tError)

lemma collarLb_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarLb R f) y :=
  contDiffAt_const.add ((contDiffAt_const.sub (collarWeight_smoothAt R y)).mul hf.LError)

lemma collarL_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarL R f) y := by
  apply (collarLb_smoothAt R hf).add
  apply ((paddingWeight_smooth R).contDiffAt.comp y (show ContDiffAt ℝ ∞ (fun y : MP => Real.exp (y 0)) y by fun_prop)).div
  · fun_prop
  · positivity

lemma collarF_smoothAt {R : ℝ} (hR : 0 < R) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarF R f) y :=
  (hf.fstar.add ((contDiffAt_const.sub (collarWeight_smoothAt R y)).mul hf.massError)).add
    (radialLift_smoothAt ((paddingMass_smooth hR).contDiffAt
      (isOpen_Ioi.mem_nhds (Real.exp_pos (y 0)))))

lemma collarEta_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarEtaDivR R f) y :=
  (contDiffAt_const.sub (collarWeight_smoothAt R y)).smul hf.etaDivR

lemma collarQ_regularAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.RegularAt y) :
    ContDiffAt ℝ 3 (collarQ R f) y :=
  hf.sigma.add ((contDiffAt_const.sub ((collarWeight_smoothAt R y).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))).smul hf.metricError)

lemma collarShift_regularAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.RegularAt y) :
    ContDiffAt ℝ 3 (collarShift R f) y :=
  (contDiffAt_const.sub ((collarWeight_smoothAt R y).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))).smul hf.shift

lemma LogCollarData.SmoothAt.eventually_regularAt {f : LogCollarData} {x : MP}
    (hf : f.SmoothAt x) : ∀ᶠ y in 𝓝 x, f.RegularAt y := by
  have hr := hf.regularAt
  filter_upwards [hr.sigma.eventually (by norm_num), hr.metricError.eventually (by norm_num),
    hr.shift.eventually (by norm_num),hr.tError.eventually (by norm_num),
    hr.LError.eventually (by norm_num),hr.massError.eventually (by norm_num),
    hr.fstar.eventually (by norm_num),hr.etaDivR.eventually (by norm_num),
    hr.tauDivR2.eventually (by norm_num)] with y h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩

end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarGamma_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarGamma R f) x :=
  (show ContDiffAt ℝ ∞ (fun y : PhysicalPoint => (y 0)^2) x by fun_prop).smul
    ((collarQ_smoothAt R hf).comp x (radiusLogPoint_smoothAt hr))

lemma physicalCollarShift_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarShift R f) x :=
  (collarShift_smoothAt R hf).comp x (radiusLogPoint_smoothAt hr)

lemma physicalCollarT_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarT R f) x :=
  (collarT_smoothAt R hf).comp x (radiusLogPoint_smoothAt hr)

lemma physicalCollarF_smoothAt {R : ℝ} (hR : 0 < R) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarF R f) x :=
  (collarF_smoothAt hR hf).comp x (radiusLogPoint_smoothAt hr)

lemma physicalCollarL_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarL R f) x :=
  (collarL_smoothAt R hf).comp x (radiusLogPoint_smoothAt hr)

lemma physicalCollarEta_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarEta R f) x :=
  (show ContDiffAt ℝ ∞ (fun y : PhysicalPoint => y 0) x by fun_prop).smul
    ((collarEta_smoothAt R hf).comp x (radiusLogPoint_smoothAt hr))

lemma physicalCollarRawTau_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarRawTau R f) x := by
  have hrad : ContDiffAt ℝ ∞ (fun y : PhysicalPoint => y 0) x := by fun_prop
  exact ((hrad.pow 2).mul (contDiffAt_const.sub ((roundingWeight_smooth R).contDiffAt.comp x hrad))).smul
    (hf.tauDivR2.comp x (radiusLogPoint_smoothAt hr))

lemma physicalCollarGamma_regularAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.RegularAt (radiusLogPoint x)) :
    ContDiffAt ℝ 3 (physicalCollarGamma R f) x :=
  (show ContDiffAt ℝ 3 (fun y : PhysicalPoint => (y 0)^2) x by fun_prop).smul
    ((collarQ_regularAt R hf).comp x ((radiusLogPoint_smoothAt hr).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)))

lemma physicalCollarShift_regularAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.RegularAt (radiusLogPoint x)) :
    ContDiffAt ℝ 3 (physicalCollarShift R f) x :=
  (collarShift_regularAt R hf).comp x ((radiusLogPoint_smoothAt hr).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))

end
end CKSAngularGeometry

end




noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarGamma_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarGamma R f (slice (Real.exp ρ) a) =
      Real.exp ρ^2 • fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarGamma, slice_zero, radiusLogPoint_slice, Real.log_exp,
    collarQ_slice]

lemma physicalCollarShift_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarShift R f (slice (Real.exp ρ) a) =
      (1/Real.exp ρ^5) • fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarShift, radiusLogPoint_slice, Real.log_exp]
  rw [← collarShift_slice, smul_smul]
  simp

lemma physicalCollarT_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarT R f (slice (Real.exp ρ) a) =
      1+(1/Real.exp ρ)^3*fieldT (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarT, radiusLogPoint_slice, Real.log_exp]
  rw [← collarT_slice]
  field_simp
  ring

lemma physicalCollarF_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarF R f (slice (Real.exp ρ) a) =
      fieldF (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarF, radiusLogPoint_slice, Real.log_exp]
  exact collarF_slice R ρ f a

lemma physicalCollarL_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarL R f (slice (Real.exp ρ) a) =
      1+paddingWeight R (Real.exp ρ)/Real.exp ρ^2+
        (1/Real.exp ρ)^3*fieldL (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarL, radiusLogPoint_slice, Real.log_exp, collarL, slice_zero]
  rw [← collarLb_slice]
  field_simp
  ring

lemma physicalCollarEta_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarEta R f (slice (Real.exp ρ) a) =
      (1/Real.exp ρ^2) • fieldEta (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarEta, slice_zero, radiusLogPoint_slice, Real.log_exp]
  rw [← collarEta_slice, smul_smul]
  congr 1
  field_simp

lemma physicalCollarRawTau_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarRawTau R f (slice (Real.exp ρ) a) =
      ((1-roundingWeight R (Real.exp ρ))/Real.exp ρ) • (f.angular ρ).tau a := by
  simp [physicalCollarRawTau,LogCollarData.angular,smul_smul]
  congr 1
  field_simp

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarGamma_radial (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (i j : Fin 2) :
    D (CKSRealizedRound.basis 0) (fun y => physicalCollarGamma R f y i j)
      (slice (Real.exp ρ) a) =
      2*Real.exp ρ*fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a i j+
        (1/Real.exp ρ^2)*fieldQr (collarParams R (Real.exp ρ)) (f.angular ρ) a i j := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hq : ContDiffAt ℝ 3 (fun y => collarQ R f y i j) (slice ρ a) :=
    contDiffAt_pi.mp (contDiffAt_pi.mp (collarQ_regularAt R hf) i) j
  have hq' : DifferentiableAt ℝ (fun y => collarQ R f y i j)
      (radiusLogPoint (slice (Real.exp ρ) a)) := by
    simpa using hq.differentiableAt (by norm_num)
  have hrad : DifferentiableAt ℝ (fun y : PhysicalPoint => y 0) (slice (Real.exp ρ) a) := by fun_prop
  change D _ (fun y => (y 0)^2*collarQ R f (radiusLogPoint y) i j) _ = _
  erw [D_mul _ (hrad.pow 2) (hq'.comp _ (radiusLogPoint_hasFDerivAt hr).differentiableAt),
    D_pow _ 2 hrad, D_radiusLogPoint 0 hr hq']
  have hder : D (CKSRealizedRound.basis 0) (fun y : PhysicalPoint => y 0)
      (slice (Real.exp ρ) a) = 1 := by
    exact CKSRealizedRound.D_coord 0 0 _
  simp only [ite_true, Pi.pow_apply, Function.comp_apply,
    radiusLogPoint_slice, Real.log_exp, slice_zero,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, hder, mul_one, collarQ_slice]
  rw [← collarQ_radial R ρ hf hσ i j]
  simp only [CKSRealizedRound.basis, CKSMixedGeometry.basis]
  field_simp
  ring

lemma physicalCollarGamma_angular (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a)) (b i j : Fin 2) :
    D (CKSRealizedRound.basis b.succ) (fun y => physicalCollarGamma R f y i j)
      (slice (Real.exp ρ) a) =
      Real.exp ρ^2*D (basis b)
        (fun y => fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) y i j) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.RegularAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hg := physicalCollarGamma_regularAt R hr hf'
  erw [← D_slice b (Real.exp ρ) ((contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j).differentiableAt (by norm_num))]
  have he : (fun y => physicalCollarGamma R f (slice (Real.exp ρ) y) i j) =
      fun y => Real.exp ρ^2*fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) y i j := by
    funext y
    rw [physicalCollarGamma_slice]
    rfl
  rw [he]
  have hqa : ContDiffAt ℝ 3 (fun y => fieldQ (collarParams R (Real.exp ρ))
      (f.angular ρ) y i j) a := by
    have hh := (contDiffAt_pi.mp (contDiffAt_pi.mp (collarQ_regularAt R hf) i) j).comp a
      ((slice_smooth ρ).contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))
    simpa only [Function.comp_def,collarQ_slice] using hh
  exact D_const_mul _ _ (hqa.differentiableAt (by norm_num))

lemma physicalCollarShift_angular (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a)) (b i : Fin 2) :
    D (CKSRealizedRound.basis b.succ) (fun y => physicalCollarShift R f y i)
      (slice (Real.exp ρ) a) =
      (1/Real.exp ρ^5)*D (basis b)
        (fun y => fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) y i) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.RegularAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hs := physicalCollarShift_regularAt R hr hf'
  erw [← D_slice b (Real.exp ρ) ((contDiffAt_pi.mp hs i).differentiableAt (by norm_num))]
  have he : (fun y => physicalCollarShift R f (slice (Real.exp ρ) y) i) =
      fun y => (1/Real.exp ρ^5)*fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) y i := by
    funext y
    rw [physicalCollarShift_slice]
    rfl
  rw [he]
  have hsa : ContDiffAt ℝ 3 (fun y => fieldS (collarParams R (Real.exp ρ))
      (f.angular ρ) y i) a := by
    have hh := ((contDiffAt_pi.mp (collarShift_regularAt R hf) i).comp a
      ((slice_smooth ρ).contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))).const_smul
        (Real.exp ρ^5)
    have heS : (fun y => fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) y i) =
        fun y => Real.exp ρ^5*collarShift R f (slice ρ y) i := by
      funext y
      rw [← collarShift_slice]
      rfl
    rw [heS]
    exact hh
  exact D_const_mul _ _ (hsa.differentiableAt (by norm_num))

lemma physicalCollarRadialRate (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0) :
    leafRadialRate (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a) =
      (2*Real.exp ρ) • fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a+
        (1/Real.exp ρ^2) • fieldC (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  ext i j
  simp only [leafRadialRate, physicalCollarGamma_radial R ρ hf hσ,
    physicalCollarGamma_angular R ρ hf, physicalCollarShift_angular R ρ hf,
    physicalCollarGamma_slice,physicalCollarShift_slice,
    Matrix.add_apply,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
  simp only [fieldC,normalizedLie,collarParams,Matrix.cons_val_zero,
    Fin.sum_univ_two]
  field_simp
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafTensorTrace_eq (γ T : Mat) :
    leafTensorTrace γ T = ∑ i, ∑ j, inverse γ i j*T j i := by
  simp only [leafTensorTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, inverse_eq]

lemma leafTensorTrace_metric_smul (γ T : Mat) {c : ℝ} (hc : c ≠ 0) :
    leafTensorTrace (c • γ) T = leafTensorTrace γ T/c := by
  simp only [leafTensorTrace_eq, inverse_smul c γ hc]
  simp only [Fin.sum_univ_two]
  ring

lemma leafTensorTraceFree_add (γ A B : Mat) :
    leafTensorTraceFree γ (A+B) = leafTensorTraceFree γ A+leafTensorTraceFree γ B := by
  unfold leafTensorTraceFree
  rw [leafTensorTrace_add]
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma leafTensorTraceFree_smul (γ A : Mat) (c : ℝ) :
    leafTensorTraceFree γ (c • A) = c • leafTensorTraceFree γ A := by
  unfold leafTensorTraceFree
  rw [leafTensorTrace_smul]
  ext i j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma leafTensorTraceFree_self {γ : Mat} (hp : γ.PosDef) :
    leafTensorTraceFree γ γ = 0 := by
  rw [leafTensorTraceFree,leafTensorTrace_self hp]
  norm_num

lemma leafTensorTraceFree_metric_smul (γ T : Mat) {c : ℝ} (hc : c ≠ 0) :
    leafTensorTraceFree (c • γ) T = leafTensorTraceFree γ T := by
  unfold leafTensorTraceFree
  rw [leafTensorTrace_metric_smul γ T hc]
  ext i j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp

lemma traceFreeField_eq (q t : Point → Mat) (y : Point) :
    traceFreeField q t y = leafTensorTraceFree (q y) (t y) := by
  ext i j
  simp only [traceFreeField,leafTensorTraceFree,leafTensorTrace_eq,
    Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma physicalCollarGamma_pos_iff (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef ↔
      (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a).PosDef := by
  rw [physicalCollarGamma_slice]
  constructor
  · intro hp
    have h := hp.smul (show 0 < 1/Real.exp ρ^2 by positivity)
    simpa only [smul_smul,one_div_mul_cancel (by positivity : Real.exp ρ^2 ≠ 0),one_smul] using h
  · intro hp
    exact hp.smul (by positivity)

lemma physicalCollarExpansion_slice (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef) :
    radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a) =
      lapseDField (1/Real.exp ρ) (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hq := (physicalCollarGamma_pos_iff R ρ f a).mp hp
  rw [radialExpansion, physicalCollarRadialRate R ρ hf hσ, physicalCollarGamma_slice,
    leafTensorTrace_metric_smul _ _ (by positivity : Real.exp ρ^2 ≠ 0),
    leafTensorTrace_add,leafTensorTrace_smul,leafTensorTrace_smul,leafTensorTrace_self hq]
  simp only [slice_zero,lapseDField,fieldD,leafTensorTrace_eq]
  field_simp
  ring

lemma physicalCollarShear_unscaled (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef) :
    leafTensorTraceFree (physicalCollarGamma R f (slice (Real.exp ρ) a))
      (sourceChi (physicalCollarU R f) (physicalCollarGamma R f) (physicalCollarShift R f)
        (slice (Real.exp ρ) a)) =
      (physicalCollarU R f (slice (Real.exp ρ) a)/(2*Real.exp ρ^2)) •
        leafTensorTraceFree (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a)
          (fieldC (collarParams R (Real.exp ρ)) (f.angular ρ) a) := by
  have hq := (physicalCollarGamma_pos_iff R ρ f a).mp hp
  rw [sourceChi_radialRate,physicalCollarRadialRate R ρ hf hσ,physicalCollarGamma_slice,
    leafTensorTraceFree_metric_smul _ _ (by positivity : Real.exp ρ^2 ≠ 0),
    leafTensorTraceFree_smul,leafTensorTraceFree_add,leafTensorTraceFree_smul,
    leafTensorTraceFree_smul,leafTensorTraceFree_self hq,smul_zero,zero_add,smul_smul]
  congr 1
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafRadialRate_smoothAt {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {x : PhysicalPoint} (hγ : ContDiffAt ℝ ∞ γ x) (hs : ContDiffAt ℝ ∞ s x) :
    ContDiffAt ℝ ∞ (leafRadialRate γ s) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have hsc (i) : ContDiffAt ℝ ∞ (fun y => s y i) x := contDiffAt_pi.mp hs i
  have hd (k : Fin 3) (i j) : ContDiffAt ℝ ∞
      (D (CKSRealizedRound.basis k) (fun y => γ y i j)) x :=
    contDiffAt_D (hc i j) (by simp) _
  have hsd (k : Fin 3) (i) : ContDiffAt ℝ ∞
      (D (CKSRealizedRound.basis k) (fun y => s y i)) x :=
    contDiffAt_D (hsc i) (by simp) _
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [leafRadialRate,Fin.sum_univ_two]
  fun_prop

lemma radialExpansion_smoothAt {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {x : PhysicalPoint} (hγ : ContDiffAt ℝ ∞ γ x) (hs : ContDiffAt ℝ ∞ s x)
    (hp : (γ x).PosDef) : ContDiffAt ℝ ∞ (radialExpansion γ s) x := by
  unfold radialExpansion
  exact ((show ContDiffAt ℝ ∞ (fun y : PhysicalPoint => y 0) x by fun_prop).div_const 4).mul
    (leafTensorTrace_contDiffAt hγ (leafRadialRate_smoothAt hγ hs) hp)

lemma radialMassRadical_smoothAt {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (ht : ContDiffAt ℝ ∞ t x) (hF : ContDiffAt ℝ ∞ F x) (hr : x 0 ≠ 0) :
    ContDiffAt ℝ ∞ (radialMassRadical t F) x := by
  have hrad : ContDiffAt ℝ ∞ (fun y : PhysicalPoint => y 0) x := by fun_prop
  exact (contDiffAt_const.add ((hrad.mul ht).pow 2)).sub
    ((contDiffAt_const.mul hF).div hrad hr)

lemma radialMassLapse_smoothAt {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ ∞ γ x) (hs : ContDiffAt ℝ ∞ s x)
    (ht : ContDiffAt ℝ ∞ t x) (hF : ContDiffAt ℝ ∞ F x)
    (hr : x 0 ≠ 0) (hp : (γ x).PosDef)
    (hd : radialExpansion γ s x ≠ 0) (hu : radialMassRadical t F x ≠ 0) :
    ContDiffAt ℝ ∞ (radialMassLapse γ s t F) x :=
  ((radialMassRadical_smoothAt ht hF hr).sqrt hu).div
    (radialExpansion_smoothAt hγ hs hp) hd

lemma radialTangential_smoothAt {γ τ : PhysicalPoint → Mat} {t : PhysicalPoint → ℝ}
    {x : PhysicalPoint} (hγ : ContDiffAt ℝ ∞ γ x) (hτ : ContDiffAt ℝ ∞ τ x)
    (ht : ContDiffAt ℝ ∞ t x) (hp : (γ x).PosDef) :
    ContDiffAt ℝ ∞ (radialTangential γ t τ) x :=
  (ht.smul hγ).add (leafTensorTraceFree_contDiffAt hγ hτ hp)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma lapseNormalizedField_rad (z : ℝ) (T F d : Point → ℝ) (a : Point) :
    lapseNormalizedField z T F d a =
      Real.sqrt (lapseRadField z T F a)/lapseDField z d a := by
  unfold lapseNormalizedField lapseRadField lapseVField lapseDField
  congr 2
  have h : 1+z^2 ≠ 0 := by positivity
  field_simp
  ring

lemma physicalCollarRadical_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a) =
      (1+Real.exp ρ^2)*lapseRadField (1/Real.exp ρ)
        (fieldT (collarParams R (Real.exp ρ)) (f.angular ρ))
        (fieldF (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  rw [radialMassRadical,physicalCollarT_slice,physicalCollarF_slice,slice_zero,
    lapse_radical_reconstruction (Real.exp_pos ρ)]
  unfold lapseRadField lapseVField
  congr 2
  ring

lemma physicalCollarRadical_pos_iff (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a) ↔
      0 < lapseRadField (1/Real.exp ρ)
        (fieldT (collarParams R (Real.exp ρ)) (f.angular ρ))
        (fieldF (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  rw [physicalCollarRadical_slice,mul_pos_iff_of_pos_left (by positivity : 0 < 1+Real.exp ρ^2)]

lemma physicalCollarU_slice (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef) :
    physicalCollarU R f (slice (Real.exp ρ) a) = physicalBaseLapse (Real.exp ρ)*
      fieldNormalizedLapse (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  rw [physicalCollarU,radialMassLapse,physicalCollarRadical_slice,
    physicalCollarExpansion_slice R ρ hf hσ hp,
    Real.sqrt_mul (by positivity : 0 ≤ 1+Real.exp ρ^2),
    physicalBaseLapse_eq (Real.exp_pos ρ)]
  unfold fieldNormalizedLapse
  rw [lapseNormalizedField_rad]
  simp only [collarParams,Matrix.cons_val_zero]
  ring

lemma physicalCollarU_coefficient (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f)
      (slice (Real.exp ρ) a))
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f)
      (slice (Real.exp ρ) a)) :
    physicalCollarU R f (slice (Real.exp ρ) a) = physicalBaseLapse (Real.exp ρ)*
      (1+(1/Real.exp ρ)^3*fieldA (collarParams R (Real.exp ρ)) (f.angular ρ) a) := by
  rw [physicalCollarU_slice R ρ hf hσ hp]
  apply congrArg (physicalBaseLapse (Real.exp ρ) * ·)
  apply lapseAField_identity
  · exact (physicalCollarRadical_pos_iff R ρ f a).mp hu
  · change lapseDField (1/Real.exp ρ) (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a ≠ 0
    rw [← physicalCollarExpansion_slice R ρ hf hσ hp]
    exact hd.ne'

lemma radialTangential_traceFree {γ : Mat} (hp : γ.PosDef) (τ : Mat) (t : ℝ) :
    leafTensorTraceFree γ (t • γ+leafTensorTraceFree γ τ) = leafTensorTraceFree γ τ := by
  unfold leafTensorTraceFree
  rw [leafTensorTrace_add,leafTensorTrace_smul,leafTensorTrace_self hp,
    ← leafTensorTraceFree,leafTensorTrace_traceFree hp]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma physicalCollarTau_slice (R ρ : ℝ) (f : LogCollarData) {a : Point}
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef) :
    leafTensorTraceFree (physicalCollarGamma R f (slice (Real.exp ρ) a))
      (physicalCollarTangential R f (slice (Real.exp ρ) a)) =
      (1/Real.exp ρ) • fieldTau (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  rw [physicalCollarTangential,radialTangential,radialTangential_traceFree hp,
    physicalCollarGamma_slice,physicalCollarRawTau_slice,
    leafTensorTraceFree_metric_smul _ _ (by positivity : Real.exp ρ^2 ≠ 0),
    leafTensorTraceFree_smul]
  rw [fieldTau,traceFreeField_eq,smul_smul]
  congr 1
  change (1-roundingWeight R (Real.exp ρ))/Real.exp ρ = 1/Real.exp ρ*(1-roundingWeight R (Real.exp ρ))
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Filter CKSBending Set
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma collarT_regularAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.RegularAt y) :
    ContDiffAt ℝ 2 (collarT R f) y :=
  contDiffAt_const.add ((contDiffAt_const.sub ((collarWeight_smoothAt R y).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).mul hf.tError)

lemma collarF_regularAt {R : ℝ} (hR : 0 < R) {f : LogCollarData} {y : MP} (hf : f.RegularAt y) :
    ContDiffAt ℝ 2 (collarF R f) y :=
  (hf.fstar.add ((contDiffAt_const.sub ((collarWeight_smoothAt R y).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).mul hf.massError)).add
    ((radialLift_smoothAt ((paddingMass_smooth hR).contDiffAt
      (isOpen_Ioi.mem_nhds (Real.exp_pos (y 0))))).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))

lemma collarEta_regularAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.RegularAt y) :
    ContDiffAt ℝ 2 (collarEtaDivR R f) y :=
  (contDiffAt_const.sub ((collarWeight_smoothAt R y).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).smul hf.etaDivR

end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarT_radial (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a)) :
    D (CKSRealizedRound.basis 0) (physicalCollarT R f) (slice (Real.exp ρ) a) =
      (1/Real.exp ρ^4)*fieldTr (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have ht : DifferentiableAt ℝ (collarT R f) (radiusLogPoint (slice (Real.exp ρ) a)) := by
    simpa using (collarT_regularAt R hf).differentiableAt (by norm_num)
  unfold physicalCollarT
  rw [D_radiusLogPoint 0 hr ht]
  simp only [ite_true,slice_zero,radiusLogPoint_slice,Real.log_exp]
  rw [← collarT_radial R ρ hf]
  simp only [CKSRealizedRound.basis,CKSMixedGeometry.basis]
  field_simp

lemma physicalCollarEta_radial (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a)) (i : Fin 2) :
    D (CKSRealizedRound.basis 0) (fun y => physicalCollarEta R f y i) (slice (Real.exp ρ) a) =
      (1/Real.exp ρ^3)*fieldEr (collarParams R (Real.exp ρ)) (f.angular ρ) a i := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have he : DifferentiableAt ℝ (fun y => collarEtaDivR R f y i)
      (radiusLogPoint (slice (Real.exp ρ) a)) := by
    simpa using (contDiffAt_pi.mp (collarEta_regularAt R hf) i).differentiableAt (by norm_num)
  have hrad : DifferentiableAt ℝ (fun y : PhysicalPoint => y 0) (slice (Real.exp ρ) a) := by fun_prop
  change D _ (fun y => y 0*collarEtaDivR R f (radiusLogPoint y) i) _ = _
  erw [D_mul _ hrad (he.comp _ (radiusLogPoint_hasFDerivAt hr).differentiableAt),
    D_radiusLogPoint 0 hr he]
  have hder : D (CKSRealizedRound.basis 0) (fun y : PhysicalPoint => y 0)
      (slice (Real.exp ρ) a) = 1 := CKSRealizedRound.D_coord 0 0 _
  simp only [ite_true,slice_zero,radiusLogPoint_slice,Real.log_exp,Function.comp_apply,hder,mul_one]
  rw [← collarEta_radial R ρ hf i]
  simp only [CKSRealizedRound.basis,CKSMixedGeometry.basis]
  field_simp
  ring

lemma physicalCollarF_radial {R : ℝ} (hR : 0 < R) (ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hstar : D (CKSRealizedRound.basis 0) f.fstar (slice ρ a)=0) :
    D (CKSRealizedRound.basis 0) (physicalCollarF R f) (slice (Real.exp ρ) a) =
      paddingWeight R (Real.exp ρ)/(Real.exp ρ*Real.sqrt (Real.exp ρ))+
      (1/Real.exp ρ^2)*((1-roundingWeight R (Real.exp ρ))*(f.angular ρ).massRadial a-
        (Real.exp ρ*deriv (roundingWeight R) (Real.exp ρ))*(f.angular ρ).massGap a) := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have ht : DifferentiableAt ℝ (collarF R f) (radiusLogPoint (slice (Real.exp ρ) a)) := by
    simpa using (collarF_regularAt hR hf).differentiableAt (by norm_num)
  unfold physicalCollarF
  rw [D_radiusLogPoint 0 hr ht]
  simp only [ite_true,slice_zero,radiusLogPoint_slice,Real.log_exp]
  change (Real.exp ρ)⁻¹*D (CKSMixedGeometry.basis 0) (collarF R f) (slice ρ a) = _
  rw [collarF_radial hR ρ hf hstar]
  rw [← paddingDensity_rpow (Real.exp_pos ρ)]
  unfold paddingDensity
  field_simp
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalAngularScalarJet_congr {f g : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (h : f =ᶠ[𝓝 x] g) : physicalAngularScalarJet f x = physicalAngularScalarJet g x := by
  apply Prod.ext
  · exact h.self_of_nhds
  apply Prod.ext
  · ext a
    exact D_congr h (CKSRealizedRound.basis a.succ)
  · ext a b
    have hd : D (CKSRealizedRound.basis b.succ) f =ᶠ[𝓝 x] D (CKSRealizedRound.basis b.succ) g := by
      filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
      exact congrArg (fun L : PhysicalPoint →L[ℝ] ℝ => L (CKSRealizedRound.basis b.succ)) hy
    exact D_congr hd (CKSRealizedRound.basis a.succ)

lemma D_eventually_congr {f g : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (h : f =ᶠ[𝓝 x] g) (v : PhysicalPoint) : D v f =ᶠ[𝓝 x] D v g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : PhysicalPoint →L[ℝ] ℝ => L v) hy

lemma radial_positive_eventually {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ ∞ γ x) (hs : ContDiffAt ℝ ∞ s x)
    (ht : ContDiffAt ℝ ∞ t x) (hF : ContDiffAt ℝ ∞ F x)
    (hr : 0 < x 0) (hp : (γ x).PosDef)
    (hd : 0 < radialExpansion γ s x) (hu : 0 < radialMassRadical t F x) :
    (∀ᶠ y in 𝓝 x, 0 < radialExpansion γ s y) ∧
      (∀ᶠ y in 𝓝 x, 0 < radialMassRadical t F y) := by
  exact ⟨(radialExpansion_smoothAt hγ hs hp).continuousAt.eventually (eventually_gt_nhds hd),
    (radialMassRadical_smoothAt ht hF hr.ne').continuousAt.eventually (eventually_gt_nhds hu)⟩

lemma radial_reconstruction_eventually {γ τ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ ∞ γ x) (hs : ContDiffAt ℝ ∞ s x)
    (ht : ContDiffAt ℝ ∞ t x) (hF : ContDiffAt ℝ ∞ F x)
    (hr : 0 < x 0) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hd : 0 < radialExpansion γ s x) (hu : 0 < radialMassRadical t F x) :
    (sourceMass (radialMassLapse γ s t F) γ (radialTangential γ t τ) s =ᶠ[𝓝 x] F) ∧
    (sourceD (radialMassLapse γ s t F) γ s =ᶠ[𝓝 x] radialExpansion γ s) ∧
    ((fun y => sourceP γ (radialTangential γ t τ) y/2) =ᶠ[𝓝 x] t) := by
  obtain ⟨hd',hu'⟩ := radial_positive_eventually hγ hs ht hF hr hp.self_of_nhds hd hu
  have hr' : ∀ᶠ y in 𝓝 x, 0 < y 0 :=
    (ContinuousLinearMap.proj 0 : PhysicalPoint →L[ℝ] ℝ).continuous.continuousAt.eventually (eventually_gt_nhds hr)
  have he : ∀ᶠ y in 𝓝 x,
      sourceMass (radialMassLapse γ s t F) γ (radialTangential γ t τ) s y = F y ∧
      sourceD (radialMassLapse γ s t F) γ s y = radialExpansion γ s y ∧
      sourceP γ (radialTangential γ t τ) y/2 = t y := by
    filter_upwards [hp,hd',hu',hr'] with y hyp hyd hyu hyr
    have h := physical_radial_reconstruction γ τ s t F y hyr hyp hyd hyu
    exact ⟨h.2.2.2.2,h.2.1,by rw [h.2.2.2.1]; ring⟩
  exact ⟨he.mono (fun _ h => h.1),he.mono (fun _ h => h.2.1),he.mono (fun _ h => h.2.2)⟩

lemma physicalCollar_positive_eventually {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hR : 0 < R) (hf : f.SmoothAt (slice ρ a))
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a))
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a)) :
    (∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) y) ∧
    (∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) y) := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  exact radial_positive_eventually (physicalCollarGamma_smoothAt R hr hf')
    (physicalCollarShift_smoothAt R hr hf') (physicalCollarT_smoothAt R hr hf')
    (physicalCollarF_smoothAt hR hr hf') (by simpa using Real.exp_pos ρ) hp hd hu

lemma physicalCollar_reconstruction_eventually {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hR : 0 < R) (hf : f.SmoothAt (slice ρ a))
    (hp : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a))
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a)) :
    (sourceMass (physicalCollarU R f) (physicalCollarGamma R f) (physicalCollarTangential R f)
      (physicalCollarShift R f) =ᶠ[𝓝 (slice (Real.exp ρ) a)] physicalCollarF R f) ∧
    (sourceD (physicalCollarU R f) (physicalCollarGamma R f) (physicalCollarShift R f) =ᶠ[𝓝 (slice (Real.exp ρ) a)]
      radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f)) ∧
    ((fun y => sourceP (physicalCollarGamma R f) (physicalCollarTangential R f) y/2) =ᶠ[𝓝 (slice (Real.exp ρ) a)] physicalCollarT R f) := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  exact radial_reconstruction_eventually (physicalCollarGamma_smoothAt R hr hf')
    (physicalCollarShift_smoothAt R hr hf') (physicalCollarT_smoothAt R hr hf')
    (physicalCollarF_smoothAt hR hr hf') (by simpa using Real.exp_pos ρ) hp hd hu

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma rescale_eq_smul (c : ℝ) (q : Jet) : rescale c q = c • q := rfl

lemma radius_inverse_smul_cancel {r : ℝ} (hr : r ≠ 0) (n : ℕ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    r^n • ((1/r)^n • v) = v := by
  rw [smul_smul,← mul_pow,mul_one_div_cancel hr,one_pow,one_smul]

lemma actualScalarJet_affine {g : Point → ℝ} {a : Point} (hg : ContDiffAt ℝ 2 g a) (c d : ℝ) :
    actualScalarJet (fun y => c+d*g y) a = constantJet c+d • actualScalarJet g a := by
  erw [actualScalarJet_add contDiffAt_const (hg.const_smul d),actualScalarJet_const,
    actualScalarJet_smul d hg]

lemma physicalAngularScalarJet_affine {f : PhysicalPoint → ℝ} {g : Point → ℝ} {r : ℝ} {a : Point}
    (hf : ContDiffAt ℝ 2 f (slice r a)) (hg : ContDiffAt ℝ 2 g a) (c d : ℝ)
    (he : (fun y => f (slice r y)) =ᶠ[𝓝 a] (fun y => c+d*g y)) :
    physicalAngularScalarJet f (slice r a) = constantJet c+d • actualScalarJet g a := by
  rw [physicalAngularScalarJet_slice hf,actualScalarJet_congr he,actualScalarJet_affine hg]

lemma physicalCollarGamma_jet (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    rescale (1/Real.exp ρ^2) (physicalAngularJet (physicalCollarGamma R f) (slice (Real.exp ρ) a)) =
      actualJet (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hg := (physicalCollarGamma_smoothAt R hr hf').of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [physicalAngularJet_slice hg]
  have he : (fun y => physicalCollarGamma R f (slice (Real.exp ρ) y)) =
      fun y => Real.exp ρ^2 • fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) y := by
    funext y
    exact physicalCollarGamma_slice R ρ f y
  have hqa := (fieldQ_diff (collarParams R (Real.exp ρ))
    (angular_regular hf.regularAt (hf.tError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)))).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  rw [he,actualJet_smul _ hqa,rescale_eq_smul,smul_smul]
  simp

lemma physicalCollarT_jet (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    Real.exp ρ^3 • (physicalAngularScalarJet (physicalCollarT R f) (slice (Real.exp ρ) a)-constantJet 1) =
      actualScalarJet (fieldT (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have ht := (physicalCollarT_smoothAt R hr hf').of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hta := fieldT_diff (collarParams R (Real.exp ρ))
    (angular_regular hf.regularAt (hf.tError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)))
  rw [physicalAngularScalarJet_affine ht hta 1 ((1/Real.exp ρ)^3)
    (Filter.Eventually.of_forall (physicalCollarT_slice R ρ f))]
  rw [add_sub_cancel_left,radius_inverse_smul_cancel (Real.exp_ne_zero ρ)]

lemma physicalCollarL_jet (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    Real.exp ρ^3 • (physicalAngularScalarJet (physicalCollarL R f) (slice (Real.exp ρ) a)-
      constantJet (1+paddingWeight R (Real.exp ρ)/Real.exp ρ^2)) =
      actualScalarJet (fieldL (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hl := (physicalCollarL_smoothAt R hr hf').of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hla := fieldL_diff (collarParams R (Real.exp ρ))
    (angular_regular hf.regularAt (hf.tError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)))
  rw [physicalAngularScalarJet_affine hl hla _ ((1/Real.exp ρ)^3)
    (Filter.Eventually.of_forall (physicalCollarL_slice R ρ f))]
  rw [add_sub_cancel_left,radius_inverse_smul_cancel (Real.exp_ne_zero ρ)]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSAngularGeometry
open scoped Topology ContDiff
lemma LogCollarData.SmoothAt.angular_regular {f : LogCollarData} {ρ : ℝ} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) : (f.angular ρ).RegularAt a :=
  CKSAngularSlice.angular_regular hf.regularAt (hf.tError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))
end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalAngularScalarJet_scaled {f : PhysicalPoint → ℝ} {g : Point → ℝ} {r : ℝ} {a : Point}
    (hf : ContDiffAt ℝ 2 f (slice r a)) (hg : ContDiffAt ℝ 2 g a) (c : ℝ)
    (he : (fun y => f (slice r y)) =ᶠ[𝓝 a] (fun y => c*g y)) :
    physicalAngularScalarJet f (slice r a) = c • actualScalarJet g a := by
  rw [physicalAngularScalarJet_slice hf,actualScalarJet_congr he]
  exact actualScalarJet_smul c hg

lemma physicalCollarShift_jets (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    Real.exp ρ^5 • (fun i => physicalAngularScalarJet (fun y => physicalCollarShift R f y i)
      (slice (Real.exp ρ) a)) =
        fun i => actualScalarJet (fun y => fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) y i) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hs := (physicalCollarShift_smoothAt R hr hf').of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsa := (fieldS_diff (collarParams R (Real.exp ρ)) hf.angular_regular).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  funext i
  change Real.exp ρ^5 • physicalAngularScalarJet _ _ = _
  rw [physicalAngularScalarJet_scaled (contDiffAt_pi.mp hs i) (contDiffAt_pi.mp hsa i)
    (1/Real.exp ρ^5) (Filter.Eventually.of_forall (fun y => congrFun (physicalCollarShift_slice R ρ f y) i)),smul_smul]
  simp

lemma physicalCollarEta_jets (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    Real.exp ρ^2 • (fun i => physicalAngularScalarJet (fun y => physicalCollarEta R f y i)
      (slice (Real.exp ρ) a)) =
        fun i => actualScalarJet (fun y => fieldEta (collarParams R (Real.exp ρ)) (f.angular ρ) y i) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hs := (physicalCollarEta_smoothAt R hr hf').of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsa : ContDiffAt ℝ 2 (fieldEta (collarParams R (Real.exp ρ)) (f.angular ρ)) a :=
    hf.angular_regular.2.2.2.1.const_smul _
  funext i
  change Real.exp ρ^2 • physicalAngularScalarJet _ _ = _
  rw [physicalAngularScalarJet_scaled (contDiffAt_pi.mp hs i) (contDiffAt_pi.mp hsa i)
    (1/Real.exp ρ^2) (Filter.Eventually.of_forall (fun y => congrFun (physicalCollarEta_slice R ρ f y) i)),smul_smul]
  simp

lemma physicalCollarEta_radial_scaled (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a)) :
    Real.exp ρ^3 • (fun i => D (CKSRealizedRound.basis 0) (fun y => physicalCollarEta R f y i)
      (slice (Real.exp ρ) a)) = fieldEr (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  funext i
  change Real.exp ρ^3 * D _ _ _ = _
  rw [physicalCollarEta_radial R ρ hf i]
  field_simp

lemma physicalCollarF_jet {R : ℝ} (hR : 0 < R) (ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    physicalAngularScalarJet (physicalCollarF R f) (slice (Real.exp ρ) a) =
      actualScalarJet (fieldF (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  rw [physicalAngularScalarJet_slice ((physicalCollarF_smoothAt hR hr hf').of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  congr 1
  funext y
  exact physicalCollarF_slice R ρ f y

lemma physicalCollarTr_jet (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    Real.exp ρ^4 • physicalAngularScalarJet
      (D (CKSRealizedRound.basis 0) (physicalCollarT R f)) (slice (Real.exp ρ) a) =
      actualScalarJet (fieldTr (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have ht : ContDiffAt ℝ 2 (D (CKSRealizedRound.basis 0) (physicalCollarT R f)) (slice (Real.exp ρ) a) :=
    (contDiffAt_D (physicalCollarT_smoothAt R hr hf') (by simp) _).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he : (fun y => D (CKSRealizedRound.basis 0) (physicalCollarT R f) (slice (Real.exp ρ) y))
      =ᶠ[𝓝 a] fun y => (1/Real.exp ρ^4)*fieldTr (collarParams R (Real.exp ρ)) (f.angular ρ) y := by
    filter_upwards [(slice_smooth ρ).continuous.continuousAt.tendsto.eventually hf.eventually_regularAt] with y hy
    exact physicalCollarT_radial R ρ hy
  rw [physicalAngularScalarJet_scaled ht (fieldTr_diff _ hf.angular_regular) _ he,smul_smul]
  simp

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarU_smoothAt {R : ℝ} (hR : 0 < R) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x))
    (hp : (physicalCollarGamma R f x).PosDef)
    (hd : radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) x ≠ 0)
    (hu : radialMassRadical (physicalCollarT R f) (physicalCollarF R f) x ≠ 0) :
    ContDiffAt ℝ ∞ (physicalCollarU R f) x :=
  radialMassLapse_smoothAt (physicalCollarGamma_smoothAt R hr hf)
    (physicalCollarShift_smoothAt R hr hf) (physicalCollarT_smoothAt R hr hf)
    (physicalCollarF_smoothAt hR hr hf) hr hp hd hu

lemma physicalCollarTangential_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x))
    (hp : (physicalCollarGamma R f x).PosDef) :
    ContDiffAt ℝ ∞ (physicalCollarTangential R f) x :=
  radialTangential_smoothAt (physicalCollarGamma_smoothAt R hr hf)
    (physicalCollarRawTau_smoothAt R hr hf) (physicalCollarT_smoothAt R hr hf) hp

lemma physicalCollarU_jet {R : ℝ} (hR : 0 < R) (ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a))
    (hσ : ∀ᶠ y in 𝓝 (slice ρ a), ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) y=0)
    (hp : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a))
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a)) :
    Real.exp ρ^3 • ((1/physicalBaseLapse (Real.exp ρ)) •
      physicalAngularScalarJet (physicalCollarU R f) (slice (Real.exp ρ) a)-constantJet 1) =
      actualScalarJet (fieldA (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hU := (physicalCollarU_smoothAt hR hr hf' hp.self_of_nhds hd.ne' hu.ne').of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hq := (physicalCollarGamma_pos_iff R ρ f a).mp hp.self_of_nhds
  have hq0 : determinant (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  have hrad := (physicalCollarRadical_pos_iff R ρ f a).mp hu
  have hdf : lapseDField (1/Real.exp ρ) (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a ≠ 0 := by
    rw [← physicalCollarExpansion_slice R ρ hf.regularAt hσ.self_of_nhds hp.self_of_nhds]
    exact hd.ne'
  have hA : ContDiffAt ℝ 2 (fieldA (collarParams R (Real.exp ρ)) (f.angular ρ)) a :=
    lapseAField_diff _ (fieldT_diff _ hf.angular_regular) (fieldF_diff _ hf.angular_regular)
      (fieldD_diff _ hf.angular_regular hq0) hrad hdf
  obtain ⟨hde,hue⟩ := physicalCollar_positive_eventually hR hf hp.self_of_nhds hd hu
  have he : (fun y => physicalCollarU R f (slice (Real.exp ρ) y)) =ᶠ[𝓝 a]
      fun y => physicalBaseLapse (Real.exp ρ)*(1+(1/Real.exp ρ)^3*fieldA (collarParams R (Real.exp ρ)) (f.angular ρ) y) := by
    filter_upwards [(slice_smooth ρ).continuous.continuousAt.tendsto.eventually hf.eventually_regularAt,
      (slice_smooth ρ).continuous.continuousAt.tendsto.eventually hσ,
      (slice_smooth (Real.exp ρ)).continuous.continuousAt.tendsto.eventually hp,
      (slice_smooth (Real.exp ρ)).continuous.continuousAt.tendsto.eventually hde,
      (slice_smooth (Real.exp ρ)).continuous.continuousAt.tendsto.eventually hue] with y hy hyσ hyp hyd hyu
    exact physicalCollarU_coefficient R ρ hy hyσ hyp hyd hyu
  rw [physicalAngularScalarJet_slice hU,actualScalarJet_congr he]
  have haf : ContDiffAt ℝ 2 (fun y => (1:ℝ)+(1/Real.exp ρ)^3*fieldA (collarParams R (Real.exp ρ)) (f.angular ρ) y) a :=
    contDiffAt_const.add (contDiffAt_const.mul hA)
  rw [actualScalarJet_smul (physicalBaseLapse (Real.exp ρ)) haf,
    actualScalarJet_affine hA 1 ((1/Real.exp ρ)^3),smul_smul]
  have hb : physicalBaseLapse (Real.exp ρ) ≠ 0 := by unfold physicalBaseLapse; positivity
  rw [one_div_mul_cancel hb,one_smul,add_sub_cancel_left,radius_inverse_smul_cancel (Real.exp_ne_zero ρ)]

lemma physicalCollarExpansion_jet (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a))
    (hσ : ∀ᶠ y in 𝓝 (slice ρ a), ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) y=0)
    (hp : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef) :
    Real.exp ρ^3 • (physicalAngularScalarJet
      (radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f))
      (slice (Real.exp ρ) a)-constantJet 1) =
        actualScalarJet (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hD := (radialExpansion_smoothAt (physicalCollarGamma_smoothAt R hr hf')
    (physicalCollarShift_smoothAt R hr hf') hp.self_of_nhds).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hq := (physicalCollarGamma_pos_iff R ρ f a).mp hp.self_of_nhds
  have hq0 : determinant (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  have he : (fun y => radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f)
      (slice (Real.exp ρ) y)) =ᶠ[𝓝 a]
      fun y => 1+(1/Real.exp ρ)^3*fieldD (collarParams R (Real.exp ρ)) (f.angular ρ) y := by
    filter_upwards [(slice_smooth ρ).continuous.continuousAt.tendsto.eventually hf.eventually_regularAt,
      (slice_smooth ρ).continuous.continuousAt.tendsto.eventually hσ,
      (slice_smooth (Real.exp ρ)).continuous.continuousAt.tendsto.eventually hp] with y hy hyσ hyp
    exact physicalCollarExpansion_slice R ρ hy hyσ hyp
  rw [physicalAngularScalarJet_affine hD (fieldD_diff _ hf.angular_regular hq0) 1 _ he,
    add_sub_cancel_left,radius_inverse_smul_cancel (Real.exp_ne_zero ρ)]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarTau_jets (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a))
    (hp : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef) :
    Real.exp ρ • (fun i j => physicalAngularScalarJet (fun y =>
      leafTensorTraceFree (physicalCollarGamma R f y) (physicalCollarTangential R f y) i j)
        (slice (Real.exp ρ) a)) =
      matrixScalarJets (fieldTau (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have ht := (leafTensorTraceFree_contDiffAt (physicalCollarGamma_smoothAt R hr hf')
    (physicalCollarTangential_smoothAt R hr hf' hp.self_of_nhds) hp.self_of_nhds).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hq := (physicalCollarGamma_pos_iff R ρ f a).mp hp.self_of_nhds
  have hq0 : determinant (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  have hta : ContDiffAt ℝ 2 (fieldTau (collarParams R (Real.exp ρ)) (f.angular ρ)) a :=
    (traceFreeField_diff ((fieldQ_diff _ hf.angular_regular).of_le (by norm_num))
      hf.angular_regular.2.2.2.2 hq0).const_smul _
  funext i j
  change Real.exp ρ • physicalAngularScalarJet _ _ = actualScalarJet _ a
  have he : (fun y => leafTensorTraceFree (physicalCollarGamma R f (slice (Real.exp ρ) y))
      (physicalCollarTangential R f (slice (Real.exp ρ) y)) i j) =ᶠ[𝓝 a]
      fun y => (1/Real.exp ρ)*fieldTau (collarParams R (Real.exp ρ)) (f.angular ρ) y i j := by
    filter_upwards [(slice_smooth (Real.exp ρ)).continuous.continuousAt.tendsto.eventually hp] with y hy
    exact congrFun (congrFun (physicalCollarTau_slice R ρ f hy) i) j
  rw [physicalAngularScalarJet_scaled (contDiffAt_pi.mp (contDiffAt_pi.mp ht i) j) (component_diff hta i j) _ he,smul_smul]
  simp

lemma physicalCollarShear_scaled (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef) :
    Real.exp ρ • leafTensorTraceFree (physicalCollarGamma R f (slice (Real.exp ρ) a))
      (sourceChi (physicalCollarU R f) (physicalCollarGamma R f) (physicalCollarShift R f)
      (slice (Real.exp ρ) a)) = fieldX (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  rw [physicalCollarShear_unscaled R ρ hf hσ hp,physicalCollarU_slice R ρ hf hσ hp,
    smul_smul,fieldX,traceFreeField_eq]
  congr 1
  simp only [physicalBaseLapse,collarParams,Matrix.cons_val_zero]
  field_simp

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem physical_collar_null_realization {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hR : 0 < R) (hf : f.SmoothAt (slice ρ a))
    (hσ : ∀ᶠ y in 𝓝 (slice ρ a), ∀ i j,
      D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) y=0)
    (hstar : D (CKSRealizedRound.basis 0) f.fstar (slice ρ a)=0)
    (hp : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f)
      (slice (Real.exp ρ) a))
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f)
      (slice (Real.exp ρ) a)) :
    physicalNullInput (physicalCollarU R f) (physicalCollarL R f)
      (physicalCollarGamma R f) (physicalCollarTangential R f)
      (physicalCollarShift R f) (physicalCollarEta R f)
      (slice (Real.exp ρ) a) (paddingWeight R (Real.exp ρ)) =
    fieldNullInput (collarParams R (Real.exp ρ)) (f.angular ρ) a
 := by
  have hrec := physicalCollar_reconstruction_eventually hR hf hp hd hu
  have hmass := (physicalAngularScalarJet_congr hrec.1).trans (physicalCollarF_jet hR ρ hf)
  have ht := physicalAngularScalarJet_congr hrec.2.2
  have htr := physicalAngularScalarJet_congr (D_eventually_congr hrec.2.2 (CKSRealizedRound.basis 0))
  have hde := physicalAngularScalarJet_congr hrec.2.1
  have hder := D_congr hrec.1 (CKSRealizedRound.basis 0)
  have hF : (Real.exp ρ)^2*(D (CKSRealizedRound.basis 0)
      (sourceMass (physicalCollarU R f) (physicalCollarGamma R f)
       (physicalCollarTangential R f) (physicalCollarShift R f))
      (slice (Real.exp ρ) a)-paddingWeight R (Real.exp ρ)/(Real.exp ρ*Real.sqrt (Real.exp ρ))) =
      (1-(collarParams R (Real.exp ρ)) 1)*(f.angular ρ).massRadial a-
        (collarParams R (Real.exp ρ)) 2*(f.angular ρ).massGap a := by
    rw [hder,physicalCollarF_radial hR ρ hf.regularAt hstar]
    change (Real.exp ρ)^2*(_+1/Real.exp ρ^2*_-_) =
      (1-roundingWeight R (Real.exp ρ))*(f.angular ρ).massRadial a-
      (Real.exp ρ*deriv (roundingWeight R) (Real.exp ρ))*(f.angular ρ).massGap a
    field_simp
    ring
  unfold physicalNullInput
  simp only [slice_zero]
  rw [hmass,hF]
  apply Prod.ext
  · unfold physicalMomentumInput
    simp only [slice_zero]
    rw [ht,htr,hde,physicalCollarGamma_jet R ρ hf,physicalCollarU_jet hR ρ hf hσ hp hd hu,
      physicalCollarT_jet R ρ hf,physicalCollarL_jet R ρ hf,physicalCollarTr_jet R ρ hf,
      physicalCollarExpansion_jet R ρ hf hσ hp,physicalCollarShift_jets R ρ hf,
      physicalCollarEta_jets R ρ hf,physicalCollarTau_jets R ρ hf hp,
      physicalCollarShear_scaled R ρ hf.regularAt hσ.self_of_nhds hp.self_of_nhds,
      physicalCollarEta_radial_scaled R ρ hf.regularAt]
    rfl
  · rfl

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafTensorTraceFree_isHermitian {γ τ : Mat} (hγ : γ.IsHermitian) (hτ : τ.IsHermitian) :
    (leafTensorTraceFree γ τ).IsHermitian := hτ.sub (hγ.smul (by rfl))

lemma physicalCollarTangential_isHermitian (R : ℝ) (f : LogCollarData) (x : PhysicalPoint)
    (hγ : (physicalCollarGamma R f x).IsHermitian)
    (hτ : (f.tauDivR2 (radiusLogPoint x)).IsHermitian) :
    (physicalCollarTangential R f x).IsHermitian :=
  (hγ.smul (by rfl)).add (leafTensorTraceFree_isHermitian hγ (hτ.smul (by rfl)))

theorem physical_collar_DEC_iff {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hR : 0 < R) (hf : f.SmoothAt (slice ρ a))
    (hσ : ∀ᶠ y in 𝓝 (slice ρ a), ∀ i j,
      D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) y=0)
    (hstar : D (CKSRealizedRound.basis 0) f.fstar (slice ρ a)=0)
    (hτ : ∀ᶠ y in 𝓝 (slice ρ a), (f.tauDivR2 y).IsHermitian)
    (hp : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a))
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a)) :
    physicalDEC (physicalCollarMetric R f) (physicalCollarTensor R f)
      (physicalCollarFrame R f) (slice (Real.exp ρ) a) ↔
      coordinateDEC (fieldNullInput (collarParams R (Real.exp ρ)) (f.angular ρ) a) (Real.exp ρ)
 := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hrp : 0 < (slice (Real.exp ρ) a) 0 := by simpa using Real.exp_pos ρ
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hτ' : ∀ᶠ y in 𝓝 (radiusLogPoint (slice (Real.exp ρ) a)), (f.tauDivR2 y).IsHermitian := by simpa using hτ
  have hTs : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarTangential R f y).IsHermitian := by
    filter_upwards [hp,(radiusLogPoint_smoothAt hr).continuousAt.tendsto.eventually hτ'] with y hyp hyτ
    exact physicalCollarTangential_isHermitian R f y hyp.isHermitian hyτ
  have hU0 : 0 < physicalCollarU R f (slice (Real.exp ρ) a) := radialMassLapse_pos hd hu
  have hH : 0 < sourceH (physicalCollarU R f) (physicalCollarGamma R f)
      (physicalCollarShift R f) (slice (Real.exp ρ) a) := by
    rw [physicalCollarU,sourceH_radialMassLapse _ _ _ _ hr hd.ne']
    exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hu)) hrp
  have hhat : 0 < (slice (Real.exp ρ) a) 0 * sourceH (physicalCollarU R f) (physicalCollarGamma R f)
      (physicalCollarShift R f) (slice (Real.exp ρ) a)/2 := div_pos (mul_pos hrp hH) (by norm_num)
  have h := physical_normalized_DEC_iff
    (physicalCollarU_smoothAt hR hr hf' hp.self_of_nhds hd.ne' hu.ne')
    (physicalCollarGamma_smoothAt R hr hf') (physicalCollarShift_smoothAt R hr hf')
    (physicalCollarL_smoothAt R hr hf') (physicalCollarEta_smoothAt R hr hf')
    (physicalCollarTangential_smoothAt R hr hf' hp.self_of_nhds)
    hU0 hp hTs hrp hhat (paddingWeight R (Real.exp ρ))
  dsimp only at h
  rw [physical_collar_null_realization hR hf hσ hstar hp hd hu] at h
  unfold physicalCollarMetric physicalCollarTensor physicalCollarFrame
  simpa only [slice_zero] using h

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma positiveAngular_posDef {q : Mat} (hs : q.IsHermitian) (hp : positiveAngular q) : q.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hs
  intro v hv
  have he : star v ⬝ᵥ (q *ᵥ v) = determinant q/q 1 1*(v 0)^2+
      q 1 1*(v 1+q 0 1/q 1 1*v 0)^2 := by
    simp only [dotProduct,mulVec,Fin.sum_univ_two,star_trivial]
    rw [hermitian_real_symmetry hs 1 0]
    unfold determinant
    rw [hermitian_real_symmetry hs 1 0]
    field_simp [hp.1.ne']
    ring
  rw [he]
  by_cases h0 : v 0=0
  · have h1 : v 1 ≠ 0 := by
      intro hh
      apply hv
      funext i
      fin_cases i <;> simp [h0,hh]
    simp only [h0,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,zero_add]
    exact mul_pos hp.1 (sq_pos_of_ne_zero h1)
  · exact add_pos_of_pos_of_nonneg (mul_pos (div_pos hp.2 hp.1) (sq_pos_of_ne_zero h0))
      (mul_nonneg hp.1.le (sq_nonneg _))

lemma positiveAngular_continuousAt {q : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hq : ContinuousAt q x) (hp : positiveAngular (q x)) :
    ∀ᶠ y in 𝓝 x, positiveAngular (q y) := by
  have h1 := ((continuous_apply 1).continuousAt.comp
    ((continuous_apply 1).continuousAt.comp hq)).eventually (Ioi_mem_nhds hp.1)
  have hd := (determinant_smooth.continuous.continuousAt.comp hq).eventually (Ioi_mem_nhds hp.2)
  filter_upwards [h1,hd] with y hy1 hyd
  exact ⟨hy1,hyd⟩

lemma posDef_eventually_of_symmetric {q : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hq : ContinuousAt q x) (hs : ∀ᶠ y in 𝓝 x, (q y).IsHermitian) (hp : (q x).PosDef) :
    ∀ᶠ y in 𝓝 x, (q y).PosDef := by
  have ha : positiveAngular (q x) := ⟨hp.diag_pos,(determinant_eq _).symm ▸ hp.det_pos⟩
  filter_upwards [hs,positiveAngular_continuousAt hq ha] with y hys hyp
  exact positiveAngular_posDef hys hyp

lemma physicalCollarGamma_isHermitian (R : ℝ) (f : LogCollarData) (x : PhysicalPoint)
    (hσ : (f.sigma (radiusLogPoint x)).IsHermitian)
    (he : (f.metricError (radiusLogPoint x)).IsHermitian) :
    (physicalCollarGamma R f x).IsHermitian :=
  (hσ.add (he.smul (by rfl))).smul (by rfl)

lemma physicalCollarGamma_eventually_posDef {R : ℝ} {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x))
    (hσ : ∀ᶠ z in 𝓝 (radiusLogPoint x), (f.sigma z).IsHermitian)
    (he : ∀ᶠ z in 𝓝 (radiusLogPoint x), (f.metricError z).IsHermitian)
    (hp : (physicalCollarGamma R f x).PosDef) :
    ∀ᶠ y in 𝓝 x, (physicalCollarGamma R f y).PosDef := by
  apply posDef_eventually_of_symmetric (physicalCollarGamma_smoothAt R hr hf).continuousAt _ hp
  filter_upwards [(radiusLogPoint_smoothAt hr).continuousAt.tendsto.eventually (hσ.and he)] with y hy
  exact physicalCollarGamma_isHermitian R f y hy.1 hy.2

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma sourceLapse_pos {f : SourceMassFields} {x : Point} (hp : (sourceMetric f x).PosDef) :
    0 < sourceLapse f x := one_div_pos.mpr (Real.sqrt_pos.mpr (metricBlock_schur_positive hp))

lemma source_metric_foliation {f : SourceMassFields} {x : Point} (hp : (sourceMetric f x).PosDef) :
    foliationMetric (sourceLapse f x) (sourceGamma f x) (sourceShift f x)=sourceMetric f x := by
  have hq : determinant (sourceGamma f x) ≠ 0 := by
    rw [determinant_eq]
    exact (metricBlock_leaf_posDef hp).det_pos.ne'
  have hs : 0 < sourceSchur f x := metricBlock_schur_positive hp
  have hr : 1/(sourceLapse f x)^2=sourceSchur f x := by
    rw [sourceLapse,div_pow,one_pow,Real.sq_sqrt hs.le]
    field_simp
  unfold foliationMetric sourceMetric
  rw [hr]
  have hv : (fun a => ∑ b, sourceGamma f x a b*sourceShift f x b)=f.b x := by
    funext a
    exact inverse_mul_vector (sourceGamma f x) hq (f.b x) a
  rw [hv]
  congr 1
  unfold sourceSchur sourceShift
  rw [inverse_quadratic _ hq]
  ring

lemma source_tensor_foliation {f : SourceTensorFields} {x : Point}
    (hp : (sourceMetric f.base x).PosDef) (hk : (sourceTangentialK f.base x).IsHermitian) :
    foliationTensor (sourceLapse f.base x) (sourceOriginalL f x) (sourceOriginalEta f x)
      (sourceTangentialK f.base x) (sourceShift f.base x)=sourceTensor f x := by
  have hU := (sourceLapse_pos hp).ne'
  have heta : ∀ a, sourceOriginalEta f x a/sourceLapse f.base x =
      f.kb x a-∑ b, sourceTangentialK f.base x a b*sourceShift f.base x b := by
    intro a
    change sourceLapse f.base x * _ / sourceLapse f.base x = _
    rw [mul_div_cancel_left₀ _ hU]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    rw [hermitian_real_symmetry hk a b]
    ring
  have hL : sourceOriginalL f x/(sourceLapse f.base x)^2 =
      sourceRadialK f x-2*∑ a, sourceShift f.base x a*f.kb x a+
        ∑ a, ∑ b, sourceTangentialK f.base x a b*(sourceShift f.base x a*sourceShift f.base x b) := by
    unfold sourceOriginalL sourceLapse
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hU)
  have heta' (a) := (div_eq_iff hU).mp (heta a)
  unfold foliationTensor sourceTensor
  have hcross : (fun a => sourceOriginalEta f x a/sourceLapse f.base x+
      ∑ b, sourceTangentialK f.base x a b*sourceShift f.base x b)=f.kb x := by
    funext a
    rw [heta a]
    ring
  rw [hcross,hL]
  congr 1
  simp_rw [heta']
  simp only [Fin.sum_univ_two]
  field_simp
  ring

lemma source_radialExpansion_eq (f : SourceMassFields) (x : Point) :
    radialExpansion (sourceGamma f) (sourceShift f) x=sourceExpansion f x := by
  unfold radialExpansion sourceExpansion
  rw [leafTensorTrace_eq]
  rfl

lemma source_radialMassRadical_eq {f : SourceMassFields} {x : Point} (hr : x 0 ≠ 0) :
    radialMassRadical (sourceT f) (sourcePhysicalMass f) x=
      (sourceLapse f x*sourceExpansion f x)^2 := by
  unfold radialMassRadical sourcePhysicalMass sourceT sourceLapse
  field_simp
  ring

lemma source_radialMassLapse_eq {f : SourceMassFields} {x : Point}
    (hr : x 0 ≠ 0) (hp : (sourceMetric f x).PosDef) (hd : 0 < sourceExpansion f x) :
    radialMassLapse (sourceGamma f) (sourceShift f) (sourceT f) (sourcePhysicalMass f) x=
      sourceLapse f x := by
  rw [radialMassLapse,source_radialExpansion_eq,source_radialMassRadical_eq hr,
    Real.sqrt_sq (mul_nonneg (sourceLapse_pos hp).le hd.le)]
  exact mul_div_cancel_right₀ _ hd.ne'

lemma source_radialTangential_eq {f : SourceTensorFields} {x : Point}
    (hp : (sourceMetric f.base x).PosDef) :
    radialTangential (sourceGamma f.base) (sourceT f.base) (sourceOriginalTau f) x=
      sourceTangentialK f.base x := by
  have hγ := metricBlock_leaf_posDef hp
  have ht : sourceOriginalTau f x=leafTensorTraceFree (sourceGamma f.base x)
      (sourceTangentialK f.base x) := by
    rw [sourceOriginalTau,leafTensorTraceFree,leafTensorTrace_eq]
    rfl
  have hpull : leafTensorTraceFree (sourceGamma f.base x) (sourceOriginalTau f x)=sourceOriginalTau f x := by
    unfold leafTensorTraceFree
    rw [ht,leafTensorTrace_traceFree hγ]
    simp
  rw [radialTangential,hpull,sourceOriginalTau]
  have he : sourceT f.base x=traceProduct (inverse (sourceGamma f.base x)) (sourceTangentialK f.base x)/2 := by
    unfold sourceT
    ring
  rw [he]
  abel

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSBending
noncomputable section
open CKSCalculus Filter CKSAngularGeometry
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma collarParams_initial {R r S : ℝ} (hR : 0 < R) (hr : r ≤ R) :
    collarParams R r = oldParams (collarParams S r) := by
  have hr2 : r ≤ 2*R := hr.trans (by linarith)
  ext i
  fin_cases i <;> simp [collarParams,oldParams,roundingWeight_zero hR hr2,
    roundingWeight_deriv_initial hR hr2,paddingMass_initial hR hr,paddingWeight_zero hR hr]

end
end CKSBending

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma radiusLogPoint_exp {x : PhysicalPoint} (hr : 0 < x 0) :
    Real.exp (radiusLogPoint x 0)=x 0 := by simp [radiusLogPoint,Real.exp_log hr]

lemma inner_collar_fields {R : ℝ} {f : LogCollarData} {x : PhysicalPoint}
    (hR : 0 < R) (hr : 0 < x 0) (hi : x 0 ≤ R) :
    physicalCollarGamma R f x = (x 0)^2 • (f.sigma (radiusLogPoint x)+f.metricError (radiusLogPoint x)) ∧
    physicalCollarShift R f x = f.shift (radiusLogPoint x) ∧
    physicalCollarT R f x = 1+f.tError (radiusLogPoint x) ∧
    physicalCollarF R f x = f.fstar (radiusLogPoint x)+f.massError (radiusLogPoint x) ∧
    physicalCollarL R f x = 1+f.LError (radiusLogPoint x) ∧
    physicalCollarEta R f x = x 0 • f.etaDivR (radiusLogPoint x) ∧
    physicalCollarRawTau R f x = (x 0)^2 • f.tauDivR2 (radiusLogPoint x) := by
  have hi2 : x 0 ≤ 2*R := hi.trans (by linarith)
  simp only [physicalCollarGamma,physicalCollarShift,physicalCollarT,physicalCollarF,
    physicalCollarL,physicalCollarEta,physicalCollarRawTau,collarQ,collarShift,collarT,
    collarF,collarL,collarLb,collarEtaDivR,radialLift,radiusLogPoint_exp hr,
    roundingWeight_zero hR hi2,paddingWeight_zero hR hi,paddingMass_initial hR hi,
    sub_zero,one_smul,one_mul,zero_div,add_zero,mul_one,true_and]

lemma radialExpansion_congr {γ δ : PhysicalPoint → Mat} {s t : PhysicalPoint → Point}
    {x : PhysicalPoint} (hq : γ =ᶠ[𝓝 x] δ) (hs : s =ᶠ[𝓝 x] t) :
    radialExpansion γ s x=radialExpansion δ t x := by
  have hqD (i a b) := D_congr (hq.mono (fun y hy => congrArg (fun q : Mat => q a b) hy))
    (CKSRealizedRound.basis i)
  have hsD (i a) := D_congr (hs.mono (fun y hy => congrFun hy a)) (CKSRealizedRound.basis i)
  have hd : leafRadialRate γ s x=leafRadialRate δ t x := by
    funext a b
    simp only [leafRadialRate,hq.self_of_nhds,hs.self_of_nhds,hqD,hsD]
  unfold radialExpansion
  rw [hq.self_of_nhds,hd]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma source_inner_collar_fields {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hR : 0 < R) (hr : 0 < x 0) (hi : x 0 ≤ R)
    (hf : f.base.RegularAt x) (hp : (sourceMetric f.base x).PosDef) :
    physicalCollarGamma R (sourceCollarData f.logFields) x = sourceGamma f.base x ∧
    physicalCollarShift R (sourceCollarData f.logFields) x = sourceShift f.base x ∧
    physicalCollarT R (sourceCollarData f.logFields) x = sourceT f.base x ∧
    physicalCollarF R (sourceCollarData f.logFields) x = sourcePhysicalMass f.base x ∧
    physicalCollarL R (sourceCollarData f.logFields) x = sourceOriginalL f x ∧
    physicalCollarEta R (sourceCollarData f.logFields) x = sourceOriginalEta f x ∧
    physicalCollarRawTau R (sourceCollarData f.logFields) x = sourceOriginalTau f x := by
  obtain ⟨hγ,hs,ht,hF,hL,hη,hτ⟩ := inner_collar_fields (f:=sourceCollarData f.logFields) hR hr hi
  have hc := logRadiusChart_radiusLogPoint hr
  have he := radiusLogPoint_exp hr
  have hg := congrFun (sourceGamma_pullback f.base) (radiusLogPoint x)
  have hshift := congrFun (sourceShift_pullback f.base) (radiusLogPoint x)
  have htan := congrFun (sourceT_pullback f.base) (radiusLogPoint x)
  have hl := congrFun (sourceOriginalL_pullback f) (radiusLogPoint x)
  have heta := congrFun (sourceOriginalEta_pullback f) (radiusLogPoint x)
  have htau := congrFun (sourceOriginalTau_pullback f) (radiusLogPoint x)
  rw [hc] at hg hshift htan hl heta htau
  have hfp : f.base.RegularAt (logRadiusChart (radiusLogPoint x)) := hc.symm ▸ hf
  have hpp : (sourceMetric f.base (logRadiusChart (radiusLogPoint x))).PosDef := hc.symm ▸ hp
  have hmass := sourcePhysicalMass_pullback hfp hpp
  rw [hc] at hmass
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hγ]
    change (x 0)^2 • (f.logFields.base.sigma (radiusLogPoint x)+logQError f.logFields.base (radiusLogPoint x)) = _
    rw [logQError_scaled,he]
    have hh : f.logFields.base.sigma (radiusLogPoint x)+
        ((1/(x 0)^2) • logGamma f.logFields.base (radiusLogPoint x)-f.logFields.base.sigma (radiusLogPoint x)) =
        (1/(x 0)^2) • logGamma f.logFields.base (radiusLogPoint x) := by abel
    rw [hh,smul_smul, mul_one_div_cancel (pow_ne_zero _ hr.ne'),one_smul]
    exact hg.symm
  · rw [hs]
    exact hshift.symm
  · rw [ht]
    change 1+(logT f.base.logFields (radiusLogPoint x)-1)=sourceT f.base x
    rw [← htan]
    ring
  · rw [hF]
    change cksLeadingField f.base.logFields (radiusLogPoint x)+
      (logPhysicalMass f.base.logFields (radiusLogPoint x)-cksLeadingField f.base.logFields (radiusLogPoint x))=_
    rw [← hmass]
    ring
  · rw [hL]
    change 1+(logOriginalL f.logFields (radiusLogPoint x)-1)=_
    rw [← hl]
    ring
  · rw [hη]
    funext a
    change x 0*(logOriginalEta f.logFields (radiusLogPoint x) a/Real.exp (radiusLogPoint x 0))=_
    rw [he,← heta]
    field_simp
  · rw [hτ]
    funext a b
    change (x 0)^2*(logOriginalTau f.logFields (radiusLogPoint x) a b/Real.exp (radiusLogPoint x 0)^2)=_
    rw [he,← htau]
    field_simp

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma actualMetricFirstJet_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : actualMetricFirstJet G x = actualMetricFirstJet H x := by
  funext i j k
  exact D_congr (h.mono (fun y hy => congrArg (fun q : AmbientMat => q j k) hy)) _

lemma coordinateChristoffel_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : coordinateChristoffel G x = coordinateChristoffel H x := by
  unfold coordinateChristoffel
  rw [h.self_of_nhds,actualMetricFirstJet_congr h]

lemma covariantVector_congr {G H : PhysicalPoint → AmbientMat}
    {W V : PhysicalPoint → PhysicalPoint} {x e : PhysicalPoint}
    (hG : G =ᶠ[𝓝 x] H) (hW : W =ᶠ[𝓝 x] V) :
    covariantVector G e W x = covariantVector H e V x := by
  funext k
  have hd := D_congr (hW.mono (fun y hy => congrFun hy k)) e
  simp only [covariantVector,hW.self_of_nhds,coordinateChristoffel_congr hG,hd]

lemma frameCoefficient_congr {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    frameCoefficient G E x = frameCoefficient H F x := by
  funext i j k
  unfold frameCoefficient
  rw [hG.self_of_nhds,hE.self_of_nhds i,hE.self_of_nhds k,
    covariantVector_congr hG (hE.mono (fun y hy => hy j))]

lemma actualFrameBracket_congr {E F : LocalFrame} {x : PhysicalPoint}
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    actualFrameBracket E x = actualFrameBracket F x := by
  funext i j k
  unfold actualFrameBracket
  rw [hE.self_of_nhds i,hE.self_of_nhds j,
    D_congr (hE.mono (fun y hy => congrFun (hy j) k)),
    D_congr (hE.mono (fun y hy => congrFun (hy i) k))]

lemma frameBracketCoefficient_congr {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    frameBracketCoefficient G E x = frameBracketCoefficient H F x := by
  funext i j k
  unfold frameBracketCoefficient
  rw [hG.self_of_nhds,hE.self_of_nhds k,actualFrameBracket_congr hE]

lemma actualFrameCurvature_congr {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    actualFrameCurvature G E x = actualFrameCurvature H F x := by
  have hc : ∀ᶠ y in 𝓝 x, frameCoefficient G E y=frameCoefficient H F y := by
    filter_upwards [hG.eventually_nhds,hE.eventually_nhds] with y hyG hyE
    exact frameCoefficient_congr hyG hyE
  funext i j k l
  unfold actualFrameCurvature
  rw [hE.self_of_nhds i,hE.self_of_nhds j,
    D_congr (hc.mono (fun y hy => congrArg (fun q => q j k l) hy)),
    D_congr (hc.mono (fun y hy => congrArg (fun q => q i k l) hy)),
    hc.self_of_nhds,frameBracketCoefficient_congr hG hE]

lemma actualFrameScalar_congr {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    actualFrameScalar G E x = actualFrameScalar H F x := by
  unfold actualFrameScalar
  rw [actualFrameCurvature_congr hG hE]

lemma coordinateConnectionVector_congr {G H : PhysicalPoint → AmbientMat}
    {x e v : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) :
    coordinateConnectionVector G e v x = coordinateConnectionVector H e v x := by
  unfold coordinateConnectionVector
  rw [coordinateChristoffel_congr hG]

lemma coordinateTensorCovariant_congr {G H K L : PhysicalPoint → AmbientMat}
    {x e v w : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) (hK : K =ᶠ[𝓝 x] L) :
    coordinateTensorCovariant G K e v w x = coordinateTensorCovariant H L e v w x := by
  unfold coordinateTensorCovariant
  have hd (i j) := D_congr (hK.mono (fun y hy => congrArg (fun k : AmbientMat => k i j) hy)) e
  simp only [hK.self_of_nhds,coordinateConnectionVector_congr hG,hd]

lemma coordinateMomentum_congr {G H K L : PhysicalPoint → AmbientMat}
    {x w : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) (hK : K =ᶠ[𝓝 x] L) :
    coordinateMomentum G K x w = coordinateMomentum H L x w := by
  have hc : ∀ i j, coordinateTensorCovariant G K (CKSRealizedRound.basis i)
      (CKSRealizedRound.basis j) w x = coordinateTensorCovariant H L
      (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x :=
    fun _ _ => coordinateTensorCovariant_congr hG hK
  have ht : (fun y => ((G y)⁻¹*K y).trace) =ᶠ[𝓝 x] (fun y => ((H y)⁻¹*L y).trace) := by
    filter_upwards [hG,hK] with y hyG hyK
    rw [hyG,hyK]
  simp only [coordinateMomentum,hG.self_of_nhds,hc,D_congr ht]

lemma momentumCovector_congr {G H K L : PhysicalPoint → AmbientMat}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) (hK : K =ᶠ[𝓝 x] L) :
    momentumCovector G K x = momentumCovector H L x := by
  funext i
  exact coordinateMomentum_congr hG hK

theorem physicalDEC_congr {G H K L : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) (hK : K =ᶠ[𝓝 x] L)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    physicalDEC G K E x ↔ physicalDEC H L F x := by
  unfold physicalDEC physicalEnergy
  rw [momentumCovector_congr hG hK,actualFrameScalar_congr hG hE,
    hG.self_of_nhds,hK.self_of_nhds]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma source_inner_collar_fields_eventually {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hr : 0 < x 0) (hi : x 0 < R) (hf : f.base.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (sourceMetric f.base y).PosDef) :
    ∀ᶠ y in 𝓝 x,
      physicalCollarGamma R (sourceCollarData f.logFields) y = sourceGamma f.base y ∧
      physicalCollarShift R (sourceCollarData f.logFields) y = sourceShift f.base y ∧
      physicalCollarT R (sourceCollarData f.logFields) y = sourceT f.base y ∧
      physicalCollarF R (sourceCollarData f.logFields) y = sourcePhysicalMass f.base y ∧
      physicalCollarL R (sourceCollarData f.logFields) y = sourceOriginalL f y ∧
      physicalCollarEta R (sourceCollarData f.logFields) y = sourceOriginalEta f y ∧
      physicalCollarRawTau R (sourceCollarData f.logFields) y = sourceOriginalTau f y := by
  have hr' := ((continuous_apply 0).continuousAt (x := x)).eventually (Ioi_mem_nhds hr)
  have hi' := ((continuous_apply 0).continuousAt (x := x)).eventually (Iio_mem_nhds hi)
  filter_upwards [hr',hi',hf.eventually,hp] with y hyr hyi hyf hyp
  exact source_inner_collar_fields (hr.trans hi) hyr hyi.le hyf hyp

lemma source_inner_collar_lapse {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hr : 0 < x 0) (hi : x 0 < R) (hf : f.base.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (sourceMetric f.base y).PosDef)
    (hd : 0 < sourceExpansion f.base x) :
    physicalCollarU R (sourceCollarData f.logFields) x=sourceLapse f.base x := by
  have h := source_inner_collar_fields_eventually hr hi hf hp
  have he := radialExpansion_congr (h.mono (fun _ hy => hy.1))
    (h.mono (fun _ hy => hy.2.1))
  have ht := h.self_of_nhds.2.2.1
  have hF := h.self_of_nhds.2.2.2.1
  unfold physicalCollarU radialMassLapse
  rw [he]
  unfold radialMassRadical
  rw [ht,hF]
  exact source_radialMassLapse_eq hr.ne' hp.self_of_nhds hd

lemma source_inner_collar_recovery {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hr : 0 < x 0) (hi : x 0 < R) (hf : f.base.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (sourceMetric f.base y).PosDef)
    (hd : 0 < sourceExpansion f.base x)
    (hk : (sourceTangentialK f.base x).IsHermitian) :
    physicalCollarMetric R (sourceCollarData f.logFields) x=sourceMetric f.base x ∧
    physicalCollarTensor R (sourceCollarData f.logFields) x=sourceTensor f x ∧
    ∀ i, physicalCollarFrame R (sourceCollarData f.logFields) i x=sourceFrame f.base i x := by
  obtain ⟨hγ,hs,ht,hF,hL,hη,hτ⟩ := source_inner_collar_fields (hr.trans hi) hr hi.le hf hp.self_of_nhds
  have hU := source_inner_collar_lapse hr hi hf hp hd
  have hT : physicalCollarTangential R (sourceCollarData f.logFields) x=sourceTangentialK f.base x := by
    unfold physicalCollarTangential radialTangential
    rw [hγ,ht,hτ]
    exact source_radialTangential_eq hp.self_of_nhds
  refine ⟨?_,?_,?_⟩
  · unfold physicalCollarMetric
    rw [hU,hγ,hs]
    exact source_metric_foliation hp.self_of_nhds
  · unfold physicalCollarTensor
    rw [hU,hL,hη,hT,hs]
    exact source_tensor_foliation hp.self_of_nhds hk
  · intro i
    unfold physicalCollarFrame sourceFrame
    rw [hU,hγ,hs]

theorem physical_source_inner_collar_DEC_iff {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hr : 0 < x 0) (hi : x 0 < R) (hf : f.base.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (sourceMetric f.base y).PosDef)
    (hd : ∀ᶠ y in 𝓝 x, 0 < sourceExpansion f.base y)
    (hk : ∀ᶠ y in 𝓝 x, (sourceTangentialK f.base y).IsHermitian) :
    physicalDEC (physicalCollarMetric R (sourceCollarData f.logFields))
      (physicalCollarTensor R (sourceCollarData f.logFields))
      (physicalCollarFrame R (sourceCollarData f.logFields)) x ↔
      physicalDEC (sourceMetric f.base) (sourceTensor f) (sourceFrame f.base) x := by
  have hr' := ((continuous_apply 0).continuousAt (x := x)).eventually (Ioi_mem_nhds hr)
  have hi' := ((continuous_apply 0).continuousAt (x := x)).eventually (Iio_mem_nhds hi)
  have hrec : ∀ᶠ y in 𝓝 x,
      physicalCollarMetric R (sourceCollarData f.logFields) y=sourceMetric f.base y ∧
      physicalCollarTensor R (sourceCollarData f.logFields) y=sourceTensor f y ∧
      ∀ i, physicalCollarFrame R (sourceCollarData f.logFields) i y=sourceFrame f.base i y := by
    filter_upwards [hr',hi',hf.eventually,hp.eventually_nhds,hd,hk] with y hyr hyi hyf hyp hyd hyk
    exact source_inner_collar_recovery hyr hyi hyf hyp hyd hyk
  exact physicalDEC_congr (hrec.mono (fun _ h => h.1)) (hrec.mono (fun _ h => h.2.1))
    (hrec.mono (fun _ h => h.2.2))

end
end CKSMixedGeometry

end

















noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma SourceMassFields.SmoothAt.regularAt {f : SourceMassFields} {x : Point}
    (hf : f.SmoothAt x) : f.RegularAt x := by
  exact ⟨hf.sigma.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.mg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.mK.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),
    hf.mr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.eg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.ek.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.b.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.err.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)⟩

lemma SourceTensorFields.SmoothAt.regularAt {f : SourceTensorFields} {x : Point}
    (hf : f.SmoothAt x) : f.RegularAt x :=
  ⟨hf.base.regularAt,hf.kr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.kb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)⟩

lemma inverse_smoothAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : E → Mat} {x : E}
    (hq : ContDiffAt ℝ ∞ q x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => inverse (q y)) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  unfold inverse
  apply ContDiffAt.div
  · fin_cases i <;> fin_cases k <;> dsimp <;> first
      | exact contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _
      | exact (contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _).neg
  · exact determinant_smooth.contDiffAt.comp x hq
  · exact h0

lemma traceProduct_smoothAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q p : E → Mat} {x : E}
    (hq : ContDiffAt ℝ ∞ q x) (hp : ContDiffAt ℝ ∞ p x) :
    ContDiffAt ℝ ∞ (fun y => traceProduct (q y) (p y)) x :=
  ContDiffAt.sum fun i _ => ContDiffAt.sum fun k _ =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k).mul (contDiffAt_pi.mp (contDiffAt_pi.mp hp k) i)

lemma sourceGamma_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sourceGamma f) y := by
  have hr : ContDiffAt ℝ ∞ (fun z : Point => z 0) y := by fun_prop
  exact (((hr.pow 2).smul (angularLift_diff hf.sigma)).add
      ((contDiffAt_const.fun_div hr hy).smul (angularLift_diff hf.mg))).add hf.eg

lemma sourceTangentialK_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sourceTangentialK f) y := by
  have hr : ContDiffAt ℝ ∞ (fun z : Point => z 0) y := by fun_prop
  exact (((hr.pow 2).smul (angularLift_diff hf.sigma)).add
      ((contDiffAt_const.fun_div hr hy).smul (angularLift_diff hf.mK))).add hf.ek

lemma sourceRadialMetric_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sourceRadialMetric f) y := by
  have hr : ContDiffAt ℝ ∞ (fun z : Point => z 0) y := by fun_prop
  exact ((contDiffAt_const.div (contDiffAt_const.add (hr.pow 2)) (by positivity)).add
    ((angularLift_diff hf.mr).div (hr.pow 5) (pow_ne_zero _ hy))).add hf.err

lemma sourceShift_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceShift f) y := by
  have h0 : determinant (sourceGamma f y) ≠ 0 := by
    rw [determinant_eq]; exact (metricBlock_leaf_posDef hp).det_pos.ne'
  have hi := inverse_smoothAt (sourceGamma_smoothAt hf hy) h0
  exact contDiffAt_pi.mpr fun a => ContDiffAt.sum fun b _ =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hi a) b).mul (contDiffAt_pi.mp hf.b b)

lemma sourceSchur_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceSchur f) y := by
  have h0 : determinant (sourceGamma f y) ≠ 0 := by
    rw [determinant_eq]; exact (metricBlock_leaf_posDef hp).det_pos.ne'
  have hi := inverse_smoothAt (sourceGamma_smoothAt hf hy) h0
  exact (sourceRadialMetric_smoothAt hf hy).sub (ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hi a) b).mul ((contDiffAt_pi.mp hf.b a).mul (contDiffAt_pi.mp hf.b b)))

lemma sourceLapse_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceLapse f) y := by
  have hs : 0 < sourceSchur f y := metricBlock_schur_positive hp
  exact contDiffAt_const.div ((sourceSchur_smoothAt hf hy hp).sqrt hs.ne') (Real.sqrt_ne_zero'.mpr hs)

lemma sourceExpansion_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceExpansion f) y := by
  have he : sourceExpansion f=radialExpansion (sourceGamma f) (sourceShift f) :=
    funext fun x => (source_radialExpansion_eq f x).symm
  rw [he]
  exact radialExpansion_smoothAt (sourceGamma_smoothAt hf hy) (sourceShift_smoothAt hf hy hp)
    (metricBlock_leaf_posDef hp)

lemma sourceT_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceT f) y := by
  have he : sourceT f=fun x => leafTensorTrace (sourceGamma f x) (sourceTangentialK f x)/2 := by
    funext x; rw [leafTensorTrace_eq,sourceT]; unfold traceProduct; ring
  rw [he]
  exact (leafTensorTrace_contDiffAt (sourceGamma_smoothAt hf hy) (sourceTangentialK_smoothAt hf hy)
    (metricBlock_leaf_posDef hp)).div_const 2

lemma sourcePhysicalMass_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourcePhysicalMass f) y := by
  have he : sourcePhysicalMass f=fun x => x 0/2*(1+(x 0*sourceT f x)^2-
      (sourceLapse f x*sourceExpansion f x)^2) := by
    funext x; unfold sourcePhysicalMass sourceT sourceLapse; ring
  rw [he]
  have hT := sourceT_smoothAt hf hy hp
  have hU := sourceLapse_smoothAt hf hy hp
  have hd := sourceExpansion_smoothAt hf hy hp
  fun_prop

lemma sourceRadialK_smoothAt {f : SourceTensorFields} {y : Point} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (sourceRadialK f) y := by
  have hh : ContDiffAt ℝ ∞ (fun z : Point => 1+(z 0)^2) y := by fun_prop
  exact (contDiffAt_const.div hh (by positivity)).add hf.kr

lemma sourceOriginalL_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) (hp : (sourceMetric f.base y).PosDef) :
    ContDiffAt ℝ ∞ (sourceOriginalL f) y := by
  have hshift := sourceShift_smoothAt hf.base hy hp
  have hk := sourceTangentialK_smoothAt hf.base hy
  have hU := sourceLapse_smoothAt hf.base hy hp
  exact (hU.pow 2).mul (((sourceRadialK_smoothAt hf).sub (contDiffAt_const.mul
    (ContDiffAt.sum fun a _ => (contDiffAt_pi.mp hshift a).mul (contDiffAt_pi.mp hf.kb a)))).add
      (ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => (contDiffAt_pi.mp (contDiffAt_pi.mp hk a) b).mul
        ((contDiffAt_pi.mp hshift a).mul (contDiffAt_pi.mp hshift b))))

lemma sourceOriginalEta_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) (hp : (sourceMetric f.base y).PosDef) :
    ContDiffAt ℝ ∞ (sourceOriginalEta f) y := by
  have hshift := sourceShift_smoothAt hf.base hy hp
  have hk := sourceTangentialK_smoothAt hf.base hy
  have hU := sourceLapse_smoothAt hf.base hy hp
  apply contDiffAt_pi.mpr
  intro a
  exact hU.mul ((contDiffAt_pi.mp hf.kb a).sub (ContDiffAt.sum fun b _ =>
    (contDiffAt_pi.mp hshift b).mul (contDiffAt_pi.mp (contDiffAt_pi.mp hk b) a)))

lemma sourceOriginalTau_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) (hp : (sourceMetric f.base y).PosDef) :
    ContDiffAt ℝ ∞ (sourceOriginalTau f) y := by
  have he : sourceOriginalTau f=fun x => leafTensorTraceFree (sourceGamma f.base x) (sourceTangentialK f.base x) := by
    funext x; rw [sourceOriginalTau,leafTensorTraceFree,leafTensorTrace_eq]; rfl
  rw [he]
  exact leafTensorTraceFree_contDiffAt (sourceGamma_smoothAt hf.base hy) (sourceTangentialK_smoothAt hf.base hy)
    (metricBlock_leaf_posDef hp)

end
end CKSMixedGeometry

end




end OAI
end

section
namespace OAI














noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma source_cksLeading_smoothAt {f : SourceMassFields} {x : Point}
    (hf : f.SmoothAt (logRadiusChart x)) (hs : determinant (f.logFields.sigma x) ≠ 0) :
    ContDiffAt ℝ ∞ (cksLeadingField f.logFields) x := by
  have hσ := hf.sigma
  have hg := hf.mg
  have hk := hf.mK
  have hr := hf.mr
  rw [angularProjection_logRadiusChart] at hσ hg hk hr
  have hi := inverse_smoothAt (angularLift_diff hσ) hs
  exact ((contDiffAt_const.mul (angularLift_diff hr)).add
    (contDiffAt_const.mul (traceProduct_smoothAt hi (angularLift_diff hg)))).add
      (contDiffAt_const.mul (traceProduct_smoothAt hi (angularLift_diff hk)))

theorem sourceCollarData_smoothAt {f : SourceTensorFields} {x : Point}
    (hf : f.SmoothAt (logRadiusChart x))
    (hp : ∀ᶠ y in 𝓝 (logRadiusChart x), (sourceMetric f.base y).PosDef)
    (hs : determinant (f.base.logFields.sigma x) ≠ 0) :
    (sourceCollarData f.logFields).SmoothAt x := by
  have hr : (logRadiusChart x) 0 ≠ 0 := by simp [logRadiusChart]
  have hc := logRadiusChart_smooth.contDiffAt (x := x)
  have hσ := hf.base.sigma
  rw [angularProjection_logRadiusChart] at hσ
  have hσ' := angularLift_diff hσ
  have hγ := (sourceGamma_smoothAt hf.base hr).comp x hc
  dsimp only [Function.comp_def] at hγ
  rw [sourceGamma_pullback] at hγ
  have hshift := (sourceShift_smoothAt hf.base hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at hshift
  rw [sourceShift_pullback] at hshift
  have ht := (sourceT_smoothAt hf.base hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at ht
  rw [sourceT_pullback] at ht
  have hL := (sourceOriginalL_smoothAt hf hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at hL
  rw [sourceOriginalL_pullback] at hL
  have hη := (sourceOriginalEta_smoothAt hf hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at hη
  rw [sourceOriginalEta_pullback] at hη
  have hτ := (sourceOriginalTau_smoothAt hf hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at hτ
  rw [sourceOriginalTau_pullback] at hτ
  have heq : logPhysicalMass f.base.logFields =ᶠ[𝓝 x] (fun y => sourcePhysicalMass f.base (logRadiusChart y)) := by
    filter_upwards [hc.continuousAt.tendsto.eventually hf.base.regularAt.eventually,
      hc.continuousAt.tendsto.eventually hp] with y hy hyp
    exact (sourcePhysicalMass_pullback hy hyp).symm
  have hmass := ((sourcePhysicalMass_smoothAt hf.base hr hp.self_of_nhds).comp x hc).congr_of_eventuallyEq heq
  have hlead := source_cksLeading_smoothAt hf.base hs
  have hexp : ContDiffAt ℝ ∞ (fun y : Point => Real.exp (y 0)) x := by fun_prop
  have he : ContDiffAt ℝ ∞ (logQError f.base.logFields) x := by
    have he' : logQError f.base.logFields=fun y =>
        (1/Real.exp (y 0)^2) • logGamma f.base.logFields y-f.base.logFields.sigma y :=
      funext (logQError_scaled f.base.logFields)
    rw [he']
    exact ((contDiffAt_const.div (hexp.pow 2) (by positivity)).smul hγ).sub hσ'
  refine ⟨hσ',he,hshift,ht.sub contDiffAt_const,hL.sub contDiffAt_const,
    hmass.sub hlead,hlead,?_,?_⟩
  · exact contDiffAt_pi.mpr fun a => (contDiffAt_pi.mp hη a).div hexp (Real.exp_ne_zero _)
  · exact contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b =>
      (contDiffAt_pi.mp (contDiffAt_pi.mp hτ a) b).div (hexp.pow 2) (by positivity)

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma sourceAspect_smoothAt {f : SourceMassFields} {x : Angle}
    (hσ : ContDiffAt ℝ ∞ f.sigma x) (hg : ContDiffAt ℝ ∞ f.mg x)
    (hk : ContDiffAt ℝ ∞ f.mK x) (hr : ContDiffAt ℝ ∞ f.mr x)
    (hs : determinant (f.sigma x) ≠ 0) : ContDiffAt ℝ ∞ (sourceAspect f) x := by
  have hi : ContDiffAt ℝ ∞ (fun y : Angle => inverse (f.sigma y)) x := inverse_smoothAt hσ hs
  have hm : ContDiffAt ℝ ∞ (fun y : Angle => f.mg y+(2:ℝ) • f.mK y) x :=
    hg.add ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Angle => (2:ℝ)) x).smul hk)
  have ht := traceProduct_smoothAt hi hm
  exact ht.add (contDiffAt_const.mul hr)

lemma sourceCollar_sigma_radial {f : SourceTensorFields} {x : Point}
    (hf : f.base.RegularAt (logRadiusChart x)) :
    ∀ i j, D (CKSRealizedRound.basis 0)
      (fun z => (sourceCollarData f.logFields).sigma z i j) x=0 := by
  have hs := hf.sigma
  rw [angularProjection_logRadiusChart] at hs
  intro i j
  exact D_angularLift ((contDiffAt_pi.mp (contDiffAt_pi.mp hs i) j).differentiableAt (by norm_num))

lemma sourceCollar_sigma_radial_eventually {f : SourceTensorFields} {x : Point}
    (hf : f.base.RegularAt (logRadiusChart x)) :
    ∀ᶠ y in 𝓝 x, ∀ i j, D (CKSRealizedRound.basis 0)
      (fun z => (sourceCollarData f.logFields).sigma z i j) y=0 := by
  filter_upwards [(logRadiusChart_smooth.continuous.continuousAt (x:=x)).tendsto.eventually hf.eventually]
    with y hy
  exact sourceCollar_sigma_radial hy

lemma sourceCollar_fstar_radial {f : SourceTensorFields} {x : Point}
    (hf : f.base.SmoothAt (logRadiusChart x))
    (hs : determinant (f.base.logFields.sigma x) ≠ 0) :
    D (CKSRealizedRound.basis 0) (sourceCollarData f.logFields).fstar x=0 := by
  change D (basis 0) (cksLeadingField f.base.logFields) x=0
  rw [source_leading_mass]
  have hσ := hf.sigma
  have hg := hf.mg
  have hk := hf.mK
  have hr := hf.mr
  rw [angularProjection_logRadiusChart] at hσ hg hk hr
  exact D_angularLift (((sourceAspect_smoothAt hσ hg hk hr hs).div_const 4).differentiableAt (by simp))

lemma sourceCollar_metricError_hermitian {f : SourceTensorFields} {x : Point}
    (hp : (sourceMetric f.base (logRadiusChart x)).PosDef)
    (hs : (f.base.sigma (angularProjection x)).IsHermitian) :
    ((sourceCollarData f.logFields).metricError x).IsHermitian := by
  change (logQError f.base.logFields x).IsHermitian
  rw [logQError_scaled]
  have hγ := (metricBlock_leaf_posDef hp).isHermitian
  change (sourceGamma f.base (logRadiusChart x)).IsHermitian at hγ
  rw [congrFun (sourceGamma_pullback f.base) x] at hγ
  exact (hγ.smul (by rfl)).sub hs

lemma sourceCollar_tau_hermitian {f : SourceTensorFields} {x : Point}
    (hp : (sourceMetric f.base (logRadiusChart x)).PosDef)
    (hk : (sourceTangentialK f.base (logRadiusChart x)).IsHermitian) :
    ((sourceCollarData f.logFields).tauDivR2 x).IsHermitian := by
  have he : (sourceCollarData f.logFields).tauDivR2 x=
      (1/Real.exp (x 0)^2) • sourceOriginalTau f (logRadiusChart x) := by
    rw [congrFun (sourceOriginalTau_pullback f) x]
    ext i j
    change logOriginalTau f.logFields x i j / Real.exp (x 0)^2 =
      (1/Real.exp (x 0)^2) * logOriginalTau f.logFields x i j
    ring
  rw [he]
  exact (hk.sub ((metricBlock_leaf_posDef hp).isHermitian.smul (by rfl))).smul (by rfl)

lemma sourceCollar_symmetries {f : SourceTensorFields} {x : Point}
    (hp : ∀ᶠ y in 𝓝 (logRadiusChart x), (sourceMetric f.base y).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (f.base.sigma (angularProjection y)).IsHermitian)
    (hk : ∀ᶠ y in 𝓝 (logRadiusChart x), (sourceTangentialK f.base y).IsHermitian) :
    (∀ᶠ y in 𝓝 x, ((sourceCollarData f.logFields).sigma y).IsHermitian) ∧
    (∀ᶠ y in 𝓝 x, ((sourceCollarData f.logFields).metricError y).IsHermitian) ∧
    (∀ᶠ y in 𝓝 x, ((sourceCollarData f.logFields).tauDivR2 y).IsHermitian) := by
  have hc := logRadiusChart_smooth.continuous.continuousAt (x:=x)
  have hp' := hc.tendsto.eventually hp
  have hk' := hc.tendsto.eventually hk
  refine ⟨hs,?_,?_⟩
  · filter_upwards [hp',hs] with y hyp hys
    exact sourceCollar_metricError_hermitian hyp hys
  · filter_upwards [hp',hk'] with y hyp hyk
    exact sourceCollar_tau_hermitian hyp hyk

end
end CKSMixedGeometry

end



noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarQ_hermitian {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hσ : (f.sigma (slice ρ a)).IsHermitian)
    (he : (f.metricError (slice ρ a)).IsHermitian) :
    (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a).IsHermitian := by
  have hs' : (f.sigma (radiusLogPoint (slice (Real.exp ρ) a))).IsHermitian := by simpa using hσ
  have he' : (f.metricError (radiusLogPoint (slice (Real.exp ρ) a))).IsHermitian := by simpa using he
  have h := (physicalCollarGamma_isHermitian R f (slice (Real.exp ρ) a) hs' he').smul
    (show star (1/Real.exp ρ^2)=1/Real.exp ρ^2 by rfl)
  rw [physicalCollarGamma_slice,smul_smul,one_div_mul_cancel (by positivity : Real.exp ρ^2 ≠ 0),one_smul] at h
  exact h

lemma physical_collar_pivots {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a))
    (hσ : ∀ᶠ y in 𝓝 (slice ρ a), (f.sigma y).IsHermitian)
    (he : ∀ᶠ y in 𝓝 (slice ρ a), (f.metricError y).IsHermitian)
    (hσD : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hq : positiveAngular (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a))
    (hu : 0 < lapseRadField (1/Real.exp ρ)
      (fieldT (collarParams R (Real.exp ρ)) (f.angular ρ))
      (fieldF (collarParams R (Real.exp ρ)) (f.angular ρ)) a)
    (hd : 0 < lapseDField (1/Real.exp ρ)
      (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a) :
    (∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef) ∧
      0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a) ∧
      0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a) := by
  have hpq := positiveAngular_posDef (physicalCollarQ_hermitian hσ.self_of_nhds he.self_of_nhds) hq
  have hp := (physicalCollarGamma_pos_iff R ρ f a).mpr hpq
  refine ⟨?_,?_,(physicalCollarRadical_pos_iff R ρ f a).mpr hu⟩
  · apply physicalCollarGamma_eventually_posDef (by simp) (by simpa using hf)
      (by simpa using hσ) (by simpa using he) hp
  · rw [physicalCollarExpansion_slice R ρ hf.regularAt hσD hp]
    exact hd

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physical_source_collar_old_DEC {R ρ : ℝ} {f : SourceTensorFields} {x : AP}
    (hf : f.SmoothAt (logRadiusChart (slice ρ x)))
    (hp : ∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef)
    (hσ : ∀ᶠ y in 𝓝 (slice ρ x), (f.base.sigma (angularProjection y)).IsHermitian)
    (hk : ∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceTangentialK f.base y).IsHermitian)
    (hs : determinant (f.base.logFields.sigma (slice ρ x)) ≠ 0)
    (hq : positiveAngular (fieldQ (oldParams (collarParams R (Real.exp ρ)))
      ((sourceCollarData f.logFields).angular ρ) x))
    (hu : 0 < lapseRadField (1/Real.exp ρ)
      (fieldT (oldParams (collarParams R (Real.exp ρ))) ((sourceCollarData f.logFields).angular ρ))
      (fieldF (oldParams (collarParams R (Real.exp ρ))) ((sourceCollarData f.logFields).angular ρ)) x)
    (hd : 0 < lapseDField (1/Real.exp ρ)
      (fieldD (oldParams (collarParams R (Real.exp ρ))) ((sourceCollarData f.logFields).angular ρ)) x)
    (hDEC : physicalDEC (sourceMetric f.base) (sourceTensor f) (sourceFrame f.base)
      (logRadiusChart (slice ρ x))) :
    coordinateDEC (fieldNullInput (oldParams (collarParams R (Real.exp ρ)))
      ((sourceCollarData f.logFields).angular ρ) x) (Real.exp ρ) := by
  let S := 2*Real.exp ρ
  have hS : 0 < S := by dsimp [S]; positivity
  have hi : Real.exp ρ < S := by dsimp [S]; linarith [Real.exp_pos ρ]
  have heq : collarParams S (Real.exp ρ)=oldParams (collarParams R (Real.exp ρ)) :=
    collarParams_initial hS hi.le
  have hc := sourceCollarData_smoothAt hf hp hs
  obtain ⟨hσh,heh,hτh⟩ := sourceCollar_symmetries hp hσ hk
  have hσD := sourceCollar_sigma_radial_eventually hf.base.regularAt
  have hstar := sourceCollar_fstar_radial hf.base hs
  obtain ⟨hγ,hd',hu'⟩ := physical_collar_pivots (R:=S) hc hσh heh hσD.self_of_nhds
    (by rw [heq]; exact hq) (by rw [heq]; exact hu) (by rw [heq]; exact hd)
  have hr : 0 < (slice (Real.exp ρ) x) 0 := by simpa using Real.exp_pos ρ
  have hi' : (slice (Real.exp ρ) x) 0 < S := by simpa using hi
  have hf' : f.SmoothAt (slice (Real.exp ρ) x) := by simpa using hf
  have hp' : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) x), (sourceMetric f.base y).PosDef := by simpa using hp
  have hfields := source_inner_collar_fields_eventually hr hi' hf'.base.regularAt hp'
  have hexp := radialExpansion_congr (hfields.mono (fun _ h => h.1)) (hfields.mono (fun _ h => h.2.1))
  rw [source_radialExpansion_eq] at hexp
  have hdSource : 0 < sourceExpansion f.base (slice (Real.exp ρ) x) := by
    rw [← hexp]; exact hd'
  have hdS := ((sourceExpansion_smoothAt hf'.base hr.ne' hp'.self_of_nhds).continuousAt).eventually
    (Ioi_mem_nhds hdSource)
  have hphysical := (physical_source_inner_collar_DEC_iff hr hi' hf'.base.regularAt hp' hdS
    (by simpa using hk)).mpr (by simpa using hDEC)
  have hh := (physical_collar_DEC_iff hS hc hσD hstar hτh hγ hd' hu').mp hphysical
  rwa [heq] at hh

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem source_actual_collar_physical_DEC {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
      f.SmoothAt (logRadiusChart (slice ρ x)) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef) →
      (∀ᶠ y in 𝓝 (slice ρ x), (f.base.sigma (angularProjection y)).IsHermitian) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceTangentialK f.base y).IsHermitian) →
      matrixThreeJets (angularLift f.base.sigma) (slice ρ x) ∈ K →
      ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ x)‖ ≤ B →
      ‖matrixThreeJets (angularLift f.base.mg) (slice ρ x)‖ ≤ B →
      ‖matrixScalarJets (angularLift f.base.mK) (slice ρ x)‖ ≤ B →
      ‖actualScalarJet (angularLift f.base.mr) (slice ρ x)‖ ≤ B →
      f.ComponentBounds B (logRadiusChart (slice ρ x)) →
      physicalDEC (sourceMetric f.base) (sourceTensor f) (sourceFrame f.base)
        (logRadiusChart (slice ρ x)) →
      physicalDEC (physicalCollarMetric R (sourceCollarData f.logFields))
        (physicalCollarTensor R (sourceCollarData f.logFields))
        (physicalCollarFrame R (sourceCollarData f.logFields)) (slice (Real.exp ρ) x)
 := by
  obtain ⟨A,hA,hcoord⟩ := source_actual_collar_coordinate_DEC hK hreg hB
  obtain ⟨C,hC,hfuture⟩ := source_actual_collar_future_regions hK hreg hB
  refine ⟨max A C,hA.trans (le_max_left _ _),?_⟩
  intro R f ρ x hR hr htop hf hp hσ hk hmem hs hmg hmk hmr hb hDEC
  have hRA : A ≤ R := (le_max_left _ _).trans hR
  have hRC : C ≤ R := (le_max_right _ _).trans hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (hA.trans hRA)
  obtain ⟨⟨hq,hu,hd⟩,⟨hoq,hou,hod⟩⟩ := hfuture R f ρ x hRC hr htop hf hp hmem hs hmg hmk hmr hb
  have hdet : determinant (f.base.logFields.sigma (slice ρ x)) ≠ 0 := by
    rw [determinant_eq]
    exact (hreg _ hmem).det_pos.ne'
  have hold := physical_source_collar_old_DEC hf hp hσ hk hdet hoq hou hod hDEC
  have hmk' := hf.base.mK.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hek := hf.base.ek.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hnew := hcoord R f ρ x hRA hr htop hf.regularAt hmk' hek hp hmem hs hmg hmk hmr hb hold
  have hc := sourceCollarData_smoothAt hf hp hdet
  obtain ⟨hσh,heh,hτh⟩ := sourceCollar_symmetries hp hσ hk
  have hσD := sourceCollar_sigma_radial_eventually hf.base.regularAt
  have hstar := sourceCollar_fstar_radial hf.base hdet
  obtain ⟨hγ,hd',hu'⟩ := physical_collar_pivots hc hσh heh hσD.self_of_nhds hq hu hd
  exact (physical_collar_DEC_iff hRpos hc hσD hstar hτh hγ hd' hu').mpr hnew

end
end CKSMixedGeometry

end


noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma foliationTensor_contDiffAt {U L : PhysicalPoint → ℝ}
    {η s : PhysicalPoint → Point} {kT : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hk : ContDiffAt ℝ ∞ kT x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => foliationTensor (U y) (L y) (η y) (kT y) (s y)) x := by
  have hkc (i j) : ContDiffAt ℝ ∞ (fun y => kT y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hk i) j
  have hsc (i) : ContDiffAt ℝ ∞ (fun y => s y i) x := contDiffAt_pi.mp hs i
  have hηc (i) : ContDiffAt ℝ ∞ (fun y => η y i) x := contDiffAt_pi.mp hη i
  have hrr : ContDiffAt ℝ ∞
      (fun y => L y/(U y)^2+2/U y*(∑ a, η y a*s y a)+∑ a, ∑ b, kT y a b*s y a*s y b) x :=
    ((hL.div (hU.pow 2) (pow_ne_zero _ h0)).add
      ((contDiffAt_const.div hU h0).mul (ContDiffAt.sum (fun a _ => (hηc a).mul (hsc a))))).add
      (ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ => ((hkc a b).mul (hsc a)).mul (hsc b))))
  have hm (a) : ContDiffAt ℝ ∞ (fun y => η y a/U y+∑ b, kT y a b*s y b) x :=
    ((hηc a).div hU h0).add (ContDiffAt.sum (fun b _ => (hkc a b).mul (hsc b)))
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hrr
  · exact hm 0
  · exact hm 1
  · exact hm 0
  · exact hkc 0 0
  · exact hkc 0 1
  · exact hm 1
  · exact hkc 1 0
  · exact hkc 1 1

lemma physical_collar_regularAt {R : ℝ} (hR : 0 < R) {f : LogCollarData} {x : PhysicalPoint}
    (hr : 0 < x 0) (hf : f.SmoothAt (radiusLogPoint x))
    (hγ : (physicalCollarGamma R f x).PosDef)
    (hτ : (f.tauDivR2 (radiusLogPoint x)).IsHermitian)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) x)
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) x) :
    PhysicalRegularAt (physicalCollarMetric R f) (physicalCollarTensor R f) x := by
  have hU : ContDiffAt ℝ ∞ (physicalCollarU R f) x :=
    physicalCollarU_smoothAt hR hr.ne' hf hγ hd.ne' hu.ne'
  have hU0 : physicalCollarU R f x ≠ 0 := (radialMassLapse_pos hd hu).ne'
  have hγs := physicalCollarGamma_smoothAt R hr.ne' hf
  have hss := physicalCollarShift_smoothAt R hr.ne' hf
  refine ⟨foliationMetric_contDiffAt hU hγs hss hU0,?_,foliationMetric_posDef hU0 hγ _,?_⟩
  · exact foliationTensor_contDiffAt hU (physicalCollarL_smoothAt R hr.ne' hf)
      (physicalCollarEta_smoothAt R hr.ne' hf) (physicalCollarTangential_smoothAt R hr.ne' hf hγ) hss hU0
  · unfold physicalCollarTensor foliationTensor
    exact metricBlock_hermitian _ _ (physicalCollarTangential_isHermitian R f x hγ.isHermitian hτ)
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem source_actual_collar_regular {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
      f.SmoothAt (logRadiusChart (slice ρ x)) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef) →
      (∀ᶠ y in 𝓝 (slice ρ x), (f.base.sigma (angularProjection y)).IsHermitian) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceTangentialK f.base y).IsHermitian) →
      matrixThreeJets (angularLift f.base.sigma) (slice ρ x) ∈ K →
      ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ x)‖ ≤ B →
      ‖matrixThreeJets (angularLift f.base.mg) (slice ρ x)‖ ≤ B →
      ‖matrixScalarJets (angularLift f.base.mK) (slice ρ x)‖ ≤ B →
      ‖actualScalarJet (angularLift f.base.mr) (slice ρ x)‖ ≤ B →
      f.ComponentBounds B (logRadiusChart (slice ρ x)) →
      PhysicalRegularAt (physicalCollarMetric R (sourceCollarData f.logFields))
        (physicalCollarTensor R (sourceCollarData f.logFields)) (slice (Real.exp ρ) x)
 := by
  obtain ⟨C,hC,hfuture⟩ := source_actual_collar_future_regions hK hreg hB
  refine ⟨C,hC,?_⟩
  intro R f ρ x hR hr htop hf hp hσ hk hmem hs hmg hmk hmr hb
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (hC.trans hR)
  obtain ⟨⟨hq,hu,hd⟩,_⟩ := hfuture R f ρ x hR hr htop hf hp hmem hs hmg hmk hmr hb
  have hdet : determinant (f.base.logFields.sigma (slice ρ x)) ≠ 0 := by
    rw [determinant_eq]
    exact (hreg _ hmem).det_pos.ne'
  have hc := sourceCollarData_smoothAt hf hp hdet
  obtain ⟨hσh,heh,hτh⟩ := sourceCollar_symmetries hp hσ hk
  have hσD := sourceCollar_sigma_radial_eventually hf.base.regularAt
  obtain ⟨hγ,hd',hu'⟩ := physical_collar_pivots hc hσh heh hσD.self_of_nhds hq hu hd
  apply physical_collar_regularAt hRpos (by simpa using Real.exp_pos ρ)
    (by simpa using hc) hγ.self_of_nhds
    (by simpa using hτh.self_of_nhds) hd' hu'

end
end CKSMixedGeometry

end






noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma CollarSourcePatch.sigma_eventually {A B : SpatialTensor} (P : CollarSourcePatch A B)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ P.region) :
    ∀ᶠ z in 𝓝 y, (P.fields.base.sigma (angularProjection z)).IsHermitian := by
  filter_upwards [angularProjection.continuous.continuousAt.preimage_mem_nhds
    (P.region_open.mem_nhds hy)] with z hz
  exact (P.patch.roundMetric_posDef (P.region_target hz)).isHermitian
lemma SourceCollarAtlas.positive_eventually {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region) :
    ∀ᶠ z in 𝓝 y, (sourceMetric (q.patch i).fields.base z).PosDef := by
  filter_upwards [(angularRadialTail_open q.radius (q.patch i).region_open).mem_nhds hy] with z hz
  exact q.source_positive i z hz
lemma SourceCollarAtlas.symmetric_eventually {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region) :
    ∀ᶠ z in 𝓝 y, (sourceTangentialK (q.patch i).fields.base z).IsHermitian := by
  filter_upwards [(angularRadialTail_open q.radius (q.patch i).region_open).mem_nhds hy] with z hz
  exact q.source_symmetric i z hz
lemma slice_exp_log_projection {y : CKSMixedGeometry.Point} (hy : 0 < y 0) :
    slice (Real.exp (Real.log (y 0))) (angularProjection y) = y := by
  rw [Real.exp_log hy,slice_projection]
lemma logRadiusChart_slice_exp (ρ : ℝ) (a : Angle) :
    logRadiusChart (slice ρ a) = slice (Real.exp ρ) a := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [logRadiusChart]
  · simp [logRadiusChart,Fin.succ_ne_zero]

theorem SourceCollarAtlas.eventually_pointwise {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ q.radius < R₀ ∧ ∀ R ≥ R₀, ∀ i y,
      R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
      PhysicalRegularAt (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields)) y ∧
      physicalDEC (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) y := by
  obtain ⟨R₁,hR₁,hreg⟩ := source_actual_collar_regular q.jetSet_compact q.jetSet_positive q.bound_nonneg
  obtain ⟨R₂,hR₂,hDEC⟩ := source_actual_collar_physical_DEC q.jetSet_compact q.jetSet_positive q.bound_nonneg
  refine ⟨max (max R₁ R₂) (q.radius+1),hR₁.trans ((le_max_left _ _).trans (le_max_left _ _)),?_,?_⟩
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  intro R hR i y hr ht hw
  have hR1 : R₁ ≤ R := ((le_max_left _ _).trans (le_max_left _ _)).trans hR
  have hR2 : R₂ ≤ R := ((le_max_right _ _).trans (le_max_left _ _)).trans hR
  have hr0 : 0 < y 0 := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (hR₁.trans hR1)) hr
  have hrad : q.radius < y 0 := lt_of_lt_of_le
    ((show q.radius < q.radius+1 by linarith).trans_le ((le_max_right _ _).trans hR)) hr
  have hx : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨hrad,hw⟩
  have hlog : logRadiusChart (slice (Real.log (y 0)) (angularProjection y)) = y :=
    (logRadiusChart_slice_exp _ _).trans (slice_exp_log_projection hr0)
  have hf := q.source_smooth i y hx
  have hp := q.positive_eventually i hx
  have hk := q.symmetric_eventually i hx
  have hσ := (q.patch i).sigma_eventually (y := slice (Real.log (y 0)) (angularProjection y))
    (by simpa only [angularProjection_slice] using hw)
  obtain ⟨hm,h1,h2,h3,h4,hb⟩ := q.bounds i (angularProjection y) hw (Real.log (y 0))
  have hb' := hb (by rwa [Real.exp_log hr0])
  rw [hlog] at hb'
  constructor
  · have h := hreg R (q.patch i).fields (Real.log (y 0)) (angularProjection y) hR1
      (by rwa [Real.exp_log hr0]) (by rwa [Real.exp_log hr0])
      (by rwa [hlog]) (by rwa [hlog]) hσ (by rwa [hlog]) hm h1 h2 h3 h4
      (by rwa [hlog])
    simpa only [slice_exp_log_projection hr0] using h
  · have h := hDEC R (q.patch i).fields (Real.log (y 0)) (angularProjection y) hR2
      (by rwa [Real.exp_log hr0]) (by rwa [Real.exp_log hr0])
      (by rwa [hlog]) (by rwa [hlog]) hσ (by rwa [hlog]) hm h1 h2 h3 h4
      (by rwa [hlog]) (by rw [hlog]; exact q.source_DEC i y hx)
    simpa only [slice_exp_log_projection hr0] using h
end
end CKSLorentz

end















end OAI
end

theorem solution.{u_1} : type_of% @OAI.CKSLorentz.SourceCollarAtlas.eventually_pointwise.{u_1} := @OAI.CKSLorentz.SourceCollarAtlas.eventually_pointwise.{u_1}
