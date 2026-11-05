-- Prove2me | solution 1 for OAI.CKSLorentz.hyperbolic_source_geometry
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:53:54.847387+00:00
-- url     : https://prove2.me/submissions/1158de68-b066-4bcc-9a04-83a6f5e45b29

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

set_option linter.all false

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

lemma contDiffAt_D {f : E → ℝ} {x : E} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f x)
    {m : ℕ∞ω} (hmn : m + 1 ≤ n) (e : E) : ContDiffAt ℝ m (D e f) x :=
  (hf.fderiv_right hmn).clm_apply contDiffAt_const

lemma D_D {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (e w : E) :
    D w (D e f) x = fderiv ℝ (fderiv ℝ f) x w e := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold D
  rw [fderiv_clm_apply hd (differentiableAt_const e)]
  simp

lemma D_comm {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (e w : E) :
    D w (D e f) x = D e (D w f) x := by
  rw [D_D hf, D_D hf]
  exact hf.isSymmSndFDerivAt (by simp) w e

lemma diffAt_div {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (h0 : g x ≠ 0) :
    DifferentiableAt ℝ (fun y => f y / g y) x := by
  have hgi : DifferentiableAt ℝ (fun y => (g y)⁻¹) x := hg.inv h0
  simpa only [div_eq_mul_inv] using
    (show DifferentiableAt ℝ (fun y => f y * (g y)⁻¹) x from hf.fun_mul hgi)

end
end CKSCalculus

end









end OAI
end

section
namespace OAI

noncomputable section
namespace CKSFrame
noncomputable section
open scoped BigOperators
abbrev Coefficients := I → I → I → ℝ

def koszul (b : Coefficients) (i j k : I) : ℝ :=
  (b i j k-b j k i+b k i j)/2

end
end CKSFrame

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

lemma foliationNormal_unit {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.IsHermitian) (s : Point) :
    star (foliationNormal U s) ⬝ᵥ (foliationMetric U γ s *ᵥ foliationNormal U s)=1 := by
  rw [foliationMetric_quadratic U hγ s]
  have hy : (fun a : Fin 2 => foliationNormal U s a.succ+s a*foliationNormal U s 0)=0 := by
    ext a; fin_cases a <;> simp [foliationNormal,mul_comm]
  rw [hy]
  simp [foliationNormal,hU]

lemma foliationNormal_orthogonal {U : ℝ} (_hU : U ≠ 0) {γ : Mat} (_hγ : γ.IsHermitian)
    (s : Point) (a : Fin 2) :
    ∑ j : Fin 3, foliationMetric U γ s a.succ j*foliationNormal U s j=0 := by
  fin_cases a <;> norm_num [Fin.succ,Fin.sum_univ_three,foliationMetric,metricBlock,Matrix.of_apply,foliationNormal,
    Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.head_fin_const,Matrix.tail_cons,Matrix.cons_val_fin_one] <;> ring

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
open scoped BigOperators Topology

lemma christoffel_lowered {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hG : (G x).PosDef) (i j k : Fin 3) :
    (∑ l, coordinateChristoffel G x i j l * G x l k) =
      lowerKoszul (actualMetricFirstJet G x) i j k := by
  simp only [coordinateChristoffel, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hi := Matrix.nonsing_inv_mul (G x) (isUnit_iff_ne_zero.mpr hG.det_pos.ne')
  change (∑ l, lowerKoszul (actualMetricFirstJet G x) i j l * ((G x)⁻¹ * G x) l k) = _
  rw [hi]
  change (∑ l, lowerKoszul (actualMetricFirstJet G x) i j l * (if l=k then 1 else 0)) = _
  simp

lemma actualMetricFirstJet_symmetric {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hG : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (i j k : Fin 3) :
    actualMetricFirstJet G x i j k = actualMetricFirstJet G x i k j := by
  apply D_congr
  filter_upwards [hG] with y hy
  exact (hermitian_real_symmetry hy j k).symm

lemma coordinateChristoffel_torsion {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hG : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (i j k : Fin 3) :
    coordinateChristoffel G x i j k = coordinateChristoffel G x j i k := by
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  unfold lowerKoszul
  rw [actualMetricFirstJet_symmetric hG l j i]
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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology

lemma D_sum3 (e : PhysicalPoint) {x : PhysicalPoint} (f : Fin 3 → PhysicalPoint → ℝ)
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    D e (fun y => ∑ i, f i y) x = ∑ i, D e (f i) x := by
  simp only [D, fderiv_fun_sum (fun i _ => hf i), _root_.sum_apply]

lemma D_direction_expansion (e x : PhysicalPoint) (f : PhysicalPoint → ℝ) :
    D e f x = ∑ i, e i*D (CKSRealizedRound.basis i) f x := by
  unfold D
  conv_lhs => rw [direction_expansion e]
  simp

lemma D_metricPair (e : PhysicalPoint) {G : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hg : DifferentiableAt ℝ G x) (hv : DifferentiableAt ℝ V x)
    (hw : DifferentiableAt ℝ W x) :
    D e (fun y => metricPair (G y) (V y) (W y)) x =
      ∑ i, ∑ j, (D e (fun y => G y i j) x*V x i*W x j +
        G x i j*D e (fun y => V y i) x*W x j+
        G x i j*V x i*D e (fun y => W y j) x) := by
  have hgc (i j) : DifferentiableAt ℝ (fun y => G y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hg i) j
  have hvc (i) : DifferentiableAt ℝ (fun y => V y i) x := differentiableAt_pi.mp hv i
  have hwc (i) : DifferentiableAt ℝ (fun y => W y i) x := differentiableAt_pi.mp hw i
  have ht (i j) : DifferentiableAt ℝ (fun y => G y i j*V y i*W y j) x :=
    ((hgc i j).fun_mul (hvc i)).fun_mul (hwc j)
  have hsum (i) : DifferentiableAt ℝ (fun y => ∑ j, G y i j*V y i*W y j) x :=
    DifferentiableAt.fun_sum (fun j _ => ht i j)
  unfold metricPair
  rw [D_sum3 e _ hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [D_sum3 e _ (ht i)]
  apply Finset.sum_congr rfl
  intro j _
  rw [D_mul e ((hgc i j).fun_mul (hvc i)) (hwc j), D_mul e (hgc i j) (hvc i)]
  ring

lemma covariantVector_lowered {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : (G x).PosDef) (e : PhysicalPoint) (W : PhysicalPoint → PhysicalPoint) (k : Fin 3) :
    (∑ l, covariantVector G e W x l * G x l k) =
      (∑ l, D e (fun y => W y l) x * G x l k) +
      ∑ i, ∑ j, e i * W x j * lowerKoszul (actualMetricFirstJet G x) i j k := by
  simp only [covariantVector, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [christoffel_lowered hg]

lemma metricPair_symm {g : AmbientMat} (hg : g.IsHermitian) (v w : PhysicalPoint) :
    metricPair g v w=metricPair g w v := by
  unfold metricPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hermitian_real_symmetry hg i j]
  ring

lemma metricPair_covariant {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : (G x).PosDef) (e w : PhysicalPoint) (V : PhysicalPoint → PhysicalPoint) :
    metricPair (G x) (covariantVector G e V x) w =
      (∑ k, (∑ l, D e (fun y => V y l) x * G x l k) * w k) +
      ∑ k, (∑ i, ∑ j, e i * V x j * lowerKoszul (actualMetricFirstJet G x) i j k) * w k := by
  unfold metricPair
  rw [Finset.sum_comm]
  simp_rw [mul_comm (G x _ _) (covariantVector G e V x _), ← Finset.sum_mul,
    covariantVector_lowered hg]
  simp [add_mul, Finset.sum_add_distrib]

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
open scoped BigOperators Topology

lemma covariantVector_metric {G : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hg : DifferentiableAt ℝ G x) (hv : DifferentiableAt ℝ V x)
    (hw : DifferentiableAt ℝ W x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (e : PhysicalPoint) :
    D e (fun y => metricPair (G y) (V y) (W y)) x =
      metricPair (G x) (covariantVector G e V x) (W x) +
      metricPair (G x) (V x) (covariantVector G e W x) := by
  rw [D_metricPair e hg hv hw,
    metricPair_symm hp.isHermitian (V x) (covariantVector G e W x),
    metricPair_covariant hp, metricPair_covariant hp]
  have hd (i j) : D e (fun y => G y i j) x =
      ∑ a, e a * actualMetricFirstJet G x a i j := D_direction_expansion e x _
  simp_rw [hd]
  simp only [Fin.sum_univ_three, lowerKoszul]
  simp only [hermitian_real_symmetry hp.isHermitian 0 1,
    hermitian_real_symmetry hp.isHermitian 0 2,
    hermitian_real_symmetry hp.isHermitian 1 2,
    actualMetricFirstJet_symmetric hs 0 1 0,
    actualMetricFirstJet_symmetric hs 0 2 0,
    actualMetricFirstJet_symmetric hs 0 2 1,
    actualMetricFirstJet_symmetric hs 1 1 0,
    actualMetricFirstJet_symmetric hs 1 2 0,
    actualMetricFirstJet_symmetric hs 1 2 1,
    actualMetricFirstJet_symmetric hs 2 1 0,
    actualMetricFirstJet_symmetric hs 2 2 0,
    actualMetricFirstJet_symmetric hs 2 2 1]
  ring

lemma frameCoefficient_metric {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : DifferentiableAt ℝ G x)
    (he : ∀ i, DifferentiableAt ℝ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0)
    (i j k : Fin 3) : frameCoefficient G E x i j k = -frameCoefficient G E x i k j := by
  have h := covariantVector_metric hg (he j) (he k) hp hs (E i x)
  have hd : D (E i x) (fun y => metricPair (G y) (E j y) (E k y)) x=0 := by
    rw [D_congr (ho.mono (fun _ hy => hy j k)) (E i x)]
    exact D_const _ _ _
  rw [hd, metricPair_symm hp.isHermitian (E j x)] at h
  change 0=frameCoefficient G E x i j k+frameCoefficient G E x i k j at h
  linarith

lemma covariantVector_torsion {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (i j : Fin 3) :
    (fun k => covariantVector G (E i x) (E j) x k - covariantVector G (E j x) (E i) x k) =
      actualFrameBracket E x i j := by
  ext k
  have hsum : (∑ a, ∑ b, E i x a * E j x b * coordinateChristoffel G x a b k) =
      ∑ a, ∑ b, E j x a * E i x b * coordinateChristoffel G x a b k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [coordinateChristoffel_torsion hs b a]
    ring
  dsimp [covariantVector,actualFrameBracket]
  rw [hsum]
  ring

lemma frameCoefficient_torsion {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (i j k : Fin 3) :
    frameCoefficient G E x i j k-frameCoefficient G E x j i k=frameBracketCoefficient G E x i j k := by
  unfold frameBracketCoefficient
  rw [← covariantVector_torsion hs i j]
  simp only [frameCoefficient,metricPair,mul_sub,sub_mul,Finset.sum_sub_distrib]

theorem physical_frame_koszul {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : DifferentiableAt ℝ G x)
    (he : ∀ i, DifferentiableAt ℝ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0) :
    frameCoefficient G E x = CKSFrame.koszul (frameBracketCoefficient G E x) := by
  funext i j k
  have h1 := frameCoefficient_torsion (E := E) hs i j k
  have h2 := frameCoefficient_torsion (E := E) hs j k i
  have h3 := frameCoefficient_torsion (E := E) hs k i j
  have hm1 := frameCoefficient_metric hg he hp hs ho i k j
  have hm2 := frameCoefficient_metric hg he hp hs ho j i k
  have hm3 := frameCoefficient_metric hg he hp hs ho k j i
  unfold CKSFrame.koszul
  linarith

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
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma orthonormal_frame_inverse {g : AmbientMat} {e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    (g*(Matrix.transpose e))*e=1 := by
  have hh : e*(g*Matrix.transpose e)=1 := by
    ext i j
    change (∑ k, e i k * ∑ l, g k l*e j l) = if i=j then 1 else 0
    rw [← ho i j]
    simp only [metricPair, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  exact mul_eq_one_comm.mp hh

lemma orthonormal_frame_expansion {g : AmbientMat} {e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0)
    (v : PhysicalPoint) (j : Fin 3) :
    ∑ a, metricPair g v (e a)*e a j=v j := by
  have hm := orthonormal_frame_inverse ho
  calc
    _ = ∑ k, v k*((g*Matrix.transpose e)*e) k j := by
      simp only [metricPair, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ k, v k*(if k=j then 1 else 0) := by rw [hm]; rfl
    _ = v j := by simp

lemma metricPair_frame_left (k : AmbientMat) {g : AmbientMat}
    {e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0)
    (v w : PhysicalPoint) :
    ∑ a, metricPair g v (e a)*metricPair k (e a) w=metricPair k v w := by
  calc
    _ = ∑ i, ∑ j, k i j*(∑ a, metricPair g v (e a)*e a i)*w j := by
      simp only [metricPair, Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = metricPair k v w := by simp_rw [orthonormal_frame_expansion ho]; rfl

lemma metricPair_frame_right (k : AmbientMat) {g : AmbientMat}
    {e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0)
    (v w : PhysicalPoint) :
    ∑ a, metricPair g v (e a)*metricPair k w (e a)=metricPair k w v := by
  calc
    _ = ∑ i, ∑ j, k i j*w i*(∑ a, metricPair g v (e a)*e a j) := by
      simp only [metricPair, Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = metricPair k w v := by simp_rw [orthonormal_frame_expansion ho]; rfl

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
open Matrix Filter CKSCalculus
open scoped BigOperators Topology ContDiff

lemma metricPair_foliationNormal {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.IsHermitian)
    (s : Point) : metricPair (foliationMetric U γ s) (foliationNormal U s) (foliationNormal U s)=1 := by
  have h := foliationNormal_unit hU hγ s
  simpa only [metricPair,dotProduct,mulVec,star_apply,star_trivial,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc] using h

lemma metricPair_normal_tangent {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.IsHermitian)
    (s : Point) (v : PhysicalPoint) (hv : v 0=0) :
    metricPair (foliationMetric U γ s) v (foliationNormal U s)=0 := by
  unfold metricPair
  apply Finset.sum_eq_zero
  intro i _
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [hv]
  · calc
      _ = v a.succ * ∑ j, foliationMetric U γ s a.succ j * foliationNormal U s j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [foliationNormal_orthogonal hU hγ s a]; ring

lemma adaptedFrame_radial (U : ℝ) (γ : Mat) (s : Point) (a : Fin 2) :
    adaptedFrame U γ s a.succ 0=0 := by fin_cases a <;> rfl

lemma metricPair_tangent_expanded (U : ℝ) (γ : Mat) (s : Point)
    (v w : PhysicalPoint) (hv : v 0=0) (hw : w 0=0) :
    metricPair (foliationMetric U γ s) v w =
      γ 0 0*v 1*w 1+γ 0 1*v 1*w 2+(γ 1 0*v 2*w 1+γ 1 1*v 2*w 2) := by
  simp only [metricPair, Fin.sum_univ_three, hv, hw, mul_zero, zero_mul, zero_add, add_zero]
  rfl

lemma adaptedFrame_orthonormal {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.PosDef)
    (s : Point) (i j : Fin 3) :
    metricPair (foliationMetric U γ s) (adaptedFrame U γ s i) (adaptedFrame U γ s j)=
      if i=j then 1 else 0 := by
  have h00 : 0 < γ 0 0 := hγ.diag_pos
  have hd : 0 < γ.det := hγ.det_pos
  have ha : 0 < Real.sqrt (γ 0 0) := Real.sqrt_pos.mpr h00
  have hb : 0 < Real.sqrt γ.det := Real.sqrt_pos.mpr hd
  have ha2 := Real.sq_sqrt h00.le
  have hb2 := Real.sq_sqrt hd.le
  have hdet : γ.det=γ 0 0*γ 1 1-(γ 0 1)^2 := by
    rw [Matrix.det_fin_two,hermitian_real_symmetry hγ.isHermitian 0 1]
    ring
  have hn (a : Fin 2) := metricPair_normal_tangent hU hγ.isHermitian s
    (adaptedFrame U γ s a.succ) (adaptedFrame_radial U γ s a)
  have hgs : (foliationMetric U γ s).IsHermitian := metricBlock_hermitian _ _ hγ.isHermitian
  have hnt (a : Fin 2) : metricPair (foliationMetric U γ s) (adaptedFrame U γ s 0)
      (adaptedFrame U γ s a.succ)=0 := by
    rw [metricPair_symm hgs]
    exact hn a
  fin_cases i <;> fin_cases j
  · exact metricPair_foliationNormal hU hγ.isHermitian s
  · exact hnt 0
  · exact hnt 1
  · exact hn 0
  · rw [metricPair_tangent_expanded U γ s _ _ rfl rfl]
    change γ 0 0 * (Real.sqrt (γ 0 0))⁻¹ * (Real.sqrt (γ 0 0))⁻¹ +
      γ 0 1 * (Real.sqrt (γ 0 0))⁻¹ * 0 +
      (γ 1 0 * 0 * (Real.sqrt (γ 0 0))⁻¹ + γ 1 1 * 0 * 0) = 1
    simp only [mul_zero,zero_mul,add_zero]
    field_simp
    rw [ha2]
  · rw [metricPair_tangent_expanded U γ s _ _ rfl rfl]
    change γ 0 0 * (Real.sqrt (γ 0 0))⁻¹ * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) +
      γ 0 1 * (Real.sqrt (γ 0 0))⁻¹ * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) +
      (γ 1 0 * 0 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) +
       γ 1 1 * 0 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det)) = 0
    simp only [zero_mul,mul_zero,add_zero]
    field_simp
    rw [ha2]
    ring
  · exact hn 1
  · rw [metricPair_tangent_expanded U γ s _ _ rfl rfl]
    change γ 0 0 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) * (Real.sqrt (γ 0 0))⁻¹ +
      γ 0 1 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) * 0 +
      (γ 1 0 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) * (Real.sqrt (γ 0 0))⁻¹ +
       γ 1 1 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) * 0) = 0
    rw [hermitian_real_symmetry hγ.isHermitian 0 1]
    simp only [mul_zero,add_zero]
    field_simp
    rw [ha2]
    ring
  · rw [metricPair_tangent_expanded U γ s _ _ rfl rfl]
    change γ 0 0 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) +
      γ 0 1 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) +
      (γ 1 0 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) +
       γ 1 1 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) * (Real.sqrt (γ 0 0)/Real.sqrt γ.det)) = 1
    rw [hermitian_real_symmetry hγ.isHermitian 0 1]
    field_simp
    rw [ha2,hb2,hdet]
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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma matrix_det_contDiffAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) : ContDiffAt ℝ ∞ (fun y => (G y).det) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  simp only [Matrix.det_fin_three]
  fun_prop

lemma matrix_inv_component_contDiffAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => (G y)⁻¹ i j) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hd := (matrix_det_contDiffAt hg).inv h0
  simp only [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul,
    Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 1 1 * G y 2 2 - G y 1 2 * G y 2 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 1 * G y 2 2) + G y 0 2 * G y 2 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 1 * G y 1 2 - G y 0 2 * G y 1 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 1 0 * G y 2 2) + G y 1 2 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 0 * G y 2 2 - G y 0 2 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 0 * G y 1 2) + G y 0 2 * G y 1 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 1 0 * G y 2 1 - G y 1 1 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 0 * G y 2 1) + G y 0 1 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 0 * G y 1 1 - G y 0 1 * G y 1 0)) x
    exact hd.mul (by fun_prop)

lemma coordinateChristoffel_contDiffAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (i j k : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => coordinateChristoffel G y i j k) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hdc (a i j) : ContDiffAt ℝ ∞
      (fun y => D (CKSRealizedRound.basis a) (fun z => G z i j) y) x :=
    contDiffAt_D (hc i j) (by simp) _
  have hi (i j) := matrix_inv_component_contDiffAt hg h0 i j
  unfold coordinateChristoffel
  apply ContDiffAt.sum
  intro l _
  apply ContDiffAt.mul _ (hi l k)
  change ContDiffAt ℝ ∞ (fun y =>
    (D (CKSRealizedRound.basis i) (fun z => G z j l) y +
     D (CKSRealizedRound.basis j) (fun z => G z i l) y -
     D (CKSRealizedRound.basis l) (fun z => G z i j) y)/2) x
  exact (((hdc i j l).add (hdc j i l)).sub (hdc l i j)).div_const 2

lemma variable_direction_smooth {V : PhysicalPoint → PhysicalPoint}
    {f : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hv : ContDiffAt ℝ ∞ V x) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (fun y => D (V y) f y) x := by
  exact (hf.fderiv_right (by simp)).clm_apply hv

lemma covariantVector_contDiffAt {G : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (hv : ContDiffAt ℝ ∞ V x) (hw : ContDiffAt ℝ ∞ W x) :
    ContDiffAt ℝ ∞ (fun y => covariantVector G (V y) W y) x := by
  have hvc i := contDiffAt_pi.mp hv i
  have hwc i := contDiffAt_pi.mp hw i
  apply contDiffAt_pi.mpr
  intro k
  have hd := variable_direction_smooth hv (hwc k)
  have hc (i j) := coordinateChristoffel_contDiffAt hg h0 i j k
  unfold covariantVector
  exact hd.add (ContDiffAt.sum (fun i _ => ContDiffAt.sum
    (fun j _ => ((hvc i).mul (hwc j)).mul (hc i j))))

lemma metricPair_contDiffAt {G : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (hv : ContDiffAt ℝ ∞ V x)
    (hw : ContDiffAt ℝ ∞ W x) :
    ContDiffAt ℝ ∞ (fun y => metricPair (G y) (V y) (W y)) x := by
  have hgc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hvc i := contDiffAt_pi.mp hv i
  have hwc i := contDiffAt_pi.mp hw i
  exact ContDiffAt.sum (fun i _ => ContDiffAt.sum
    (fun j _ => ((hgc i j).mul (hvc i)).mul (hwc j)))

lemma frameCoefficient_contDiffAt {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (i j k : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => frameCoefficient G E y i j k) x :=
  metricPair_contDiffAt hg (covariantVector_contDiffAt hg h0 (he i) (he j)) (he k)

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
open scoped BigOperators Topology

 def ActualAdaptedAt (G : PhysicalPoint → AmbientMat) (E : LocalFrame) (x : PhysicalPoint) : Prop :=
  DifferentiableAt ℝ G x ∧ (∀ i, DifferentiableAt ℝ (E i) x) ∧ (G x).PosDef ∧
  (∀ᶠ y in 𝓝 x, (G y).IsHermitian) ∧
  (∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0) ∧
  (∀ a b : Fin 2, frameBracketCoefficient G E x a.succ b.succ 0=0)

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
open scoped BigOperators Topology Matrix.Norms.Elementwise

def frameTensor (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : AmbientMat := fun i j => metricPair (K x) (E i x) (E j x)

def actualFrameTensorCovariant (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k : Fin 3) : ℝ :=
  D (E i x) (fun y => frameTensor K E y j k) x -
    ∑ a, (frameCoefficient G E x i j a*frameTensor K E x a k+
      frameCoefficient G E x i k a*frameTensor K E x j a)

def actualFrameMomentum (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (j : Fin 3) : ℝ :=
  (∑ i, actualFrameTensorCovariant G K E x i i j)-
    ∑ i, D (E j x) (fun y => frameTensor K E y i i) x

def actualFrameEnergy (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : ℝ :=
  (actualFrameScalar G E x+(∑ i, frameTensor K E x i i)^2-
    ∑ i, ∑ j, (frameTensor K E x i j)^2)/2

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
open Matrix Filter CKSCalculus
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma foliationMetric_differentiableAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : U x ≠ 0) :
    DifferentiableAt ℝ (fun y => foliationMetric (U y) (γ y) (s y)) x := by
  have hγc (i j) : DifferentiableAt ℝ (fun y => γ y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hγ i) j
  have hsc (i) : DifferentiableAt ℝ (fun y => s y i) x := differentiableAt_pi.mp hs i
  have hrr : DifferentiableAt ℝ
      (fun y => 1/(U y)^2+∑ a, ∑ b, γ y a b*s y a*s y b) x :=
    (CKSCalculus.diffAt_div (differentiableAt_const 1) (hU.pow 2) (pow_ne_zero _ h0)).add
      (DifferentiableAt.fun_sum (fun a _ => DifferentiableAt.fun_sum
        (fun b _ => ((hγc a b).fun_mul (hsc a)).fun_mul (hsc b))))
  have hm (a) : DifferentiableAt ℝ (fun y => ∑ b, γ y a b*s y b) x :=
    DifferentiableAt.fun_sum (fun b _ => (hγc a b).fun_mul (hsc b))
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
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

lemma adaptedFrame_differentiableAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (hp : (γ x).PosDef) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => adaptedFrame (U y) (γ y) (s y) i) x := by
  have hγc (i j) : DifferentiableAt ℝ (fun y => γ y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hγ i) j
  have hsc (i) : DifferentiableAt ℝ (fun y => s y i) x := differentiableAt_pi.mp hs i
  have h00 : 0 < γ x 0 0 := hp.diag_pos
  have ha := (hγc 0 0).sqrt h00.ne'
  have hd : DifferentiableAt ℝ (fun y => (γ y).det) x := by
    simpa only [Matrix.det_fin_two] using
      ((hγc 0 0).fun_mul (hγc 1 1)).fun_sub ((hγc 0 1).fun_mul (hγc 1 0))
  have hb := hd.sqrt hp.det_pos.ne'
  have hapos := Real.sqrt_pos.mpr h00
  have hbpos := Real.sqrt_pos.mpr hp.det_pos
  apply differentiableAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hU
  · exact hU.neg.fun_mul (hsc 0)
  · exact hU.neg.fun_mul (hsc 1)
  · exact differentiableAt_const 0
  · exact ha.inv hapos.ne'
  · exact differentiableAt_const 0
  · exact differentiableAt_const 0
  · exact CKSCalculus.diffAt_div (hγc 0 1).neg (ha.fun_mul hb) (mul_ne_zero hapos.ne' hbpos.ne')
  · exact CKSCalculus.diffAt_div ha hb hbpos.ne'

lemma adaptedFrame_leafBracket {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : U x ≠ 0) (hγ : (γ x).IsHermitian) (a b : Fin 2) :
    frameBracketCoefficient (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x a.succ b.succ 0=0 := by
  apply metricPair_normal_tangent hU hγ
  change D _ (fun y => adaptedFrame (U y) (γ y) (s y) b.succ 0) x -
      D _ (fun y => adaptedFrame (U y) (γ y) (s y) a.succ 0) x = 0
  simp only [adaptedFrame_radial]
  have hz (e : PhysicalPoint) : D e (fun _ : PhysicalPoint => (0 : ℝ)) x=0 := by
    exact CKSCalculus.D_const e x 0
  rw [hz,hz]
  ring

theorem foliation_actualAdaptedAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    ∀ᶠ y in 𝓝 x, ActualAdaptedAt
      (fun z => foliationMetric (U z) (γ z) (s z))
      (fun i z => adaptedFrame (U z) (γ z) (s z) i) y := by
  have hu1 : ContDiffAt ℝ 1 U x := hU.of_le (by simp)
  have hg1 : ContDiffAt ℝ 1 γ x := hγ.of_le (by simp)
  have hs1 : ContDiffAt ℝ 1 s x := hs.of_le (by simp)
  have hu0 := hU.continuousAt.eventually_ne h0
  have hnear : ∀ᶠ y in 𝓝 x, U y ≠ 0 ∧ (γ y).PosDef := by
    filter_upwards [hu0,hp] with y hy hg
    exact ⟨hy,hg⟩
  filter_upwards [hu1.eventually (by norm_num), hg1.eventually (by norm_num),
    hs1.eventually (by norm_num),hnear,hnear.eventually_nhds] with y hyu hyg hys hyp hn
  refine ⟨foliationMetric_differentiableAt (hyu.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) (hys.differentiableAt (by norm_num)) hyp.1,
    fun i => adaptedFrame_differentiableAt (hyu.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) (hys.differentiableAt (by norm_num)) hyp.2 i,
    foliationMetric_posDef hyp.1 hyp.2 (s y), ?_, ?_, ?_⟩
  · filter_upwards [hn] with z hz
    exact metricBlock_hermitian _ _ hz.2.isHermitian
  · filter_upwards [hn] with z hz
    exact adaptedFrame_orthonormal hz.1 hz.2 (s z)
  · exact adaptedFrame_leafBracket hyp.1 hyp.2.isHermitian

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
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma metricPair_add_left (g : AmbientMat) (v w z : PhysicalPoint) :
    metricPair g (v+w) z=metricPair g v z+metricPair g w z := by
  simp only [metricPair,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

lemma metricPair_add_right (g : AmbientMat) (v w z : PhysicalPoint) :
    metricPair g v (w+z)=metricPair g v w+metricPair g v z := by
  simp only [metricPair,Pi.add_apply,mul_add,Finset.sum_add_distrib]

lemma D_metricPair_bilinear (e : PhysicalPoint) {K : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hk : DifferentiableAt ℝ K x) (hv : DifferentiableAt ℝ V x)
    (hw : DifferentiableAt ℝ W x) :
    D e (fun y => metricPair (K y) (V y) (W y)) x =
      metricPair (fun i j => D e (fun y => K y i j) x) (V x) (W x)+
      metricPair (K x) (fun i => D e (fun y => V y i) x) (W x)+
      metricPair (K x) (V x) (fun i => D e (fun y => W y i) x) := by
  rw [D_metricPair e hk hv hw]
  simp only [metricPair,Finset.sum_add_distrib]

lemma coordinateTensorCovariant_product_rule {G K : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hk : DifferentiableAt ℝ K x) (hv : DifferentiableAt ℝ V x)
    (hw : DifferentiableAt ℝ W x) (e : PhysicalPoint) :
    coordinateTensorCovariant G K e (V x) (W x) x =
      D e (fun y => metricPair (K y) (V y) (W y)) x -
      metricPair (K x) (covariantVector G e V x) (W x) -
      metricPair (K x) (V x) (covariantVector G e W x) := by
  have hvv : covariantVector G e V x =
      (fun i => D e (fun y => V y i) x)+coordinateConnectionVector G e (V x) x := rfl
  have hww : covariantVector G e W x =
      (fun i => D e (fun y => W y i) x)+coordinateConnectionVector G e (W x) x := rfl
  rw [D_metricPair_bilinear e hk hv hw,hvv,hww,metricPair_add_left,metricPair_add_right]
  unfold coordinateTensorCovariant
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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma orthonormal_frame_gram {g e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    e.transpose*e=g⁻¹ := by
  apply (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.mul_assoc]
  exact orthonormal_frame_inverse ho

lemma orthonormal_frame_completeness {g e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) (i j : Fin 3) :
    (∑ a, e a i*e a j)=g⁻¹ i j := by
  exact congrFun (congrFun (orthonormal_frame_gram ho) i) j

lemma frame_tensor_matrix (k e : AmbientMat) :
    Matrix.of (fun i j => metricPair k (e i) (e j))=e*k*e.transpose := by
  ext i j
  change (∑ a, ∑ b, k a b*e i a*e j b) = (∑ b, (∑ a, e i a*k a b)*e j b)
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma frame_trace_exact (k : AmbientMat) {g e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    (∑ i, metricPair k (e i) (e i))=(g⁻¹*k).trace := by
  change (Matrix.of (fun i j => metricPair k (e i) (e j))).trace = _
  rw [frame_tensor_matrix,Matrix.trace_mul_comm,
    ← Matrix.mul_assoc e.transpose e,orthonormal_frame_gram ho]

lemma symmetric_square_trace {k : AmbientMat} (hk : k.IsHermitian) :
    (∑ i, ∑ j, (k i j)^2)=(k*k).trace := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hermitian_real_symmetry hk i j]
  ring

lemma frame_tensor_norm_exact {k g e : AmbientMat} (hk : k.IsHermitian)
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    (∑ i, ∑ j, (metricPair k (e i) (e j))^2)=(g⁻¹*k*g⁻¹*k).trace := by
  let t : AmbientMat := Matrix.of (fun i j => metricPair k (e i) (e j))
  have ht : t.IsHermitian := by
    ext i j
    change metricPair k (e j) (e i)=metricPair k (e i) (e j)
    exact metricPair_symm hk _ _
  change (∑ i, ∑ j, (t i j)^2)=_
  rw [symmetric_square_trace ht]
  have he : t=e*k*e.transpose := frame_tensor_matrix k e
  rw [he]
  calc
    _ = (e*(k*(e.transpose*e)*k*e.transpose)).trace := by congr 1; simp only [Matrix.mul_assoc]
    _ = ((k*(e.transpose*e)*k*e.transpose)*e).trace := Matrix.trace_mul_comm _ _
    _ = (k*(e.transpose*e)*k*(e.transpose*e)).trace := by congr 1; simp only [Matrix.mul_assoc]
    _ = (k*g⁻¹*k*g⁻¹).trace := by rw [orthonormal_frame_gram ho]
    _ = (g⁻¹*k*g⁻¹*k).trace := by
      rw [Matrix.trace_mul_comm (k*g⁻¹*k) g⁻¹]
      simp only [Matrix.mul_assoc]

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
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma metricPair_differentiableAt {K : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hk : DifferentiableAt ℝ K x) (hv : DifferentiableAt ℝ V x)
    (hw : DifferentiableAt ℝ W x) :
    DifferentiableAt ℝ (fun y => metricPair (K y) (V y) (W y)) x := by
  have hkc (i j) : DifferentiableAt ℝ (fun y => K y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hk i) j
  have hvc i : DifferentiableAt ℝ (fun y => V y i) x := differentiableAt_pi.mp hv i
  have hwc i : DifferentiableAt ℝ (fun y => W y i) x := differentiableAt_pi.mp hw i
  exact DifferentiableAt.fun_sum (fun i _ => DifferentiableAt.fun_sum
    (fun j _ => ((hkc i j).fun_mul (hvc i)).fun_mul (hwc j)))

lemma coordinateTensorCovariant_bilinear (G K : PhysicalPoint → AmbientMat)
    (x e v w : PhysicalPoint) :
    coordinateTensorCovariant G K e v w x =
      metricPair (fun i j => coordinateTensorCovariant G K
        (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x) e v := by
  have hb (a b) : coordinateTensorCovariant G K
      (CKSRealizedRound.basis a) (CKSRealizedRound.basis b) w x =
      (∑ j, D (CKSRealizedRound.basis a) (fun y => K y b j) x*w j) -
      (∑ i, ∑ j, K x i j*coordinateChristoffel G x a b i*w j) -
      (∑ j, K x b j*(∑ c, w c*coordinateChristoffel G x a c j)) := by
    simp [coordinateTensorCovariant,coordinateConnectionVector,metricPair,
      CKSRealizedRound.basis,Pi.single_apply]
  have hd (i j) : D e (fun y => K y i j) x =
      ∑ a, e a*D (CKSRealizedRound.basis a) (fun y => K y i j) x :=
    D_direction_expansion e x _
  have h₁ : metricPair (fun i j => D e (fun y => K y i j) x) v w =
      ∑ a, ∑ b, (∑ j, D (CKSRealizedRound.basis a) (fun y => K y b j) x*w j)*e a*v b := by
    unfold metricPair
    simp only [hd,Finset.sum_mul]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h₂ : metricPair (K x) (coordinateConnectionVector G e v x) w =
      ∑ a, ∑ b, (∑ i, ∑ j, K x i j*coordinateChristoffel G x a b i*w j)*e a*v b := by
    simp only [metricPair,coordinateConnectionVector,Finset.sum_mul,Finset.mul_sum]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]; arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h₃ : metricPair (K x) v (coordinateConnectionVector G e w x) =
      ∑ a, ∑ b, (∑ j, K x b j*(∑ c, w c*coordinateChristoffel G x a c j))*e a*v b := by
    simp only [metricPair,coordinateConnectionVector,Finset.sum_mul,Finset.mul_sum]
    conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro c _
    ring
  unfold metricPair
  simp_rw [hb,sub_mul,Finset.sum_sub_distrib]
  exact congrArg₂ (· - ·) (congrArg₂ (· - ·) h₁ h₂) h₃

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
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma covector_frame_square (ρ : PhysicalPoint) {g e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    (∑ a, (∑ i, ρ i*e a i)^2)=metricPair g⁻¹ ρ ρ := by
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  unfold metricPair
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (∑ a, e a i*e a j)*ρ i*ρ j := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [orthonormal_frame_completeness ho]

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
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma metricPair_smul_left (g : AmbientMat) (r : ℝ) (v w : PhysicalPoint) :
    metricPair g (r • v) w=r*metricPair g v w := by
  simp only [metricPair,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma metricPair_smul_right (g : AmbientMat) (r : ℝ) (v w : PhysicalPoint) :
    metricPair g v (r • w)=r*metricPair g v w := by
  simp only [metricPair,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coordinateConnectionVector_add_right (G : PhysicalPoint → AmbientMat)
    (x e v w : PhysicalPoint) :
    coordinateConnectionVector G e (v+w) x=
      coordinateConnectionVector G e v x+coordinateConnectionVector G e w x := by
  ext k
  simp only [coordinateConnectionVector,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

lemma coordinateConnectionVector_smul_right (G : PhysicalPoint → AmbientMat)
    (x e v : PhysicalPoint) (r : ℝ) :
    coordinateConnectionVector G e (r • v) x=r • coordinateConnectionVector G e v x := by
  ext k
  simp only [coordinateConnectionVector,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def coordinateTensorCovariantLast (G K : PhysicalPoint → AmbientMat)
    (x e v : PhysicalPoint) : PhysicalPoint →ₗ[ℝ] ℝ where
  toFun := fun w => coordinateTensorCovariant G K e v w x
  map_add' := by
    intro w z
    simp only [coordinateTensorCovariant,coordinateConnectionVector_add_right,
      metricPair_add_right]
    erw [metricPair_add_right]
    ring
  map_smul' := by
    intro r w
    simp only [coordinateTensorCovariant,coordinateConnectionVector_smul_right,
      metricPair_smul_right,smul_eq_mul,RingHom.id_apply]
    erw [metricPair_smul_right]
    ring

def coordinateMomentumLinear (G K : PhysicalPoint → AmbientMat)
    (x : PhysicalPoint) : PhysicalPoint →ₗ[ℝ] ℝ where
  toFun := coordinateMomentum G K x
  map_add' := by
    intro w z
    have hc (i j) : coordinateTensorCovariant G K
        (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) (w+z) x=
        coordinateTensorCovariant G K (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x+
        coordinateTensorCovariant G K (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) z x :=
      (coordinateTensorCovariantLast G K x _ _).map_add w z
    simp only [coordinateMomentum,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
      Matrix.of_apply,hc,mul_add,Finset.sum_add_distrib,D,map_add]
    ring
  map_smul' := by
    intro r w
    have hc (i j) : coordinateTensorCovariant G K
        (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) (r • w) x=
        r*coordinateTensorCovariant G K (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x :=
      (coordinateTensorCovariantLast G K x _ _).map_smul r w
    simp only [coordinateMomentum,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
      Matrix.of_apply,hc,D,map_smul,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_left_comm _ r,← Finset.mul_sum]
    ring

lemma coordinateMomentum_expansion (G K : PhysicalPoint → AmbientMat)
    (x w : PhysicalPoint) :
    coordinateMomentum G K x w=
      ∑ i, coordinateMomentum G K x (CKSRealizedRound.basis i)*w i := by
  change coordinateMomentumLinear G K x w=_
  conv_lhs => rw [direction_expansion w]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul,coordinateMomentumLinear,LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro i _
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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma covariant_second_pair {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0)
    (i j k l : Fin 3) :
    metricPair (G x)
      (covariantVector G (E i x) (fun y => covariantVector G (E j y) (E k) y) x)
      (E l x) = D (E i x) (fun y => frameCoefficient G E y j k l) x +
      ∑ m, frameCoefficient G E x j k m*frameCoefficient G E x i m l := by
  have hh := covariantVector_metric (hg.differentiableAt (by simp))
    ((covariantVector_contDiffAt hg (ne_of_gt hp.det_pos) (he j) (he k)).differentiableAt (by simp))
    ((he l).differentiableAt (by simp)) hp hs (E i x)
  have hpairs := metricPair_frame_right (G x) ho.self_of_nhds
    (covariantVector G (E i x) (E l) x) (covariantVector G (E j x) (E k) x)
  change (∑ m, frameCoefficient G E x i l m*frameCoefficient G E x j k m) = _ at hpairs
  have hm (m) := frameCoefficient_metric (hg.differentiableAt (by simp))
    (fun a => (he a).differentiableAt (by simp)) hp hs ho i l m
  simp_rw [hm] at hpairs
  have hpairs' : metricPair (G x) (covariantVector G (E j x) (E k) x)
      (covariantVector G (E i x) (E l) x) =
      -(∑ m, frameCoefficient G E x j k m*frameCoefficient G E x i m l) := by
    rw [← hpairs]
    simp only [neg_mul,Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    ring
  change D (E i x) (fun y => frameCoefficient G E y j k l) x = _ at hh
  rw [hpairs'] at hh
  linarith

def covariantDirectionLinear (G : PhysicalPoint → AmbientMat)
    (W : PhysicalPoint → PhysicalPoint) (x : PhysicalPoint) :
    PhysicalPoint →ₗ[ℝ] PhysicalPoint where
  toFun e := covariantVector G e W x
  map_add' e f := by
    ext k
    simp only [covariantVector,D,map_add,Pi.add_apply,
      add_mul,Finset.sum_add_distrib]
    ring
  map_smul' r e := by
    ext k
    simp only [covariantVector,D,map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp only [mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma metricPair_sum_left (g : AmbientMat) (v : Fin 3 → PhysicalPoint) (w : PhysicalPoint) :
    metricPair g (∑ i, v i) w=∑ i, metricPair g (v i) w := by
  simp only [Fin.sum_univ_three,metricPair_add_left]

lemma covariant_frame_direction {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (ho : ∀ i j,
      metricPair (G x) (E i x) (E j x)=if i=j then 1 else 0)
    (e : PhysicalPoint) (j k : Fin 3) :
    metricPair (G x) (covariantVector G e (E j) x) (E k x)=
      ∑ m, metricPair (G x) e (E m x)*frameCoefficient G E x m j k := by
  have hex : e=∑ m, metricPair (G x) e (E m x) • E m x := by
    ext a
    simpa only [Fin.sum_univ_three,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using
      (orthonormal_frame_expansion ho e a).symm
  change metricPair (G x) (covariantDirectionLinear G (E j) x e) (E k x)=_
  conv_lhs => rw [hex]
  rw [map_sum]
  simp only [map_smul,metricPair_sum_left,metricPair_smul_left]
  rfl

theorem actualFrameCurvature_operator {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0)
    (i j k l : Fin 3) :
    actualFrameCurvature G E x i j k l =
      metricPair (G x)
        (covariantVector G (E i x) (fun y => covariantVector G (E j y) (E k) y) x) (E l x) -
      metricPair (G x)
        (covariantVector G (E j x) (fun y => covariantVector G (E i y) (E k) y) x) (E l x) -
      metricPair (G x) (covariantVector G (actualFrameBracket E x i j) (E k) x) (E l x) := by
  rw [covariant_second_pair hg he hp hs ho,covariant_second_pair hg he hp hs ho,
    covariant_frame_direction ho.self_of_nhds]
  simp only [actualFrameCurvature,frameBracketCoefficient,Finset.sum_sub_distrib]
  ring

lemma metricPair_sub_left (g : AmbientMat) (v w z : PhysicalPoint) :
    metricPair g (v-w) z=metricPair g v z-metricPair g w z := by
  simp only [metricPair,Pi.sub_apply,mul_sub,sub_mul,Finset.sum_sub_distrib]

def curvatureVector (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k : Fin 3) : PhysicalPoint :=
  covariantVector G (E i x) (fun y => covariantVector G (E j y) (E k) y) x -
  covariantVector G (E j x) (fun y => covariantVector G (E i y) (E k) y) x -
  covariantVector G (actualFrameBracket E x i j) (E k) x

theorem actualScalar_curvature_trace {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    actualFrameScalar G E x =
      ∑ i, ∑ j, metricPair (G x) (curvatureVector G E x i j j) (E i x) := by
  simp only [actualFrameScalar,curvatureVector,metricPair_sub_left]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact actualFrameCurvature_operator hg he hp hs ho i j j i

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

lemma adaptedFrame_contDiffAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hp : (γ x).PosDef) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => adaptedFrame (U y) (γ y) (s y) i) x := by
  have hγc (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have hsc (i) : ContDiffAt ℝ ∞ (fun y => s y i) x := contDiffAt_pi.mp hs i
  have h00 : 0 < γ x 0 0 := hp.diag_pos
  have ha := (hγc 0 0).sqrt h00.ne'
  have hd : ContDiffAt ℝ ∞ (fun y => (γ y).det) x := by
    simpa only [Matrix.det_fin_two] using
      ((hγc 0 0).mul (hγc 1 1)).sub ((hγc 0 1).mul (hγc 1 0))
  have hb := hd.sqrt hp.det_pos.ne'
  have hapos := Real.sqrt_pos.mpr h00
  have hbpos := Real.sqrt_pos.mpr hp.det_pos
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hU
  · exact hU.neg.mul (hsc 0)
  · exact hU.neg.mul (hsc 1)
  · exact contDiffAt_const
  · exact ha.inv hapos.ne'
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact (hγc 0 1).neg.div (ha.mul hb) (mul_ne_zero hapos.ne' hbpos.ne')
  · exact ha.div hb hbpos.ne'

end
end CKSAngularGeometry

end


end OAI
end

section
namespace OAI




noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff

def hyperbolicMetric (x Y Z : E) : ℝ :=
  inner ℝ Y Z - inner ℝ x Y * inner ℝ x Z / (1+‖x‖^2)

lemma hyperTime_derivative (x : E) :
    HasFDerivAt hyperTime ((hyperTime x)⁻¹ • innerSL ℝ x) x := by
  have h := (Real.hasDerivAt_sqrt (show 1+‖x‖^2 ≠ 0 by positivity)).comp_hasFDerivAt x
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1)
  convert! h using 1
  ext Y
  simp [hyperTime, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

lemma hyperboloid_derivative_pair (x Y Z : E) :
    minkowski (fderiv ℝ hyperboloid x Y) (fderiv ℝ hyperboloid x Z) = hyperbolicMetric x Y Z := by
  have hd := (hyperTime_derivative x).prodMk (hasFDerivAt_id x)
  change HasFDerivAt hyperboloid _ x at hd
  rw [hd.fderiv]
  simp only [minkowski, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    smul_apply, innerSL_apply_apply, smul_eq_mul, hyperbolicMetric]
  rw [← hyperTime_sq]
  ring

theorem hyperbolicMap_isometry {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (x Y Z : E) :
    hyperbolicMetric (hyperbolicMap e m p x)
      (fderiv ℝ (hyperbolicMap e m p) x Y) (fderiv ℝ (hyperbolicMap e m p) x Z) =
        hyperbolicMetric x Y Z := by
  have heq : hyperboloid ∘ hyperbolicMap e m p = boostCLM e m p ∘ hyperboloid := by
    funext z; exact hyperboloid_boost he hm0 hm z
  have hh := congrArg (fun f : E → V => fderiv ℝ f x) heq
  rw [fderiv_comp x (hyperboloid_smooth.differentiable (by simp)).differentiableAt
      ((hyperbolicMap_smooth e m p).differentiable (by simp)).differentiableAt,
    fderiv_comp x (boostCLM e m p).differentiableAt
      (hyperboloid_smooth.differentiable (by simp)).differentiableAt,
    (boostCLM e m p).fderiv] at hh
  have hy := congrArg (fun L : E →L[ℝ] V => L Y) hh
  have hz := congrArg (fun L : E →L[ℝ] V => L Z) hh
  simp only [ContinuousLinearMap.comp_apply] at hy hz
  rw [← hyperboloid_derivative_pair, hy, hz]
  exact (boost_minkowski hm0.ne' (add_pos (energy_pos he) hm0).ne' hm _ _).trans
    (hyperboloid_derivative_pair x Y Z)

end
end CKSLorentz

end




noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma sum_coordinate_basis (v : Point) : ∑ k : I, v k • basis k = v := by
  ext k
  simp [basis, Finset.sum_apply, Pi.single_apply]

end
end CKSMixedGeometry

end

























































































noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped BigOperators Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma physical_D_div_const (e : PhysicalPoint) {f : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    D e (fun y => f y/c) x = D e f x/c := by
  simp only [div_eq_mul_inv]
  rw [D_mul e hf (differentiableAt_const _),D_const]
  ring

end
end CKSAngularGeometry

end




































































noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

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

end
end CKSMixedGeometry

end




end OAI
end

section
namespace OAI





































noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
lemma hyperbolicField_apply (x v w : E) : hyperbolicField x v w = hyperbolicMetric x v w := by
  change inner ℝ v w - (1/(1+‖x‖^2)) * (inner ℝ x v * inner ℝ x w) =
    inner ℝ v w - inner ℝ x v * inner ℝ x w / (1+‖x‖^2)
  ring

end
end CKSLorentz

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

lemma actual_inverse_derivative {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (v : PhysicalPoint) :
    (fun i j => D v (fun y => (G y)⁻¹ i j) x) =
      -(G x)⁻¹ * (show AmbientMat from fun i j => D v (fun y => G y i j) x) * (G x)⁻¹ := by
  let dG : AmbientMat := fun i j => D v (fun y => G y i j) x
  let dI : AmbientMat := fun i j => D v (fun y => (G y)⁻¹ i j) x
  have hc (i j) : DifferentiableAt ℝ (fun y => G y i j) x :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j).differentiableAt (by simp)
  have hi (i j) : DifferentiableAt ℝ (fun y => (G y)⁻¹ i j) x :=
    (matrix_inv_component_contDiffAt hg h0 i j).differentiableAt (by simp)
  have hz : ∀ᶠ y in 𝓝 x, (G y).det ≠ 0 :=
    (matrix_det_contDiffAt hg).continuousAt.eventually_ne h0
  have hD : dG * (G x)⁻¹ + G x * dI = 0 := by
    ext i j
    have hd : D v (fun y => (G y * (G y)⁻¹) i j) x = 0 := by
      calc
        _ = D v (fun _ => (1 : AmbientMat) i j) x := by
          apply D_congr
          filter_upwards [hz] with y hy
          rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hy)]
        _ = 0 := D_const _ _ _
    simp only [Matrix.mul_apply] at hd
    rw [D_sum3 v (fun k y => G y i k * (G y)⁻¹ k j)
      (fun k => (hc i k).fun_mul (hi k j))] at hd
    simp only [D_mul _ (hc i _) (hi _ j)] at hd
    change (∑ k, dG i k * (G x)⁻¹ k j) + (∑ k, G x i k * dI k j) = 0
    simpa only [dG, dI, Finset.sum_add_distrib, add_comm, mul_comm] using hd
  have hIG : (G x)⁻¹ * G x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h0)
  have hD' : G x * dI = -(dG * (G x)⁻¹) := (eq_neg_iff_add_eq_zero).2 (by
    simpa only [add_comm] using hD)
  change dI = -(G x)⁻¹ * dG * (G x)⁻¹
  calc
    dI = ((G x)⁻¹ * G x) * dI := by rw [hIG, one_mul]
    _ = (G x)⁻¹ * (G x * dI) := mul_assoc _ _ _
    _ = -(G x)⁻¹ * dG * (G x)⁻¹ := by rw [hD']; simp only [mul_neg, neg_mul, mul_assoc]

lemma physicalMetricJet_dInv {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (a i j : Fin 3) :
    D (CKSRealizedRound.basis a) (fun y => (G y)⁻¹ i j) x =
      (physicalMetricJet G x).dInv a i j := by
  have h := congrFun (congrFun (actual_inverse_derivative hg h0
    (CKSRealizedRound.basis a)) i) j
  rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.neg_apply] at h
  change D (CKSRealizedRound.basis a) (fun y => (G y)⁻¹ i j) x =
    -(∑ c, (∑ b, (G x)⁻¹ i b * D (CKSRealizedRound.basis a)
      (fun y => G y b c) x) * (G x)⁻¹ c j) at h
  rw [h]
  simp only [CKSRound.MetricJet.dInv, physicalMetricJet, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalMetricJet_gamma {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : (G x).IsHermitian) (a i j : Fin 3) :
    (physicalMetricJet G x).gamma a i j = coordinateChristoffel G x i j a := by
  simp only [CKSRound.MetricJet.gamma, physicalMetricJet, coordinateChristoffel,
    lowerKoszul, actualMetricFirstJet, Finset.sum_div]
  apply Finset.sum_congr rfl; intro l _
  rw [hermitian_real_symmetry hs.inv a l]
  ring

lemma physicalMetricJet_dGamma {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (s a i j : Fin 3) :
    D (CKSRealizedRound.basis s) (fun y => coordinateChristoffel G y i j a) x =
      (physicalMetricJet G x).dGamma s a i j := by
  have hc (b c) : ContDiffAt ℝ ∞ (fun y => G y b c) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg b) c
  have hd (b c d) : DifferentiableAt ℝ
      (fun y => D (CKSRealizedRound.basis b) (fun z => G z c d) y) x :=
    (contDiffAt_D (hc c d) (m := ∞) (by simp) _).differentiableAt (by simp)
  have hi (b c) : DifferentiableAt ℝ (fun y => (G y)⁻¹ b c) x :=
    (matrix_inv_component_contDiffAt hg h0 b c).differentiableAt (by simp)
  have ht (l) := ((hd i j l).fun_add (hd j i l)).fun_sub (hd l i j)
  have hm (l) := (hi a l).fun_mul (ht l)
  calc
    _ = D (CKSRealizedRound.basis s) (fun y => (physicalMetricJet G y).gamma a i j) x := by
      apply D_congr
      filter_upwards [hs] with y hy
      exact (physicalMetricJet_gamma hy a i j).symm
    _ = _ := by
      unfold CKSRound.MetricJet.gamma
      change D (CKSRealizedRound.basis s) (fun y =>
        (∑ l, (G y)⁻¹ a l * (D (CKSRealizedRound.basis i) (fun z => G z j l) y +
          D (CKSRealizedRound.basis j) (fun z => G z i l) y -
          D (CKSRealizedRound.basis l) (fun z => G z i j) y)) / 2) x = _
      rw [physical_D_div_const _ (DifferentiableAt.fun_sum (fun l _ => hm l)),
        D_sum3 _ _ hm]
      unfold CKSRound.MetricJet.dGamma
      congr 1
      apply Finset.sum_congr rfl; intro l _
      rw [D_mul _ (hi a l) (ht l), D_sub _ ((hd i j l).fun_add (hd j i l)) (hd l i j),
        D_add _ (hd i j l) (hd j i l), physicalMetricJet_dInv hg h0]
      simp only [physicalMetricJet]
      ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAmbientCalculus
noncomputable section
open Matrix CKSCalculus CKSAngularGeometry Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

abbrev A := Fin 3
abbrev P := PhysicalPoint
abbrev Vect := PhysicalPoint
abbrev Symbols := A → A → A → ℝ

def delta (v : Vect) (f : P → ℝ) (x : P) : ℝ := D v f x

lemma delta_expansion (v : Vect) (f : P → ℝ) (x : P) :
    delta v f x = ∑ i : A, v i * D (CKSRealizedRound.basis i) f x :=
  D_direction_expansion v x f

lemma delta_mul (v : Vect) {f g : P → ℝ} {x : P}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    delta v (fun y => f y * g y) x = f x * delta v g x + g x * delta v f x :=
  D_mul _ hf hg

lemma delta_add (v : Vect) {f g : P → ℝ} {x : P}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    delta v (fun y => f y + g y) x = delta v f x + delta v g x :=
  D_add _ hf hg

lemma delta_sum (v : Vect) {x : P} (f : A → P → ℝ)
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    delta v (fun y => ∑ i, f i y) x = ∑ i, delta v (f i) x :=
  D_sum3 _ f hf

def bracket (V W : P → Vect) (x : P) : Vect := fun k =>
  delta (V x) (fun y => W y k) x - delta (W x) (fun y => V y k) x

lemma delta_moving (v : Vect) {W : P → Vect} {f : P → ℝ} {x : P}
    (hW : DifferentiableAt ℝ W x) (hf : ContDiffAt ℝ 2 f x) :
    delta v (fun y => delta (W y) f y) x =
      ∑ i : A, (W x i * delta v (D (CKSRealizedRound.basis i) f) x +
        D (CKSRealizedRound.basis i) f x * delta v (fun y => W y i) x) := by
  have hWi (i : A) := differentiableAt_pi.mp hW i
  have hfi (i : A) : DifferentiableAt ℝ (D (CKSRealizedRound.basis i) f) x :=
    (contDiffAt_D hf (m := 1) (by norm_num) _).differentiableAt (by norm_num)
  simp only [delta_expansion (W _)]
  rw [delta_sum _ (fun i y => W y i * D (CKSRealizedRound.basis i) f y)
    (fun i => (hWi i).mul (hfi i))]
  apply Finset.sum_congr rfl
  intro i _
  exact delta_mul _ (hWi i) (hfi i)

lemma delta_commutator {V W : P → Vect} {f : P → ℝ} {x : P}
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x)
    (hf : ContDiffAt ℝ 2 f x) :
    delta (V x) (fun y => delta (W y) f y) x -
      delta (W x) (fun y => delta (V y) f y) x = delta (bracket V W x) f x := by
  rw [delta_moving _ hW hf, delta_moving _ hV hf]
  simp only [delta_expansion, bracket, Fin.sum_univ_three]
  rw [D_comm hf (CKSRealizedRound.basis 0) (CKSRealizedRound.basis 1),
    D_comm hf (CKSRealizedRound.basis 0) (CKSRealizedRound.basis 2),
    D_comm hf (CKSRealizedRound.basis 1) (CKSRealizedRound.basis 2)]
  ring

def nabla (Γ : P → Symbols) (v : Vect) (W : P → Vect) (x : P) : Vect := fun k =>
  delta v (fun y => W y k) x + ∑ i : A, ∑ j : A, v i * W x j * Γ x k i j

def curvature (Γ : P → Symbols) (V W Z : P → Vect) (x : P) : Vect :=
  nabla Γ (V x) (fun y => nabla Γ (W y) Z y) x -
    nabla Γ (W x) (fun y => nabla Γ (V y) Z y) x - nabla Γ (bracket V W x) Z x

def coordCurvature (Γ : P → Symbols) (x : P) (k l i j : A) : ℝ :=
  D (CKSRealizedRound.basis i) (fun y => Γ y k j l) x -
    D (CKSRealizedRound.basis j) (fun y => Γ y k i l) x +
    ∑ m : A, (Γ x m j l * Γ x k i m - Γ x m i l * Γ x k j m)

lemma delta_nabla (v : Vect) {Γ : P → Symbols} {W Z : P → Vect} {x : P}
    (hΓ : DifferentiableAt ℝ Γ x) (hW : DifferentiableAt ℝ W x)
    (hZ : ContDiffAt ℝ 2 Z x) (k : A) :
    delta v (fun y => nabla Γ (W y) Z y k) x =
      delta v (fun y => delta (W y) (fun z => Z z k) y) x +
      ∑ i : A, ∑ j : A,
        (W x i * Z x j * delta v (fun y => Γ y k i j) x +
          Γ x k i j * (W x i * delta v (fun y => Z y j) x +
            Z x j * delta v (fun y => W y i) x)) := by
  have hWi (i : A) := differentiableAt_pi.mp hW i
  have hZi (i : A) := contDiffAt_pi.mp hZ i
  have hdZi (i j : A) : DifferentiableAt ℝ
      (D (CKSRealizedRound.basis i) (fun y => Z y j)) x :=
    (contDiffAt_D (hZi j) (m := 1) (by norm_num) _).differentiableAt (by norm_num)
  have hΓi (a i j : A) : DifferentiableAt ℝ (fun y => Γ y a i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp hΓ a) i) j
  have hvZ : DifferentiableAt ℝ (fun y => delta (W y) (fun z => Z z k) y) x := by
    simp only [delta_expansion]
    exact DifferentiableAt.fun_sum fun i _ => (hWi i).mul (hdZi i k)
  have ht (i j : A) : DifferentiableAt ℝ
      (fun y => W y i * Z y j * Γ y k i j) x :=
    ((hWi i).mul ((hZi j).differentiableAt (by norm_num))).mul (hΓi k i j)
  have hs (i : A) : DifferentiableAt ℝ (fun y => ∑ j : A, W y i * Z y j * Γ y k i j) x :=
    DifferentiableAt.fun_sum fun j _ => ht i j
  have hss : DifferentiableAt ℝ (fun y => ∑ i : A, ∑ j : A, W y i * Z y j * Γ y k i j) x :=
    DifferentiableAt.fun_sum fun i _ => hs i
  change delta v (fun y => delta (W y) (fun z => Z z k) y +
    ∑ i : A, ∑ j : A, W y i * Z y j * Γ y k i j) x = _
  rw [delta_add _ hvZ hss, delta_sum _ _ hs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [delta_sum _ _ (ht i)]
  apply Finset.sum_congr rfl
  intro j _
  rw [delta_mul v (f := fun y => W y i * Z y j) (g := fun y => Γ y k i j)
    ((hWi i).mul ((hZi j).differentiableAt (by norm_num))) (hΓi k i j),
    delta_mul v (f := fun y => W y i) (g := fun y => Z y j)
      (hWi i) ((hZi j).differentiableAt (by norm_num))]

theorem curvature_coordinate {Γ : P → Symbols} {V W Z : P → Vect} {x : P}
    (hΓ : DifferentiableAt ℝ Γ x) (hV : DifferentiableAt ℝ V x)
    (hW : DifferentiableAt ℝ W x) (hZ : ContDiffAt ℝ 2 Z x) (k : A) :
    curvature Γ V W Z x k = ∑ i : A, ∑ j : A, ∑ l : A,
      V x i * W x j * Z x l * coordCurvature Γ x k l i j := by
  change (delta (V x) (fun y => nabla Γ (W y) Z y k) x +
      ∑ i : A, ∑ j : A, V x i * nabla Γ (W x) Z x j * Γ x k i j) -
    (delta (W x) (fun y => nabla Γ (V y) Z y k) x +
      ∑ i : A, ∑ j : A, W x i * nabla Γ (V x) Z x j * Γ x k i j) -
    (delta (bracket V W x) (fun y => Z y k) x +
      ∑ i : A, ∑ j : A, bracket V W x i * Z x j * Γ x k i j) = _
  rw [delta_nabla _ hΓ hW hZ, delta_nabla _ hΓ hV hZ]
  have hc := delta_commutator hV hW (contDiffAt_pi.mp hZ k)
  rw [sub_eq_iff_eq_add.mp hc]
  simp only [nabla, coordCurvature, bracket, delta_expansion, Fin.sum_univ_three]
  ring

end
end CKSAmbientCalculus

end

noncomputable section
namespace CKSAmbientCalculus
noncomputable section
open Matrix CKSAngularGeometry
open scoped BigOperators

def pair (γ : AmbientMat) (v w : Vect) : ℝ := ∑ i : A, ∑ j : A, γ i j * v i * w j

lemma inverse_metric_trace {γ : AmbientMat} (hp : γ.PosDef) (k i : A) :
    (∑ m : A, γ k m * γ⁻¹ i m) = if k = i then 1 else 0 := by
  have h : (γ * γ⁻¹) k i = (1 : AmbientMat) k i :=
    congrFun (congrFun (Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hp.det_pos.ne')) k) i
  simpa only [Matrix.mul_apply, hermitian_real_symmetry hp.isHermitian.inv, Matrix.one_apply] using h

lemma sum_three_rotate (f : A → A → A → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem scalar_frame_contraction {γ : AmbientMat} (hp : γ.PosDef) (E : A → Vect)
    (hg : ∀ i j, (∑ a : A, E a i * E a j) = γ⁻¹ i j)
    (R : A → A → A → A → ℝ) :
    (∑ a : A, ∑ b : A, pair γ
      (fun k => ∑ i : A, ∑ j : A, ∑ l : A, E a i * E b j * E b l * R k l i j)
      (E a)) = ∑ j : A, ∑ l : A, γ⁻¹ j l * ∑ k : A, R k l k j := by
  calc
    _ = ∑ k : A, ∑ m : A, ∑ i : A, ∑ j : A, ∑ l : A,
        ∑ a : A, ∑ b : A,
          γ k m * E a i * E a m * E b j * E b l * R k l i j := by
      simp only [pair, Finset.mul_sum, Finset.sum_mul]
      conv_lhs =>
        rw [sum_three_rotate]
        arg 2; ext k
        rw [sum_three_rotate]
        arg 2; ext m
        rw [sum_three_rotate]
        arg 2; ext i
        rw [sum_three_rotate]
        arg 2; ext j
        rw [sum_three_rotate]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro m _
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro l _
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      ring
    _ = ∑ k : A, ∑ m : A, ∑ i : A, ∑ j : A, ∑ l : A,
        (γ k m * γ⁻¹ i m) * γ⁻¹ j l * R k l i j := by
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro m _
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro l _
      calc
        _ = (γ k m * (∑ a : A, E a i * E a m)) *
            (∑ b : A, E b j * E b l) * R k l i j := by
          simp only [Fin.sum_univ_three]
          ring
        _ = _ := by rw [hg, hg]
    _ = ∑ k : A, ∑ i : A, ∑ j : A, ∑ l : A, ∑ m : A,
        (γ k m * γ⁻¹ i m) * γ⁻¹ j l * R k l i j := by
      apply Finset.sum_congr rfl; intro k _
      conv_lhs =>
        rw [Finset.sum_comm]
        arg 2; ext i
        rw [Finset.sum_comm]
        arg 2; ext j
        rw [Finset.sum_comm]
    _ = ∑ k : A, ∑ i : A, ∑ j : A, ∑ l : A,
        (if k = i then 1 else 0) * γ⁻¹ j l * R k l i j := by
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro l _
      rw [← Finset.sum_mul, ← Finset.sum_mul, inverse_metric_trace hp]
    _ = _ := by
      simp only [Fin.sum_univ_three]
      simp
      ring

end
end CKSAmbientCalculus

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def physicalSymbols (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) :
    CKSAmbientCalculus.Symbols := fun a i j => coordinateChristoffel G x i j a

lemma physicalSymbols_differentiableAt {G : PhysicalPoint → AmbientMat}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) :
    DifferentiableAt ℝ (physicalSymbols G) x := by
  apply differentiableAt_pi.mpr; intro a
  apply differentiableAt_pi.mpr; intro i
  apply differentiableAt_pi.mpr; intro j
  exact (coordinateChristoffel_contDiffAt hg h0 i j a).differentiableAt (by simp)

lemma curvatureVector_coordinate {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (a b c k : Fin 3) :
    curvatureVector G E x a b c k = ∑ i, ∑ j, ∑ l,
      E a x i * E b x j * E c x l *
        CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l i j := by
  have hz : ContDiffAt ℝ 2 (E c) x := (he c).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  change CKSAmbientCalculus.curvature (physicalSymbols G) (E a) (E b) (E c) x k = _
  exact CKSAmbientCalculus.curvature_coordinate (physicalSymbols_differentiableAt hg h0)
    ((he a).differentiableAt (by simp)) ((he b).differentiableAt (by simp))
    hz k

lemma physical_scalar_coordinate_trace {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    actualFrameScalar G E x = ∑ j, ∑ l, (G x)⁻¹ j l * ∑ k,
      CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l k j := by
  rw [actualScalar_curvature_trace hg he hp hs ho]
  have hc (a b) : curvatureVector G E x a b b = fun k => ∑ i, ∑ j, ∑ l,
      E a x i * E b x j * E b x l *
        CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l i j := by
    funext k
    exact curvatureVector_coordinate hg hp.det_pos.ne' he a b b k
  simp only [hc]
  change (∑ a, ∑ b, CKSAmbientCalculus.pair (G x)
    (fun k => ∑ i, ∑ j, ∑ l, E a x i * E b x j * E b x l *
      CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l i j) (E a x)) = _
  exact CKSAmbientCalculus.scalar_frame_contraction hp (fun a => E a x)
    (orthonormal_frame_completeness ho.self_of_nhds)
    (CKSAmbientCalculus.coordCurvature (physicalSymbols G) x)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalMetricJet_gamma_torsion {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (a i j : Fin 3) :
    (physicalMetricJet G x).gamma a i j = (physicalMetricJet G x).gamma a j i := by
  rw [physicalMetricJet_gamma hs.self_of_nhds, physicalMetricJet_gamma hs.self_of_nhds]
  exact coordinateChristoffel_torsion hs i j a

lemma physicalMetricJet_dGamma_torsion {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (s a i j : Fin 3) :
    (physicalMetricJet G x).dGamma s a i j = (physicalMetricJet G x).dGamma s a j i := by
  rw [← physicalMetricJet_dGamma hg h0 hs, ← physicalMetricJet_dGamma hg h0 hs]
  apply D_congr
  filter_upwards [hs.eventually_nhds] with y hy
  exact coordinateChristoffel_torsion hy i j a

lemma physicalMetricJet_ricci {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (l j : Fin 3) :
    (∑ k, CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l k j) =
      (physicalMetricJet G x).ricci l j := by
  simp only [CKSAmbientCalculus.coordCurvature, physicalSymbols,
    physicalMetricJet_dGamma hg h0 hs, ← physicalMetricJet_gamma hs.self_of_nhds,
    Finset.sum_add_distrib, CKSRound.MetricJet.ricci]
  apply congrArg₂ (fun u v : ℝ => u + v)
  · apply Finset.sum_congr rfl; intro k _
    rw [physicalMetricJet_dGamma_torsion hg h0 hs k k j l,
      physicalMetricJet_dGamma_torsion hg h0 hs j k k l]
  · apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro m _
    rw [physicalMetricJet_gamma_torsion hs m j l,
      physicalMetricJet_gamma_torsion hs m k l]
    ring

theorem physicalMetricJet_scalar {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    actualFrameScalar G E x = (physicalMetricJet G x).scalar := by
  rw [physical_scalar_coordinate_trace hg he hp hs ho]
  simp only [physicalMetricJet_ricci hg hp.det_pos.ne' hs, CKSRound.MetricJet.scalar]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro j _
  change (G x)⁻¹ j l * _ = (G x)⁻¹ l j * _
  rw [hermitian_real_symmetry hp.isHermitian.inv j l]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma matrix_inverse_trace_coordinates {g : AmbientMat} (hs : g.IsHermitian)
    (k : AmbientMat) : (g⁻¹*k).trace = ∑ a, ∑ b, g⁻¹ a b * k a b := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [hermitian_real_symmetry hs.inv b a]

lemma physicalMetricJet_trace {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : (G x).IsHermitian) :
    ((G x)⁻¹*K x).trace = (physicalMetricJet G x).trace (physicalTensorJet K x) :=
  matrix_inverse_trace_coordinates hs (K x)

lemma matrix_tensor_norm_coordinates {g k : AmbientMat} (hs : g.IsHermitian)
    (hk : k.IsHermitian) :
    (g⁻¹*k*g⁻¹*k).trace = ∑ a, ∑ b, ∑ c, ∑ d,
      g⁻¹ a c * g⁻¹ b d * k a b * k c d := by
  simp only [Matrix.mul_assoc, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext a
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  rw [hermitian_real_symmetry hs.inv c a, hermitian_real_symmetry hk d c]
  ring

lemma physicalMetricJet_normSq {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : (G x).IsHermitian) (hk : (K x).IsHermitian) :
    ((G x)⁻¹*K x*(G x)⁻¹*K x).trace =
      (physicalMetricJet G x).normSq (physicalTensorJet K x) :=
  matrix_tensor_norm_coordinates hs hk

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalMetricJet_dTrace {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (hk : ContDiffAt ℝ ∞ K x) (h0 : (G x).det ≠ 0)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (i : Fin 3) :
    D (CKSRealizedRound.basis i) (fun y => ((G y)⁻¹*K y).trace) x =
      (physicalMetricJet G x).dTrace (physicalTensorJet K x) i := by
  have hki (a b) : DifferentiableAt ℝ (fun y => K y a b) x :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hk a) b).differentiableAt (by simp)
  have hgi (a b) : DifferentiableAt ℝ (fun y => (G y)⁻¹ a b) x :=
    (matrix_inv_component_contDiffAt hg h0 a b).differentiableAt (by simp)
  have ht (a b) := (hgi a b).fun_mul (hki a b)
  calc
    _ = D (CKSRealizedRound.basis i) (fun y => ∑ a, ∑ b, (G y)⁻¹ a b*K y a b) x := by
      apply D_congr
      filter_upwards [hs] with y hy
      exact matrix_inverse_trace_coordinates hy (K y)
    _ = _ := by
      rw [D_sum3 _ _ (fun a => DifferentiableAt.fun_sum (fun b _ => ht a b))]
      unfold CKSRound.MetricJet.dTrace
      apply Finset.sum_congr rfl; intro a _
      rw [D_sum3 _ _ (ht a)]
      apply Finset.sum_congr rfl; intro b _
      rw [D_mul _ (hgi a b) (hki a b), physicalMetricJet_dInv hg h0]
      simp only [physicalTensorJet, physicalMetricJet]
      ring

lemma physicalMetricJet_tensorCovariant {G K : PhysicalPoint → AmbientMat}
    {x : PhysicalPoint} (hs : (G x).IsHermitian) (a b i : Fin 3) :
    coordinateTensorCovariant G K (CKSRealizedRound.basis a)
      (CKSRealizedRound.basis b) (CKSRealizedRound.basis i) x =
        (physicalTensorJet K x).d a b i -
        (∑ c, (physicalMetricJet G x).gamma c a b * (physicalTensorJet K x).val c i) -
        (∑ c, (physicalMetricJet G x).gamma c a i * (physicalTensorJet K x).val b c) := by
  simp only [physicalMetricJet_gamma hs, physicalTensorJet]
  simp [coordinateTensorCovariant, coordinateConnectionVector, metricPair,
    CKSRealizedRound.basis, Pi.single_apply, mul_comm]

theorem physicalMetricJet_momentum {G K : PhysicalPoint → AmbientMat}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x) (hk : ContDiffAt ℝ ∞ K x)
    (h0 : (G x).det ≠ 0) (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (i : Fin 3) :
    momentumCovector G K x i = (physicalMetricJet G x).momentum (physicalTensorJet K x) i := by
  simp only [momentumCovector, coordinateMomentum,
    matrix_inverse_trace_coordinates hs.self_of_nhds, Matrix.of_apply,
    physicalMetricJet_tensorCovariant hs.self_of_nhds, physicalMetricJet_dTrace hg hk h0 hs,
    CKSRound.MetricJet.momentum, CKSRound.MetricJet.tensorDivergence]
  rfl

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalMetricJet_energy {G K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (hks : (K x).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    physicalEnergy G K E x = (physicalMetricJet G x).energy (physicalTensorJet K x) := by
  unfold physicalEnergy CKSRound.MetricJet.energy
  rw [physicalMetricJet_scalar hg he hp hs ho, physicalMetricJet_trace hp.isHermitian,
    physicalMetricJet_normSq hp.isHermitian hks]

theorem physical_coordinate_DEC_iff {G K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (hk : ContDiffAt ℝ ∞ K x) (he : ∀ i, ContDiffAt ℝ ∞ (E i) x)
    (hp : (G x).PosDef) (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (hks : (K x).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    physicalDEC G K E x ↔ CKSLocalBending.DEC (physicalMetricJet G x) (physicalTensorJet K x)
 := by
  have hn : metricPair (G x)⁻¹ (momentumCovector G K x) (momentumCovector G K x) =
      CKSLocalBending.momentumSq (physicalMetricJet G x) (physicalTensorJet K x) := by
    simp only [metricPair, physicalMetricJet_momentum hg hk hp.det_pos.ne' hs]
    rfl
  unfold physicalDEC CKSLocalBending.DEC
  rw [hn, physicalMetricJet_energy hg he hp hs hks ho]

end
end CKSAngularGeometry

end






noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

structure SmoothOrthonormalAt (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : Prop where
  metric_smooth : ContDiffAt ℝ ∞ G x
  frame_smooth : ∀ i, ContDiffAt ℝ ∞ (E i) x
  positive : (G x).PosDef
  symmetric : ∀ᶠ y in 𝓝 x, (G y).IsHermitian
  orthonormal : ∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0

structure FrameChartAt (φ : PhysicalPoint → PhysicalPoint)
    (G H : PhysicalPoint → AmbientMat) (E F : LocalFrame) (x : PhysicalPoint) : Prop where
  chart_smooth : ContDiffAt ℝ ∞ φ x
  source : SmoothOrthonormalAt G E (φ x)
  target : SmoothOrthonormalAt H F x
  frame_related : ∀ᶠ y in 𝓝 x, ∀ i, fderiv ℝ φ y (F i y) = E i (φ y)
  metric_related : ∀ v w, metricPair (H x) v w =
    metricPair (G (φ x)) (fderiv ℝ φ x v) (fderiv ℝ φ x w)
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma actualFrameBracket_eq_lieBracket {E : LocalFrame} {x : PhysicalPoint}
    (he : ∀ i, DifferentiableAt ℝ (E i) x) (i j : Fin 3) :
    actualFrameBracket E x i j = VectorField.lieBracket ℝ (E i) (E j) x := by
  ext k
  simp only [actualFrameBracket,D,VectorField.lieBracket,Pi.sub_apply,
    fderiv_apply (he j),fderiv_apply (he i),ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
lemma FrameChartAt.bracket_related {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x) (i j : Fin 3) :
    fderiv ℝ φ x (actualFrameBracket F x i j) = actualFrameBracket E (φ x) i j := by
  have hdφ := h.chart_smooth.differentiableAt (by simp)
  have hde k := (h.source.frame_smooth k).differentiableAt (by simp)
  have hdf k := (h.target.frame_smooth k).differentiableAt (by simp)
  have hr k : (fun y => fderiv ℝ φ y (F k y)) =ᶠ[𝓝 x] (fun y => E k (φ y)) :=
    h.frame_related.mono (fun y hy => hy k)
  rw [actualFrameBracket_eq_lieBracket hdf]
  rw [VectorField.fderiv_apply_lieBracket h.chart_smooth (by rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out) (hdf j) (hdf i)]
  rw [(hr j).fderiv_eq,(hr i).fderiv_eq,
    fderiv_fun_comp x (hde j) hdφ,fderiv_fun_comp x (hde i) hdφ]
  simp only [ContinuousLinearMap.comp_apply,h.frame_related.self_of_nhds]
  exact (actualFrameBracket_eq_lieBracket hde i j).symm
lemma FrameChartAt.bracket_coefficients {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x) :
    frameBracketCoefficient H F x = frameBracketCoefficient G E (φ x) := by
  funext i j k
  unfold frameBracketCoefficient
  rw [h.metric_related,h.bracket_related,h.frame_related.self_of_nhds k]
lemma FrameChartAt.connection_coefficients {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x) :
    frameCoefficient H F x = frameCoefficient G E (φ x) := by
  have hs := h.source
  have ht := h.target
  rw [physical_frame_koszul (ht.metric_smooth.differentiableAt (by simp))
    (fun i => (ht.frame_smooth i).differentiableAt (by simp)) ht.positive ht.symmetric ht.orthonormal]
  rw [physical_frame_koszul (hs.metric_smooth.differentiableAt (by simp))
    (fun i => (hs.frame_smooth i).differentiableAt (by simp)) hs.positive hs.symmetric hs.orthonormal]
  rw [h.bracket_coefficients]

lemma D_chart_related {φ : PhysicalPoint → PhysicalPoint}
    {f g : PhysicalPoint → ℝ} {v w x : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ x) (hf : DifferentiableAt ℝ f (φ x))
    (hvw : fderiv ℝ φ x v = w) (hfg : g =ᶠ[𝓝 x] (fun y => f (φ y))) :
    D v g x = D w f (φ x) := by
  unfold D
  rw [hfg.fderiv_eq,fderiv_fun_comp x hf hφ,ContinuousLinearMap.comp_apply,hvw]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma frame_connection_direction_chart {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y) (a i j k : Fin 3) :
    D (F a x) (fun y => frameCoefficient H F y i j k) x =
      D (E a (φ x)) (fun y => frameCoefficient G E y i j k) (φ x) := by
  have hx := h.self_of_nhds
  apply D_chart_related (hx.chart_smooth.differentiableAt (by simp))
    ((frameCoefficient_contDiffAt hx.source.metric_smooth hx.source.positive.det_pos.ne'
      hx.source.frame_smooth i j k).differentiableAt (by simp))
    (hx.frame_related.self_of_nhds a)
  filter_upwards [h] with y hy
  exact congrFun (congrFun (congrFun hy.connection_coefficients i) j) k
lemma actualFrameCurvature_chart_covariance {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y) (i j k l : Fin 3) :
    actualFrameCurvature H F x i j k l = actualFrameCurvature G E (φ x) i j k l := by
  unfold actualFrameCurvature
  rw [frame_connection_direction_chart h,frame_connection_direction_chart h,
    h.self_of_nhds.connection_coefficients,h.self_of_nhds.bracket_coefficients]
lemma actualFrameScalar_chart_covariance {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y) :
    actualFrameScalar H F x = actualFrameScalar G E (φ x) := by
  unfold actualFrameScalar
  simp_rw [actualFrameCurvature_chart_covariance h]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma frameTensor_chart_covariance {φ : PhysicalPoint → PhysicalPoint}
    {G H K L : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x)
    (hkl : ∀ v w, metricPair (L x) v w =
      metricPair (K (φ x)) (fderiv ℝ φ x v) (fderiv ℝ φ x w)) :
    frameTensor L F x = frameTensor K E (φ x) := by
  funext i j
  unfold frameTensor
  rw [hkl,h.frame_related.self_of_nhds i,h.frame_related.self_of_nhds j]
lemma frame_tensor_direction_chart {φ : PhysicalPoint → PhysicalPoint}
    {G H K L : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y)
    (hk : ContDiffAt ℝ ∞ K (φ x))
    (hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (L y) v w =
      metricPair (K (φ y)) (fderiv ℝ φ y v) (fderiv ℝ φ y w)) (a i j : Fin 3) :
    D (F a x) (fun y => frameTensor L F y i j) x =
      D (E a (φ x)) (fun y => frameTensor K E y i j) (φ x) := by
  have hx := h.self_of_nhds
  apply D_chart_related (hx.chart_smooth.differentiableAt (by simp))
    ((metricPair_contDiffAt hk (hx.source.frame_smooth i) (hx.source.frame_smooth j)).differentiableAt (by simp))
    (hx.frame_related.self_of_nhds a)
  filter_upwards [h,hkl] with y hy hky
  exact congrFun (congrFun (frameTensor_chart_covariance hy hky) i) j
lemma actualFrameTensorCovariant_chart_covariance {φ : PhysicalPoint → PhysicalPoint}
    {G H K L : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y)
    (hk : ContDiffAt ℝ ∞ K (φ x))
    (hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (L y) v w =
      metricPair (K (φ y)) (fderiv ℝ φ y v) (fderiv ℝ φ y w)) (i j k : Fin 3) :
    actualFrameTensorCovariant H L F x i j k = actualFrameTensorCovariant G K E (φ x) i j k := by
  unfold actualFrameTensorCovariant
  rw [frame_tensor_direction_chart h hk hkl,h.self_of_nhds.connection_coefficients,
    frameTensor_chart_covariance h.self_of_nhds hkl.self_of_nhds]

theorem actual_constraints_chart_covariance
    {φ : PhysicalPoint → PhysicalPoint} {G H K L : PhysicalPoint → AmbientMat}
    {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y)
    (hk : ContDiffAt ℝ ∞ K (φ x))
    (hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (L y) v w =
      metricPair (K (φ y)) (fderiv ℝ φ y v) (fderiv ℝ φ y w)) :
    actualFrameScalar H F x = actualFrameScalar G E (φ x) ∧
    actualFrameEnergy H L F x = actualFrameEnergy G K E (φ x) ∧
    (∀ i, actualFrameMomentum H L F x i = actualFrameMomentum G K E (φ x) i)
 := by
  have hs := actualFrameScalar_chart_covariance h
  have ht := frameTensor_chart_covariance h.self_of_nhds hkl.self_of_nhds
  refine ⟨hs,?_,?_⟩
  · unfold actualFrameEnergy
    rw [hs,ht]
  · intro j
    unfold actualFrameMomentum
    simp_rw [actualFrameTensorCovariant_chart_covariance h hk hkl,
      frame_tensor_direction_chart h hk hkl]
end
end CKSAngularGeometry

end


noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def coordinatePullback (φ : PhysicalPoint → PhysicalPoint)
    (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : AmbientMat := fun i j =>
  metricPair (G (φ x)) (fderiv ℝ φ x (CKSRealizedRound.basis i))
    (fderiv ℝ φ x (CKSRealizedRound.basis j))
def coordinatePullbackFrame (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (E : LocalFrame) : LocalFrame := fun i x => fderiv ℝ e.symm (e x) (E i (e x))
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma metricPair_sum_right (g : AmbientMat) (v : PhysicalPoint) (w : Fin 3 → PhysicalPoint) :
    metricPair g v (∑ i, w i) = ∑ i, metricPair g v (w i) := by
  simp only [metricPair,Fin.sum_univ_three,Pi.add_apply]
  ring
lemma coordinatePullback_pair (φ : PhysicalPoint → PhysicalPoint)
    (G : PhysicalPoint → AmbientMat) (x v w : PhysicalPoint) :
    metricPair (coordinatePullback φ G x) v w =
      metricPair (G (φ x)) (fderiv ℝ φ x v) (fderiv ℝ φ x w) := by
  conv_rhs => arg 2; rw [direction_expansion v]
  conv_rhs => arg 3; rw [direction_expansion w]
  simp only [map_sum,map_smul]
  simp only [metricPair_sum_left,metricPair_sum_right,metricPair_smul_left,
    metricPair_smul_right,Finset.mul_sum]
  change (∑ i, ∑ j, metricPair (G (φ x))
    (fderiv ℝ φ x (CKSRealizedRound.basis i))
    (fderiv ℝ φ x (CKSRealizedRound.basis j)) * v i * w j) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma metricPair_dotProduct (g : AmbientMat) (v : PhysicalPoint) :
    metricPair g v v = star v ⬝ᵥ (g *ᵥ v) := by
  simp only [metricPair,dotProduct,mulVec,star_trivial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma coordinatePullback_symmetric {φ : PhysicalPoint → PhysicalPoint}
    {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint} (hg : (G (φ x)).IsHermitian) :
    (coordinatePullback φ G x).IsHermitian := by
  ext i j
  simpa only [conjTranspose_apply,star_trivial,coordinatePullback] using
    metricPair_symm hg (fderiv ℝ φ x (CKSRealizedRound.basis j))
      (fderiv ℝ φ x (CKSRealizedRound.basis i))
lemma coordinatePullback_positive {φ : PhysicalPoint → PhysicalPoint}
    {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint} (hg : (G (φ x)).PosDef)
    (hφ : Function.Injective (fderiv ℝ φ x)) : (coordinatePullback φ G x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (coordinatePullback_symmetric hg.isHermitian)
  intro v hv
  rw [← metricPair_dotProduct,coordinatePullback_pair,metricPair_dotProduct]
  exact hg.dotProduct_mulVec_pos (fun h => hv (hφ (h.trans (map_zero _).symm)))
lemma coordinatePullback_smooth {φ : PhysicalPoint → PhysicalPoint}
    {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hφ : ContDiffAt ℝ ∞ φ x) (hg : ContDiffAt ℝ ∞ G (φ x)) :
    ContDiffAt ℝ ∞ (coordinatePullback φ G) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact metricPair_contDiffAt (hg.comp x hφ)
    ((hφ.fderiv_right (by simp)).clm_apply contDiffAt_const)
    ((hφ.fderiv_right (by simp)).clm_apply contDiffAt_const)
lemma chart_fderiv_left_inverse
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : DifferentiableAt ℝ e x) (hi : DifferentiableAt ℝ e.symm (e x))
    (v : PhysicalPoint) : fderiv ℝ e.symm (e x) (fderiv ℝ e x v) = v := by
  have hEq : (fun y => e.symm (e y)) =ᶠ[𝓝 x] id := e.eventually_left_inverse hx
  have hh := hEq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp x hi he,fderiv_id] at hh
  exact congrArg (fun T : PhysicalPoint →L[ℝ] PhysicalPoint => T v) hh
lemma chart_fderiv_right_inverse
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : DifferentiableAt ℝ e x) (hi : DifferentiableAt ℝ e.symm (e x))
    (v : PhysicalPoint) : fderiv ℝ e x (fderiv ℝ e.symm (e x) v) = v := by
  have hh := chart_fderiv_left_inverse e.symm (e.map_source hx) hi
    (by simpa only [e.left_inv hx,OpenPartialHomeomorph.symm_symm] using he) v
  simpa only [e.left_inv hx,OpenPartialHomeomorph.symm_symm] using hh
lemma coordinatePullbackFrame_smooth
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint) (E : LocalFrame)
    {x : PhysicalPoint} (he : ContDiffAt ℝ ∞ e x) (hi : ContDiffAt ℝ ∞ e.symm (e x))
    (hE : ∀ i, ContDiffAt ℝ ∞ (E i) (e x)) (i : Fin 3) :
    ContDiffAt ℝ ∞ (coordinatePullbackFrame e E i) x :=
  ((hi.fderiv_right (by simp)).comp x he).clm_apply ((hE i).comp x he)
end
end CKSAngularGeometry

end


noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
theorem actualFrameTensorCovariant_coordinate_general {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x)
    (hk : DifferentiableAt ℝ K x) (i j k : Fin 3) :
    actualFrameTensorCovariant G K E x i j k =
      coordinateTensorCovariant G K (E i x) (E j x) (E k x) x := by
  have ho := h.orthonormal.self_of_nhds
  have hleft := metricPair_frame_left (K x) (e := Matrix.of (fun a b => E a x b))
    ho (covariantVector G (E i x) (E j) x) (E k x)
  have hright := metricPair_frame_right (K x) (e := Matrix.of (fun a b => E a x b))
    ho (covariantVector G (E i x) (E k) x) (E j x)
  change (∑ a, metricPair (G x) (covariantVector G (E i x) (E j) x) (E a x)*
    metricPair (K x) (E a x) (E k x)) = _ at hleft
  change (∑ a, metricPair (G x) (covariantVector G (E i x) (E k) x) (E a x)*
    metricPair (K x) (E j x) (E a x)) = _ at hright
  rw [coordinateTensorCovariant_product_rule hk ((h.frame_smooth j).differentiableAt (by simp)) ((h.frame_smooth k).differentiableAt (by simp))]
  unfold actualFrameTensorCovariant
  rw [Finset.sum_add_distrib]
  change D (E i x) (fun y => metricPair (K y) (E j y) (E k y)) x -
    ((∑ a, metricPair (G x) (covariantVector G (E i x) (E j) x) (E a x)*
      metricPair (K x) (E a x) (E k x)) +
     ∑ a, metricPair (G x) (covariantVector G (E i x) (E k) x) (E a x)*
      metricPair (K x) (E j x) (E a x)) = _
  rw [hleft,hright]
  ring

lemma frame_trace_derivative_general {G K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x) (hk : DifferentiableAt ℝ K x)
    (e : PhysicalPoint) :
    (∑ i, D e (fun y => frameTensor K E y i i) x)=
      D e (fun y => ((G y)⁻¹*K y).trace) x := by
  change (∑ i, D e (fun y => metricPair (K y) (E i y) (E i y)) x) = _
  rw [← D_sum3 e _ (fun i => metricPair_differentiableAt hk ((h.frame_smooth i).differentiableAt (by simp)) ((h.frame_smooth i).differentiableAt (by simp)))]
  apply D_congr
  filter_upwards [h.orthonormal] with y hy
  exact frame_trace_exact (K y) (e := Matrix.of (fun i j => E i y j)) hy

theorem actualFrameEnergy_coordinate_general {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x)
    (hk : (K x).IsHermitian) :
    actualFrameEnergy G K E x =
      (actualFrameScalar G E x+((G x)⁻¹*K x).trace^2-
        ((G x)⁻¹*K x*(G x)⁻¹*K x).trace)/2 := by
  have ho := h.orthonormal.self_of_nhds
  have ht := frame_trace_exact (K x) (e := Matrix.of (fun i j => E i x j)) ho
  have hn := frame_tensor_norm_exact hk (e := Matrix.of (fun i j => E i x j)) ho
  change (∑ i, metricPair (K x) (E i x) (E i x))=_ at ht
  change (∑ i, ∑ j, (metricPair (K x) (E i x) (E j x))^2)=_ at hn
  unfold actualFrameEnergy frameTensor
  rw [ht,hn]

theorem actualFrameMomentum_coordinate_general {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x)
    (hk : DifferentiableAt ℝ K x) (j : Fin 3) :
    actualFrameMomentum G K E x j=coordinateMomentum G K x (E j x) := by
  have ht := frame_trace_exact
    (Matrix.of (fun a b => coordinateTensorCovariant G K
      (CKSRealizedRound.basis a) (CKSRealizedRound.basis b) (E j x) x))
    (e := Matrix.of (fun a b => E a x b)) h.orthonormal.self_of_nhds
  change (∑ i, metricPair
    (fun a b => coordinateTensorCovariant G K (CKSRealizedRound.basis a)
      (CKSRealizedRound.basis b) (E j x) x) (E i x) (E i x)) = _ at ht
  have hd : (∑ i, actualFrameTensorCovariant G K E x i i j) =
      ((G x)⁻¹ * Matrix.of (fun a b => coordinateTensorCovariant G K
        (CKSRealizedRound.basis a) (CKSRealizedRound.basis b) (E j x) x)).trace := by
    rw [← ht]
    apply Finset.sum_congr rfl
    intro i _
    rw [actualFrameTensorCovariant_coordinate_general h hk]
    exact coordinateTensorCovariant_bilinear G K x (E i x) (E i x) (E j x)
  unfold actualFrameMomentum coordinateMomentum
  rw [hd,frame_trace_derivative_general h hk]

theorem physical_momentum_frame_norm_general {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x)
    (hk : DifferentiableAt ℝ K x) :
    (∑ a, (actualFrameMomentum G K E x a)^2)=
      metricPair (G x)⁻¹ (momentumCovector G K x) (momentumCovector G K x) := by
  conv_lhs => arg 2; ext a; rw [actualFrameMomentum_coordinate_general h hk,coordinateMomentum_expansion]
  exact covector_frame_square (momentumCovector G K x)
    (e := Matrix.of (fun i j => E i x j)) h.orthonormal.self_of_nhds

end
end CKSAngularGeometry

end


noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma smooth_coordinate_pullback_frame_at
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ContDiffAt ℝ ∞ e x) (hi : ContDiffAt ℝ ∞ e.symm (e x))
    (hSrc : SmoothOrthonormalAt G E (e x)) :
    FrameChartAt e G (coordinatePullback e G) E (coordinatePullbackFrame e E) x := by
  have hed := he.differentiableAt (by simp)
  have hid := hi.differentiableAt (by simp)
  have hEinj : Function.Injective (fderiv ℝ e x) := by
    intro v w h
    have hh := congrArg (fderiv ℝ e.symm (e x)) h
    simpa only [chart_fderiv_left_inverse e hx hed hid] using hh
  have hRel : ∀ᶠ y in 𝓝 x, ∀ i, fderiv ℝ e y (coordinatePullbackFrame e E i y) = E i (e y) := by
    filter_upwards [e.open_source.mem_nhds hx,(he.of_le (show 1 ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp),
      he.continuousAt.eventually ((hi.of_le (show 1 ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp))] with y hy hey hiy i
    exact chart_fderiv_right_inverse e hy (hey.differentiableAt (by simp))
      (hiy.differentiableAt (by simp)) _
  have hOrth : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (coordinatePullback e G y) (coordinatePullbackFrame e E i y)
        (coordinatePullbackFrame e E j y) = if i=j then 1 else 0 := by
    filter_upwards [hRel,he.continuousAt.eventually hSrc.orthonormal] with y hyr hyo i j
    rw [coordinatePullback_pair,hyr i,hyr j,hyo]
  refine ⟨he,hSrc,?_,hRel,coordinatePullback_pair e G x⟩
  refine ⟨coordinatePullback_smooth he hSrc.metric_smooth,
    coordinatePullbackFrame_smooth e E he hi hSrc.frame_smooth,
    coordinatePullback_positive hSrc.positive hEinj,?_,hOrth⟩
  exact (he.continuousAt.eventually hSrc.symmetric).mono fun _ h => coordinatePullback_symmetric h

theorem local_coordinate_DEC_pullback
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y)
    (hi : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ e.symm y)
    (hE : ∀ᶠ y in 𝓝 (e x), SmoothOrthonormalAt G E y)
    (hK : ContDiffAt ℝ ∞ K (e x)) (hs : (K (e x)).IsHermitian) :
    CKSLocalBending.DEC (physicalMetricJet (coordinatePullback e G) x)
      (physicalTensorJet (coordinatePullback e K) x) ↔
    CKSLocalBending.DEC (physicalMetricJet G (e x)) (physicalTensorJet K (e x)) := by
  have h : ∀ᶠ y in 𝓝 x, FrameChartAt e G (coordinatePullback e G) E
      (coordinatePullbackFrame e E) y := by
    filter_upwards [e.open_source.mem_nhds hx,he,
      he.self_of_nhds.continuousAt.eventually hi,he.self_of_nhds.continuousAt.eventually hE]
      with y hy hey hiy hEy
    exact smooth_coordinate_pullback_frame_at e G E hy hey hiy hEy
  have hc := h.self_of_nhds
  have hk' := coordinatePullback_smooth hc.chart_smooth hK
  have hkSymm := coordinatePullback_symmetric hs
  have hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (coordinatePullback e K y) v w =
      metricPair (K (e y)) (fderiv ℝ e y v) (fderiv ℝ e y w) :=
    Eventually.of_forall fun y => coordinatePullback_pair e K y
  obtain ⟨_,hC,hJ⟩ := actual_constraints_chart_covariance h hK hkl
  have hδ : physicalEnergy (coordinatePullback e G) (coordinatePullback e K)
      (coordinatePullbackFrame e E) x = physicalEnergy G K E (e x) := by
    rw [actualFrameEnergy_coordinate_general hc.target hkSymm,
      actualFrameEnergy_coordinate_general hc.source hs] at hC
    exact hC
  rw [← physical_coordinate_DEC_iff hc.target.metric_smooth hk' hc.target.frame_smooth
    hc.target.positive hc.target.symmetric hkSymm hc.target.orthonormal,
    ← physical_coordinate_DEC_iff hc.source.metric_smooth hK hc.source.frame_smooth
      hc.source.positive hc.source.symmetric hs hc.source.orthonormal]
  unfold physicalDEC
  rw [← physical_momentum_frame_norm_general hc.target (hk'.differentiableAt (by simp)),
    ← physical_momentum_frame_norm_general hc.source (hK.differentiableAt (by simp)), hδ]
  simp_rw [hJ]
end
end CKSAngularGeometry

end










noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set CKSSphericalChart CKSRealizedRound
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma SmoothOrthonormalAt.congr_metric {G H : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (hg : SmoothOrthonormalAt G E x)
    (h : H =ᶠ[𝓝 x] G) : SmoothOrthonormalAt H E x := by
  refine ⟨hg.metric_smooth.congr_of_eventuallyEq h, hg.frame_smooth, ?_, ?_, ?_⟩
  · rw [h.self_of_nhds]
    exact hg.positive
  · filter_upwards [h,hg.symmetric] with y hy hs
    rwa [hy]
  · filter_upwards [h,hg.orthonormal] with y hy ho
    rwa [hy]

end
end CKSAngularGeometry

end


























noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma foliation_smoothOrthonormalAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    SmoothOrthonormalAt (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x := by
  have ha := (foliation_actualAdaptedAt hU hγ hs h0 hp).self_of_nhds
  exact ⟨foliationMetric_contDiffAt hU hγ hs h0,
    adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds,ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2.1⟩

end
end CKSAngularGeometry

end



noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry
open scoped BigOperators
lemma spatialCoefficients_pair (A : SpatialTensor) (y v w : PhysicalPoint) :
    metricPair (spatialCoefficients A y) v w =
      A (CKSCartesianOuter.toPoint.symm y) (CKSCartesianOuter.toPoint.symm v)
        (CKSCartesianOuter.toPoint.symm w) := by
  conv_rhs => rw [← CKSMixedGeometry.sum_coordinate_basis v,
    ← CKSMixedGeometry.sum_coordinate_basis w]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,
    smul_eq_mul,spatialCoefficients,metricPair]
  simp only [Fin.sum_univ_three]
  ring

end
end CKSLorentz

end




noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
lemma sourceSpatial_symmetric {A : SpatialTensor} {x : E}
    (hA : ∀ v w, A x v w = A x w v) :
    ∀ v w, sourceSpatial A x v w = sourceSpatial A x w v := by
  intro v w
  change hyperbolicField x v w + A x v w = hyperbolicField x w v + A x w v
  rw [hA v w,hyperbolicField_apply,hyperbolicField_apply]
  simp only [hyperbolicMetric,real_inner_comm v w]
  ring

end
end CKSLorentz

end


noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry
open scoped BigOperators

def matrixLeaf (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : Mat :=
  fun i j => G x i.succ j.succ
def matrixMixed (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : Point :=
  fun i => G x 0 i.succ
def matrixShift (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : Point :=
  fun i => ∑ j, inverse (matrixLeaf G x) i j * matrixMixed G x j
def matrixSchur (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : ℝ :=
  G x 0 0 - ∑ i, ∑ j, inverse (matrixLeaf G x) i j * (matrixMixed G x i * matrixMixed G x j)
def matrixLapse (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : ℝ :=
  1/Real.sqrt (matrixSchur G x)
def matrixFrame (G : PhysicalPoint → AmbientMat) : LocalFrame :=
  fun i x => adaptedFrame (matrixLapse G x) (matrixLeaf G x) (matrixShift G x) i
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry Matrix Set Filter
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
lemma actual_matrix_block {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : (G x).IsHermitian) :
    metricBlock (G x 0 0) (matrixMixed G x) (matrixLeaf G x) = G x := by
  have h10 := hermitian_real_symmetry hs 1 0
  have h20 := hermitian_real_symmetry hs 2 0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [metricBlock,matrixMixed,matrixLeaf,h10,h20]
lemma actual_matrix_leaf_pos {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hp : (G x).PosDef) : (matrixLeaf G x).PosDef :=
  hp.submatrix (Fin.succ_injective 2)
lemma actual_matrix_schur_pos {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hp : (G x).PosDef) : 0 < matrixSchur G x := by
  apply metricBlock_schur_positive
  rwa [actual_matrix_block hp.isHermitian]
lemma actual_matrix_foliation {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hp : (G x).PosDef) :
    foliationMetric (matrixLapse G x) (matrixLeaf G x) (matrixShift G x) = G x := by
  have hq : determinant (matrixLeaf G x) ≠ 0 := by
    rw [determinant_eq]; exact (actual_matrix_leaf_pos hp).det_pos.ne'
  have hs := actual_matrix_schur_pos hp
  have hr : 1/(matrixLapse G x)^2 = matrixSchur G x := by
    rw [matrixLapse,div_pow,one_pow,Real.sq_sqrt hs.le]
    field_simp
  unfold foliationMetric
  rw [hr]
  have hv : (fun a => ∑ b, matrixLeaf G x a b * matrixShift G x b) = matrixMixed G x := by
    funext a
    exact inverse_mul_vector (matrixLeaf G x) hq (matrixMixed G x) a
  rw [hv,← actual_matrix_block hp.isHermitian]
  congr 1
  unfold matrixSchur matrixShift
  rw [inverse_quadratic _ hq]
  ring
lemma actual_matrix_frame {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hG : ContDiffAt ℝ ∞ G x) (hp : ∀ᶠ y in 𝓝 x, (G y).PosDef) :
    SmoothOrthonormalAt G (matrixFrame G) x := by
  have hq : ContDiffAt ℝ ∞ (matrixLeaf G) x :=
    contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => contDiffAt_pi.mp (contDiffAt_pi.mp hG _) _
  have hb : ContDiffAt ℝ ∞ (matrixMixed G) x :=
    contDiffAt_pi.mpr fun i => contDiffAt_pi.mp (contDiffAt_pi.mp hG _) _
  have hz : determinant (matrixLeaf G x) ≠ 0 := by
    rw [determinant_eq]; exact (actual_matrix_leaf_pos hp.self_of_nhds).det_pos.ne'
  have hi := inverse_smoothAt hq hz
  have hshift : ContDiffAt ℝ ∞ (matrixShift G) x :=
    contDiffAt_pi.mpr fun i => ContDiffAt.sum fun j _ =>
      (contDiffAt_pi.mp (contDiffAt_pi.mp hi i) j).mul (contDiffAt_pi.mp hb j)
  have hschur : ContDiffAt ℝ ∞ (matrixSchur G) x :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hG 0) 0).sub
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
        (contDiffAt_pi.mp (contDiffAt_pi.mp hi i) j).mul
          ((contDiffAt_pi.mp hb i).mul (contDiffAt_pi.mp hb j)))
  have hpos := actual_matrix_schur_pos hp.self_of_nhds
  have hu : ContDiffAt ℝ ∞ (matrixLapse G) x :=
    contDiffAt_const.div (hschur.sqrt hpos.ne') (Real.sqrt_ne_zero'.mpr hpos)
  have hpU : 0 < matrixLapse G x := one_div_pos.mpr (Real.sqrt_pos.mpr hpos)
  have h := foliation_smoothOrthonormalAt hu hq hshift hpU.ne'
    (hp.mono fun _ h => actual_matrix_leaf_pos h)
  exact h.congr_metric (hp.mono fun _ h => (actual_matrix_foliation h).symm)
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
attribute [local instance] OAI.CKSLorentz.sgpNorm
attribute [local instance] OAI.CKSLorentz.sgpSpace
lemma spatialTensorPullback_smooth {F : E → E} {A : SpatialTensor} {x : E}
    (hF : ContDiffAt ℝ ∞ F x) (hA : ContDiffAt ℝ ∞ A (F x)) :
    ContDiffAt ℝ ∞ (spatialTensorPullback F A) x := by
  have hD := hF.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)
  have hf : ContDiff ℝ ∞ (fun B : SpatialBilinear => B.flip) := by
    let L : SpatialBilinear →L[ℝ] SpatialBilinear :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff
  exact hf.contDiffAt.comp _ ((hf.contDiffAt.comp _ ((hA.comp x hF).clm_comp hD)).clm_comp hD)
lemma spatialCoefficients_smooth {A : SpatialTensor} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) :
    ContDiffAt ℝ ∞ (spatialCoefficients A) (CKSCartesianOuter.toPoint x) := by
  have h := hA.comp (CKSCartesianOuter.toPoint x) CKSCartesianOuter.toPoint.symm.contDiff.contDiffAt
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  exact (h.clm_apply contDiffAt_const).clm_apply contDiffAt_const
lemma spatialCoefficients_symmetric {A : SpatialTensor} {x : E}
    (hA : ∀ v w, A x v w = A x w v) :
    (spatialCoefficients A (CKSCartesianOuter.toPoint x)).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  simpa [spatialCoefficients] using (hA (CKSCartesianOuter.toPoint.symm (CKSMixedGeometry.basis i))
    (CKSCartesianOuter.toPoint.symm (CKSMixedGeometry.basis j))).symm
lemma spatialCoefficients_positive {A : SpatialTensor} {x : E}
    (hA : ∀ v w, A x v w = A x w v)
    (hp : ∀ v : E, v ≠ 0 → 0 < A x v v) :
    (spatialCoefficients A (CKSCartesianOuter.toPoint x)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (spatialCoefficients_symmetric hA)
  intro v hv
  have hz : CKSCartesianOuter.toPoint.symm v ≠ 0 := by
    simpa only [map_zero] using CKSCartesianOuter.toPoint.symm.injective.ne hv
  have h := hp _ hz
  have he := spatialCoefficients_pair A (CKSCartesianOuter.toPoint x) v v
  simp only [ContinuousLinearEquiv.symm_apply_apply] at he
  rw [← he] at h
  simpa only [metricPair,dotProduct,Matrix.mulVec,Finset.mul_sum,star_trivial,
    mul_assoc,mul_left_comm,mul_comm] using h
noncomputable def spatialCoordinateHomeomorph (h : E ≃ₜ E) : PhysicalPoint ≃ₜ PhysicalPoint :=
  CKSCartesianOuter.toPoint.symm.toHomeomorph.trans (h.trans CKSCartesianOuter.toPoint.toHomeomorph)

lemma spatialCoordinateHomeomorph_fderiv (h : E ≃ₜ E) {y : PhysicalPoint}
    (hF : DifferentiableAt ℝ h (CKSCartesianOuter.toPoint.symm y)) :
    fderiv ℝ (spatialCoordinateHomeomorph h) y = CKSCartesianOuter.toPoint.toContinuousLinearMap.comp
      ((fderiv ℝ h (CKSCartesianOuter.toPoint.symm y)).comp CKSCartesianOuter.toPoint.symm.toContinuousLinearMap) := by
  change fderiv ℝ (CKSCartesianOuter.toPoint ∘ h ∘ CKSCartesianOuter.toPoint.symm) y = _
  simp only [fderiv_comp y (CKSCartesianOuter.toPoint.differentiableAt) (hF.comp y CKSCartesianOuter.toPoint.symm.differentiableAt),
    fderiv_comp y hF CKSCartesianOuter.toPoint.symm.differentiableAt,ContinuousLinearEquiv.fderiv]
lemma spatialCoefficients_general_pullback (h : E ≃ₜ E) (A : SpatialTensor) {y : PhysicalPoint}
    (hF : DifferentiableAt ℝ h (CKSCartesianOuter.toPoint.symm y)) :
    coordinatePullback (spatialCoordinateHomeomorph h) (spatialCoefficients A) y =
      spatialCoefficients (spatialTensorPullback h A) y := by
  ext i j
  unfold coordinatePullback
  rw [spatialCoefficients_pair,spatialCoordinateHomeomorph_fderiv h hF]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply,spatialCoordinateHomeomorph,Homeomorph.trans_apply,
    ContinuousLinearEquiv.coe_toHomeomorph]
  rfl
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma spatialDEC_pullback (h : E ≃ₜ E) (hF : ContDiff ℝ ∞ h) (hI : ContDiff ℝ ∞ h.symm)
    (G K : SpatialTensor) {U : Set E} (hU : IsOpen U)
    (hGs : ∀ z ∈ U, ContDiffAt ℝ ∞ G z) (hKs : ∀ z ∈ U, ContDiffAt ℝ ∞ K z)
    (hGsym : ∀ z ∈ U, ∀ v w, G z v w = G z w v)
    (hKsym : ∀ z ∈ U, ∀ v w, K z v w = K z w v)
    (hp : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} (hx : h x ∈ U) :
    spatialDEC (spatialTensorPullback h G) (spatialTensorPullback h K) x ↔ spatialDEC G K (h x) := by
  let e := (spatialCoordinateHomeomorph h).toOpenPartialHomeomorph
  have he : ContDiff ℝ ∞ e := CKSCartesianOuter.toPoint.contDiff.comp
    (hF.comp CKSCartesianOuter.toPoint.symm.contDiff)
  have hi : ContDiff ℝ ∞ e.symm := CKSCartesianOuter.toPoint.contDiff.comp
    (hI.comp CKSCartesianOuter.toPoint.symm.contDiff)
  have ex : e (CKSCartesianOuter.toPoint x) = CKSCartesianOuter.toPoint (h x) := by
    simp [e,spatialCoordinateHomeomorph]
  have hc : ∀ y : PhysicalPoint, CKSCartesianOuter.toPoint.symm y ∈ U →
      (spatialCoefficients G y).PosDef := by
    intro y hy
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      spatialCoefficients_positive (hGsym _ hy) (hp _ hy)
  have hn : ∀ᶠ y in 𝓝 (CKSCartesianOuter.toPoint (h x)), CKSCartesianOuter.toPoint.symm y ∈ U := by
    exact CKSCartesianOuter.toPoint.symm.continuous.continuousAt.preimage_mem_nhds
      (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hU.mem_nhds hx)
  have hE : ∀ᶠ y in 𝓝 (e (CKSCartesianOuter.toPoint x)),
      SmoothOrthonormalAt (spatialCoefficients G) (matrixFrame (spatialCoefficients G)) y := by
    rw [ex]
    filter_upwards [hn] with y hy
    apply actual_matrix_frame
    · simpa only [ContinuousLinearEquiv.apply_symm_apply] using spatialCoefficients_smooth (hGs _ hy)
    · filter_upwards [CKSCartesianOuter.toPoint.symm.continuous.continuousAt.preimage_mem_nhds
        (hU.mem_nhds hy)] with z hz
      exact hc z hz
  have hKsm : ContDiffAt ℝ ∞ (spatialCoefficients K) (e (CKSCartesianOuter.toPoint x)) := by
    rw [ex]; exact spatialCoefficients_smooth (hKs _ hx)
  have hKsy : (spatialCoefficients K (e (CKSCartesianOuter.toPoint x))).IsHermitian := by
    rw [ex]; exact spatialCoefficients_symmetric (hKsym _ hx)
  have ht := local_coordinate_DEC_pullback e (spatialCoefficients G) (spatialCoefficients K)
    (matrixFrame (spatialCoefficients G)) (x := CKSCartesianOuter.toPoint x) (by trivial)
    (Eventually.of_forall fun _ => he.contDiffAt) (Eventually.of_forall fun _ => hi.contDiffAt)
    hE hKsm hKsy
  have eqs (F : SpatialTensor) : coordinatePullback e (spatialCoefficients F) =
      spatialCoefficients (spatialTensorPullback h F) := by
    funext y
    exact spatialCoefficients_general_pullback h F (hF.differentiable (by simp)).differentiableAt
  rw [eqs G,eqs K,ex] at ht
  exact ht
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
attribute [local instance] CKSSpatialManifold.real_id_isometric real_smulCommClass
  spatialDual_smulCommClass
attribute [local instance] OAI.CKSLorentz.hsgNorm

attribute [local instance] OAI.CKSLorentz.hsgSpace

attribute [local instance] spatialBilinear_isScalarTower

lemma hyperbolicField_smooth : ContDiff ℝ ∞ hyperbolicField := by
  unfold hyperbolicField
  exact contDiff_const.sub ((contDiff_const.div (contDiff_const.add (contDiff_norm_sq ℝ))
    (fun x => by positivity)).smul ((innerSL ℝ).contDiff.smulRight (innerSL ℝ).contDiff))
lemma sourceSpatial_smooth {A : SpatialTensor} {x : E} (hA : ContDiffAt ℝ ∞ A x) :
    ContDiffAt ℝ ∞ (sourceSpatial A) x := hyperbolicField_smooth.contDiffAt.add hA
lemma sourceSpatial_boost {e : ℝ} {p : E} (he : ‖p‖ < e) (A : SpatialTensor) :
    sourceSpatial (spatialTensorPullback (hyperbolicMap e (mass e p) p) A) =
      spatialTensorPullback (hyperbolicMap e (mass e p) p) (sourceSpatial A) := by
  funext x; ext v w
  change hyperbolicField x v w + A _ _ _ = hyperbolicField _ _ _ + A _ _ _
  rw [hyperbolicField_apply,hyperbolicField_apply]
  exact congrArg (fun z : ℝ => z + A _ _ _) (hyperbolicMap_isometry he (mass_pos he) (mass_sq he) x v w).symm
lemma smoothHomeomorph_fderiv_injective (h : E ≃ₜ E) (hs : ContDiff ℝ ∞ h)
    (hi : ContDiff ℝ ∞ h.symm) (x : E) : Function.Injective (fderiv ℝ h x) := by
  have hc : (fderiv ℝ h.symm (h x)).comp (fderiv ℝ h x) = ContinuousLinearMap.id ℝ E := by
    rw [← fderiv_comp x (hi.differentiable (by simp)).differentiableAt
      (hs.differentiable (by simp)).differentiableAt]
    have hh : h.symm ∘ h = id := funext h.symm_apply_apply
    rw [hh,fderiv_id]
  intro v w hv
  have hi' := congrArg (fderiv ℝ h.symm (h x)) hv
  have hv' := congrArg (fun L : E →L[ℝ] E => L v) hc
  have hw' := congrArg (fun L : E →L[ℝ] E => L w) hc
  change _ = v at hv'; change _ = w at hw'
  exact hv'.symm.trans (hi'.trans hw')

theorem hyperbolic_source_geometry {e : ℝ} {p : E} (he : ‖p‖ < e)
    (A B : SpatialTensor) {U : Set E} (hU : IsOpen U)
    (hAs : ∀ z ∈ U, ContDiffAt ℝ ∞ A z)
    (hBs : ∀ z ∈ U, ContDiffAt ℝ ∞ B z)
    (hA : ∀ z ∈ U, ∀ v w, A z v w = A z w v)
    (hB : ∀ z ∈ U, ∀ v w, B z v w = B z w v)
    (hp : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < sourceSpatial A z v v)
    (hDEC : ∀ z ∈ U, spatialDEC (sourceSpatial A) (sourceSpatial B) z)
    {x : E} (hx : hyperbolicMap e (mass e p) p x ∈ U) :
    let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) A
    let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) B
    ContDiffAt ℝ ∞ A' x ∧ ContDiffAt ℝ ∞ B' x ∧
    (∀ v w, A' x v w = A' x w v) ∧
    (∀ v w, B' x v w = B' x w v) ∧
    (∀ v : E, v ≠ 0 → 0 < sourceSpatial A' x v v) ∧
    spatialDEC (sourceSpatial A') (sourceSpatial B') x := by
  dsimp only
  let h := hyperbolicHomeomorph e p he
  have hs : ContDiff ℝ ∞ h := hyperbolicMap_smooth e (mass e p) p
  have hi : ContDiff ℝ ∞ h.symm := hyperbolicMap_smooth e (mass e p) (-p)
  refine ⟨spatialTensorPullback_smooth hs.contDiffAt (hAs _ hx),
    spatialTensorPullback_smooth hs.contDiffAt (hBs _ hx),?_,?_,?_,?_⟩
  · intro v w; exact hA _ hx _ _
  · intro v w; exact hB _ hx _ _
  · rw [sourceSpatial_boost he]
    intro v hv
    apply hp _ hx
    have hd := smoothHomeomorph_fderiv_injective h hs hi x
    have hz := hd.ne hv
    simp only [map_zero] at hz
    convert hz using 1
    rfl
  · rw [sourceSpatial_boost he,sourceSpatial_boost he]
    exact (spatialDEC_pullback h hs hi (sourceSpatial A) (sourceSpatial B) hU
      (fun z hz => sourceSpatial_smooth (hAs z hz))
      (fun z hz => sourceSpatial_smooth (hBs z hz))
      (fun z hz => sourceSpatial_symmetric (hA z hz))
      (fun z hz => sourceSpatial_symmetric (hB z hz)) hp hx).mpr (hDEC _ hx)
end
end CKSLorentz

end
















































end OAI
end

theorem solution : type_of% @OAI.CKSLorentz.hyperbolic_source_geometry := @OAI.CKSLorentz.hyperbolic_source_geometry
