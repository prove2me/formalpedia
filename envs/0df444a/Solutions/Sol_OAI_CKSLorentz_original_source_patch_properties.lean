-- Prove2me | solution 1 for OAI.CKSLorentz.original_source_patch_properties
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:52:54.047113+00:00
-- url     : https://prove2.me/submissions/f1508e92-757e-46d3-bead-ccac28746dc0

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
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma angularLift_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Angle → E} {x : Point} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f (angularProjection x)) :
    ContDiffAt ℝ n (angularLift f) x := hf.comp x angularProjection.contDiff.contDiffAt

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
open scoped RealInnerProductSpace ContDiff

def hyperbolicMetric (x Y Z : E) : ℝ :=
  inner ℝ Y Z - inner ℝ x Y * inner ℝ x Z / (1+‖x‖^2)

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
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

namespace SmoothAngularPatch

lemma param_tangent (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (v : Angle) : inner ℝ (P.param θ) (fderiv ℝ P.param θ v) = 0 := by
  have hφ := (P.param_contDiffAt hθ).differentiableAt (by simp)
  have hconst : (fun η => inner ℝ (P.param η) (P.param η)) = fun _ : Angle => (1:ℝ) := by
    funext η
    rw [real_inner_self_eq_norm_sq]
    have hn : ‖P.param η‖=1 := P.param_norm η
    rw [hn,one_pow]
  have hd := fderiv_inner_apply (𝕜:=ℝ) hφ hφ v
  rw [hconst] at hd
  simp only [fderiv_fun_const] at hd
  change 0 = inner ℝ (P.param θ) (fderiv ℝ P.param θ v) +
    inner ℝ (fderiv ℝ P.param θ v) (P.param θ) at hd
  have hc := real_inner_comm (fderiv ℝ P.param θ v) (P.param θ)
  linarith

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
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry
open CKSAngularGeometry (metricBlock AmbientMat)

def cksReference (σ : Angle → Mat) (y : Point) : AmbientMat :=
  metricBlock (1/(1+(y 0)^2)) 0 ((y 0)^2 • σ (angularProjection y))
end
end CKSLorentz

end






noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Matrix.Norms.Elementwise
lemma SmoothAngularPatch.roundMetric_contDiffAt (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) : ContDiffAt ℝ ∞ (angularRoundMetric P.param) θ := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  exact ContDiffAt.inner ℝ
    (((P.param_contDiffAt hθ).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)
    (((P.param_contDiffAt hθ).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)
end
end CKSLorentz

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

end
end CKSMixedGeometry

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

lemma sourceRadialK_smoothAt {f : SourceTensorFields} {y : Point} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (sourceRadialK f) y := by
  have hh : ContDiffAt ℝ ∞ (fun z : Point => 1+(z 0)^2) y := by fun_prop
  exact (contDiffAt_const.div hh (by positivity)).add hf.kr

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
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients Set
open scoped BigOperators
lemma bilinear_eq_of_coordinate_basis (B C : Point →L[ℝ] Point →L[ℝ] ℝ)
    (h : ∀ i j, B (basis i) (basis j) = C (basis i) (basis j)) : B = C := by
  ext v w
  rw [← sum_coordinate_basis v,← sum_coordinate_basis w]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,h]
lemma polarLift_components (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) (i j : I) :
    polarTensorComponents P (polarLift P F) i j y = F y i j := by
  have hi := congrArg (fun L : Point →L[ℝ] Point => L (basis i)) (polarInverse_fderiv_left P hr hy)
  have hj := congrArg (fun L : Point →L[ℝ] Point => L (basis j)) (polarInverse_fderiv_left P hr hy)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hi hj
  change matrixBilinear (F (polarInverse P (polarParam P y)))
    (fderiv ℝ (polarInverse P) (polarParam P y) (fderiv ℝ (polarParam P) y (basis i)))
    (fderiv ℝ (polarInverse P) (polarParam P y) (fderiv ℝ (polarParam P) y (basis j))) = _
  rw [polarInverse_param P hr hy,hi,hj]
  simp [matrixBilinear,basis,Pi.single_apply]
lemma polarTensor_ext (P : SmoothAngularPatch) {A B : SpatialTensor}
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (h : ∀ i j, polarTensorComponents P A i j y = polarTensorComponents P B i j y) :
    A (polarParam P y) = B (polarParam P y) := by
  have hh : (A (polarParam P y)).bilinearComp (fderiv ℝ (polarParam P) y) (fderiv ℝ (polarParam P) y) =
      (B (polarParam P y)).bilinearComp (fderiv ℝ (polarParam P) y) (fderiv ℝ (polarParam P) y) :=
    bilinear_eq_of_coordinate_basis _ _ h
  ext v w
  obtain ⟨v,rfl⟩ := polarParam_fderiv_surjective P hr hy v
  obtain ⟨w,rfl⟩ := polarParam_fderiv_surjective P hr hy w
  exact congrArg (fun L : Point →L[ℝ] Point →L[ℝ] ℝ => L v w) hh

theorem polarLift_reconstruction (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (∀ i j, polarTensorComponents P (polarLift P F) i j y = F y i j) ∧
    (∀ A : SpatialTensor, (∀ i j, polarTensorComponents P A i j y = F y i j) →
      polarLift P F (polarParam P y) = A (polarParam P y)) := by
  refine ⟨polarLift_components P F hr hy,?_⟩
  intro A hA
  apply polarTensor_ext P hr hy
  intro i j
  rw [polarLift_components P F hr hy,hA]
end
end CKSLorentz

end























noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry Matrix
open CKSAngularGeometry (metricBlock AmbientMat)
lemma cksSourceFields_gamma (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point) :
    sourceGamma (cksSourceFields σ A B mr mg mK).base y =
      (y 0)^2 • σ (angularProjection y)+Matrix.of (fun a b : Fin 2 => A a.succ b.succ y) := by
  ext a b
  change (y 0)^2 * σ (angularProjection y) a b + 1/(y 0) * mg a.succ b.succ (angularProjection y) +
    (A a.succ b.succ y - ordinaryLeadingComponent 1 (mg a.succ b.succ) y) = _
  simp only [ordinaryLeadingComponent,pow_one,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.of_apply]
  ring
lemma cksSourceFields_tangential (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point) :
    sourceTangentialK (cksSourceFields σ A B mr mg mK).base y =
      (y 0)^2 • σ (angularProjection y)+Matrix.of (fun a b : Fin 2 => B a.succ b.succ y) := by
  ext a b
  change (y 0)^2 * σ (angularProjection y) a b + 1/(y 0) * mK a.succ b.succ (angularProjection y) +
    (B a.succ b.succ y - ordinaryLeadingComponent 1 (mK a.succ b.succ) y) = _
  simp only [ordinaryLeadingComponent,pow_one,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.of_apply]
  ring
lemma cksSourceFields_radial (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point) :
    sourceRadialMetric (cksSourceFields σ A B mr mg mK).base y =
      1/(1+(y 0)^2)+A 0 0 y := by
  simp only [sourceRadialMetric,cksSourceFields,ordinaryLeadingComponent]
  ring
lemma metricBlock_add_perturbation (a : ℝ) (q : Mat) (A : AmbientMat)
    (hA : A.IsHermitian) :
    metricBlock (a+A 0 0) (fun i => A 0 i.succ)
      (q+Matrix.of (fun i k : Fin 2 => A i.succ k.succ)) = metricBlock a 0 q+A := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [metricBlock]
  all_goals exact CKSAngularGeometry.hermitian_real_symmetry hA _ _

theorem cksSourceFields_reconstruct (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point)
    (hA : Matrix.IsHermitian (fun i k => A i k y)) (hB : Matrix.IsHermitian (fun i k => B i k y)) :
    sourceMetric (cksSourceFields σ A B mr mg mK).base y =
      cksReference σ y + Matrix.of (fun i k => A i k y) ∧
    sourceTensor (cksSourceFields σ A B mr mg mK) y =
      cksReference σ y + Matrix.of (fun i k => B i k y) := by
  constructor
  · unfold sourceMetric cksReference
    rw [cksSourceFields_gamma,cksSourceFields_radial]
    exact metricBlock_add_perturbation _ _ _ hA
  · unfold sourceTensor cksReference
    rw [cksSourceFields_tangential]
    exact metricBlock_add_perturbation _ _ _ hB
end
end CKSLorentz

end





noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
lemma hyperbolicField_apply (x v w : E) : hyperbolicField x v w = hyperbolicMetric x v w := by
  change inner ℝ v w - (1/(1+‖x‖^2)) * (inner ℝ x v * inner ℝ x w) =
    inner ℝ v w - inner ℝ x v * inner ℝ x w / (1+‖x‖^2)
  ring
lemma polarParam_fderiv (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) (v : Point) :
    fderiv ℝ (polarParam P) y v = v 0 • P.param (angularProjection y) +
      y 0 • fderiv ℝ P.param (angularProjection y) (angularProjection v) := by
  have hP := (P.param_contDiffAt hy).differentiableAt (by simp)
  have hp := (ContinuousLinearMap.proj (0:I) : Point →L[ℝ] ℝ).hasFDerivAt (x := y)
  have ha := hP.hasFDerivAt.comp y angularProjection.hasFDerivAt
  have hh := hp.smul ha
  change HasFDerivAt (polarParam P) _ y at hh
  rw [hh.fderiv]
  change y 0 • fderiv ℝ P.param (angularProjection y) (angularProjection v) + v 0 • P.param (angularProjection y) = _
  exact add_comm _ _
lemma polarParam_fderiv_radial (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) :
    fderiv ℝ (polarParam P) y (basis 0) = P.param (angularProjection y) := by
  rw [polarParam_fderiv P hy]
  have ha : angularProjection (basis 0) = 0 := by ext a; simp [angularProjection,basis,Fin.succ_ne_zero]
  rw [ha]
  simp [basis]
lemma polarParam_fderiv_angular (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) (a : Fin 2) :
    fderiv ℝ (polarParam P) y (basis a.succ) = y 0 • fderiv ℝ P.param (angularProjection y) (CKSAngularGeometry.basis a) := by
  rw [polarParam_fderiv P hy]
  have ha : angularProjection (basis a.succ) = CKSAngularGeometry.basis a := by
    ext b
    simp [angularProjection,basis,CKSAngularGeometry.basis,Pi.single_apply,Fin.succ_inj]
  rw [ha]
  simp [basis,Fin.succ_ne_zero]
lemma hyperbolicField_polar (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (fun i j => polarTensorComponents P hyperbolicField i j y) = cksReference (angularRoundMetric P.param) y := by
  have hn : ‖P.param (angularProjection y)‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using P.param_sphere (angularProjection y)
  have hi : inner ℝ (P.param (angularProjection y)) (P.param (angularProjection y)) = 1 := by
    rw [real_inner_self_eq_norm_sq,hn,one_pow]
  have ht := P.param_tangent hy
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) j
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis 0))
        (fderiv ℝ (polarParam P) y (basis 0)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_radial P hy]
      unfold hyperbolicMetric
      rw [polarParam_norm P hr.le]
      simp only [polarParam,real_inner_smul_left,hi,mul_one]
      simp only [cksReference,CKSAngularGeometry.metricBlock]
      change 1 - y 0 * y 0/(1+(y 0)^2) = 1/(1+(y 0)^2)
      have hnz : 1 + (y 0)^2 ≠ 0 := by positivity
      field_simp
      ring
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis 0))
        (fderiv ℝ (polarParam P) y (basis b.succ)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_radial P hy,polarParam_fderiv_angular P hy]
      fin_cases b <;> simp [hyperbolicMetric,polarParam,real_inner_smul_left,real_inner_smul_right,ht,cksReference,CKSAngularGeometry.metricBlock]
  · refine Fin.cases ?_ (fun b => ?_) j
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis a.succ))
        (fderiv ℝ (polarParam P) y (basis 0)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_radial P hy,polarParam_fderiv_angular P hy]
      have hta : inner ℝ (fderiv ℝ P.param (angularProjection y) (CKSAngularGeometry.basis a)) (P.param (angularProjection y)) = 0 := by
        rw [real_inner_comm]; exact ht _
      fin_cases a <;> simp_all [hyperbolicMetric,polarParam,real_inner_smul_left,real_inner_smul_right,cksReference,CKSAngularGeometry.metricBlock]
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis a.succ))
        (fderiv ℝ (polarParam P) y (basis b.succ)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_angular P hy,polarParam_fderiv_angular P hy]
      simp only [hyperbolicMetric,polarParam,real_inner_smul_left,real_inner_smul_right,ht,mul_zero,zero_div,sub_zero]
      fin_cases a <;> fin_cases b <;>
        simp [cksReference,CKSAngularGeometry.metricBlock,angularRoundMetric,pow_two,mul_assoc]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry
lemma polarTensorComponents_hermitian (P : SmoothAngularPatch) (A : SpatialTensor)
    (y : CKSMixedGeometry.Point)
    (hA : ∀ v w, A (polarParam P y) v w = A (polarParam P y) w v) :
    Matrix.IsHermitian (fun i j => polarTensorComponents P A i j y) := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  exact hA _ _
lemma polar_sourceSpatial (P : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    cksReference (angularRoundMetric P.param) y + Matrix.of (fun i j => polarTensorComponents P A i j y) =
      (fun i j => polarTensorComponents P (sourceSpatial A) i j y) := by
  rw [← hyperbolicField_polar P hr hy]
  rfl

theorem spatial_source_reconstruction {A B : SpatialTensor} (P : CollarSourcePatch A B)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.patch.chart.target)
    (hA : ∀ v w, A (polarParam P.patch y) v w = A (polarParam P.patch y) w v)
    (hB : ∀ v w, B (polarParam P.patch y) v w = B (polarParam P.patch y) w v) :
    sourceMetric P.fields.base y = (fun i j => polarTensorComponents P.patch (sourceSpatial A) i j y) ∧
    sourceTensor P.fields y = (fun i j => polarTensorComponents P.patch (sourceSpatial B) i j y) ∧
    polarLift P.patch (sourceMetric P.fields.base) (polarParam P.patch y) = sourceSpatial A (polarParam P.patch y) ∧
    polarLift P.patch (sourceTensor P.fields) (polarParam P.patch y) = sourceSpatial B (polarParam P.patch y) := by
  obtain ⟨hg,hk⟩ := cksSourceFields_reconstruct (angularRoundMetric P.patch.param)
    (polarTensorComponents P.patch A) (polarTensorComponents P.patch B) P.mr P.mg P.mK y
    (polarTensorComponents_hermitian P.patch A y hA) (polarTensorComponents_hermitian P.patch B y hB)
  have heg : sourceMetric P.fields.base y = (fun i j => polarTensorComponents P.patch (sourceSpatial A) i j y) :=
    hg.trans (polar_sourceSpatial P.patch A hr hy)
  have hek : sourceTensor P.fields y = (fun i j => polarTensorComponents P.patch (sourceSpatial B) i j y) :=
    hk.trans (polar_sourceSpatial P.patch B hr hy)
  refine ⟨heg,hek,?_,?_⟩
  · apply (polarLift_reconstruction P.patch (sourceMetric P.fields.base) hr hy).2
    intro i j
    exact congrArg (fun F : AmbientMat => F i j) heg.symm
  · apply (polarLift_reconstruction P.patch (sourceTensor P.fields) hr hy).2
    intro i j
    exact congrArg (fun F : AmbientMat => F i j) hek.symm
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
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma coordinatePullback_symm
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint) (G : PhysicalPoint → AmbientMat)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : DifferentiableAt ℝ e x) (hi : DifferentiableAt ℝ e.symm (e x)) :
    coordinatePullback e.symm (coordinatePullback e G) (e x) = G (e x) := by
  ext i j
  change metricPair (coordinatePullback e G (e.symm (e x)))
    (fderiv ℝ e.symm (e x) (CKSRealizedRound.basis i))
    (fderiv ℝ e.symm (e x) (CKSRealizedRound.basis j)) = _
  rw [e.left_inv hx,coordinatePullback_pair,
    chart_fderiv_right_inverse e hx he hi,chart_fderiv_right_inverse e hx he hi]
  simp [metricPair,CKSRealizedRound.basis,Pi.single_apply,mul_ite]
lemma physicalMetricJet_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : physicalMetricJet G x = physicalMetricJet H x := by
  have hc (i j) : (fun y => G y i j) =ᶠ[𝓝 x] (fun y => H y i j) :=
    h.mono fun _ hh => congrFun (congrFun hh i) j
  have hd (a i j) : D (CKSRealizedRound.basis a) (fun y => G y i j) =ᶠ[𝓝 x]
      D (CKSRealizedRound.basis a) (fun y => H y i j) :=
    (hc i j).eventually_nhds.mono fun _ hh => D_congr hh _
  unfold physicalMetricJet
  congr 1
  · exact congrArg Inv.inv h.self_of_nhds
  · funext a i j
    exact D_congr (hc i j) _
  · funext a b i j
    exact D_congr (hd b i j) _
lemma physicalTensorJet_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : physicalTensorJet G x = physicalTensorJet H x := by
  have hc (i j) : (fun y => G y i j) =ᶠ[𝓝 x] (fun y => H y i j) :=
    h.mono fun _ hh => congrFun (congrFun hh i) j
  unfold physicalTensorJet
  congr 1
  · exact h.self_of_nhds
  · funext a i j
    exact D_congr (hc i j) _
theorem local_coordinate_DEC_pushforward
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y)
    (hi : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ e.symm y)
    (hE : ∀ᶠ y in 𝓝 x, SmoothOrthonormalAt (coordinatePullback e G) E y)
    (hK : ContDiffAt ℝ ∞ (coordinatePullback e K) x)
    (hs : (coordinatePullback e K x).IsHermitian) :
    CKSLocalBending.DEC (physicalMetricJet G (e x)) (physicalTensorJet K (e x)) ↔
    CKSLocalBending.DEC (physicalMetricJet (coordinatePullback e G) x)
      (physicalTensorJet (coordinatePullback e K) x) := by
  have hEq (A : PhysicalPoint → AmbientMat) :
      coordinatePullback e.symm (coordinatePullback e A) =ᶠ[𝓝 (e x)] A := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx),hi,
      (e.symm.continuousAt (e.map_source hx)).eventually (e.left_inv hx ▸ he)] with y hy hiy hey
    have hh := coordinatePullback_symm e A (e.map_target hy)
      (hey.differentiableAt (by simp)) (by simpa only [e.right_inv hy] using hiy.differentiableAt (by simp))
    simpa only [e.right_inv hy] using hh
  have h := local_coordinate_DEC_pullback e.symm (coordinatePullback e G)
    (coordinatePullback e K) E (e.map_source hx) hi
    (by simpa only [e.left_inv hx,OpenPartialHomeomorph.symm_symm] using he)
    (by simpa only [e.left_inv hx] using hE)
    (by simpa only [e.left_inv hx] using hK)
    (by simpa only [e.left_inv hx] using hs)
  rw [physicalMetricJet_congr (hEq G),physicalTensorJet_congr (hEq K),e.left_inv hx] at h
  exact h
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
namespace CKSMixedGeometry
noncomputable section
open CKSAngularGeometry
open scoped ContDiff Matrix.Norms.Elementwise
lemma metricBlock_smoothAt {a : Point → ℝ} {b : Point → CKSAngularGeometry.Point}
    {q : Point → Mat} {x : Point}
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x) (hq : ContDiffAt ℝ ∞ q x) :
    ContDiffAt ℝ ∞ (fun y => metricBlock (a y) (b y) (q y)) x := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  refine Fin.cases ?_ (fun c => ?_) i
  · refine Fin.cases ?_ (fun d => ?_) j
    · exact ha
    · fin_cases d <;> simpa [metricBlock] using contDiffAt_pi.mp hb _
  · refine Fin.cases ?_ (fun d => ?_) j
    · fin_cases c <;> simpa [metricBlock] using contDiffAt_pi.mp hb _
    · fin_cases c <;> fin_cases d <;> simpa [metricBlock] using contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _

lemma sourceTensor_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) : ContDiffAt ℝ ∞ (sourceTensor f) y :=
  metricBlock_smoothAt (sourceRadialK_smoothAt hf) hf.kb (sourceTangentialK_smoothAt hf.base hy)
end
end CKSMixedGeometry

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
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

lemma polarCartesianChart_mem (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    y ∈ (polarCartesianChart P hr hy).source :=
  (cartesianPolar_smoothAt P hy).mem_toOpenPartialHomeomorph_source
    (polarDerivative_hasFDerivAt P hr hy) (by simp)
lemma polarCartesianChart_smooth (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ (polarCartesianChart P hr hy) z) ∧
    ∀ᶠ z in 𝓝 (cartesianPolar P y), ContDiffAt ℝ ∞ (polarCartesianChart P hr hy).symm z := by
  let e := polarCartesianChart P hr hy
  have hex : y ∈ e.source := polarCartesianChart_mem P hr hy
  have hnear : ∀ᶠ z in 𝓝 y, 0 < z 0 ∧ angularProjection z ∈ P.chart.target :=
    Filter.inter_mem ((isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hr)
      (angularProjection.continuous.continuousAt.preimage_mem_nhds (P.chart.open_target.mem_nhds hy))
  refine ⟨hnear.mono (fun z hz => cartesianPolar_smoothAt P hz.2),?_⟩
  have hn : ∀ᶠ z in 𝓝 (e y), 0 < (e.symm z) 0 ∧ angularProjection (e.symm z) ∈ P.chart.target :=
    (e.symm.continuousAt (e.map_source hex)).eventually (e.left_inv hex ▸ hnear)
  filter_upwards [e.open_target.mem_nhds (e.map_source hex),hn] with z hz hreg
  exact e.contDiffAt_symm hz (polarDerivative_hasFDerivAt P hreg.1 hreg.2)
    (cartesianPolar_smoothAt P hreg.2)
end
end CKSLorentz

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
lemma spatialCoefficients_pullback (P : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ P.chart.target) :
    coordinatePullback (cartesianPolar P) (spatialCoefficients A) y =
      fun i j => polarTensorComponents P A i j y := by
  ext i j
  unfold coordinatePullback
  rw [spatialCoefficients_pair,cartesianPolar_fderiv P hy]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply,cartesianPolar,polarTensorComponents]
  rfl

end
end CKSLorentz

end



noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma polarTensorComponents_smoothAt (P : SmoothAngularPatch) {A : SpatialTensor}
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ P.chart.target)
    (hA : ContDiffAt ℝ ∞ A (polarParam P y)) (i j : CKSMixedGeometry.I) :
    ContDiffAt ℝ ∞ (polarTensorComponents P A i j) y := by
  have hp := polarParam_contDiffAt P hy
  have hd := hp.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)
  exact ((hA.comp y hp).clm_apply (hd.clm_apply contDiffAt_const)).clm_apply
    (hd.clm_apply contDiffAt_const)
lemma original_source_fields_smooth {A B : SpatialTensor} (P : CollarSourcePatch A B)
    {y : CKSMixedGeometry.Point} (hr : y 0 ≠ 0) (hy : angularProjection y ∈ P.patch.chart.target)
    (hAs : ContDiffAt ℝ ∞ A (polarParam P.patch y))
    (hBs : ContDiffAt ℝ ∞ B (polarParam P.patch y))
    (hmr : ContDiffAt ℝ ∞ P.mr (angularProjection y))
    (hmg : ∀ a b, ContDiffAt ℝ ∞ (P.mg a b) (angularProjection y))
    (hmK : ∀ a b, ContDiffAt ℝ ∞ (P.mK a b) (angularProjection y)) : P.fields.SmoothAt y := by
  have hA := polarTensorComponents_smoothAt P.patch hy hAs
  have hB := polarTensorComponents_smoothAt P.patch hy hBs
  have hl (a : ℕ) (m : Angle → ℝ) (hm : ContDiffAt ℝ ∞ m (angularProjection y)) :
      ContDiffAt ℝ ∞ (ordinaryLeadingComponent a m) y := by
    unfold ordinaryLeadingComponent
    exact (contDiffAt_const.div
      ((ContinuousLinearMap.proj (0:CKSMixedGeometry.I) : CKSMixedGeometry.Point →L[ℝ] ℝ).contDiff.contDiffAt.pow a)
      (pow_ne_zero a hr)).mul (hm.comp y angularProjection.contDiff.contDiffAt)
  refine ⟨⟨?_,?_,?_,hmr,?_,?_,?_,?_⟩,hB 0 0,?_⟩
  · exact P.patch.roundMetric_contDiffAt hy
  · exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => hmg i.succ j.succ
  · exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => hmK i.succ j.succ
  · exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => (hA i.succ j.succ).sub (hl 1 _ (hmg _ _))
  · exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => (hB i.succ j.succ).sub (hl 1 _ (hmK _ _))
  · exact contDiffAt_pi.mpr fun i => hA 0 i.succ
  · exact (hA 0 0).sub (hl 5 _ hmr)
  · exact contDiffAt_pi.mpr fun i => hB 0 i.succ
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
lemma polarTensorComponents_pair (P : SmoothAngularPatch) (A : SpatialTensor)
    (y v w : CKSMixedGeometry.Point) :
    metricPair (fun i j => polarTensorComponents P A i j y) v w =
      A (polarParam P y) (fderiv ℝ (polarParam P) y v) (fderiv ℝ (polarParam P) y w) := by
  conv_rhs => rw [← CKSMixedGeometry.sum_coordinate_basis v,
    ← CKSMixedGeometry.sum_coordinate_basis w]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,
    smul_eq_mul,polarTensorComponents,metricPair]
  simp only [Fin.sum_univ_three]
  ring
lemma polarTensorComponents_posDef (P : SmoothAngularPatch) {A : SpatialTensor}
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (hA : ∀ v w, A (polarParam P y) v w = A (polarParam P y) w v)
    (hp : ∀ v : E, v ≠ 0 → 0 < A (polarParam P y) v v) :
    Matrix.PosDef (fun i j => polarTensorComponents P A i j y) := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (polarTensorComponents_hermitian P A y hA)
  intro v hv
  have hz : fderiv ℝ (polarParam P) y v ≠ 0 := by
    simpa only [map_zero] using (polarParam_fderiv_injective P hr hy).ne hv
  have h := hp _ hz
  rw [← polarTensorComponents_pair P A y v v] at h
  simpa only [metricPair,dotProduct,Matrix.mulVec,Finset.mul_sum,star_trivial,
    mul_assoc,mul_left_comm,mul_comm] using h
lemma physicalDEC_of_spatial {A B : SpatialTensor} (P : SmoothAngularPatch)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (hg : (fun z => fun i j => polarTensorComponents P A i j z) =ᶠ[𝓝 y] G)
    (hk : (fun z => fun i j => polarTensorComponents P B i j z) =ᶠ[𝓝 y] K)
    (hE : ∀ᶠ z in 𝓝 y, SmoothOrthonormalAt G E z)
    (hK : ContDiffAt ℝ ∞ K y) (hs : (K y).IsHermitian)
    (hDEC : spatialDEC A B (polarParam P y)) : physicalDEC G K E y := by
  let e := polarCartesianChart P hr hy
  have hsrc : y ∈ e.source := polarCartesianChart_mem P hr hy
  obtain ⟨he,hi⟩ := polarCartesianChart_smooth P hr hy
  have hEq (F : SpatialTensor) : coordinatePullback e (spatialCoefficients F) =ᶠ[𝓝 y]
      (fun z => fun i j => polarTensorComponents P F i j z) := by
    filter_upwards [angularProjection.continuous.continuousAt.preimage_mem_nhds
      (P.chart.open_target.mem_nhds hy)] with z hz
    exact spatialCoefficients_pullback P F hz
  have hG := (hEq A).trans hg
  have hT := (hEq B).trans hk
  have hframe : ∀ᶠ z in 𝓝 y, SmoothOrthonormalAt (coordinatePullback e (spatialCoefficients A)) E z := by
    filter_upwards [hE,hG.eventually_nhds] with z hz heq
    exact hz.congr_metric heq
  have hTsm := hK.congr_of_eventuallyEq hT
  have hTs : (coordinatePullback e (spatialCoefficients B) y).IsHermitian := by
    rwa [hT.self_of_nhds]
  have ht := local_coordinate_DEC_pushforward e (spatialCoefficients A) (spatialCoefficients B) E
    hsrc he hi hframe hTsm hTs
  have h := ht.mp hDEC
  rw [physicalMetricJet_congr hG,physicalTensorJet_congr hT] at h
  have hf := hE.self_of_nhds
  exact (physical_coordinate_DEC_iff hf.metric_smooth hK hf.frame_smooth hf.positive hf.symmetric hs
    hf.orthonormal).mpr h
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem original_source_patch_properties {A B : SpatialTensor} (P : CollarSourcePatch A B)
    {S : ℝ} (hS : 0 < S)
    (hAs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ A x)
    (hBs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ B x)
    (hA : ∀ x, S < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, S < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, S < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v)
    (hDEC : ∀ x, S < ‖x‖ → spatialDEC (sourceSpatial A) (sourceSpatial B) x)
    (hmr : ∀ θ ∈ P.region, ContDiffAt ℝ ∞ P.mr θ)
    (hmg : ∀ a b θ, θ ∈ P.region → ContDiffAt ℝ ∞ (P.mg a b) θ)
    (hmK : ∀ a b θ, θ ∈ P.region → ContDiffAt ℝ ∞ (P.mK a b) θ)
    {y : CKSMixedGeometry.Point} (hy : y ∈ angularRadialTail S P.region) :
    P.fields.SmoothAt y ∧ (sourceMetric P.fields.base y).PosDef ∧
    (sourceTangentialK P.fields.base y).IsHermitian ∧
    physicalDEC (sourceMetric P.fields.base) (sourceTensor P.fields)
      (sourceFrame P.fields.base) y := by
  have radial {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) :
      S < ‖polarParam P.patch z‖ := by
    rw [polarParam_norm P.patch (hS.trans hz.1).le]; exact hz.1
  have hrec := fun {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) =>
    spatial_source_reconstruction P (hS.trans hz.1) (P.region_target hz.2)
      (hA _ (radial hz)) (hB _ (radial hz))
  have hs {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) : P.fields.SmoothAt z :=
    original_source_fields_smooth P (hS.trans hz.1).ne' (P.region_target hz.2)
      (hAs _ (radial hz)) (hBs _ (radial hz)) (hmr _ hz.2)
      (fun a b => hmg a b _ hz.2) (fun a b => hmK a b _ hz.2)
  have hp {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) :
      (sourceMetric P.fields.base z).PosDef := by
    rw [(hrec hz).1]
    exact polarTensorComponents_posDef P.patch (hS.trans hz.1) (P.region_target hz.2)
      (sourceSpatial_symmetric (hA _ (radial hz))) (hpos _ (radial hz))
  have hks {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) :
      (sourceTensor P.fields z).IsHermitian := by
    rw [(hrec hz).2.1]
    exact polarTensorComponents_hermitian P.patch _ z (sourceSpatial_symmetric (hB _ (radial hz)))
  have hk {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) :
      (sourceTangentialK P.fields.base z).IsHermitian := by
    have h := (hks hz).submatrix (fun i : Fin 2 => i.succ)
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have he {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) :
      SmoothOrthonormalAt (sourceMetric P.fields.base) (sourceFrame P.fields.base) z := by
    have hpe : ∀ᶠ w in 𝓝 z, (sourceMetric P.fields.base w).PosDef :=
      Filter.Eventually.mono ((angularRadialTail_open S P.region_open).mem_nhds hz) (fun _ hw => hp hw)
    have hγ : ∀ᶠ w in 𝓝 z, (sourceGamma P.fields.base w).PosDef :=
      hpe.mono fun _ hw => metricBlock_leaf_posDef hw
    have h := foliation_smoothOrthonormalAt
      (sourceLapse_smoothAt (hs hz).base (hS.trans hz.1).ne' (hp hz))
      (sourceGamma_smoothAt (hs hz).base (hS.trans hz.1).ne')
      (sourceShift_smoothAt (hs hz).base (hS.trans hz.1).ne' (hp hz))
      (sourceLapse_pos (hp hz)).ne' hγ
    exact h.congr_metric (hpe.mono (fun w hw => (source_metric_foliation hw).symm))
  refine ⟨hs hy,hp hy,hk hy,?_⟩
  have hn : ∀ᶠ z in 𝓝 y, z ∈ angularRadialTail S P.region :=
    (angularRadialTail_open S P.region_open).mem_nhds hy
  exact physicalDEC_of_spatial P.patch (hS.trans hy.1) (P.region_target hy.2)
    (sourceMetric P.fields.base) (sourceTensor P.fields) (sourceFrame P.fields.base)
    (hn.mono fun z hz => (hrec hz).1.symm) (hn.mono fun z hz => (hrec hz).2.1.symm)
    (hn.mono fun z hz => he hz) (sourceTensor_smoothAt (hs hy) (hS.trans hy.1).ne')
    (hks hy) (hDEC _ (radial hy))
end
end CKSLorentz

end





















































end OAI
end

theorem solution : type_of% @OAI.CKSLorentz.original_source_patch_properties := @OAI.CKSLorentz.original_source_patch_properties
