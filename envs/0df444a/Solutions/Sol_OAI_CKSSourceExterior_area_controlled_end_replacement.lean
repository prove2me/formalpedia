-- Prove2me | solution 1 for OAI.CKSSourceExterior.area_controlled_end_replacement
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:35:41.626877+00:00
-- url     : https://prove2.me/submissions/105e5dcf-f4fd-48f0-a23e-2e8c51416960

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSLorentz_boosted_cks_patches
import Theorems.Thm_OAI_CKSSpatialManifold_original_CKS_replacement_intrinsic_chart_package

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
namespace CKSSphericalHarmonics
noncomputable section
open MvPolynomial

open MeasureTheory

open scoped Pointwise
def sphereHome (u : Ambient ≃ₗᵢ[ℝ] Ambient) : Sphere ≃ₜ Sphere :=
  u.toHomeomorph.subtype (fun x => by
    simp only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.coe_toHomeomorph,
      u.norm_map])

lemma sphereHome_val (u : Ambient ≃ₗᵢ[ℝ] Ambient) (x : Sphere) :
    (sphereHome u x).1 = u x.1 := rfl

lemma volume_preimage_isometry (u : Ambient ≃ₗᵢ[ℝ] Ambient) (s : Set Ambient) :
    (volume : Measure Ambient) (u ⁻¹' s) = volume s := by
  have hm := u.toHomeomorph.toMeasurableEquiv.map_apply (μ := volume) s
  change (Measure.map u volume) s = volume (u ⁻¹' s) at hm
  rw [u.measurePreserving.map_eq] at hm
  exact hm.symm

lemma sphereCone_preimage (u : Ambient ≃ₗᵢ[ℝ] Ambient) (s : Set Sphere) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereHome u ⁻¹' s)) =
      u ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨r, hr, u v.1, ⟨sphereHome u v, hv, rfl⟩, (u.map_smul r v.1).symm⟩
  · rintro ⟨r, hr, _, ⟨v, hv, rfl⟩, hx⟩
    refine ⟨r, hr, u.symm v.1, ⟨sphereHome u.symm v, ?_, rfl⟩, ?_⟩
    · change sphereHome u (sphereHome u.symm v) ∈ s
      have h : sphereHome u (sphereHome u.symm v) = v := by
        apply Subtype.ext
        exact u.apply_symm_apply v.1
      simpa [h] using hv
    · apply u.injective
      simpa using hx

theorem sphereHome_measurePreserving (u : Ambient ≃ₗᵢ[ℝ] Ambient) :
    MeasurePreserving (sphereHome u) surfaceMeasure surfaceMeasure := by
  refine ⟨(sphereHome u).continuous.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereHome u).continuous.measurable hs,
    Measure.toSphere_apply' _ (hs.preimage (sphereHome u).continuous.measurable),
    Measure.toSphere_apply' _ hs, sphereCone_preimage, volume_preimage_isometry]

lemma sphereIntegral_apply (f : C(Sphere, ℝ)) :
    sphereIntegral f = ∫ x, f x ∂surfaceMeasure := by
  change inner ℝ (toL2 1) (toL2 f) = _
  rw [toL2, MeasureTheory.ContinuousMap.inner_toLp]
  simp

open scoped Manifold ContDiff Topology
open Set

lemma rotationGenerator_apply (i j k : Fin 3) (x : Ambient) :
    rotationGenerator i j x k = (if k = j then x i else 0) - (if k = i then x j else 0) := rfl

attribute [local instance] cksLocalInst_1853

lemma rotationGenerator_smooth (i j : Fin 3) : ContDiff ℝ ∞ (rotationGenerator i j) :=
  (rotationGenerator i j).toContinuousLinearMap.contDiff

lemma smoothRotation_smooth {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (i j : Fin 3) : ContDiffOn ℝ ∞ (smoothRotation i j F) puncturedSpace := by
  exact (hF.fderiv_of_isOpen puncturedSpace.isOpen (by simp)).clm_apply
    (rotationGenerator_smooth i j).contDiffOn

lemma planeRotation_hasDerivAt (i j : Fin 3) (hij : i ≠ j) (x : Ambient) (t : ℝ) :
    HasDerivAt (fun s => planeRotation i j hij s x)
      (rotationGenerator i j (planeRotation i j hij t x)) t := by
  have h : HasDerivAt (fun s => fun k : Fin 3 =>
      if k = i then Real.cos s * x i - Real.sin s * x j
      else if k = j then Real.sin s * x i + Real.cos s * x j else x k)
      (fun k => (rotationGenerator i j (planeRotation i j hij t x)) k) t := by
    apply hasDerivAt_pi.mpr
    intro k
    by_cases hi : k = i
    · subst k
      convert! ((Real.hasDerivAt_cos t).mul_const (x i)).sub
        ((Real.hasDerivAt_sin t).mul_const (x j)) using 1
      · funext s; simp
      · simp [rotationGenerator_apply, planeRotation_apply, planeRotationMap_apply, hij, hij.symm]
        ring
    · by_cases hj : k = j
      · subst k
        convert! ((Real.hasDerivAt_sin t).mul_const (x i)).add
          ((Real.hasDerivAt_cos t).mul_const (x j)) using 1
        · funext s; simp [hij.symm]
        · simp [rotationGenerator_apply, planeRotation_apply, planeRotationMap_apply, hij.symm]
          ring
      · simpa [rotationGenerator_apply, hi, hj] using hasDerivAt_const t (x k)
  convert! (PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt t h using 1

lemma smoothRotation_orbit_derivative {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (i j : Fin 3) (hij : i ≠ j) (x : Sphere) (t : ℝ) :
    HasDerivAt (fun s => F (planeRotation i j hij s (x : Ambient)))
      (smoothRotation i j F (planeRotation i j hij t (x : Ambient))) t := by
  have hn : (planeRotation i j hij t (x : Ambient)) ≠ 0 := by
    simpa using (planeRotation i j hij t).injective.ne (sphere_ne_zero x)
  have hd := (hF.contDiffAt (puncturedSpace.isOpen.mem_nhds hn)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt t (planeRotation_hasDerivAt i j hij x t)

theorem sphereIntegral_smoothRotation {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (i j : Fin 3) (hij : i ≠ j) :
    sphereIntegral (smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j)) = 0 := by
  let f := smoothRestriction F hF
  let g := smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j)
  let orb (t : ℝ) (x : Sphere) := sphereHome (planeRotation i j hij t) x
  have hcF (t : ℝ) : Continuous (fun x : Sphere => f (orb t x)) :=
    f.continuous.comp (sphereHome (planeRotation i j hij t)).continuous
  have hcG (t : ℝ) : Continuous (fun x : Sphere => g (orb t x)) :=
    g.continuous.comp (sphereHome (planeRotation i j hij t)).continuous
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := surfaceMeasure) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t x => f (orb t x)) (F' := fun t x => g (orb t x))
    (bound := fun _ => ‖g‖)
    (by simp) (Filter.Eventually.of_forall (fun t => (hcF t).aestronglyMeasurable))
    ((hcF 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hcG 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x t _ => g.norm_coe_le_norm (orb t x)))
    (integrable_const ‖g‖)
    (Filter.Eventually.of_forall (fun x t _ => smoothRotation_orbit_derivative hF i j hij x t))
  have he : (fun t : ℝ => ∫ x, f (orb t x) ∂surfaceMeasure) =
      fun _ => sphereIntegral f := by
    funext t
    rw [sphereIntegral_apply]
    exact (sphereHome_measurePreserving (planeRotation i j hij t)).integral_comp
      (sphereHome (planeRotation i j hij t)).measurableEmbedding f
  have hz := hd.2
  rw [he] at hz
  have he' := hz.unique (hasDerivAt_const 0 (sphereIntegral f))
  simpa [sphereIntegral_apply, orb, sphereHome_val, g, smoothRestriction] using he'

lemma smoothRotation_mul {F G : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (hG : ContDiffOn ℝ ∞ G puncturedSpace)
    (i j : Fin 3) {x : Ambient} (hx : x ≠ 0) :
    smoothRotation i j (F * G) x = F x * smoothRotation i j G x + G x * smoothRotation i j F x := by
  have hf := (hF.contDiffAt (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hg := (hG.contDiffAt (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  simp [smoothRotation, fderiv_mul hf hg]

lemma inner_toL2 (f g : C(Sphere, ℝ)) :
    inner ℝ (toL2 f) (toL2 g) = sphereIntegral (f * g) := by
  rw [sphereIntegral_apply]
  change inner ℝ (ContinuousMap.toLp 2 surfaceMeasure ℝ f)
    (ContinuousMap.toLp 2 surfaceMeasure ℝ g) = _
  rw [MeasureTheory.ContinuousMap.inner_toLp]
  simp [mul_comm]

theorem smoothRotation_skew_adjoint {F G : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (hG : ContDiffOn ℝ ∞ G puncturedSpace)
    (i j : Fin 3) (hij : i ≠ j) :
    inner ℝ (toL2 (smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j)))
      (toL2 (smoothRestriction G hG)) =
    -inner ℝ (toL2 (smoothRestriction F hF))
      (toL2 (smoothRestriction (smoothRotation i j G) (smoothRotation_smooth hG i j))) := by
  have he : smoothRestriction (smoothRotation i j (F * G)) (smoothRotation_smooth (hF.mul hG) i j) =
      smoothRestriction F hF * smoothRestriction (smoothRotation i j G) (smoothRotation_smooth hG i j) +
      smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j) * smoothRestriction G hG := by
    ext x
    change smoothRotation i j (F * G) x = _
    rw [smoothRotation_mul hF hG i j (sphere_ne_zero x)]
    change _ = F x * smoothRotation i j G x + smoothRotation i j F x * G x
    ring
  have h := sphereIntegral_smoothRotation (F := F * G) (hF.mul hG) i j hij
  rw [he, map_add] at h
  rw [inner_toL2, inner_toL2]
  linarith

lemma rotationGenerator_decomposition (x v : Ambient) :
    ‖x‖ ^ 2 • v = (∑ i : Fin 3, ∑ j : Fin 3, (x i * v j) • rotationGenerator i j x) +
      (∑ i : Fin 3, x i * v i) • x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [Fin.sum_univ_three, rotationGenerator_apply] <;> ring

end
end CKSSphericalHarmonics

end


end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MeasureTheory Set

theorem sphereArea_eq_four_pi : sphereArea = 4 * Real.pi := by
  rw [sphereArea, sphereIntegral_apply]
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one]
  rw [Measure.toSphere_real_apply_univ]
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
    measureReal_def, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI


noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff Manifold Topology
open Set

lemma boost_mass {e m : ℝ} {p : E} (hm0 : m ≠ 0) : boost e m p (m,0) = (e,p) := by
  simp [boost, hm0]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff Manifold Topology
open Set

def boundaryAmbient (e m : ℝ) (p : E) (n : E) : E :=
  (denominator e m p n)⁻¹ • boundarySpatial e m p n

lemma boundary_null (e : ℝ) (p : E) (he : ‖p‖ < e) (n : Sphere) :
    boost e (mass e p) p (1,(n:E)) =
      denominator e (mass e p) p n • ((1:ℝ), (boundary e p he n : E)) := by
  have hd := (denominator_pos he (mass_pos he) n).ne'
  apply Prod.ext
  · simp [boost, denominator]
  · change boundarySpatial e (mass e p) p n =
      denominator e (mass e p) p n • ((denominator e (mass e p) p n)⁻¹ • _)
    simp [smul_smul, hd]

lemma boundaryAmbient_smooth {e m : ℝ} {p : E} {n : E}
    (hd : denominator e m p n ≠ 0) : ContDiffAt ℝ ∞ (boundaryAmbient e m p) n := by
  have hi : ContDiff ℝ ∞ (fun n : E => inner ℝ p n) :=
    ContDiff.inner ℝ contDiff_const contDiff_id
  have hD : ContDiff ℝ ∞ (denominator e m p) :=
    (contDiff_const.add hi).div_const m
  have hS : ContDiff ℝ ∞ (boundarySpatial e m p) :=
    contDiff_id.add ((contDiff_const.add (hi.div_const (m*(e+m)))).smul contDiff_const)
  exact (hD.contDiffAt.inv hd).smul hS.contDiffAt

lemma boundary_smooth (e : ℝ) (p : E) (he : ‖p‖ < e) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (boundary e p he) := by
  have h : ContMDiff (𝓡 2) 𝓘(ℝ,E) ∞
      (fun n : Sphere => boundaryAmbient e (mass e p) p n) := by
    intro n
    exact (boundaryAmbient_smooth (denominator_pos he (mass_pos he) n).ne').comp_contMDiffAt
      (contMDiff_coe_sphere (E := E) (n := 2)).contMDiffAt
  exact h.codRestrict_sphere fun n => (boundary e p he n).property

end
end CKSLorentz

end

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
open scoped RealInnerProductSpace ContDiff

def boostField (p n : E) : E := p-inner ℝ p n • n

def flowDLinear (p : E) (t : ℝ) : E →L[ℝ] ℝ := t • innerSL ℝ p
def flowSLinear (p : E) (t : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + (flowCoeff p t • innerSL ℝ p).smulRight p

lemma flowEnergy_pos (p : E) (t : ℝ) : 0 < flowEnergy p t := Real.sqrt_pos.2 (by positivity)
lemma flowEnergy_sq (p : E) (t : ℝ) : flowEnergy p t ^2 = 1+t^2*‖p‖^2 := Real.sq_sqrt (by positivity)
lemma flowEnergy_add_pos (p : E) (t : ℝ) : 0 < flowEnergy p t+1 := by linarith [flowEnergy_pos p t]
lemma flowEnergy_gt (p : E) (t : ℝ) : ‖t • p‖ < flowEnergy p t := by
  rw [norm_smul, Real.norm_eq_abs]
  have hs : (|t| * ‖p‖)^2 = t^2*‖p‖^2 := by rw [mul_pow, sq_abs]
  nlinarith [flowEnergy_sq p t, flowEnergy_pos p t, norm_nonneg p, abs_nonneg t]

lemma flowEnergy_smooth (p : E) : ContDiff ℝ ∞ (flowEnergy p) :=
  (contDiff_const.add ((contDiff_id.pow 2).mul contDiff_const)).sqrt (fun t => by positivity)
lemma flowCoeff_smooth (p : E) : ContDiff ℝ ∞ (flowCoeff p) :=
  (contDiff_id.pow 2).div ((flowEnergy_smooth p).add contDiff_const)
    (fun t => (flowEnergy_add_pos p t).ne')
lemma flowD_smooth (p : E) : ContDiff ℝ ∞ (fun z : ℝ × E => flowD p z.1 z.2) :=
  ((flowEnergy_smooth p).comp contDiff_fst).add
    (contDiff_fst.mul (ContDiff.inner ℝ contDiff_const contDiff_snd))
lemma flowS_smooth (p : E) : ContDiff ℝ ∞ (fun z : ℝ × E => flowS p z.1 z.2) :=
  contDiff_snd.add ((contDiff_fst.add (((flowCoeff_smooth p).comp contDiff_fst).mul
    (ContDiff.inner ℝ contDiff_const contDiff_snd))).smul contDiff_const)

lemma flowD_eq (p : E) (t : ℝ) (n : E) :
    flowD p t n = denominator (flowEnergy p t) 1 (t • p) n := by simp [flowD, denominator, inner_smul_left]
lemma flowS_eq (p : E) (t : ℝ) (n : E) :
    flowS p t n = boundarySpatial (flowEnergy p t) 1 (t • p) n := by
  simp only [flowS, flowCoeff, boundarySpatial, inner_smul_left, conj_trivial, one_div,
    inv_one, one_mul, smul_smul]
  congr 1
  ring_nf
lemma flowD_pos (p : E) (t : ℝ) (n : Sphere) : 0 < flowD p t n := by
  rw [flowD_eq]
  exact denominator_pos (flowEnergy_gt p t) zero_lt_one n
lemma flowS_norm (p : E) (t : ℝ) (n : Sphere) : ‖flowS p t n‖ = flowD p t n := by
  rw [flowS_eq, flowD_eq]
  apply boundarySpatial_norm (flowEnergy_gt p t) zero_lt_one
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith [flowEnergy_sq p t]
lemma flowPhi_norm (p : E) (t : ℝ) (n : Sphere) : ‖flowPhi p t n‖ = 1 := by
  rw [flowPhi, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (flowD_pos p t n)), flowS_norm]
  exact inv_mul_cancel₀ (flowD_pos p t n).ne'

lemma flowEnergy_derivative (p : E) (t : ℝ) :
    HasDerivAt (flowEnergy p) (t*‖p‖^2/flowEnergy p t) t := by
  have h := (Real.hasDerivAt_sqrt (show 1+t^2*‖p‖^2 ≠ 0 by positivity)).comp t
    ((((hasDerivAt_id t).pow 2).mul_const (‖p‖^2)).const_add 1)
  convert! h using 1
  simp [flowEnergy]
  ring

lemma flowCoeff_derivative (p : E) (t : ℝ) :
    HasDerivAt (flowCoeff p) (t/flowEnergy p t) t := by
  have h := ((hasDerivAt_id t).pow 2).div
    ((flowEnergy_derivative p t).add_const 1) (flowEnergy_add_pos p t).ne'
  convert! h using 1
  have hq := flowEnergy_sq p t
  have hpos := (flowEnergy_pos p t).ne'
  have hadd := (flowEnergy_add_pos p t).ne'
  simp only [id_eq, Pi.pow_apply, pow_one, mul_one, Nat.cast_ofNat, Nat.reduceSub]
  field_simp
  nlinarith [congrArg (fun x : ℝ => t*x) hq]

lemma flowD_derivative (p : E) (t : ℝ) (n : E) :
    HasDerivAt (fun t => flowD p t n) (t*‖p‖^2/flowEnergy p t+inner ℝ p n) t := by
  convert! (flowEnergy_derivative p t).add ((hasDerivAt_id t).mul_const (inner ℝ p n)) using 1
  simp
lemma flowS_derivative (p : E) (t : ℝ) (n : E) :
    HasDerivAt (fun t => flowS p t n) ((1+t/flowEnergy p t*inner ℝ p n) • p) t := by
  convert! (((hasDerivAt_id t).add ((flowCoeff_derivative p t).mul_const (inner ℝ p n))).smul_const p).const_add n using 1

lemma flowD_fderivative (p : E) (t : ℝ) (n : E) :
    HasFDerivAt (flowD p t) (flowDLinear p t) n := by
  convert! (((innerSL ℝ p).hasFDerivAt.const_mul t).const_add (flowEnergy p t)) using 1
lemma flowS_fderivative (p : E) (t : ℝ) (n : E) :
    HasFDerivAt (flowS p t) (flowSLinear p t) n := by
  convert! (hasFDerivAt_id n).add
    ((((innerSL ℝ p).hasFDerivAt.const_mul (flowCoeff p t)).const_add t).smul_const p) using 1

lemma flowD_transport (p : E) (t : ℝ) (n : E) :
    flowEnergy p t * (t*‖p‖^2/flowEnergy p t + inner ℝ p n) =
      flowDLinear p t (boostField p n)+inner ℝ p n*flowD p t n := by
  simp only [flowDLinear, smul_apply, innerSL_apply_apply, smul_eq_mul,
    boostField, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, flowD]
  field_simp [(flowEnergy_pos p t).ne']
  ring

lemma flowS_transport (p : E) (t : ℝ) (n : E) :
    flowEnergy p t • ((1+t/flowEnergy p t*inner ℝ p n) • p) =
      flowSLinear p t (boostField p n)+inner ℝ p n • flowS p t n := by
  simp only [flowSLinear, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul,
    boostField, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, flowS, flowCoeff]
  have hq : t^2*‖p‖^2/(flowEnergy p t+1) = flowEnergy p t-1 := by
    apply (div_eq_iff (flowEnergy_add_pos p t).ne').2
    nlinarith [flowEnergy_sq p t]
  have hc : flowEnergy p t * (1+t/flowEnergy p t*inner ℝ p n) =
      1+t*inner ℝ p n+t^2/(flowEnergy p t+1)*‖p‖^2 := by
    rw [show t^2/(flowEnergy p t+1)*‖p‖^2 = t^2*‖p‖^2/(flowEnergy p t+1) by ring, hq]
    field_simp [(flowEnergy_pos p t).ne']
    ring
  rw [smul_smul, hc]
  module

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open scoped RealInnerProductSpace ContDiff
open Finset

def boostField (p x : Ambient) : Ambient := p - inner ℝ p x • x

def coordinateCM (i : Fin 3) : C(Sphere,ℝ) :=
  smoothRestriction (fun x : Ambient => x i) (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn

lemma smoothRotation_coordinate (i j k : Fin 3) (x : Ambient) :
    smoothRotation i j (fun x : Ambient => x k) x =
      (if k=j then x i else 0) - (if k=i then x j else 0) := by
  change fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) k) x _ = _
  rw [(EuclideanSpace.proj (𝕜 := ℝ) k).fderiv]
  exact rotationGenerator_apply i j k x

lemma sphereIntegral_coordinate_rotation {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (i j : Fin 3) :
    sphereIntegral (coordinateCM i *
      smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j)) =
      if i=j then 0 else sphereIntegral (coordinateCM j * smoothRestriction F hF) := by
  by_cases hij : i=j
  · subst j
    have hzero : smoothRestriction (smoothRotation i i F) (smoothRotation_smooth hF i i) = 0 := by
      ext n
      change fderiv ℝ F n (rotationGenerator i i n) = 0
      have hgen : rotationGenerator i i (n:Ambient) = 0 := by ext k; simp [rotationGenerator_apply]
      rw [hgen, map_zero]
    simp [hzero]
  have h := smoothRotation_skew_adjoint (F := fun x : Ambient => x i) (G := F)
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn hF i j hij
  rw [inner_toL2, inner_toL2] at h
  have he : smoothRestriction (smoothRotation i j (fun x : Ambient => x i))
      (smoothRotation_smooth (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn i j) = -coordinateCM j := by
    ext n
    change smoothRotation i j (fun x : Ambient => x i) n = -(n:Ambient) j
    simp [smoothRotation_coordinate, hij]
  rw [he] at h
  simp only [neg_mul, map_neg] at h
  simpa [hij, coordinateCM] using neg_injective h.symm

lemma boostField_decomposition (p : Ambient) (n : Sphere) :
    boostField p n = ∑ i : Fin 3, ∑ j : Fin 3,
      ((n:Ambient) i * p j) • rotationGenerator i j n := by
  have h := rotationGenerator_decomposition (n:Ambient) p
  have hn : ‖(n:Ambient)‖ = 1 := by simp
  rw [hn, one_pow, one_smul] at h
  have hi : inner ℝ p (n:Ambient) = ∑ i : Fin 3, (n:Ambient) i * p i := by
    rw [PiLp.inner_apply]
    simp [mul_comm]
  unfold boostField
  rw [hi]
  exact sub_eq_iff_eq_add.mpr h

theorem sphereIntegral_boostField {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (p : Ambient) :
    ∫ n : Sphere, fderiv ℝ F n (boostField p n) ∂surfaceMeasure =
      2 * ∫ n : Sphere, inner ℝ p (n:Ambient) * F n ∂surfaceMeasure := by
  let L : C(Sphere,ℝ) := ∑ i : Fin 3, ∑ j : Fin 3,
    p j • (coordinateCM i * smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j))
  have hL : ∀ n : Sphere, L n = fderiv ℝ F n (boostField p n) := by
    intro n
    rw [boostField_decomposition]
    simp only [map_sum, map_smul, L, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      ContinuousMap.mul_apply, smul_eq_mul, coordinateCM, smoothRestriction, smoothRotation, ContinuousMap.coe_mk]
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj
    ring
  have hi : ∫ n : Sphere, fderiv ℝ F n (boostField p n) ∂surfaceMeasure = sphereIntegral L := by
    rw [sphereIntegral_apply]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun n => (hL n).symm
  rw [hi]
  have hsig : sphereIntegral L =
      2 * sphereIntegral ((∑ j : Fin 3, p j • coordinateCM j) * smoothRestriction F hF) := by
    simp only [L, map_sum, map_smul, smul_eq_mul, sphereIntegral_coordinate_rotation hF]
    simp only [Fin.sum_univ_three]
    simp only [Fin.reduceEq, ite_true, ite_false, mul_zero, zero_add, add_zero]
    rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  rw [hsig, sphereIntegral_apply]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with n
  simp only [ContinuousMap.mul_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, coordinateCM, smoothRestriction, ContinuousMap.coe_mk]
  congr 1
  rw [PiLp.inner_apply]
  simp [mul_comm]

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Topology
open Set

lemma boostField_tangent (p : E) (n : Sphere) : inner ℝ (n:E) (boostField p n) = 0 := by
  simp [boostField, inner_sub_right, inner_smul_right, real_inner_comm]

lemma norm_derivative_sphere (n : Sphere) : HasFDerivAt (norm : E → ℝ) (innerSL ℝ (n:E)) n := by
  have h := (Real.hasDerivAt_sqrt (show ‖(n:E)‖^2 ≠ 0 by rw [sphere_norm]; norm_num)).comp_hasFDerivAt (n:E)
    (hasStrictFDerivAt_norm_sq (n:E)).hasFDerivAt
  convert! h using 1
  · funext x
    exact (Real.sqrt_sq (norm_nonneg x)).symm
  · ext x
    simp

lemma normalizeAmbient_fderiv_tangent (n : Sphere) (Y : E) (hY : inner ℝ (n:E) Y = 0) :
    fderiv ℝ normalizeAmbient n Y = Y := by
  have hi := (hasDerivAt_inv (show ‖(n:E)‖ ≠ 0 by rw [sphere_norm]; norm_num)).comp_hasFDerivAt (n:E)
    (norm_derivative_sphere n)
  have h := hi.smul (hasFDerivAt_id (n:E))
  change HasFDerivAt normalizeAmbient _ n at h
  rw [h.fderiv]
  simp [ContinuousLinearMap.smulRight_apply, hY]

lemma flowPhi_smooth_at (p : E) (t : ℝ) (n : Sphere) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => flowPhi p z.1 z.2) (t,(n:E)) :=
  (((flowD_smooth p).contDiffAt).inv (flowD_pos p t n).ne').smul (flowS_smooth p).contDiffAt

lemma flowPhi_nonzero (p : E) (t : ℝ) (n : Sphere) : flowPhi p t n ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [flowPhi_norm]; norm_num

lemma flowPhi_fderiv (p : E) (t : ℝ) (n : Sphere) (Y : E) :
    fderiv ℝ (flowPhi p t) n Y =
      (flowD p t n)⁻¹ • flowSLinear p t Y -
        (flowDLinear p t Y/(flowD p t n)^2) • flowS p t n := by
  have hi := (hasDerivAt_inv (flowD_pos p t n).ne').comp_hasFDerivAt (n:E) (flowD_fderivative p t n)
  have h := hi.smul (flowS_fderivative p t n)
  change HasFDerivAt (flowPhi p t) _ n at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, Function.comp_apply]
  module

lemma flowPhi_derivative (p : E) (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => flowPhi p t n)
      ((flowD p t n)⁻¹ • ((1+t/flowEnergy p t*inner ℝ p (n:E)) • p) -
        ((t*‖p‖^2/flowEnergy p t+inner ℝ p (n:E))/(flowD p t n)^2) • flowS p t n) t := by
  convert! ((flowD_derivative p t n).inv (flowD_pos p t n).ne').smul (flowS_derivative p t n) using 1
  module

lemma flowPhi_transport (p : E) (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => flowPhi p t n)
      ((flowEnergy p t)⁻¹ • fderiv ℝ (flowPhi p t) n (boostField p n)) t := by
  convert! flowPhi_derivative p t n using 1
  rw [flowPhi_fderiv]
  have hS := flowS_transport p t (n:E)
  have hD := flowD_transport p t (n:E)
  have hS' : flowSLinear p t (boostField p n) =
      flowEnergy p t • ((1+t/flowEnergy p t*inner ℝ p (n:E)) • p) - inner ℝ p (n:E) • flowS p t n :=
    eq_sub_of_add_eq hS.symm
  have hD' : flowDLinear p t (boostField p n) =
      flowEnergy p t * (t*‖p‖^2/flowEnergy p t+inner ℝ p (n:E)) - inner ℝ p (n:E)*flowD p t n :=
    eq_sub_of_add_eq hD.symm
  rw [hS', hD']
  have hE := (flowEnergy_pos p t).ne'
  have hden := (flowD_pos p t n).ne'
  ext i
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hE, hden]
  ring

lemma weightedPullback_smooth_at (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => weightedPullback p z.1 F z.2) (t,(n:E)) := by
  have hc := hF.contDiffAt (CKSSphericalHarmonics.puncturedSpace.isOpen.mem_nhds (flowPhi_nonzero p t n))
  have hd : ContDiffAt ℝ ∞ (fun z : ℝ × E => (flowD p z.1 z.2)⁻¹ ^2) (t,(n:E)) :=
    ((flowD_smooth p).contDiffAt.inv (flowD_pos p t n).ne').pow 2
  exact hd.mul (hc.comp (t,(n:E)) (flowPhi_smooth_at p t n))

lemma weightedPullback_spatial_derivative (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) (Y : E) :
    fderiv ℝ (weightedPullback p t F) n Y =
      (2*(flowD p t n)⁻¹*(-flowDLinear p t Y/(flowD p t n)^2))*F (flowPhi p t n) +
        (flowD p t n)⁻¹ ^2 * fderiv ℝ F (flowPhi p t n) (fderiv ℝ (flowPhi p t) n Y) := by
  have hphi : DifferentiableAt ℝ (flowPhi p t) (n:E) := by
    convert! ((flowPhi_smooth_at p t n).comp (n:E) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hf := (hF.contDiffAt (CKSSphericalHarmonics.puncturedSpace.isOpen.mem_nhds (flowPhi_nonzero p t n))).differentiableAt (by simp)
  have ha := ((hasDerivAt_inv (flowD_pos p t n).ne').pow 2).comp_hasFDerivAt (n:E) (flowD_fderivative p t n)
  have h := ha.mul (hf.hasFDerivAt.comp (n:E) hphi.hasFDerivAt)
  change HasFDerivAt (weightedPullback p t F) _ n at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    Function.comp_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
  ring

lemma weightedPullback_transport (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => weightedPullback p t F n)
      ((flowEnergy p t)⁻¹ * (fderiv ℝ (weightedPullback p t F) n (boostField p n) -
        2*inner ℝ p (n:E)*weightedPullback p t F n)) t := by
  have hf := (hF.contDiffAt (CKSSphericalHarmonics.puncturedSpace.isOpen.mem_nhds (flowPhi_nonzero p t n))).differentiableAt (by simp)
  have h := (((flowD_derivative p t n).inv (flowD_pos p t n).ne').pow 2).mul
    (hf.hasFDerivAt.comp_hasDerivAt t (flowPhi_transport p t n))
  convert! h using 1
  rw [weightedPullback_spatial_derivative p hF]
  simp only [map_smul, smul_eq_mul, weightedPullback, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply, Pi.inv_apply, Function.comp_apply]
  have hD := flowD_transport p t (n:E)
  have hD' : flowDLinear p t (boostField p n) =
      flowEnergy p t * (t*‖p‖^2/flowEnergy p t+inner ℝ p (n:E)) - inner ℝ p (n:E)*flowD p t n :=
    eq_sub_of_add_eq hD.symm
  rw [hD']
  field_simp [(flowEnergy_pos p t).ne', (flowD_pos p t n).ne']
  ring

lemma normalizedPullback_smooth (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) :
    ContDiffOn ℝ ∞ (normalizedPullback p F) (Set.univ ×ˢ (CKSSphericalHarmonics.puncturedSpace : Set E)) := by
  intro z hz
  let n : Sphere := CKSSphericalHarmonics.normalizeSphere ⟨z.2,hz.2⟩
  have h := weightedPullback_smooth_at p hF z.1 n
  exact (h.comp z (contDiffAt_fst.prodMk ((normalizeAmbient_smooth hz.2).comp z contDiffAt_snd))).contDiffWithinAt

lemma normalizedPullback_spatial (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun x => normalizedPullback p F (t,x)) CKSSphericalHarmonics.puncturedSpace :=
  (normalizedPullback_smooth p hF).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨Set.mem_univ _,hx⟩)

lemma normalizedPullback_fderiv_tangent (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) :
    fderiv ℝ (fun x => normalizedPullback p F (t,x)) n (boostField p n) =
      fderiv ℝ (weightedPullback p t F) n (boostField p n) := by
  have hf := ((weightedPullback_smooth_at p hF t n).comp (n:E) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hn := (normalizeAmbient_smooth (CKSSphericalHarmonics.sphere_ne_zero n)).differentiableAt (by simp)
  change fderiv ℝ ((weightedPullback p t F) ∘ normalizeAmbient) n _ = _
  have hf' : DifferentiableAt ℝ (weightedPullback p t F) (normalizeAmbient n) := by
    rw [normalizeAmbient_sphere]
    convert! hf
  rw [fderiv_comp (n:E) hf' hn, ContinuousLinearMap.comp_apply, normalizeAmbient_sphere,
    normalizeAmbient_fderiv_tangent n _ (boostField_tangent p n)]

lemma normalizedPullback_transport (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => normalizedPullback p F (t,(n:E)))
      ((flowEnergy p t)⁻¹ * (fderiv ℝ (fun x => normalizedPullback p F (t,x)) n (boostField p n) -
        2*inner ℝ p (n:E)*normalizedPullback p F (t,(n:E)))) t := by
  simp only [normalizedPullback_sphere, normalizedPullback_fderiv_tangent p hF]
  exact weightedPullback_transport p hF t n

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Topology
open Set MeasureTheory
open CKSSphericalHarmonics (puncturedSpace surfaceMeasure smoothRestriction)

def pullbackRate (p : E) (F : E → ℝ) (z : ℝ × E) : ℝ :=
  fderiv ℝ (normalizedPullback p F) z (1,0)

lemma normalizedDomain_open : IsOpen (Set.univ ×ˢ (puncturedSpace : Set E) : Set (ℝ × E)) :=
  isOpen_univ.prod puncturedSpace.isOpen

lemma pullbackRate_smooth (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    ContDiffOn ℝ ∞ (pullbackRate p F) (Set.univ ×ˢ (puncturedSpace : Set E)) :=
  ((normalizedPullback_smooth p hF).fderiv_of_isOpen normalizedDomain_open (by simp)).clm_apply contDiffOn_const

lemma pullback_time_derivative (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => normalizedPullback p F (t,(n:E))) (pullbackRate p F (t,(n:E))) t := by
  have hg := ((normalizedPullback_smooth p hF).contDiffAt (x := (t,(n:E)))
    (normalizedDomain_open.mem_nhds ⟨mem_univ t,CKSSphericalHarmonics.sphere_ne_zero n⟩)).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => (t,(n:E))) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t (n:E))
  convert! hg.hasFDerivAt.comp_hasDerivAt t hline using 1

lemma pullbackRate_transport (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (t : ℝ) (n : Sphere) :
    pullbackRate p F (t,(n:E)) =
      (flowEnergy p t)⁻¹ * (fderiv ℝ (fun x => normalizedPullback p F (t,x)) n (boostField p n) -
        2*inner ℝ p (n:E)*normalizedPullback p F (t,(n:E))) :=
  (pullback_time_derivative p hF t n).unique (normalizedPullback_transport p hF t n)

lemma continuous_restrict_sphere {G : ℝ × E → ℝ}
    (hG : ContDiffOn ℝ ∞ G (Set.univ ×ˢ (puncturedSpace : Set E))) :
    Continuous (fun z : ℝ × Sphere => G (z.1,(z.2:E))) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hi : Continuous (fun z : ℝ × Sphere => (z.1,(z.2:E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have ho : ContinuousAt G (z.1,(z.2:E)) :=
    (hG.contDiffAt (x := (z.1,(z.2:E))) (normalizedDomain_open.mem_nhds
      ⟨mem_univ _, CKSSphericalHarmonics.sphere_ne_zero z.2⟩)).continuousAt
  exact ho.comp (f := fun z : ℝ × Sphere => (z.1,(z.2:E))) hi.continuousAt

lemma sphere_integrable_smooth {H : E → ℝ} (hH : ContDiffOn ℝ ∞ H puncturedSpace) :
    Integrable (fun n : Sphere => H n) surfaceMeasure :=
  (smoothRestriction H hH).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma boostField_smooth (p : E) : ContDiff ℝ ∞ (boostField p) :=
  contDiff_const.sub ((ContDiff.inner ℝ contDiff_const contDiff_id).smul contDiff_id)

lemma pullbackRate_integral_zero (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) (t : ℝ) :
    ∫ n : Sphere, pullbackRate p F (t,(n:E)) ∂surfaceMeasure = 0 := by
  let G : E → ℝ := fun x => normalizedPullback p F (t,x)
  have hG : ContDiffOn ℝ ∞ G puncturedSpace := normalizedPullback_spatial p hF t
  have hDG : ContDiffOn ℝ ∞ (fun x => fderiv ℝ G x (boostField p x)) puncturedSpace :=
    (hG.fderiv_of_isOpen puncturedSpace.isOpen (by simp)).clm_apply (boostField_smooth p).contDiffOn
  have hqG : ContDiffOn ℝ ∞ (fun x => inner ℝ p x * G x) puncturedSpace :=
    (ContDiff.inner ℝ contDiff_const contDiff_id).contDiffOn.mul hG
  have he : (fun n : Sphere => pullbackRate p F (t,(n:E))) =
      fun n : Sphere => (flowEnergy p t)⁻¹ * (fderiv ℝ G n (boostField p n) - 2*(inner ℝ p (n:E)*G n)) := by
    funext n
    rw [pullbackRate_transport p hF]
    dsimp only [G]; ring
  rw [he, integral_const_mul, integral_sub (sphere_integrable_smooth hDG) ((sphere_integrable_smooth hqG).const_mul 2), integral_const_mul]
  have hi := CKSSphericalHarmonics.sphereIntegral_boostField hG p
  change (∫ n : Sphere, fderiv ℝ G n (boostField p n) ∂surfaceMeasure) = _ at hi
  rw [hi]; ring

lemma normalizedIntegral_derivative_zero (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ n : Sphere, normalizedPullback p F (t,(n:E)) ∂surfaceMeasure) 0 t₀ := by
  let H (t : ℝ) (n : Sphere) := normalizedPullback p F (t,(n:E))
  let R (t : ℝ) (n : Sphere) := pullbackRate p F (t,(n:E))
  have hH : Continuous (fun z : ℝ × Sphere => H z.1 z.2) :=
    continuous_restrict_sphere (normalizedPullback_smooth p hF)
  have hR : Continuous (fun z : ℝ × Sphere => R z.1 z.2) :=
    continuous_restrict_sphere (pullbackRate_smooth p hF)
  have hHt (t : ℝ) : Continuous (H t) := by
    have hc : Continuous (fun n : Sphere => (t,n)) := continuous_const.prodMk continuous_id
    exact Continuous.comp (f := fun n : Sphere => (t,n))
      (g := fun z : ℝ × Sphere => H z.1 z.2) hH hc
  have hRt (t : ℝ) : Continuous (R t) := by
    have hc : Continuous (fun n : Sphere => (t,n)) := continuous_const.prodMk continuous_id
    exact Continuous.comp (f := fun n : Sphere => (t,n))
      (g := fun z : ℝ × Sphere => R z.1 z.2) hR hc
  let K : Set (ℝ × Sphere) := Icc (t₀-1) (t₀+1) ×ˢ univ
  have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hR.continuousOn
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := surfaceMeasure) (x₀ := t₀) (s := Ioo (t₀-1) (t₀+1))
    (F := H) (F' := R) (bound := fun _ => C)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun t => (hHt t).aestronglyMeasurable)
    ((hHt t₀).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hRt t₀).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun n t ht => hC (t,n) ⟨⟨ht.1.le,ht.2.le⟩, mem_univ n⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun n t _ => pullback_time_derivative p hF t n)
  convert! h.2 using 1
  exact (pullbackRate_integral_zero p hF t₀).symm

theorem flow_area_substitution (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) (t : ℝ) :
    ∫ n : Sphere, (flowD p t n)⁻¹ ^2 * F (flowPhi p t n) ∂surfaceMeasure =
      ∫ n : Sphere, F n ∂surfaceMeasure := by
  let H (t : ℝ) (n : Sphere) := normalizedPullback p F (t,(n:E))
  have hd := normalizedIntegral_derivative_zero p hF
  have he := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  have hzero : ∀ n : Sphere, H 0 n = F n := by
    intro n
    simp [H, normalizedPullback_sphere, weightedPullback, flowPhi, flowD, flowEnergy,
      flowS, flowCoeff]
  have ht : ∀ n : Sphere, H t n = (flowD p t n)⁻¹ ^2 * F (flowPhi p t n) := by
    intro n
    rw [show H t n = weightedPullback p t F n by exact normalizedPullback_sphere p F t n]
    rfl
  change (∫ n : Sphere, H t n ∂surfaceMeasure) = ∫ n : Sphere, H 0 n ∂surfaceMeasure at he
  simpa only [hzero,ht] using he

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Topology
open MeasureTheory
open CKSSphericalHarmonics (puncturedSpace surfaceMeasure)

lemma flowEnergy_normalized {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) : flowEnergy (m⁻¹ • p) 1 = e/m := by
  have hs : (e/m)^2 = 1+‖m⁻¹ • p‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm0)]
    field_simp
    nlinarith
  have hf := flowEnergy_sq (m⁻¹ • p) 1
  simp only [one_pow, one_mul] at hf
  nlinarith [flowEnergy_pos (m⁻¹ • p) 1, div_pos (energy_pos he) hm0]

lemma flowD_normalized {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) (n : E) :
    flowD (m⁻¹ • p) 1 n = denominator e m p n := by
  simp only [flowD, flowEnergy_normalized he hm0 hm, one_mul, inner_smul_left, conj_trivial, denominator]
  ring

lemma flowS_normalized {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) (n : E) :
    flowS (m⁻¹ • p) 1 n = boundarySpatial e m p n := by
  simp only [flowS, flowCoeff, flowEnergy_normalized he hm0 hm, one_pow, boundarySpatial,
    inner_smul_left, conj_trivial, smul_smul]
  congr 1
  congr 1
  field_simp

lemma flowPhi_normalized {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) (n : E) :
    flowPhi (m⁻¹ • p) 1 n = boundaryAmbient e m p n := by
  rw [flowPhi, flowD_normalized he hm0 hm, flowS_normalized he hm0 hm]
  rfl

theorem boost_area_substitution {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    ∫ n : Sphere, (denominator e m p n)⁻¹ ^2 * F (boundaryAmbient e m p n) ∂surfaceMeasure =
      ∫ n : Sphere, F n ∂surfaceMeasure := by
  have h := flow_area_substitution (m⁻¹ • p) hF 1
  simpa only [flowD_normalized he hm0 hm, flowPhi_normalized he hm0 hm] using h

lemma inverse_null_boundary (e : ℝ) (p : E) (he : ‖p‖ < e) (n : Sphere) :
    boostCLM e (mass e p) (-p) (1,(boundary e p he n:E)) =
      (denominator e (mass e p) p n)⁻¹ • ((1:ℝ),(n:E)) := by
  have h := congrArg (boostCLM e (mass e p) (-p)) (boundary_null e p he n)
  simp only [map_smul, boostCLM_apply] at h
  rw [boost_neg_inverse (mass_pos he).ne' (add_pos (energy_pos he) (mass_pos he)).ne' (mass_sq he)] at h
  rw [h, smul_smul, inv_mul_cancel₀ (denominator_pos he (mass_pos he) n).ne', one_smul]
  rfl

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere radialExtension radialExtension_smooth radialExtension_on_sphere surfaceMeasure)

lemma nullDirection_smooth : ContMDiff (𝓡 2) 𝓘(ℝ,V) ∞ nullDirection :=
by
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun _ : Sphere => (1:ℝ)) := contMDiff_const
  exact hc.prodMk_space (contMDiff_coe_sphere (E := E) (n := 2))

lemma aspectPullback_smooth (e : ℝ) (p : E) (he : ‖p‖ < e) {M : Sphere → ℝ}
    (hM : SmoothSphere M) : SmoothSphere (aspectPullback e p he M) := by
  have hd : ContDiff ℝ ∞ (denominator e (mass e p) p) :=
    (contDiff_const.add (ContDiff.inner ℝ contDiff_const contDiff_id)).div_const _
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun n : Sphere => denominator e (mass e p) p n) :=
    hd.comp_contMDiff (contMDiff_coe_sphere (E := E) (n := 2))
  exact ((hc.inv₀ (fun n => (denominator_pos he (mass_pos he) n).ne')).pow 3).mul
    (hM.comp (boundary_smooth e p he))

lemma rawCharge_integrable {M : Sphere → ℝ} (hM : SmoothSphere M) :
    Integrable (fun n => M n • nullDirection n) surfaceMeasure :=
  (hM.continuous.smul nullDirection_smooth.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma rawCharge_test {M : Sphere → ℝ} (hM : SmoothSphere M) (L : V →L[ℝ] ℝ) :
    L (rawCharge M) = ∫ n : Sphere, M n * L (nullDirection n) ∂surfaceMeasure := by
  rw [rawCharge, ← L.integral_comp_comm (rawCharge_integrable hM)]
  simp only [map_smul, smul_eq_mul]

lemma transformedCharge_test (e : ℝ) (p : E) (he : ‖p‖ < e) {M : Sphere → ℝ}
    (hM : SmoothSphere M) (L : V →L[ℝ] ℝ) :
    L (rawCharge (aspectPullback e p he M)) =
      L (boostCLM e (mass e p) (-p) (rawCharge M)) := by
  let B := boostCLM e (mass e p) (-p)
  let Q : Sphere → ℝ := fun n => M n * L (B (nullDirection n))
  have hQ : SmoothSphere Q := hM.mul
    (L.contMDiff.comp (B.contMDiff.comp nullDirection_smooth))
  have hi := boost_area_substitution he (mass_pos he) (mass_sq he) (radialExtension_smooth hQ)
  have hiR : (∫ n : Sphere, radialExtension Q n ∂surfaceMeasure) =
      L (B (rawCharge M)) := by
    change _ = (L.comp B) (rawCharge M)
    rw [rawCharge_test hM (L.comp B)]
    congr 1
    funext n
    rw [radialExtension_on_sphere]
    rfl
  have hiL : (∫ n : Sphere,
      (denominator e (mass e p) p n)⁻¹ ^2 * radialExtension Q (boundaryAmbient e (mass e p) p n) ∂surfaceMeasure) =
      L (rawCharge (aspectPullback e p he M)) := by
    rw [rawCharge_test (aspectPullback_smooth e p he hM)]
    congr 1
    funext n
    change (denominator e (mass e p) p n)⁻¹ ^2 * radialExtension Q (boundary e p he n) = _
    rw [radialExtension_on_sphere]
    dsimp only [Q, B, nullDirection]
    rw [inverse_null_boundary e p he n, map_smul, smul_eq_mul]
    dsimp only [aspectPullback, nullDirection]
    ring
  rw [hiL,hiR] at hi
  exact hi

theorem rawCharge_lorentz (e : ℝ) (p : E) (he : ‖p‖ < e) {M : Sphere → ℝ}
    (hM : SmoothSphere M) :
    rawCharge (aspectPullback e p he M) = boostCLM e (mass e p) (-p) (rawCharge M) := by
  apply Prod.ext
  · exact transformedCharge_test e p he hM (ContinuousLinearMap.fst ℝ ℝ E)
  · ext i
    exact transformedCharge_test e p he hM ((EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ ℝ E))

theorem bondiCharge_lorentz (e : ℝ) (p : E) (he : ‖p‖ < e) {M : Sphere → ℝ}
    (hM : SmoothSphere M) :
    bondiCharge (aspectPullback e p he M) = boostCLM e (mass e p) (-p) (bondiCharge M) := by
  simp only [bondiCharge, rawCharge_lorentz e p he hM, map_smul]

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere surfaceMeasure Balanced sphereIntegral sphereArea)

lemma boost_to_rest {e : ℝ} {p : E} (he : ‖p‖ < e) :
    boostCLM e (mass e p) (-p) (e,p) = (mass e p,0) := by
  have h := boost_neg_inverse (mass_pos he).ne'
    (add_pos (energy_pos he) (mass_pos he)).ne' (mass_sq he) (mass e p,0)
  rw [boost_mass (mass_pos he).ne'] at h
  exact h

lemma charge_energy {M : Sphere → ℝ} (hM : SmoothSphere M) :
    (bondiCharge M).1 = (16*Real.pi)⁻¹ * ∫ n, M n ∂surfaceMeasure := by
  have h := rawCharge_test hM (ContinuousLinearMap.fst ℝ ℝ E)
  change (rawCharge M).1 = ∫ n, M n * 1 ∂surfaceMeasure at h
  simp only [mul_one] at h
  change (16*Real.pi)⁻¹ * (rawCharge M).1 = _
  rw [h]

lemma charge_momentum {M : Sphere → ℝ} (hM : SmoothSphere M) (i : Fin 3) :
    (bondiCharge M).2 i = (16*Real.pi)⁻¹ * ∫ n, M n * (n:E) i ∂surfaceMeasure := by
  have h := rawCharge_test hM
    ((EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ ℝ E))
  change (rawCharge M).2 i = ∫ n, M n * (n:E) i ∂surfaceMeasure at h
  change (16*Real.pi)⁻¹ * (rawCharge M).2 i = _
  rw [h]

lemma heatDatum_smooth {M : Sphere → ℝ} (hM : SmoothSphere M) :
    SmoothSphere (heatDatum M hM) := hM.div_const 4

lemma heatDatum_balanced {M : Sphere → ℝ} (hM : SmoothSphere M) {m : ℝ}
    (hc : bondiCharge M = (m,0)) : Balanced (heatDatum M hM) m := by
  have hp : 16*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have he := charge_energy hM
  rw [hc] at he
  have hm : ∫ n, M n ∂surfaceMeasure = (16*Real.pi)*m := by
    change m = (16*Real.pi)⁻¹ * _ at he
    calc
      _ = (16*Real.pi)*((16*Real.pi)⁻¹ * ∫ n, M n ∂surfaceMeasure) := by field_simp
      _ = _ := by rw [← he]
  constructor
  · rw [CKSSphericalHarmonics.sphereIntegral_apply, CKSSphericalHarmonics.sphereArea_eq_four_pi]
    change (∫ n, M n/4 ∂surfaceMeasure) = m*(4*Real.pi)
    simp only [div_eq_mul_inv, integral_mul_const, hm]
    ring
  · intro i
    have hq := charge_momentum hM i
    rw [hc] at hq
    have hi : ∫ n, M n * (n:E) i ∂surfaceMeasure = 0 := by
      have hz : (16*Real.pi)⁻¹ * (∫ n, M n * (n:E) i ∂surfaceMeasure) = 0 := hq.symm
      exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hp)
    rw [CKSSphericalHarmonics.sphereIntegral_apply]
    change (∫ n, (M n/4)*(n:E) i ∂surfaceMeasure) = 0
    have heq : (fun n : Sphere => (M n/4)*(n:E) i) = fun n => (M n*(n:E) i)/4 := by
      funext n; ring
    rw [heq]
    simp only [div_eq_mul_inv, integral_mul_const, hi, zero_mul]

theorem balanced_charge_and_heat {M : Sphere → ℝ} (hM : SmoothSphere M)
    (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1) :
    let e := (bondiCharge M).1
    let p := (bondiCharge M).2
    let M' := aspectPullback e p ht M
    ∃ hM' : SmoothSphere M',
      bondiCharge M' = (mass e p,0) ∧
      SmoothSphere (heatDatum M' hM') ∧
      Balanced (heatDatum M' hM') (mass e p) := by
  dsimp only
  let e := (bondiCharge M).1
  let p := (bondiCharge M).2
  let M' := aspectPullback e p ht M
  have hM' : SmoothSphere M' := aspectPullback_smooth e p ht hM
  refine ⟨hM', ?_, heatDatum_smooth hM', ?_⟩
  · rw [bondiCharge_lorentz e p ht hM]
    exact boost_to_rest ht
  · apply heatDatum_balanced hM'
    rw [bondiCharge_lorentz e p ht hM]
    exact boost_to_rest ht

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

end
end CKSAngularGeometry

end








noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

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
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
structure ContinuousMetricJetAt (g : PhysicalPoint → CKSRound.MetricJet) (x : PhysicalPoint) : Prop where
  inv : ∀ i j, ContinuousAt (fun y => (g y).inv i j) x
  d : ∀ a i j, ContinuousAt (fun y => (g y).d a i j) x
  dd : ∀ a b i j, ContinuousAt (fun y => (g y).dd a b i j) x
structure ContinuousTensorJetAt (k : PhysicalPoint → CKSRound.TensorJet) (x : PhysicalPoint) : Prop where
  val : ∀ i j, ContinuousAt (fun y => (k y).val i j) x
  d : ∀ a i j, ContinuousAt (fun y => (k y).d a i j) x
lemma ContinuousMetricJetAt.gamma {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (a i j : Fin 3) :
    ContinuousAt (fun y => (g y).gamma a i j) x := by
  have hi := h.inv
  have hd := h.d
  unfold CKSRound.MetricJet.gamma
  fun_prop
lemma ContinuousMetricJetAt.dInv {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (a i j : Fin 3) :
    ContinuousAt (fun y => (g y).dInv a i j) x := by
  have hi := h.inv
  have hd := h.d
  unfold CKSRound.MetricJet.dInv
  fun_prop
lemma ContinuousMetricJetAt.dGamma {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (a b i j : Fin 3) :
    ContinuousAt (fun y => (g y).dGamma a b i j) x := by
  have hi := h.inv
  have hd := h.d
  have hdd := h.dd
  have hdi := h.dInv
  unfold CKSRound.MetricJet.dGamma
  fun_prop
lemma ContinuousMetricJetAt.ricci {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (i j : Fin 3) :
    ContinuousAt (fun y => (g y).ricci i j) x := by
  have hc := h.gamma
  have hd := h.dGamma
  unfold CKSRound.MetricJet.ricci
  fun_prop
lemma ContinuousMetricJetAt.scalar {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) : ContinuousAt (fun y => (g y).scalar) x := by
  have hi := h.inv
  have hr := h.ricci
  unfold CKSRound.MetricJet.scalar
  fun_prop
lemma ContinuousMetricJetAt.trace {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => (g y).trace (k y)) x := by
  have hi := h.inv
  have hv := hk.val
  unfold CKSRound.MetricJet.trace
  fun_prop
lemma ContinuousMetricJetAt.normSq {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => (g y).normSq (k y)) x := by
  have hi := h.inv
  have hv := hk.val
  unfold CKSRound.MetricJet.normSq
  fun_prop
lemma ContinuousMetricJetAt.dTrace {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) (i : Fin 3) :
    ContinuousAt (fun y => (g y).dTrace (k y) i) x := by
  have hi := h.inv
  have hdi := h.dInv
  have hv := hk.val
  have hd := hk.d
  unfold CKSRound.MetricJet.dTrace
  fun_prop
lemma ContinuousMetricJetAt.tensorDivergence {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) (i : Fin 3) :
    ContinuousAt (fun y => (g y).tensorDivergence (k y) i) x := by
  have hi := h.inv
  have hc := h.gamma
  have hv := hk.val
  have hd := hk.d
  unfold CKSRound.MetricJet.tensorDivergence
  fun_prop
lemma ContinuousMetricJetAt.energy {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => (g y).energy (k y)) x := by
  have hs := h.scalar
  have ht := h.trace hk
  have hn := h.normSq hk
  unfold CKSRound.MetricJet.energy
  fun_prop
lemma ContinuousMetricJetAt.momentum {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) (i : Fin 3) :
    ContinuousAt (fun y => (g y).momentum (k y) i) x := by
  have ht := h.dTrace hk i
  have hd := h.tensorDivergence hk i
  unfold CKSRound.MetricJet.momentum
  fun_prop
lemma ContinuousMetricJetAt.momentumSq {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => CKSLocalBending.momentumSq (g y) (k y)) x := by
  have hi := h.inv
  have hm := h.momentum hk
  unfold CKSLocalBending.momentumSq
  fun_prop
lemma physicalMetricJet_continuousAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) : ContinuousMetricJetAt (physicalMetricJet G) x := by
  have hc (i j) := contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  refine ⟨fun i j => (matrix_inv_component_contDiffAt hg h0 i j).continuousAt,?_,?_⟩
  · intro a i j
    exact (contDiffAt_D (hc i j) (m := ∞) (by simp) (CKSRealizedRound.basis a)).continuousAt
  · intro a b i j
    exact (contDiffAt_D (contDiffAt_D (hc i j) (m := ∞) (by simp) (CKSRealizedRound.basis b))
      (m := ∞) (by simp) (CKSRealizedRound.basis a)).continuousAt
lemma physicalTensorJet_continuousAt {K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hk : ContDiffAt ℝ ∞ K x) : ContinuousTensorJetAt (physicalTensorJet K) x := by
  have hc (i j) := contDiffAt_pi.mp (contDiffAt_pi.mp hk i) j
  refine ⟨fun i j => (hc i j).continuousAt,?_⟩
  intro a i j
  exact (contDiffAt_D (hc i j) (m := ∞) (by simp) (CKSRealizedRound.basis a)).continuousAt

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

end
end CKSLorentz

end

















noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
theorem local_coordinate_energy_pullback
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y)
    (hi : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ e.symm y)
    (hE : ∀ᶠ y in 𝓝 (e x), SmoothOrthonormalAt G E y)
    (hK : ContDiffAt ℝ ∞ K (e x)) (hs : (K (e x)).IsHermitian) :
    (physicalMetricJet (coordinatePullback e G) x).energy
      (physicalTensorJet (coordinatePullback e K) x) =
    (physicalMetricJet G (e x)).energy (physicalTensorJet K (e x)) := by
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
  rw [physicalMetricJet_energy hc.target.metric_smooth hc.target.frame_smooth
      hc.target.positive hc.target.symmetric hkSymm hc.target.orthonormal,
    physicalMetricJet_energy hc.source.metric_smooth hc.source.frame_smooth
      hc.source.positive hc.source.symmetric hs hc.source.orthonormal] at hδ
  exact hδ

end
end CKSAngularGeometry

end



noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics CKSADM CKSBending Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma spatialCoefficients_congr {P Q : SpatialTensor} {x : E} (h : P =ᶠ[𝓝 x] Q) :
    spatialCoefficients P =ᶠ[𝓝 (CKSCartesianOuter.toPoint x)] spatialCoefficients Q := by
  have hh := CKSCartesianOuter.toPoint.symm.continuous.continuousAt.eventually
    (CKSCartesianOuter.toPoint.symm_apply_apply x ▸ h)
  filter_upwards [hh] with y hy
  ext i j
  change P (CKSCartesianOuter.toPoint.symm y) _ _ = Q (CKSCartesianOuter.toPoint.symm y) _ _
  rw [hy]
lemma spatialEnergy_congr {A B C D : SpatialTensor} {x : E}
    (hA : A =ᶠ[𝓝 x] C) (hB : B =ᶠ[𝓝 x] D) : spatialEnergy A B x = spatialEnergy C D x := by
  unfold spatialEnergy
  rw [physicalMetricJet_congr (spatialCoefficients_congr hA),physicalTensorJet_congr (spatialCoefficients_congr hB)]

end
end CKSLorentz

end







noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
lemma spatial_energy_continuousAt {A B : SpatialTensor} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x)
    (hsym : ∀ v w, A x v w = A x w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < A x v v) :
    ContinuousAt (spatialEnergy A B) x := by
  have hg := physicalMetricJet_continuousAt (spatialCoefficients_smooth hA)
    (spatialCoefficients_positive hsym hpos).det_pos.ne'
  have hk := physicalTensorJet_continuousAt (spatialCoefficients_smooth hB)
  exact (hg.energy hk).comp CKSCartesianOuter.toPoint.continuous.continuousAt

end
end CKSLorentz

end








noncomputable section
namespace CKSGeometricCuts
noncomputable section
open Set Manifold MeasureTheory CKSReplacementCompleteness
open scoped ContDiff ENNReal NNReal
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H3 M]
  [IsManifold I3 1 M] [T3Space M]

def identityOuterDomain [IsManifold I3 ∞ M] [ConnectedSpace M]
    (hS : IsCompact (I3.boundary M)) : OuterDomain M where
  Carrier := M
  topology := inferInstance
  charts := inferInstance
  smooth := inferInstance
  inclusion := id
  embedding := IsSmoothEmbedding.id
  closed := by simpa only [range_id] using (isClosed_univ : IsClosed (univ : Set M))
  connected := by simpa only [range_id] using (isConnected_univ : IsConnected (univ : Set M))
  contains_distant_end := ⟨∅,isCompact_empty,by simp⟩
  interior_into := by simp
  compact_boundary := by simpa using hS

end
end CKSGeometricCuts

end







noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
lemma endInner_fullRank (g : SmoothMetric I (M := M)) (f : M → E)
    (A : SpatialTensor) {x : M} (heq : g.inner x = endInner I f A x) :
    Function.Bijective (mfderiv I 𝓘(ℝ,E) f x) := by
  let : FiniteDimensional ℝ (TangentSpace I x) := by exact (inferInstance : FiniteDimensional ℝ E)
  have hi : Function.Injective (mfderiv I 𝓘(ℝ,E) f x) := by
    intro v w hvw
    by_contra hne
    have hp := g.pos x (v-w) (sub_ne_zero.mpr hne)
    rw [heq] at hp
    have hz : (mfderiv I 𝓘(ℝ,E) f x) (v-w) = 0 := by rw [map_sub,hvw,sub_self]
    change 0 < A (f x) ((mfderiv I 𝓘(ℝ,E) f x) (v-w))
      ((mfderiv I 𝓘(ℝ,E) f x) (v-w)) at hp
    rw [hz] at hp
    have ha : A (f x) (0:E) (0:E) = 0 := by simp
    exact (lt_irrefl 0) (ha ▸ hp)
  exact ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩

end
end CKSSpatialManifold

end


noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
omit [IsManifold I ∞ M] in
lemma endInner_comp [IsManifold I ∞ M] {F : E → E} {f : M → E}
    (A : SpatialTensor) {x : M}
    (hF : ContDiffAt ℝ ∞ F (f x)) (hf : ContMDiffAt I 𝓘(ℝ,E) ∞ f x) :
    endInner I (F ∘ f) A x = endInner I f (spatialTensorPullback F A) x := by
  have hc := mfderiv_comp x (hF.contMDiffAt.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hc
  ext v w
  change A (F (f x)) ((mfderiv I 𝓘(ℝ,E) (F ∘ f) x) v)
      ((mfderiv I 𝓘(ℝ,E) (F ∘ f) x) w) =
    A (F (f x)) ((fderiv ℝ F (f x)) ((mfderiv I 𝓘(ℝ,E) f x) v))
      ((fderiv ℝ F (f x)) ((mfderiv I 𝓘(ℝ,E) f x) w))
  rw [hc]
  rfl
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem endInner_balanced {e : ℝ} {p : E} (he : ‖p‖ < e)
    (f : M → E) (A : SpatialTensor) {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ,E) ∞ f x) :
    endInner I ((hyperbolicHomeomorph e p he).symm ∘ f)
      (sourceSpatial (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)) x =
      endInner I f (sourceSpatial A) x := by
  rw [sourceSpatial_boost he]
  let h := hyperbolicHomeomorph e p he
  have hi : ContDiff ℝ ∞ h.symm := hyperbolicMap_smooth e (mass e p) (-p)
  have hs : ContDiff ℝ ∞ h := hyperbolicMap_smooth e (mass e p) p
  have hf' : ContMDiffAt I 𝓘(ℝ,E) ∞ (h.symm ∘ f) x := hi.contDiffAt.contMDiffAt.comp x hf
  have ht := endInner_comp (I := I) (F := h) (f := h.symm ∘ f)
    (sourceSpatial A) hs.contDiffAt hf'
  have heq : h ∘ (h.symm ∘ f) = f := by funext y; exact h.apply_symm_apply (f y)
  rw [heq] at ht
  exact ht.symm
end
end CKSSpatialManifold

end



end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CKSIntrinsicConstraints
lemma coordinateMomentumNorm_continuousAt {A B : SpatialTensor} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x)
    (hsym : ∀ v w, A x v w = A x w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < A x v v) :
    ContinuousAt (coordinateMomentumNorm A B) x := by
  have hg := physicalMetricJet_continuousAt (spatialCoefficients_smooth hA)
    (spatialCoefficients_positive hsym hpos).det_pos.ne'
  have hk := physicalTensorJet_continuousAt (spatialCoefficients_smooth hB)
  exact (hg.momentumSq hk).sqrt.comp CKSCartesianOuter.toPoint.continuous.continuousAt

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {g K : InnerField I (M := M)} {x : M}
def ConstraintChart.at (c : ConstraintChart g K x) (y : M) (hy : y ∈ c.domain) :
    ConstraintChart g K y := { c with mem := hy }
omit [IsManifold I ∞ M] in
lemma ConstraintChart.continuous_energy [IsManifold I ∞ M] (c : ConstraintChart g K x) :
    ContinuousOn (fun y => spatialEnergy c.metric c.tensor (c.coordinate y)) c.domain := by
  intro y hy
  exact (spatial_energy_continuousAt (c.coefficientSmooth y hy).1
    (c.coefficientSmooth y hy).2 (c.positiveSymmetric y hy).1
    (c.positiveSymmetric y hy).2.1).comp_continuousWithinAt
      (c.smooth.continuousOn y hy)
omit [IsManifold I ∞ M] in
lemma ConstraintChart.continuous_momentumNorm [IsManifold I ∞ M] (c : ConstraintChart g K x) :
    ContinuousOn (fun y => coordinateMomentumNorm c.metric c.tensor (c.coordinate y)) c.domain := by
  intro y hy
  exact (coordinateMomentumNorm_continuousAt (c.coefficientSmooth y hy).1
    (c.coefficientSmooth y hy).2 (c.positiveSymmetric y hy).1
    (c.positiveSymmetric y hy).2.1).comp_continuousWithinAt
      (c.smooth.continuousOn y hy)
end CKSIntrinsicConstraints

end

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CKSAngularGeometry
lemma momentumSq_eq_frame {G K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x) (hk : ContDiffAt ℝ ∞ K x) :
    CKSLocalBending.momentumSq (physicalMetricJet G x) (physicalTensorJet K x) =
      ∑ a, (actualFrameMomentum G K E x a)^2 := by
  rw [physical_momentum_frame_norm_general h (hk.differentiableAt (by simp))]
  simp only [metricPair,physicalMetricJet_momentum h.metric_smooth hk h.positive.det_pos.ne' h.symmetric]
  rfl

lemma local_coordinate_momentumSq_pullback
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y)
    (hi : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ e.symm y)
    (hE : ∀ᶠ y in 𝓝 (e x), SmoothOrthonormalAt G E y)
    (hK : ContDiffAt ℝ ∞ K (e x)) :
    CKSLocalBending.momentumSq (physicalMetricJet (coordinatePullback e G) x)
      (physicalTensorJet (coordinatePullback e K) x) =
    CKSLocalBending.momentumSq (physicalMetricJet G (e x)) (physicalTensorJet K (e x)) := by
  have h : ∀ᶠ y in 𝓝 x, FrameChartAt e G (coordinatePullback e G) E
      (coordinatePullbackFrame e E) y := by
    filter_upwards [e.open_source.mem_nhds hx,he,
      he.self_of_nhds.continuousAt.eventually hi,he.self_of_nhds.continuousAt.eventually hE]
      with y hy hey hiy hEy
    exact smooth_coordinate_pullback_frame_at e G E hy hey hiy hEy
  have hc := h.self_of_nhds
  have hk' := coordinatePullback_smooth hc.chart_smooth hK
  have hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (coordinatePullback e K y) v w =
      metricPair (K (e y)) (fderiv ℝ e y v) (fderiv ℝ e y w) :=
    Eventually.of_forall fun y => coordinatePullback_pair e K y
  obtain ⟨_,_,hJ⟩ := actual_constraints_chart_covariance h hK hkl
  rw [momentumSq_eq_frame hc.target hk',momentumSq_eq_frame hc.source hK]
  simp_rw [hJ]
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace CKSIntrinsicConstraints
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
theorem exists_smooth_local_inverse {f : E → E} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ f y)
    (hb : Function.Bijective (fderiv ℝ f x)) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = f ∧ x ∈ e.source ∧
      (∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y) ∧
      (∀ᶠ y in 𝓝 (f x), ContDiffAt ℝ ∞ e.symm y) := by
  let L : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap hb).toContinuousLinearEquiv
  have hLeq : L.toContinuousLinearMap = fderiv ℝ f x := by ext v; rfl
  have hd : HasFDerivAt f (L : E →L[ℝ] E) x := by
    rw [hLeq]
    exact (hf.self_of_nhds.differentiableAt (by simp)).hasFDerivAt
  let e := hf.self_of_nhds.toOpenPartialHomeomorph f hd (by simp)
  have hx : x ∈ e.source := hf.self_of_nhds.mem_toOpenPartialHomeomorph_source hd (by simp)
  refine ⟨e,rfl,hx,hf,?_⟩
  have hL : ∀ᶠ y in 𝓝 x, ∃ L' : E ≃L[ℝ] E,
      L'.toContinuousLinearMap = fderiv ℝ f y :=
    by
    have h := (hf.self_of_nhds.continuousAt_fderiv (by simp)).eventually (hLeq ▸ L.nhds)
    exact h
  have hec : Tendsto e.symm (𝓝 (f x)) (𝓝 x) := e.tendsto_symm hx
  filter_upwards [e.open_target.mem_nhds (e.map_source hx),hec.eventually hf,
    hec.eventually hL] with y hy hfy hLy
  obtain ⟨L',hL'⟩ := hLy
  apply e.contDiffAt_symm hy (f₀' := L') _ hfy
  rw [hL']
  exact (hfy.differentiableAt (by simp)).hasFDerivAt
end CKSIntrinsicConstraints

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped ContDiff Topology
namespace CKSIntrinsicConstraints
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {g K : InnerField I (M := M)} {x : M}

def inverseChartFrame (z : M) (u : E) : E →L[ℝ] TangentSpace I ((extChartAt I z).symm u) :=
  mfderivWithin 𝓘(ℝ,E) I (extChartAt I z).symm (range I) u

lemma ConstraintChart.interior_coordinate_smooth (c : ConstraintChart g K x) (z : M) {u : E}
    (hu : u ∈ interior (extChartAt I z).target)
    (hc : (extChartAt I z).symm u ∈ c.domain) :
    ContDiffAt ℝ ∞ (c.coordinate ∘ (extChartAt I z).symm) u := by
  exact (((c.smooth _ hc).contMDiffAt (c.isOpen.mem_nhds hc)).comp u
    ((contMDiffOn_extChartAt_symm z u (interior_subset hu)).contMDiffAt
      (mem_interior_iff_mem_nhds.mp hu))).contDiffAt

lemma ConstraintChart.interior_coordinate_deriv (c : ConstraintChart g K x) (z : M) {u : E}
    (hu : u ∈ interior (extChartAt I z).target)
    (hc : (extChartAt I z).symm u ∈ c.domain) :
    fderiv ℝ (c.coordinate ∘ (extChartAt I z).symm) u =
      (mfderiv I 𝓘(ℝ,E) c.coordinate ((extChartAt I z).symm u)).comp (inverseChartFrame z u) := by
  have h := (((c.smooth _ hc).contMDiffAt (c.isOpen.mem_nhds hc)).mdifferentiableAt
    (by simp)).hasMFDerivAt.comp_hasMFDerivWithinAt u
      (mdifferentiableWithinAt_extChartAt_symm (interior_subset hu)).hasMFDerivWithinAt
  have hd : HasFDerivWithinAt (c.coordinate ∘ (extChartAt I z).symm)
      ((mfderiv I 𝓘(ℝ,E) c.coordinate ((extChartAt I z).symm u)).comp (inverseChartFrame z u))
      (range I) u := h.hasFDerivWithinAt
  have hat : HasFDerivAt (c.coordinate ∘ (extChartAt I z).symm)
      ((mfderiv I 𝓘(ℝ,E) c.coordinate ((extChartAt I z).symm u)).comp (inverseChartFrame z u)) u :=
    hd.hasFDerivAt (mem_of_superset (mem_interior_iff_mem_nhds.mp hu)
      (extChartAt_target_subset_range z))
  exact HasFDerivAt.fderiv (E := E) (F := E) hat

lemma inverseChartFrame_bijective (z : M) {u : E}
    (hu : u ∈ (extChartAt I z).target) : Function.Bijective (inverseChartFrame z u) := by
  let : FiniteDimensional ℝ (TangentSpace I ((extChartAt I z).symm u)) :=
    (inferInstance : FiniteDimensional ℝ E)
  have hi : Function.Injective (inverseChartFrame z u) := by
    intro v w h
    have h' := congrArg (mfderiv I 𝓘(ℝ,E) (extChartAt I z) ((extChartAt I z).symm u)) h
    have he := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hu
    have hv := congrArg (fun L : E →L[ℝ] E => L v) he
    have hw := congrArg (fun L : E →L[ℝ] E => L w) he
    exact hv.symm.trans (h'.trans hw)
  exact ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩

lemma ConstraintChart.interior_coordinate_fullRank (c : ConstraintChart g K x) (z : M) {u : E}
    (hu : u ∈ interior (extChartAt I z).target)
    (hc : (extChartAt I z).symm u ∈ c.domain) :
    Function.Bijective (fderiv ℝ (c.coordinate ∘ (extChartAt I z).symm) u) := by
  rw [c.interior_coordinate_deriv z hu hc]
  exact (c.fullRank _ hc).comp (inverseChartFrame_bijective z (interior_subset hu))

lemma ConstraintChart.interior_pullback_equal (c d : ConstraintChart g K x) (z : M) {u : E}
    (hu : u ∈ interior (extChartAt I z).target)
    (hc : (extChartAt I z).symm u ∈ c.domain)
    (hd : (extChartAt I z).symm u ∈ d.domain) :
    spatialTensorPullback (c.coordinate ∘ (extChartAt I z).symm) c.metric u =
      spatialTensorPullback (d.coordinate ∘ (extChartAt I z).symm) d.metric u ∧
    spatialTensorPullback (c.coordinate ∘ (extChartAt I z).symm) c.tensor u =
      spatialTensorPullback (d.coordinate ∘ (extChartAt I z).symm) d.tensor u := by
  have heqg := (c.represents _ hc).1.symm.trans (d.represents _ hd).1
  have heqK := (c.represents _ hc).2.symm.trans (d.represents _ hd).2
  constructor
  · ext v w
    simp only [spatialTensorPullback,
      c.interior_coordinate_deriv z hu hc,d.interior_coordinate_deriv z hu hd]
    exact congrArg (fun A => A (inverseChartFrame z u v) (inverseChartFrame z u w)) heqg
  · ext v w
    simp only [spatialTensorPullback,
      c.interior_coordinate_deriv z hu hc,d.interior_coordinate_deriv z hu hd]
    exact congrArg (fun A => A (inverseChartFrame z u v) (inverseChartFrame z u w)) heqK
end CKSIntrinsicConstraints

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter CKSLorentz CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CKSIntrinsicConstraints
lemma full_rank_physical_constraints_pullback
    {f : PhysicalPoint → PhysicalPoint} {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hf : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ f y)
    (hb : Function.Bijective (fderiv ℝ f x))
    (hdata : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ G (f y) ∧
      ContDiffAt ℝ ∞ K (f y) ∧ (G (f y)).PosDef)
    (hKsym : (K (f x)).IsHermitian) :
    (physicalMetricJet (coordinatePullback f G) x).energy
      (physicalTensorJet (coordinatePullback f K) x) =
      (physicalMetricJet G (f x)).energy (physicalTensorJet K (f x)) ∧
    CKSLocalBending.momentumSq (physicalMetricJet (coordinatePullback f G) x)
      (physicalTensorJet (coordinatePullback f K) x) =
      CKSLocalBending.momentumSq (physicalMetricJet G (f x)) (physicalTensorJet K (f x)) := by
  obtain ⟨e,he,hx,hs,hi⟩ := exists_smooth_local_inverse hf hb
  have ht : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ G y ∧ ContDiffAt ℝ ∞ K y ∧ (G y).PosDef := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx),
      (e.tendsto_symm hx).eventually hdata] with y hy hd
    rw [← he,e.right_inv hy] at hd
    exact hd
  have hp : ∀ᶠ y in 𝓝 (e x), (G y).PosDef := ht.mono fun _ h => h.2.2
  have hE : ∀ᶠ y in 𝓝 (e x), SmoothOrthonormalAt G (matrixFrame G) y := by
    filter_upwards [ht,hp.eventually_nhds] with y hy hpy
    exact actual_matrix_frame hy.1 hpy
  rw [← he] at hi hKsym ⊢
  exact ⟨local_coordinate_energy_pullback e G K (matrixFrame G) hx hs hi hE
    ht.self_of_nhds.2.1 hKsym,
    local_coordinate_momentumSq_pullback e G K (matrixFrame G) hx hs hi hE ht.self_of_nhds.2.1⟩

def physicalMap (f : E → E) : PhysicalPoint → PhysicalPoint :=
  CKSCartesianOuter.toPoint ∘ f ∘ CKSCartesianOuter.toPoint.symm

lemma physicalMap_smooth {f : E → E} {x : E} (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (physicalMap f) (CKSCartesianOuter.toPoint x) := by
  exact CKSCartesianOuter.toPoint.contDiff.contDiffAt.comp _
    (hf.comp _ CKSCartesianOuter.toPoint.symm.contDiff.contDiffAt)
lemma physicalMap_fderiv {f : E → E} {y : PhysicalPoint}
    (hf : DifferentiableAt ℝ f (CKSCartesianOuter.toPoint.symm y)) :
    fderiv ℝ (physicalMap f) y = CKSCartesianOuter.toPoint.toContinuousLinearMap.comp
      ((fderiv ℝ f (CKSCartesianOuter.toPoint.symm y)).comp
        CKSCartesianOuter.toPoint.symm.toContinuousLinearMap) := by
  simp only [physicalMap,fderiv_comp y CKSCartesianOuter.toPoint.differentiableAt
    (hf.comp y CKSCartesianOuter.toPoint.symm.differentiableAt),
    fderiv_comp y hf CKSCartesianOuter.toPoint.symm.differentiableAt,ContinuousLinearEquiv.fderiv]
lemma physicalMap_bijective_fderiv {f : E → E} {x : E}
    (hf : DifferentiableAt ℝ f x) (hb : Function.Bijective (fderiv ℝ f x)) :
    Function.Bijective (fderiv ℝ (physicalMap f) (CKSCartesianOuter.toPoint x)) := by
  rw [physicalMap_fderiv (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf),
    ContinuousLinearEquiv.symm_apply_apply]
  exact CKSCartesianOuter.toPoint.bijective.comp (hb.comp CKSCartesianOuter.toPoint.symm.bijective)
lemma spatialCoefficients_function_pullback (f : E → E) (A : SpatialTensor) {y : PhysicalPoint}
    (hf : DifferentiableAt ℝ f (CKSCartesianOuter.toPoint.symm y)) :
    coordinatePullback (physicalMap f) (spatialCoefficients A) y =
      spatialCoefficients (spatialTensorPullback f A) y := by
  ext i j
  unfold coordinatePullback
  rw [spatialCoefficients_pair,physicalMap_fderiv hf]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply,physicalMap,Function.comp_apply]
  rfl

lemma full_rank_spatial_constraints_pullback
    {f : E → E} {A B : SpatialTensor} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ f y)
    (hb : Function.Bijective (fderiv ℝ f x))
    (hdata : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ A (f y) ∧ ContDiffAt ℝ ∞ B (f y) ∧
      (∀ v w, A (f y) v w = A (f y) w v) ∧
      (∀ v : E, v ≠ 0 → 0 < A (f y) v v))
    (hBsym : ∀ v w, B (f x) v w = B (f x) w v) :
    spatialEnergy (spatialTensorPullback f A) (spatialTensorPullback f B) x =
      spatialEnergy A B (f x) ∧
    coordinateMomentumNorm (spatialTensorPullback f A) (spatialTensorPullback f B) x =
      coordinateMomentumNorm A B (f x) := by
  have ht := CKSCartesianOuter.toPoint.symm.continuous.continuousAt (x := CKSCartesianOuter.toPoint x)
  have hf' : ∀ᶠ y in 𝓝 (CKSCartesianOuter.toPoint x), ContDiffAt ℝ ∞ (physicalMap f) y := by
    filter_upwards [ht.eventually (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf)] with y hy
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using physicalMap_smooth hy
  have hd : ∀ᶠ y in 𝓝 (CKSCartesianOuter.toPoint x),
      ContDiffAt ℝ ∞ (spatialCoefficients A) (physicalMap f y) ∧
      ContDiffAt ℝ ∞ (spatialCoefficients B) (physicalMap f y) ∧
      (spatialCoefficients A (physicalMap f y)).PosDef := by
    filter_upwards [ht.eventually (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hdata)] with y hy
    exact ⟨spatialCoefficients_smooth hy.1,spatialCoefficients_smooth hy.2.1,
      spatialCoefficients_positive hy.2.2.1 hy.2.2.2⟩
  have heq (G : SpatialTensor) :
      coordinatePullback (physicalMap f) (spatialCoefficients G) =ᶠ[𝓝 (CKSCartesianOuter.toPoint x)]
        spatialCoefficients (spatialTensorPullback f G) := by
    filter_upwards [ht.eventually (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf)] with y hy
    exact spatialCoefficients_function_pullback f G (hy.differentiableAt (by simp))
  have hBs : (spatialCoefficients B (physicalMap f (CKSCartesianOuter.toPoint x))).IsHermitian := by
    simpa only [physicalMap,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using
      spatialCoefficients_symmetric hBsym
  obtain ⟨hC,hQ⟩ := full_rank_physical_constraints_pullback hf'
    (physicalMap_bijective_fderiv (hf.self_of_nhds.differentiableAt (by simp)) hb) hd hBs
  rw [physicalMetricJet_congr (heq A),physicalTensorJet_congr (heq B)] at hC hQ
  refine ⟨?_,?_⟩
  · simpa only [spatialEnergy,physicalMap,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using hC
  · simpa only [coordinateMomentumNorm,physicalMap,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using congrArg Real.sqrt hQ
end CKSIntrinsicConstraints

end

end OAI
end

section
namespace OAI

noncomputable section
open Manifold Set Filter
open scoped ContDiff Topology
namespace CKSIntrinsicTopology
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
lemma dense_interior : Dense (I.interior M) := by
  intro x
  let u := extChartAt I x x
  have hu : u ∈ (extChartAt I x).target := mem_extChartAt_target x
  have hcl : u ∈ closure (interior (range I)) :=
    I.range_subset_closure_interior (extChartAt_target_subset_range x hu)
  let : NeBot (𝓝[interior (range I)] u) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hcont : ContinuousWithinAt (extChartAt I x).symm (range I) u :=
    (mdifferentiableWithinAt_extChartAt_symm hu).continuousWithinAt
  have ht : Tendsto (extChartAt I x).symm (𝓝[interior (range I)] u) (𝓝 x) := by
    simpa only [ContinuousWithinAt,u,extChartAt_to_inv] using hcont.mono interior_subset
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    (nhdsWithin_mono u interior_subset) (extChartAt_target_mem_nhdsWithin x)] with y hy hty
  have hiny : y ∈ interior (extChartAt I x).target := by
    apply mem_interior_iff_mem_nhds.mpr
    have hn := extChartAt_target_mem_nhdsWithin_of_mem hty
    rwa [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hy)] at hn
  apply (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
    (chart_mem_atlas H x) (by simpa only [extChartAt_source] using (extChartAt I x).map_target hty)).mpr
  change extChartAt I x ((extChartAt I x).symm y) ∈ interior (extChartAt I x).target
  rwa [(extChartAt I x).right_inv hty]
end CKSIntrinsicTopology

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing CKSAngularGeometry
open scoped ContDiff Topology
namespace CKSIntrinsicConstraints
lemma coordinateMomentumNorm_congr {A B C D : SpatialTensor} {x : E}
    (hA : A =ᶠ[𝓝 x] C) (hB : B =ᶠ[𝓝 x] D) :
    coordinateMomentumNorm A B x = coordinateMomentumNorm C D x := by
  unfold coordinateMomentumNorm
  rw [physicalMetricJet_congr (spatialCoefficients_congr hA),
    physicalTensorJet_congr (spatialCoefficients_congr hB)]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {g K : InnerField I (M := M)} {x : M}
lemma ConstraintChart.compare_interior (c d : ConstraintChart g K x)
    (hx : I.IsInteriorPoint x) : c.energy = d.energy ∧ c.momentumNorm = d.momentumNorm := by
  let u := extChartAt I x x
  have hu : u ∈ interior (extChartAt I x).target := I.isInteriorPoint_iff.mp hx
  have hux : (extChartAt I x).symm u = x := extChartAt_to_inv x
  have hcont : ContinuousAt (extChartAt I x).symm u :=
    ((contMDiffOn_extChartAt_symm (n := ∞) x u (interior_subset hu)).contMDiffAt
      (mem_interior_iff_mem_nhds.mp hu)).continuousAt
  have hc : (extChartAt I x).symm u ∈ c.domain := by rw [hux]; exact c.mem
  have hd : (extChartAt I x).symm u ∈ d.domain := by rw [hux]; exact d.mem
  have hnb : ∀ᶠ y in 𝓝 u, y ∈ interior (extChartAt I x).target ∧
      (extChartAt I x).symm y ∈ c.domain ∧ (extChartAt I x).symm y ∈ d.domain := by
    filter_upwards [isOpen_interior.mem_nhds hu,
      hcont.eventually (c.isOpen.mem_nhds hc),hcont.eventually (d.isOpen.mem_nhds hd)] with y hy hcy hdy
    exact ⟨hy,hcy,hdy⟩
  have hcov (a : ConstraintChart g K x) (ha : (extChartAt I x).symm u ∈ a.domain)
      (ah : ∀ᶠ y in 𝓝 u, (extChartAt I x).symm y ∈ a.domain) :=
    full_rank_spatial_constraints_pullback
      (show ∀ᶠ y in 𝓝 u, ContDiffAt ℝ ∞ (a.coordinate ∘ (extChartAt I x).symm) y from by
        filter_upwards [hnb,ah] with y hy hay
        exact a.interior_coordinate_smooth x hy.1 hay)
      (a.interior_coordinate_fullRank x hu ha)
      (show ∀ᶠ y in 𝓝 u, ContDiffAt ℝ ∞ a.metric (a.coordinate ((extChartAt I x).symm y)) ∧
        ContDiffAt ℝ ∞ a.tensor (a.coordinate ((extChartAt I x).symm y)) ∧
        (∀ v w, a.metric (a.coordinate ((extChartAt I x).symm y)) v w =
          a.metric (a.coordinate ((extChartAt I x).symm y)) w v) ∧
        (∀ v : E, v ≠ 0 → 0 < a.metric (a.coordinate ((extChartAt I x).symm y)) v v) from by
          filter_upwards [ah] with y hay
          exact ⟨(a.coefficientSmooth _ hay).1,(a.coefficientSmooth _ hay).2,
            (a.positiveSymmetric _ hay).1,(a.positiveSymmetric _ hay).2.1⟩)
      ((a.positiveSymmetric _ ha).2.2)
  have heq := hnb.mono (fun y hy => c.interior_pullback_equal d x hy.1 hy.2.1 hy.2.2)
  have hg := spatialEnergy_congr (heq.mono fun _ h => h.1) (heq.mono fun _ h => h.2)
  have hk := coordinateMomentumNorm_congr (heq.mono fun _ h => h.1) (heq.mono fun _ h => h.2)
  have hc' := hcov c hc (hnb.mono fun _ h => h.2.1)
  have hd' := hcov d hd (hnb.mono fun _ h => h.2.2)
  rw [hc'.1,hd'.1] at hg
  rw [hc'.2,hd'.2] at hk
  exact ⟨by simpa only [ConstraintChart.energy,Function.comp_apply,hux] using hg,
    by simpa only [ConstraintChart.momentumNorm,Function.comp_apply,hux] using hk⟩
end CKSIntrinsicConstraints

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold
open scoped ContDiff Topology
namespace CKSIntrinsicConstraints
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {g K : InnerField I (M := M)} {x : M}
lemma ConstraintChart.compare (c d : ConstraintChart g K x) :
    c.energy = d.energy ∧ c.momentumNorm = d.momentumNorm := by
  let : NeBot (𝓝[I.interior M] x) :=
    mem_closure_iff_nhdsWithin_neBot.mp (CKSIntrinsicTopology.dense_interior I x)
  have heq : ∀ᶠ y in 𝓝[I.interior M] x,
      spatialEnergy c.metric c.tensor (c.coordinate y) = spatialEnergy d.metric d.tensor (d.coordinate y) ∧
      coordinateMomentumNorm c.metric c.tensor (c.coordinate y) =
        coordinateMomentumNorm d.metric d.tensor (d.coordinate y) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (c.isOpen.mem_nhds c.mem),
      nhdsWithin_le_nhds (d.isOpen.mem_nhds d.mem)] with y hy hcy hdy
    exact (c.at y hcy).compare_interior (d.at y hdy) hy
  constructor
  · exact tendsto_nhds_unique_of_eventuallyEq
      (((c.continuous_energy x c.mem).continuousAt (c.isOpen.mem_nhds c.mem)).mono_left nhdsWithin_le_nhds)
      (((d.continuous_energy x d.mem).continuousAt (d.isOpen.mem_nhds d.mem)).mono_left nhdsWithin_le_nhds)
      (heq.mono fun _ h => h.1)
  · exact tendsto_nhds_unique_of_eventuallyEq
      (((c.continuous_momentumNorm x c.mem).continuousAt (c.isOpen.mem_nhds c.mem)).mono_left nhdsWithin_le_nhds)
      (((d.continuous_momentumNorm x d.mem).continuousAt (d.isOpen.mem_nhds d.mem)).mono_left nhdsWithin_le_nhds)
      (heq.mono fun _ h => h.2)

end CKSIntrinsicConstraints

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSourceExterior
noncomputable section
open Set Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold CKSGeometricCuts
open CKSIntrinsicConstraints (ConstraintChart chart_exists_of_DECAt)
open scoped ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

lemma tensor_properties_from_representation
    (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (f : N → E) (A B : SpatialTensor) {x : N}
    (he : g.inner x = endInner I3 f A x ∧ K x = endInner I3 f B x) :
    (∀ v w, A (f x) v w = A (f x) w v) ∧
    (∀ v : E, v ≠ 0 → 0 < A (f x) v v) ∧
    (∀ v w, B (f x) v w = B (f x) w v) := by
  have hfull := endInner_fullRank g f A he.1
  refine ⟨?_,?_,?_⟩
  · intro v w
    obtain ⟨a,ha⟩ := hfull.2 v
    obtain ⟨b,hb⟩ := hfull.2 w
    have hs := g.symm x a b
    rw [he.1] at hs
    change A (f x) (mfderiv I3 𝓘(ℝ,E) f x a) (mfderiv I3 𝓘(ℝ,E) f x b) =
      A (f x) (mfderiv I3 𝓘(ℝ,E) f x b) (mfderiv I3 𝓘(ℝ,E) f x a) at hs
    simpa only [ha,hb] using hs
  · intro v hv
    obtain ⟨a,ha⟩ := hfull.2 v
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha
      change (0 : E) = v at ha
      exact hv ha.symm
    have hp := g.pos x a ha0
    rw [he.1] at hp
    change 0 < A (f x) (mfderiv I3 𝓘(ℝ,E) f x a) (mfderiv I3 𝓘(ℝ,E) f x a) at hp
    simpa only [ha] using hp
  · intro v w
    obtain ⟨a,ha⟩ := hfull.2 v
    obtain ⟨b,hb⟩ := hfull.2 w
    have hs := hKsym x a b
    rw [he.2] at hs
    change B (f x) (mfderiv I3 𝓘(ℝ,E) f x a) (mfderiv I3 𝓘(ℝ,E) f x b) =
      B (f x) (mfderiv I3 𝓘(ℝ,E) f x b) (mfderiv I3 𝓘(ℝ,E) f x a) at hs
    simpa only [ha,hb] using hs

lemma perturbation_symmetric_of_source {A : SpatialTensor} {y : E}
    (h : ∀ v w, sourceSpatial A y v w = sourceSpatial A y w v) :
    ∀ v w, A y v w = A y w v := by
  intro v w
  have hh : hyperbolicField y v w = hyperbolicField y w v := by
    rw [hyperbolicField_apply,hyperbolicField_apply]
    simp only [hyperbolicMetric,real_inner_comm v w]
    ring
  have hs := h v w
  change hyperbolicField y v w + A y v w = hyperbolicField y w v + A y w v at hs
  rw [hh] at hs
  exact add_left_cancel hs

lemma CKSData.source_geometry
    (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (hDEC : PhysicalDEC I3 g.inner K) (d : CKSData g K) :
    (∀ y, d.chart.radius < ‖y‖ → ∀ v w,
      d.metricPerturbation y v w = d.metricPerturbation y w v) ∧
    (∀ y, d.chart.radius < ‖y‖ → ∀ v w,
      d.tensorPerturbation y v w = d.tensorPerturbation y w v) ∧
    (∀ y, d.chart.radius < ‖y‖ → ∀ v : E, v ≠ 0 →
      0 < sourceSpatial d.metricPerturbation y v v) ∧
    (∀ y, d.chart.radius < ‖y‖ →
      spatialDEC (sourceSpatial d.metricPerturbation) (sourceSpatial d.tensorPerturbation) y) := by
  have hg (x : N) (hx : x ∈ d.chart.domain) :=
    tensor_properties_from_representation g K hKsym d.chart.coordinate
      (sourceSpatial d.metricPerturbation) (sourceSpatial d.tensorPerturbation) (d.represents x hx)
  have hy (y : E) (h : d.chart.radius < ‖y‖) := hg _ (d.chart.right_inverse y h).1
  have he (y : E) (h : d.chart.radius < ‖y‖) := (d.chart.right_inverse y h).2
  refine ⟨?_,?_,?_,?_⟩
  · intro y h
    apply perturbation_symmetric_of_source
    simpa only [he y h] using (hy y h).1
  · intro y h
    apply perturbation_symmetric_of_source
    simpa only [he y h] using (hy y h).2.2
  · intro y h
    simpa only [he y h] using (hy y h).2.1
  · intro y h
    let x := d.chart.inverse y
    have hx : x ∈ d.chart.domain := (d.chart.right_inverse y h).1
    let c : ConstraintChart g.inner K x := {
      domain := d.chart.domain
      coordinate := d.chart.coordinate
      metric := sourceSpatial d.metricPerturbation
      tensor := sourceSpatial d.tensorPerturbation
      isOpen := d.chart.isOpen
      mem := hx
      smooth := d.chart.smooth
      fullRank := fun z hz => endInner_fullRank g d.chart.coordinate _ (d.represents z hz).1
      coefficientSmooth := fun z hz =>
        ⟨sourceSpatial_smooth (d.metric_smooth _ (d.chart.mapsTo z hz)),
         sourceSpatial_smooth (d.tensor_smooth _ (d.chart.mapsTo z hz))⟩
      positiveSymmetric := hg
      represents := d.represents }
    obtain ⟨c₀,hc₀⟩ := chart_exists_of_DECAt (hDEC x)
    have heq := c₀.compare c
    rw [heq.1,heq.2] at hc₀
    change spatialDEC (sourceSpatial d.metricPerturbation) (sourceSpatial d.tensorPerturbation)
      (d.chart.coordinate x) at hc₀
    simpa only [x,he y h] using hc₀
end
end CKSSourceExterior

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSourceExterior
noncomputable section
open Set Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold CKSGeometricCuts
open CKSSphericalHarmonics (SmoothSphere)
open scoped ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

lemma CKSData.balanced_in_chart
    (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N)) (d : CKSData g K)
    (ht : ‖(bondiCharge d.massAspect).2‖ < (bondiCharge d.massAspect).1)
    (c : CoordinateEnd (N := N)) (hdom : c.domain ⊆ d.chart.domain)
    (hcoord : c.coordinate = (hyperbolicHomeomorph (bondiCharge d.massAspect).1
      (bondiCharge d.massAspect).2 ht).symm ∘ d.chart.coordinate) :
    ∃ d' : CKSData g K, d'.chart = c ∧
      d'.massAspect = aspectPullback (bondiCharge d.massAspect).1 (bondiCharge d.massAspect).2 ht d.massAspect ∧
      bondiCharge d'.massAspect = (mass (bondiCharge d.massAspect).1 (bondiCharge d.massAspect).2,0) := by
  let e := (bondiCharge d.massAspect).1
  let p := (bondiCharge d.massAspect).2
  let H := hyperbolicHomeomorph e p ht
  let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) d.metricPerturbation
  let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) d.tensorPerturbation
  have hfar (y : E) (hy : c.radius < ‖y‖) : d.chart.radius < ‖H y‖ := by
    have hx := (c.right_inverse y hy).1
    have hr := (c.right_inverse y hy).2
    have he : d.chart.coordinate (c.inverse y) = H y := by
      rw [hcoord] at hr
      change H.symm (d.chart.coordinate (c.inverse y)) = y at hr
      simpa only [H.apply_symm_apply] using congrArg H hr
    rw [← he]
    exact d.chart.mapsTo _ (hdom hx)
  have hAs (y : E) (hy : c.radius < ‖y‖) : ContDiffAt ℝ ∞ A' y :=
    spatialTensorPullback_smooth (hyperbolicMap_smooth e (mass e p) p).contDiffAt
      (d.metric_smooth _ (hfar y hy))
  have hBs (y : E) (hy : c.radius < ‖y‖) : ContDiffAt ℝ ∞ B' y :=
    spatialTensorPullback_smooth (hyperbolicMap_smooth e (mass e p) p).contDiffAt
      (d.tensor_smooth _ (hfar y hy))
  obtain ⟨patches,hcover,hreal,hrep⟩ := boosted_cks_patches ht d.metricPerturbation
    d.tensorPerturbation d.patches d.covers d.realizes d.aspect_eq
  obtain ⟨hM',hcharge,_,_⟩ := balanced_charge_and_heat d.aspect_smooth ht
  let d' : CKSData g K := {
    chart := c
    metricPerturbation := A'
    tensorPerturbation := B'
    metric_smooth := hAs
    tensor_smooth := hBs
    represents := by
      intro x hx
      have hsx := d.chart.smooth.contMDiffAt (d.chart.isOpen.mem_nhds (hdom hx))
      rw [hcoord]
      exact ⟨(d.represents x (hdom hx)).1.trans
          (endInner_balanced ht d.chart.coordinate d.metricPerturbation hsx).symm,
        (d.represents x (hdom hx)).2.trans
          (endInner_balanced ht d.chart.coordinate d.tensorPerturbation hsx).symm⟩
    massAspect := aspectPullback e p ht d.massAspect
    aspect_smooth := hM'
    patches := patches
    covers := hcover
    realizes := hreal
    aspect_eq := hrep }
  exact ⟨d',rfl,rfl,hcharge⟩
end
end CKSSourceExterior

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff Topology ENNReal
namespace CKSFullCutArea
open CKSGeometricCuts (OuterDomain)
open CKSBoundarySurface
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  [SecondCountableTopology N]

theorem area_finite (g : SmoothMetric (N := N)) (D : OuterDomain N) : area g D < ⊤ := by
  let : MeasurableSpace (Surface D) := borel (Surface D)
  let : BorelSpace (Surface D) := ⟨rfl⟩
  exact isCompact_univ.measure_lt_top

theorem minEnclosingArea_finite [ConnectedSpace N]
    (g : SmoothMetric (N := N)) (hS : IsCompact (I3.boundary N)) : minEnclosingArea g < ⊤ := by
  let D := CKSGeometricCuts.identityOuterDomain hS
  exact (iInf_le (area g) D).trans_lt (area_finite g D)

end CKSFullCutArea

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSourceExterior
noncomputable section
open Set Manifold Bundle MeasureTheory CKSGeometricCuts CKSMetricGluing
open scoped ContDiff
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N]
  [@IsManifold ℝ _ E3 _ _ H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 CKSGeometricCuts.halfSpaceDimension_neZero) I3 ∞ N _ _]
  [SecondCountableTopology N]

lemma minimumEnclosingArea_eq_toReal (g : SmoothMetric I3 (M := N)) :
    minimumEnclosingArea g = (CKSFullCutArea.minEnclosingArea g).toReal := by
  exact (ENNReal.toReal_iInf (fun D => ne_of_lt (CKSFullCutArea.area_finite g D))).symm

end
end CKSSourceExterior

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSourceExterior
noncomputable section
open Set Manifold Bundle Filter CKSLorentz CKSMetricGluing CKSSpatialManifold CKSGeometricCuts
open CKSADM (Symbol)
open scoped ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  [T2Space N] [SecondCountableTopology N] [ConnectedSpace N]
attribute [local instance] manifold_regular

theorem area_controlled_end_replacement
    (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N))
    (hK : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (_hOrient : Orientable (N := N))
    (hScompact : IsCompact (I3.boundary N)) (_hSnonempty : (I3.boundary N).Nonempty)
    (hcomplete : CKSReplacementCompleteness.IsComplete I3 g.toContinuousRiemannianMetric)
    (hDEC : PhysicalDEC I3 g.inner K)
    (d : CKSData g K)
    (ht : ‖(bondiCharge d.massAspect).2‖ < (bondiCharge d.massAspect).1) :
    ∃ (d' : CKSData g K) (R₀ : ℝ) (ε : ℝ → ℝ),
      bondiCharge d'.massAspect =
        (Real.sqrt ((bondiCharge d.massAspect).1^2 - ‖(bondiCharge d.massAspect).2‖^2),0) ∧
      d'.chart.radius < R₀ ∧ 12 ≤ R₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      CKSFullCutArea.minEnclosingArea g < ⊤ ∧
      ∀ R ≥ R₀, (0 ≤ ε R ∧ ε R < 1) ∧
        ∃ (gR : SmoothMetric I3 (M := N)) (kR : InnerField I3 (M := N))
          (G k : SpatialTensor) (η : ℝ),
          ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 kR) ∧
          (∀ x v w, kR x v w = kR x w v) ∧
          (∀ x, x ∉ d'.chart.domain ∨ ‖d'.chart.coordinate x‖ ≤ R →
            gR.inner x = g.inner x ∧ kR x = K x) ∧
          PhysicalDEC I3 gR.inner kR ∧
          (∀ x v, (1-ε R) * g.inner x v v ≤ gR.inner x v v) ∧
          CKSReplacementCompleteness.IsComplete I3 gR.toContinuousRiemannianMetric ∧
          constraintsIntegrable gR kR ∧
          (∀ x ∈ d'.chart.domain,
            gR.inner x = endInner I3 d'.chart.coordinate G x ∧
            kR x = endInner I3 d'.chart.coordinate k x) ∧
          (∀ i j : Fin 3, Symbol 1
            (fun x => spatialCartesian G x i j - (if i=j then 1 else 0))) ∧
          (∀ x : E, 2*R^2 < ‖x‖ → k x = 0) ∧
          Tendsto (spatialADMEnergy G) atTop
            (𝓝 (Real.sqrt ((bondiCharge d.massAspect).1^2 - ‖(bondiCharge d.massAspect).2‖^2) + η)) ∧
          Tendsto (spatialADMMomentum G k) atTop (𝓝 0) ∧
          0 ≤ η ∧ η ≤ 2 * R ^ (-(1/2 : ℝ)) ∧
          CKSFullCutArea.minEnclosingArea gR < ⊤ ∧
          (1-ε R) * minimumEnclosingArea g ≤ minimumEnclosingArea gR ∧
          ∀ D : OuterDomain N,
            CKSFullCutArea.area g D < ⊤ ∧ CKSFullCutArea.area gR D < ⊤ ∧
            (1-ε R) * cutArea g D ≤ cutArea gR D
 := by
  classical
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  obtain ⟨hA,hB,hpos,hdDEC⟩ := CKSData.source_geometry g K hKsym hDEC d
  obtain ⟨T,R₀,ε,G,k,hT,hTR,hR₀,hε,hVo,hfs,his,hleft,hright,hclosed,hcompact,hout⟩ :=
    original_CKS_replacement_intrinsic_chart_package d.aspect_smooth ht
      d.metricPerturbation d.tensorPerturbation d.patches d.covers d.aspect_eq d.realizes
      d.chart.radius_pos d.metric_smooth d.tensor_smooth hA hB hpos hdDEC
      g K hK hKsym hDEC hcomplete d.chart.coordinate d.chart.isOpen d.chart.smooth
      d.chart.closed_far_side d.chart.inverse d.chart.inverse_smooth
      d.chart.left_inverse d.chart.right_inverse d.chart.compact_inner_side d.represents
      (C := ∅) isCompact_empty
  let H := hyperbolicHomeomorph (bondiCharge d.massAspect).1 (bondiCharge d.massAspect).2 ht
  let f' := H.symm ∘ d.chart.coordinate
  let c : CoordinateEnd (N := N) := {
    radius := T
    radius_pos := hT
    domain := {x | x ∈ d.chart.domain ∧ T < ‖f' x‖}
    isOpen := hVo
    coordinate := f'
    inverse := d.chart.inverse ∘ H
    smooth := hfs
    inverse_smooth := his
    mapsTo := fun x hx => hx.2
    left_inverse := hleft
    right_inverse := hright
    closed_far_side := hclosed
    compact_inner_side := fun r hr => hcompact r hr.le }
  obtain ⟨d',hd',hM',hcharge⟩ := CKSData.balanced_in_chart g K d ht c
    (fun x hx => hx.1) rfl
  have hgfinite := CKSFullCutArea.minEnclosingArea_finite g hScompact
  refine ⟨d',R₀,ε,hcharge,?_,hR₀,hε,hgfinite,?_⟩
  · rw [hd']
    exact hTR
  · intro R hR
    obtain ⟨heps,gR,kR,hks,hksym,hgDEC,hgcomplete,hC,hold,hlower,harea,hrep,
      hkzero,hAF,hE,hP,hη0,hη1,hendint,hmomzero,hint,hindarea,hcutarea⟩ := hout R hR
    have hc : 0 ≤ 1-ε R := sub_nonneg.mpr heps.2.le
    have hgRfinite := CKSFullCutArea.minEnclosingArea_finite gR hScompact
    refine ⟨heps,gR,kR,G R,k R,CKSBending.paddingCharge R,hks,hksym,?_,hgDEC,hlower,
      hgcomplete,hint,?_,hAF,hkzero,hE,hP,hη0,?_,hgRfinite,?_,?_⟩
    · simpa only [hd'] using hold
    · intro x hx
      rw [hd'] at hx ⊢
      exact hrep x hx
    · have hRpos : 0 < R := lt_of_lt_of_le (by linarith : 0 < R₀) hR
      rw [Real.rpow_neg hRpos.le,← Real.sqrt_eq_rpow]
      simpa only [div_eq_mul_inv] using hη1
    · have h := ENNReal.toReal_mono (ne_of_lt hgRfinite) hindarea
      simpa only [minimumEnclosingArea_eq_toReal,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] using h
    · intro D
      obtain ⟨hD,hDR,hDa⟩ := hcutarea D
      refine ⟨hD,hDR,?_⟩
      have h := ENNReal.toReal_mono (ne_of_lt hDR) hDa
      simpa only [cutArea,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] using h

end
end CKSSourceExterior

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CKSSourceExterior.area_controlled_end_replacement.{u_1} := @OAI.CKSSourceExterior.area_controlled_end_replacement.{u_1}
