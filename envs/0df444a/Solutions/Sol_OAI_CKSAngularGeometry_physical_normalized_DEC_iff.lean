-- Prove2me | solution 1 for OAI.CKSAngularGeometry.physical_normalized_DEC_iff
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:11:54.169418+00:00
-- url     : https://prove2.me/submissions/e07ef90b-ddb0-4b61-a766-e13545180182

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

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

lemma D_inv (e : E) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) :
    D e (fun y => (f y)⁻¹) x = -(D e f x) / (f x) ^ 2 := by
  unfold D
  change fderiv ℝ ((fun z : ℝ => z⁻¹) ∘ f) x e = _
  rw [((hasDerivAt_inv h0).comp_hasFDerivAt x hf.hasFDerivAt).fderiv]
  simp
  ring

lemma D_div (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (h0 : g x ≠ 0) :
    D e (fun y => f y / g y) x =
      (D e f x * g x - f x * D e g x) / (g x) ^ 2 := by
  simp only [div_eq_mul_inv]
  rw [D_mul (g := fun y => (g y)⁻¹) e hf (hg.inv h0), D_inv e hg h0]
  field_simp
  ring

lemma diffAt_div {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (h0 : g x ≠ 0) :
    DifferentiableAt ℝ (fun y => f y / g y) x := by
  have hgi : DifferentiableAt ℝ (fun y => (g y)⁻¹) x := hg.inv h0
  simpa only [div_eq_mul_inv] using
    (show DifferentiableAt ℝ (fun y => f y * (g y)⁻¹) x from hf.fun_mul hgi)

lemma D_pow (e : E) {f : E → ℝ} {x : E} (n : ℕ)
    (hf : DifferentiableAt ℝ f x) :
    D e (fun y => f y ^ n) x = n * f x ^ (n - 1) * D e f x := by
  unfold D
  rw [fderiv_fun_pow n hf]
  simp

lemma D_inv_sq (e : E) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) :
    D e (fun y => 1 / f y ^ 2) x = -2 * D e f x / f x ^ 3 := by
  rw [D_div (g := fun y => f y ^ 2) e (differentiableAt_const 1) (hf.pow 2) (pow_ne_zero _ h0),
    D_const, D_pow e 2 hf]
  norm_num
  field_simp

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
open scoped BigOperators Matrix

abbrev A := Fin 2

structure ConnectionData where
  B : A → ℝ
  rotation : ℝ
  chi11 : ℝ
  chi12 : ℝ
  chi22 : ℝ
  leaf : A → ℝ

def chi (c : ConnectionData) : Matrix A A ℝ :=
  !![c.chi11,c.chi12;c.chi12,c.chi22]

def leafConnection (c : ConnectionData) (a : A) : Matrix A A ℝ :=
  !![0,c.leaf a;-c.leaf a,0]

def connection (c : ConnectionData) : I → Matrix I I ℝ :=
  ![!![0,c.B 0,c.B 1; -c.B 0,0,c.rotation; -c.B 1,-c.rotation,0],
    !![0,c.chi11,c.chi12; -c.chi11,0,c.leaf 0; -c.chi12,-c.leaf 0,0],
    !![0,c.chi12,c.chi22; -c.chi12,0,c.leaf 1; -c.chi22,-c.leaf 1,0]]

lemma connection_metric (c : ConnectionData) (i j k : I) :
    connection c i j k = -connection c i k j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [connection]

lemma connection_normal (c : ConnectionData) (a b : A) :
    connection c a.succ 0 b.succ = chi c a b := by
  fin_cases a <;> fin_cases b <;> rfl

def curvature (c : ConnectionData) (dc : I → ConnectionData) (i j k l : I) : ℝ :=
  connection (dc i) j k l-connection (dc j) i k l+
  ∑ m, (connection c j k m*connection c i m l-
    connection c i k m*connection c j m l-
    (connection c i j m-connection c j i m)*connection c m k l)

def scalarCurvature (c : ConnectionData) (dc : I → ConnectionData) : ℝ :=
  ∑ i, ∑ j, curvature c dc i j j i

def leafCurvature (c : ConnectionData) (dc : I → ConnectionData) (a b d e : A) : ℝ :=
  leafConnection (dc a.succ) b d e-leafConnection (dc b.succ) a d e+
  ∑ m, (leafConnection c b d m*leafConnection c a m e-
    leafConnection c a d m*leafConnection c b m e-
    (leafConnection c a b m-leafConnection c b a m)*leafConnection c m d e)

def leafScalar (c : ConnectionData) (dc : I → ConnectionData) : ℝ :=
  ∑ a, ∑ b, leafCurvature c dc a b b a

def mean (c : ConnectionData) : ℝ := c.chi11+c.chi22

def normalMean (dc : I → ConnectionData) : ℝ := (dc 0).chi11+(dc 0).chi22

def chiNormSq (c : ConnectionData) : ℝ := c.chi11^2+2*c.chi12^2+c.chi22^2

def accelNormSq (c : ConnectionData) : ℝ := (c.B 0)^2+(c.B 1)^2

def accelDiv (c : ConnectionData) (dc : I → ConnectionData) : ℝ :=
  ∑ a, ((dc a.succ).B a+∑ b, leafConnection c a b a*c.B b)

lemma leafScalar_formula (c : ConnectionData) (dc : I → ConnectionData) :
    leafScalar c dc = 2*((dc 2).leaf 0-(dc 1).leaf 1-(c.leaf 0)^2-(c.leaf 1)^2) := by
  simp [leafScalar,leafCurvature,leafConnection,Fin.sum_univ_succ]
  ring

lemma scalarCurvature_formula (c : ConnectionData) (dc : I → ConnectionData) :
    scalarCurvature c dc = leafScalar c dc-2*normalMean dc-(mean c)^2-
      chiNormSq c+2*accelDiv c dc-2*accelNormSq c := by
  rw [leafScalar_formula]
  simp [scalarCurvature,curvature,connection,mean,normalMean,chiNormSq,accelDiv,
    accelNormSq,leafConnection,Fin.sum_univ_succ]
  ring

end
end CKSFrame

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

def extractConnection (g : Coefficients) : ConnectionData where
  B := ![g 0 0 1,g 0 0 2]
  rotation := g 0 1 2
  chi11 := g 1 0 1
  chi12 := g 1 0 2
  chi22 := g 2 0 2
  leaf := ![g 1 1 2,g 2 1 2]

lemma extractConnection_complete {g : Coefficients} (hg : ∀ i j k, g i j k = -g i k j)
    (hχ : g 2 0 1 = g 1 0 2) : connection (extractConnection g) = g := by
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [connection,extractConnection] <;>
    first | rfl | (have h := hg 0 0 0; linarith) | (have h := hg 0 1 0; linarith) |
      (have h := hg 0 2 0; linarith) | (have h := hg 0 1 1; linarith) |
      (have h := hg 0 2 1; linarith) | (have h := hg 0 2 2; linarith) |
      (have h := hg 1 0 0; linarith) | (have h := hg 1 1 0; linarith) |
      (have h := hg 1 1 1; linarith) | (have h := hg 1 2 0; linarith) |
      (have h := hg 1 2 1; linarith) | (have h := hg 1 2 2; linarith) |
      (have h := hg 2 0 0; linarith) | (have h := hg 2 1 0; linarith) |
      (have h := hg 2 1 1; linarith) | (have h := hg 2 2 0; linarith) |
      (have h := hg 2 2 1; linarith) | (have h := hg 2 2 2; linarith)

end
end CKSFrame

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSFrame
noncomputable section
open scoped BigOperators Matrix

structure TensorData where
  L : ℝ
  eta : A → ℝ
  p : ℝ
  tau11 : ℝ
  tau12 : ℝ

def tensor (t : TensorData) : Matrix I I ℝ :=
  !![t.L,t.eta 0,t.eta 1;
    t.eta 0,t.p/2+t.tau11,t.tau12;
    t.eta 1,t.tau12,t.p/2-t.tau11]

def tangential (t : TensorData) : Matrix A A ℝ :=
  !![t.p/2+t.tau11,t.tau12;t.tau12,t.p/2-t.tau11]

def tau (t : TensorData) : Matrix A A ℝ :=
  !![t.tau11,t.tau12;t.tau12,-t.tau11]

def covariantTensor (c : ConnectionData) (t : TensorData) (dt : I → TensorData)
    (i j k : I) : ℝ := tensor (dt i) j k-
  ∑ a, (connection c i j a*tensor t a k+connection c i k a*tensor t j a)

def momentum (c : ConnectionData) (t : TensorData) (dt : I → TensorData) (j : I) : ℝ :=
  (∑ i, covariantTensor c t dt i i j)-∑ i, tensor (dt j) i i

def energy (c : ConnectionData) (dc : I → ConnectionData) (t : TensorData) : ℝ :=
  (scalarCurvature c dc+(∑ i, tensor t i i)^2-∑ i, ∑ j, (tensor t i j)^2)/2

def shearNormSq (c : ConnectionData) : ℝ :=
  (c.chi11-mean c/2)^2+2*c.chi12^2+(c.chi22-mean c/2)^2

def tauNormSq (t : TensorData) : ℝ := 2*t.tau11^2+2*t.tau12^2

def etaNormSq (t : TensorData) : ℝ := (t.eta 0)^2+(t.eta 1)^2

def shearTau (c : ConnectionData) (t : TensorData) : ℝ :=
  (c.chi11-c.chi22)*t.tau11+2*c.chi12*t.tau12

def etaAcceleration (c : ConnectionData) (t : TensorData) : ℝ :=
  ∑ a, t.eta a*c.B a

def etaDiv (c : ConnectionData) (t : TensorData) (dt : I → TensorData) : ℝ :=
  ∑ a, ((dt a.succ).eta a-∑ b, leafConnection c a a b*t.eta b)

def tauDiv (c : ConnectionData) (t : TensorData) (dt : I → TensorData) (a : A) : ℝ :=
  ∑ b, (tau (dt b.succ) b a-∑ e,
    (leafConnection c b b e*tau t e a+leafConnection c b a e*tau t b e))

def normalLieEta (c : ConnectionData) (t : TensorData) (dt : I → TensorData) (a : A) : ℝ :=
  (dt 0).eta a-∑ b, (connection c 0 a.succ b.succ-chi c a b)*t.eta b

def accelTensor (c : ConnectionData) (t : TensorData) (a : A) : ℝ :=
  t.L*c.B a-∑ b, tangential t b a*c.B b

lemma tensor_trace (t : TensorData) : (∑ i, tensor t i i) = t.L+t.p := by
  simp [tensor,Fin.sum_univ_succ]

lemma energy_decomposition (c : ConnectionData) (dc : I → ConnectionData) (t : TensorData) :
    energy c dc t = leafScalar c dc/2-normalMean dc+accelDiv c dc-accelNormSq c-
      3/4*(mean c)^2-shearNormSq c/2+t.L*t.p+t.p^2/4-tauNormSq t/2-etaNormSq t := by
  unfold energy
  rw [scalarCurvature_formula,tensor_trace]
  simp [tensor,Fin.sum_univ_succ,chiNormSq,shearNormSq,mean,tauNormSq,etaNormSq]
  ring

lemma normal_momentum_decomposition (c : ConnectionData) (t : TensorData) (dt : I → TensorData) :
    momentum c t dt 0 = mean c*(t.L-t.p/2)-shearTau c t-(dt 0).p+
      etaDiv c t dt-2*etaAcceleration c t := by
  simp [momentum,covariantTensor,tensor,connection,mean,shearTau,etaDiv,etaAcceleration,
    leafConnection,Fin.sum_univ_succ]
  ring

lemma tangential_momentum_decomposition (c : ConnectionData) (t : TensorData) (dt : I → TensorData)
    (a : A) : momentum c t dt a.succ = normalLieEta c t dt a+mean c*t.eta a+
      tauDiv c t dt a-((dt a.succ).L+(dt a.succ).p/2)+accelTensor c t a := by
  fin_cases a <;>
    simp [momentum,covariantTensor,tensor,connection,mean,normalLieEta,tauDiv,chi,tau,
      accelTensor,tangential,leafConnection,Fin.sum_univ_succ] <;> ring

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

lemma foliationTensor_normal {U L : ℝ} (hU : U ≠ 0) (η : Point) {kT : Mat}
    (hk : kT.IsHermitian) (s : Point) :
    star (foliationNormal U s) ⬝ᵥ (foliationTensor U L η kT s *ᵥ foliationNormal U s)=L := by
  simp only [foliationTensor,foliationNormal,metricBlock,Matrix.of_apply,mulVec,dotProduct,Fin.sum_univ_three,
    Fin.sum_univ_two,star_trivial,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
    Matrix.tail_cons]
  rw [hermitian_real_symmetry hk 0 1]
  field_simp
  ring

lemma foliationTensor_mixed {U L : ℝ} (hU : U ≠ 0) (η : Point) (kT : Mat) (s : Point) (a : Fin 2) :
    ∑ j : Fin 3, foliationTensor U L η kT s a.succ j*foliationNormal U s j=η a := by
  fin_cases a <;> norm_num [Fin.succ,foliationTensor,foliationNormal,metricBlock,Matrix.of_apply,Fin.sum_univ_three,
    Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.head_fin_const,Matrix.tail_cons,Matrix.cons_val_fin_one] <;>
    field_simp <;> ring

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
open Matrix CKSCalculus
open scoped BigOperators
 def foliationMetricDerivative (U : ℝ) (γ : Mat) (s : Point)
    (dU : ℝ) (dγ : Mat) (ds : Point) : AmbientMat :=
  metricBlock (-2*dU/U^3+∑ a, ∑ b,
    (dγ a b*s a*s b+γ a b*ds a*s b+γ a b*s a*ds b))
    (fun a => ∑ b, (dγ a b*s b+γ a b*ds b)) dγ

 def foliationNormalDerivative (U : ℝ) (s : Point) (dU : ℝ) (ds : Point) : PhysicalPoint :=
  ![dU,-dU*s 0-U*ds 0,-dU*s 1-U*ds 1]

lemma foliationMetric_derivative (e : PhysicalPoint) {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : U x ≠ 0) :
    (fun i j => D e (fun y => foliationMetric (U y) (γ y) (s y) i j) x) =
      foliationMetricDerivative (U x) (γ x) (s x) (D e U x)
        (fun i j => D e (fun y => γ y i j) x) (fun i => D e (fun y => s y i) x) := by
  have hγc (i j) : DifferentiableAt ℝ (fun y => γ y i j) x := differentiableAt_pi.mp (differentiableAt_pi.mp hγ i) j
  have hsc (i) : DifferentiableAt ℝ (fun y => s y i) x := differentiableAt_pi.mp hs i
  have dsum (f : Fin 2 → PhysicalPoint → ℝ)
      (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
      D e (fun y => ∑ i, f i y) x = ∑ i, D e (f i) x := by
    simp only [D, fderiv_fun_sum (fun i _ => hf i), _root_.sum_apply]
  have hUi2 : DifferentiableAt ℝ (fun y => 1/(U y)^2) x :=
    CKSCalculus.diffAt_div (differentiableAt_const 1) (hU.pow 2) (pow_ne_zero _ h0)
  have ht (a b : Fin 2) : DifferentiableAt ℝ (fun y => γ y a b*s y a*s y b) x :=
    ((hγc a b).fun_mul (hsc a)).fun_mul (hsc b)
  have hsum (a : Fin 2) : DifferentiableAt ℝ (fun y => ∑ b, γ y a b*s y a*s y b) x :=
    DifferentiableAt.fun_sum (fun b _ => ht a b)
  have hrr : D e (fun y => 1/(U y)^2+∑ a, ∑ b, γ y a b*s y a*s y b) x =
      -2*D e U x/(U x)^3+∑ a, ∑ b,
        (D e (fun y => γ y a b) x*s x a*s x b+
          γ x a b*D e (fun y => s y a) x*s x b+
          γ x a b*s x a*D e (fun y => s y b) x) := by
    rw [D_add e hUi2 (DifferentiableAt.fun_sum (fun a _ => hsum a)),
      D_inv_sq e hU h0, dsum _ hsum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [dsum _ (ht a)]
    apply Finset.sum_congr rfl
    intro b _
    rw [D_mul e ((hγc a b).fun_mul (hsc a)) (hsc b), D_mul e (hγc a b) (hsc a)]
    ring
  have hmixed (a : Fin 2) : D e (fun y => ∑ b, γ y a b*s y b) x =
      ∑ b, (D e (fun y => γ y a b) x*s x b + γ x a b*D e (fun y => s y b) x) := by
    rw [dsum _ (fun b => (hγc a b).fun_mul (hsc b))]
    apply Finset.sum_congr rfl
    intro b _
    rw [D_mul e (hγc a b) (hsc b)]
    ring
  ext i j
  fin_cases i <;> fin_cases j
  · exact hrr
  · exact hmixed 0
  · exact hmixed 1
  · exact hmixed 0
  · rfl
  · rfl
  · exact hmixed 1
  · rfl
  · rfl

lemma foliationNormal_derivative (e : PhysicalPoint) {U : PhysicalPoint → ℝ}
    {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hs : DifferentiableAt ℝ s x) :
    (fun i => D e (fun y => foliationNormal (U y) (s y) i) x)=
      foliationNormalDerivative (U x) (s x) (D e U x) (fun i => D e (fun y => s y i) x) := by
  have hsc (i) : DifferentiableAt ℝ (fun y => s y i) x := differentiableAt_pi.mp hs i
  ext i
  fin_cases i <;> dsimp [foliationNormal,foliationNormalDerivative]
  all_goals rw [D_mul (f := fun y => -U y) e hU.neg (hsc _)]
  all_goals simp only [D, fderiv_fun_neg, _root_.neg_apply]
  all_goals ring

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
open scoped BigOperators

 def normalCovariantFirstJet (U : ℝ) (γ : Mat) (s : Point)
    (dU : Fin 3 → ℝ) (dγ : Fin 3 → Mat) (ds : Fin 3 → Point)
    (i k : Fin 3) : ℝ :=
  ∑ j, (foliationMetric U γ s j k*foliationNormalDerivative U s (dU i) (ds i) j+
    foliationNormal U s j * lowerKoszul
      (fun t => foliationMetricDerivative U γ s (dU t) (dγ t) (ds t)) i j k)

theorem foliation_chi_koszul {U : ℝ} (_hU : U ≠ 0) {γ : Mat} (hγ : γ.IsHermitian)
    (s : Point) (dU : Fin 3 → ℝ) (dγ : Fin 3 → Mat) (ds : Fin 3 → Point)
    (hdγ : ∀ i, (dγ i).IsHermitian) (a b : Fin 2) :
    normalCovariantFirstJet U γ s dU dγ ds a.succ b.succ =
      U/2 * (dγ 0 a b - ∑ c, (s c*dγ c.succ a b+
        γ c b*ds a.succ c+γ a c*ds b.succ c)) := by
  fin_cases a <;> fin_cases b <;>
    simp [normalCovariantFirstJet,lowerKoszul,foliationMetric,foliationMetricDerivative,
      foliationNormal,foliationNormalDerivative,metricBlock,Matrix.of_apply,
      Fin.sum_univ_three,Fin.sum_univ_two,
      hermitian_real_symmetry hγ 0 1,
      hermitian_real_symmetry (hdγ 0) 0 1,
      hermitian_real_symmetry (hdγ 1) 0 1,
      hermitian_real_symmetry (hdγ 2) 0 1]
  all_goals field_simp [_hU]
  all_goals ring

theorem foliation_acceleration_koszul {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.IsHermitian)
    (s : Point) (dU : Fin 3 → ℝ) (dγ : Fin 3 → Mat) (ds : Fin 3 → Point)
    (hdγ : ∀ i, (dγ i).IsHermitian) (a : Fin 2) :
    (∑ i, foliationNormal U s i * normalCovariantFirstJet U γ s dU dγ ds i a.succ)=
      dU a.succ/U := by
  fin_cases a <;>
    simp [normalCovariantFirstJet,lowerKoszul,foliationMetric,foliationMetricDerivative,
      foliationNormal,foliationNormalDerivative,metricBlock,Matrix.of_apply,
      Fin.sum_univ_three,Fin.sum_univ_two,
      hermitian_real_symmetry hγ 0 1,
      hermitian_real_symmetry (hdγ 0) 0 1,
      hermitian_real_symmetry (hdγ 1) 0 1,
      hermitian_real_symmetry (hdγ 2) 0 1]
  all_goals field_simp [hU]
  all_goals ring

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
open scoped BigOperators Topology

 def coordinateNormalCovariant (G : PhysicalPoint → AmbientMat) (N : PhysicalPoint → PhysicalPoint)
    (x : PhysicalPoint) (i k : Fin 3) : ℝ :=
  ∑ j, (G x j k * D (CKSRealizedRound.basis i) (fun y => N y j) x +
    N x j * lowerKoszul (actualMetricFirstJet G x) i j k)

lemma normalCovariant_realization {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : U x ≠ 0) (i k : Fin 3) :
    coordinateNormalCovariant (fun y => foliationMetric (U y) (γ y) (s y))
      (fun y => foliationNormal (U y) (s y)) x i k =
    normalCovariantFirstJet (U x) (γ x) (s x)
      (fun p => D (CKSRealizedRound.basis p) U x)
      (fun p a b => D (CKSRealizedRound.basis p) (fun y => γ y a b) x)
      (fun p a => D (CKSRealizedRound.basis p) (fun y => s y a) x) i k := by
  have hg : actualMetricFirstJet (fun y => foliationMetric (U y) (γ y) (s y)) x =
      fun p => foliationMetricDerivative (U x) (γ x) (s x)
        (D (CKSRealizedRound.basis p) U x)
        (fun a b => D (CKSRealizedRound.basis p) (fun y => γ y a b) x)
        (fun a => D (CKSRealizedRound.basis p) (fun y => s y a) x) := by
    funext p
    exact foliationMetric_derivative _ hU hγ hs h0
  have hn (p j) := congrFun (foliationNormal_derivative (CKSRealizedRound.basis p) hU hs) j
  unfold coordinateNormalCovariant normalCovariantFirstJet
  rw [hg]
  simp_rw [← hn]

lemma derivative_matrix_hermitian {γ : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : ∀ᶠ y in 𝓝 x, (γ y).IsHermitian) (e : PhysicalPoint) :
    Matrix.IsHermitian (fun a b : Fin 2 => D e (fun y => γ y a b) x) := by
  ext a b
  change D e (fun y => γ y b a) x = D e (fun y => γ y a b) x
  apply D_congr
  filter_upwards [hγ] with y hy
  exact hermitian_real_symmetry hy a b

theorem physical_foliation_leaf_geometry {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    (∀ a b : Fin 2,
      coordinateNormalCovariant (fun y => foliationMetric (U y) (γ y) (s y))
        (fun y => foliationNormal (U y) (s y)) x a.succ b.succ =
      U x/2 * (D (CKSRealizedRound.basis 0) (fun y => γ y a b) x -
        ∑ c, (s x c*D (CKSRealizedRound.basis c.succ) (fun y => γ y a b) x +
          γ x c b*D (CKSRealizedRound.basis a.succ) (fun y => s y c) x +
          γ x a c*D (CKSRealizedRound.basis b.succ) (fun y => s y c) x))) ∧
    (∀ a : Fin 2,
      (∑ i, foliationNormal (U x) (s x) i *
        coordinateNormalCovariant (fun y => foliationMetric (U y) (γ y) (s y))
          (fun y => foliationNormal (U y) (s y)) x i a.succ) =
        D (CKSRealizedRound.basis a.succ) U x / U x) := by
  have hsym : ∀ᶠ y in 𝓝 x, (γ y).IsHermitian := hp.mono (fun _ h => h.isHermitian)
  have hsym0 : (γ x).IsHermitian := hsym.self_of_nhds
  constructor
  · intro a b
    rw [normalCovariant_realization hU hγ hs h0.ne']
    exact foliation_chi_koszul h0.ne' hsym0 _ _ _ _
      (fun p => derivative_matrix_hermitian hsym (CKSRealizedRound.basis p)) a b
  · intro a
    simp_rw [normalCovariant_realization hU hγ hs h0.ne']
    exact foliation_acceleration_koszul h0.ne' hsym0 _ _ _ _
      (fun p => derivative_matrix_hermitian hsym (CKSRealizedRound.basis p)) a

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

 def coordinateCovariantNormal (G : PhysicalPoint → AmbientMat)
    (N : PhysicalPoint → PhysicalPoint) (x : PhysicalPoint) (i k : Fin 3) : ℝ :=
  D (CKSRealizedRound.basis i) (fun y => N y k) x +
    ∑ j, coordinateChristoffel G x i j k * N x j

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

theorem coordinateNormalCovariant_is_LeviCivita {G : PhysicalPoint → AmbientMat}
    {N : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint} (hG : (G x).PosDef)
    (i k : Fin 3) :
    (∑ l, coordinateCovariantNormal G N x i l * G x l k) =
      coordinateNormalCovariant G N x i k := by
  simp only [coordinateCovariantNormal, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hs : (∑ j, ∑ l, coordinateChristoffel G x i j l * N x j * G x l k) =
      ∑ j, N x j * lowerKoszul (actualMetricFirstJet G x) i j k := by
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = N x j * ∑ l, coordinateChristoffel G x i j l * G x l k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [christoffel_lowered hG]
  rw [hs]
  simp only [coordinateNormalCovariant, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
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

lemma adaptedFrame_first (U : ℝ) (γ : Mat) (s : Point) :
    adaptedFrame U γ s 0=foliationNormal U s := rfl

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

 def frameConnectionField (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : CKSFrame.ConnectionData :=
  CKSFrame.extractConnection (frameCoefficient G E x)

 def connectionFieldDerivative (c : PhysicalPoint → CKSFrame.ConnectionData)
    (e x : PhysicalPoint) : CKSFrame.ConnectionData where
  B := fun a => D e (fun y => (c y).B a) x
  rotation := D e (fun y => (c y).rotation) x
  chi11 := D e (fun y => (c y).chi11) x
  chi12 := D e (fun y => (c y).chi12) x
  chi22 := D e (fun y => (c y).chi22) x
  leaf := fun a => D e (fun y => (c y).leaf a) x

lemma connectionFieldDerivative_exact (c : PhysicalPoint → CKSFrame.ConnectionData)
    (e x : PhysicalPoint) (i j k : Fin 3) :
    CKSFrame.connection (connectionFieldDerivative c e x) i j k =
      D e (fun y => CKSFrame.connection (c y) i j k) x := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [connectionFieldDerivative,CKSFrame.connection,D,fderiv_fun_neg]

 def ActualAdaptedAt (G : PhysicalPoint → AmbientMat) (E : LocalFrame) (x : PhysicalPoint) : Prop :=
  DifferentiableAt ℝ G x ∧ (∀ i, DifferentiableAt ℝ (E i) x) ∧ (G x).PosDef ∧
  (∀ᶠ y in 𝓝 x, (G y).IsHermitian) ∧
  (∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0) ∧
  (∀ a b : Fin 2, frameBracketCoefficient G E x a.succ b.succ 0=0)

lemma frame_connection_actual {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (h : ActualAdaptedAt G E x) :
    CKSFrame.connection (frameConnectionField G E x)=frameCoefficient G E x := by
  obtain ⟨hg,he,hp,hs,ho,ht⟩ := h
  apply CKSFrame.extractConnection_complete (frameCoefficient_metric hg he hp hs ho)
  have h1 := frameCoefficient_torsion (E := E) hs 1 2 0
  have hm1 := frameCoefficient_metric hg he hp hs ho 1 2 0
  have hm2 := frameCoefficient_metric hg he hp hs ho 2 1 0
  have hh := ht 0 1
  change frameBracketCoefficient G E x 1 2 0=0 at hh
  rw [hh] at h1
  linarith

lemma physical_curvature_representation {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (h : ∀ᶠ y in 𝓝 x, ActualAdaptedAt G E y)
    (i j k l : Fin 3) :
    actualFrameCurvature G E x i j k l = CKSFrame.curvature
      (frameConnectionField G E x)
      (fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x) i j k l := by
  have hx := h.self_of_nhds
  have hc := frame_connection_actual hx
  have hd (a b d f : Fin 3) :
      D (E a x) (fun y => frameCoefficient G E y b d f) x =
      D (E a x) (fun y => CKSFrame.connection (frameConnectionField G E y) b d f) x := by
    apply D_congr
    filter_upwards [h] with y hy
    rw [frame_connection_actual hy]
  unfold actualFrameCurvature CKSFrame.curvature
  simp_rw [connectionFieldDerivative_exact, hc]
  simp_rw [← hd]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [frameCoefficient_torsion hx.2.2.2.1]

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

lemma coordinateCovariantNormal_direction (G : PhysicalPoint → AmbientMat)
    (N : PhysicalPoint → PhysicalPoint) (x e : PhysicalPoint) (k : Fin 3) :
    covariantVector G e N x k = ∑ i, e i*coordinateCovariantNormal G N x i k := by
  rw [covariantVector,D_direction_expansion]
  simp only [coordinateCovariantNormal,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma normalCovariant_frame {G : PhysicalPoint → AmbientMat}
    (N : PhysicalPoint → PhysicalPoint) {x : PhysicalPoint} (hg : (G x).PosDef)
    (e v : PhysicalPoint) :
    metricPair (G x) (covariantVector G e N x) v =
      metricPair (coordinateNormalCovariant G N x) e v := by
  unfold metricPair
  simp_rw [coordinateCovariantNormal_direction]
  simp only [Finset.mul_sum,Finset.sum_mul]
  calc
    _ = ∑ i, ∑ j, (∑ l, coordinateCovariantNormal G N x i l*G x l j)*e i*v j := by
      simp only [Finset.sum_mul]
      conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by simp_rw [coordinateNormalCovariant_is_LeviCivita hg]

lemma metricPair_tangential_slots (k : AmbientMat) (e v : PhysicalPoint)
    (he : e 0=0) (hv : v 0=0) :
    metricPair k e v = ∑ a : Fin 2, ∑ b : Fin 2, k a.succ b.succ*e a.succ*v b.succ := by
  simp only [metricPair,Fin.sum_univ_succ,he,hv,mul_zero,zero_mul,Finset.sum_const_zero,zero_add]

theorem leaf_frame_chi {U : PhysicalPoint → ℝ} {γ : PhysicalPoint → Mat}
    {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a b : Fin 2) :
    frameCoefficient (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x a.succ 0 b.succ =
      ∑ i : Fin 2, ∑ j : Fin 2, sourceChi U γ s x i j *
        adaptedFrame (U x) (γ x) (s x) a.succ i.succ *
        adaptedFrame (U x) (γ x) (s x) b.succ j.succ := by
  unfold frameCoefficient
  change metricPair _ (covariantVector _ _ (fun y => foliationNormal (U y) (s y)) x) _ = _
  erw [normalCovariant_frame (G := fun y => foliationMetric (U y) (γ y) (s y))
    (fun y => foliationNormal (U y) (s y)) (foliationMetric_posDef h0.ne' hp.self_of_nhds (s x))]
  erw [metricPair_tangential_slots _ _ _ (adaptedFrame_radial _ _ _ a)
    (adaptedFrame_radial _ _ _ b)]
  have hχ := (physical_foliation_leaf_geometry hU hγ hs h0 hp).1
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hχ]; rfl))

theorem leaf_frame_acceleration {U : PhysicalPoint → ℝ} {γ : PhysicalPoint → Mat}
    {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a : Fin 2) :
    frameCoefficient (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x 0 0 a.succ =
      ∑ b : Fin 2, (D (CKSRealizedRound.basis b.succ) U x/U x)*
        adaptedFrame (U x) (γ x) (s x) a.succ b.succ := by
  unfold frameCoefficient
  change metricPair _ (covariantVector _ (foliationNormal (U x) (s x))
    (fun y => foliationNormal (U y) (s y)) x) _ = _
  erw [normalCovariant_frame (G := fun y => foliationMetric (U y) (γ y) (s y))
    (fun y => foliationNormal (U y) (s y)) (foliationMetric_posDef h0.ne' hp.self_of_nhds (s x))]
  unfold metricPair
  rw [Finset.sum_comm]
  rw [Fin.sum_univ_succ]
  simp only [adaptedFrame_radial,mul_zero,Finset.sum_const_zero,zero_add]
  have hB := (physical_foliation_leaf_geometry hU hγ hs h0 hp).2
  apply Finset.sum_congr rfl
  intro b _
  rw [← hB b,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSFrame
noncomputable section
open Matrix
open scoped BigOperators

def extractTensor (k : Matrix I I ℝ) : TensorData where
  L := k 0 0
  eta := ![k 0 1,k 0 2]
  p := k 1 1+k 2 2
  tau11 := (k 1 1-k 2 2)/2
  tau12 := k 1 2

lemma extractTensor_complete {k : Matrix I I ℝ} (hk : k.IsHermitian) :
    tensor (extractTensor k)=k := by
  have h10 := CKSAngularGeometry.hermitian_real_symmetry hk 0 1
  have h20 := CKSAngularGeometry.hermitian_real_symmetry hk 0 2
  have h21 := CKSAngularGeometry.hermitian_real_symmetry hk 1 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tensor,extractTensor] <;> linarith

end
end CKSFrame

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

def frameTensor (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : AmbientMat := fun i j => metricPair (K x) (E i x) (E j x)

def frameTensorData (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : CKSFrame.TensorData := CKSFrame.extractTensor (frameTensor K E x)

def frameTensorDerivativeData (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (a : Fin 3) : CKSFrame.TensorData :=
  CKSFrame.extractTensor (fun i j => D (E a x) (fun y => frameTensor K E y i j) x)

lemma frameTensor_hermitian {K : PhysicalPoint → AmbientMat} (E : LocalFrame)
    {x : PhysicalPoint} (hk : (K x).IsHermitian) : (frameTensor K E x).IsHermitian := by
  ext i j
  change metricPair (K x) (E j x) (E i x)=metricPair (K x) (E i x) (E j x)
  exact metricPair_symm hk _ _

lemma frameTensorData_exact {K : PhysicalPoint → AmbientMat} (E : LocalFrame)
    {x : PhysicalPoint} (hk : (K x).IsHermitian) :
    CKSFrame.tensor (frameTensorData K E x)=frameTensor K E x :=
  CKSFrame.extractTensor_complete (frameTensor_hermitian E hk)

lemma frameTensorDerivativeData_exact {K : PhysicalPoint → AmbientMat} (E : LocalFrame)
    {x : PhysicalPoint} (hk : ∀ᶠ y in 𝓝 x, (K y).IsHermitian) (a : Fin 3) :
    CKSFrame.tensor (frameTensorDerivativeData K E x a)=
      (fun i j => D (E a x) (fun y => frameTensor K E y i j) x) := by
  apply CKSFrame.extractTensor_complete
  ext i j
  change D (E a x) (fun y => frameTensor K E y j i) x =
    D (E a x) (fun y => frameTensor K E y i j) x
  apply D_congr
  filter_upwards [hk] with y hy
  exact metricPair_symm hy _ _

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

lemma actualFrame_covariant_representation {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : ActualAdaptedAt G E x)
    (hk : ∀ᶠ y in 𝓝 x, (K y).IsHermitian) (i j k : Fin 3) :
    actualFrameTensorCovariant G K E x i j k = CKSFrame.covariantTensor
      (frameConnectionField G E x) (frameTensorData K E x)
      (frameTensorDerivativeData K E x) i j k := by
  unfold actualFrameTensorCovariant CKSFrame.covariantTensor
  rw [frame_connection_actual h, frameTensorData_exact E hk.self_of_nhds,
    frameTensorDerivativeData_exact E hk]

lemma actualFrame_momentum_representation {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : ActualAdaptedAt G E x)
    (hk : ∀ᶠ y in 𝓝 x, (K y).IsHermitian) (j : Fin 3) :
    actualFrameMomentum G K E x j = CKSFrame.momentum
      (frameConnectionField G E x) (frameTensorData K E x)
      (frameTensorDerivativeData K E x) j := by
  unfold actualFrameMomentum CKSFrame.momentum
  simp_rw [actualFrame_covariant_representation h hk,frameTensorDerivativeData_exact E hk]

lemma actualFrame_energy_representation {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : ∀ᶠ y in 𝓝 x, ActualAdaptedAt G E y)
    (hk : (K x).IsHermitian) :
    actualFrameEnergy G K E x = CKSFrame.energy
      (frameConnectionField G E x)
      (fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x)
      (frameTensorData K E x) := by
  unfold actualFrameEnergy CKSFrame.energy actualFrameScalar CKSFrame.scalarCurvature
  simp_rw [frameTensorData_exact E hk,physical_curvature_representation h]

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

theorem actualFrameTensorCovariant_coordinate {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : ActualAdaptedAt G E x)
    (hk : DifferentiableAt ℝ K x) (i j k : Fin 3) :
    actualFrameTensorCovariant G K E x i j k =
      coordinateTensorCovariant G K (E i x) (E j x) (E k x) x := by
  have ho := h.2.2.2.2.1.self_of_nhds
  have hleft := metricPair_frame_left (K x) (e := Matrix.of (fun a b => E a x b))
    ho (covariantVector G (E i x) (E j) x) (E k x)
  have hright := metricPair_frame_right (K x) (e := Matrix.of (fun a b => E a x b))
    ho (covariantVector G (E i x) (E k) x) (E j x)
  change (∑ a, metricPair (G x) (covariantVector G (E i x) (E j) x) (E a x)*
    metricPair (K x) (E a x) (E k x)) = _ at hleft
  change (∑ a, metricPair (G x) (covariantVector G (E i x) (E k) x) (E a x)*
    metricPair (K x) (E j x) (E a x)) = _ at hright
  rw [coordinateTensorCovariant_product_rule hk (h.2.1 j) (h.2.1 k)]
  unfold actualFrameTensorCovariant
  rw [Finset.sum_add_distrib]
  change D (E i x) (fun y => metricPair (K y) (E j y) (E k y)) x -
    ((∑ a, metricPair (G x) (covariantVector G (E i x) (E j) x) (E a x)*
      metricPair (K x) (E a x) (E k x)) +
     ∑ a, metricPair (G x) (covariantVector G (E i x) (E k) x) (E a x)*
      metricPair (K x) (E j x) (E a x)) = _
  rw [hleft,hright]
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

theorem actualFrameEnergy_coordinate {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : ActualAdaptedAt G E x)
    (hk : (K x).IsHermitian) :
    actualFrameEnergy G K E x =
      (actualFrameScalar G E x+((G x)⁻¹*K x).trace^2-
        ((G x)⁻¹*K x*(G x)⁻¹*K x).trace)/2 := by
  have ho := h.2.2.2.2.1.self_of_nhds
  have ht := frame_trace_exact (K x) (e := Matrix.of (fun i j => E i x j)) ho
  have hn := frame_tensor_norm_exact hk (e := Matrix.of (fun i j => E i x j)) ho
  change (∑ i, metricPair (K x) (E i x) (E i x))=_ at ht
  change (∑ i, ∑ j, (metricPair (K x) (E i x) (E j x))^2)=_ at hn
  unfold actualFrameEnergy frameTensor
  rw [ht,hn]

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

def angularFrame (U : ℝ) (γ : Mat) (s : Point) : Mat :=
  fun a b => adaptedFrame U γ s a.succ b.succ

lemma angularFrame_gram {U : ℝ} {γ : Mat} {s : Point}
    (hU : U ≠ 0) (hγ : γ.PosDef) :
    (angularFrame U γ s).transpose * angularFrame U γ s = γ⁻¹ := by
  let e := angularFrame U γ s
  have horth : e*(γ*e.transpose)=1 := by
    ext a b
    change (∑ i, e a i*(∑ j, γ i j*e b j)) = if a=b then 1 else 0
    have ho := adaptedFrame_orthonormal hU hγ s a.succ b.succ
    rw [metricPair_tangential_slots _ _ _ (adaptedFrame_radial U γ s a)
      (adaptedFrame_radial U γ s b)] at ho
    have hmm : (∑ i : Fin 2, ∑ j : Fin 2,
        foliationMetric U γ s i.succ j.succ * adaptedFrame U γ s a.succ i.succ *
          adaptedFrame U γ s b.succ j.succ) =
        ∑ i, ∑ j, γ i j*e a i*e b j := rfl
    rw [hmm] at ho
    simp only [Fin.succ_inj] at ho
    rw [← ho]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  apply (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.mul_assoc]
  exact mul_eq_one_comm.mp horth

lemma angular_trace_transform (k e : Mat) :
    (∑ a : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2, k i j*e a i*e a j)=
      (e*k*e.transpose).trace := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma physical_chi_representation {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a b : Fin 2) :
    CKSFrame.chi (frameConnectionField
      (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) a b =
    ∑ i : Fin 2, ∑ j : Fin 2, sourceChi U γ s x i j *
      angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) b j := by
  have ha := (foliation_actualAdaptedAt hU hγ hs h0.ne' hp).self_of_nhds
  rw [← CKSFrame.connection_normal,frame_connection_actual ha]
  exact leaf_frame_chi (hU.differentiableAt (by simp))
    (hγ.differentiableAt (by simp)) (hs.differentiableAt (by simp)) h0 hp a b

theorem physical_mean_curvature {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    CKSFrame.mean (frameConnectionField
      (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) =
      ((γ x)⁻¹*sourceChi U γ s x).trace := by
  let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
    (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
  have ht : CKSFrame.mean c = ∑ a : Fin 2, CKSFrame.chi c a a := by
    simp [CKSFrame.mean,CKSFrame.chi,Fin.sum_univ_two]
  change CKSFrame.mean c = _
  rw [ht]
  calc
    _ = ∑ a : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2, sourceChi U γ s x i j *
        angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) a j := by
      apply Finset.sum_congr rfl
      intro a _
      exact physical_chi_representation hU hγ hs h0 hp a a
    _ = _ := by
      rw [angular_trace_transform,Matrix.trace_mul_comm,
        ← Matrix.mul_assoc,angularFrame_gram h0.ne' hp.self_of_nhds]

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

lemma frame_trace_derivative {G K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (h : ActualAdaptedAt G E x) (hk : DifferentiableAt ℝ K x)
    (e : PhysicalPoint) :
    (∑ i, D e (fun y => frameTensor K E y i i) x)=
      D e (fun y => ((G y)⁻¹*K y).trace) x := by
  change (∑ i, D e (fun y => metricPair (K y) (E i y) (E i y)) x) = _
  rw [← D_sum3 e _ (fun i => metricPair_differentiableAt hk (h.2.1 i) (h.2.1 i))]
  apply D_congr
  filter_upwards [h.2.2.2.2.1] with y hy
  exact frame_trace_exact (K y) (e := Matrix.of (fun i j => E i y j)) hy

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

theorem actualFrameMomentum_coordinate {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : ActualAdaptedAt G E x)
    (hk : DifferentiableAt ℝ K x) (j : Fin 3) :
    actualFrameMomentum G K E x j=coordinateMomentum G K x (E j x) := by
  have ht := frame_trace_exact
    (Matrix.of (fun a b => coordinateTensorCovariant G K
      (CKSRealizedRound.basis a) (CKSRealizedRound.basis b) (E j x) x))
    (e := Matrix.of (fun a b => E a x b)) h.2.2.2.2.1.self_of_nhds
  change (∑ i, metricPair
    (fun a b => coordinateTensorCovariant G K (CKSRealizedRound.basis a)
      (CKSRealizedRound.basis b) (E j x) x) (E i x) (E i x)) = _ at ht
  have hd : (∑ i, actualFrameTensorCovariant G K E x i i j) =
      ((G x)⁻¹ * Matrix.of (fun a b => coordinateTensorCovariant G K
        (CKSRealizedRound.basis a) (CKSRealizedRound.basis b) (E j x) x)).trace := by
    rw [← ht]
    apply Finset.sum_congr rfl
    intro i _
    rw [actualFrameTensorCovariant_coordinate h hk]
    exact coordinateTensorCovariant_bilinear G K x (E i x) (E i x) (E j x)
  unfold actualFrameMomentum coordinateMomentum
  rw [hd,frame_trace_derivative h hk]

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

lemma angular_covector_frame_square (ρ : Point) {U : ℝ} {γ : Mat} {s : Point}
    (hU : U ≠ 0) (hγ : γ.PosDef) :
    (∑ a, (∑ i, ρ i*angularFrame U γ s a i)^2)=
      ∑ i, ∑ j, γ⁻¹ i j*ρ i*ρ j := by
  have hc (i j) : (∑ a, angularFrame U γ s a i*angularFrame U γ s a j)=γ⁻¹ i j :=
    congrFun (congrFun (angularFrame_gram (s := s) hU hγ) i) j
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (∑ a, angularFrame U γ s a i*angularFrame U γ s a j)*ρ i*ρ j := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [hc]

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

def angularLowerConnection (γ : PhysicalPoint → Mat) (x : PhysicalPoint)
    (i j k : Fin 2) : ℝ :=
  (D (CKSRealizedRound.basis i.succ) (fun y => γ y j k) x +
   D (CKSRealizedRound.basis j.succ) (fun y => γ y i k) x -
   D (CKSRealizedRound.basis k.succ) (fun y => γ y i j) x)/2

lemma foliation_lower_angular (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (x : PhysicalPoint) (i j k : Fin 2) :
    lowerKoszul (actualMetricFirstJet (fun y => foliationMetric (U y) (γ y) (s y)) x)
      i.succ j.succ k.succ = angularLowerConnection γ x i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

lemma tangential_sum_pair (A : AmbientMat) (v w : PhysicalPoint)
    (hv : v 0 = 0) (hw : w 0 = 0) :
    (∑ k : Fin 3, (∑ l : Fin 3, v l*A l k)*w k) =
      ∑ k : Fin 2, (∑ l : Fin 2, v l.succ*A l.succ k.succ)*w k.succ := by
  rw [Fin.sum_univ_succ]
  simp only [hw,mul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fin.sum_univ_succ,hv,zero_mul,zero_add]

lemma tangential_sum_triple (C : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (e v w : PhysicalPoint) (he : e 0=0) (hv : v 0=0) (hw : w 0=0) :
    (∑ k : Fin 3, (∑ i : Fin 3, ∑ j : Fin 3, e i*v j*C i j k)*w k)=
      ∑ k : Fin 2, (∑ i : Fin 2, ∑ j : Fin 2,
        e i.succ*v j.succ*C i.succ j.succ k.succ)*w k.succ := by
  rw [Fin.sum_univ_succ]
  simp only [hw,mul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [Fin.sum_univ_succ]
  simp only [he,zero_mul,Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  simp only [hv,mul_zero,zero_mul,zero_add]

lemma foliationMetric_angular (U : ℝ) (γ : Mat) (s : Point) (i j : Fin 2) :
    foliationMetric U γ s i.succ j.succ=γ i j := by
  fin_cases i <;> fin_cases j <;> rfl

lemma source_tangential_connection {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hp : (γ x).PosDef) (h0 : U x ≠ 0) (e w : PhysicalPoint)
    (V : PhysicalPoint → PhysicalPoint) (he : e 0=0) (hw : w 0=0)
    (hV : ∀ y, V y 0=0) :
    metricPair (foliationMetric (U x) (γ x) (s x))
      (covariantVector (fun y => foliationMetric (U y) (γ y) (s y)) e V x) w =
      (∑ k : Fin 2, (∑ l : Fin 2, D e (fun y => V y l.succ) x*γ x l k)*w k.succ) +
      ∑ k : Fin 2, (∑ i : Fin 2, ∑ j : Fin 2,
        e i.succ*V x j.succ*angularLowerConnection γ x i j k)*w k.succ := by
  have hz : D e (fun y => V y 0) x=0 := by
    have hh : (fun y => V y 0)=(fun _ => (0:ℝ)) := funext hV
    rw [hh,D_const]
  have hg : PosDef ((fun y => foliationMetric (U y) (γ y) (s y)) x) :=
    foliationMetric_posDef h0 hp (s x)
  have hr := metricPair_covariant (G := fun y => foliationMetric (U y) (γ y) (s y)) (x := x) hg e w V
  change metricPair (foliationMetric (U x) (γ x) (s x))
    (covariantVector (fun y => foliationMetric (U y) (γ y) (s y)) e V x) w = _ at hr
  rw [hr,tangential_sum_pair _ _ _ hz hw,
    tangential_sum_triple _ _ _ _ he (hV x) hw]
  simp only [foliationMetric_angular,foliation_lower_angular]

def inducedFrameCoefficient (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (x : PhysicalPoint) (a b c : Fin 2) : ℝ :=
  (∑ k : Fin 2, (∑ l : Fin 2,
    D (adaptedFrame (U x) (γ x) (s x) a.succ)
      (fun y => angularFrame (U y) (γ y) (s y) b l) x * γ x l k) *
      angularFrame (U x) (γ x) (s x) c k) +
  ∑ k : Fin 2, (∑ i : Fin 2, ∑ j : Fin 2,
    angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) b j *
      angularLowerConnection γ x i j k) * angularFrame (U x) (γ x) (s x) c k

theorem physical_leaf_connection {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hp : (γ x).PosDef) (h0 : U x ≠ 0) (a b c : Fin 2) :
    frameCoefficient (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x a.succ b.succ c.succ =
      inducedFrameCoefficient U γ s x a b c := by
  exact source_tangential_connection hp h0 _ _ _
    (adaptedFrame_radial _ _ _ a) (adaptedFrame_radial _ _ _ c)
    (fun y => adaptedFrame_radial _ _ _ b)

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

theorem physical_momentum_frame_norm {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : ActualAdaptedAt G E x)
    (hk : DifferentiableAt ℝ K x) :
    (∑ a, (actualFrameMomentum G K E x a)^2)=
      metricPair (G x)⁻¹ (momentumCovector G K x) (momentumCovector G K x) := by
  conv_lhs => arg 2; ext a; rw [actualFrameMomentum_coordinate h hk,coordinateMomentum_expansion]
  exact covector_frame_square (momentumCovector G K x)
    (e := Matrix.of (fun i j => E i x j)) h.2.2.2.2.1.self_of_nhds

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
open Matrix CKSCalculus Filter CKSFrame
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem physical_foliation_constraints {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hk : DifferentiableAt ℝ K x) (hks : ∀ᶠ y in 𝓝 x, (K y).IsHermitian) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField G E x
    let dc := fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x
    let t := frameTensorData K E x
    let dt := frameTensorDerivativeData K E x
    (actualFrameScalar G E x+((G x)⁻¹*K x).trace^2-
        ((G x)⁻¹*K x*(G x)⁻¹*K x).trace)/2 =
      leafScalar c dc/2-normalMean dc+accelDiv c dc-accelNormSq c-
        3/4*(mean c)^2-shearNormSq c/2+t.L*t.p+t.p^2/4-tauNormSq t/2-etaNormSq t ∧
    coordinateMomentum G K x (E 0 x) =
      mean c*(t.L-t.p/2)-shearTau c t-(dt 0).p+etaDiv c t dt-2*etaAcceleration c t ∧
    ∀ a, coordinateMomentum G K x (E a.succ x) =
      normalLieEta c t dt a+mean c*t.eta a+tauDiv c t dt a-
        ((dt a.succ).L+(dt a.succ).p/2)+accelTensor c t a := by
  dsimp only
  have h := foliation_actualAdaptedAt hU hγ hs h0.ne' hp
  constructor
  · rw [← actualFrameEnergy_coordinate h.self_of_nhds hks.self_of_nhds,
      actualFrame_energy_representation h hks.self_of_nhds]
    exact energy_decomposition _ _ _
  constructor
  · rw [← actualFrameMomentum_coordinate h.self_of_nhds hk,
      actualFrame_momentum_representation h.self_of_nhds hks]
    exact normal_momentum_decomposition _ _ _
  · intro a
    rw [← actualFrameMomentum_coordinate h.self_of_nhds hk,
      actualFrame_momentum_representation h.self_of_nhds hks]
    exact tangential_momentum_decomposition _ _ _ a

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

lemma physical_acceleration_components {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a : Fin 2) :
    (frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x).B a =
      ∑ b : Fin 2, (D (CKSRealizedRound.basis b.succ) U x / U x) *
        angularFrame (U x) (γ x) (s x) a b := by
  have h := leaf_frame_acceleration hU hγ hs h0 hp a
  fin_cases a <;> exact h

theorem physical_acceleration_norm {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    CKSFrame.accelNormSq (frameConnectionField
      (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) =
      ∑ i : Fin 2, ∑ j : Fin 2, (γ x)⁻¹ i j *
        (D (CKSRealizedRound.basis i.succ) U x / U x) *
        (D (CKSRealizedRound.basis j.succ) U x / U x) := by
  have he : CKSFrame.accelNormSq (frameConnectionField
      (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) =
      ∑ a : Fin 2, ((frameConnectionField
        (fun y => foliationMetric (U y) (γ y) (s y))
        (fun i y => adaptedFrame (U y) (γ y) (s y) i) x).B a)^2 := by
    simp only [CKSFrame.accelNormSq,Fin.sum_univ_two]
  rw [he]
  simp_rw [physical_acceleration_components hU hγ hs h0 hp]
  exact angular_covector_frame_square _ h0.ne' hp.self_of_nhds

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
namespace CKSFrame
noncomputable section
open CKSCalculus
open scoped BigOperators

def normalVector (U : ℝ) (s : A → ℝ) : Chart := ![U,-U*s 0,-U*s 1]

lemma normal_radius (U : ℝ) (s : A → ℝ) (x : Chart) :
    D (normalVector U s) (fun y : Chart => y 0) x = U := by
  change D (normalVector U s) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) 0) x = U
  rw [D_clm]
  rfl

lemma normal_mass_derivative {H p : Chart → ℝ} {x : Chart}
    (hH : DifferentiableAt ℝ H x) (hp : DifferentiableAt ℝ p x) (U : ℝ) (s : A → ℝ) :
    D (normalVector U s) (massField H p) x =
      U/2*(1+(x 0*p x/2)^2-(x 0*H x/2)^2)+x 0*((x 0*p x/2)*
        (U*p x/2+x 0*D (normalVector U s) p x/2)-
        (x 0*H x/2)*(U*H x/2+x 0*D (normalVector U s) H x/2)) := by
  have hr : DifferentiableAt ℝ (fun y : Chart => y 0) x := by fun_prop
  have ht : DifferentiableAt ℝ (fun y : Chart => y 0*p y/2) x := diffAt_div (hr.fun_mul hp) (differentiableAt_const _) (by norm_num)
  have hu : DifferentiableAt ℝ (fun y : Chart => y 0*H y/2) x := diffAt_div (hr.fun_mul hH) (differentiableAt_const _) (by norm_num)
  have hc : DifferentiableAt ℝ (fun _ : Chart => (1:ℝ)) x := differentiableAt_const _
  unfold massField
  erw [D_mul _ (diffAt_div hr (differentiableAt_const (2:ℝ)) (by norm_num)) ((hc.add (ht.pow 2)).sub (hu.pow 2)),
    D_div _ hr (differentiableAt_const _) (by norm_num),D_const,
    D_sub _ (hc.add (ht.pow 2)) (hu.pow 2),D_add _ hc (ht.pow 2),D_const,
    D_pow _ 2 ht,D_pow _ 2 hu,
    D_div _ (hr.fun_mul hp) (differentiableAt_const _) (by norm_num),
    D_div _ (hr.fun_mul hH) (differentiableAt_const _) (by norm_num),D_const,
    D_mul _ hr hp,D_mul _ hr hH,normal_radius]
  simp only [Pi.add_apply,Pi.sub_apply,Pi.pow_apply]
  ring

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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma angular_frame_covector_contract {U : ℝ} {γ : Mat} {s : Point}
    (hU : U ≠ 0) (hγ : γ.PosDef) (v α : Point) :
    (∑ b : Fin 2, (∑ k : Fin 2, v k * angularFrame U γ s b k) *
      (∑ j : Fin 2, α j * angularFrame U γ s b j)) =
      ∑ k : Fin 2, ∑ j : Fin 2, γ⁻¹ k j * v k * α j := by
  have hg (k j : Fin 2) :
      (∑ b : Fin 2, angularFrame U γ s b k * angularFrame U γ s b j) = γ⁻¹ k j := by
    exact congrFun (congrFun (angularFrame_gram hU hγ) k) j
  calc
    _ = ∑ k : Fin 2, ∑ j : Fin 2,
        (∑ b : Fin 2, angularFrame U γ s b k * angularFrame U γ s b j) * v k * α j := by
      simp only [Fin.sum_univ_two]
      ring
    _ = _ := by simp only [hg]

lemma metric_inverse_covector_contract {γ : Mat} (hγ : γ.PosDef) (v α : Point) :
    (∑ k : Fin 2, ∑ j : Fin 2, γ⁻¹ k j * (∑ l : Fin 2, v l * γ l k) * α j) =
      ∑ j : Fin 2, v j * α j := by
  calc
    _ = ∑ j : Fin 2, (∑ l : Fin 2, v l * (γ * γ⁻¹) l j) * α j := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = _ := by
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hγ.det_pos.ne')]
      simp

lemma physical_christoffel_lower (γ : PhysicalPoint → Mat) (x : PhysicalPoint)
    (j i k : Fin 2) :
    christoffel (physicalAngularJet γ x) j i k =
      ∑ l : Fin 2, (γ x)⁻¹ j l * angularLowerConnection γ x i k l := by
  simp only [christoffel, physicalAngularJet, inverse_eq, angularLowerConnection,
    Fin.sum_univ_two]
  ring

lemma inverse_symm_entry {γ : Mat} (hp : γ.PosDef) (i j : Fin 2) :
    γ⁻¹ i j = γ⁻¹ j i := by
  have hs := hp.inv.isHermitian
  have h := congrFun (congrFun hs.eq i) j
  simpa using h.symm

lemma induced_connection_covector {U : PhysicalPoint → ℝ} {γ : PhysicalPoint → Mat}
    {s : PhysicalPoint → Point} {x : PhysicalPoint} (hU : U x ≠ 0)
    (hp : (γ x).PosDef) (a b : Fin 2) (α : Point) :
    (∑ c : Fin 2, inducedFrameCoefficient U γ s x a b c *
      (∑ j : Fin 2, α j * angularFrame (U x) (γ x) (s x) c j)) =
    (∑ j : Fin 2, D (adaptedFrame (U x) (γ x) (s x) a.succ)
      (fun y => angularFrame (U y) (γ y) (s y) b j) x * α j) +
    ∑ i : Fin 2, ∑ k : Fin 2, ∑ j : Fin 2,
      angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) b k *
      christoffel (physicalAngularJet γ x) j i k * α j := by
  simp only [inducedFrameCoefficient, add_mul, Finset.sum_add_distrib]
  rw [angular_frame_covector_contract hU hp, metric_inverse_covector_contract hp]
  congr 1
  rw [angular_frame_covector_contract hU hp]
  simp only [physical_christoffel_lower, Fin.sum_univ_two]
  rw [inverse_symm_entry hp 1 0]
  ring

lemma D_angular_sum (e : PhysicalPoint) {x : PhysicalPoint}
    (f : Fin 2 → PhysicalPoint → ℝ) (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    D e (fun y => ∑ i, f i y) x = ∑ i, D e (f i) x := by
  simp only [D, fderiv_fun_sum (fun i _ => hf i), _root_.sum_apply]

lemma D_angular_direction (U : ℝ) (γ : Mat) (s : Point)
    (a : Fin 2) (f : PhysicalPoint → ℝ) (x : PhysicalPoint) :
    D (adaptedFrame U γ s a.succ) f x =
      ∑ i : Fin 2, angularFrame U γ s a i * D (CKSRealizedRound.basis i.succ) f x := by
  rw [D_direction_expansion, Fin.sum_univ_succ, adaptedFrame_radial,
    zero_mul, zero_add]
  rfl

lemma extracted_leaf_connection (c : CKSFrame.ConnectionData) (a b d : Fin 2) :
    CKSFrame.leafConnection c a b d = CKSFrame.connection c a.succ b.succ d.succ := by
  fin_cases a <;> fin_cases b <;> fin_cases d <;> rfl

lemma physical_leaf_connection_extracted {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a b d : Fin 2) :
    CKSFrame.leafConnection (frameConnectionField
      (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) a b d =
      -inducedFrameCoefficient U γ s x a d b := by
  rw [extracted_leaf_connection, CKSFrame.connection_metric,
    frame_connection_actual (foliation_actualAdaptedAt hU hγ hs h0 hp).self_of_nhds,
    physical_leaf_connection hp.self_of_nhds h0]

lemma angular_frame_tensor_contract {U : ℝ} {γ : Mat} {s : Point}
    (hU : U ≠ 0) (hγ : γ.PosDef) (T : Mat) :
    (∑ a : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2,
      angularFrame U γ s a i * angularFrame U γ s a j * T i j) =
      ∑ i : Fin 2, ∑ j : Fin 2, γ⁻¹ i j * T i j := by
  have hg (i j : Fin 2) :
      (∑ a : Fin 2, angularFrame U γ s a i * angularFrame U γ s a j) = γ⁻¹ i j := by
    exact congrFun (congrFun (angularFrame_gram hU hγ) i) j
  calc
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
      (∑ a : Fin 2, angularFrame U γ s a i * angularFrame U γ s a j) * T i j := by
      simp only [Fin.sum_univ_two]
      ring
    _ = _ := by simp only [hg]

lemma physical_covector_divergence {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (α : Fin 2 → PhysicalPoint → ℝ) (hα : ∀ i, DifferentiableAt ℝ (α i) x) :
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    (∑ a : Fin 2, (D (adaptedFrame (U x) (γ x) (s x) a.succ)
      (fun y => ∑ j : Fin 2, α j y * angularFrame (U y) (γ y) (s y) a j) x +
      ∑ b : Fin 2, CKSFrame.leafConnection c a b a *
        (∑ j : Fin 2, α j x * angularFrame (U x) (γ x) (s x) b j))) =
    ∑ i : Fin 2, ∑ j : Fin 2, (γ x)⁻¹ i j *
      (D (CKSRealizedRound.basis i.succ) (α j) x -
        ∑ k : Fin 2, christoffel (physicalAngularJet γ x) k i j * α k x) := by
  dsimp only
  have he (a j : Fin 2) : DifferentiableAt ℝ
      (fun y => angularFrame (U y) (γ y) (s y) a j) x :=
    differentiableAt_pi.mp ((adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds a.succ).differentiableAt (by simp)) j.succ
  have hsum (a : Fin 2) :
      D (adaptedFrame (U x) (γ x) (s x) a.succ)
        (fun y => ∑ j : Fin 2, α j y * angularFrame (U y) (γ y) (s y) a j) x =
      ∑ j : Fin 2, (α j x * D (adaptedFrame (U x) (γ x) (s x) a.succ)
        (fun y => angularFrame (U y) (γ y) (s y) a j) x +
        angularFrame (U x) (γ x) (s x) a j *
          D (adaptedFrame (U x) (γ x) (s x) a.succ) (α j) x) := by
    rw [D_angular_sum _ (fun j y => α j y * angularFrame (U y) (γ y) (s y) a j)
      (fun j => (hα j).mul (he a j))]
    apply Finset.sum_congr rfl
    intro j _
    exact D_mul _ (hα j) (he a j)
  calc
    _ = ∑ a : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2,
        angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) a j *
        (D (CKSRealizedRound.basis i.succ) (α j) x -
          ∑ k : Fin 2, christoffel (physicalAngularJet γ x) k i j * α k x) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [physical_leaf_connection_extracted hU hγ hs h0 hp,
        neg_mul, Finset.sum_neg_distrib]
      rw [induced_connection_covector h0 hp.self_of_nhds, hsum]
      simp only [D_angular_direction, Fin.sum_univ_two]
      ring
    _ = _ := angular_frame_tensor_contract h0 hp.self_of_nhds _

lemma physical_acceleration_divergence {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField G E x
    let dc := fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x
    CKSFrame.accelDiv c dc =
      ∑ i : Fin 2, ∑ j : Fin 2, (γ x)⁻¹ i j *
        (D (CKSRealizedRound.basis i.succ)
          (fun y => D (CKSRealizedRound.basis j.succ) U y / U y) x -
          ∑ k : Fin 2, christoffel (physicalAngularJet γ x) k i j *
            (D (CKSRealizedRound.basis k.succ) U x / U x)) := by
  dsimp only
  let α : Fin 2 → PhysicalPoint → ℝ := fun j y => D (CKSRealizedRound.basis j.succ) U y / U y
  have hu1 : ContDiffAt ℝ 1 U x := hU.of_le (by simp)
  have hg1 : ContDiffAt ℝ 1 γ x := hγ.of_le (by simp)
  have hs1 : ContDiffAt ℝ 1 s x := hs.of_le (by simp)
  have hnear : ∀ᶠ y in 𝓝 x, 0 < U y := hU.continuousAt.eventually (lt_mem_nhds h0)
  have hB (a : Fin 2) :
      (fun y => (frameConnectionField (fun z => foliationMetric (U z) (γ z) (s z))
        (fun i z => adaptedFrame (U z) (γ z) (s z) i) y).B a) =ᶠ[𝓝 x]
      (fun y => ∑ j : Fin 2, α j y * angularFrame (U y) (γ y) (s y) a j) := by
    filter_upwards [hu1.eventually (by norm_num), hg1.eventually (by norm_num),
      hs1.eventually (by norm_num), hnear, hp.eventually_nhds] with y hyu hyg hys hyp hpg
    exact physical_acceleration_components (hyu.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) (hys.differentiableAt (by norm_num)) hyp hpg a
  have hU2 : ContDiffAt ℝ 2 U x := hU.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hd (i : Fin 2) : DifferentiableAt ℝ (D (CKSRealizedRound.basis i.succ) U) x :=
    (contDiffAt_D hU2 (m := 1) (by norm_num) _).differentiableAt (by norm_num)
  have hα (i : Fin 2) : DifferentiableAt ℝ (α i) x :=
    diffAt_div (hd i) (hU.differentiableAt (by simp)) h0.ne'
  rw [CKSFrame.accelDiv]
  calc
    _ = ∑ a : Fin 2, (D (adaptedFrame (U x) (γ x) (s x) a.succ)
        (fun y => ∑ j : Fin 2, α j y * angularFrame (U y) (γ y) (s y) a j) x +
      ∑ b : Fin 2, CKSFrame.leafConnection (frameConnectionField
        (fun y => foliationMetric (U y) (γ y) (s y))
        (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) a b a *
        (∑ j : Fin 2, α j x * angularFrame (U x) (γ x) (s x) b j)) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      · exact D_congr (hB a) _
      · apply Finset.sum_congr rfl
        intro b _
        congr 1
        exact (hB b).self_of_nhds
    _ = _ := physical_covector_divergence hU hγ hs h0.ne' hp α hα

theorem physical_acceleration_laplacian {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField G E x
    let dc := fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x
    CKSFrame.accelDiv c dc - CKSFrame.accelNormSq c =
      -lapseLaplacian (physicalAngularJet γ x) (physicalAngularScalarJet U x) := by
  dsimp only
  rw [physical_acceleration_divergence hU hγ hs h0 hp,
    physical_acceleration_norm (hU.differentiableAt (by simp))
      (hγ.differentiableAt (by simp)) (hs.differentiableAt (by simp)) h0 hp]
  have hU2 : ContDiffAt ℝ 2 U x := hU.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hd (j : Fin 2) : DifferentiableAt ℝ (D (CKSRealizedRound.basis j.succ) U) x :=
    (contDiffAt_D hU2 (m := 1) (by norm_num) _).differentiableAt (by norm_num)
  simp only [D_div _ (hd _) (hU.differentiableAt (by simp)) h0.ne',
    lapseLaplacian, physicalAngularScalarJet, physicalAngularJet, inverse_eq,
    Fin.sum_univ_two]
  field_simp
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def angularTensorFrame (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (T : PhysicalPoint → Mat)
    (x : PhysicalPoint) (a b : Fin 2) : ℝ :=
  ∑ i, ∑ j, T x i j * angularFrame (U x) (γ x) (s x) a i *
    angularFrame (U x) (γ x) (s x) b j

lemma angularFrame_component_diff {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hp : (γ x).PosDef) (a i : Fin 2) :
    DifferentiableAt ℝ (fun y => angularFrame (U y) (γ y) (s y) a i) x :=
  differentiableAt_pi.mp ((adaptedFrame_contDiffAt hU hγ hs hp a.succ).differentiableAt
    (by simp)) i.succ

lemma D_angularTensorFrame {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hp : (γ x).PosDef)
    (hT : DifferentiableAt ℝ T x) (v : PhysicalPoint) (a b : Fin 2) :
    D v (fun y => angularTensorFrame U γ s T y a b) x =
      ∑ i : Fin 2, ∑ j : Fin 2,
        (D v (fun y => T y i j) x * angularFrame (U x) (γ x) (s x) a i *
          angularFrame (U x) (γ x) (s x) b j +
        T x i j * D v (fun y => angularFrame (U y) (γ y) (s y) a i) x *
          angularFrame (U x) (γ x) (s x) b j +
        T x i j * angularFrame (U x) (γ x) (s x) a i *
          D v (fun y => angularFrame (U y) (γ y) (s y) b j) x) := by
  have ht (i j : Fin 2) : DifferentiableAt ℝ (fun y => T y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hT i) j
  have he := angularFrame_component_diff hU hγ hs hp
  unfold angularTensorFrame
  rw [D_angular_sum _ _ (fun i => DifferentiableAt.fun_sum (fun j _ =>
    ((ht i j).fun_mul (he a i)).fun_mul (he b j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [D_angular_sum _ _ (fun j => ((ht i j).fun_mul (he a i)).fun_mul (he b j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [D_mul _ ((ht i j).fun_mul (he a i)) (he b j), D_mul _ (ht i j) (he a i)]
  ring

lemma induced_tensor_connection_left {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (a b d : Fin 2) :
    (∑ c : Fin 2, inducedFrameCoefficient U γ s x a b c *
      angularTensorFrame U γ s T x c d) =
    (∑ i : Fin 2, ∑ j : Fin 2, T x i j *
      D (adaptedFrame (U x) (γ x) (s x) a.succ)
        (fun y => angularFrame (U y) (γ y) (s y) b i) x *
      angularFrame (U x) (γ x) (s x) d j) +
    ∑ i : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2, ∑ j : Fin 2,
      angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) b k *
      christoffel (physicalAngularJet γ x) l i k * T x l j *
      angularFrame (U x) (γ x) (s x) d j := by
  have h := induced_connection_covector (s := s) h0 hp a b
    (fun i => ∑ j : Fin 2, T x i j * angularFrame (U x) (γ x) (s x) d j)
  simp only [angularTensorFrame, Fin.sum_univ_two] at h ⊢
  linear_combination h

lemma induced_tensor_connection_right {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (a b d : Fin 2) :
    (∑ c : Fin 2, inducedFrameCoefficient U γ s x a d c *
      angularTensorFrame U γ s T x b c) =
    (∑ i : Fin 2, ∑ j : Fin 2, T x i j *
      angularFrame (U x) (γ x) (s x) b i *
      D (adaptedFrame (U x) (γ x) (s x) a.succ)
        (fun y => angularFrame (U y) (γ y) (s y) d j) x) +
    ∑ i : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2, ∑ j : Fin 2,
      angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) d k *
      christoffel (physicalAngularJet γ x) l i k * T x j l *
      angularFrame (U x) (γ x) (s x) b j := by
  have h := induced_connection_covector (s := s) h0 hp a d
    (fun j => ∑ i : Fin 2, T x i j * angularFrame (U x) (γ x) (s x) b i)
  simp only [angularTensorFrame, Fin.sum_univ_two] at h ⊢
  linear_combination h

lemma physical_leaf_connection_direct {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a b d : Fin 2) :
    CKSFrame.leafConnection (frameConnectionField
      (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) a b d =
      inducedFrameCoefficient U γ s x a b d := by
  rw [extracted_leaf_connection,
    frame_connection_actual (foliation_actualAdaptedAt hU hγ hs h0 hp).self_of_nhds,
    physical_leaf_connection hp.self_of_nhds h0]

lemma physical_leaf_tensor_covariant {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hT : DifferentiableAt ℝ T x) (a b d : Fin 2) :
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    (D (E a.succ x) (fun y => angularTensorFrame U γ s T y b d) x -
      ∑ e : Fin 2, (CKSFrame.leafConnection c a b e * angularTensorFrame U γ s T x e d +
        CKSFrame.leafConnection c a d e * angularTensorFrame U γ s T x b e)) =
    ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
      angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) b j *
        angularFrame (U x) (γ x) (s x) d k *
          (D (CKSRealizedRound.basis i.succ) (fun y => T y j k) x -
            ∑ l : Fin 2, (christoffel (physicalAngularJet γ x) l i j * T x l k +
              christoffel (physicalAngularJet γ x) l i k * T x j l)) := by
  dsimp only
  simp only [physical_leaf_connection_direct hU hγ hs h0 hp, Finset.sum_add_distrib]
  rw [D_angularTensorFrame hU hγ hs hp.self_of_nhds hT,
    induced_tensor_connection_left h0 hp.self_of_nhds,
    induced_tensor_connection_right h0 hp.self_of_nhds]
  simp only [D_angular_direction, Fin.sum_univ_two]
  ring

theorem physical_leaf_tensor_divergence {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hT : DifferentiableAt ℝ T x) (a : Fin 2) :
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    (∑ b : Fin 2, (D (E b.succ x) (fun y => angularTensorFrame U γ s T y b a) x -
      ∑ d : Fin 2, (CKSFrame.leafConnection c b b d * angularTensorFrame U γ s T x d a +
        CKSFrame.leafConnection c b a d * angularTensorFrame U γ s T x b d))) =
      ∑ k : Fin 2, tensorDiv (physicalAngularJet γ x)
        (fun i j => physicalAngularScalarJet (fun y => T y i j) x) k *
          angularFrame (U x) (γ x) (s x) a k := by
  dsimp only
  have hcov := physical_leaf_tensor_covariant hU hγ hs h0 hp hT
  dsimp only at hcov
  simp_rw [hcov]
  let e : Fin 2 → Point := fun a => angularFrame (U x) (γ x) (s x) a
  let A : Fin 2 → Fin 2 → Fin 2 → ℝ := fun i j k =>
    D (CKSRealizedRound.basis i.succ) (fun y => T y j k) x -
      ∑ l : Fin 2, (christoffel (physicalAngularJet γ x) l i j * T x l k +
        christoffel (physicalAngularJet γ x) l i k * T x j l)
  calc
    (∑ b : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
        e b i * e b j * e a k * A i j k) =
      ∑ k : Fin 2, (∑ b : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2,
        e b i * e b j * A i j k) * e a k := by
          simp only [Fin.sum_univ_two]
          ring
    _ = ∑ k : Fin 2, (∑ i : Fin 2, ∑ j : Fin 2, (γ x)⁻¹ i j * A i j k) * e a k := by
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fun z => z * e a k)
        (angular_frame_tensor_contract (s := s x) h0 hp.self_of_nhds (fun i j => A i j k))
    _ = _ := by
      simp only [tensorDiv, physicalAngularScalarJet, inverse_eq, physicalAngularJet, A, e]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma foliationNormal_succ (U : ℝ) (s : Point) (i : Fin 2) :
    foliationNormal U s i.succ = -U * s i := by
  fin_cases i <;> rfl

lemma tangential_frame_covector_expansion {U : ℝ} {γ : Mat} {s : Point}
    (h0 : U ≠ 0) (hp : γ.PosDef) (v : PhysicalPoint) (α : Point) :
    (∑ b : Fin 2, metricPair (foliationMetric U γ s) v (adaptedFrame U γ s b.succ) *
      (∑ i : Fin 2, α i * angularFrame U γ s b i)) =
      ∑ i : Fin 2, α i * (v i.succ + s i * v 0) := by
  have he := orthonormal_frame_expansion (e := Matrix.of (fun a b => adaptedFrame U γ s a b))
    (adaptedFrame_orthonormal h0 hp s) v
  have hrad := he 0
  simp only [Matrix.of_apply, Fin.sum_univ_succ, adaptedFrame_radial, mul_zero,
    Finset.sum_const_zero, add_zero] at hrad
  change metricPair (foliationMetric U γ s) v (foliationNormal U s) * U = v 0 at hrad
  have ht (i : Fin 2) :
      (∑ b : Fin 2, metricPair (foliationMetric U γ s) v (adaptedFrame U γ s b.succ) *
        angularFrame U γ s b i) = v i.succ + s i * v 0 := by
    have hh := he i.succ
    simp only [Matrix.of_apply, Fin.sum_univ_succ, adaptedFrame_first,
      foliationNormal_succ] at hh
    change metricPair (foliationMetric U γ s) v (foliationNormal U s) * (-U * s i) +
      (∑ b : Fin 2, metricPair (foliationMetric U γ s) v (adaptedFrame U γ s b.succ) *
        angularFrame U γ s b i) = v i.succ at hh
    calc
      _ = v i.succ + s i * (metricPair (foliationMetric U γ s) v (foliationNormal U s) * U) := by
        linear_combination hh
      _ = _ := by rw [hrad]
  calc
    _ = ∑ i : Fin 2, α i * (∑ b : Fin 2,
        metricPair (foliationMetric U γ s) v (adaptedFrame U γ s b.succ) * angularFrame U γ s b i) := by
          simp only [Fin.sum_univ_two]
          ring
    _ = _ := by simp only [ht]

lemma adaptedFrame_normal_bracket {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hs : DifferentiableAt ℝ s x) (a i : Fin 2) :
    let E := fun b y => adaptedFrame (U y) (γ y) (s y) b
    actualFrameBracket E x 0 a.succ i.succ + s x i * actualFrameBracket E x 0 a.succ 0 =
      D (foliationNormal (U x) (s x))
        (fun y => angularFrame (U y) (γ y) (s y) a i) x +
        U x * D (E a.succ x) (fun y => s y i) x := by
  dsimp only
  have hdn := foliationNormal_derivative (adaptedFrame (U x) (γ x) (s x) a.succ) hU hs
  have hi := congrFun hdn i.succ
  have hzero := congrFun hdn 0
  have hni : foliationNormalDerivative (U x) (s x)
      (D (adaptedFrame (U x) (γ x) (s x) a.succ) U x)
      (fun j => D (adaptedFrame (U x) (γ x) (s x) a.succ) (fun y => s y j) x) i.succ =
    -(D (adaptedFrame (U x) (γ x) (s x) a.succ) U x) * s x i -
      U x * D (adaptedFrame (U x) (γ x) (s x) a.succ) (fun y => s y i) x := by
    fin_cases i <;> dsimp [foliationNormalDerivative]
  rw [hni] at hi
  change D (adaptedFrame (U x) (γ x) (s x) a.succ) U x = _ at hzero
  simp only [actualFrameBracket, adaptedFrame_radial, adaptedFrame_first, D_const]
  change D (foliationNormal (U x) (s x))
    (fun y => angularFrame (U y) (γ y) (s y) a i) x -
    D (adaptedFrame (U x) (γ x) (s x) a.succ) (fun y => foliationNormal (U y) (s y) i.succ) x +
    s x i * (0 - D (adaptedFrame (U x) (γ x) (s x) a.succ) U x) = _
  rw [hi]
  ring

lemma physical_normal_tangential_connection {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a : Fin 2) (α : Point) :
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    (∑ b : Fin 2, (CKSFrame.connection c 0 a.succ b.succ - CKSFrame.chi c a b) *
      (∑ i : Fin 2, α i * angularFrame (U x) (γ x) (s x) b i)) =
      ∑ i : Fin 2, α i *
        (D (foliationNormal (U x) (s x))
          (fun y => angularFrame (U y) (γ y) (s y) a i) x +
          U x * D (E a.succ x) (fun y => s y i) x) := by
  dsimp only
  have ha := (foliation_actualAdaptedAt hU hγ hs h0 hp).self_of_nhds
  have hmetric : ∀ᶠ y in 𝓝 x, (foliationMetric (U y) (γ y) (s y)).IsHermitian :=
    hp.mono fun y hy => metricBlock_hermitian _ _ hy.isHermitian
  simp only [← CKSFrame.connection_normal, frame_connection_actual ha,
    frameCoefficient_torsion hmetric]
  change (∑ b : Fin 2, metricPair (foliationMetric (U x) (γ x) (s x))
    (actualFrameBracket (fun i y => adaptedFrame (U y) (γ y) (s y) i) x 0 a.succ)
    (adaptedFrame (U x) (γ x) (s x) b.succ) *
      (∑ i : Fin 2, α i * angularFrame (U x) (γ x) (s x) b i)) = _
  rw [tangential_frame_covector_expansion (s := s x) h0 hp.self_of_nhds]
  apply Finset.sum_congr rfl
  intro i _
  rw [adaptedFrame_normal_bracket (hU.differentiableAt (by simp)) (hs.differentiableAt (by simp))]

theorem physical_normal_covector_lie {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {α : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hα : DifferentiableAt ℝ α x) (a : Fin 2) :
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    D (E 0 x) (fun y => ∑ i : Fin 2, α y i * angularFrame (U y) (γ y) (s y) a i) x -
      (∑ b : Fin 2, (CKSFrame.connection c 0 a.succ b.succ - CKSFrame.chi c a b) *
        (∑ i : Fin 2, α x i * angularFrame (U x) (γ x) (s x) b i)) =
    ∑ i : Fin 2, U x * (D (CKSRealizedRound.basis 0) (fun y => α y i) x -
      ∑ j : Fin 2, (s x j * D (CKSRealizedRound.basis j.succ) (fun y => α y i) x +
        α x j * D (CKSRealizedRound.basis i.succ) (fun y => s y j) x)) *
          angularFrame (U x) (γ x) (s x) a i := by
  dsimp only
  have he := angularFrame_component_diff hU hγ hs hp.self_of_nhds
  have hal (i : Fin 2) : DifferentiableAt ℝ (fun y => α y i) x := differentiableAt_pi.mp hα i
  have hd (i : Fin 2) :
      D (foliationNormal (U x) (s x)) (fun y => α y i) x =
        U x * D (CKSRealizedRound.basis 0) (fun y => α y i) x -
        U x * ∑ j : Fin 2, s x j * D (CKSRealizedRound.basis j.succ) (fun y => α y i) x := by
    rw [D_direction_expansion, Fin.sum_univ_succ]
    change U x * D (CKSRealizedRound.basis 0) (fun y => α y i) x +
      (∑ j : Fin 2, foliationNormal (U x) (s x) j.succ *
        D (CKSRealizedRound.basis j.succ) (fun y => α y i) x) = _
    simp only [foliationNormal_succ, Fin.sum_univ_two]
    ring
  rw [physical_normal_tangential_connection hU hγ hs h0 hp]
  rw [D_angular_sum _ _ (fun i => (hal i).fun_mul (he a i))]
  simp only [adaptedFrame_first]
  simp_rw [D_mul _ (hal _) (he a _), hd, D_angular_direction]
  simp only [Fin.sum_univ_two]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma foliationTensor_hermitian (U L : ℝ) (η : Point) {T : Mat}
    (hT : T.IsHermitian) (s : Point) : (foliationTensor U L η T s).IsHermitian :=
  metricBlock_hermitian _ _ hT

lemma metricPair_foliationTensor_normal {U L : ℝ} (h0 : U ≠ 0)
    (η : Point) {T : Mat} (hT : T.IsHermitian) (s : Point) :
    metricPair (foliationTensor U L η T s) (foliationNormal U s) (foliationNormal U s) = L := by
  have h := foliationTensor_normal (L := L) h0 η hT s
  simpa only [metricPair, dotProduct, mulVec, star_apply, star_trivial,
    Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using h

lemma metricPair_foliationTensor_mixed {U L : ℝ} (h0 : U ≠ 0)
    (η : Point) {T : Mat} (hT : T.IsHermitian) (γ : Mat) (s : Point) (a : Fin 2) :
    metricPair (foliationTensor U L η T s) (foliationNormal U s) (adaptedFrame U γ s a.succ) =
      ∑ i : Fin 2, η i * angularFrame U γ s a i := by
  rw [metricPair_symm (foliationTensor_hermitian U L η hT s)]
  unfold metricPair
  rw [Fin.sum_univ_succ]
  simp only [adaptedFrame_radial, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (∑ j : Fin 3, foliationTensor U L η T s i.succ j * foliationNormal U s j) *
        angularFrame U γ s a i := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp only [angularFrame]
      ring
    _ = _ := by rw [foliationTensor_mixed h0]

lemma frameTensorData_eta (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (a : Fin 2) :
    (frameTensorData K E x).eta a = frameTensor K E x 0 a.succ := by
  fin_cases a <;> rfl

lemma frameTensorDerivative_eta (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (j : Fin 3) (a : Fin 2) :
    (frameTensorDerivativeData K E x j).eta a =
      D (E j x) (fun y => (frameTensorData K E y).eta a) x := by
  fin_cases a <;> rfl

lemma foliation_frame_tensor_eta {U L : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s η : PhysicalPoint → Point}
    {T : PhysicalPoint → Mat} {x : PhysicalPoint} (h0 : U x ≠ 0)
    (hT : (T x).IsHermitian) (a : Fin 2) :
    (frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x).eta a =
      ∑ i : Fin 2, η x i * angularFrame (U x) (γ x) (s x) a i := by
  rw [frameTensorData_eta]
  exact metricPair_foliationTensor_mixed h0 (η x) hT (γ x) (s x) a

lemma foliation_frame_tensor_tangential (U L : PhysicalPoint → ℝ)
    (γ : PhysicalPoint → Mat) (s η : PhysicalPoint → Point)
    (T : PhysicalPoint → Mat) (x : PhysicalPoint) (a b : Fin 2) :
    frameTensor (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x a.succ b.succ =
      angularTensorFrame U γ s T x a b := by
  unfold frameTensor
  rw [metricPair_tangential_slots _ _ _ (adaptedFrame_radial _ _ _ a) (adaptedFrame_radial _ _ _ b)]
  rfl

lemma angularTensorFrame_trace {U : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) :
    (∑ a : Fin 2, angularTensorFrame U γ s T x a a) = leafTensorTrace (γ x) (T x) := by
  unfold angularTensorFrame leafTensorTrace
  rw [angular_trace_transform, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, angularFrame_gram h0 hp]

lemma angularTensorFrame_metric {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (a b : Fin 2) :
    angularTensorFrame U γ s γ x a b = if a = b then 1 else 0 := by
  have ho := adaptedFrame_orthonormal h0 hp (s x) a.succ b.succ
  rw [metricPair_tangential_slots _ _ _ (adaptedFrame_radial _ _ _ a) (adaptedFrame_radial _ _ _ b)] at ho
  simpa only [angularTensorFrame, angularFrame, foliationMetric_angular, Fin.succ_inj] using ho

lemma angularTensorFrame_traceFree {U : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (a b : Fin 2) :
    angularTensorFrame U γ s (fun y => leafTensorTraceFree (γ y) (T y)) x a b =
      angularTensorFrame U γ s T x a b - leafTensorTrace (γ x) (T x) / 2 *
        (if a=b then 1 else 0) := by
  rw [← angularTensorFrame_metric h0 hp a b]
  simp only [angularTensorFrame, leafTensorTraceFree, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Fin.sum_univ_two]
  ring

lemma foliation_frame_tensor_trace {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) :
    (frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x).p = leafTensorTrace (γ x) (T x) := by
  change frameTensor _ _ x 1 1 + frameTensor _ _ x 2 2 = _
  have h := angularTensorFrame_trace (T := T) (s := s) h0 hp
  rw [Fin.sum_univ_two] at h
  rw [← foliation_frame_tensor_tangential U L γ s η T x 0 0,
    ← foliation_frame_tensor_tangential U L γ s η T x 1 1] at h
  exact h

lemma tensor_tau_entry (t : CKSFrame.TensorData) (a b : Fin 2) :
    CKSFrame.tau t a b = CKSFrame.tensor t a.succ b.succ - t.p / 2 *
      (if a=b then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> simp [CKSFrame.tau, CKSFrame.tensor]

lemma foliation_frame_tensor_tau {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (hT : (T x).IsHermitian) (a b : Fin 2) :
    CKSFrame.tau (frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) a b =
      angularTensorFrame U γ s (fun y => leafTensorTraceFree (γ y) (T y)) x a b := by
  rw [tensor_tau_entry, frameTensorData_exact _ (foliationTensor_hermitian _ _ _ hT _),
    foliation_frame_tensor_tangential, foliation_frame_tensor_trace h0 hp,
    angularTensorFrame_traceFree h0 hp]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma frameTensorDerivative_L (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (j : Fin 3) :
    (frameTensorDerivativeData K E x j).L =
      D (E j x) (fun y => (frameTensorData K E y).L) x := rfl

lemma frameTensorDerivative_p {K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hK : DifferentiableAt ℝ K x)
    (hE : ∀ i, DifferentiableAt ℝ (E i) x) (j : Fin 3) :
    (frameTensorDerivativeData K E x j).p =
      D (E j x) (fun y => (frameTensorData K E y).p) x := by
  exact (D_add _ (metricPair_differentiableAt hK (hE 1) (hE 1))
    (metricPair_differentiableAt hK (hE 2) (hE 2))).symm

lemma frameTensorDerivative_tau {K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hK : DifferentiableAt ℝ K x)
    (hE : ∀ i, DifferentiableAt ℝ (E i) x) (j : Fin 3) (a b : Fin 2) :
    CKSFrame.tau (frameTensorDerivativeData K E x j) a b =
      D (E j x) (fun y => CKSFrame.tau (frameTensorData K E y) a b) x := by
  have hf (i k : Fin 3) : DifferentiableAt ℝ (fun y => frameTensor K E y i k) x :=
    metricPair_differentiableAt hK (hE i) (hE k)
  have hd := D_div (E j x) ((hf 1 1).fun_sub (hf 2 2)) (differentiableAt_const (2 : ℝ)) (by norm_num)
  rw [D_sub _ (hf 1 1) (hf 2 2), D_const] at hd
  fin_cases a <;> fin_cases b
  · convert hd.symm using 1 <;>
      dsimp [CKSFrame.tau, frameTensorDerivativeData, frameTensorData, CKSFrame.extractTensor]
    ring
  · rfl
  · rfl
  · change -((D (E j x) (fun y => frameTensor K E y 1 1) x -
        D (E j x) (fun y => frameTensor K E y 2 2) x) / 2) =
      D (E j x) (fun y => -((frameTensor K E y 1 1 - frameTensor K E y 2 2) / 2)) x
    rw [show (fun y => -((frameTensor K E y 1 1 - frameTensor K E y 2 2) / 2)) =
      (fun y => (-1 : ℝ) * ((frameTensor K E y 1 1 - frameTensor K E y 2 2) / 2)) by funext y; ring,
      D_const_mul _ (-1) (diffAt_div ((hf 1 1).fun_sub (hf 2 2)) (differentiableAt_const 2) (by norm_num)), hd]
    ring

lemma foliationTensor_differentiableAt {U L : PhysicalPoint → ℝ}
    {T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hL : DifferentiableAt ℝ L x)
    (hT : DifferentiableAt ℝ T x) (hs : DifferentiableAt ℝ s x)
    (hη : DifferentiableAt ℝ η x) (h0 : U x ≠ 0) :
    DifferentiableAt ℝ (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)) x := by
  have hc (i j) : DifferentiableAt ℝ (fun y => T y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hT i) j
  have hsc (i) : DifferentiableAt ℝ (fun y => s y i) x := differentiableAt_pi.mp hs i
  have hec (i) : DifferentiableAt ℝ (fun y => η y i) x := differentiableAt_pi.mp hη i
  have hu1 : DifferentiableAt ℝ (fun y => 2 / U y) x := diffAt_div (differentiableAt_const 2) hU h0
  have hu2 : DifferentiableAt ℝ (fun y => L y / U y ^ 2) x := diffAt_div hL (hU.pow 2) (pow_ne_zero 2 h0)
  have heu (i) : DifferentiableAt ℝ (fun y => η y i / U y) x := diffAt_div (hec i) hU h0
  have ha : DifferentiableAt ℝ (fun y => L y / U y ^ 2 + 2 / U y *
      (∑ a : Fin 2, η y a * s y a) + ∑ a : Fin 2, ∑ b : Fin 2, T y a b * s y a * s y b) x := by
    simp only [Fin.sum_univ_two]
    fun_prop
  have hb (a : Fin 2) : DifferentiableAt ℝ (fun y => η y a / U y + ∑ b : Fin 2, T y a b * s y b) x := by
    simp only [Fin.sum_univ_two]
    fun_prop
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    first | exact ha | exact hb 0 | exact hb 1 | exact hc 0 0 | exact hc 0 1 | exact hc 1 0 | exact hc 1 1

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

lemma leafConnection_skew (c : CKSFrame.ConnectionData) (a b d : Fin 2) :
    CKSFrame.leafConnection c a b d = -CKSFrame.leafConnection c a d b := by
  fin_cases b <;> fin_cases d <;> simp [CKSFrame.leafConnection]

theorem physical_eta_divergence {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hη : DifferentiableAt ℝ η x)
    (h0 : U x ≠ 0) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hT : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) :
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    CKSFrame.etaDiv c (frameTensorData K E x) (frameTensorDerivativeData K E x) =
      covectorDiv (physicalAngularJet γ x) (fun i => physicalAngularScalarJet (fun y => η y i) x) := by
  dsimp only
  have he (a : Fin 2) :
      (fun y => (frameTensorData (fun z => foliationTensor (U z) (L z) (η z) (T z) (s z))
        (fun i z => adaptedFrame (U z) (γ z) (s z) i) y).eta a) =ᶠ[𝓝 x]
      (fun y => ∑ i : Fin 2, η y i * angularFrame (U y) (γ y) (s y) a i) := by
    filter_upwards [hU.continuousAt.eventually_ne h0, hT] with y huy hty
    exact foliation_frame_tensor_eta huy hty a
  rw [CKSFrame.etaDiv]
  simp only [frameTensorDerivative_eta, D_congr (he _)]
  simp only [(he _).self_of_nhds]
  have hh := physical_covector_divergence hU hγ hs h0 hp (fun i y => η y i)
    (fun i => differentiableAt_pi.mp hη i)
  dsimp only at hh
  rw [show covectorDiv (physicalAngularJet γ x)
      (fun i => physicalAngularScalarJet (fun y => η y i) x) =
        ∑ i : Fin 2, ∑ j : Fin 2, (γ x)⁻¹ i j *
          (D (CKSRealizedRound.basis i.succ) (fun y => η y j) x -
            ∑ k : Fin 2, christoffel (physicalAngularJet γ x) k i j * η x k) by
    simp only [covectorDiv, physicalAngularScalarJet, physicalAngularJet, inverse_eq]]
  rw [← hh]
  apply Finset.sum_congr rfl
  intro a _
  simp only [leafConnection_skew (a := a) (b := a), neg_mul,
    Finset.sum_neg_distrib, sub_neg_eq_add]

theorem physical_tau_divergence {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : DifferentiableAt ℝ L x)
    (hη : DifferentiableAt ℝ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : U x ≠ 0) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (a : Fin 2) :
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    CKSFrame.tauDiv c (frameTensorData K E x) (frameTensorDerivativeData K E x) a =
      ∑ k : Fin 2, tensorDiv (physicalAngularJet γ x)
        (fun i j => physicalAngularScalarJet (fun y => leafTensorTraceFree (γ y) (T y) i j) x) k *
          angularFrame (U x) (γ x) (s x) a k := by
  dsimp only
  have he (a b : Fin 2) :
      (fun y => CKSFrame.tau (frameTensorData (fun z => foliationTensor (U z) (L z) (η z) (T z) (s z))
        (fun i z => adaptedFrame (U z) (γ z) (s z) i) y) a b) =ᶠ[𝓝 x]
      (fun y => angularTensorFrame U γ s (fun z => leafTensorTraceFree (γ z) (T z)) y a b) := by
    filter_upwards [hU.continuousAt.eventually_ne h0, hp, hTs] with y huy hpy hty
    exact foliation_frame_tensor_tau huy hpy hty a b
  have hk := foliationTensor_differentiableAt (hU.differentiableAt (by simp)) hL
    (hT.differentiableAt (by simp)) (hs.differentiableAt (by simp)) hη h0
  have hE (i : Fin 3) := (adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds i).differentiableAt (by simp)
  rw [CKSFrame.tauDiv]
  simp only [frameTensorDerivative_tau hk hE, D_congr (he _ _), (he _ _).self_of_nhds]
  exact physical_leaf_tensor_divergence hU hγ hs h0 hp
    ((leafTensorTraceFree_contDiffAt hγ hT hp.self_of_nhds).differentiableAt (by simp)) a

theorem physical_eta_normal_lie {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hη : DifferentiableAt ℝ η x)
    (h0 : U x ≠ 0) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hT : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (a : Fin 2) :
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    CKSFrame.normalLieEta c (frameTensorData K E x) (frameTensorDerivativeData K E x) a =
      ∑ i : Fin 2, U x * (D (CKSRealizedRound.basis 0) (fun y => η y i) x -
        covectorLie (fun j => physicalAngularScalarJet (fun y => s y j) x)
          (fun j => physicalAngularScalarJet (fun y => η y j) x) i) *
            angularFrame (U x) (γ x) (s x) a i := by
  dsimp only
  have he (a : Fin 2) :
      (fun y => (frameTensorData (fun z => foliationTensor (U z) (L z) (η z) (T z) (s z))
        (fun i z => adaptedFrame (U z) (γ z) (s z) i) y).eta a) =ᶠ[𝓝 x]
      (fun y => ∑ i : Fin 2, η y i * angularFrame (U y) (γ y) (s y) a i) := by
    filter_upwards [hU.continuousAt.eventually_ne h0, hT] with y huy hty
    exact foliation_frame_tensor_eta huy hty a
  rw [CKSFrame.normalLieEta, frameTensorDerivative_eta, D_congr (he a)]
  simp only [(he _).self_of_nhds]
  exact physical_normal_covector_lie hU hγ hs h0 hp hη a

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma angularTensorFrame_pair {U : PhysicalPoint → ℝ}
    {γ X T : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) :
    (∑ a : Fin 2, ∑ b : Fin 2,
      angularTensorFrame U γ s X x a b * angularTensorFrame U γ s T x a b) =
      tensorPair (physicalAngularJet γ x) (X x) (T x) := by
  have hg (i j : Fin 2) :
      (∑ a : Fin 2, angularFrame (U x) (γ x) (s x) a i *
        angularFrame (U x) (γ x) (s x) a j) = (γ x)⁻¹ i j :=
    congrFun (congrFun (angularFrame_gram h0 hp) i) j
  calc
    _ = ∑ i : Fin 2, ∑ k : Fin 2, ∑ j : Fin 2, ∑ l : Fin 2,
        (∑ a : Fin 2, angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) a j) *
        (∑ b : Fin 2, angularFrame (U x) (γ x) (s x) b k * angularFrame (U x) (γ x) (s x) b l) *
        X x i k * T x j l := by
      simp only [angularTensorFrame, Fin.sum_univ_two]
      ring
    _ = _ := by simp only [hg, tensorPair, physicalAngularJet, inverse_eq]

lemma angularTensorFrame_covector {U : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (B : Point) (a : Fin 2) :
    (∑ b : Fin 2, angularTensorFrame U γ s T x b a *
      (∑ k : Fin 2, B k * angularFrame (U x) (γ x) (s x) b k)) =
      ∑ j : Fin 2, (∑ i : Fin 2, ∑ k : Fin 2, T x i j * (γ x)⁻¹ i k * B k) *
        angularFrame (U x) (γ x) (s x) a j := by
  have hg (i j : Fin 2) :
      (∑ b : Fin 2, angularFrame (U x) (γ x) (s x) b i *
        angularFrame (U x) (γ x) (s x) b j) = (γ x)⁻¹ i j :=
    congrFun (congrFun (angularFrame_gram h0 hp) i) j
  calc
    _ = ∑ j : Fin 2, (∑ i : Fin 2, ∑ k : Fin 2, T x i j *
        (∑ b : Fin 2, angularFrame (U x) (γ x) (s x) b i * angularFrame (U x) (γ x) (s x) b k) * B k) *
        angularFrame (U x) (γ x) (s x) a j := by
      simp only [angularTensorFrame, Fin.sum_univ_two]
      ring
    _ = _ := by simp only [hg]

lemma physical_shear_components {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a b : Fin 2) :
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    CKSFrame.chi c a b - CKSFrame.mean c / 2 * (if a=b then 1 else 0) =
      angularTensorFrame U γ s (fun y => leafTensorTraceFree (γ y) (sourceChi U γ s y)) x a b := by
  dsimp only
  rw [angularTensorFrame_traceFree h0.ne' hp.self_of_nhds,
    physical_chi_representation hU hγ hs h0 hp,
    physical_mean_curvature hU hγ hs h0 hp]
  rfl

lemma shearNormSq_sum (c : CKSFrame.ConnectionData) :
    CKSFrame.shearNormSq c = ∑ a : Fin 2, ∑ b : Fin 2,
      (CKSFrame.chi c a b - CKSFrame.mean c / 2 * (if a=b then 1 else 0)) *
      (CKSFrame.chi c a b - CKSFrame.mean c / 2 * (if a=b then 1 else 0)) := by
  simp [CKSFrame.shearNormSq, CKSFrame.chi, Fin.sum_univ_two]
  ring

lemma tauNormSq_sum (t : CKSFrame.TensorData) :
    CKSFrame.tauNormSq t = ∑ a : Fin 2, ∑ b : Fin 2, CKSFrame.tau t a b * CKSFrame.tau t a b := by
  simp [CKSFrame.tauNormSq, CKSFrame.tau, Fin.sum_univ_two]
  ring

lemma shearTau_sum (c : CKSFrame.ConnectionData) (t : CKSFrame.TensorData) :
    CKSFrame.shearTau c t = ∑ a : Fin 2, ∑ b : Fin 2,
      (CKSFrame.chi c a b - CKSFrame.mean c / 2 * (if a=b then 1 else 0)) * CKSFrame.tau t a b := by
  simp [CKSFrame.shearTau, CKSFrame.chi, CKSFrame.tau, Fin.sum_univ_two]
  ring

lemma physical_shear_norm {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    let X := leafTensorTraceFree (γ x) (sourceChi U γ s x)
    CKSFrame.shearNormSq c = tensorPair (physicalAngularJet γ x) X X := by
  dsimp only
  rw [shearNormSq_sum]
  simp only [physical_shear_components hU hγ hs h0 hp]
  exact angularTensorFrame_pair h0.ne' hp.self_of_nhds

lemma physical_tau_norm {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (hT : (T x).IsHermitian) :
    let t := frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    let τ := leafTensorTraceFree (γ x) (T x)
    CKSFrame.tauNormSq t = tensorPair (physicalAngularJet γ x) τ τ := by
  dsimp only
  rw [tauNormSq_sum]
  simp only [foliation_frame_tensor_tau h0 hp hT]
  exact angularTensorFrame_pair h0 hp

lemma physical_shear_tau {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (hT : (T x).IsHermitian) :
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    let t := frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    CKSFrame.shearTau c t = tensorPair (physicalAngularJet γ x)
      (leafTensorTraceFree (γ x) (sourceChi U γ s x)) (leafTensorTraceFree (γ x) (T x)) := by
  dsimp only
  rw [shearTau_sum]
  simp only [physical_shear_components hU hγ hs h0 hp, foliation_frame_tensor_tau h0.ne' hp.self_of_nhds hT]
  exact angularTensorFrame_pair h0.ne' hp.self_of_nhds

lemma physical_eta_norm {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (hT : (T x).IsHermitian) :
    let t := frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    CKSFrame.etaNormSq t = covectorPair (physicalAngularJet γ x) (η x) (η x) := by
  dsimp only
  rw [CKSFrame.etaNormSq]
  simp only [foliation_frame_tensor_eta h0 hT]
  have h := angular_frame_covector_contract (s := s x) h0 hp (η x) (η x)
  simp only [Fin.sum_univ_two] at h
  simpa only [pow_two, covectorPair, physicalAngularJet, inverse_eq, Fin.sum_univ_two] using h

lemma physical_eta_acceleration {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (hT : (T x).IsHermitian) :
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    let t := frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    CKSFrame.etaAcceleration c t = covectorPair (physicalAngularJet γ x) (η x)
      (fun i => D (CKSRealizedRound.basis i.succ) U x / U x) := by
  dsimp only
  rw [CKSFrame.etaAcceleration]
  simp only [foliation_frame_tensor_eta h0.ne' hT, physical_acceleration_components
    (hU.differentiableAt (by simp)) (hγ.differentiableAt (by simp)) (hs.differentiableAt (by simp)) h0 hp]
  simpa only [covectorPair, physicalAngularJet, inverse_eq] using
    angular_frame_covector_contract (s := s x) h0.ne' hp.self_of_nhds (η x)
      (fun i => D (CKSRealizedRound.basis i.succ) U x / U x)

lemma accelTensor_traceFree (c : CKSFrame.ConnectionData) (t : CKSFrame.TensorData) (a : Fin 2) :
    CKSFrame.accelTensor c t a = (t.L-t.p/2)*c.B a - ∑ b, CKSFrame.tau t b a*c.B b := by
  fin_cases a <;> simp [CKSFrame.accelTensor, CKSFrame.tau, CKSFrame.tangential, Fin.sum_univ_two] <;> ring

lemma foliation_frame_tensor_L {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hT : (T x).IsHermitian) :
    (frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x).L = L x :=
  metricPair_foliationTensor_normal h0 (η x) hT (s x)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physical_mean_curvature_C1 {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    CKSFrame.mean (frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) =
      leafTensorTrace (γ x) (sourceChi U γ s x) := by
  simp only [CKSFrame.mean, frameConnectionField, CKSFrame.extractConnection]
  rw [show (1 : Fin 3) = (0 : Fin 2).succ from rfl,
    show (2 : Fin 3) = (1 : Fin 2).succ from rfl,
    leaf_frame_chi hU hγ hs h0 hp, leaf_frame_chi hU hγ hs h0 hp]
  exact (Fin.sum_univ_two (fun a => angularTensorFrame U γ s (sourceChi U γ s) x a a)).symm.trans
    (angularTensorFrame_trace h0.ne' hp.self_of_nhds)

lemma physical_normal_mean {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField G E
    CKSFrame.normalMean (fun a => connectionFieldDerivative c (E a x) x) =
      D (E 0 x) (fun y => leafTensorTrace (γ y) (sourceChi U γ s y)) x := by
  dsimp only
  have hu1 : ContDiffAt ℝ 1 U x := hU.of_le (by simp)
  have hg1 : ContDiffAt ℝ 1 γ x := hγ.of_le (by simp)
  have hs1 : ContDiffAt ℝ 1 s x := hs.of_le (by simp)
  have hnear : ∀ᶠ y in 𝓝 x, 0 < U y := hU.continuousAt.eventually (lt_mem_nhds h0)
  have heq : (fun y => CKSFrame.mean (frameConnectionField
      (fun z => foliationMetric (U z) (γ z) (s z))
      (fun i z => adaptedFrame (U z) (γ z) (s z) i) y)) =ᶠ[𝓝 x]
      (fun y => leafTensorTrace (γ y) (sourceChi U γ s y)) := by
    filter_upwards [hu1.eventually (by norm_num), hg1.eventually (by norm_num),
      hs1.eventually (by norm_num), hnear, hp.eventually_nhds] with y hyu hyg hys hyp hpg
    exact physical_mean_curvature_C1 (hyu.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) (hys.differentiableAt (by norm_num)) hyp hpg
  have hG := foliationMetric_contDiffAt hU hγ hs h0.ne'
  have hdet := (foliationMetric_posDef h0.ne' hp.self_of_nhds (s x)).det_pos.ne'
  have hE (i : Fin 3) := adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds i
  have hc (i j k : Fin 3) := (frameCoefficient_contDiffAt hG hdet hE i j k).differentiableAt (by simp)
  simp only [CKSFrame.normalMean, connectionFieldDerivative]
  have hd1 : DifferentiableAt ℝ (fun y => (frameConnectionField
      (fun z => foliationMetric (U z) (γ z) (s z))
      (fun i z => adaptedFrame (U z) (γ z) (s z) i) y).chi11) x := hc 1 0 1
  have hd2 : DifferentiableAt ℝ (fun y => (frameConnectionField
      (fun z => foliationMetric (U z) (γ z) (s z))
      (fun i z => adaptedFrame (U z) (γ z) (s z) i) y).chi22) x := hc 2 0 2
  rw [← D_add _ hd1 hd2]
  exact D_congr heq _

lemma physical_tensor_derivative_L {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContinuousAt U x) (h0 : U x ≠ 0)
    (hT : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (j : Fin 3) :
    (frameTensorDerivativeData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x j).L =
      D (adaptedFrame (U x) (γ x) (s x) j) L x := by
  rw [frameTensorDerivative_L]
  apply D_congr
  filter_upwards [hU.eventually_ne h0, hT] with y hy hty
  exact foliation_frame_tensor_L hy hty

lemma physical_tensor_derivative_p {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : DifferentiableAt ℝ L x)
    (hT : DifferentiableAt ℝ T x) (hη : DifferentiableAt ℝ η x)
    (h0 : U x ≠ 0) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (j : Fin 3) :
    (frameTensorDerivativeData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x j).p =
      D (adaptedFrame (U x) (γ x) (s x) j) (fun y => leafTensorTrace (γ y) (T y)) x := by
  have hk := foliationTensor_differentiableAt (hU.differentiableAt (by simp)) hL
    hT (hs.differentiableAt (by simp)) hη h0
  have hE (i : Fin 3) := (adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds i).differentiableAt (by simp)
  rw [frameTensorDerivative_p hk hE]
  apply D_congr
  filter_upwards [hU.continuousAt.eventually_ne h0, hp] with y hy hpy
  exact foliation_frame_tensor_trace hy hpy

lemma physical_tensor_tangential_trace_derivative {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : DifferentiableAt ℝ L x)
    (hT : ContDiffAt ℝ ∞ T x) (hη : DifferentiableAt ℝ η x)
    (h0 : U x ≠ 0) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (a : Fin 2) :
    let dt := frameTensorDerivativeData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    (dt a.succ).L + (dt a.succ).p / 2 =
      ∑ i : Fin 2, ((physicalAngularScalarJet L x).2.1 i +
        (physicalAngularScalarJet (fun y => leafTensorTrace (γ y) (T y) / 2) x).2.1 i) *
          angularFrame (U x) (γ x) (s x) a i := by
  dsimp only
  rw [physical_tensor_derivative_L hU.continuousAt h0 hTs,
    physical_tensor_derivative_p hU hγ hs hL (hT.differentiableAt (by simp)) hη h0 hp]
  have hd := (leafTensorTrace_contDiffAt hγ hT hp.self_of_nhds).differentiableAt (by simp)
  have hdiv (v : PhysicalPoint) :
      D v (fun y => leafTensorTrace (γ y) (T y) / 2) x =
        D v (fun y => leafTensorTrace (γ y) (T y)) x / 2 := by
    rw [D_div v hd (differentiableAt_const 2) (by norm_num), D_const]
    ring
  simp only [D_angular_direction, physicalAngularScalarJet, hdiv, Fin.sum_univ_two]
  ring

lemma physical_acceleration_tensor {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (hT : (T x).IsHermitian) (a : Fin 2) :
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    let t := frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    let B := fun i => D (CKSRealizedRound.basis i.succ) U x / U x
    CKSFrame.accelTensor c t a =
      ∑ j : Fin 2, ((L x - leafTensorTrace (γ x) (T x) / 2) * B j -
        ∑ i : Fin 2, ∑ k : Fin 2, leafTensorTraceFree (γ x) (T x) i j * (γ x)⁻¹ i k * B k) *
          angularFrame (U x) (γ x) (s x) a j := by
  dsimp only
  rw [accelTensor_traceFree, foliation_frame_tensor_L h0.ne' hT,
    foliation_frame_tensor_trace h0.ne' hp.self_of_nhds]
  simp only [foliation_frame_tensor_tau h0.ne' hp.self_of_nhds hT,
    physical_acceleration_components (hU.differentiableAt (by simp))
      (hγ.differentiableAt (by simp)) (hs.differentiableAt (by simp)) h0 hp]
  rw [angularTensorFrame_covector h0.ne' hp.self_of_nhds]
  simp only [Fin.sum_univ_two]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLeafCalculus
noncomputable section
open Matrix CKSCalculus CKSAngularGeometry Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

abbrev A := Fin 2
abbrev P := PhysicalPoint
abbrev Vect := CKSAngularGeometry.Point
abbrev Symbols := A → A → A → ℝ

def lift (v : Vect) : P := Fin.cases 0 v

def delta (v : Vect) (f : P → ℝ) (x : P) : ℝ := D (lift v) f x

lemma delta_expansion (v : Vect) (f : P → ℝ) (x : P) :
    delta v f x = ∑ i : A, v i * D (CKSRealizedRound.basis i.succ) f x := by
  rw [delta, D_direction_expansion, Fin.sum_univ_succ]
  simp only [lift, Fin.cases_zero, Fin.cases_succ, zero_mul, zero_add]

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
  D_angular_sum _ f hf

def bracket (V W : P → Vect) (x : P) : Vect := fun k =>
  delta (V x) (fun y => W y k) x - delta (W x) (fun y => V y k) x

lemma delta_moving (v : Vect) {W : P → Vect} {f : P → ℝ} {x : P}
    (hW : DifferentiableAt ℝ W x) (hf : ContDiffAt ℝ 2 f x) :
    delta v (fun y => delta (W y) f y) x =
      ∑ i : A, (W x i * delta v (D (CKSRealizedRound.basis i.succ) f) x +
        D (CKSRealizedRound.basis i.succ) f x * delta v (fun y => W y i) x) := by
  have hWi (i : A) := differentiableAt_pi.mp hW i
  have hfi (i : A) : DifferentiableAt ℝ (D (CKSRealizedRound.basis i.succ) f) x :=
    (contDiffAt_D hf (m := 1) (by norm_num) _).differentiableAt (by norm_num)
  simp only [delta_expansion (W _)]
  rw [delta_sum _ (fun i y => W y i * D (CKSRealizedRound.basis i.succ) f y)
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
  simp only [delta_expansion, bracket, Fin.sum_univ_two]
  rw [D_comm hf (CKSRealizedRound.basis (0 : A).succ)
    (CKSRealizedRound.basis (1 : A).succ)]
  ring

def nabla (Γ : P → Symbols) (v : Vect) (W : P → Vect) (x : P) : Vect := fun k =>
  delta v (fun y => W y k) x + ∑ i : A, ∑ j : A, v i * W x j * Γ x k i j

def curvature (Γ : P → Symbols) (V W Z : P → Vect) (x : P) : Vect :=
  nabla Γ (V x) (fun y => nabla Γ (W y) Z y) x -
    nabla Γ (W x) (fun y => nabla Γ (V y) Z y) x - nabla Γ (bracket V W x) Z x

def coordCurvature (Γ : P → Symbols) (x : P) (k l i j : A) : ℝ :=
  D (CKSRealizedRound.basis i.succ) (fun y => Γ y k j l) x -
    D (CKSRealizedRound.basis j.succ) (fun y => Γ y k i l) x +
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
      (D (CKSRealizedRound.basis i.succ) (fun y => Z y j)) x :=
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
  simp only [nabla, coordCurvature, bracket, delta_expansion, Fin.sum_univ_two]
  ring

lemma nabla_congr {Γ : P → Symbols} {v : Vect} {W Z : P → Vect} {x : P}
    (h : W =ᶠ[𝓝 x] Z) : nabla Γ v W x = nabla Γ v Z x := by
  ext k
  simp only [nabla, h.self_of_nhds]
  congr 1
  apply D_congr
  filter_upwards [h] with y hy
  rw [hy]

lemma nabla_expansion {Γ : P → Symbols} (v : Vect) {x : P}
    {F : A → P → ℝ} {E : A → P → Vect}
    (hF : ∀ a, DifferentiableAt ℝ (F a) x)
    (hE : ∀ a, DifferentiableAt ℝ (E a) x) (k : A) :
    nabla Γ v (fun y k => ∑ m : A, F m y * E m y k) x k =
      ∑ m : A, (delta v (F m) x * E m x k + F m x * nabla Γ v (E m) x k) := by
  change delta v (fun y => ∑ m : A, F m y * E m y k) x + _ = _
  rw [delta_sum v _ (fun m => (hF m).fun_mul (differentiableAt_pi.mp (hE m) k))]
  simp_rw [delta_mul v (hF _) (differentiableAt_pi.mp (hE _) k)]
  simp only [nabla, Fin.sum_univ_two]
  ring

lemma nabla_direction_expansion (Γ : P → Symbols) (f : A → ℝ) (E : A → Vect)
    (Z : P → Vect) (x : P) (k : A) :
    nabla Γ (fun i => ∑ a : A, f a * E a i) Z x k =
      ∑ a : A, f a * nabla Γ (E a) Z x k := by
  simp only [nabla, delta_expansion, Fin.sum_univ_two]
  ring

lemma nabla_torsion {Γ : P → Symbols} {V W : P → Vect} {x : P}
    (hs : ∀ k i j, Γ x k i j = Γ x k j i) :
    nabla Γ (V x) W x - nabla Γ (W x) V x = bracket V W x := by
  ext k
  simp only [nabla, bracket, Pi.sub_apply, Fin.sum_univ_two]
  rw [hs k 1 0]
  ring

def frameCurvature (F : P → Symbols) (E : A → P → Vect) (x : P)
    (a b d c : A) : ℝ :=
  delta (E a x) (fun y => F y b d c) x - delta (E b x) (fun y => F y a d c) x +
    ∑ m : A, (F x b d m * F x a m c - F x a d m * F x b m c -
      (F x a b m - F x b a m) * F x m d c)

lemma nabla_second_frame {Γ F : P → Symbols} {E : A → P → Vect} {x : P}
    (hF : ∀ a b c, DifferentiableAt ℝ (fun y => F y a b c) x)
    (hE : ∀ a, DifferentiableAt ℝ (E a) x)
    (hc : ∀ᶠ y in 𝓝 x, ∀ a b k,
      nabla Γ (E a y) (E b) y k = ∑ c : A, F y a b c * E c y k)
    (a b d k : A) :
    nabla Γ (E a x) (fun y => nabla Γ (E b y) (E d) y) x k =
      ∑ m : A, (delta (E a x) (fun y => F y b d m) x * E m x k +
        F x b d m * ∑ c : A, F x a m c * E c x k) := by
  have h : (fun y => nabla Γ (E b y) (E d) y) =ᶠ[𝓝 x]
      (fun y k => ∑ c : A, F y b d c * E c y k) := by
    filter_upwards [hc] with y hy
    exact funext (hy b d)
  rw [nabla_congr h, nabla_expansion _ (hF b d) hE]
  simp only [hc.self_of_nhds]

theorem curvature_frame {Γ F : P → Symbols} {E : A → P → Vect} {x : P}
    (hF : ∀ a b c, DifferentiableAt ℝ (fun y => F y a b c) x)
    (hE : ∀ a, DifferentiableAt ℝ (E a) x)
    (hs : ∀ k i j, Γ x k i j = Γ x k j i)
    (hc : ∀ᶠ y in 𝓝 x, ∀ a b k,
      nabla Γ (E a y) (E b) y k = ∑ c : A, F y a b c * E c y k)
    (a b d k : A) :
    curvature Γ (E a) (E b) (E d) x k =
      ∑ c : A, frameCurvature F E x a b d c * E c x k := by
  have hb : bracket (E a) (E b) x =
      fun i => ∑ m : A, (F x a b m - F x b a m) * E m x i := by
    rw [← nabla_torsion hs]
    ext i
    simp only [Pi.sub_apply, hc.self_of_nhds, Fin.sum_univ_two]
    ring
  change nabla Γ (E a x) (fun y => nabla Γ (E b y) (E d) y) x k -
    nabla Γ (E b x) (fun y => nabla Γ (E a y) (E d) y) x k -
    nabla Γ (bracket (E a) (E b) x) (E d) x k = _
  rw [nabla_second_frame hF hE hc, nabla_second_frame hF hE hc, hb,
    nabla_direction_expansion]
  simp only [hc.self_of_nhds, frameCurvature, Fin.sum_univ_two]
  ring

end
end CKSLeafCalculus

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped BigOperators Topology ContDiff NNReal Matrix.Norms.Elementwise
lemma physical_component_diff {q : PhysicalPoint → Mat} {x : PhysicalPoint} (hq : ContDiffAt ℝ 2 q x) (i k : I) :
    ContDiffAt ℝ 2 (fun y => q y i k) x := by
  exact contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k

lemma physical_inverse_component_diff {q : PhysicalPoint → Mat} {x : PhysicalPoint} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) (i k : I) :
    DifferentiableAt ℝ (fun y => inverse (q y) i k) x := by
  unfold inverse
  apply CKSCalculus.diffAt_div
  · fin_cases i <;> fin_cases k <;> dsimp <;>
      first | exact (physical_component_diff hq _ _).differentiableAt (by norm_num)
            | exact ((physical_component_diff hq _ _).differentiableAt (by norm_num)).neg
  · exact ((determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq).differentiableAt (by norm_num)
  · exact h0

lemma physical_D_determinant {q : PhysicalPoint → Mat} {x : PhysicalPoint} (hq : ContDiffAt ℝ 2 q x) (e : PhysicalPoint) :
    D e (fun y => determinant (q y)) x =
      q x 0 0 * D e (fun y => q y 1 1) x + q x 1 1 * D e (fun y => q y 0 0) x -
      (q x 0 1 * D e (fun y => q y 1 0) x + q x 1 0 * D e (fun y => q y 0 1) x) := by
  have hd i k := (physical_component_diff hq i k).differentiableAt (by norm_num)
  unfold determinant
  rw [D_sub e ((hd 0 0).fun_mul (hd 1 1)) ((hd 0 1).fun_mul (hd 1 0)),
    D_mul e (hd 0 0) (hd 1 1), D_mul e (hd 0 1) (hd 1 0)]

theorem physical_derivative_inverse {q : PhysicalPoint → Mat} {x : PhysicalPoint} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) (s a b : I) :
    D (CKSRealizedRound.basis s.succ) (fun y => inverse (q y) a b) x =
      inverseDerivative (physicalAngularJet q x) s a b := by
  have hd i k := (physical_component_diff hq i k).differentiableAt (by norm_num)
  have hdet : DifferentiableAt ℝ (fun y => determinant (q y)) x :=
    ((determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq).differentiableAt (by norm_num)
  have hdneg i k : D (CKSRealizedRound.basis s.succ) (fun y => -(q y i k)) x =
      - D (CKSRealizedRound.basis s.succ) (fun y => q y i k) x := by
    unfold D
    rw [fderiv_fun_neg]
    rfl
  unfold inverseDerivative
  simp only [physicalAngularJet, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> dsimp [inverse] <;>
    rw [D_div _ (by first | exact hd _ _ | exact (hd _ _).neg) hdet h0, physical_D_determinant hq] <;>
    (try rw [hdneg]) <;> dsimp [inverse,determinant] <;> field_simp <;> ring

lemma physical_D_sum {α : Type*} (u : Finset α) (f : α → PhysicalPoint → ℝ) (e x : PhysicalPoint)
    (hf : ∀ i ∈ u, DifferentiableAt ℝ (f i) x) :
    D e (fun y => ∑ i ∈ u, f i y) x = ∑ i ∈ u, D e (f i) x := by
  simp only [D, fderiv_fun_sum hf, sum_apply]

lemma physical_D_div_const (e : PhysicalPoint) {f : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    D e (fun y => f y/c) x = D e f x/c := by
  simp only [div_eq_mul_inv]
  rw [D_mul e hf (differentiableAt_const _),D_const]
  ring

lemma physical_first_diff {q : PhysicalPoint → Mat} {x : PhysicalPoint} (hq : ContDiffAt ℝ 2 q x) (a i k : I) :
    DifferentiableAt ℝ (D (CKSRealizedRound.basis a.succ) (fun y => q y i k)) x :=
  (contDiffAt_D (physical_component_diff hq i k) (m := 1) (by norm_num) (CKSRealizedRound.basis a.succ)).differentiableAt (by norm_num)

theorem physical_derivative_connection {q : PhysicalPoint → Mat} {x : PhysicalPoint} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) (s a i k : I) :
    D (CKSRealizedRound.basis s.succ) (fun y => christoffel (physicalAngularJet q y) a i k) x = christoffelDerivative (physicalAngularJet q x) s a i k := by
  let b (l : I) (y : PhysicalPoint) :=
    D (CKSRealizedRound.basis i.succ) (fun z => q z k l) y + D (CKSRealizedRound.basis k.succ) (fun z => q z i l) y - D (CKSRealizedRound.basis l.succ) (fun z => q z i k) y
  have hb l : DifferentiableAt ℝ (b l) x :=
    ((physical_first_diff hq i k l).fun_add (physical_first_diff hq k i l)).fun_sub (physical_first_diff hq l i k)
  have hterm l : DifferentiableAt ℝ (fun y => inverse (q y) a l * b l y) x :=
    (physical_inverse_component_diff hq h0 a l).fun_mul (hb l)
  have hsum : DifferentiableAt ℝ (fun y => ∑ l : I, inverse (q y) a l*b l y) x :=
    DifferentiableAt.fun_sum fun l hl => hterm l
  change D (CKSRealizedRound.basis s.succ) (fun y => (∑ l : I, inverse (q y) a l*b l y)/2) x = _
  rw [physical_D_div_const _ hsum]
  have hdsum := physical_D_sum Finset.univ (fun l y => inverse (q y) a l*b l y) (CKSRealizedRound.basis s.succ) x (fun l hl => hterm l)
  rw [hdsum]
  unfold christoffelDerivative
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [D_mul _ (physical_inverse_component_diff hq h0 a l) (hb l), physical_derivative_inverse hq h0]
  have hdb : D (CKSRealizedRound.basis s.succ) (b l) x =
      D (CKSRealizedRound.basis s.succ) (D (CKSRealizedRound.basis i.succ) (fun y => q y k l)) x +
      D (CKSRealizedRound.basis s.succ) (D (CKSRealizedRound.basis k.succ) (fun y => q y i l)) x -
      D (CKSRealizedRound.basis s.succ) (D (CKSRealizedRound.basis l.succ) (fun y => q y i k)) x := by
    dsimp [b]
    rw [D_sub _ ((physical_first_diff hq i k l).fun_add (physical_first_diff hq k i l)) (physical_first_diff hq l i k),
      D_add _ (physical_first_diff hq i k l) (physical_first_diff hq k i l)]
  rw [hdb]
  dsimp [physicalAngularJet,b]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLeafCalculus
noncomputable section
open Matrix CKSAngularGeometry
open scoped BigOperators

def pair (γ : Mat) (v w : Vect) : ℝ := ∑ i : A, ∑ j : A, γ i j * v i * w j

lemma pair_frame_sum (γ : Mat) (E : A → Vect)
    (ho : ∀ a b, pair γ (E a) (E b) = if a = b then 1 else 0)
    (f : A → ℝ) (a : A) :
    pair γ (fun k => ∑ c : A, f c * E c k) (E a) = f a := by
  calc
    _ = ∑ c : A, f c * pair γ (E c) (E a) := by
      simp only [pair, Fin.sum_univ_two]
      ring
    _ = _ := by simp [ho]

lemma inverse_metric_trace {γ : Mat} (hp : γ.PosDef) (k i : A) :
    (∑ m : A, γ k m * γ⁻¹ i m) = if k = i then 1 else 0 := by
  have h : (γ * γ⁻¹) k i = (1 : Mat) k i :=
    congrFun (congrFun (Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hp.det_pos.ne')) k) i
  simpa only [Matrix.mul_apply, inverse_symm_entry hp, Matrix.one_apply] using h

theorem scalar_frame_contraction {γ : Mat} (hp : γ.PosDef) (E : A → Vect)
    (hg : ∀ i j, (∑ a : A, E a i * E a j) = γ⁻¹ i j)
    (R : A → A → A → A → ℝ) :
    (∑ a : A, ∑ b : A, pair γ
      (fun k => ∑ i : A, ∑ j : A, ∑ l : A, E a i * E b j * E b l * R k l i j)
      (E a)) = ∑ j : A, ∑ l : A, γ⁻¹ j l * ∑ k : A, R k l k j := by
  calc
    _ = ∑ k : A, ∑ i : A, ∑ j : A, ∑ l : A,
        (∑ m : A, γ k m * (∑ a : A, E a i * E a m)) *
          (∑ b : A, E b j * E b l) * R k l i j := by
      simp only [pair, Fin.sum_univ_two]
      ring
    _ = ∑ k : A, ∑ i : A, ∑ j : A, ∑ l : A,
        (if k = i then 1 else 0) * γ⁻¹ j l * R k l i j := by
      simp only [hg, inverse_metric_trace hp]
    _ = _ := by
      simp only [Fin.sum_univ_two]
      simp
      ring

end
end CKSLeafCalculus

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSLeafCalculus
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma lift_angularFrame (U : ℝ) (γ : Mat) (s : Point) (a : Fin 2) :
    lift (angularFrame U γ s a) = adaptedFrame U γ s a.succ := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (adaptedFrame_radial U γ s a).symm
  · rfl

lemma leafConnection_derivative (c : PhysicalPoint → CKSFrame.ConnectionData)
    (e x : PhysicalPoint) (a b d : Fin 2) :
    CKSFrame.leafConnection (connectionFieldDerivative c e x) a b d =
      D e (fun y => CKSFrame.leafConnection (c y) a b d) x := by
  fin_cases b <;> fin_cases d <;>
    simp [CKSFrame.leafConnection, connectionFieldDerivative, D, fderiv_fun_neg]

lemma physical_christoffel_differentiable {γ : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ 2 γ x) (hp : (γ x).PosDef) :
    DifferentiableAt ℝ (fun y => christoffel (physicalAngularJet γ y)) x := by
  have h0 : determinant (γ x) ≠ 0 := by rw [determinant_eq]; exact hp.det_pos.ne'
  refine differentiableAt_pi.mpr fun a => differentiableAt_pi.mpr fun i =>
    differentiableAt_pi.mpr fun k => ?_
  change DifferentiableAt ℝ (fun y => (∑ l : Fin 2, inverse (γ y) a l *
    (D (CKSRealizedRound.basis i.succ) (fun z => γ z k l) y +
      D (CKSRealizedRound.basis k.succ) (fun z => γ z i l) y -
      D (CKSRealizedRound.basis l.succ) (fun z => γ z i k) y)) / 2) x
  apply diffAt_div _ (differentiableAt_const (2 : ℝ)) (by norm_num)
  exact DifferentiableAt.fun_sum fun l _ =>
    (physical_inverse_component_diff hγ h0 a l).fun_mul
      (((physical_first_diff hγ i k l).fun_add (physical_first_diff hγ k i l)).fun_sub
        (physical_first_diff hγ l i k))

lemma physical_christoffel_symmetric {γ : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a i j : Fin 2) :
    christoffel (physicalAngularJet γ x) a i j =
      christoffel (physicalAngularJet γ x) a j i := by
  have hd (l : Fin 2) : D (CKSRealizedRound.basis l.succ) (fun y => γ y i j) x =
      D (CKSRealizedRound.basis l.succ) (fun y => γ y j i) x := by
    apply D_congr
    filter_upwards [hp] with y hy
    exact (hermitian_real_symmetry hy.isHermitian i j).symm
  simp only [christoffel, physicalAngularJet, hd]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma physical_nabla_angularFrame {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (a b k : Fin 2) :
    nabla (fun y => christoffel (physicalAngularJet γ y))
      (angularFrame (U x) (γ x) (s x) a)
      (fun y => angularFrame (U y) (γ y) (s y) b) x k =
      ∑ c : Fin 2, inducedFrameCoefficient U γ s x a b c *
        angularFrame (U x) (γ x) (s x) c k := by
  have h := induced_connection_covector (s := s) h0 hp a b (Pi.single k 1)
  simp only [Pi.single_apply, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  rw [nabla, delta, lift_angularFrame]
  exact h.symm

theorem physical_leaf_curvature_coordinates {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a b d k : Fin 2) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField G E x
    let dc := fun i => connectionFieldDerivative (frameConnectionField G E) (E i x) x
    (∑ z : Fin 2, CKSFrame.leafCurvature c dc a b d z *
      angularFrame (U x) (γ x) (s x) z k) =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ l : Fin 2,
        angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) b j *
          angularFrame (U x) (γ x) (s x) d l *
            coordCurvature (fun y => christoffel (physicalAngularJet γ y)) x k l i j := by
  let G := fun y => foliationMetric (U y) (γ y) (s y)
  let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
  let e := fun a y => angularFrame (U y) (γ y) (s y) a
  let F := fun y => CKSFrame.leafConnection (frameConnectionField G E y)
  let Γ := fun y => christoffel (physicalAngularJet γ y)
  have hactual := foliation_actualAdaptedAt hU hγ hs h0 hp
  have hE : ∀ i, ContDiffAt ℝ ∞ (E i) x :=
    adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds
  have he : ∀ i, ContDiffAt ℝ ∞ (e i) x := by
    intro i
    exact contDiffAt_pi.mpr fun j => contDiffAt_pi.mp (hE i.succ) j.succ
  have hFnear : ∀ᶠ y in 𝓝 x, ∀ a b c,
      F y a b c = frameCoefficient G E y a.succ b.succ c.succ := by
    filter_upwards [hactual] with y hy
    intro a b c
    rw [show F y a b c = CKSFrame.connection (frameConnectionField G E y)
      a.succ b.succ c.succ from extracted_leaf_connection _ a b c,
      frame_connection_actual hy]
  have hF : ∀ a b c, DifferentiableAt ℝ (fun y => F y a b c) x := by
    intro a b c
    apply ((frameCoefficient_contDiffAt (foliationMetric_contDiffAt hU hγ hs h0)
      (foliationMetric_posDef h0 hp.self_of_nhds (s x)).det_pos.ne' hE
      a.succ b.succ c.succ).differentiableAt (by simp)).congr_of_eventuallyEq
    filter_upwards [hFnear] with y hy
    exact hy a b c
  have hc : ∀ᶠ y in 𝓝 x, ∀ a b k,
      nabla Γ (e a y) (e b) y k = ∑ c : Fin 2, F y a b c * e c y k := by
    filter_upwards [hFnear, hp, hU.continuousAt.eventually_ne h0] with y hy hyp hy0
    intro a b k
    have hind (c : Fin 2) : F y a b c = inducedFrameCoefficient U γ s y a b c :=
      (hy a b c).trans (physical_leaf_connection hyp hy0 a b c)
    simp only [hind]
    exact physical_nabla_angularFrame (s := s) hy0 hyp a b k
  have hγ2 : ContDiffAt ℝ 2 γ x :=
    hγ.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hframe := curvature_frame hF (fun i => (he i).differentiableAt (by simp))
    (physical_christoffel_symmetric hp) hc a b d k
  have hcoord := curvature_coordinate (physical_christoffel_differentiable hγ2 hp.self_of_nhds)
    ((he a).differentiableAt (by simp)) ((he b).differentiableAt (by simp))
    ((he d).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) k
  have hcurv (z : Fin 2) : frameCurvature F e x a b d z =
      CKSFrame.leafCurvature (frameConnectionField G E x)
        (fun i => connectionFieldDerivative (frameConnectionField G E) (E i x) x) a b d z := by
    simp only [frameCurvature, CKSFrame.leafCurvature, leafConnection_derivative,
      F, e, E, delta, lift_angularFrame]
  exact (by simpa only [hcurv] using hframe.symm.trans hcoord)

lemma physical_coordinate_scalar {γ : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ 2 γ x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    (∑ j : Fin 2, ∑ l : Fin 2, (γ x)⁻¹ j l *
      ∑ k : Fin 2, coordCurvature (fun y => christoffel (physicalAngularJet γ y)) x k l k j) =
      scalarCurvature (physicalAngularJet γ x) := by
  have h0 : determinant (γ x) ≠ 0 := by rw [determinant_eq]; exact hp.self_of_nhds.det_pos.ne'
  have hd (a k i j : Fin 2) :
      christoffelDerivative (physicalAngularJet γ x) a k i j =
        christoffelDerivative (physicalAngularJet γ x) a k j i := by
    rw [← physical_derivative_connection hγ h0, ← physical_derivative_connection hγ h0]
    apply D_congr
    filter_upwards [hp.eventually_nhds] with y hy
    exact physical_christoffel_symmetric hy k i j
  have hr (l j : Fin 2) :
      (∑ k : Fin 2, coordCurvature (fun y => christoffel (physicalAngularJet γ y)) x k l k j) =
        ricci (physicalAngularJet γ x) l j := by
    have ht (k : Fin 2) :
        coordCurvature (fun y => christoffel (physicalAngularJet γ y)) x k l k j =
        (christoffelDerivative (physicalAngularJet γ x) k k l j -
          christoffelDerivative (physicalAngularJet γ x) j k l k) +
        ∑ m : Fin 2, (christoffel (physicalAngularJet γ x) k k m *
          christoffel (physicalAngularJet γ x) m l j -
          christoffel (physicalAngularJet γ x) k j m *
          christoffel (physicalAngularJet γ x) m l k) := by
      rw [coordCurvature, physical_derivative_connection hγ h0,
        physical_derivative_connection hγ h0, hd k k j l, hd j k k l]
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      rw [physical_christoffel_symmetric hp m j l, physical_christoffel_symmetric hp m k l]
      ring
    simp only [ht, Finset.sum_add_distrib, ricci]
  calc
    _ = ∑ j : Fin 2, ∑ l : Fin 2, (γ x)⁻¹ j l * ricci (physicalAngularJet γ x) l j := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      congr 1
      exact hr l j
    _ = _ := by
      change _ = ∑ j : Fin 2, ∑ l : Fin 2, inverse (γ x) j l * ricci (physicalAngularJet γ x) j l
      simp only [inverse_eq, Fin.sum_univ_two]
      rw [inverse_symm_entry hp.self_of_nhds 1 0]
      ring

lemma angularFrame_orthonormal_pair {U : ℝ} {γ : Mat} (hU : U ≠ 0)
    (hp : γ.PosDef) (s : Point) (a b : Fin 2) :
    pair γ (angularFrame U γ s a) (angularFrame U γ s b) = if a = b then 1 else 0 := by
  have h := adaptedFrame_orthonormal hU hp s a.succ b.succ
  rw [metricPair_tangent_expanded U γ s _ _ (adaptedFrame_radial U γ s a)
    (adaptedFrame_radial U γ s b)] at h
  simpa only [pair, angularFrame, Fin.sum_univ_two, Fin.succ_inj,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using h

theorem physical_leaf_scalar {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField G E x
    let dc := fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x
    CKSFrame.leafScalar c dc = scalarCurvature (physicalAngularJet γ x) := by
  dsimp only
  let G := fun y => foliationMetric (U y) (γ y) (s y)
  let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
  let c := frameConnectionField G E x
  let dc := fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x
  let e : Fin 2 → Point := fun a => angularFrame (U x) (γ x) (s x) a
  have ho := angularFrame_orthonormal_pair h0.ne' hp.self_of_nhds (s x)
  have hg (i j : Fin 2) : (∑ a : Fin 2, e a i * e a j) = (γ x)⁻¹ i j :=
    congrFun (congrFun (angularFrame_gram h0.ne' hp.self_of_nhds) i) j
  have hc (a b : Fin 2) :
      (fun k => ∑ z : Fin 2, CKSFrame.leafCurvature c dc a b b z * e z k) =
        (fun k => ∑ i : Fin 2, ∑ j : Fin 2, ∑ l : Fin 2,
          e a i * e b j * e b l *
            coordCurvature (fun y => christoffel (physicalAngularJet γ y)) x k l i j) := by
    exact funext fun k => physical_leaf_curvature_coordinates hU hγ hs h0.ne' hp a b b k
  calc
    _ = ∑ a : Fin 2, ∑ b : Fin 2, pair (γ x)
        (fun k => ∑ z : Fin 2, CKSFrame.leafCurvature c dc a b b z * e z k) (e a) := by
      change (∑ a : Fin 2, ∑ b : Fin 2, CKSFrame.leafCurvature c dc a b b a) = _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact (pair_frame_sum (γ x) e ho (fun z => CKSFrame.leafCurvature c dc a b b z) a).symm
    _ = ∑ a : Fin 2, ∑ b : Fin 2, pair (γ x)
        (fun k => ∑ i : Fin 2, ∑ j : Fin 2, ∑ l : Fin 2,
          e a i * e b j * e b l *
            coordCurvature (fun y => christoffel (physicalAngularJet γ y)) x k l i j) (e a) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hc a b]
    _ = _ := by
      rw [scalar_frame_contraction hp.self_of_nhds e hg]
      exact physical_coordinate_scalar
        (hγ.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hp

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem physical_source_constraints {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let H := fun y => leafTensorTrace (γ y) (sourceChi U γ s y)
    let p := fun y => leafTensorTrace (γ y) (T y)
    let X := fun y => leafTensorTraceFree (γ y) (sourceChi U γ s y)
    let τ := fun y => leafTensorTraceFree (γ y) (T y)
    let q := physicalAngularJet γ x
    let ηj := fun i => physicalAngularScalarJet (fun y => η y i) x
    let τj := fun i j => physicalAngularScalarJet (fun y => τ y i j) x
    let B := fun i => D (CKSRealizedRound.basis i.succ) U x / U x
    (actualFrameScalar G E x + ((G x)⁻¹ * K x).trace ^ 2 -
        ((G x)⁻¹ * K x * (G x)⁻¹ * K x).trace) / 2 =
      scalarCurvature q / 2 - D (E 0 x) H x -
        lapseLaplacian q (physicalAngularScalarJet U x) - 3/4 * (H x)^2 -
        tensorPair q (X x) (X x) / 2 + L x * p x + (p x)^2 / 4 -
        tensorPair q (τ x) (τ x) / 2 - covectorPair q (η x) (η x) ∧
    coordinateMomentum G K x (E 0 x) =
      normalMomentum q (H x) (L x) (p x / 2) (D (E 0 x) p x)
        (X x) (τ x) ηj B ∧
    ∀ a, coordinateMomentum G K x (E a.succ x) =
      ∑ i : Fin 2, angularMomentum q (H x) (U x)
        (physicalAngularScalarJet L x) (physicalAngularScalarJet (fun y => p y / 2) x)
        (fun j => physicalAngularScalarJet (fun y => s y j) x) ηj τj
        (fun j => D (CKSRealizedRound.basis 0) (fun y => η y j) x) B i *
          angularFrame (U x) (γ x) (s x) a i
 := by
  dsimp only
  have hUd := hU.differentiableAt (by simp)
  have hγd := hγ.differentiableAt (by simp)
  have hsd := hs.differentiableAt (by simp)
  have hLd := hL.differentiableAt (by simp)
  have hηd := hη.differentiableAt (by simp)
  have hTd := hT.differentiableAt (by simp)
  have hK := foliationTensor_differentiableAt hUd hLd hTd hsd hηd h0.ne'
  have hKs : ∀ᶠ y in 𝓝 x, (foliationTensor (U y) (L y) (η y) (T y) (s y)).IsHermitian := by
    filter_upwards [hTs] with y hy
    exact foliationTensor_hermitian _ _ _ hy _
  obtain ⟨hC, hQ, hZ⟩ := physical_foliation_constraints hU hγ hs h0 hp hK hKs
  dsimp only at hC hQ hZ
  constructor
  · rw [hC, physical_leaf_scalar hU hγ hs h0 hp,
      physical_normal_mean hU hγ hs h0 hp,
      physical_mean_curvature_C1 hUd hγd hsd h0 hp,
      physical_shear_norm hU hγ hs h0 hp,
      foliation_frame_tensor_L h0.ne' hTs.self_of_nhds,
      foliation_frame_tensor_trace h0.ne' hp.self_of_nhds,
      physical_tau_norm h0.ne' hp.self_of_nhds hTs.self_of_nhds,
      physical_eta_norm h0.ne' hp.self_of_nhds hTs.self_of_nhds]
    have hA := physical_acceleration_laplacian hU hγ hs h0 hp
    dsimp only at hA
    linear_combination hA
  constructor
  · rw [hQ, physical_mean_curvature_C1 hUd hγd hsd h0 hp,
      foliation_frame_tensor_L h0.ne' hTs.self_of_nhds,
      foliation_frame_tensor_trace h0.ne' hp.self_of_nhds,
      physical_shear_tau hU hγ hs h0 hp hTs.self_of_nhds,
      physical_tensor_derivative_p hU hγ hs hLd hTd hηd h0.ne' hp,
      physical_eta_divergence hU hγ hs hηd h0.ne' hp hTs,
      physical_eta_acceleration hU hγ hs h0 hp hTs.self_of_nhds]
    rfl
  · intro a
    rw [hZ a, physical_eta_normal_lie hU hγ hs hηd h0.ne' hp hTs,
      physical_mean_curvature_C1 hUd hγd hsd h0 hp,
      foliation_frame_tensor_eta h0.ne' hTs.self_of_nhds,
      physical_tau_divergence hU hγ hs hLd hηd hT h0.ne' hp hTs,
      physical_tensor_tangential_trace_derivative hU hγ hs hLd hT hηd h0.ne' hp hTs,
      physical_acceleration_tensor hU hγ hs h0 hp hTs.self_of_nhds]
    simp only [angularMomentum, physicalAngularScalarJet, physicalAngularJet, inverse_eq, Fin.sum_univ_two]
    ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma sourceChi_contDiffAt {U : PhysicalPoint → ℝ} {γ : PhysicalPoint → Mat}
    {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) : ContDiffAt ℝ ∞ (sourceChi U γ s) x := by
  have hg (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have hsc (i) : ContDiffAt ℝ ∞ (fun y => s y i) x := contDiffAt_pi.mp hs i
  have hgd (e) (i j) : ContDiffAt ℝ ∞ (D e (fun y => γ y i j)) x :=
    contDiffAt_D (hg i j) (by simp) e
  have hsd (e) (i) : ContDiffAt ℝ ∞ (D e (fun y => s y i)) x :=
    contDiffAt_D (hsc i) (by simp) e
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  simp only [sourceChi, Fin.sum_univ_two]
  fun_prop

theorem physical_source_mass_identity {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (hr : 0 < x 0)
    (hu : 0 < x 0 * leafTensorTrace (γ x) (sourceChi U γ s x) / 2) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let H := fun y => leafTensorTrace (γ y) (sourceChi U γ s y)
    let p := fun y => leafTensorTrace (γ y) (T y)
    let X := leafTensorTraceFree (γ x) (sourceChi U γ s x)
    let τ := leafTensorTraceFree (γ x) (T x)
    let q := physicalAngularJet γ x
    let ηj := fun i => physicalAngularScalarJet (fun y => η y i) x
    let B := fun i => D (CKSRealizedRound.basis i.succ) U x / U x
    let F := CKSFrame.massField H p
    let u := x 0 * H x / 2
    let v := x 0 * p x / 2
    (actualFrameScalar G E x + ((G x)⁻¹ * K x).trace ^ 2 -
        ((G x)⁻¹ * K x * (G x)⁻¹ * K x).trace) / 2 -
      v/u * coordinateMomentum G K x (E 0 x) =
      2 * D (E 0 x) F x / (u*(x 0)^2) +
      (scalarCurvature q / 2 - 1/(x 0)^2) +
      (U x/u - 1) * (2 - 6*F x/(x 0))/(x 0)^2 -
      lapseLaplacian q (physicalAngularScalarJet U x) -
      (tensorPair q X X + tensorPair q τ τ) / 2 +
      v/u * tensorPair q X τ - covectorPair q (η x) (η x) -
      v/u * (covectorDiv q ηj - 2*covectorPair q (η x) B)
 := by
  dsimp only
  have hh := (leafTensorTrace_contDiffAt hγ (sourceChi_contDiffAt hU hγ hs)
    hp.self_of_nhds).differentiableAt (by simp)
  have ht := (leafTensorTrace_contDiffAt hγ hT hp.self_of_nhds).differentiableAt (by simp)
  have hd := CKSFrame.normal_mass_derivative hh ht (U x) (s x)
  change D (adaptedFrame (U x) (γ x) (s x) 0) _ x = _ at hd
  obtain ⟨hC, hQ, _⟩ := physical_source_constraints hU hγ hs hL hη hT h0 hp hTs
  dsimp only at hC hQ
  rw [hC, hQ, hd]
  have hnvec : CKSFrame.normalVector (U x) (s x) = adaptedFrame (U x) (γ x) (s x) 0 := rfl
  rw [hnvec]
  have hn : leafTensorTrace (γ x) (sourceChi U γ s x) ≠ 0 := by
    intro h; simp [h] at hu
  simp only [normalMomentum, CKSFrame.massField, physicalAngularScalarJet]
  simp only [covectorPair, div_eq_mul_inv]
  field_simp [hr.ne', hn]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def sourceB (U : PhysicalPoint → ℝ) (x : PhysicalPoint) : Point :=
  fun i => D (CKSRealizedRound.basis i.succ) U x / U x

def sourceQ (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) : ℝ :=
  normalMomentum (physicalAngularJet γ x) (sourceH U γ s x) (L x)
    (sourceP γ T x / 2) (D (adaptedFrame (U x) (γ x) (s x) 0) (sourceP γ T) x)
    (leafTensorTraceFree (γ x) (sourceChi U γ s x)) (leafTensorTraceFree (γ x) (T x))
    (fun i => physicalAngularScalarJet (fun y => η y i) x) (sourceB U x)

def sourceZ (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) : Point :=
  angularMomentum (physicalAngularJet γ x) (sourceH U γ s x) (U x)
    (physicalAngularScalarJet L x) (physicalAngularScalarJet (fun y => sourceP γ T y / 2) x)
    (fun i => physicalAngularScalarJet (fun y => s y i) x)
    (fun i => physicalAngularScalarJet (fun y => η y i) x)
    (fun i j => physicalAngularScalarJet (fun y => leafTensorTraceFree (γ y) (T y) i j) x)
    (fun i => D (CKSRealizedRound.basis 0) (fun y => η y i) x) (sourceB U x)

theorem physical_source_momentum_norm {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    metricPair (G x)⁻¹ (momentumCovector G K x) (momentumCovector G K x) =
      (sourceQ U L γ T s η x)^2 +
      covectorPair (physicalAngularJet γ x) (sourceZ U L γ T s η x) (sourceZ U L γ T s η x) := by
  dsimp only
  have hk := foliationTensor_differentiableAt (hU.differentiableAt (by simp))
    (hL.differentiableAt (by simp)) (hT.differentiableAt (by simp))
    (hs.differentiableAt (by simp)) (hη.differentiableAt (by simp)) h0.ne'
  have he := (foliation_actualAdaptedAt hU hγ hs h0.ne' hp).self_of_nhds
  rw [← physical_momentum_frame_norm he hk]
  simp_rw [actualFrameMomentum_coordinate he hk]
  rw [Fin.sum_univ_succ]
  obtain ⟨_, hQ, hZ⟩ := physical_source_constraints hU hγ hs hL hη hT h0 hp hTs
  dsimp only at hQ hZ
  rw [hQ]
  change (sourceQ U L γ T s η x)^2 + _ = _
  congr 1
  simp_rw [hZ]
  change (∑ a, (∑ i, sourceZ U L γ T s η x i * angularFrame (U x) (γ x) (s x) a i)^2) = _
  simp only [covectorPair, physicalAngularJet, inverse_eq]
  exact angular_covector_frame_square (s := s x) (sourceZ U L γ T s η x) h0.ne' hp.self_of_nhds

theorem physical_source_DEC_iff {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    physicalDEC G K E x ↔
      Real.sqrt ((sourceQ U L γ T s η x)^2 +
        covectorPair (physicalAngularJet γ x) (sourceZ U L γ T s η x) (sourceZ U L γ T s η x)) ≤
      physicalEnergy G K E x := by
  dsimp only [physicalDEC]
  rw [physical_source_momentum_norm hU hγ hs hL hη hT h0 hp hTs]

end
end CKSAngularGeometry

end


noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma inverse_radius_smul_cancel {r : ℝ} (hr : r ≠ 0) (n : ℕ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    (1/r)^n • (r^n • v) = v := by
  rw [smul_smul, ← mul_pow, one_div_mul_cancel hr, one_pow, one_smul]

lemma physicalBaseLapse_ne {r : ℝ} (hr : r ≠ 0) : physicalBaseLapse r ≠ 0 :=
  mul_ne_zero hr (Real.sqrt_ne_zero'.mpr (by positivity))

variable (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ)

lemma physical_input_L (hr : x 0 ≠ 0) :
    physicalLJet (physicalMomentumInput U L γ T s η x w) = physicalAngularScalarJet L x := by
  change constantJet (1+w*(1/x 0)^2)+
    (1/x 0)^3 • ((x 0)^3 • (physicalAngularScalarJet L x-constantJet (1+w/(x 0)^2))) = _
  rw [inverse_radius_smul_cancel hr]
  have he : 1+w*(1/x 0)^2 = 1+w/(x 0)^2 := by ring
  rw [he]
  abel

lemma physical_input_t (hr : x 0 ≠ 0) :
    physicalTJet (physicalMomentumInput U L γ T s η x w) =
      physicalAngularScalarJet (fun y => sourceP γ T y/2) x := by
  change constantJet 1+(1/x 0)^3 • ((x 0)^3 •
    (physicalAngularScalarJet (fun y => sourceP γ T y/2) x-constantJet 1)) = _
  rw [inverse_radius_smul_cancel hr]
  abel

lemma physical_input_lapseJet (hr : x 0 ≠ 0) :
    constantJet 1+mz (physicalMomentumInput U L γ T s η x w)^3 •
      mc (physicalMomentumInput U L γ T s η x w) 0 =
    (1/physicalBaseLapse (x 0)) • physicalAngularScalarJet U x := by
  change constantJet 1+(1/x 0)^3 • ((x 0)^3 •
    ((1/physicalBaseLapse (x 0)) • physicalAngularScalarJet U x-constantJet 1)) = _
  rw [inverse_radius_smul_cancel hr]
  abel

lemma physical_input_speed (hr : x 0 ≠ 0) :
    normalizedSpeed (physicalMomentumInput U L γ T s η x w) = U x/x 0 := by
  have he := congrArg Prod.fst (physical_input_lapseJet U L γ T s η x w hr)
  change 1+mz (physicalMomentumInput U L γ T s η x w)^3 *
    (mc (physicalMomentumInput U L γ T s η x w) 0).1 = (1/physicalBaseLapse (x 0))*U x at he
  rw [normalizedSpeed, he]
  change Real.sqrt (1+(1/x 0)^2) * ((1/physicalBaseLapse (x 0))*U x) = _
  unfold physicalBaseLapse
  field_simp [hr, Real.sqrt_ne_zero'.mpr (by positivity : 0 < 1+(1/x 0)^2)]

lemma physical_input_d (hr : x 0 ≠ 0) :
    nullD (physicalMomentumInput U L γ T s η x w) = sourceD U γ s x := by
  change 1+(1/x 0)^3*((x 0)^3*(sourceD U γ s x-1)) = _
  field_simp
  ring

lemma physical_input_mean (hr : x 0 ≠ 0) (hU : U x ≠ 0) :
    normalizedMean (physicalMomentumInput U L γ T s η x w) = sourceH U γ s x := by
  change 2*normalizedSpeed (physicalMomentumInput U L γ T s η x w)*
    nullD (physicalMomentumInput U L γ T s η x w) = _
  rw [physical_input_speed U L γ T s η x w hr, physical_input_d U L γ T s η x w hr]
  unfold sourceD
  field_simp

lemma physical_input_ratio (hr : x 0 ≠ 0) (hU : U x ≠ 0) :
    nullRatio (physicalMomentumInput U L γ T s η x w) = sourceP γ T x/sourceH U γ s x := by
  have he := congrArg Prod.fst (physical_input_t U L γ T s η x w hr)
  change 1+mz (physicalMomentumInput U L γ T s η x w)^3 *
    (mc (physicalMomentumInput U L γ T s η x w) 1).1 = sourceP γ T x/2 at he
  rw [nullRatio, he,physical_input_speed U L γ T s η x w hr,
    physical_input_d U L γ T s η x w hr]
  have hd : U x/x 0*sourceD U γ s x = sourceH U γ s x/2 := by
    unfold sourceD; field_simp
  rw [hd]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv]
  ring

lemma physical_input_acceleration (hr : x 0 ≠ 0) (hU : U x ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w)^3 •
      accelerationCoefficient (physicalMomentumInput U L γ T s η x w) = sourceB U x := by
  have he := congrArg Prod.fst (physical_input_lapseJet U L γ T s η x w hr)
  change 1+mz (physicalMomentumInput U L γ T s η x w)^3 *
    (mc (physicalMomentumInput U L γ T s η x w) 0).1 = (1/physicalBaseLapse (x 0))*U x at he
  funext a
  simp only [Pi.smul_apply,smul_eq_mul,accelerationCoefficient,he]
  change (1/x 0)^3*((x 0)^3*((1/physicalBaseLapse (x 0))*
    D (CKSRealizedRound.basis a.succ) U x-0)/((1/physicalBaseLapse (x 0))*U x)) = _
  unfold sourceB
  field_simp [hr,hU,physicalBaseLapse_ne hr]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma rescale_composition (a b : ℝ) (q : Jet) :
    rescale a (rescale b q) = rescale (a*b) q := by
  apply Prod.ext
  · funext i j; simp only [rescale]; ring
  · apply Prod.ext
    · funext d i j; simp only [rescale]; ring
    · funext c d i j; simp only [rescale]; ring

lemma rescale_one (q : Jet) : rescale 1 q = q := by
  rcases q with ⟨q,d,dd⟩
  simp only [rescale,one_mul]

variable (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ)

lemma physical_input_q (hr : x 0 ≠ 0) :
    rescale (1/mz (physicalMomentumInput U L γ T s η x w)^2)
      (mq (physicalMomentumInput U L γ T s η x w)) = physicalAngularJet γ x := by
  change rescale (1/(1/x 0)^2) (rescale (1/(x 0)^2) (physicalAngularJet γ x)) = _
  rw [rescale_composition]
  have he : 1/(1/x 0)^2*(1/(x 0)^2) = 1 := by field_simp
  rw [he,rescale_one]

lemma physical_input_s (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w)^5 • mS (physicalMomentumInput U L γ T s η x w) =
      (fun a => physicalAngularScalarJet (fun y => s y a) x) :=
  inverse_radius_smul_cancel hr 5 _

lemma physical_input_eta (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w)^2 • mE (physicalMomentumInput U L γ T s η x w) =
      (fun a => physicalAngularScalarJet (fun y => η y a) x) :=
  inverse_radius_smul_cancel hr 2 _

lemma physical_input_tau (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w) • mT (physicalMomentumInput U L γ T s η x w) =
      (fun a b => physicalAngularScalarJet (fun y => leafTensorTraceFree (γ y) (T y) a b) x) := by
  change (1/x 0) • ((x 0) • _) = _
  rw [smul_smul,one_div_mul_cancel hr,one_smul]

lemma physical_input_X (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w) • mX (physicalMomentumInput U L γ T s η x w) =
      leafTensorTraceFree (γ x) (sourceChi U γ s x) := by
  change (1/x 0) • ((x 0) • _) = _
  rw [smul_smul,one_div_mul_cancel hr,one_smul]

lemma physical_input_Er (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w)^3 • mEr (physicalMomentumInput U L γ T s η x w) =
      (fun a => D (CKSRealizedRound.basis 0) (fun y => η y a) x) :=
  inverse_radius_smul_cancel hr 3 _

lemma physical_input_tau_value (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w) •
      ((fun a b => (mT (physicalMomentumInput U L γ T s η x w) a b).1) : Mat) =
      leafTensorTraceFree (γ x) (T x) := by
  have he := physical_input_tau U L γ T s η x w hr
  exact congrArg (fun t : CovariantTensorJet => fun a b => (t a b).1) he

lemma physical_input_eta_value (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w)^2 •
      (fun a => (mE (physicalMomentumInput U L γ T s η x w) a).1) = η x := by
  have he := physical_input_eta U L γ T s η x w hr
  exact congrArg (fun t : CovectorJet => fun a => (t a).1) he

lemma physical_normal_derivative (f : PhysicalPoint → ℝ) :
    D (adaptedFrame (U x) (γ x) (s x) 0) f x =
      U x*(D (CKSRealizedRound.basis 0) f x-
        ∑ a : Fin 2, s x a*D (CKSRealizedRound.basis a.succ) f x) := by
  rw [D_direction_expansion,Fin.sum_univ_succ]
  change U x*D (CKSRealizedRound.basis 0) f x+
    (∑ a : Fin 2, foliationNormal (U x) (s x) a.succ*D (CKSRealizedRound.basis a.succ) f x) = _
  simp only [foliationNormal_succ,Fin.sum_univ_two]
  ring

lemma physical_input_Np (hr : x 0 ≠ 0)
    (hp : DifferentiableAt ℝ (sourceP γ T) x) :
    let p := physicalMomentumInput U L γ T s η x w
    2*normalizedSpeed p*mz p^3*((mc p 3).1-mz p^4*∑ a, (mS p a).1*(mc p 1).2.1 a) =
      D (adaptedFrame (U x) (γ x) (s x) 0) (sourceP γ T) x := by
  dsimp only
  rw [physical_input_speed U L γ T s η x w hr,physical_normal_derivative]
  change 2*(U x/x 0)*(1/x 0)^3*((x 0)^4*D (CKSRealizedRound.basis 0)
    (fun y => sourceP γ T y/2) x-(1/x 0)^4*∑ a : Fin 2,
      ((x 0)^5*s x a)*((x 0)^3*(D (CKSRealizedRound.basis a.succ) (fun y => sourceP γ T y/2) x-0))) = _
  simp_rw [physical_D_div_const _ hp]
  simp only [Fin.sum_univ_two]
  field_simp
  ring

lemma physical_input_Q (hr : x 0 ≠ 0) (hU : U x ≠ 0)
    (hp : DifferentiableAt ℝ (sourceP γ T) x) :
    coordinateQ (physicalMomentumInput U L γ T s η x w) = sourceQ U L γ T s η x := by
  unfold coordinateQ
  rw [physical_input_q U L γ T s η x w hr,physical_input_mean U L γ T s η x w hr hU,
    physical_input_L U L γ T s η x w hr,physical_input_t U L γ T s η x w hr,
    physical_input_Np U L γ T s η x w hr hp,physical_input_X U L γ T s η x w hr,
    physical_input_tau_value U L γ T s η x w hr,physical_input_eta U L γ T s η x w hr,
    physical_input_acceleration U L γ T s η x w hr hU]
  rfl

lemma physical_input_Z (hr : x 0 ≠ 0) (hU : U x ≠ 0) :
    coordinateZ (physicalMomentumInput U L γ T s η x w) = sourceZ U L γ T s η x := by
  funext a
  unfold coordinateZ
  rw [physical_input_q U L γ T s η x w hr,physical_input_mean U L γ T s η x w hr hU,
    physical_input_L U L γ T s η x w hr,physical_input_t U L γ T s η x w hr,
    physical_input_speed U L γ T s η x w hr,physical_input_s U L γ T s η x w hr,
    physical_input_tau U L γ T s η x w hr,physical_input_eta U L γ T s η x w hr,
    physical_input_Er U L γ T s η x w hr,physical_input_acceleration U L γ T s η x w hr hU]
  have he : U x/x 0 / (1/x 0) = U x := by field_simp
  change angularMomentum _ _ (U x/x 0/(1/x 0)) _ _ _ _ _ _ _ _ = _
  rw [he]
  rfl

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma lapseLaplacian_lapse_smul (q : Jet) (z : ScalarJet) {c : ℝ}
    (hc : c ≠ 0) (hz : z.1 ≠ 0) : lapseLaplacian q (c • z) = lapseLaplacian q z := by
  unfold lapseLaplacian
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp only [Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_two]
  field_simp

variable (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ)

lemma physical_input_massrow (hr : x 0 ≠ 0) (hU : U x ≠ 0)
    (hH : sourceH U γ s x ≠ 0) :
    let p := physicalNullInput U L γ T s η x w
    2*(mw (nP p)/(x 0*Real.sqrt (x 0))+mz (nP p)^2*nFr p-
      mz (nP p)^5*∑ a, (mS (nP p) a).1*(nF p).2.1 a)/nullD (nP p)*mz (nP p)^2 =
    2*D (adaptedFrame (U x) (γ x) (s x) 0) (sourceMass U γ T s) x/
      ((x 0*sourceH U γ s x/2)*(x 0)^2) := by
  dsimp only [physicalNullInput,nP,nFr,nF]
  rw [physical_input_d U L γ T s η x w hr,physical_normal_derivative]
  change 2*(w/(x 0*Real.sqrt (x 0))+(1/x 0)^2*((x 0)^2*
    (D (CKSRealizedRound.basis 0) (sourceMass U γ T s) x-w/(x 0*Real.sqrt (x 0))))-
    (1/x 0)^5*∑ a : Fin 2, ((x 0)^5*s x a)*D (CKSRealizedRound.basis a.succ) (sourceMass U γ T s) x)/
    sourceD U γ s x*(1/x 0)^2 = _
  simp only [Fin.sum_univ_two,sourceD]
  field_simp
  ring

lemma physical_input_smallNull_formula (hr : x 0 ≠ 0) (hU : U x ≠ 0)
    (hH : sourceH U γ s x ≠ 0) :
    let q := physicalAngularJet γ x
    let X := leafTensorTraceFree (γ x) (sourceChi U γ s x)
    let τ := leafTensorTraceFree (γ x) (T x)
    let F := sourceMass U γ T s
    let u := x 0*sourceH U γ s x/2
    let a := sourceP γ T x/sourceH U γ s x
    coordinateSmallNull (physicalNullInput U L γ T s η x w) (x 0) =
      2*D (adaptedFrame (U x) (γ x) (s x) 0) F x/(u*(x 0)^2)+
      (scalarCurvature q/2-1/(x 0)^2)+
      (U x/u-1)*(2-6*F x/(x 0))/(x 0)^2-
      lapseLaplacian q (physicalAngularScalarJet U x)-
      (tensorPair q X X+tensorPair q τ τ)/2+a*tensorPair q X τ-
      covectorPair q (η x) (η x)-
      a*(covectorDiv q (fun i => physicalAngularScalarJet (fun y => η y i) x)-
        2*covectorPair q (η x) (sourceB U x)) := by
  dsimp only
  unfold coordinateSmallNull
  rw [physical_input_massrow U L γ T s η x w hr hU hH]
  dsimp only [physicalNullInput,nP,nF]
  unfold physicalNullQuadratic physicalNullEta
  rw [physical_input_q U L γ T s η x w hr,physical_input_d U L γ T s η x w hr,
    physical_input_lapseJet U L γ T s η x w hr,physical_input_ratio U L γ T s η x w hr hU,
    physical_input_X U L γ T s η x w hr,physical_input_tau_value U L γ T s η x w hr,
    physical_input_eta_value U L γ T s η x w hr,physical_input_eta U L γ T s η x w hr,
    physical_input_acceleration U L γ T s η x w hr hU]
  rw [lapseLaplacian_lapse_smul _ _ (one_div_ne_zero (physicalBaseLapse_ne hr)) hU]
  have hc : (1/sourceD U γ s x-1)*(2-6*(1/x 0)*sourceMass U γ T s x)*(1/x 0)^2 =
      (U x/(x 0*sourceH U γ s x/2)-1)*(2-6*sourceMass U γ T s x/(x 0))/(x 0)^2 := by
    unfold sourceD
    field_simp
  change _+(_/2-(1/x 0)^2)+
    (1/sourceD U γ s x-1)*(2-6*(1/x 0)*sourceMass U γ T s x)*(1/x 0)^2-_
      +_ -_ = _
  rw [hc]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physical_input_smallNull {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (hr : 0 < x 0)
    (hu : 0 < x 0 * sourceH U γ s x / 2) (w : ℝ) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    coordinateSmallNull (physicalNullInput U L γ T s η x w) (x 0) =
      physicalEnergy G K E x-sourceP γ T x/sourceH U γ s x*sourceQ U L γ T s η x := by
  dsimp only
  have hH : sourceH U γ s x ≠ 0 := by intro h; simp [h] at hu
  have hm := physical_source_mass_identity hU hγ hs hL hη hT h0 hp hTs hr hu
  obtain ⟨_,hq,_⟩ := physical_source_constraints hU hγ hs hL hη hT h0 hp hTs
  dsimp only at hm hq
  rw [hq] at hm
  have ha : (x 0*sourceP γ T x/2)/(x 0*sourceH U γ s x/2) =
      sourceP γ T x/sourceH U γ s x := by field_simp
  change physicalEnergy (fun y => foliationMetric (U y) (γ y) (s y))
    (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
    (fun i y => adaptedFrame (U y) (γ y) (s y) i) x-
      (x 0*sourceP γ T x/2)/(x 0*sourceH U γ s x/2)*sourceQ U L γ T s η x = _ at hm
  change _ = 2*D (adaptedFrame (U x) (γ x) (s x) 0) (sourceMass U γ T s) x/
    ((x 0*sourceH U γ s x/2)*(x 0)^2)+
    (scalarCurvature (physicalAngularJet γ x)/2-1/(x 0)^2)+
    (U x/(x 0*sourceH U γ s x/2)-1)*(2-6*sourceMass U γ T s x/(x 0))/(x 0)^2-
    lapseLaplacian (physicalAngularJet γ x) (physicalAngularScalarJet U x)-
    (tensorPair (physicalAngularJet γ x) (leafTensorTraceFree (γ x) (sourceChi U γ s x))
      (leafTensorTraceFree (γ x) (sourceChi U γ s x))+
      tensorPair (physicalAngularJet γ x) (leafTensorTraceFree (γ x) (T x))
        (leafTensorTraceFree (γ x) (T x)))/2+
    ((x 0*sourceP γ T x/2)/(x 0*sourceH U γ s x/2))*
      tensorPair (physicalAngularJet γ x) (leafTensorTraceFree (γ x) (sourceChi U γ s x))
        (leafTensorTraceFree (γ x) (T x))-
    covectorPair (physicalAngularJet γ x) (η x) (η x)-
    ((x 0*sourceP γ T x/2)/(x 0*sourceH U γ s x/2))*
      (covectorDiv (physicalAngularJet γ x) (fun i => physicalAngularScalarJet (fun y => η y i) x)-
        2*covectorPair (physicalAngularJet γ x) (η x) (sourceB U x)) at hm
  rw [ha] at hm
  exact (physical_input_smallNull_formula U L γ T s η x w hr.ne' h0.ne' hH).trans hm.symm

lemma physical_input_energy {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (hr : 0 < x 0)
    (hu : 0 < x 0 * sourceH U γ s x / 2) (w : ℝ) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    coordinateEnergy (physicalNullInput U L γ T s η x w) (x 0) = physicalEnergy G K E x := by
  dsimp only
  have ht : DifferentiableAt ℝ (sourceP γ T) x :=
    (leafTensorTrace_contDiffAt hγ hT hp.self_of_nhds).differentiableAt (by simp)
  change coordinateSmallNull (physicalNullInput U L γ T s η x w) (x 0)+
    nullRatio (physicalMomentumInput U L γ T s η x w)*
      coordinateQ (physicalMomentumInput U L γ T s η x w) = _
  rw [physical_input_smallNull hU hγ hs hL hη hT h0 hp hTs hr hu w,
    physical_input_ratio U L γ T s η x w hr.ne' h0.ne',
    physical_input_Q U L γ T s η x w hr.ne' h0.ne' ht]
  ring

theorem physical_normalized_DEC_iff {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (hr : 0 < x 0)
    (hu : 0 < x 0 * sourceH U γ s x / 2) (w : ℝ) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    physicalDEC G K E x ↔ coordinateDEC (physicalNullInput U L γ T s η x w) (x 0)
 := by
  dsimp only
  have ht : DifferentiableAt ℝ (sourceP γ T) x :=
    (leafTensorTrace_contDiffAt hγ hT hp.self_of_nhds).differentiableAt (by simp)
  have hd := physical_source_DEC_iff hU hγ hs hL hη hT h0 hp hTs
  dsimp only at hd
  rw [hd]
  unfold coordinateDEC
  change _ ↔ Real.sqrt ((coordinateQ (physicalMomentumInput U L γ T s η x w))^2+
    covectorPair (rescale (1/mz (physicalMomentumInput U L γ T s η x w)^2)
      (mq (physicalMomentumInput U L γ T s η x w)))
      (coordinateZ (physicalMomentumInput U L γ T s η x w))
      (coordinateZ (physicalMomentumInput U L γ T s η x w))) ≤
    coordinateEnergy (physicalNullInput U L γ T s η x w) (x 0)
  rw [physical_input_Q U L γ T s η x w hr.ne' h0.ne' ht,
    physical_input_Z U L γ T s η x w hr.ne' h0.ne',
    physical_input_q U L γ T s η x w hr.ne',
    physical_input_energy hU hγ hs hL hη hT h0 hp hTs hr hu w]

end
end CKSAngularGeometry

end






























































end OAI
end

theorem solution : type_of% @OAI.CKSAngularGeometry.physical_normalized_DEC_iff := @OAI.CKSAngularGeometry.physical_normalized_DEC_iff
