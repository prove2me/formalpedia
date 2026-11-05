-- Prove2me | solution 1 for OAI.CKSCartesianOuter.spherical_physical_energy
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:06:47.528562+00:00
-- url     : https://prove2.me/submissions/d0d54b3b-fb06-48b4-b3b1-15f122bf1c59

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSInducedSphere_smoothDatum_rapid
import Theorems.Thm_OAI_CKSSphericalChart_outerMass_smooth
import Theorems.Thm_OAI_CKSSphericalChart_outerA_smooth
import Theorems.Thm_OAI_CKSSphericalChart_outerPhi_smooth

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




noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound Filter
open scoped Topology ContDiff

lemma contDiffAt_radial {v : ℝ → ℝ} {x : Point} {n : ℕ∞ω}
    (hv : ContDiffAt ℝ n v (x 0)) : ContDiffAt ℝ n (radial v) x :=
  hv.comp x (coord 0).contDiff.contDiffAt

lemma contDiffAt_radicand {F : Point → ℝ} {v : ℝ → ℝ} {x : Point} {n : ℕ∞ω}
    (hF : ContDiffAt ℝ n F x) (hv : ContDiffAt ℝ n v (x 0)) (hr : x 0 ≠ 0) :
    ContDiffAt ℝ n (radicand F v) x := by
  exact ((contDiffAt_const (c := (1 : ℝ))).add ((contDiffAt_radial hv).pow 2)).sub
    (((contDiffAt_const (c := (2 : ℝ))).mul hF).div (coord 0).contDiff.contDiffAt hr)

lemma contDiffAt_lapse {F : Point → ℝ} {v : ℝ → ℝ} {x : Point} {n : ℕ∞ω}
    (hF : ContDiffAt ℝ n F x) (hv : ContDiffAt ℝ n v (x 0)) (hr : x 0 ≠ 0)
    (hpos : 0 < radicand F v x) : ContDiffAt ℝ n (lapse F v) x :=
  (contDiffAt_radicand hF hv hr).sqrt hpos.ne'

lemma lapse_pos {F : Point → ℝ} {v : ℝ → ℝ} {x : Point}
    (hpos : 0 < radicand F v x) : 0 < lapse F v x := Real.sqrt_pos.2 hpos

end
end CKSRealizedRound

end




noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound CKSLocalBending CKSBending
open scoped Topology ContDiff

def outerMetric (F : Point → ℝ) (v : ℝ → ℝ) := metric (lapse F v)
def outerTensor (F : Point → ℝ) (v β : ℝ → ℝ) (a b : Point → ℝ) :=
  tensor (lapse F v) v (radial (normalEntry v β))
    (correctedComponent v a) (correctedComponent v b)

end
end CKSRealizedRound

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
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma phi_smooth : ContDiffOn ℝ ∞ phi (Ioi 0) := by
  unfold phi
  have hc : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition ((x-6)/6)) := by fun_prop
  exact (contDiffOn_const.sub hc.contDiffOn).add
    (hc.contDiffOn.mul ((contDiffOn_id.inv (fun x hx => ne_of_gt hx)).pow 3))
lemma xi_smooth : ContDiff ℝ ∞ xi := by unfold xi; fun_prop

lemma beta_smooth : ContDiff ℝ ∞ beta := by unfold beta; fun_prop

lemma bendingV_smooth {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (bendingV R) (Ioi 0) := by
  unfold bendingV
  have hc : ContDiffOn ℝ ∞ (fun r : ℝ => phi (r/R)) (Ioi 0) :=
    phi_smooth.comp (contDiffOn_id.div_const R) (fun r hr => div_pos hr hR)
  exact (contDiffOn_id.mul hc).mul
    ((xi_smooth.comp (contDiff_id.div_const (R^2))).contDiffOn)

lemma bendingBeta_smooth (R : ℝ) : ContDiff ℝ ∞ (bendingBeta R) :=
  beta_smooth.comp (contDiff_id.div_const R)

end
end CKSBending

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
namespace CKSInducedSphere
noncomputable section
open Finset

lemma proj_symm (x : Vec) (i j : Ix) : proj x i j = proj x j i := by
  simp only [proj, eq_comm, mul_comm]

lemma proj_normal {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (i : Ix) :
    ∑ j, proj x i j * x j = 0 := by
  simp only [proj, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq univ i (fun j => x j), ite_eq_left (mem_univ i)]
  simp_rw [mul_assoc, ← pow_two]
  rw [← Finset.mul_sum, hx]
  ring

lemma proj_idempotent {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (i j : Ix) :
    ∑ k, proj x i k * proj x k j = proj x i j := by
  simp only [proj, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' univ j (fun k => (if i = k then 1 else 0) - x i * x k),
    ite_eq_left (mem_univ j)]
  have hn := proj_normal hx i
  simp only [proj] at hn
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  simp only [hn, zero_mul, sub_zero]

lemma proj_trace {x : Vec} (hx : ∑ i, x i ^ 2 = 1) : ∑ i, proj x i i = 2 := by
  simp only [proj, ← pow_two, Finset.sum_sub_distrib]
  rw [hx]
  norm_num

lemma sum3_rotate (f : Ix → Ix → Ix → ℝ) :
    (∑ i, ∑ a, ∑ b, f i a b) = ∑ a, ∑ b, ∑ i, f i a b := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := (univ : Finset Ix)) (t := (univ : Finset (Ix × Ix)))
      (f := fun i ab => f i ab.1 ab.2))

lemma hessTF_symm (x : Vec) (H : Mat) (hH : ∀ i j, H i j = H j i) (i j : Ix) :
    hessTF x H i j = hessTF x H j i := by
  unfold hessTF
  rw [proj_symm x i j]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  rw [proj_symm x i b, proj_symm x a j, hH b a]
  ring

lemma hessTF_normal_left {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (H : Mat) (j : Ix) :
    ∑ i, x i * hessTF x H i j = 0 := by
  simp only [hessTF, mul_sub, Finset.mul_sum, sum_sub_distrib]
  have he (i a b : Ix) : x i * (proj x i a * H a b * proj x b j) =
      (proj x a i * x i) * (H a b * proj x b j) := by rw [proj_symm x i a]; ring
  simp_rw [he]
  rw [sum3_rotate]
  simp only [← Finset.sum_mul, proj_normal hx, zero_mul, sum_const_zero]
  have ht (i : Ix) : x i * (tangentTrace x H / 2 * proj x i j) =
      tangentTrace x H / 2 * (proj x j i * x i) := by rw [proj_symm x i j]; ring
  simp_rw [ht, ← Finset.mul_sum, proj_normal hx]
  ring

lemma hessTF_trace_zero {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (H : Mat) :
    ∑ i, hessTF x H i i = 0 := by
  simp only [hessTF, sum_sub_distrib, ← Finset.mul_sum, proj_trace hx]
  have he (i a b : Ix) : proj x i a * H a b * proj x b i =
      (proj x b i * proj x i a) * H a b := by ring
  simp_rw [he]
  rw [sum3_rotate]
  simp only [← Finset.sum_mul, proj_idempotent hx]
  simp_rw [proj_symm x _ _]
  change tangentTrace x H - tangentTrace x H / 2 * 2 = 0
  ring

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MvPolynomial

lemma rotation_apply (i j : Fin 3) (p : Poly) :
    rotation i j p = X i * pderiv j p - X j * pderiv i p := by
  simp [rotation, smul_eq_mul]

lemma sphereEval_X (i : Fin 3) : sphereEval (X i) = sphereCoordinate i :=
  aeval_X _ _

open MeasureTheory

open scoped Pointwise
def sphereHome (u : Ambient ≃ₗᵢ[ℝ] Ambient) : Sphere ≃ₜ Sphere :=
  u.toHomeomorph.subtype (fun x => by
    simp only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.coe_toHomeomorph,
      u.norm_map])

def rotatedCoordinate (i j : Fin 3) (t : ℝ) (k : Fin 3) : C(Sphere, ℝ) :=
  if k = i then Real.cos t • sphereCoordinate i - Real.sin t • sphereCoordinate j
  else if k = j then Real.sin t • sphereCoordinate i + Real.cos t • sphereCoordinate j
  else sphereCoordinate k

def rotationAction (i j : Fin 3) (t : ℝ) : Poly →ₐ[ℝ] C(Sphere, ℝ) :=
  aeval (rotatedCoordinate i j t)

lemma rotationAction_zero (i j : Fin 3) : rotationAction i j 0 = sphereEval := by
  apply MvPolynomial.algHom_ext
  intro k
  simp only [rotationAction, sphereEval, aeval_X, rotatedCoordinate, Real.cos_zero,
    Real.sin_zero, one_smul, zero_smul, sub_zero, zero_add]
  split_ifs with hi hj
  · subst k; rfl
  · subst k; rfl
  · rfl

lemma rotationAction_apply (i j : Fin 3) (hij : i ≠ j) (t : ℝ)
    (p : Poly) (x : Sphere) :
    rotationAction i j t p x = sphereEval p (sphereHome (planeRotation i j hij t) x) := by
  have h : (ContinuousMap.evalAlgHom ℝ ℝ x).comp (rotationAction i j t) =
      (ContinuousMap.evalAlgHom ℝ ℝ (sphereHome (planeRotation i j hij t) x)).comp
        sphereEval := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, ContinuousMap.evalAlgHom_apply, rotationAction,
      aeval_X, sphereEval]
    change rotatedCoordinate i j t k x = (planeRotationMap i j t x.1) k
    rw [planeRotationMap_apply]
    simp only [rotatedCoordinate]
    split_ifs <;> rfl
  exact congrArg (fun f : Poly →ₐ[ℝ] ℝ => f p) h

lemma rotatedCoordinate_hasDerivAt_zero (i j : Fin 3) (hij : i ≠ j) (k : Fin 3) :
    HasDerivAt (fun t => rotatedCoordinate i j t k)
      (sphereEval (rotation i j (X k))) 0 := by
  have hs := (Real.hasDerivAt_sin (0 : ℝ))
  have hc := (Real.hasDerivAt_cos (0 : ℝ))
  by_cases hi : k = i
  · subst k
    convert! (hc.smul_const (sphereCoordinate i)).sub
        (hs.smul_const (sphereCoordinate j)) using 1 <;>
      simp [rotatedCoordinate, rotation_apply, hij, pderiv_X, sphereEval_X]
    rfl
  · by_cases hj : k = j
    · subst k
      convert! (hs.smul_const (sphereCoordinate i)).add
          (hc.smul_const (sphereCoordinate j)) using 1 <;>
        simp [rotatedCoordinate, rotation_apply, hij.symm, pderiv_X, sphereEval_X]
      rfl
    · simpa [rotatedCoordinate, rotation_apply, hi, hj, Ne.symm hi, Ne.symm hj,
        pderiv_X] using hasDerivAt_const (0 : ℝ) (sphereCoordinate k)

lemma rotationAction_hasDerivAt_zero (i j : Fin 3) (hij : i ≠ j) (p : Poly) :
    HasDerivAt (fun t => rotationAction i j t p) (sphereEval (rotation i j p)) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [rotationAction, rotation_apply] using
      hasDerivAt_const (0 : ℝ) (algebraMap ℝ C(Sphere, ℝ) a)
  | add p q hp hq =>
    convert! hp.add hq using 1 <;> simp only [map_add]
    rfl
  | mul_X p k hp =>
    have hk : HasDerivAt (fun t => rotationAction i j t (X k))
        (sphereEval (rotation i j (X k))) 0 :=
      by simpa only [rotationAction, aeval_X] using
        rotatedCoordinate_hasDerivAt_zero i j hij k
    convert! hp.mul hk using 1
    · funext t; exact map_mul (rotationAction i j t) p (X k)
    · rw [Derivation.leibniz, map_add]
      simp only [smul_eq_mul, map_mul, rotationAction_zero]
      ring

open scoped Manifold ContDiff Topology
open Set

lemma rotationGenerator_apply (i j k : Fin 3) (x : Ambient) :
    rotationGenerator i j x k = (if k = j then x i else 0) - (if k = i then x j else 0) := rfl

attribute [local instance] cksLocalInst_1853

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

def polynomialExtension (p : Poly) (x : Ambient) : ℝ := aeval (fun i => x i) p

lemma polynomialExtension_smooth (p : Poly) : ContDiff ℝ ∞ (polynomialExtension p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    convert! (contDiff_const : ContDiff ℝ ∞ (fun _ : Ambient => a)) using 1
    funext x; simp [polynomialExtension]
  | add p q hp hq =>
    convert! hp.add hq using 1
    funext x; exact map_add (aeval (fun i => x i)) p q
  | mul_X p k hp =>
    convert! hp.mul (EuclideanSpace.proj k).contDiff using 1
    funext x; simp [polynomialExtension]

lemma polynomialExtension_on_sphere (p : Poly) (x : Sphere) :
    polynomialExtension p x = sphereEval p x := by
  have h : aeval (fun i => (x : Ambient) i) =
      (ContinuousMap.evalAlgHom ℝ ℝ x).comp sphereEval := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [sphereEval, sphereCoordinate]
    rfl
  exact congrArg (fun h : Poly →ₐ[ℝ] ℝ => h p) h

lemma radialExtension_pos_smul (f : Sphere → ℝ) (x : Ambient) {a : ℝ} (ha : 0 < a) :
    radialExtension f (a • x) = radialExtension f x := by
  by_cases hx : x = 0
  · simp [hx, radialExtension]
  rw [radialExtension, dite_eq_left (smul_ne_zero ha.ne' hx), radialExtension, dite_eq_left hx]
  congr 1
  apply Subtype.ext
  simp only [normalizeSphere, norm_smul, Real.norm_eq_abs, abs_of_pos ha, mul_inv_rev,
    smul_smul]
  congr 1
  field_simp

lemma radialExtension_isometry (f : Sphere → ℝ) (e : Ambient ≃ₗᵢ[ℝ] Ambient)
    (x : Ambient) (hx : x ≠ 0) :
    radialExtension f (e x) = f (sphereHome e (normalizeSphere ⟨x, hx⟩)) := by
  rw [radialExtension, dite_eq_left (by simpa using e.injective.ne hx)]
  congr 1
  apply Subtype.ext
  simp [normalizeSphere, sphereHome]

lemma polynomial_sphere_smooth (p : Poly) : SmoothSphere (sphereEval p) := by
  have h := (polynomialExtension_smooth p).contMDiff.comp (contMDiff_coe_sphere (n := 2))
  convert! h using 1
  funext x
  exact (polynomialExtension_on_sphere p x).symm

lemma radialExtension_fderiv_self {f : Sphere → ℝ} (hf : SmoothSphere f)
    {x : Ambient} (hx : x ≠ 0) : fderiv ℝ (radialExtension f) x x = 0 := by
  have hd := ((radialExtension_smooth hf).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hd' : HasFDerivAt (radialExtension f) (fderiv ℝ (radialExtension f) x) ((1 : ℝ) • x) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have he : (fun s : ℝ => radialExtension f (s • x)) =ᶠ[nhds 1]
      (fun _ => radialExtension f x) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact radialExtension_pos_smul f x hs
  have h2 := (hasDerivAt_const (1 : ℝ) (radialExtension f x)).congr_of_eventuallyEq he
  simpa using h1.unique h2

lemma smoothRotation_radial_polynomial (p : Poly) (i j : Fin 3) {x : Ambient} (hx : x ≠ 0) :
    smoothRotation i j (radialExtension (sphereEval p)) x =
      radialExtension (sphereEval (rotation i j p)) x := by
  by_cases hij : i = j
  · subst j
    have hg : rotationGenerator i i x = 0 := by ext k; simp [rotationGenerator_apply]
    simp [smoothRotation, hg, rotation_apply, radialExtension]
  have hd := ((radialExtension_smooth (polynomial_sphere_smooth p)).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hd' : HasFDerivAt (radialExtension (sphereEval p))
      (fderiv ℝ (radialExtension (sphereEval p)) x) (planeRotation i j hij 0 x) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) (planeRotation_hasDerivAt i j hij x 0)
  let y : Sphere := normalizeSphere ⟨x, hx⟩
  have h2 := (ContinuousMap.evalCLM (R := ℝ) y).hasFDerivAt.comp_hasDerivAt 0
    (rotationAction_hasDerivAt_zero i j hij p)
  have he : (fun t => radialExtension (sphereEval p) (planeRotation i j hij t x)) =
      fun t => rotationAction i j t p y := by
    funext t
    rw [rotationAction_apply i j hij]
    exact radialExtension_isometry _ _ _ hx
  change HasDerivAt (fun s => radialExtension (sphereEval p) (planeRotation i j hij s x)) _ 0 at h1
  rw [he] at h1
  have h := h1.unique h2
  simpa [smoothRotation, radialExtension, hx, y] using h

lemma rotationGenerator_decomposition (x v : Ambient) :
    ‖x‖ ^ 2 • v = (∑ i : Fin 3, ∑ j : Fin 3, (x i * v j) • rotationGenerator i j x) +
      (∑ i : Fin 3, x i * v i) • x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [Fin.sum_univ_three, rotationGenerator_apply] <;> ring

lemma radial_polynomial_fderiv (p : Poly) {x : Ambient} (hx : x ≠ 0) (v : Ambient) :
    fderiv ℝ (radialExtension (sphereEval p)) x v =
      ∑ i : Fin 3, ∑ j : Fin 3, (x i * v j / ‖x‖ ^ 2) *
        radialExtension (sphereEval (rotation i j p)) x := by
  have h := congrArg (fderiv ℝ (radialExtension (sphereEval p)) x)
    (rotationGenerator_decomposition x v)
  simp only [map_add, map_sum, map_smul, radialExtension_fderiv_self (polynomial_sphere_smooth p) hx,
    smul_eq_mul] at h
  have hrot (i j : Fin 3) : fderiv ℝ (radialExtension (sphereEval p)) x (rotationGenerator i j x) =
      radialExtension (sphereEval (rotation i j p)) x := smoothRotation_radial_polynomial p i j hx
  simp only [hrot] at h
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  apply (eq_div_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).mpr
  simpa [mul_comm, mul_zero] using h

end
end CKSSphericalHarmonics

end

noncomputable section
namespace CKSSpectralHeat
noncomputable section
open Set Filter Real
open scoped Topology ContDiff

lemma eigenvalue_ge_six (n : ℕ) : 6 ≤ eigenvalue n := by
  unfold eigenvalue
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith
lemma eigenvalue_pos (n : ℕ) : 0 < eigenvalue n := by linarith [eigenvalue_ge_six n]

lemma kernel_smooth : ContDiff ℝ ∞ kernel := by unfold kernel; fun_prop

lemma kernel_nonneg_time {t : ℝ} (ht : 0 ≤ t) : kernel t = exp (-t) := by
  simp [kernel, smoothTransition.one_of_one_le (show 1 ≤ t + 1 by linarith)]

lemma kernel_zero {t : ℝ} (ht : t ≤ -1) : kernel t = 0 := by
  simp [kernel, smoothTransition.zero_of_nonpos (show t + 1 ≤ 0 by linarith)]

lemma kernel_derivative_bounded (b : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ t, ‖iteratedDeriv b kernel t‖ ≤ C := by
  have hc : Continuous (iteratedDeriv b kernel) :=
    kernel_smooth.continuous_iteratedDeriv b (by exact_mod_cast (le_top : (b : ℕ∞) ≤ ⊤))
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro t
  by_cases htlo : t < -2
  · have heq : kernel =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds (show t < -1 by linarith)] with x hx
      exact kernel_zero hx.le
    rw [heq.iteratedDeriv_eq b]
    simp [le_trans zero_le_one (le_max_right C 1)]
  by_cases hthi : 1 < t
  · have heq : kernel =ᶠ[𝓝 t] (fun x => exp (-1 * x)) := by
      filter_upwards [Ioi_mem_nhds (show 0 < t by linarith)] with x hx
      simpa using kernel_nonneg_time hx.le
    rw [heq.iteratedDeriv_eq b, iteratedDeriv_exp_const_mul]
    have he : exp (-t) ≤ 1 := exp_le_one_iff.2 (by linarith)
    calc
      ‖(-1 : ℝ) ^ b * exp (-1 * t)‖ = exp (-t) := by
        rw [norm_mul, norm_pow]
        simp [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      _ ≤ 1 := he
      _ ≤ max C 1 := le_max_right _ _
  · exact (hC t ⟨not_lt.mp htlo, not_lt.mp hthi⟩).trans (le_max_left _ _)

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def Rapid (coeff : ℕ → B) : Prop :=
  ∀ b : ℕ, Summable (fun n => eigenvalue n ^ b * ‖coeff n‖)

def inverseCoeff (coeff : ℕ → B) (n : ℕ) : B :=
  (1 - eigenvalue n / 2)⁻¹ • coeff n

lemma inverse_denominator_bound (n : ℕ) : |(1 - eigenvalue n / 2)⁻¹| ≤ 1 / 2 := by
  have he := eigenvalue_ge_six n
  have hd : 2 ≤ |1 - eigenvalue n / 2| := by
    rw [abs_of_neg (by linarith)]
    linarith
  rw [abs_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hd

omit [CompleteSpace B] in
lemma inverseCoeff_rapid [CompleteSpace B] (coeff : ℕ → B) (h : Rapid coeff) : Rapid (inverseCoeff coeff) := by
  intro b
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (eigenvalue_pos n).le _) (norm_nonneg _))
    _ ((h b).mul_left (1 / 2))
  intro n
  rw [inverseCoeff, norm_smul, Real.norm_eq_abs]
  calc
    eigenvalue n ^ b * (|(1 - eigenvalue n / 2)⁻¹| * ‖coeff n‖) ≤
      eigenvalue n ^ b * ((1 / 2) * ‖coeff n‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (inverse_denominator_bound n) (norm_nonneg _))
          (pow_nonneg (eigenvalue_pos n).le _)
    _ = (1 / 2) * (eigenvalue n ^ b * ‖coeff n‖) := by ring

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [CompleteSpace C]

end
end CKSSpectralHeat

end

end OAI
end

section
namespace OAI


noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff

lemma U_open : IsOpen U := isClosed_singleton.isOpen_compl

attribute [local instance] CKSLorentz.two_atLeastTwo

lemma partial_partial {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (i j : Ix) :
    pd i (pd j F) x = fderiv ℝ (fderiv ℝ F) x (e i) (e j) := by
  have hd := ((hF.fderiv_of_isOpen (m := ∞) U_open (by simp)).contDiffAt
    (U_open.mem_nhds hx)).differentiableAt (by simp)
  unfold pd
  rw [fderiv_clm_apply hd (differentiableAt_const (e j))]
  simp

lemma partial_comm {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (i j : Ix) : pd i (pd j F) x = pd j (pd i F) x := by
  rw [partial_partial hF hx, partial_partial hF hx]
  exact ((hF.contDiffAt (U_open.mem_nhds hx)).isSymmSndFDerivAt (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using (ENat.LEInfty.out (m := 2)))).eq _ _

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma radialExtension_norm_bound (f : C(Sphere, ℝ)) (x : Ambient) :
    ‖radialExtension f x‖ ≤ ‖f‖ := by
  by_cases hx : x ≠ 0
  · rw [radialExtension, dite_eq_left hx]
    exact ContinuousMap.norm_coe_le_norm f _
  · simp [radialExtension, hx]

def angularField (i j : Fin 3) (x : Ambient) : Ambient →L[ℝ] ℝ :=
  (x i / ‖x‖ ^ 2) • EuclideanSpace.proj j

lemma angularField_smooth (i j : Fin 3) : ContDiffOn ℝ ∞ (angularField i j) puncturedSpace := by
  have hn : ContDiffOn ℝ ∞ (fun x : Ambient => ‖x‖) puncturedSpace := by
    intro x hx
    exact (contDiffAt_norm ℝ hx).contDiffWithinAt
  exact ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).contDiff.contDiffOn.div (hn.pow 2)
    (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).smul contDiffOn_const

lemma radial_polynomial_hasFDerivAt (p : Poly) {x : Ambient} (hx : x ≠ 0) :
    HasFDerivAt (radialExtension (sphereEval p))
      (∑ i : Fin 3, ∑ j : Fin 3,
        radialExtension (sphereEval (rotation i j p)) x • angularField i j x) x := by
  have hd := ((radialExtension_smooth (polynomial_sphere_smooth p)).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  convert! hd.hasFDerivAt using 1
  ext v
  rw [radial_polynomial_fderiv p hx v]
  simp only [sum_apply, smul_apply, smul_eq_mul,
    angularField, EuclideanSpace.proj, PiLp.proj_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma temporalJet_hasDerivAt (b n : ℕ) (t : ℝ) :
    HasDerivAt (temporalJet b n) (temporalJet (b + 1) n t) t := by
  have hk := (CKSSpectralHeat.kernel_smooth.differentiable_iteratedDeriv b
    (by exact_mod_cast (ENat.natCast_lt_top b))).differentiableAt (x := CKSSpectralHeat.eigenvalue n * t) |>.hasDerivAt
  have h := (hk.comp t ((hasDerivAt_id t).const_mul (CKSSpectralHeat.eigenvalue n))).const_mul
    (CKSSpectralHeat.eigenvalue n ^ b)
  convert! h using 1
  simp only [temporalJet, iteratedDeriv_succ, pow_succ]
  ring

lemma temporalJet_bound (b : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n t,
    ‖temporalJet b n t‖ ≤ C * CKSSpectralHeat.eigenvalue n ^ b := by
  obtain ⟨C, hC, hb⟩ := CKSSpectralHeat.kernel_derivative_bounded b
  refine ⟨C, hC, fun n t => ?_⟩
  rw [temporalJet, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_pos (CKSSpectralHeat.eigenvalue_pos n)]
  nlinarith [mul_le_mul_of_nonneg_left (hb (CKSSpectralHeat.eigenvalue n * t))
    (pow_nonneg (CKSSpectralHeat.eigenvalue_pos n).le b)]

def heatDomain : Set SpaceTime := {z | z.2 ≠ 0}

lemma heatDomain_open : IsOpen heatDomain :=
  isOpen_ne_fun continuous_snd continuous_const

def heatField : Option (Fin 3 × Fin 3) → SpaceTime → SpaceTime →L[ℝ] ℝ
  | none, _ => ContinuousLinearMap.fst ℝ ℝ Ambient
  | some ij, z => (angularField ij.1 ij.2 z.2).comp (ContinuousLinearMap.snd ℝ ℝ Ambient)

lemma heatField_smooth (o : Option (Fin 3 × Fin 3)) : ContDiffOn ℝ ∞ (heatField o) heatDomain := by
  cases o with
  | none => exact contDiffOn_const
  | some ij =>
    exact ((angularField_smooth ij.1 ij.2).comp contDiffOn_snd
      (fun z hz => hz)).clm_comp contDiffOn_const

def heatNext (a : HeatJet) : Option (Fin 3 × Fin 3) → HeatJet
  | none => (a.1 + 1, a.2)
  | some ij => (a.1, ij :: a.2)

lemma heatTerm_derivative_identity (p : ℕ → Poly) (a : HeatJet) (n : ℕ) (z : SpaceTime) :
    (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n z • heatField o z) =
    temporalJet a.1 n z.1 •
      ((∑ i : Fin 3, ∑ j : Fin 3,
        radialExtension (sphereEval (rotation i j (rotationWord a.2 (p n)))) z.2 •
          angularField i j z.2).comp (ContinuousLinearMap.snd ℝ ℝ Ambient)) +
    radialExtension (sphereEval (rotationWord a.2 (p n))) z.2 •
      ((ContinuousLinearMap.toSpanSingleton ℝ (temporalJet (a.1 + 1) n z.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ Ambient)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [Fintype.sum_option, Fintype.sum_prod_type, heatTerm, heatNext, heatField,
    rotationWord, sum_apply, smul_apply,
    add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Finset.mul_sum]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  exact add_comm _ _

lemma heatTerm_hasFDerivAt (p : ℕ → Poly) (a : HeatJet) (n : ℕ) (z : SpaceTime)
    (hz : z ∈ heatDomain) :
    HasFDerivAt (heatTerm p a n)
      (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n z • heatField o z) z := by
  have ht := (temporalJet_hasDerivAt a.1 n z.1).hasFDerivAt.comp z
    (ContinuousLinearMap.fst ℝ ℝ Ambient).hasFDerivAt
  have hx := (radial_polynomial_hasFDerivAt (rotationWord a.2 (p n)) hz).comp z
    (ContinuousLinearMap.snd ℝ ℝ Ambient).hasFDerivAt
  rw [heatTerm_derivative_identity]
  convert! ht.mul hx using 1

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSDifferentialSeries
noncomputable section
open Set Filter
open scoped Topology ContDiff
variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
variable {s : Set E} (hs : IsOpen s)
variable (A : J → E → E →L[ℝ] ℝ) (hA : ∀ j, ContDiffOn ℝ ∞ (A j) s)
variable (next : I → J → I) (F : I → ℕ → E → ℝ)
variable (hF : ∀ i n x, x ∈ s → HasFDerivAt (F i n)
  (∑ j, F (next i j) n x • A j x) x)
variable (bound : ∀ i, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n x, x ∈ s → ‖F i n x‖ ≤ u n)

def series (i : I) (x : E) : ℝ := ∑' n, F i n x

include bound

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma series_summable [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : I) {x : E} (hx : x ∈ s) : Summable (fun n => F i n x) := by
  obtain ⟨u, hu, hb⟩ := bound i
  exact Summable.of_norm_bounded hu (fun n => hb n x hx)

include hF

lemma series_continuous (i : I) : ContinuousOn (series F i) s := by
  obtain ⟨u, hu, hb⟩ := bound i
  exact continuousOn_tsum (fun n x hx => (hF i n x hx).continuousAt.continuousWithinAt) hu hb

include hs hA

lemma series_hasFDerivAt (i : I) {x : E} (hx : x ∈ s) :
    HasFDerivAt (series F i) (∑ j, series F (next i j) x • A j x) x := by
  have bounds := bound
  choose u hu hb using bounds
  let K : ℝ := (∑ j, ‖A j x‖) + 1
  have hc : ContinuousAt (fun y => ∑ j, ‖A j y‖) x := by
    exact (continuousOn_finsetSum _ (fun j _ =>
      (hA j).continuousOn.norm)).continuousAt (hs.mem_nhds hx)
  have he : ∀ᶠ y in 𝓝 x, (∑ j, ‖A j y‖) < K :=
    hc.eventually_lt continuousAt_const (by dsimp [K]; linarith)
  have hn : {y | y ∈ s ∧ (∑ j, ‖A j y‖) < K} ∈ 𝓝 x :=
    inter_mem (hs.mem_nhds hx) he
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hn
  have hlocal (j : J) (y : E) (hy : y ∈ Metric.ball x r) : ‖A j y‖ ≤ K := by
    exact (Finset.single_le_sum (fun k _ => norm_nonneg (A k y))
      (Finset.mem_univ j)).trans (hrs hy).2.le
  have hus : Summable (fun n => K * ∑ j, u (next i j) n) :=
    (summable_sum (fun j _ => hu (next i j))).mul_left K
  have hderiv := hasFDerivAt_tsum_of_isPreconnected hus Metric.isOpen_ball
    (convex_ball x r).isPreconnected
    (fun n y hy => hF i n y (hrs hy).1)
    (fun n y hy => (show ‖∑ j, F (next i j) n y • A j y‖ ≤ K * ∑ j, u (next i j) n from by
      calc
        ‖∑ j, F (next i j) n y • A j y‖ ≤ ∑ j, ‖F (next i j) n y • A j y‖ := norm_sum_le _ _
        _ ≤ ∑ j, u (next i j) n * K := by
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_smul]
          exact mul_le_mul (hb _ n y (hrs hy).1) (hlocal j y hy) (norm_nonneg _)
            ((norm_nonneg _).trans (hb _ n y (hrs hy).1))
        _ = K * ∑ j, u (next i j) n := by rw [← Finset.sum_mul]; ring))
    (Metric.mem_ball_self hr) (series_summable F bound i hx) (Metric.mem_ball_self hr)
  convert! hderiv using 1
  symm
  rw [Summable.tsum_finsetSum (fun j _ => (series_summable F bound (next i j) hx).smul_const (A j x))]
  apply Finset.sum_congr rfl
  intro j hj
  exact (series_summable F bound (next i j) hx).tsum_smul_const (A j x)

theorem series_contDiff (i : I) : ContDiffOn ℝ ∞ (series F i) s := by
  apply contDiffOn_infty.mpr
  intro N
  induction N generalizing i with
  | zero => exact contDiffOn_zero.mpr (series_continuous A next F hF bound i)
  | succ N ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs.uniqueDiffOn).mpr
    refine ⟨by simp, ⟨fun x => ∑ j, series F (next i j) x • A j x, ?_, ?_⟩⟩
    · exact ContDiffOn.sum (fun j _ => (ih (next i j)).smul ((hA j).of_le (by exact_mod_cast (le_top : (N : ℕ∞) ≤ ⊤))))
    · intro x hx
      exact (series_hasFDerivAt hs A hA next F hF bound i hx).hasFDerivWithinAt

end
end CKSDifferentialSeries

end

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold

lemma heatTerm_bound (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n z, z ∈ heatDomain → ‖heatTerm p a n z‖ ≤ u n := by
  obtain ⟨C, hC, hb⟩ := temporalJet_bound a.1
  refine ⟨fun n => C * (CKSSpectralHeat.eigenvalue n ^ a.1 *
    ‖sphereEval (rotationWord a.2 (p n))‖), (hp a.2 a.1).mul_left C, ?_⟩
  intro n z hz
  dsimp only
  rw [heatTerm, norm_mul, ← mul_assoc]
  exact mul_le_mul (hb n z.1) (radialExtension_norm_bound _ _) (norm_nonneg _)
    (mul_nonneg hC (pow_nonneg (CKSSpectralHeat.eigenvalue_pos n).le _))

theorem jointHeatSeries_smooth (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) :
    ContDiffOn ℝ ∞ (jointHeatSeries p a) heatDomain :=
  CKSDifferentialSeries.series_contDiff heatDomain_open heatField heatField_smooth
    heatNext (heatTerm p) (heatTerm_hasFDerivAt p) (heatTerm_bound p hp) a

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e grad hess pd proj roundLaplacian sphereGradient tensorDivergence)
open scoped Topology ContDiff

lemma projected_frame (x : Point) (i j : Ix) :
    proj (fun k => sphereParam x k) i j =
      thetaFrame x i * thetaFrame x j + phiUnit x i * phiUnit x j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [proj,sphereParam,thetaFrame,phiUnit,Fin.reduceEq]
  all_goals ring_nf <;> simp only [Real.sin_sq] <;> ring

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

lemma spatialHeat_smooth (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) (t : ℝ) :
    ContDiffOn ℝ ∞ (spatialHeat p a t) puncturedSpace :=
  (jointHeatSeries_smooth p hp a).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => hx)

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
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

lemma rotationWord_smul (w : List (Fin 3 × Fin 3)) (c : ℝ) (p : Poly) :
    rotationWord w (c • p) = c • rotationWord w p := by
  induction w with
  | nil => rfl
  | cons ij w ih => simp only [rotationWord, ih, Derivation.map_smul]

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix Mat e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

lemma pair_symm (M : Mat) (hM : ∀ i j, M i j = M j i) (v w : E) :
    pair M v w = pair M w v := by
  unfold pair
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [hM j i]
  ring

lemma pair_normal (M : Mat) (n v : E) (hn : ∀ j : Ix, ∑ i : Ix, n i * M i j = 0) :
    pair M n v = 0 := by
  unfold pair
  rw [sum_comm]
  have he (j : Ix) : (∑ i : Ix, n i * v j * M i j) = v j * ∑ i : Ix, n i * M i j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  simp only [he,hn,mul_zero,sum_const_zero]

lemma pair_trace (M : Mat) (x : Point)
    (hn : ∀ j : Ix, ∑ i : Ix, sphereParam x i * M i j = 0) :
    pair M (thetaFrame x) (thetaFrame x) + pair M (phiUnit x) (phiUnit x) = ∑ i : Ix, M i i := by
  have he : pair M (thetaFrame x) (thetaFrame x) + pair M (phiUnit x) (phiUnit x) =
      ∑ i : Ix, ∑ j : Ix, proj (fun k => sphereParam x k) i j * M i j := by
    simp [pair,projected_frame,add_mul,sum_add_distrib]
  rw [he]
  simp only [proj,sub_mul,sum_sub_distrib,ite_mul,one_mul,zero_mul,sum_ite_eq]
  change (∑ i : Ix, M i i) - pair M (sphereParam x) (sphereParam x) = _
  rw [pair_normal M _ _ hn,sub_zero]

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

lemma inversePolynomials_rapid (p : ℕ → Poly) (hp : PolynomialRapid p) :
    PolynomialRapid (inversePolynomials p) := by
  intro w b
  have h := CKSSpectralHeat.inverseCoeff_rapid (fun n => sphereEval (rotationWord w (p n))) (hp w) b
  simpa only [inversePolynomials, rotationWord_smul, map_smul, CKSSpectralHeat.inverseCoeff] using h

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff
open CKSSphericalHarmonics

lemma heatTensor_symmetric (p : ℕ → Poly) (hp : PolynomialRapid p)
    (t : ℝ) {x : E} (hx : ‖x‖ = 1) (i j : Ix) :
    heatTensor p t x i j = heatTensor p t x j i := by
  have hn : x ∈ U := by intro h; simp [h] at hx
  exact hessTF_symm _ _ (fun a b => partial_comm
    (spatialHeat_smooth _ (inversePolynomials_rapid p hp) _ t) hn a b) i j

lemma heatTensor_tangent (p : ℕ → Poly) (t : ℝ) {x : E} (hx : ‖x‖ = 1) (j : Ix) :
    ∑ i : Ix, x i * heatTensor p t x i j = 0 :=
  hessTF_normal_left (unit_sum_sq hx) _ j

lemma heatTensor_trace_zero (p : ℕ → Poly) (t : ℝ) {x : E} (hx : ‖x‖ = 1) :
    ∑ i : Ix, heatTensor p t x i i = 0 :=
  hessTF_trace_zero (unit_sum_sq hx) _

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics
open CKSInducedSphere (E Ix Mat U)
open scoped Topology ContDiff

lemma positiveChart_open : IsOpen positiveChart := isOpen_lt continuous_const (coord 0).continuous

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology Matrix

 def sphericalAngularMetric (x : CKSRealizedRound.Point) : CKSAngularGeometry.Mat :=
  Matrix.diagonal ![1, Real.sin (x 1)^2]

lemma sphericalAngularMetric_posDef {x : CKSRealizedRound.Point} (hs : Real.sin (x 1) ≠ 0) :
    (sphericalAngularMetric x).PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i
  · norm_num
  · exact sq_pos_of_ne_zero hs

lemma outerMetric_foliation (F : CKSRealizedRound.Point → ℝ) (v : ℝ → ℝ) (x : CKSRealizedRound.Point) :
    CKSRealizedRound.outerMetric F v x =
      CKSAngularGeometry.foliationMetric (CKSRealizedRound.lapse F v x)
        (x 0 ^ 2 • sphericalAngularMetric x) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CKSRealizedRound.outerMetric, CKSRealizedRound.metric,
      CKSAngularGeometry.foliationMetric,CKSAngularGeometry.metricBlock,sphericalAngularMetric,
      Matrix.of_apply,Matrix.smul_apply]

end
end CKSSphericalChart

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
namespace CKSRealizedRound
noncomputable section
open Matrix CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma contDiffAt_normalEntry {v β : ℝ → ℝ} {r : ℝ}
    (hv : ContDiffAt ℝ ∞ v r) (hβ : ContDiffAt ℝ ∞ β r) (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (normalEntry v β) r := by
  exact (hv.derivWithin (m := ∞) (by simp)).add
    (hβ.div (contDiffAt_id.pow 2) (pow_ne_zero _ hr))

lemma contDiffAt_correctionCoeff {v : ℝ → ℝ} {r : ℝ}
    (hv : ContDiffAt ℝ ∞ v r) (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (correctionCoeff v) r := by
  exact (contDiffAt_id.mul ((hv.derivWithin (m := ∞) (by simp)).sub
    (hv.div contDiffAt_id hr))).div (contDiffAt_const.add (hv.pow 2))
      (ne_of_gt (by positivity))

lemma contDiffAt_correctedComponent {v : ℝ → ℝ} {a : Point → ℝ} {x : Point}
    (hv : ContDiffAt ℝ ∞ v (x 0)) (ha : ContDiffAt ℝ ∞ a x) (hr : x 0 ≠ 0) :
    ContDiffAt ℝ ∞ (correctedComponent v a) x :=
  (contDiffAt_radial (contDiffAt_correctionCoeff hv hr)).mul ha

lemma tensor_contDiffAt {u : Point → ℝ} {v : ℝ → ℝ} {L a b : Point → ℝ} {x : Point}
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v (x 0))
    (hL : ContDiffAt ℝ ∞ L x) (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x)
    (h0 : u x ≠ 0) : ContDiffAt ℝ ∞ (tensor u v L a b) x := by
  have hvr := (contDiffAt_radial hv).mul (coord 0).contDiff.contDiffAt
  have hs : ContDiffAt ℝ ∞ (fun y : Point => Real.sin (y 1)^2) x := by fun_prop
  have hfirst := hL.div (hu.pow 2) (pow_ne_zero _ h0)
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hfirst
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact hvr.add ha
  · exact hb
  · exact contDiffAt_const
  · exact hb
  · exact (hvr.sub ha).mul hs

lemma tensor_hermitian (u : Point → ℝ) (v : ℝ → ℝ) (L a b : Point → ℝ) (x : Point) :
    (tensor u v L a b x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [tensor]

lemma outerTensor_contDiffAt {F a b : Point → ℝ} {v β : ℝ → ℝ} {x : Point}
    (hF : ContDiffAt ℝ ∞ F x) (hv : ContDiffAt ℝ ∞ v (x 0))
    (hβ : ContDiffAt ℝ ∞ β (x 0))
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x)
    (hr : x 0 ≠ 0) (hp : 0 < radicand F v x) :
    ContDiffAt ℝ ∞ (outerTensor F v β a b) x :=
  tensor_contDiffAt (contDiffAt_lapse hF hv hr hp) hv
    (contDiffAt_radial (contDiffAt_normalEntry hv hβ hr))
    (contDiffAt_correctedComponent hv ha hr) (contDiffAt_correctedComponent hv hb hr)
    (lapse_pos hp).ne'

end
end CKSRealizedRound

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSAngularGeometry CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise Matrix

lemma sphericalAngularMetric_contDiff : ContDiff ℝ ∞ sphericalAngularMetric := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp [sphericalAngularMetric]
  all_goals fun_prop

lemma roundAngularMetric_contDiff :
    ContDiff ℝ ∞ (fun y : CKSRealizedRound.Point => y 0 ^ 2 • sphericalAngularMetric y) := by
  have hr : ContDiff ℝ ∞ (fun y : CKSRealizedRound.Point => y 0 ^ 2) :=
    (coord 0).contDiff.pow 2
  exact hr.smul sphericalAngularMetric_contDiff

lemma roundAngularMetric_posDef {x : CKSRealizedRound.Point}
    (hr : x 0 ≠ 0) (hs : Real.sin (x 1) ≠ 0) :
    (x 0 ^ 2 • sphericalAngularMetric x).PosDef :=
  (sphericalAngularMetric_posDef hs).smul (sq_pos_of_ne_zero hr)

lemma roundAngularMetric_eventually_posDef {x : CKSRealizedRound.Point}
    (hr : x 0 ≠ 0) (hs : Real.sin (x 1) ≠ 0) :
    ∀ᶠ y in 𝓝 x, (y 0 ^ 2 • sphericalAngularMetric y).PosDef := by
  have hrn := (coord 0).continuous.continuousAt (x := x).eventually_ne hr
  have hsn := (Real.continuous_sin.comp (coord 1).continuous).continuousAt (x := x).eventually_ne hs
  filter_upwards [hrn,hsn] with y hyr hys
  exact roundAngularMetric_posDef hyr hys

end
end CKSSphericalChart

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
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma sphericalMap_euclidean (x : PhysicalPoint) :
    toPoint.symm (sphericalMap x) = x 0 • sphereParam x := toPoint.symm_apply_apply _
lemma sphericalMap_norm {x : PhysicalPoint} (hx : 0 < x 0) :
    ‖toPoint.symm (sphericalMap x)‖ = x 0 := by
  rw [sphericalMap_euclidean,norm_smul,Real.norm_eq_abs,abs_of_pos hx,sphereParam_norm,mul_one]
lemma sphericalMap_unit {x : PhysicalPoint} (hx : 0 < x 0) :
    unitVector (toPoint.symm (sphericalMap x))=sphereParam x := by
  rw [unitVector,sphericalMap_norm hx,sphericalMap_euclidean,smul_smul,
    inv_mul_cancel₀ hx.ne',one_smul]

lemma sphericalMap_mass (f₀ : C(Sphere,ℝ)) (m R : ℝ) {x : PhysicalPoint}
    (hx : 0 < x 0) : cartMass f₀ m R (toPoint.symm (sphericalMap x)) = outerMass f₀ m R x := by
  rw [cartMass,sphericalMap_norm hx,sphericalMap_unit hx]
  rfl
lemma sphericalMap_radicand (f₀ : C(Sphere,ℝ)) (m R : ℝ) {x : PhysicalPoint}
    (hx : 0 < x 0) : radicand f₀ m R (toPoint.symm (sphericalMap x)) =
      CKSRealizedRound.radicand (outerMass f₀ m R) (bendingV R) x := by
  rw [radicand,sphericalMap_norm hx,sphericalMap_mass f₀ m R hx]
  rfl
lemma metricPair_toPoint (M : AmbientMat) (v w : E) :
    metricPair M (toPoint v) (toPoint w) = pair M v w := by
  unfold metricPair pair
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change M i j*v i*w j=v i*w j*M i j
  ring
lemma pair_add_matrix (A B : AmbientMat) (v w : E) : pair (A+B) v w=pair A v w+pair B v w := by
  simp [pair,mul_add,Finset.sum_add_distrib]
lemma pair_smul_matrix (c : ℝ) (A : AmbientMat) (v w : E) : pair (c • A) v w=c*pair A v w := by
  simp only [pair,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma pair_rankOne (n : Fin 3 → ℝ) (v w : E) :
    pair (vecMulVec n n) v w=(∑ i,n i*v i)*(∑ i,n i*w i) := by
  simp only [pair,Matrix.vecMulVec_apply,Fin.sum_univ_three]
  ring
lemma normal_sphericalMap {x : PhysicalPoint} (hx : 0 < x 0) :
    normal (toPoint.symm (sphericalMap x)) = fun i => sphereParam x i := by
  funext i
  change (toPoint.symm (sphericalMap x)) i / ‖toPoint.symm (sphericalMap x)‖ = sphereParam x i
  rw [sphericalMap_norm hx,sphericalMap_euclidean]
  change (x 0 * sphereParam x i)/x 0=sphereParam x i
  field_simp
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma pair_one_sphericalBasis (x : PhysicalPoint) (i j : Fin 3) :
    pair (1 : AmbientMat) (sphericalBasis x i) (sphericalBasis x j)=
      if i=j then sphericalScale x i ^ 2 else 0 := by
  rw [sphericalBasis_scaled,sphericalBasis_scaled,pair_smul_left,pair_smul_right,
    pair_one_unitBasis]
  split_ifs with h
  · subst j; ring
  · ring
lemma normalDot_sphericalBasis (x : PhysicalPoint) (i : Fin 3) :
    (∑ j, sphereParam x j * sphericalBasis x i j)=if i=0 then 1 else 0 := by
  rw [← pair_one,sphericalBasis_scaled,pair_smul_right]
  change sphericalScale x i * pair (1 : AmbientMat) (unitBasis x 0) (unitBasis x i)=_
  rw [pair_one_unitBasis]
  fin_cases i <;> simp [sphericalScale]
lemma pair_rankOne_sphericalBasis (x : PhysicalPoint) (i j : Fin 3) :
    pair (vecMulVec (fun a => sphereParam x a) (fun a => sphereParam x a))
      (sphericalBasis x i) (sphericalBasis x j)=
        (if i=0 then 1 else 0)*(if j=0 then 1 else 0) := by
  rw [pair_rankOne,normalDot_sphericalBasis,normalDot_sphericalBasis]
end
end CKSCartesianOuter

end


noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma sphericalChart_mem (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : x ∈ (sphericalChart x hx hs).source :=
  sphericalMap_smooth.contDiffAt.mem_toOpenPartialHomeomorph_source
    (sphericalDerivative_hasFDerivAt x hx hs) (by simp)
lemma sphericalChart_inverse_smooth (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) :
    ∀ᶠ y in 𝓝 (sphericalMap x), ContDiffAt ℝ ∞ (sphericalChart x hx hs).symm y := by
  let e := sphericalChart x hx hs
  have hex : x ∈ e.source := sphericalChart_mem x hx hs
  have hix := e.left_inv hex
  have hr : ∀ᶠ z in 𝓝 x, z 0≠0 ∧ Real.sin (z 1)≠0 := by
    filter_upwards [(coord 0).continuous.continuousAt (x := x) |>.eventually_ne hx,
      (Real.continuous_sin.comp (coord 1).continuous).continuousAt (x := x) |>.eventually_ne hs]
      with z hz hsz
    exact ⟨hz,hsz⟩
  have hnear : ∀ᶠ y in 𝓝 (e x), e.symm y 0≠0 ∧ Real.sin (e.symm y 1)≠0 :=
    (e.symm.continuousAt (e.map_source hex)).eventually (hix ▸ hr)
  filter_upwards [e.open_target.mem_nhds (e.map_source hex),hnear] with y hy hreg
  exact e.contDiffAt_symm hy
    (sphericalDerivative_hasFDerivAt (e.symm y) hreg.1 hreg.2)
    sphericalMap_smooth.contDiffAt
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
theorem spherical_metric_pullback (f₀ : C(Sphere,ℝ)) (m R : ℝ) {x : PhysicalPoint}
    (hx : 0 < x 0) (hp : 0 < radicand f₀ m R (toPoint.symm (sphericalMap x))) :
    coordinatePullback sphericalMap (physicalMetric f₀ m R) x =
      outerMetric (outerMass f₀ m R) (bendingV R) x := by
  have hA := sphericalMap_radicand f₀ m R hx
  have hL : lapse (outerMass f₀ m R) (bendingV R) x ^ 2 =
      radicand f₀ m R (toPoint.symm (sphericalMap x)) := by
    rw [hA,lapse,Real.sq_sqrt (hA ▸ hp.le)]
  ext i j
  change metricPair (metric f₀ m R (toPoint.symm (sphericalMap x)))
    (fderiv ℝ sphericalMap x (basis i)) (fderiv ℝ sphericalMap x (basis j)) = _
  rw [sphericalMap_fderiv,sphericalMap_fderiv,metricPair_toPoint,metric,
    pair_add_matrix,pair_smul_matrix,normal_sphericalMap hx,
    pair_one_sphericalBasis,pair_rankOne_sphericalBasis]
  fin_cases i <;> fin_cases j <;>
    simp [outerMetric,CKSRealizedRound.metric,sphericalScale,hL]
  ring
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma pair_sub_matrix (A B : AmbientMat) (v w : E) : pair (A-B) v w=pair A v w-pair B v w := by
  simp [pair,mul_sub,Finset.sum_sub_distrib]
lemma heat_sphericalBasis (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (R : ℝ)
    (x : PhysicalPoint) (i j : Fin 3) :
    pair (canonicalT f₀ (heatTime R (x 0)) (sphereParam x))
      (sphericalBasis x i) (sphericalBasis x j) = x 0 ^ 2 *
      (!![0,0,0; 0,outerA f₀ R x,outerPhi f₀ R x;
          0,outerPhi f₀ R x,-outerA f₀ R x*Real.sin (x 1)^2] : AmbientMat) i j := by
  let T := canonicalT f₀ (heatTime R (x 0)) (sphereParam x)
  have hN : ∀ j, ∑ i, sphereParam x i*T i j=0 :=
    heatTensor_tangent (heatPolynomials f₀) _ (sphereParam_norm x)
  have hS : ∀ i j, T i j=T j i :=
    heatTensor_symmetric (heatPolynomials f₀) (smoothDatum_rapid f₀ hf₀) _ (sphereParam_norm x)
  have hTr : ∑ i,T i i=0 := heatTensor_trace_zero (heatPolynomials f₀) _ (sphereParam_norm x)
  have hn (v : E) : pair T (sphereParam x) v=0 := pair_normal T _ _ hN
  have hn' (v : E) : pair T v (sphereParam x)=0 := (pair_symm T hS _ _).trans (hn v)
  have hu : pair T (phiUnit x) (phiUnit x) = -pair T (thetaFrame x) (thetaFrame x) := by
    have hh := pair_trace T x hN
    rw [hTr] at hh
    linarith
  have htu : pair T (phiUnit x) (thetaFrame x)=pair T (thetaFrame x) (phiUnit x) :=
    pair_symm T hS _ _
  change pair T (sphericalBasis x i) (sphericalBasis x j)=_
  fin_cases i <;> fin_cases j <;>
    simp [sphericalBasis,phiFrame,hn,hn',hu,htu,outerA,outerPhi,chartTensorA,
      chartTensorPhi,tensorA,tensorPhi,tensorB,T,pair_smul_left,pair_smul_right] <;> ring

theorem spherical_tensor_pullback (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m R : ℝ)
    {x : PhysicalPoint} (hx : 0 < x 0)
    (hp : 0 < radicand f₀ m R (toPoint.symm (sphericalMap x))) :
    coordinatePullback sphericalMap (physicalTensor f₀ m R) x =
      outerTensor (outerMass f₀ m R) (bendingV R) (bendingBeta R)
        (outerA f₀ R) (outerPhi f₀ R) x := by
  have hA := sphericalMap_radicand f₀ m R hx
  have hL : lapse (outerMass f₀ m R) (bendingV R) x ^ 2 =
      radicand f₀ m R (toPoint.symm (sphericalMap x)) := by
    rw [hA,lapse,Real.sq_sqrt (hA ▸ hp.le)]
  ext i j
  change metricPair (tensor f₀ m R (toPoint.symm (sphericalMap x)))
    (fderiv ℝ sphericalMap x (basis i)) (fderiv ℝ sphericalMap x (basis j)) = _
  rw [sphericalMap_fderiv,sphericalMap_fderiv,metricPair_toPoint,tensor,
    sphericalMap_norm hx,sphericalMap_unit hx,normal_sphericalMap hx]
  simp only [pair_add_matrix,pair_smul_matrix,pair_sub_matrix,
    pair_one_sphericalBasis,pair_rankOne_sphericalBasis,heat_sphericalBasis f₀ hf₀]
  fin_cases i <;> fin_cases j <;>
    simp [outerTensor,CKSRealizedRound.tensor,sphericalScale,hL,correctedComponent,radial] <;>
      field_simp
  ring
end
end CKSCartesianOuter

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
lemma round_smoothOrthonormalAt {F : CKSRealizedRound.Point → ℝ} {v : ℝ → ℝ}
    {x : PhysicalPoint} (hF : ContDiffAt ℝ ∞ F x) (hv : ContDiffAt ℝ ∞ v (x 0))
    (hr : x 0≠0) (hs : Real.sin (x 1)≠0) (hp : 0 < CKSRealizedRound.radicand F v x) :
    SmoothOrthonormalAt (outerMetric F v)
      (fun i y => adaptedFrame (lapse F v y) (y 0^2 • sphericalAngularMetric y) 0 i) x := by
  have hu := contDiffAt_lapse hF hv hr hp
  have hg := roundAngularMetric_contDiff.contDiffAt (x := x)
  have h0 := (lapse_pos hp).ne'
  have hpos := roundAngularMetric_posDef hr hs
  have hG : outerMetric F v = fun y => foliationMetric (lapse F v y)
      (y 0 ^ 2 • sphericalAngularMetric y) 0 := funext (outerMetric_foliation F v)
  have had := (foliation_actualAdaptedAt hu hg
    (contDiffAt_const (c := (0 : CKSAngularGeometry.Point))) h0
      (roundAngularMetric_eventually_posDef hr hs)).self_of_nhds
  rw [←hG] at had
  refine ⟨?_,?_,had.2.2.1,had.2.2.2.1,had.2.2.2.2.1⟩
  · rw [hG]
    exact foliationMetric_contDiffAt hu hg contDiffAt_const h0
  · intro i
    exact adaptedFrame_contDiffAt hu hg (contDiffAt_const (c := (0 : CKSAngularGeometry.Point))) hpos i
end
end CKSAngularGeometry

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
theorem local_coordinate_energy_pushforward
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y)
    (hi : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ e.symm y)
    (hE : ∀ᶠ y in 𝓝 x, SmoothOrthonormalAt (coordinatePullback e G) E y)
    (hK : ContDiffAt ℝ ∞ (coordinatePullback e K) x)
    (hs : (coordinatePullback e K x).IsHermitian) :
    (physicalMetricJet G (e x)).energy (physicalTensorJet K (e x)) =
    (physicalMetricJet (coordinatePullback e G) x).energy
      (physicalTensorJet (coordinatePullback e K) x) := by
  have hEq (A : PhysicalPoint → AmbientMat) :
      coordinatePullback e.symm (coordinatePullback e A) =ᶠ[𝓝 (e x)] A := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx),hi,
      (e.symm.continuousAt (e.map_source hx)).eventually (e.left_inv hx ▸ he)] with y hy hiy hey
    have hh := coordinatePullback_symm e A (e.map_target hy)
      (hey.differentiableAt (by simp)) (by simpa only [e.right_inv hy] using hiy.differentiableAt (by simp))
    simpa only [e.right_inv hy] using hh
  have h := local_coordinate_energy_pullback e.symm (coordinatePullback e G)
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
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma spherical_physical_energy (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0<R) {x : PhysicalPoint} (hx : 0<x 0) (hs : Real.sin (x 1)≠0)
    (hp : 0<radicand f₀ m R (toPoint.symm (sphericalMap x))) :
    (physicalMetricJet (physicalMetric f₀ m R) (sphericalMap x)).energy
      (physicalTensorJet (physicalTensor f₀ m R) (sphericalMap x)) =
    (metricJet (lapse (outerMass f₀ m R) (bendingV R)) x).energy
      (tensorJet (lapse (outerMass f₀ m R) (bendingV R)) (bendingV R)
        (radial (normalEntry (bendingV R) (bendingBeta R)))
        (correctedComponent (bendingV R) (outerA f₀ R))
        (correctedComponent (bendingV R) (outerPhi f₀ R)) x) := by
  have hF (y : PhysicalPoint) (hy : 0<y 0) :=
    (outerMass_smooth f₀ hf₀ m hR).contDiffAt (positiveChart_open.mem_nhds hy)
  have hv (y : PhysicalPoint) (hy : 0<y 0) :=
    (bendingV_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hy)
  have hpx : 0<CKSRealizedRound.radicand (outerMass f₀ m R) (bendingV R) x :=
    sphericalMap_radicand f₀ m R hx ▸ hp
  have hreg : ∀ᶠ y in 𝓝 x, 0<y 0 ∧ Real.sin (y 1)≠0 ∧
      0<CKSRealizedRound.radicand (outerMass f₀ m R) (bendingV R) y := by
    filter_upwards [(coord 0).continuous.continuousAt (x := x) |>.eventually (isOpen_Ioi.mem_nhds hx),
      (Real.continuous_sin.comp (coord 1).continuous).continuousAt (x := x) |>.eventually_ne hs,
      (contDiffAt_radicand (hF x hx) (hv x hx) hx.ne').continuousAt.eventually (isOpen_Ioi.mem_nhds hpx)]
      with y hy hsy hpy
    exact ⟨hy,hsy,hpy⟩
  have hEqG : coordinatePullback sphericalMap (physicalMetric f₀ m R) =ᶠ[𝓝 x]
      outerMetric (outerMass f₀ m R) (bendingV R) := by
    filter_upwards [hreg] with y hy
    exact spherical_metric_pullback f₀ m R hy.1 ((sphericalMap_radicand f₀ m R hy.1).symm ▸ hy.2.2)
  have hEqK : coordinatePullback sphericalMap (physicalTensor f₀ m R) =ᶠ[𝓝 x]
      outerTensor (outerMass f₀ m R) (bendingV R) (bendingBeta R) (outerA f₀ R) (outerPhi f₀ R) := by
    filter_upwards [hreg] with y hy
    exact spherical_tensor_pullback f₀ hf₀ m R hy.1 ((sphericalMap_radicand f₀ m R hy.1).symm ▸ hy.2.2)
  let frame : LocalFrame := fun i y => adaptedFrame
    (lapse (outerMass f₀ m R) (bendingV R) y) (y 0^2 • sphericalAngularMetric y) 0 i
  have hFrame : ∀ᶠ y in 𝓝 x, SmoothOrthonormalAt
      (coordinatePullback sphericalMap (physicalMetric f₀ m R)) frame y := by
    filter_upwards [hreg,hEqG.eventually_nhds] with y hy heq
    exact (round_smoothOrthonormalAt (hF y hy.1) (hv y hy.1) hy.1.ne' hy.2.1 hy.2.2).congr_metric heq
  have ha := (outerA_smooth f₀ hf₀ hR).contDiffAt (positiveChart_open.mem_nhds hx)
  have hb := (outerPhi_smooth f₀ hf₀ hR).contDiffAt (positiveChart_open.mem_nhds hx)
  have hK := (outerTensor_contDiffAt (hF x hx) (hv x hx) (bendingBeta_smooth R).contDiffAt ha hb hx.ne' hpx).congr_of_eventuallyEq hEqK
  have hsymm : (coordinatePullback sphericalMap (physicalTensor f₀ m R) x).IsHermitian := by
    rw [hEqK.self_of_nhds]
    exact CKSRealizedRound.tensor_hermitian ..
  have h := local_coordinate_energy_pushforward (sphericalChart x hx.ne' hs)
    (physicalMetric f₀ m R) (physicalTensor f₀ m R) frame
    (sphericalChart_mem x hx.ne' hs) (Eventually.of_forall fun y => sphericalMap_smooth.contDiffAt)
    (sphericalChart_inverse_smooth x hx.ne' hs) hFrame hK hsymm
  change (physicalMetricJet (physicalMetric f₀ m R) (sphericalMap x)).energy
      (physicalTensorJet (physicalTensor f₀ m R) (sphericalMap x)) =
    (physicalMetricJet (coordinatePullback sphericalMap (physicalMetric f₀ m R)) x).energy
      (physicalTensorJet (coordinatePullback sphericalMap (physicalTensor f₀ m R)) x) at h
  rw [physicalMetricJet_congr hEqG,physicalTensorJet_congr hEqK] at h
  exact h
end
end CKSCartesianOuter

end






























end OAI
end

theorem solution : type_of% @OAI.CKSCartesianOuter.spherical_physical_energy := @OAI.CKSCartesianOuter.spherical_physical_energy
