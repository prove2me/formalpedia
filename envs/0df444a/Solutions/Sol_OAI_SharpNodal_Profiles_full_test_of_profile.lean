-- Prove2me | solution 1 for OAI.SharpNodal.Profiles.full_test_of_profile
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:21:10.624354+00:00
-- url     : https://prove2.me/submissions/f4faff35-be8d-4247-a68e-d925a31c45e6

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000

section
-- module Solutions.OAIQ4_Nl.NodalLength_Integration
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma partial_mul {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (i : Fin 2) (x : Plane) :
    coordPartial (fun y => f y * g y) i x =
      coordPartial f i x * g x + f x * coordPartial g i x := by
  unfold coordPartial
  rw [fderiv_fun_mul (hf.differentiable (by simp)).differentiableAt
    (hg.differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma integrable_mul_compact_right {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport g) : Integrable (fun x => f x * g x) := by
  exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left

lemma integral_mul_partial {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport g) (i : Fin 2) :
    (∫ x, f x * coordPartial g i x) = -(∫ x, coordPartial f i x * g x) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_mul_compact_right (smooth_partial hf i) hg hc
  · exact integrable_mul_compact_right hf (smooth_partial hg i) (compact_partial hc i)
  · exact integrable_mul_compact_right hf hg hc
  · intro x _
    exact (hf.differentiable (by simp)).differentiableAt
  · intro x _
    exact (hg.differentiable (by simp)).differentiableAt

lemma partial_partial {f : Plane → ℝ} (hf : Smooth f) (i j : Fin 2) (x : Plane) :
    coordPartial (coordPartial f i) j x =
      coordPartial (coordPartial f j) i x := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).differentiable
      (by simp)
  have h (a b : Fin 2) : coordPartial (coordPartial f a) b x =
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single b 1) (EuclideanSpace.single a 1) := by
    unfold coordPartial
    rw [fderiv_clm_apply hdf.differentiableAt (differentiableAt_const _)]
    simp
  rw [h i j, h j i]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).eq _ _

lemma integral_coeff_mul_partial_square {a v : Plane → ℝ}
    (ha : Smooth a) (hv : Smooth v) (hc : HasCompactSupport v) (i : Fin 2) :
    2 * (∫ x, a x * v x * coordPartial v i x) =
      -(∫ x, coordPartial a i x * (v x * v x)) := by
  have h := integral_mul_partial ha (hv.mul hv) hc.mul_right i
  calc
    2 * (∫ x, a x * v x * coordPartial v i x) =
        ∫ x, a x * coordPartial (fun y => v y * v y) i x := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [partial_mul hv hv]
      ring
    _ = _ := h

lemma integrable_mul_compact_left {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport f) : Integrable (fun x => f x * g x) := by
  exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_right

lemma integral_partial_mul {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport f) (i : Fin 2) :
    (∫ x, coordPartial f i x * g x) = -(∫ x, f x * coordPartial g i x) := by
  simpa only [mul_comm] using integral_mul_partial hg hf hc i

lemma integral_partial_mul_mul {f g h : Plane → ℝ}
    (hf : Smooth f) (hg : Smooth g) (hh : Smooth h) (hc : HasCompactSupport f)
    (i : Fin 2) :
    (∫ x, coordPartial f i x * g x * h x) =
      -(∫ x, f x * coordPartial g i x * h x) -
        (∫ x, f x * g x * coordPartial h i x) := by
  have hI₁ := integrable_mul_compact_left (hf.mul (smooth_partial hg i)) hh
    hc.mul_right
  have hI₂ := integrable_mul_compact_left (hf.mul hg) (smooth_partial hh i) hc.mul_right
  calc
    (∫ x, coordPartial f i x * g x * h x) =
        ∫ x, coordPartial f i x * (g x * h x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = -(∫ x, f x * coordPartial (fun y => g y * h y) i x) :=
      integral_partial_mul hf (hg.mul hh) hc i
    _ = -(∫ x, (f x * coordPartial g i x * h x) +
        (f x * g x * coordPartial h i x)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      rw [partial_mul hg hh]
      ring
    _ = _ := by rw [integral_add hI₁ hI₂]; ring

lemma laplacian_transport_pair {T v : Plane → ℝ}
    (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) (i j : Fin 2) :
    -4 * (∫ x, coordPartial (coordPartial v i) i x *
        coordPartial T j x * coordPartial v j x) -
      2 * (∫ x, coordPartial (coordPartial v i) i x *
        coordPartial (coordPartial T j) j x * v x) =
      4 * (∫ x, coordPartial (coordPartial T j) i x *
        coordPartial v i x * coordPartial v j x) -
      (∫ x, coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x *
        (v x * v x)) := by
  have h1 := integral_partial_mul_mul (smooth_partial hv i) (smooth_partial hT j)
    (smooth_partial hv j) (compact_partial hc i) i
  have h2 := integral_partial_mul_mul (smooth_partial hv i)
    (smooth_partial (smooth_partial hT j) j) hv (compact_partial hc i) i
  have h3 := integral_coeff_mul_partial_square (smooth_partial hT j)
    (smooth_partial hv i) (compact_partial hc i) j
  have h4 := integral_coeff_mul_partial_square
    (smooth_partial (smooth_partial (smooth_partial hT j) j) i) hv hc i
  have hmix : coordPartial (coordPartial v j) i = coordPartial (coordPartial v i) j :=
    funext (partial_partial hv j i)
  rw [hmix] at h1
  simp only [mul_comm, mul_left_comm, mul_assoc] at h1 h2 h3 h4 ⊢
  linarith only [h1, h2, h3, h4]

lemma multiplication_transport_pair {a T v : Plane → ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v)
    (i : Fin 2) :
    -4 * (∫ x, a x * coordPartial T i x * v x * coordPartial v i x) -
      2 * (∫ x, a x * coordPartial (coordPartial T i) i x * (v x * v x)) =
      2 * (∫ x, coordPartial a i x * coordPartial T i x * (v x * v x)) := by
  have h := integral_coeff_mul_partial_square (ha.mul (smooth_partial hT i)) hv hc i
  have hI₁ := integrable_mul_compact_right
    ((smooth_partial ha i).mul (smooth_partial hT i)) (hv.mul hv) hc.mul_right
  have hI₂ := integrable_mul_compact_right
    (ha.mul (smooth_partial (smooth_partial hT i) i)) (hv.mul hv) hc.mul_right
  have hsplit : (∫ x, coordPartial (fun y => a y * coordPartial T i y) i x *
      (v x * v x)) =
      (∫ x, coordPartial a i x * coordPartial T i x * (v x * v x)) +
      (∫ x, a x * coordPartial (coordPartial T i) i x * (v x * v x)) := by
    rw [← integral_add hI₁ hI₂]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [partial_mul ha (smooth_partial hT i)]
    ring
  rw [hsplit] at h
  linarith only [h]

lemma smooth_skew {T v : Plane → ℝ} (hT : Smooth T) (hv : Smooth v) :
    Smooth (skewPart T v) := by
  apply ContDiff.sum
  intro i _
  exact ((contDiff_const.mul (smooth_partial hT i)).mul (smooth_partial hv i)).sub
    ((smooth_partial (smooth_partial hT i) i).mul hv)

lemma compact_skew {T v : Plane → ℝ} (hv : HasCompactSupport v) :
    HasCompactSupport (skewPart T v) := by
  convert (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ =>
      ((compact_partial hv i).mul_left (f := fun x => -2 * coordPartial T i x)).sub
        (hv.mul_left (f := coordPartial (coordPartial T i) i)))) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (funext x; simp [skewPart, Finset.sum_apply])

lemma integral_sum_mul {ι : Type*} (s : Finset ι) {f : ι → Plane → ℝ} {g : Plane → ℝ}
    (hf : ∀ i ∈ s, Smooth (f i)) (hg : Smooth g) (hc : HasCompactSupport g) :
    (∫ x, (∑ i ∈ s, f i x) * g x) = ∑ i ∈ s, ∫ x, f i x * g x := by
  simp_rw [Finset.sum_mul]
  exact integral_finsetSum s fun i hi => integrable_mul_compact_right (hf i hi) hg hc

lemma integral_mul_sum {ι : Type*} (s : Finset ι) {f : Plane → ℝ} {g : ι → Plane → ℝ}
    (hf : Smooth f) (hg : ∀ i ∈ s, Smooth (g i))
    (hc : ∀ i ∈ s, HasCompactSupport (g i)) :
    (∫ x, f x * (∑ i ∈ s, g i x)) = ∑ i ∈ s, ∫ x, f x * g i x := by
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum s fun i hi => integrable_mul_compact_right hf (hg i hi) (hc i hi)

lemma integral_skew_component {f T v : Plane → ℝ}
    (hf : Smooth f) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v)
    (i : Fin 2) :
    2 * (∫ x, f x * (-2 * coordPartial T i x * coordPartial v i x -
      coordPartial (coordPartial T i) i x * v x)) =
    -4 * (∫ x, f x * coordPartial T i x * coordPartial v i x) -
      2 * (∫ x, f x * coordPartial (coordPartial T i) i x * v x) := by
  have hI₁ := integrable_mul_compact_right (hf.mul (smooth_partial hT i))
    (smooth_partial hv i) (compact_partial hc i)
  have hI₂ := integrable_mul_compact_right
    (hf.mul (smooth_partial (smooth_partial hT i) i)) hv hc
  have hF : (∫ x, f x * (-2 * coordPartial T i x * coordPartial v i x -
      coordPartial (coordPartial T i) i x * v x)) =
      -2 * (∫ x, f x * coordPartial T i x * coordPartial v i x) -
      (∫ x, f x * coordPartial (coordPartial T i) i x * v x) := by
    calc
      _ = ∫ x, -2 * (f x * coordPartial T i x * coordPartial v i x) -
          f x * coordPartial (coordPartial T i) i x * v x := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := by rw [integral_sub (hI₁.const_mul (-2)) hI₂, integral_const_mul]
  rw [hF]
  ring

lemma integral_skew {f T v : Plane → ℝ}
    (hf : Smooth f) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) :
    2 * (∫ x, f x * skewPart T v x) =
      ∑ i : Fin 2, (-4 * (∫ x, f x * coordPartial T i x * coordPartial v i x) -
        2 * (∫ x, f x * coordPartial (coordPartial T i) i x * v x)) := by
  unfold skewPart
  rw [integral_mul_sum Finset.univ hf
    (fun i _ => ((contDiff_const.mul (smooth_partial hT i)).mul
      (smooth_partial hv i)).sub ((smooth_partial (smooth_partial hT i) i).mul hv))
    (fun i _ => ((compact_partial hc i).mul_left).sub hc.mul_left)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_skew_component hf hT hv hc i

lemma laplacian_transport {T v : Plane → ℝ}
    (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) :
    2 * (∫ x, euclideanLaplacian v x * skewPart T v x) =
      ∑ j : Fin 2, ∑ i : Fin 2,
        (4 * (∫ x, coordPartial (coordPartial T j) i x *
          coordPartial v i x * coordPartial v j x) -
        (∫ x, coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x *
          (v x * v x))) := by
  rw [integral_skew (smooth_laplacian hv) hT hv hc]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : (∫ x, euclideanLaplacian v x * coordPartial T j x * coordPartial v j x) =
      ∑ i : Fin 2, ∫ x, coordPartial (coordPartial v i) i x *
        coordPartial T j x * coordPartial v j x := by
    simp only [mul_assoc, euclideanLaplacian]
    exact integral_sum_mul Finset.univ
      (fun i _ => smooth_partial (smooth_partial hv i) i)
      ((smooth_partial hT j).mul (smooth_partial hv j)) (compact_partial hc j).mul_left
  have h2 : (∫ x, euclideanLaplacian v x * coordPartial (coordPartial T j) j x * v x) =
      ∑ i : Fin 2, ∫ x, coordPartial (coordPartial v i) i x *
        coordPartial (coordPartial T j) j x * v x := by
    simp only [mul_assoc, euclideanLaplacian]
    exact integral_sum_mul Finset.univ
      (fun i _ => smooth_partial (smooth_partial hv i) i)
      ((smooth_partial (smooth_partial hT j) j).mul hv) hc.mul_left
  rw [h1, h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact laplacian_transport_pair hT hv hc i j

lemma multiplication_transport {a T v : Plane → ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) :
    2 * (∫ x, (a x * v x) * skewPart T v x) =
      ∑ i : Fin 2, 2 * (∫ x, coordPartial a i x * coordPartial T i x * (v x * v x)) := by
  rw [integral_skew (ha.mul hv) hT hv hc]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    multiplication_transport_pair ha hT hv hc i

lemma transport_commutator {a T v : Plane → ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) :
    2 * (∫ x, (euclideanLaplacian v x + a x * v x) * skewPart T v x) =
      (∑ j : Fin 2, ∑ i : Fin 2,
        (4 * (∫ x, coordPartial (coordPartial T j) i x *
          coordPartial v i x * coordPartial v j x) -
        (∫ x, coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x *
          (v x * v x)))) +
      ∑ i : Fin 2, 2 * (∫ x, coordPartial a i x * coordPartial T i x * (v x * v x)) := by
  have hI₁ := integrable_mul_compact_right (smooth_laplacian hv) (smooth_skew hT hv)
    (compact_skew hc)
  have hI₂ := integrable_mul_compact_right (ha.mul hv) (smooth_skew hT hv)
    (compact_skew hc)
  simp_rw [add_mul]
  rw [integral_add hI₁ hI₂, mul_add, laplacian_transport hT hv hc,
    multiplication_transport ha hT hv hc]


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Commutator
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma partial_finset_sum {ι : Type*} (s : Finset ι) {f : ι → Plane → ℝ}
    (hf : ∀ i ∈ s, Smooth (f i)) (k : Fin 2) (x : Plane) :
    coordPartial (fun y => ∑ i ∈ s, f i y) k x = ∑ i ∈ s, coordPartial (f i) k x := by
  unfold coordPartial
  rw [fderiv_fun_sum (fun i hi => ((hf i hi).differentiable (by simp)).differentiableAt)]
  simp only [sum_apply]

lemma smooth_gradientSquared {T : Plane → ℝ} (hT : Smooth T) :
    Smooth (gradientSquared T) :=
  ContDiff.sum fun i _ => (smooth_partial hT i).mul (smooth_partial hT i)

lemma partial_gradientSquared {T : Plane → ℝ} (hT : Smooth T) (i : Fin 2) (x : Plane) :
    coordPartial (gradientSquared T) i x =
      ∑ j : Fin 2, 2 * coordPartial (coordPartial T j) i x * coordPartial T j x := by
  unfold gradientSquared
  rw [partial_finset_sum Finset.univ
    (fun j _ => (smooth_partial hT j).mul (smooth_partial hT j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [partial_mul (smooth_partial hT j) (smooth_partial hT j)]
  ring

lemma potential_transport_component {T p v : Plane → ℝ}
    (hT : Smooth T) (hp : Smooth p) (hv : Smooth v) (hc : HasCompactSupport v)
    (K : ℝ) (i : Fin 2) :
    2 * (∫ x, coordPartial (fun y => gradientSquared T y + K^2 * p y) i x *
      coordPartial T i x * (v x * v x)) =
      (∑ j : Fin 2, 4 * (∫ x, coordPartial (coordPartial T j) i x *
        coordPartial T j x * coordPartial T i x * (v x * v x))) +
      2 * K^2 * (∫ x, coordPartial p i x * coordPartial T i x * (v x * v x)) := by
  have hI₁ := integrable_mul_compact_right
    ((smooth_partial (smooth_gradientSquared hT) i).mul (smooth_partial hT i))
    (hv.mul hv) hc.mul_right
  have hI₂ := integrable_mul_compact_right
    ((smooth_partial hp i).mul (smooth_partial hT i)) (hv.mul hv) hc.mul_right
  have hsplit : (∫ x, coordPartial (fun y => gradientSquared T y + K^2 * p y) i x *
      coordPartial T i x * (v x * v x)) =
      (∫ x, coordPartial (gradientSquared T) i x * coordPartial T i x * (v x * v x)) +
      K^2 * (∫ x, coordPartial p i x * coordPartial T i x * (v x * v x)) := by
    calc
      _ = ∫ x, (coordPartial (gradientSquared T) i x * coordPartial T i x * (v x * v x)) +
          K^2 * (coordPartial p i x * coordPartial T i x * (v x * v x)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [partial_add (smooth_gradientSquared hT) (contDiff_const.mul hp),
          partial_const_mul hp]
        ring
      _ = _ := by rw [integral_add hI₁ (hI₂.const_mul (K^2)), integral_const_mul]
  rw [hsplit, mul_add]
  have hgrad : 2 * (∫ x, coordPartial (gradientSquared T) i x * coordPartial T i x *
      (v x * v x)) = ∑ j : Fin 2, 4 * (∫ x, coordPartial (coordPartial T j) i x *
        coordPartial T j x * coordPartial T i x * (v x * v x)) := by
    simp_rw [partial_gradientSquared hT, mul_assoc]
    rw [integral_sum_mul Finset.univ
      (fun j _ => contDiff_const.mul ((smooth_partial (smooth_partial hT j) i).mul
        (smooth_partial hT j)))
      ((smooth_partial hT i).mul (hv.mul hv)) hc.mul_right.mul_left,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    ring
  rw [hgrad]
  ring

theorem carleman_commutator {T p v : Plane → ℝ}
    (hT : Smooth T) (hp : Smooth p) (hv : Smooth v) (hc : HasCompactSupport v)
    (K : ℝ) :
    2 * (∫ x, (euclideanLaplacian v x + (gradientSquared T x + K^2 * p x) * v x) *
      skewPart T v x) =
      (∑ j : Fin 2, ∑ i : Fin 2,
        (4 * (∫ x, coordPartial (coordPartial T j) i x *
          coordPartial v i x * coordPartial v j x) -
        (∫ x, coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x *
          (v x * v x)))) +
      ∑ i : Fin 2,
        ((∑ j : Fin 2, 4 * (∫ x, coordPartial (coordPartial T j) i x *
          coordPartial T j x * coordPartial T i x * (v x * v x))) +
        2 * K^2 * (∫ x, coordPartial p i x * coordPartial T i x * (v x * v x))) := by
  rw [transport_commutator ((smooth_gradientSquared hT).add (contDiff_const.mul hp)) hT hv hc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact potential_transport_component hT hp hv hc K i

lemma partial_exp {T : Plane → ℝ} (hT : Smooth T) (i : Fin 2) (x : Plane) :
    coordPartial (fun y => Real.exp (T y)) i x = Real.exp (T x) * coordPartial T i x := by
  unfold coordPartial
  rw [fderiv_exp ((hT.differentiable (by simp)).differentiableAt)]
  rfl

lemma partial_exp_mul {T w : Plane → ℝ} (hT : Smooth T) (hw : Smooth w)
    (i : Fin 2) (x : Plane) :
    coordPartial (fun y => Real.exp (T y) * w y) i x =
      Real.exp (T x) * (coordPartial T i x * w x + coordPartial w i x) := by
  rw [partial_mul hT.exp hw, partial_exp hT]
  ring

lemma partial2_exp_mul {T w : Plane → ℝ} (hT : Smooth T) (hw : Smooth w)
    (i : Fin 2) (x : Plane) :
    coordPartial (coordPartial (fun y => Real.exp (T y) * w y) i) i x =
      Real.exp (T x) * (coordPartial (coordPartial w i) i x +
        2 * coordPartial T i x * coordPartial w i x +
        (coordPartial (coordPartial T i) i x + coordPartial T i x * coordPartial T i x) * w x) := by
  rw [show coordPartial (fun y => Real.exp (T y) * w y) i =
      (fun y => Real.exp (T y) * (coordPartial T i y * w y + coordPartial w i y)) from
    funext (partial_exp_mul hT hw i)]
  rw [partial_exp_mul hT (((smooth_partial hT i).mul hw).add (smooth_partial hw i)),
    partial_add ((smooth_partial hT i).mul hw) (smooth_partial hw i),
    partial_mul (smooth_partial hT i) hw]
  ring

lemma conjugation_component {T w : Plane → ℝ} (hT : Smooth T) (hw : Smooth w)
    (i : Fin 2) (x : Plane) :
    coordPartial (coordPartial (fun y => Real.exp (T y) * w y) i) i x +
      (coordPartial T i x * coordPartial T i x) * (Real.exp (T x) * w x) +
      (-2 * coordPartial T i x * coordPartial (fun y => Real.exp (T y) * w y) i x -
        coordPartial (coordPartial T i) i x * (Real.exp (T x) * w x)) =
      Real.exp (T x) * coordPartial (coordPartial w i) i x := by
  rw [partial2_exp_mul hT hw, partial_exp_mul hT hw]
  ring

lemma conjugation {T w : Plane → ℝ} (hT : Smooth T) (hw : Smooth w)
    (p : Plane → ℝ) (K : ℝ) (x : Plane) :
    euclideanLaplacian (fun y => Real.exp (T y) * w y) x +
      (gradientSquared T x + K^2 * p x) * (Real.exp (T x) * w x) +
      skewPart T (fun y => Real.exp (T y) * w y) x =
      Real.exp (T x) * (euclideanLaplacian w x + K^2 * p x * w x) := by
  have h := congrArg (fun f : Fin 2 → ℝ => ∑ i, f i)
    (funext (fun i => conjugation_component hT hw i x))
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at h
  unfold euclideanLaplacian gradientSquared skewPart
  linear_combination h

lemma integral_laplacian_mul {v : Plane → ℝ} (hv : Smooth v) (hc : HasCompactSupport v) :
    (∫ x, euclideanLaplacian v x * v x) =
      -(∑ i : Fin 2, ∫ x, coordPartial v i x * coordPartial v i x) := by
  unfold euclideanLaplacian
  rw [integral_sum_mul Finset.univ (fun i _ => smooth_partial (smooth_partial hv i) i) hv hc,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_partial_mul (smooth_partial hv i) hv (compact_partial hc i) i

lemma l2sq_nonneg (f : Plane → ℝ) : 0 ≤ l2sq f :=
  integral_nonneg fun x => mul_self_nonneg (f x)

lemma l2sq_add {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    l2sq (fun x => f x + g x) = l2sq f + l2sq g + 2 * (∫ x, f x * g x) := by
  have hI₁ := integrable_mul_compact_left hf hf hcf
  have hI₂ := integrable_mul_compact_left hg hg hcg
  have hI₃ := integrable_mul_compact_left hf hg hcf
  unfold l2sq
  calc
    _ = ∫ x, (f x * f x + g x * g x) + 2 * (f x * g x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := by
      rw [integral_add (f := fun x => f x * f x + g x * g x)
        (hI₁.add hI₂) (hI₃.const_mul 2), integral_add hI₁ hI₂, integral_const_mul]

lemma l2sq_const_mul (f : Plane → ℝ) (c : ℝ) :
    l2sq (fun x => c * f x) = c^2 * l2sq f := by
  unfold l2sq
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma pairing_sq_le {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    (∫ x, f x * g x)^2 ≤ l2sq f * l2sq g := by
  have hquad (t : ℝ) : 0 ≤ l2sq f * (t * t) + (2 * (∫ x, f x * g x)) * t + l2sq g := by
    have h := l2sq_nonneg (fun x => t * f x + g x)
    rw [l2sq_add (contDiff_const.mul hf) hg hcf.mul_left hcg, l2sq_const_mul] at h
    simp_rw [mul_assoc] at h
    rw [integral_const_mul] at h
    nlinarith only [h]
  have h := discrim_le_zero hquad
  unfold discrim at h
  nlinarith only [h]

lemma plane_trace_sum (a₀ a₁ A B C : ℝ) :
    (C * a₀^2 - 2 * B * a₀ * a₁ + A * a₁^2) +
      (A * a₀^2 + 2 * B * a₀ * a₁ + C * a₁^2) =
      (a₀^2 + a₁^2) * (A + C) := by
  ring

lemma l2sq_linearCombination_le {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (a b : ℝ) :
    l2sq (fun x => a * f x + b * g x) ≤ (a^2 + b^2) * (l2sq f + l2sq g) := by
  have hI₁ := integrable_mul_compact_left hf hf hcf
  have hI₂ := integrable_mul_compact_left hg hg hcg
  have hs : Smooth (fun x => a * f x + b * g x) :=
    (contDiff_const.mul hf).add (contDiff_const.mul hg)
  have hc : HasCompactSupport (fun x => a * f x + b * g x) := hcf.mul_left.add hcg.mul_left
  have hsum : (a^2 + b^2) * (l2sq f + l2sq g) =
      ∫ x, (a^2 + b^2) * (f x * f x + g x * g x) := by
    unfold l2sq
    rw [integral_const_mul, integral_add hI₁ hI₂]
  rw [hsum]
  apply integral_mono (integrable_mul_compact_left hs hs hc)
    ((hI₁.add hI₂).const_mul (a^2 + b^2))
  intro x
  change (a * f x + b * g x) * (a * f x + b * g x) ≤
    (a^2 + b^2) * (f x * f x + g x * g x)
  nlinarith only [sq_nonneg (a * g x - b * f x)]

lemma integral_quadratic {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (a b c : ℝ) :
    (∫ x, a * (f x * f x) + b * (f x * g x) + c * (g x * g x)) =
      a * l2sq f + b * (∫ x, f x * g x) + c * l2sq g := by
  have hI₁ := (integrable_mul_compact_left hf hf hcf).const_mul a
  have hI₂ := (integrable_mul_compact_left hf hg hcf).const_mul b
  have hI₃ := (integrable_mul_compact_left hg hg hcg).const_mul c
  rw [integral_add (f := fun x => a * (f x * f x) + b * (f x * g x))
    (hI₁.add hI₂) hI₃, integral_add hI₁ hI₂]
  simp only [integral_const_mul, l2sq]

lemma l2sq_linearCombination {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (a b : ℝ) :
    l2sq (fun x => a * f x + b * g x) =
      a^2 * l2sq f + (2 * a * b) * (∫ x, f x * g x) + b^2 * l2sq g := by
  calc
    _ = ∫ x, a^2 * (f x * f x) + (2 * a * b) * (f x * g x) + b^2 * (g x * g x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := integral_quadratic hf hg hcf hcg _ _ _

lemma pairing_linearCombination {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (a b c d : ℝ) :
    (∫ x, (a * f x + b * g x) * (c * f x + d * g x)) =
      (a * c) * l2sq f + (a * d + b * c) * (∫ x, f x * g x) + (b * d) * l2sq g := by
  calc
    _ = ∫ x, (a * c) * (f x * f x) + (a * d + b * c) * (f x * g x) +
        (b * d) * (g x * g x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := integral_quadratic hf hg hcf hcg _ _ _

lemma plane_trace_energy_identity {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (a₀ a₁ A B C : ℝ) :
    (a₀^2 + a₁^2) * quadraticEnergy A B C f g =
      (C * a₀^2 - 2 * B * a₀ * a₁ + A * a₁^2) * (l2sq f + l2sq g) +
      2 * (∫ x, ((A * a₀ + B * a₁) * f x + (B * a₀ + C * a₁) * g x) *
        (a₀ * f x + a₁ * g x)) -
      (A + C) * l2sq (fun x => a₀ * f x + a₁ * g x) := by
  rw [pairing_linearCombination hf hg hcf hcg, l2sq_linearCombination hf hg hcf hcg]
  unfold quadraticEnergy
  ring

open Filter in
lemma pairing_tendsto_zero_of_bound {f g : ℕ → Plane → ℝ} {r : ℕ → ℝ} {r₀ : ℝ}
    (hf : ∀ j, Smooth (f j)) (hg : ∀ j, Smooth (g j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcg : ∀ j, HasCompactSupport (g j))
    (hbound : ∀ j, l2sq (f j) ≤ r j)
    (hr : Tendsto r atTop (𝓝 r₀))
    (hz : Tendsto (fun j => l2sq (g j)) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, f j x * g j x) atTop (𝓝 0) := by
  have hsq : Tendsto (fun j => (∫ x, f j x * g j x)^2) atTop (𝓝 0) :=
    squeeze_zero (fun j => sq_nonneg _) (fun j =>
      (pairing_sq_le (hf j) (hg j) (hcf j) (hcg j)).trans
        (mul_le_mul_of_nonneg_right (hbound j) (l2sq_nonneg (g j))))
      (by simpa using hr.mul hz)
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hroot

open Filter in

lemma plane_trace_energy_limit {f g : ℕ → Plane → ℝ} (a₀ a₁ A B C : ℝ)
    (ha : a₀^2 + a₁^2 ≠ 0)
    (hf : ∀ j, Smooth (f j)) (hg : ∀ j, Smooth (g j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcg : ∀ j, HasCompactSupport (g j))
    (he : Tendsto (fun j => l2sq (f j) + l2sq (g j)) atTop (𝓝 (a₀^2 + a₁^2)))
    (hp : Tendsto (fun j => l2sq (fun x => a₀ * f j x + a₁ * g j x)) atTop (𝓝 0)) :
    Tendsto (fun j => quadraticEnergy A B C (f j) (g j) +
      (A * a₀^2 + 2 * B * a₀ * a₁ + C * a₁^2)) atTop
      (𝓝 ((a₀^2 + a₁^2) * (A + C))) := by
  let c₀ := A * a₀ + B * a₁
  let c₁ := B * a₀ + C * a₁
  have hpair : Tendsto (fun j => ∫ x, (c₀ * f j x + c₁ * g j x) *
      (a₀ * f j x + a₁ * g j x)) atTop (𝓝 0) := by
    apply pairing_tendsto_zero_of_bound
      (fun j => (contDiff_const.mul (hf j)).add (contDiff_const.mul (hg j)))
      (fun j => (contDiff_const.mul (hf j)).add (contDiff_const.mul (hg j)))
      (fun j => (hcf j).mul_left.add (hcg j).mul_left)
      (fun j => (hcf j).mul_left.add (hcg j).mul_left)
      (fun j => l2sq_linearCombination_le (hf j) (hg j) (hcf j) (hcg j) c₀ c₁)
      (he.const_mul (c₀^2 + c₁^2)) hp
  let J := C * a₀^2 - 2 * B * a₀ * a₁ + A * a₁^2
  have hid (j : ℕ) : (a₀^2 + a₁^2) * quadraticEnergy A B C (f j) (g j) =
      J * (l2sq (f j) + l2sq (g j)) +
      2 * (∫ x, (c₀ * f j x + c₁ * g j x) * (a₀ * f j x + a₁ * g j x)) -
      (A + C) * l2sq (fun x => a₀ * f j x + a₁ * g j x) :=
    plane_trace_energy_identity (hf j) (hg j) (hcf j) (hcg j) a₀ a₁ A B C
  have hl := (((he.const_mul J).add (hpair.const_mul 2)).sub (hp.const_mul (A + C)))
  have hq : Tendsto (fun j => quadraticEnergy A B C (f j) (g j)) atTop (𝓝 J) := by
    have hd := hl.div_const (a₀^2 + a₁^2)
    convert hd using 1
    · ext j
      rw [← hid j, mul_div_cancel_left₀ _ ha]
    · simp only [mul_zero, add_zero, sub_zero, mul_div_cancel_right₀ _ ha]
  have ht := hq.add_const (A * a₀^2 + 2 * B * a₀ * a₁ + C * a₁^2)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  exact (plane_trace_sum a₀ a₁ A B C).symm


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Energy
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma l2sq_pos {f : Plane → ℝ} (hf : Smooth f) (hc : HasCompactSupport f) (hn : f ≠ 0) :
    0 < l2sq f := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hn
  apply integral_pos_of_integrable_nonneg_nonzero
    (hf.continuous.mul hf.continuous) (integrable_mul_compact_left hf hf hc)
    (fun x => mul_self_nonneg (f x))
  exact mul_ne_zero hx hx

lemma l2norm_nonneg (f : Plane → ℝ) : 0 ≤ l2norm f := Real.sqrt_nonneg _

lemma l2norm_sq (f : Plane → ℝ) : (l2norm f)^2 = l2sq f :=
  Real.sq_sqrt (l2sq_nonneg f)

lemma normalize_l2sq {f : Plane → ℝ} (hf : Smooth f) (hc : HasCompactSupport f) (hn : f ≠ 0) :
    l2sq (fun x => (l2norm f)⁻¹ * f x) = 1 := by
  have hs : l2norm f ≠ 0 := (Real.sqrt_pos.mpr (l2sq_pos hf hc hn)).ne'
  rw [l2sq_const_mul, ← l2norm_sq f]
  field_simp

lemma partial_tsupport_subset (f : Plane → ℝ) (i : Fin 2) :
    tsupport (coordPartial f i) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)

lemma abs_mul_mul_le {c C : ℝ} (hC : 0 ≤ C) (hc : |c| ≤ C) (x y : ℝ) :
    |c * x * y| ≤ C / 2 * (x * x + y * y) := by
  have hxy : 2 * |x| * |y| ≤ x * x + y * y := by
    have h := two_mul_le_add_sq |x| |y|
    rw [sq_abs, sq_abs, pow_two, pow_two] at h
    exact h
  calc
    |c * x * y| = |c| * (|x| * |y|) := by rw [abs_mul, abs_mul]; ring
    _ ≤ C * (|x| * |y|) := mul_le_mul_of_nonneg_right hc (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hxy hC]

lemma integral_coefficient_mul_abs_le {a f g : Plane → ℝ} {C : ℝ}
    (ha : Smooth a) (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g)
    (hC : 0 ≤ C) (hb : ∀ x ∈ tsupport f, |a x| ≤ C) :
    |∫ x, a x * f x * g x| ≤ C / 2 * (l2sq f + l2sq g) := by
  have hI : Integrable (fun x => a x * f x * g x) :=
    integrable_mul_compact_left (ha.mul hf) hg hcf.mul_left
  have hIf := integrable_mul_compact_left hf hf hcf
  have hIg := integrable_mul_compact_left hg hg hcg
  have hbound (x : Plane) : |a x * f x * g x| ≤ C / 2 * (f x * f x + g x * g x) := by
    by_cases hx : f x = 0
    · simp only [hx, mul_zero, zero_mul, abs_zero, zero_add]
      exact mul_nonneg (div_nonneg hC (by norm_num)) (mul_self_nonneg _)
    · exact abs_mul_mul_le hC (hb x (subset_closure hx)) _ _
  calc
    _ ≤ ∫ x, |a x * f x * g x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, C / 2 * (f x * f x + g x * g x) :=
      integral_mono hI.abs (by exact (hIf.add hIg).const_mul (C / 2)) hbound
    _ = _ := by rw [integral_const_mul, integral_add hIf hIg]; rfl

lemma integral_coefficient_square_abs_le {a f : Plane → ℝ} {C : ℝ}
    (ha : Smooth a) (hf : Smooth f) (hc : HasCompactSupport f)
    (hC : 0 ≤ C) (hb : ∀ x ∈ tsupport f, |a x| ≤ C) :
    |∫ x, a x * (f x * f x)| ≤ C * l2sq f := by
  have h := integral_coefficient_mul_abs_le ha hf hf hc hc hC hb
  simp only [mul_assoc] at h
  linarith only [h]

lemma smooth_plus {a v : Plane → ℝ} (ha : Smooth a) (hv : Smooth v) :
    Smooth (plusPart a v) := (smooth_laplacian hv).add (ha.mul hv)

lemma compact_plus {a v : Plane → ℝ} (hc : HasCompactSupport v) :
    HasCompactSupport (plusPart a v) := (compact_laplacian hc).add hc.mul_left

lemma gradientEnergy_nonneg (v : Plane → ℝ) : 0 ≤ gradientEnergy v :=
  Finset.sum_nonneg fun _ _ => l2sq_nonneg _

lemma plus_energy_identity {a v : Plane → ℝ} (ha : Smooth a)
    (hv : Smooth v) (hc : HasCompactSupport v) :
    (∫ x, plusPart a v x * v x) = -gradientEnergy v + (∫ x, a x * (v x * v x)) := by
  unfold plusPart
  simp_rw [add_mul]
  rw [integral_add (integrable_mul_compact_right (smooth_laplacian hv) hv hc)
    (integrable_mul_compact_right (ha.mul hv) hv hc), integral_laplacian_mul hv hc]
  simp only [gradientEnergy, l2sq, mul_assoc]

lemma pairing_abs_le_l2norm {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    |∫ x, f x * g x| ≤ l2norm f * l2norm g := by
  have h := pairing_sq_le hf hg hcf hcg
  have h₁ := l2norm_sq f
  have h₂ := l2norm_sq g
  have h₀ := mul_nonneg (l2norm_nonneg f) (l2norm_nonneg g)
  nlinarith only [h, h₁, h₂, sq_abs (∫ x, f x * g x), abs_nonneg (∫ x, f x * g x), h₀]

lemma l2norm_eq_one {f : Plane → ℝ} (h : l2sq f = 1) : l2norm f = 1 := by
  simp only [l2norm, h, Real.sqrt_one]

lemma plus_energy_bound {a v : Plane → ℝ} {C : ℝ} (ha : Smooth a)
    (hv : Smooth v) (hc : HasCompactSupport v) (hv1 : l2sq v = 1)
    (hC : 0 ≤ C) (haC : ∀ x ∈ tsupport v, |a x| ≤ C) :
    gradientEnergy v ≤ C + l2norm (plusPart a v) := by
  have hid := plus_energy_identity ha hv hc
  have hb := pairing_abs_le_l2norm (smooth_plus ha hv) hv (compact_plus hc) hc
  rw [l2norm_eq_one hv1, mul_one] at hb
  have haI := integral_coefficient_square_abs_le ha hv hc hC haC
  rw [hv1, mul_one] at haI
  linarith only [hid, (neg_le_abs (∫ x, plusPart a v x * v x)).trans hb,
    (le_abs_self (∫ x, a x * (v x * v x))).trans haI]

lemma commutator_le_sum_square {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    2 * (∫ x, f x * g x) ≤ l2sq (fun x => f x + g x) := by
  rw [l2sq_add hf hg hcf hcg]
  linarith only [l2sq_nonneg f, l2sq_nonneg g]

lemma carleman_scalar_bootstrap {X Y E S D t c : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (_hE : 0 ≤ E)
    (hS : 1 ≤ S) (hD : S ≤ D) (ht : 0 ≤ t) (htsq : t^2 = S * D^2)
    (hc : 1 ≤ c)
    (hpair : X^2 + Y^2 ≤ c * S * (E + D^2))
    (henergy : E ≤ c * D^2 + X) :
    X ≤ (2*c + 2) * t ∧ Y ≤ (2*c + 2) * t ∧ E ≤ (3*c + 2) * D^2 := by
  have hD0 : 0 ≤ D := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hSD : S ≤ D^2 := by nlinarith only [hS, hD]
  have hSt : S ≤ t := by
    nlinarith only [ht, hS, htsq, mul_le_mul_of_nonneg_left hSD hS0]
  have htD : t ≤ D^2 := by
    have h := mul_le_mul_of_nonneg_right hSD (sq_nonneg D)
    nlinarith only [ht, htsq, h, sq_nonneg D]
  have hbase : X^2 + Y^2 ≤ c * S * X + c * (c+1) * t^2 := by
    calc
      _ ≤ c * S * (E + D^2) := hpair
      _ ≤ c * S * (c * D^2 + X + D^2) :=
        mul_le_mul_of_nonneg_left (add_le_add henergy le_rfl) (mul_nonneg hc0 hS0)
      _ = _ := by rw [htsq]; ring
  have hSX : c * S * X ≤ c * t * X := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSt hc0) hX
  have hA0 : 0 ≤ (2*c+2)*t := mul_nonneg (by linarith) ht
  have hct2 := mul_nonneg (sq_nonneg c) (sq_nonneg t)
  have hct1 := mul_nonneg hc0 (sq_nonneg t)
  have ht2 := sq_nonneg t
  have hsum : X^2 + 2*Y^2 ≤ (3*c^2+2*c)*t^2 := by
    nlinarith only [hbase, hSX, sq_nonneg (X-c*t)]
  have hXb : X ≤ (2*c+2) * t := by
    apply (sq_le_sq₀ hX hA0).mp
    nlinarith only [hsum, sq_nonneg Y, hct2, hct1, ht2]
  have hYb : Y ≤ (2*c+2) * t := by
    apply (sq_le_sq₀ hY hA0).mp
    nlinarith only [hsum, sq_nonneg X, hct2, hct1, ht2]
  refine ⟨hXb, hYb, ?_⟩
  have hxD := hXb.trans (mul_le_mul_of_nonneg_left htD (by linarith))
  linarith only [henergy, hxD]

lemma transport_commutator_energy {a T v : Plane → ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) :
    2 * (∫ x, plusPart a v x * skewPart T v x) =
      4 * hessianEnergy T v - bilaplacianEnergy T v + 2 * potentialTransport a T v := by
  rw [show plusPart a v = (fun x => euclideanLaplacian v x + a x * v x) from rfl,
    transport_commutator ha hT hv hc]
  simp only [hessianEnergy, bilaplacianEnergy, potentialTransport,
    Finset.sum_sub_distrib, Finset.mul_sum]

lemma hessianEnergy_abs_le {T v : Plane → ℝ} {C : ℝ}
    (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) (hC : 0 ≤ C)
    (hb : ∀ i j x, x ∈ tsupport v → |coordPartial (coordPartial T j) i x| ≤ C) :
    |hessianEnergy T v| ≤ 2 * C * gradientEnergy v := by
  have hi (i j : Fin 2) :
      |∫ x, coordPartial (coordPartial T j) i x * coordPartial v i x * coordPartial v j x| ≤
        C / 2 * (l2sq (coordPartial v i) + l2sq (coordPartial v j)) :=
    integral_coefficient_mul_abs_le (smooth_partial (smooth_partial hT j) i)
      (smooth_partial hv i) (smooth_partial hv j) (compact_partial hc i) (compact_partial hc j)
      hC (fun x hx => hb i j x (partial_tsupport_subset v i hx))
  calc
    _ ≤ ∑ j : Fin 2, ∑ i : Fin 2,
        |∫ x, coordPartial (coordPartial T j) i x * coordPartial v i x * coordPartial v j x| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j : Fin 2, ∑ i : Fin 2,
        C / 2 * (l2sq (coordPartial v i) + l2sq (coordPartial v j)) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hi i j
    _ = _ := by simp only [gradientEnergy, Fin.sum_univ_two]; ring

lemma bilaplacianEnergy_abs_le {T v : Plane → ℝ} {C : ℝ}
    (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) (hC : 0 ≤ C)
    (hb : ∀ i j x, x ∈ tsupport v →
      |coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x| ≤ C) :
    |bilaplacianEnergy T v| ≤ 4 * C * l2sq v := by
  have hi (i j : Fin 2) := integral_coefficient_square_abs_le
    (smooth_partial (smooth_partial (smooth_partial (smooth_partial hT j) j) i) i)
    hv hc hC (hb i j)
  calc
    _ ≤ ∑ j : Fin 2, ∑ i : Fin 2,
        |∫ x, coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x * (v x * v x)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j : Fin 2, ∑ i : Fin 2, C * l2sq v :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hi i j
    _ = _ := by simp only [Fin.sum_univ_two]; ring

lemma potentialTransport_abs_le {a T v : Plane → ℝ} {C : ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) (hC : 0 ≤ C)
    (hb : ∀ i x, x ∈ tsupport v → |coordPartial a i x * coordPartial T i x| ≤ C) :
    |potentialTransport a T v| ≤ 2 * C * l2sq v := by
  have hi (i : Fin 2) := integral_coefficient_square_abs_le
    ((smooth_partial ha i).mul (smooth_partial hT i)) hv hc hC (hb i)
  calc
    _ ≤ ∑ i : Fin 2, |∫ x, coordPartial a i x * coordPartial T i x * (v x * v x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 2, C * l2sq v := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp only [Fin.sum_univ_two]; ring

lemma transport_commutator_abs_le {a T v : Plane → ℝ} {c S D : ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v)
    (hc0 : 0 ≤ c) (hS : 0 ≤ S) (hv1 : l2sq v = 1)
    (hH : ∀ i j x, x ∈ tsupport v → |coordPartial (coordPartial T j) i x| ≤ c*S)
    (hB : ∀ i j x, x ∈ tsupport v →
      |coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x| ≤ c*S*D^2)
    (hA : ∀ i x, x ∈ tsupport v → |coordPartial a i x * coordPartial T i x| ≤ c*S*D^2) :
    |2 * (∫ x, plusPart a v x * skewPart T v x)| ≤
      8*c*S*(gradientEnergy v + D^2) := by
  rw [transport_commutator_energy ha hT hv hc]
  have hH' := hessianEnergy_abs_le hT hv hc (mul_nonneg hc0 hS) hH
  have hB' := bilaplacianEnergy_abs_le hT hv hc
    (mul_nonneg (mul_nonneg hc0 hS) (sq_nonneg D)) hB
  have hA' := potentialTransport_abs_le ha hT hv hc
    (mul_nonneg (mul_nonneg hc0 hS) (sq_nonneg D)) hA
  rw [hv1, mul_one] at hB' hA'
  calc
    _ ≤ |4 * hessianEnergy T v - bilaplacianEnergy T v| + |2 * potentialTransport a T v| :=
      abs_add_le _ _
    _ ≤ |4 * hessianEnergy T v| + |bilaplacianEnergy T v| + |2 * potentialTransport a T v| :=
      add_le_add (abs_sub _ _) le_rfl
    _ = 4*|hessianEnergy T v| + |bilaplacianEnergy T v| + 2*|potentialTransport a T v| := by
      rw [abs_mul, abs_mul]; norm_num
    _ ≤ _ := by linarith only [hH', hB', hA']

lemma operator_bootstrap {a T v : Plane → ℝ} {c S D : ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hcv : HasCompactSupport v)
    (hc : 1 ≤ c) (hS : 1 ≤ S) (hD : S ≤ D) (hv1 : l2sq v = 1)
    (hP : ∀ x ∈ tsupport v, |a x| ≤ c*D^2)
    (hH : ∀ i j x, x ∈ tsupport v → |coordPartial (coordPartial T j) i x| ≤ c*S)
    (hB : ∀ i j x, x ∈ tsupport v →
      |coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x| ≤ c*S*D^2)
    (hA : ∀ i x, x ∈ tsupport v → |coordPartial a i x * coordPartial T i x| ≤ c*S*D^2)
    (hsmall : l2sq (fun x => plusPart a v x + skewPart T v x) ≤ S*D^2) :
    l2norm (plusPart a v) ≤ (16*c+4) * (Real.sqrt S * D) ∧
    l2norm (skewPart T v) ≤ (16*c+4) * (Real.sqrt S * D) ∧
    gradientEnergy v ≤ (24*c+5)*D^2 := by
  have hc0 : 0 ≤ c := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hcomm := transport_commutator_abs_le ha hT hv hcv hc0 hS0 hv1 hH hB hA
  have hdecomp := l2sq_add (smooth_plus ha hv) (smooth_skew hT hv) (compact_plus hcv)
    (compact_skew hcv)
  have hpair : (l2norm (plusPart a v))^2 + (l2norm (skewPart T v))^2 ≤
      (8*c+1)*S*(gradientEnergy v+D^2) := by
    rw [l2norm_sq, l2norm_sq]
    have hlow := (neg_le_abs (2*(∫ x, plusPart a v x * skewPart T v x))).trans hcomm
    have hpos := mul_nonneg hS0 (gradientEnergy_nonneg v)
    nlinarith only [hsmall, hdecomp, hlow, hpos]
  have henergy : gradientEnergy v ≤ (8*c+1)*D^2 + l2norm (plusPart a v) := by
    have h := plus_energy_bound ha hv hcv hv1 (mul_nonneg hc0 (sq_nonneg D)) hP
    have h' := mul_nonneg (show 0 ≤ 7*c+1 by linarith) (sq_nonneg D)
    linarith only [h, h']
  have hb := carleman_scalar_bootstrap (l2norm_nonneg _) (l2norm_nonneg _)
    (gradientEnergy_nonneg v) hS hD (mul_nonneg (Real.sqrt_nonneg S) hD0)
    (by rw [mul_pow, Real.sq_sqrt hS0]) (show 1 ≤ 8*c+1 by linarith) hpair henergy
  simpa only [show 2*(8*c+1)+2 = 16*c+4 by ring,
    show 3*(8*c+1)+2 = 24*c+5 by ring] using hb


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Normalization
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

open Filter in
lemma sqrt_div_tendsto_zero {S D : ℕ → ℝ}
    (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j) (hSinf : Tendsto S atTop atTop) :
    Tendsto (fun j => Real.sqrt (S j) / D j) atTop (𝓝 0) := by
  have hbound (j : ℕ) : Real.sqrt (S j) / D j ≤ (Real.sqrt (S j))⁻¹ := by
    have hs : 0 < S j := by linarith only [hS j]
    have hd : 0 < D j := hs.trans_le (hD j)
    have hr : 0 < Real.sqrt (S j) := Real.sqrt_pos.mpr hs
    rw [div_le_iff₀ hd, ← div_eq_inv_mul, le_div_iff₀ hr]
    nlinarith only [Real.sq_sqrt hs.le, hD j]
  apply squeeze_zero (fun j => div_nonneg (Real.sqrt_nonneg _) (by linarith only [hS j, hD j])) hbound
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hSinf)

open Filter in
lemma pairing_div_square_tendsto_zero {f v : ℕ → Plane → ℝ} {S D : ℕ → ℝ} {C : ℝ}
    (hf : ∀ j, Smooth (f j)) (hv : ∀ j, Smooth (v j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcv : ∀ j, HasCompactSupport (v j))
    (hv1 : ∀ j, l2sq (v j) = 1)
    (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j) (hSinf : Tendsto S atTop atTop)
    (hbound : ∀ j, l2norm (f j) ≤ C * (Real.sqrt (S j) * D j)) :
    Tendsto (fun j => (∫ x, f j x * v j x) / (D j)^2) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hlim : Tendsto (fun j => C * (Real.sqrt (S j) / D j)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (sqrt_div_tendsto_zero hS hD hSinf).const_mul C
  apply squeeze_zero (fun j => abs_nonneg _) (fun j => ?_) hlim
  have hDpos : 0 < D j := by linarith only [hS j, hD j]
  have hp := pairing_abs_le_l2norm (hf j) (hv j) (hcf j) (hcv j)
  rw [l2norm_eq_one (hv1 j), mul_one] at hp
  rw [abs_div, abs_of_nonneg (sq_nonneg (D j))]
  calc
    _ ≤ (C*(Real.sqrt (S j)*D j))/(D j)^2 := div_le_div_of_nonneg_right (hp.trans (hbound j)) (sq_nonneg _)
    _ = _ := by field_simp [hDpos.ne']

lemma l2sq_div (f : Plane → ℝ) (D : ℝ) :
    l2sq (fun x => f x / D) = l2sq f / D^2 := by
  simp only [div_eq_mul_inv, mul_comm (f _) D⁻¹]
  rw [l2sq_const_mul]
  ring

lemma smooth_normalizedPartial {v : Plane → ℝ} (hv : Smooth v) (D : ℝ) (i : Fin 2) :
    Smooth (normalizedPartial v D i) := (smooth_partial hv i).div_const D

lemma compact_normalizedPartial {v : Plane → ℝ} (hv : HasCompactSupport v) (D : ℝ) (i : Fin 2) :
    HasCompactSupport (normalizedPartial v D i) := by
  change HasCompactSupport (fun x => coordPartial v i x * D⁻¹)
  exact (compact_partial hv i).mul_right

lemma normalizedPartial_energy (v : Plane → ℝ) (D : ℝ) :
    l2sq (normalizedPartial v D 0) + l2sq (normalizedPartial v D 1) = gradientEnergy v / D^2 := by
  change l2sq (fun x => coordPartial v 0 x / D) + l2sq (fun x => coordPartial v 1 x / D) = _
  simp only [l2sq_div, gradientEnergy, Fin.sum_univ_two, add_div]

lemma normalized_coefficient_integral (a v : Plane → ℝ) (D : ℝ) :
    (∫ x, (a x / D^2) * (v x * v x)) = (∫ x, a x * (v x * v x)) / D^2 := by
  calc
    _ = ∫ x, (a x * (v x * v x)) / D^2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := integral_div _ _

lemma normalizedPartial_tsupport_subset (v : Plane → ℝ) (D : ℝ) (i : Fin 2) :
    tsupport (normalizedPartial v D i) ⊆ tsupport v := by
  change tsupport (fun x => coordPartial v i x * D⁻¹) ⊆ tsupport v
  exact tsupport_mul_subset_left.trans (partial_tsupport_subset v i)

lemma l2sq_add_le {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    l2sq (fun x => f x + g x) ≤ 2*(l2sq f + l2sq g) := by
  convert l2sq_linearCombination_le hf hg hcf hcg 1 1 using 1 <;> norm_num

lemma l2sq_coefficient_mul_le {a f : Plane → ℝ} {C : ℝ}
    (ha : Smooth a) (hf : Smooth f) (hc : HasCompactSupport f)
    (hC : 0 ≤ C) (hb : ∀ x ∈ tsupport f, |a x| ≤ C) :
    l2sq (fun x => a x * f x) ≤ C ^ 2 * l2sq f := by
  have hIf := integrable_mul_compact_left hf hf hc
  have hI : Integrable (fun x => (a x * f x) * (a x * f x)) :=
    integrable_mul_compact_left (ha.mul hf) (ha.mul hf) hc.mul_left
  calc
    _ ≤ ∫ x, C ^ 2 * (f x * f x) := by
      apply integral_mono hI (hIf.const_mul (C ^ 2))
      intro x
      by_cases hx : f x = 0
      · simp only [hx, mul_zero, le_refl]
      · have haC := (sq_le_sq₀ (abs_nonneg (a x)) hC).mpr (hb x (subset_closure hx))
        rw [sq_abs] at haC
        have h := mul_le_mul_of_nonneg_right haC (mul_self_nonneg (f x))
        nlinarith only [h]
    _ = _ := integral_const_mul _ _

open Filter in
lemma l2sq_add_tendsto_zero {f g : ℕ → Plane → ℝ}
    (hf : ∀ j, Smooth (f j)) (hg : ∀ j, Smooth (g j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcg : ∀ j, HasCompactSupport (g j))
    (hf0 : Tendsto (fun j => l2sq (f j)) atTop (𝓝 0))
    (hg0 : Tendsto (fun j => l2sq (g j)) atTop (𝓝 0)) :
    Tendsto (fun j => l2sq (fun x => f j x + g j x)) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => l2sq_nonneg _) (fun j => l2sq_add_le (hf j) (hg j) (hcf j) (hcg j))
  simpa only [add_zero, mul_zero] using (hf0.add hg0).const_mul 2

open Filter in
lemma l2sq_coefficient_mul_tendsto_zero {a f : ℕ → Plane → ℝ} {e r : ℕ → ℝ} {L : ℝ}
    (ha : ∀ j, Smooth (a j)) (hf : ∀ j, Smooth (f j))
    (hcf : ∀ j, HasCompactSupport (f j))
    (he : ∀ j, 0 ≤ e j) (hb : ∀ j x, x ∈ tsupport (f j) → |a j x| ≤ e j)
    (he0 : Tendsto e atTop (𝓝 0))
    (hbound : ∀ j, l2sq (f j) ≤ r j) (hr : Tendsto r atTop (𝓝 L)) :
    Tendsto (fun j => l2sq (fun x => a j x * f j x)) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => l2sq_nonneg _) (fun j =>
    (l2sq_coefficient_mul_le (ha j) (hf j) (hcf j) (he j) (hb j)).trans
      (mul_le_mul_of_nonneg_left (hbound j) (sq_nonneg _)))
  simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_mul] using (he0.pow 2).mul hr

open Filter in
lemma scaled_operator_square_limit {f : ℕ → Plane → ℝ} {S D : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j)
    (hSinf : Tendsto S atTop atTop)
    (hbound : ∀ j, l2norm (f j) ≤ C * (Real.sqrt (S j) * D j)) :
    Tendsto (fun j => l2sq (fun x => f j x / (D j)^2)) atTop (𝓝 0) := by
  have he0 : Tendsto (fun j => (C * (Real.sqrt (S j) / D j))^2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      ((sqrt_div_tendsto_zero hS hD hSinf).const_mul C).pow 2
  apply squeeze_zero (fun j => l2sq_nonneg _) (fun j => ?_) he0
  have hd : 0 < D j := by linarith only [hS j, hD j]
  have h : l2norm (f j) / (D j)^2 ≤ C * (Real.sqrt (S j) / D j) := by
    calc
      _ ≤ (C * (Real.sqrt (S j) * D j)) / (D j)^2 :=
        div_le_div_of_nonneg_right (hbound j) (sq_nonneg _)
      _ = _ := by field_simp [hd.ne']
  have hsq := (sq_le_sq₀ (div_nonneg (l2norm_nonneg _) (sq_nonneg _))
    (mul_nonneg hC (div_nonneg (Real.sqrt_nonneg _) hd.le))).mpr h
  rw [l2sq_div, ← l2norm_sq]
  simpa only [div_pow] using hsq

lemma smooth_normalizedTransport {T v : Plane → ℝ} (hT : Smooth T) (hv : Smooth v) (D : ℝ) :
    Smooth (normalizedTransport T v D) :=
  (((smooth_partial hT 0).div_const D).mul (smooth_normalizedPartial hv D 0)).add
    (((smooth_partial hT 1).div_const D).mul (smooth_normalizedPartial hv D 1))

lemma compact_normalizedTransport {T v : Plane → ℝ} (hc : HasCompactSupport v) (D : ℝ) :
    HasCompactSupport (normalizedTransport T v D) :=
  (compact_normalizedPartial hc D 0).mul_left.add (compact_normalizedPartial hc D 1).mul_left

lemma normalized_transport_identity (T v : Plane → ℝ) (D : ℝ) (x : Plane) :
    normalizedTransport T v D x = (-1/2 : ℝ) *
      (skewPart T v x / D^2 + (euclideanLaplacian T x / D^2) * v x) := by
  simp only [normalizedTransport, normalizedPartial, skewPart, euclideanLaplacian,
    Fin.sum_univ_two, div_eq_mul_inv]
  ring

lemma normalized_laplacian_abs_le {T v : Plane → ℝ} {c S D : ℝ} (hS : 0 ≤ S)
    (hH : ∀ i j x, x ∈ tsupport v → |coordPartial (coordPartial T j) i x| ≤ c*S)
    (x : Plane) (hx : x ∈ tsupport v) :
    |euclideanLaplacian T x / D^2| ≤ 2*c*(Real.sqrt S / D)^2 := by
  have hsum : |euclideanLaplacian T x| ≤ 2*c*S := by
    calc
      _ ≤ |coordPartial (coordPartial T 0) 0 x| + |coordPartial (coordPartial T 1) 1 x| := by
        simpa only [euclideanLaplacian, Fin.sum_univ_two] using
          abs_add_le (coordPartial (coordPartial T 0) 0 x) (coordPartial (coordPartial T 1) 1 x)
      _ ≤ _ := by linarith only [hH 0 0 x hx, hH 1 1 x hx]
  rw [abs_div, abs_of_nonneg (sq_nonneg D)]
  calc
    _ ≤ (2*c*S)/D^2 := div_le_div_of_nonneg_right hsum (sq_nonneg D)
    _ = _ := by rw [div_pow, Real.sq_sqrt hS]; ring

open Filter in
lemma normalized_transport_square_limit {T v : ℕ → Plane → ℝ} {S D : ℕ → ℝ} {c C : ℝ}
    (hT : ∀ j, Smooth (T j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j) = 1)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j)
    (hSinf : Tendsto S atTop atTop)
    (hY : ∀ j, l2norm (skewPart (T j) (v j)) ≤ C*(Real.sqrt (S j)*D j))
    (hH : ∀ j i k x, x ∈ tsupport (v j) →
      |coordPartial (coordPartial (T j) k) i x| ≤ c*S j) :
    Tendsto (fun j => l2sq (normalizedTransport (T j) (v j) (D j))) atTop (𝓝 0) := by
  have hskew := scaled_operator_square_limit hC hS hD hSinf hY
  have hlap : Tendsto (fun j => l2sq (fun x =>
      (euclideanLaplacian (T j) x / (D j)^2) * v j x)) atTop (𝓝 0) := by
    apply l2sq_coefficient_mul_tendsto_zero
      (fun j => (smooth_laplacian (hT j)).div_const _) hv hcv
      (e := fun j => 2*c*(Real.sqrt (S j)/D j)^2) (r := fun _ => 1)
    · intro j
      positivity
    · intro j x hx
      exact normalized_laplacian_abs_le (by linarith only [hS j]) (hH j) x hx
    · simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
        ((sqrt_div_tendsto_zero hS hD hSinf).pow 2).const_mul (2*c)
    · intro j
      exact (hv1 j).le
    · exact tendsto_const_nhds
  have hadd := l2sq_add_tendsto_zero
    (fun j => (smooth_skew (hT j) (hv j)).div_const _)
    (fun j => ((smooth_laplacian (hT j)).div_const _).mul (hv j))
    (fun j => by
      change HasCompactSupport (fun x => skewPart (T j) (v j) x * ((D j)^2)⁻¹)
      exact (compact_skew (hcv j)).mul_right)
    (fun j => (hcv j).mul_left) hskew hlap
  have hconst := hadd.const_mul ((-1/2 : ℝ)^2)
  have hid (j : ℕ) : l2sq (normalizedTransport (T j) (v j) (D j)) =
      (-1/2 : ℝ)^2 * l2sq (fun x => skewPart (T j) (v j) x / (D j)^2 +
        (euclideanLaplacian (T j) x / (D j)^2) * v j x) := by
    rw [show normalizedTransport (T j) (v j) (D j) = (fun x => (-1/2 : ℝ) *
      (skewPart (T j) (v j) x / (D j)^2 + (euclideanLaplacian (T j) x / (D j)^2) * v j x)) from
        funext (normalized_transport_identity (T j) (v j) (D j)), l2sq_const_mul]
  simpa only [← hid, mul_zero] using hconst

lemma integral_normalized_hessian (T v : Plane → ℝ) (S D : ℝ) (i j : Fin 2) :
    (∫ x, (coordPartial (coordPartial T j) i x / S) *
      normalizedPartial v D i x * normalizedPartial v D j x) =
    (∫ x, coordPartial (coordPartial T j) i x * coordPartial v i x * coordPartial v j x) /
      (S*D^2) := by
  calc
    _ = ∫ x, (coordPartial (coordPartial T j) i x * coordPartial v i x * coordPartial v j x) /
        (S*D^2) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [normalizedPartial, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := integral_div _ _

lemma normalized_hessian_expansion {T v : Plane → ℝ} (hT : Smooth T) (S D : ℝ) :
    hessianEnergy T v / (S*D^2) =
      (∫ x, (coordPartial (coordPartial T 0) 0 x / S) *
        normalizedPartial v D 0 x * normalizedPartial v D 0 x) +
      2*(∫ x, (coordPartial (coordPartial T 0) 1 x / S) *
        normalizedPartial v D 0 x * normalizedPartial v D 1 x) +
      (∫ x, (coordPartial (coordPartial T 1) 1 x / S) *
        normalizedPartial v D 1 x * normalizedPartial v D 1 x) := by
  have hcross : (∫ x, (coordPartial (coordPartial T 0) 1 x / S) *
      normalizedPartial v D 1 x * normalizedPartial v D 0 x) =
      (∫ x, (coordPartial (coordPartial T 0) 1 x / S) *
        normalizedPartial v D 0 x * normalizedPartial v D 1 x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  unfold hessianEnergy
  simp only [Fin.sum_univ_two, add_div, ← integral_normalized_hessian]
  simp_rw [partial_partial hT 1 0]
  rw [hcross]
  ring

lemma integral_coefficient_difference {a f g : Plane → ℝ} (A : ℝ)
    (ha : Smooth a) (hf : Smooth f) (hg : Smooth g) (hc : HasCompactSupport f) :
    (∫ x, (a x - A) * f x * g x) =
      (∫ x, a x * f x * g x) - A*(∫ x, f x * g x) := by
  calc
    _ = ∫ x, a x * f x * g x - A*(f x*g x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := by
      rw [integral_sub (integrable_mul_compact_left (ha.mul hf) hg hc.mul_left)
        ((integrable_mul_compact_left hf hg hc).const_mul A), integral_const_mul]


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_SupportLimits
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

open Filter in
lemma eventually_support_iff (v : ℕ → Plane → ℝ) (P : ℕ → Plane → Prop) :
    (∀ᶠ z : SupportIndex v in supportFilter v, P z.1 z.2.1) ↔
      ∀ᶠ j in atTop, ∀ x ∈ tsupport (v j), P j x := by
  rw [supportFilter, eventually_comap]
  constructor
  · intro h
    filter_upwards [h] with j hj x hx
    exact hj ⟨j, x, hx⟩ rfl
  · intro h
    filter_upwards [h] with j hj z hz
    subst j
    exact hj z.2.1 z.2.2

lemma SupportLimit.eventually_abs_sub_le {v f : ℕ → Plane → ℝ} {A ε : ℝ}
    (h : SupportLimit v f A) (hε : 0 < ε) :
    ∀ᶠ j in Filter.atTop, ∀ x ∈ tsupport (v j), |f j x-A| ≤ ε := by
  apply (eventually_support_iff v _).mp
  have hh := (Metric.tendsto_nhds.mp h) ε hε
  filter_upwards [hh] with z hz
  exact (show |f z.1 z.2.1-A| < ε from hz).le

lemma SupportLimit.const {v : ℕ → Plane → ℝ} (A : ℝ) :
    SupportLimit v (fun _ _ => A) A := tendsto_const_nhds

open Filter in
lemma SupportLimit.of_seq {v : ℕ → Plane → ℝ} {r : ℕ → ℝ} {A : ℝ}
    (h : Tendsto r atTop (𝓝 A)) : SupportLimit v (fun j _ => r j) A :=
  h.comp tendsto_comap

lemma SupportLimit.add {v f g : ℕ → Plane → ℝ} {A B : ℝ}
    (hf : SupportLimit v f A) (hg : SupportLimit v g B) :
    SupportLimit v (fun j x => f j x + g j x) (A+B) := Filter.Tendsto.add hf hg

lemma SupportLimit.sub {v f g : ℕ → Plane → ℝ} {A B : ℝ}
    (hf : SupportLimit v f A) (hg : SupportLimit v g B) :
    SupportLimit v (fun j x => f j x - g j x) (A-B) := Filter.Tendsto.sub hf hg

lemma SupportLimit.mul {v f g : ℕ → Plane → ℝ} {A B : ℝ}
    (hf : SupportLimit v f A) (hg : SupportLimit v g B) :
    SupportLimit v (fun j x => f j x * g j x) (A*B) := Filter.Tendsto.mul hf hg

lemma SupportLimit.neg {v f : ℕ → Plane → ℝ} {A : ℝ}
    (hf : SupportLimit v f A) : SupportLimit v (fun j x => -f j x) (-A) := Filter.Tendsto.neg hf

lemma SupportLimit.pow {v f : ℕ → Plane → ℝ} {A : ℝ}
    (hf : SupportLimit v f A) (n : ℕ) : SupportLimit v (fun j x => (f j x)^n) (A^n) := Filter.Tendsto.pow hf n

open Filter in
lemma coefficient_square_tendsto_const_support {a v : ℕ → Plane → ℝ} {A : ℝ}
    (ha : ∀ j, Smooth (a j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j) = 1)
    (hlim : SupportLimit v a A) :
    Tendsto (fun j => ∫ x, a j x * (v j x * v j x)) atTop (𝓝 A) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := hlim.eventually_abs_sub_le (half_pos hε)
  filter_upwards [he] with j hj
  have hb := integral_coefficient_square_abs_le ((ha j).sub contDiff_const) (hv j) (hcv j)
    (half_pos hε).le hj
  have hid := integral_coefficient_difference A (ha j) (hv j) (hv j) (hcv j)
  simp only [mul_assoc] at hid
  rw [hid] at hb
  change |(∫ x, a j x * (v j x*v j x))-A*l2sq (v j)| ≤ ε/2*l2sq (v j) at hb
  rw [hv1 j, mul_one, mul_one] at hb
  exact hb.trans_lt (half_lt_self hε)

open Filter in
lemma coefficient_pairing_support_zero_of_bound {a v f g : ℕ → Plane → ℝ} {r : ℕ → ℝ} {E : ℝ}
    (ha : ∀ j, Smooth (a j)) (hf : ∀ j, Smooth (f j)) (hg : ∀ j, Smooth (g j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcg : ∀ j, HasCompactSupport (g j))
    (hsub : ∀ j, tsupport (f j) ⊆ tsupport (v j))
    (hlim : SupportLimit v a 0)
    (hbound : ∀ j, l2sq (f j)+l2sq (g j) ≤ r j)
    (henergy : Tendsto r atTop (𝓝 E)) :
    Tendsto (fun j => ∫ x, a j x * f j x * g j x) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let B := |E|+1
  have hB : 0 < B := by dsimp [B]; linarith only [abs_nonneg E]
  have hEB : E < B := by dsimp [B]; linarith only [le_abs_self E]
  have he := hlim.eventually_abs_sub_le (div_pos hε hB)
  have hEB' := henergy.eventually_lt_const hEB
  filter_upwards [he, hEB'] with j hj hEj
  have hb := integral_coefficient_mul_abs_le (ha j) (hf j) (hg j) (hcf j) (hcg j)
    (div_pos hε hB).le (fun x hx => by simpa only [sub_zero] using hj x (hsub j hx))
  rw [Real.dist_eq, sub_zero]
  calc
    _ ≤ ε/B/2*(l2sq (f j)+l2sq (g j)) := hb
    _ ≤ ε/B/2*B := mul_le_mul_of_nonneg_left ((hbound j).trans hEj.le) (div_nonneg (div_pos hε hB).le (by norm_num))
    _ = ε/2 := by field_simp
    _ < ε := half_lt_self hε

lemma carleman_commutator_energy {T p v : Plane → ℝ}
    (hT : Smooth T) (hp : Smooth p) (hv : Smooth v) (hc : HasCompactSupport v) (K : ℝ) :
    2 * (∫ x, plusPart (fun x => gradientSquared T x + K^2*p x) v x * skewPart T v x) =
      4*hessianEnergy T v + 4*hessianGradientEnergy T v - bilaplacianEnergy T v +
        2*K^2*potentialTransport p T v := by
  rw [show plusPart (fun x => gradientSquared T x + K^2*p x) v =
      (fun x => euclideanLaplacian v x + (gradientSquared T x + K^2*p x)*v x) from rfl,
    carleman_commutator hT hp hv hc]
  simp only [hessianEnergy, hessianGradientEnergy, bilaplacianEnergy, potentialTransport,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  ring

lemma integral_normalized_hessianGradient (T v : Plane → ℝ) (S D : ℝ) (i j : Fin 2) :
    (∫ x, (coordPartial (coordPartial T j) i x / S) *
      (coordPartial T j x / D) * (coordPartial T i x / D) * (v x*v x)) =
    (∫ x, coordPartial (coordPartial T j) i x * coordPartial T j x * coordPartial T i x * (v x*v x)) /
      (S*D^2) := by
  calc
    _ = ∫ x, (coordPartial (coordPartial T j) i x * coordPartial T j x * coordPartial T i x * (v x*v x)) /
        (S*D^2) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := integral_div _ _

open Filter in
lemma normalized_hessianGradient_limit {T v : ℕ → Plane → ℝ} {S D : ℕ → ℝ}
    (a : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (hT : ∀ j, Smooth (T j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x / D j) (a i))
    (hH : ∀ i k, SupportLimit v (fun j x => coordPartial (coordPartial (T j) k) i x / S j) (H i k)) :
    Tendsto (fun j => hessianGradientEnergy (T j) (v j)/(S j*(D j)^2)) atTop
      (𝓝 (∑ i : Fin 2, ∑ k : Fin 2, H i k * a k * a i)) := by
  have hi (i k : Fin 2) := coefficient_square_tendsto_const_support
    (fun j => (((smooth_partial (smooth_partial (hT j) k) i).div_const _).mul
        ((smooth_partial (hT j) k).div_const _)).mul ((smooth_partial (hT j) i).div_const _))
    hv hcv hv1 (((hH i k).mul (hgrad k)).mul (hgrad i))
  have hs := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun k _ => hi i k))
  simpa only [integral_normalized_hessianGradient, hessianGradientEnergy, Finset.sum_div] using hs

open Filter in
lemma variable_quadratic_difference_support_limit {v h₀ h₁ h₂ f g : ℕ → Plane → ℝ}
    {A B C E : ℝ}
    (hh₀ : ∀ j, Smooth (h₀ j)) (hh₁ : ∀ j, Smooth (h₁ j)) (hh₂ : ∀ j, Smooth (h₂ j))
    (hf : ∀ j, Smooth (f j)) (hg : ∀ j, Smooth (g j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcg : ∀ j, HasCompactSupport (g j))
    (hsubf : ∀ j, tsupport (f j) ⊆ tsupport (v j))
    (hsubg : ∀ j, tsupport (g j) ⊆ tsupport (v j))
    (hb₀ : SupportLimit v h₀ A) (hb₁ : SupportLimit v h₁ B) (hb₂ : SupportLimit v h₂ C)
    (henergy : Tendsto (fun j => l2sq (f j) + l2sq (g j)) atTop (𝓝 E)) :
    Tendsto (fun j =>
      ((∫ x, h₀ j x * f j x * f j x) + 2*(∫ x, h₁ j x * f j x * g j x) +
        (∫ x, h₂ j x * g j x * g j x)) - quadraticEnergy A B C (f j) (g j))
      atTop (𝓝 0) := by
  have hfbound (j : ℕ) : l2sq (f j) + l2sq (f j) ≤ 2*(l2sq (f j)+l2sq (g j)) := by
    linarith only [l2sq_nonneg (g j)]
  have hgbound (j : ℕ) : l2sq (g j) + l2sq (g j) ≤ 2*(l2sq (f j)+l2sq (g j)) := by
    linarith only [l2sq_nonneg (f j)]
  have h₀lim : SupportLimit v (fun j x => h₀ j x-A) 0 := by
    simpa only [sub_self] using hb₀.sub (SupportLimit.const A)
  have h₁lim : SupportLimit v (fun j x => h₁ j x-B) 0 := by
    simpa only [sub_self] using hb₁.sub (SupportLimit.const B)
  have h₂lim : SupportLimit v (fun j x => h₂ j x-C) 0 := by
    simpa only [sub_self] using hb₂.sub (SupportLimit.const C)
  have h₀zero := coefficient_pairing_support_zero_of_bound
    (fun j => (hh₀ j).sub contDiff_const) hf hf hcf hcf hsubf h₀lim hfbound (henergy.const_mul 2)
  have h₁zero := coefficient_pairing_support_zero_of_bound
    (fun j => (hh₁ j).sub contDiff_const) hf hg hcf hcg hsubf h₁lim (fun _ => le_rfl) henergy
  have h₂zero := coefficient_pairing_support_zero_of_bound
    (fun j => (hh₂ j).sub contDiff_const) hg hg hcg hcg hsubg h₂lim hgbound (henergy.const_mul 2)
  have hi (j : ℕ) :
      (∫ x, (h₀ j x-A)*f j x*f j x) + 2*(∫ x, (h₁ j x-B)*f j x*g j x) +
      (∫ x, (h₂ j x-C)*g j x*g j x) =
      ((∫ x, h₀ j x * f j x * f j x) + 2*(∫ x, h₁ j x * f j x * g j x) +
        (∫ x, h₂ j x * g j x * g j x)) - quadraticEnergy A B C (f j) (g j) := by
    rw [integral_coefficient_difference A (hh₀ j) (hf j) (hf j) (hcf j),
      integral_coefficient_difference B (hh₁ j) (hf j) (hg j) (hcf j),
      integral_coefficient_difference C (hh₂ j) (hg j) (hg j) (hcg j)]
    unfold quadraticEnergy l2sq
    ring
  simpa only [hi, mul_zero, add_zero] using (h₀zero.add (h₁zero.const_mul 2)).add h₂zero

open Filter in
lemma normalized_hessian_trace_support_limit {T v : ℕ → Plane → ℝ} {S D : ℕ → ℝ}
    (a₀ a₁ A B C : ℝ) (ha : a₀^2+a₁^2 ≠ 0)
    (hT : ∀ j, Smooth (T j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j))
    (hb₀ : SupportLimit v (fun j x => coordPartial (coordPartial (T j) 0) 0 x/S j) A)
    (hb₁ : SupportLimit v (fun j x => coordPartial (coordPartial (T j) 0) 1 x/S j) B)
    (hb₂ : SupportLimit v (fun j x => coordPartial (coordPartial (T j) 1) 1 x/S j) C)
    (henergy : Tendsto (fun j => l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1)) atTop (𝓝 (a₀^2+a₁^2)))
    (hparallel : Tendsto (fun j => l2sq (fun x => a₀ * normalizedPartial (v j) (D j) 0 x +
      a₁ * normalizedPartial (v j) (D j) 1 x)) atTop (𝓝 0)) :
    Tendsto (fun j => hessianEnergy (T j) (v j) / (S j*(D j)^2) +
      (A*a₀^2+2*B*a₀*a₁+C*a₁^2)) atTop (𝓝 ((a₀^2+a₁^2)*(A+C))) := by
  have htrace := plane_trace_energy_limit a₀ a₁ A B C ha
    (fun j => smooth_normalizedPartial (hv j) _ _) (fun j => smooth_normalizedPartial (hv j) _ _)
    (fun j => compact_normalizedPartial (hcv j) _ _) (fun j => compact_normalizedPartial (hcv j) _ _)
    henergy hparallel
  have herr := variable_quadratic_difference_support_limit
    (fun j => (smooth_partial (smooth_partial (hT j) 0) 0).div_const _)
    (fun j => (smooth_partial (smooth_partial (hT j) 0) 1).div_const _)
    (fun j => (smooth_partial (smooth_partial (hT j) 1) 1).div_const _)
    (fun j => smooth_normalizedPartial (hv j) _ _) (fun j => smooth_normalizedPartial (hv j) _ _)
    (fun j => compact_normalizedPartial (hcv j) _ _) (fun j => compact_normalizedPartial (hcv j) _ _)
    (fun j => normalizedPartial_tsupport_subset _ _ _) (fun j => normalizedPartial_tsupport_subset _ _ _)
    hb₀ hb₁ hb₂ henergy
  have hsum := herr.add htrace
  convert hsum using 1
  · ext j
    rw [normalized_hessian_expansion (hT j)]
    ring
  · simp only [zero_add]

open Filter in
lemma normalized_gradient_energy_support_limit {q v : ℕ → Plane → ℝ} {S D : ℕ → ℝ} {C A : ℝ}
    (hq : ∀ j, Smooth (q j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j) = 1)
    (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j) (hSinf : Tendsto S atTop atTop)
    (hbound : ∀ j, l2norm (plusPart (q j) (v j)) ≤ C * (Real.sqrt (S j) * D j))
    (hlim : SupportLimit v (fun j x => q j x/(D j)^2) A) :
    Tendsto (fun j => l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1)) atTop (𝓝 A) := by
  have hpair := pairing_div_square_tendsto_zero (fun j => smooth_plus (hq j) (hv j)) hv
    (fun j => compact_plus (hcv j)) hcv hv1 hS hD hSinf hbound
  have hcoeff := coefficient_square_tendsto_const_support (fun j => (hq j).div_const ((D j)^2)) hv
    hcv hv1 hlim
  have hi (j : ℕ) : l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1) =
      (∫ x, (q j x / (D j)^2) * (v j x * v j x)) -
        (∫ x, plusPart (q j) (v j) x * v j x) / (D j)^2 := by
    rw [normalizedPartial_energy, normalized_coefficient_integral, plus_energy_identity (hq j) (hv j) (hcv j)]
    ring
  simpa only [← hi, sub_zero] using hcoeff.sub hpair

open Filter in
lemma l2sq_coefficient_mul_support_zero {a v f : ℕ → Plane → ℝ} {r : ℕ → ℝ} {E : ℝ}
    (ha : ∀ j, Smooth (a j)) (hf : ∀ j, Smooth (f j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hsub : ∀ j, tsupport (f j) ⊆ tsupport (v j))
    (hlim : SupportLimit v a 0)
    (hbound : ∀ j, l2sq (f j) ≤ r j) (hr : Tendsto r atTop (𝓝 E)) :
    Tendsto (fun j => l2sq (fun x => a j x*f j x)) atTop (𝓝 0) := by
  have hlim2 : SupportLimit v (fun j x => (a j x)^2) 0 := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hlim.pow 2
  have h := coefficient_pairing_support_zero_of_bound (fun j => (ha j).pow 2) hf hf hcf hcf hsub hlim2
    (fun j => by linarith only [hbound j] : ∀ j, l2sq (f j)+l2sq (f j) ≤ 2*r j) (hr.const_mul 2)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext j
  unfold l2sq
  apply integral_congr_ae
  filter_upwards [] with x
  ring

open Filter in
lemma normalized_parallel_support_limit {T v : ℕ → Plane → ℝ} {S D : ℕ → ℝ} {c C E : ℝ}
    (a : Fin 2 → ℝ)
    (hT : ∀ j, Smooth (T j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j) = 1)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j)
    (hSinf : Tendsto S atTop atTop)
    (hY : ∀ j, l2norm (skewPart (T j) (v j)) ≤ C*(Real.sqrt (S j)*D j))
    (hH : ∀ j i k x, x ∈ tsupport (v j) → |coordPartial (coordPartial (T j) k) i x| ≤ c*S j)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x / D j) (a i))
    (henergy : Tendsto (fun j => l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1)) atTop (𝓝 E)) :
    Tendsto (fun j => l2sq (fun x => a 0 * normalizedPartial (v j) (D j) 0 x +
      a 1 * normalizedPartial (v j) (D j) 1 x)) atTop (𝓝 0) := by
  let f := fun j i => normalizedPartial (v j) (D j) i
  let q := fun j i x => a i - coordPartial (T j) i x / D j
  have hf (j i) : Smooth (f j i) := smooth_normalizedPartial (hv j) _ _
  have hcf (j i) : HasCompactSupport (f j i) := compact_normalizedPartial (hcv j) _ _
  have hq (j i) : Smooth (q j i) := contDiff_const.sub ((smooth_partial (hT j) i).div_const _)
  have htotal (j : ℕ) (i : Fin 2) : l2sq (f j i) ≤ l2sq (f j 0)+l2sq (f j 1) := by
    fin_cases i
    · change l2sq (f j 0) ≤ l2sq (f j 0)+l2sq (f j 1)
      linarith only [l2sq_nonneg (f j 1)]
    · change l2sq (f j 1) ≤ l2sq (f j 0)+l2sq (f j 1)
      linarith only [l2sq_nonneg (f j 0)]
  have hzero (i : Fin 2) : Tendsto (fun j => l2sq (fun x => q j i x*f j i x)) atTop (𝓝 0) := by
    apply l2sq_coefficient_mul_support_zero (fun j => hq j i) (fun j => hf j i)
      (fun j => hcf j i) (fun j => normalizedPartial_tsupport_subset _ _ _) _
      (fun j => htotal j i) henergy
    simpa only [q, sub_self] using (SupportLimit.const (a i)).sub (hgrad i)
  have hcorr := l2sq_add_tendsto_zero
    (fun j => (hq j 0).mul (hf j 0)) (fun j => (hq j 1).mul (hf j 1))
    (fun j => (hcf j 0).mul_left) (fun j => (hcf j 1).mul_left) (hzero 0) (hzero 1)
  have htransport := normalized_transport_square_limit hT hv hcv hv1 hc hC hS hD hSinf hY hH
  have hsum := l2sq_add_tendsto_zero (fun j => smooth_normalizedTransport (hT j) (hv j) _)
    (fun j => ((hq j 0).mul (hf j 0)).add ((hq j 1).mul (hf j 1)))
    (fun j => compact_normalizedTransport (hcv j) _)
    (fun j => (hcf j 0).mul_left.add (hcf j 1).mul_left) htransport hcorr
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  ext j
  congr 1
  ext x
  dsimp [normalizedTransport, f, q]
  ring

lemma normalized_potential_coefficient_limit {T p v : ℕ → Plane → ℝ} {D K : ℕ → ℝ}
    (a : Fin 2 → ℝ)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x/D j) (a i))
    (hp : SupportLimit v (fun j x => (K j)^2*p j x/(D j)^2) 0) :
    SupportLimit v (fun j x => (gradientSquared (T j) x+(K j)^2*p j x)/(D j)^2)
      ((a 0)^2+(a 1)^2) := by
  have h := ((hgrad 0).pow 2).add ((hgrad 1).pow 2) |>.add hp
  convert h using 1
  · ext j x
    simp only [gradientSquared, Fin.sum_univ_two, div_pow]
    ring
  · simp only [add_zero]

open Filter in
lemma normalized_bilaplacian_limit {T v : ℕ → Plane → ℝ} {S D : ℕ → ℝ}
    (hT : ∀ j, Smooth (T j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hB : ∀ i k, SupportLimit v (fun j x =>
      coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x / (S j*(D j)^2)) 0) :
    Tendsto (fun j => bilaplacianEnergy (T j) (v j)/(S j*(D j)^2)) atTop (𝓝 0) := by
  have hi (i k : Fin 2) := coefficient_square_tendsto_const_support
    (fun j => (smooth_partial (smooth_partial (smooth_partial (smooth_partial (hT j) k) k) i) i).div_const _)
    hv hcv hv1 (hB i k)
  have hnorm (j : ℕ) (i k : Fin 2) :
      (∫ x, (coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x /
        (S j*(D j)^2))*(v j x*v j x)) =
      (∫ x, coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x *
        (v j x*v j x))/(S j*(D j)^2) := by
    simp only [div_mul_eq_mul_div]
    exact integral_div _ _
  simpa only [hnorm, bilaplacianEnergy, Finset.sum_div, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun k _ => tendsto_finsetSum Finset.univ (fun i _ => hi i k))

open Filter in
lemma normalized_potentialTransport_limit {T p v : ℕ → Plane → ℝ} {S D K : ℕ → ℝ}
    (hT : ∀ j, Smooth (T j)) (hp : ∀ j, Smooth (p j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hP : ∀ i, SupportLimit v (fun j x =>
      (K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/(S j*(D j)^2)) 0) :
    Tendsto (fun j => (K j)^2*potentialTransport (p j) (T j) (v j)/(S j*(D j)^2)) atTop (𝓝 0) := by
  have hi (i : Fin 2) := coefficient_square_tendsto_const_support
    (fun j => ((contDiff_const.mul (smooth_partial (hp j) i)).mul (smooth_partial (hT j) i)).div_const _)
    hv hcv hv1 (hP i)
  have hnorm (j : ℕ) (i : Fin 2) :
      (∫ x, ((K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/(S j*(D j)^2))*(v j x*v j x)) =
      (K j)^2*(∫ x, coordPartial (p j) i x*coordPartial (T j) i x*(v j x*v j x))/(S j*(D j)^2) := by
    simp only [div_mul_eq_mul_div, mul_assoc]
    rw [integral_div, integral_const_mul]
  simpa only [hnorm, potentialTransport, Finset.sum_div, Finset.mul_sum, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun i _ => hi i)

lemma hessian_form_expansion (a : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (hsym : H 0 1=H 1 0) :
    (∑ i : Fin 2, ∑ k : Fin 2, H i k*a k*a i) =
      H 0 0*(a 0)^2 + 2*H 1 0*a 0*a 1 + H 1 1*(a 1)^2 := by
  simp only [Fin.sum_univ_two, hsym]
  ring

open Filter in

lemma normalized_commutator_trace_limit {T p v : ℕ → Plane → ℝ} {S D K : ℕ → ℝ}
    (a : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (ha : (a 0)^2+(a 1)^2 ≠ 0) (hsym : H 0 1=H 1 0)
    (hT : ∀ j, Smooth (T j)) (hp : ∀ j, Smooth (p j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x/D j) (a i))
    (hH : ∀ i k, SupportLimit v (fun j x => coordPartial (coordPartial (T j) k) i x/S j) (H i k))
    (hB : ∀ i k, SupportLimit v (fun j x =>
      coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x / (S j*(D j)^2)) 0)
    (hP : ∀ i, SupportLimit v (fun j x =>
      (K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/(S j*(D j)^2)) 0)
    (henergy : Tendsto (fun j => l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1)) atTop (𝓝 ((a 0)^2+(a 1)^2)))
    (hparallel : Tendsto (fun j => l2sq (fun x => a 0 * normalizedPartial (v j) (D j) 0 x +
      a 1 * normalizedPartial (v j) (D j) 1 x)) atTop (𝓝 0)) :
    Tendsto (fun j => (2*(∫ x, plusPart (fun x => gradientSquared (T j) x+(K j)^2*p j x) (v j) x *
      skewPart (T j) (v j) x))/(S j*(D j)^2)) atTop
      (𝓝 (4*((a 0)^2+(a 1)^2)*(H 0 0+H 1 1))) := by
  let A := H 0 0*(a 0)^2+2*H 1 0*a 0*a 1+H 1 1*(a 1)^2
  have ht := normalized_hessian_trace_support_limit (a 0) (a 1) (H 0 0) (H 1 0) (H 1 1) ha
    hT hv hcv (hH 0 0) (hH 1 0) (hH 1 1) henergy hparallel
  have hh := normalized_hessianGradient_limit a H hT hv hcv hv1 hgrad hH
  rw [hessian_form_expansion a H hsym] at hh
  have hb := normalized_bilaplacian_limit hT hv hcv hv1 hB
  have hp' := normalized_potentialTransport_limit hT hp hv hcv hv1 hP
  have h := (((ht.add (hh.sub_const A)).const_mul 4).sub hb).add (hp'.const_mul 2)
  convert h using 1
  · ext j
    rw [carleman_commutator_energy (hT j) (hp j) (hv j) (hcv j)]
    dsimp [A]
    ring
  · dsimp [A]
    ring_nf


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Carleman
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

open Filter in

theorem no_normalized_quasimodes {T p v : ℕ → Plane → ℝ} {S D K : ℕ → ℝ} {c : ℝ}
    (a : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (ha : (a 0)^2+(a 1)^2 ≠ 0) (hsym : H 0 1=H 1 0) (htrace : 0 < H 0 0+H 1 1)
    (hT : ∀ j, Smooth (T j)) (hp : ∀ j, Smooth (p j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hc : 1 ≤ c) (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j) (hSinf : Tendsto S atTop atTop)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x/D j) (a i))
    (hH : ∀ i k, SupportLimit v (fun j x => coordPartial (coordPartial (T j) k) i x/S j) (H i k))
    (hB : ∀ i k, SupportLimit v (fun j x =>
      coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x / (S j*(D j)^2)) 0)
    (hP : ∀ i, SupportLimit v (fun j x =>
      (K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/(S j*(D j)^2)) 0)
    (hpot : SupportLimit v (fun j x => (K j)^2*p j x/(D j)^2) 0)
    (hqbound : ∀ j x, x ∈ tsupport (v j) → |gradientSquared (T j) x+(K j)^2*p j x| ≤ c*(D j)^2)
    (hHbound : ∀ j i k x, x ∈ tsupport (v j) →
      |coordPartial (coordPartial (T j) k) i x| ≤ c*S j)
    (hBbound : ∀ j i k x, x ∈ tsupport (v j) →
      |coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x| ≤ c*S j*(D j)^2)
    (hqTbound : ∀ j i x, x ∈ tsupport (v j) →
      |coordPartial (fun x => gradientSquared (T j) x+(K j)^2*p j x) i x * coordPartial (T j) i x| ≤ c*S j*(D j)^2)
    (hsmall : ∀ j, l2sq (fun x => plusPart (fun x => gradientSquared (T j) x+(K j)^2*p j x) (v j) x +
      skewPart (T j) (v j) x) ≤ S j*(D j)^2)
    (hzero : Tendsto (fun j => l2sq (fun x => plusPart (fun x => gradientSquared (T j) x+(K j)^2*p j x) (v j) x +
      skewPart (T j) (v j) x)/(S j*(D j)^2)) atTop (𝓝 0)) : False := by
  let q := fun j x => gradientSquared (T j) x+(K j)^2*p j x
  have hq (j) : Smooth (q j) := (smooth_gradientSquared (hT j)).add (contDiff_const.mul (hp j))
  have hboot (j) := operator_bootstrap (hq j) (hT j) (hv j) (hcv j) hc (hS j) (hD j) (hv1 j)
    (hqbound j) (hHbound j) (hBbound j) (hqTbound j) (hsmall j)
  have henergy := normalized_gradient_energy_support_limit hq hv hcv hv1 hS hD hSinf
    (fun j => (hboot j).1) (normalized_potential_coefficient_limit a hgrad hpot)
  have hparallel := normalized_parallel_support_limit a hT hv hcv hv1 (by linarith : 0 ≤ c)
    (by linarith : 0 ≤ 16*c+4) hS hD hSinf (fun j => (hboot j).2.1) hHbound hgrad henergy
  have hcomm := normalized_commutator_trace_limit a H ha hsym hT hp hv hcv hv1 hgrad hH hB hP henergy hparallel
  have hle (j) : (2*(∫ x, plusPart (q j) (v j) x*skewPart (T j) (v j) x))/(S j*(D j)^2) ≤
      l2sq (fun x => plusPart (q j) (v j) x+skewPart (T j) (v j) x)/(S j*(D j)^2) :=
    div_le_div_of_nonneg_right
      (commutator_le_sum_square (smooth_plus (hq j) (hv j)) (smooth_skew (hT j) (hv j))
        (compact_plus (hcv j)) (compact_skew (hcv j)))
      (mul_nonneg (by linarith only [hS j]) (sq_nonneg _))
  have hlimle := le_of_tendsto_of_tendsto hcomm hzero (Filter.Eventually.of_forall hle)
  have hapos : 0 < (a 0)^2+(a 1)^2 := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) ha.symm
  have hpos : 0 < 4*((a 0)^2+(a 1)^2)*(H 0 0+H 1 1) := mul_pos (mul_pos (by norm_num) hapos) htrace
  exact (not_le_of_gt hpos) hlimle

open Filter in
lemma SupportLimit.reindex {v f : ℕ → Plane → ℝ} {A : ℝ} {φ : ℕ → ℕ}
    (h : SupportLimit v f A) (hφ : Tendsto φ atTop atTop) :
    SupportLimit (fun j => v (φ j)) (fun j => f (φ j)) A := by
  let F : SupportIndex (fun j => v (φ j)) → SupportIndex v := fun z => ⟨φ z.1, z.2⟩
  have hF : Tendsto F (supportFilter (fun j => v (φ j))) (supportFilter v) := by
    apply tendsto_comap_iff.mpr
    exact hφ.comp tendsto_comap
  exact h.comp hF

open Filter in
lemma SupportLimit.finite_bound {ι : Type*} [Fintype ι]
    {v : ℕ → Plane → ℝ} {f : ι → ℕ → Plane → ℝ} {A : ι → ℝ}
    (h : ∀ i, SupportLimit v (f i) (A i)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ j in atTop, ∀ i x, x ∈ tsupport (v j) → |f i j x| ≤ C := by
  let C := 1+∑ i, |A i|
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  refine ⟨C, hC, ?_⟩
  have hi (i : ι) := (h i).eventually_abs_sub_le (by norm_num : (0 : ℝ)<1)
  have he := eventually_all.mpr hi
  filter_upwards [he] with j hj i x hx
  have hAi : |A i| ≤ ∑ k, |A k| := Finset.single_le_sum (fun k _ => abs_nonneg (A k)) (Finset.mem_univ i)
  calc
    |f i j x| = |(f i j x-A i)+A i| := by rw [sub_add_cancel]
    _ ≤ |f i j x-A i|+|A i| := abs_add_le _ _
    _ ≤ C := add_le_add (hj i x hx) hAi

lemma normalized_derivative_potential_limit {T p v : ℕ → Plane → ℝ} {S D K : ℕ → ℝ}
    (a : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (hT : ∀ j, Smooth (T j)) (hp : ∀ j, Smooth (p j))
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x/D j) (a i))
    (hH : ∀ i k, SupportLimit v (fun j x => coordPartial (coordPartial (T j) k) i x/S j) (H i k))
    (hP : ∀ i, SupportLimit v (fun j x =>
      (K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/(S j*(D j)^2)) 0)
    (i : Fin 2) :
    SupportLimit v (fun j x =>
      coordPartial (fun x => gradientSquared (T j) x+(K j)^2*p j x) i x * coordPartial (T j) i x /
        (S j*(D j)^2)) (2*(H i 0*a 0*a i+H i 1*a 1*a i)) := by
  have hh := (((hH i 0).mul (hgrad 0)).mul (hgrad i)).add
    (((hH i 1).mul (hgrad 1)).mul (hgrad i))
  have h := ((SupportLimit.const 2).mul hh).add (hP i)
  convert h using 1
  · ext j x
    rw [partial_add (smooth_gradientSquared (hT j)) (contDiff_const.mul (hp j)),
      partial_gradientSquared (hT j), partial_const_mul (hp j)]
    simp only [Fin.sum_univ_two, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [add_zero]

lemma abs_le_mul_of_div {x d C : ℝ} (hd : 0<d) (h : |x/d|≤C) : |x|≤C*d := by
  rw [abs_div, abs_of_pos hd, div_le_iff₀ hd] at h
  exact h

open Filter in

theorem no_asymptotic_quasimodes {T p v : ℕ → Plane → ℝ} {S D K : ℕ → ℝ}
    (a : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (ha : (a 0)^2+(a 1)^2 ≠ 0) (hsym : H 0 1=H 1 0) (htrace : 0 < H 0 0+H 1 1)
    (hT : ∀ j, Smooth (T j)) (hp : ∀ j, Smooth (p j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hD : ∀ j, S j ≤ D j) (hSinf : Tendsto S atTop atTop)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x/D j) (a i))
    (hH : ∀ i k, SupportLimit v (fun j x => coordPartial (coordPartial (T j) k) i x/S j) (H i k))
    (hB : ∀ i k, SupportLimit v (fun j x =>
      coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x / (S j*(D j)^2)) 0)
    (hP : ∀ i, SupportLimit v (fun j x =>
      (K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/(S j*(D j)^2)) 0)
    (hpot : SupportLimit v (fun j x => (K j)^2*p j x/(D j)^2) 0)
    (hzero : Tendsto (fun j => l2sq (fun x => plusPart (fun x => gradientSquared (T j) x+(K j)^2*p j x) (v j) x +
      skewPart (T j) (v j) x)/(S j*(D j)^2)) atTop (𝓝 0)) : False := by
  have hq := normalized_potential_coefficient_limit a hgrad hpot
  obtain ⟨Cq, hCq, hqe⟩ := SupportLimit.finite_bound (fun _ : Unit => hq)
  obtain ⟨CH, hCH, hHe⟩ := SupportLimit.finite_bound (fun z : Fin 2 × Fin 2 => hH z.1 z.2)
  obtain ⟨CB, hCB, hBe⟩ := SupportLimit.finite_bound (fun z : Fin 2 × Fin 2 => hB z.1 z.2)
  obtain ⟨CT, hCT, hTe⟩ := SupportLimit.finite_bound
    (normalized_derivative_potential_limit a H hT hp hgrad hH hP)
  let c := max (max Cq CH) (max CB CT)
  have hqc : Cq ≤ c := (le_max_left Cq CH).trans (le_max_left _ _)
  have hHc : CH ≤ c := (le_max_right Cq CH).trans (le_max_left _ _)
  have hBc : CB ≤ c := (le_max_left CB CT).trans (le_max_right _ _)
  have hTc : CT ≤ c := (le_max_right CB CT).trans (le_max_right _ _)
  have hc : 1 ≤ c := hCq.trans hqc
  have heS : ∀ᶠ j in atTop, 1 ≤ S j := hSinf.eventually (eventually_ge_atTop 1)
  have hesmall := hzero.eventually_lt_const (by norm_num : (0 : ℝ)<1)
  have he : ∀ᶠ j in atTop, 1 ≤ S j ∧
      (∀ x ∈ tsupport (v j), |gradientSquared (T j) x+(K j)^2*p j x| ≤ c*(D j)^2) ∧
      (∀ i k x, x ∈ tsupport (v j) → |coordPartial (coordPartial (T j) k) i x| ≤ c*S j) ∧
      (∀ i k x, x ∈ tsupport (v j) →
        |coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x| ≤ c*S j*(D j)^2) ∧
      (∀ i x, x ∈ tsupport (v j) →
        |coordPartial (fun x => gradientSquared (T j) x+(K j)^2*p j x) i x * coordPartial (T j) i x| ≤ c*S j*(D j)^2) ∧
      l2sq (fun x => plusPart (fun x => gradientSquared (T j) x+(K j)^2*p j x) (v j) x+
        skewPart (T j) (v j) x)≤S j*(D j)^2 := by
    filter_upwards [heS, hqe, hHe, hBe, hTe, hesmall] with j hj hqj hHj hBj hTj hsj
    have hSpos : 0<S j := by linarith
    have hDpos : 0<D j := hSpos.trans_le (hD j)
    have hden : 0<S j*(D j)^2 := mul_pos hSpos (sq_pos_of_pos hDpos)
    refine ⟨hj, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact abs_le_mul_of_div (sq_pos_of_pos hDpos) ((hqj () x hx).trans hqc)
    · intro i k x hx
      exact abs_le_mul_of_div hSpos ((hHj (i,k) x hx).trans hHc)
    · intro i k x hx
      simpa only [mul_assoc] using abs_le_mul_of_div hden ((hBj (i,k) x hx).trans hBc)
    · intro i x hx
      simpa only [mul_assoc] using abs_le_mul_of_div hden ((hTj i x hx).trans hTc)
    · exact (div_le_one hden).mp hsj.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have hn (j : ℕ) := hN (j+N) (Nat.le_add_left N j)
  have hφ := tendsto_add_atTop_nat N
  exact no_normalized_quasimodes a H ha hsym htrace
    (fun j => hT (j+N)) (fun j => hp (j+N)) (fun j => hv (j+N))
    (fun j => hcv (j+N)) (fun j => hv1 (j+N)) hc
    (fun j => (hn j).1) (fun j => hD (j+N)) (hSinf.comp hφ)
    (fun i => (hgrad i).reindex hφ) (fun i k => (hH i k).reindex hφ)
    (fun i k => (hB i k).reindex hφ) (fun i => (hP i).reindex hφ) (hpot.reindex hφ)
    (fun j => (hn j).2.1) (fun j => (hn j).2.2.1) (fun j => (hn j).2.2.2.1)
    (fun j => (hn j).2.2.2.2.1) (fun j => (hn j).2.2.2.2.2) (hzero.comp hφ)

lemma smooth_tiltedWeight (B : Plane) (S : ℝ) {χ : Plane → ℝ} (hχ : Smooth χ) :
    Smooth (tiltedWeight B S χ) :=
  ((innerSL ℝ B).contDiff.neg).sub (contDiff_const.mul hχ)

lemma partial_linear (B : Plane) (i : Fin 2) (x : Plane) :
    coordPartial (fun y => inner ℝ B y) i x = B i := by
  unfold coordPartial
  change fderiv ℝ (innerSL ℝ B) x (EuclideanSpace.single i 1) = B i
  rw [(innerSL ℝ B).fderiv]
  simp [EuclideanSpace.inner_single_right]

lemma partial_neg {f : Plane → ℝ} (hf : Smooth f) (i : Fin 2) (x : Plane) :
    coordPartial (fun y => -f y) i x = -coordPartial f i x := by
  simpa only [neg_one_mul] using partial_const_mul hf (-1) i x

lemma partial_sub {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (i : Fin 2) (x : Plane) :
    coordPartial (fun y => f y-g y) i x = coordPartial f i x-coordPartial g i x := by
  simp only [sub_eq_add_neg, partial_add hf hg.neg, partial_neg hg]

lemma partial_const (c : ℝ) (i : Fin 2) (x : Plane) :
    coordPartial (fun _ => c) i x = 0 := by simp [coordPartial]

lemma partial_tiltedWeight (B : Plane) (S : ℝ) {χ : Plane → ℝ} (hχ : Smooth χ)
    (i : Fin 2) (x : Plane) :
    coordPartial (tiltedWeight B S χ) i x = -B i-S*coordPartial χ i x := by
  change coordPartial (fun y => -(innerSL ℝ B) y-S*χ y) i x = _
  rw [partial_sub ((innerSL ℝ B).contDiff.neg) (contDiff_const.mul hχ),
    partial_neg (innerSL ℝ B).contDiff]
  change -coordPartial (fun y => inner ℝ B y) i x-coordPartial (fun y => S*χ y) i x = _
  rw [partial_linear, partial_const_mul hχ]

lemma partial2_tiltedWeight (B : Plane) (S : ℝ) {χ : Plane → ℝ} (hχ : Smooth χ)
    (i k : Fin 2) (x : Plane) :
    coordPartial (coordPartial (tiltedWeight B S χ) k) i x =
      -S*coordPartial (coordPartial χ k) i x := by
  simp_rw [funext (partial_tiltedWeight B S hχ k)]
  rw [partial_sub contDiff_const (contDiff_const.mul (smooth_partial hχ k)),
    partial_const, partial_const_mul (smooth_partial hχ k)]
  ring

lemma partial4_tiltedWeight (B : Plane) (S : ℝ) {χ : Plane → ℝ} (hχ : Smooth χ)
    (i k : Fin 2) (x : Plane) :
    coordPartial (coordPartial (coordPartial (coordPartial (tiltedWeight B S χ) k) k) i) i x =
      -S*coordPartial (coordPartial (coordPartial (coordPartial χ k) k) i) i x := by
  simp_rw [funext (partial2_tiltedWeight B S hχ k k)]
  simp_rw [funext (partial_const_mul (smooth_partial (smooth_partial hχ k) k) (-S) i)]
  exact partial_const_mul (smooth_partial (smooth_partial (smooth_partial hχ k) k) i) (-S) i x

lemma ShrinkingSupports.continuousAt {v : ℕ → Plane → ℝ} {x₀ : Plane}
    (hv : ShrinkingSupports v x₀) {f : Plane → ℝ} (hf : ContinuousAt f x₀) :
    SupportLimit v (fun _ x => f x) (f x₀) := hf.tendsto.comp hv

open Filter in
lemma SupportLimit.congr_eventually {v f g : ℕ → Plane → ℝ} {A : ℝ}
    (hf : SupportLimit v f A) (hfg : ∀ᶠ j in atTop, ∀ x ∈ tsupport (v j), f j x=g j x) :
    SupportLimit v g A :=
  hf.congr' ((eventually_support_iff v (fun j x => f j x=g j x)).mpr hfg)

open Filter in
lemma SupportLimit.zero_of_bound {v f : ℕ → Plane → ℝ} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0))
    (hf : ∀ᶠ j in atTop, ∀ x ∈ tsupport (v j), |f j x| ≤ r j) :
    SupportLimit v f 0 := by
  have h := (eventually_support_iff v (fun j x => |f j x| ≤ r j)).mpr hf
  have hr' : Tendsto (fun z : SupportIndex v => r z.1) (supportFilter v) (𝓝 0) :=
    hr.comp tendsto_comap
  exact squeeze_zero_norm' (h.mono (fun z hz => by simpa only [Real.norm_eq_abs] using hz)) hr'

open Filter in
lemma tilted_gradient_limit {v : ℕ → Plane → ℝ} {χ : Plane → ℝ} {B : ℕ → Plane}
    {S D : ℕ → ℝ} {b : Plane} {d : ℝ} {x₀ : Plane}
    (hχ : Smooth χ) (hv : ShrinkingSupports v x₀)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d)) (i : Fin 2) :
    SupportLimit v (fun j x => coordPartial (tiltedWeight (B j) (S j) χ) i x/D j)
      (-b i-d*coordPartial χ i x₀) := by
  have hbi : Tendsto (fun j => B j i/D j) atTop (𝓝 (b i)) := by
    have ht : Tendsto (fun j => ((D j)⁻¹ • B j) i) atTop (𝓝 (b i)) :=
      (EuclideanSpace.proj i).continuous.tendsto b |>.comp hb
    simpa only [PiLp.smul_apply, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using ht
  have h := (SupportLimit.of_seq hbi).neg.sub
    ((SupportLimit.of_seq hd).mul (hv.continuousAt (smooth_partial hχ i).continuous.continuousAt))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext j x
  rw [partial_tiltedWeight _ _ hχ]
  ring

open Filter in
lemma tilted_hessian_limit {v : ℕ → Plane → ℝ} {χ : Plane → ℝ} {B : ℕ → Plane}
    {S : ℕ → ℝ} {x₀ : Plane} (hχ : Smooth χ) (hv : ShrinkingSupports v x₀)
    (hS : Tendsto S atTop atTop) (i k : Fin 2) :
    SupportLimit v (fun j x => coordPartial (coordPartial (tiltedWeight (B j) (S j) χ) k) i x/S j)
      (-coordPartial (coordPartial χ k) i x₀) := by
  apply (hv.continuousAt (smooth_partial (smooth_partial hχ k) i).continuous.continuousAt).neg.congr_eventually
  filter_upwards [hS.eventually (eventually_gt_atTop 0)] with j hj x _
  rw [partial2_tiltedWeight _ _ hχ]
  field_simp

open Filter in
lemma tilted_bilaplacian_limit {v : ℕ → Plane → ℝ} {χ : Plane → ℝ} {B : ℕ → Plane}
    {S D : ℕ → ℝ} {x₀ : Plane} (hχ : Smooth χ) (hv : ShrinkingSupports v x₀)
    (hS : Tendsto S atTop atTop) (hD : Tendsto D atTop atTop) (i k : Fin 2) :
    SupportLimit v (fun j x =>
      coordPartial (coordPartial (coordPartial (coordPartial (tiltedWeight (B j) (S j) χ) k) k) i) i x /
        (S j*(D j)^2)) 0 := by
  have hd : Tendsto (fun j => (D j)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hD
  have hx := (hv.continuousAt
    (smooth_partial (smooth_partial (smooth_partial (smooth_partial hχ k) k) i) i).continuous.continuousAt).neg
  have h := hx.mul ((SupportLimit.of_seq hd).pow 2)
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero] at h
  apply h.congr_eventually
  filter_upwards [hS.eventually (eventually_gt_atTop 0)] with j hj x _
  rw [partial4_tiltedWeight _ _ hχ]
  field_simp

lemma coordinateGradient_apply (χ : Plane → ℝ) (x : Plane) (i : Fin 2) :
    coordinateGradient χ x i = coordPartial χ i x := rfl

open Filter in
lemma normalized_small_potential {p v : ℕ → Plane → ℝ} {K D : ℕ → ℝ} {C : ℝ}
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hp : ∀ᶠ j in atTop, ∀ x ∈ tsupport (v j), |p j x|≤C) :
    SupportLimit v (fun j x => (K j)^2*p j x/(D j)^2) 0 := by
  have hr : Tendsto (fun j => (K j/D j)^2*C) atTop (𝓝 0) := by
    simpa using (hK.pow 2).mul_const C
  apply SupportLimit.zero_of_bound hr
  filter_upwards [hp] with j hj x hx
  rw [mul_div_right_comm, abs_mul, abs_div, abs_pow, abs_pow, sq_abs, sq_abs]
  rw [div_pow] at *
  exact mul_le_mul_of_nonneg_left (hj x hx) (div_nonneg (sq_nonneg _) (sq_nonneg _))

open Filter in
lemma normalized_potential_gradient_limit {T p v : ℕ → Plane → ℝ} {S D K : ℕ → ℝ}
    (a : Fin 2 → ℝ)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x/D j) (a i))
    (hp : ∀ i, SupportLimit v (fun j x => (K j)^2*coordPartial (p j) i x/(S j*D j)) 0)
    (i : Fin 2) :
    SupportLimit v (fun j x => (K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/
      (S j*(D j)^2)) 0 := by
  have h := (hp i).mul (hgrad i)
  simp only [zero_mul] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext j x
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

open Filter in

theorem no_tilted_quasimodes {p v : ℕ → Plane → ℝ} {χ : Plane → ℝ}
    {B : ℕ → Plane} {S D K : ℕ → ℝ} {b : Plane} {d Cp : ℝ} {x₀ : Plane}
    (hχ : Smooth χ) (hp : ∀ j, Smooth (p j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hshr : ShrinkingSupports v x₀)
    (hS : Tendsto S atTop atTop) (hD : ∀ j, S j≤D j)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ᶠ j in atTop, ∀ x ∈ tsupport (v j), |p j x|≤Cp)
    (hpgrad : ∀ i, SupportLimit v (fun j x => (K j)^2*coordPartial (p j) i x/(S j*D j)) 0)
    (htrace : euclideanLaplacian χ x₀<0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0)
    (hzero : Tendsto (fun j => l2sq (fun x =>
      plusPart (fun x => gradientSquared (tiltedWeight (B j) (S j) χ) x+(K j)^2*p j x) (v j) x+
      skewPart (tiltedWeight (B j) (S j) χ) (v j) x)/(S j*(D j)^2)) atTop (𝓝 0)) : False := by
  let a : Fin 2 → ℝ := fun i => -b i-d*coordPartial χ i x₀
  let H : Fin 2 → Fin 2 → ℝ := fun i k => -coordPartial (coordPartial χ k) i x₀
  have ha' : (a 0)^2+(a 1)^2 ≠ 0 := by
    intro hz
    have h₀ : a 0=0 := by nlinarith [sq_nonneg (a 1)]
    have h₁ : a 1=0 := by nlinarith [sq_nonneg (a 0)]
    apply ha
    ext i
    dsimp [a] at h₀ h₁
    fin_cases i
    · change b 0+d*coordPartial χ 0 x₀=0
      linarith
    · change b 1+d*coordPartial χ 1 x₀=0
      linarith
  have hsym : H 0 1=H 1 0 := by dsimp [H]; rw [partial_partial hχ]
  have ht : 0<H 0 0+H 1 1 := by
    dsimp [euclideanLaplacian] at htrace
    simp only [Fin.sum_univ_two] at htrace
    dsimp [H]
    linarith
  have hdinf : Tendsto D atTop atTop := tendsto_atTop_mono hD hS
  have hg (i : Fin 2) := tilted_gradient_limit hχ hshr hb hd i
  exact no_asymptotic_quasimodes a H ha' hsym ht
    (fun j => smooth_tiltedWeight _ _ hχ) hp hv hcv hv1 hD hS hg
    (fun i k => tilted_hessian_limit hχ hshr hS i k)
    (fun i k => tilted_bilaplacian_limit hχ hshr hS hdinf i k)
    (normalized_potential_gradient_limit a hg hpgrad)
    (normalized_small_potential hK hpbound) hzero

lemma skew_const_mul {v : Plane → ℝ} (hv : Smooth v) (T : Plane → ℝ) (c : ℝ) :
    skewPart T (fun x => c*v x) = fun x => c*skewPart T v x := by
  ext x
  unfold skewPart
  simp only [partial_const_mul hv, Fin.sum_univ_two]
  ring

lemma conjugatedOperator_const_mul {v : Plane → ℝ} (hv : Smooth v)
    (T p : Plane → ℝ) (K c : ℝ) :
    conjugatedOperator T p K (fun x => c*v x) = fun x => c*conjugatedOperator T p K v x := by
  ext x
  simp only [conjugatedOperator, plusPart, laplacian_const_mul hv, skew_const_mul hv]
  ring

open Filter in
lemma ShrinkingSupports.of_ball {v : ℕ → Plane → ℝ} {r : ℕ → ℝ} {x₀ : Plane}
    (hr : Tendsto r atTop (𝓝 0)) (hv : ∀ j, tsupport (v j) ⊆ Metric.ball x₀ (r j)) :
    ShrinkingSupports v x₀ := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  apply (eventually_support_iff v (fun _ x => dist x x₀<ε)).mpr
  filter_upwards [hr.eventually_lt_const hε] with j hj x hx
  exact (hv j hx).trans hj

open Filter in

theorem local_carleman_conjugated {p : ℕ → Plane → ℝ} {χ : Plane → ℝ}
    {B : ℕ → Plane} {S D K e : ℕ → ℝ} {b : Plane} {d Cp r₀ : ℝ} {x₀ : Plane}
    (hχ : Smooth χ) (hp : ∀ j, Smooth (p j)) (hr₀ : 0 < r₀)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop) (hD : ∀ j, S j≤D j)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x ∈ Metric.ball x₀ r₀ → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x ∈ Metric.ball x₀ r₀ →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (htrace : euclideanLaplacian χ x₀<0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ, 0 < c ∧ ∃ j₀ : ℕ, ∀ j≥j₀, ∀ v : Plane → ℝ,
      Smooth v → HasCompactSupport v → tsupport v ⊆ Metric.ball x₀ r →
      c*S j*(D j)^2*l2sq v ≤ l2sq (conjugatedOperator (tiltedWeight (B j) (S j) χ) (p j) (K j) v) := by
  by_contra hn
  push Not at hn
  have hf (n : ℕ) : ∃ j : ℕ, n≤j ∧ ∃ v : Plane → ℝ,
      Smooth v ∧ HasCompactSupport v ∧ tsupport v ⊆ Metric.ball x₀ (min r₀ (1/((n : ℝ)+1))) ∧
      l2sq (conjugatedOperator (tiltedWeight (B j) (S j) χ) (p j) (K j) v) <
        (1/((n : ℝ)+1))*S j*(D j)^2*l2sq v :=
    hn _ (lt_min hr₀ (by positivity)) _ (by positivity) n
  choose j hj v hv hcv hsup hsmall using hf
  have hjinf : Tendsto j atTop atTop := tendsto_atTop_mono hj tendsto_id
  have hvne (n : ℕ) : v n ≠ 0 := by
    intro hz
    have hl2 : l2sq (v n)=0 := by rw [hz]; simp [l2sq]
    have hh := hsmall n
    rw [hl2, mul_zero] at hh
    exact (not_lt_of_ge (l2sq_nonneg _)) hh
  let w : ℕ → Plane → ℝ := fun n x => (l2norm (v n))⁻¹*v n x
  have hw (n : ℕ) : Smooth (w n) := contDiff_const.mul (hv n)
  have hcw (n : ℕ) : HasCompactSupport (w n) := (hcv n).mul_left
  have hw1 (n : ℕ) : l2sq (w n)=1 := normalize_l2sq (hv n) (hcv n) (hvne n)
  have hsupp (n : ℕ) : tsupport (w n) ⊆ tsupport (v n) := tsupport_mul_subset_right
  have hball (n : ℕ) : tsupport (w n) ⊆ Metric.ball x₀ (1/((n : ℝ)+1)) :=
    (hsupp n).trans ((hsup n).trans (Metric.ball_subset_ball (min_le_right _ _)))
  have hball₀ (n : ℕ) : tsupport (w n) ⊆ Metric.ball x₀ r₀ :=
    (hsupp n).trans ((hsup n).trans (Metric.ball_subset_ball (min_le_left _ _)))
  have hshr : ShrinkingSupports w x₀ := ShrinkingSupports.of_ball
    tendsto_one_div_add_atTop_nhds_zero_nat hball
  have hpb : ∀ᶠ n in atTop, ∀ x ∈ tsupport (w n), |p (j n) x|≤Cp :=
    Eventually.of_forall fun n x hx => hpbound _ _ (hball₀ n hx)
  have hpg (i : Fin 2) : SupportLimit w (fun n x =>
      (K (j n))^2*coordPartial (p (j n)) i x/(S (j n)*D (j n))) 0 := by
    apply SupportLimit.zero_of_bound (he.comp hjinf)
    exact Eventually.of_forall fun n x hx => hpgrad _ _ _ (hball₀ n hx)
  have hres (n : ℕ) : l2sq (conjugatedOperator (tiltedWeight (B (j n)) (S (j n)) χ)
      (p (j n)) (K (j n)) (w n))/(S (j n)*(D (j n))^2) < 1/((n : ℝ)+1) := by
    have hdpos := (hSpos (j n)).trans_le (hD (j n))
    have hden := mul_pos (hSpos (j n)) (sq_pos_of_pos hdpos)
    have hlpos : 0<l2norm (v n) := Real.sqrt_pos.mpr (l2sq_pos (hv n) (hcv n) (hvne n))
    apply (div_lt_iff₀ hden).mpr
    dsimp [w]
    rw [conjugatedOperator_const_mul (hv n), l2sq_const_mul]
    have hh := mul_lt_mul_of_pos_left (hsmall n) (sq_pos_of_pos (inv_pos.mpr hlpos))
    have hnrm : (l2norm (v n))⁻¹^2*l2sq (v n)=1 := by
      simpa only [w, l2sq_const_mul] using hw1 n
    calc
      _ < (l2norm (v n))⁻¹^2*((1/((n : ℝ)+1))*S (j n)*(D (j n))^2*l2sq (v n)) := hh
      _ = (1/((n : ℝ)+1))*(S (j n)*(D (j n))^2) := by
        calc
          _ = ((1/((n : ℝ)+1))*(S (j n)*(D (j n))^2))*((l2norm (v n))⁻¹^2*l2sq (v n)) := by ring
          _ = _ := by rw [hnrm, mul_one]
  have hzero : Tendsto (fun n => l2sq (conjugatedOperator (tiltedWeight (B (j n)) (S (j n)) χ)
      (p (j n)) (K (j n)) (w n))/(S (j n)*(D (j n))^2)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (l2sq_nonneg _)
      (mul_nonneg (hSpos _).le (sq_nonneg _)))
      (Eventually.of_forall fun n => (hres n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact no_tilted_quasimodes hχ (fun n => hp (j n)) hw hcw hw1 hshr
    (hS.comp hjinf) (fun n => hD (j n)) (hb.comp hjinf) (hd.comp hjinf) (hK.comp hjinf)
    hpb hpg htrace ha hzero

open Filter in

theorem local_carleman {p : ℕ → Plane → ℝ} {χ : Plane → ℝ}
    {B : ℕ → Plane} {S D K e : ℕ → ℝ} {b : Plane} {d Cp r₀ : ℝ} {x₀ : Plane}
    (hχ : Smooth χ) (hp : ∀ j, Smooth (p j)) (hr₀ : 0 < r₀)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop) (hD : ∀ j, S j≤D j)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x ∈ Metric.ball x₀ r₀ → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x ∈ Metric.ball x₀ r₀ →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (htrace : euclideanLaplacian χ x₀<0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ, 0 < c ∧ ∃ j₀ : ℕ, ∀ j≥j₀, ∀ w : Plane → ℝ,
      Smooth w → HasCompactSupport w → tsupport w ⊆ Metric.ball x₀ r →
      c*Real.sqrt (S j)*D j*l2norm (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*w x) ≤
        l2norm (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*
          (euclideanLaplacian w x+(K j)^2*p j x*w x)) := by
  obtain ⟨r, hr, c, hc, j₀, h⟩ := local_carleman_conjugated hχ hp hr₀ hSpos hS hD hb hd hK
    hpbound he hpgrad htrace ha
  refine ⟨r, hr, Real.sqrt c, Real.sqrt_pos.mpr hc, j₀, ?_⟩
  intro j hj w hw hcw hsupp
  have hT := smooth_tiltedWeight (B j) (S j) hχ
  have hv := hT.exp.mul hw
  have hcv : HasCompactSupport (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*w x) := hcw.mul_left
  have hsupv : tsupport (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*w x) ⊆ Metric.ball x₀ r :=
    tsupport_mul_subset_right.trans hsupp
  have hineq := h j hj _ hv hcv hsupv
  have hconj : conjugatedOperator (tiltedWeight (B j) (S j) χ) (p j) (K j)
      (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*w x) =
      (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*(euclideanLaplacian w x+(K j)^2*p j x*w x)) :=
    funext (conjugation hT hw (p j) (K j))
  rw [hconj] at hineq
  have hh := Real.sqrt_le_sqrt hineq
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hc.le (hSpos j).le) (sq_nonneg _)),
    Real.sqrt_mul (mul_nonneg hc.le (hSpos j).le), Real.sqrt_mul hc.le,
    Real.sqrt_sq ((hSpos j).le.trans (hD j))] at hh
  exact hh


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Cutoffs
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma gradient_eq_of_eventuallyEq {f g : Plane → ℝ} {x : Plane}
    (h : f =ᶠ[𝓝 x] g) : coordinateGradient f x = coordinateGradient g x := by
  ext i
  exact (partial_eventuallyEq h i).eq_of_nhds

lemma young_pairing {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    -2*(∫ x, f x*g x) ≤ (1/2 : ℝ)*l2sq f+2*l2sq g := by
  have h := l2sq_add (g := fun x => 2*g x) hf (contDiff_const.mul hg) hcf hcg.mul_left
  have hi : (∫ x, f x*(2*g x))=2*(∫ x, f x*g x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [l2sq_const_mul, hi] at h
  linarith only [l2sq_nonneg (fun x => f x+2*g x), h]

lemma weighted_energy_component {η U : Plane → ℝ} (hη : Smooth η) (hU : Smooth U)
    (hc : HasCompactSupport η) (i : Fin 2) :
    l2sq (fun x => η x*coordPartial U i x) =
      -(∫ x, coordPartial (coordPartial U i) i x*(η x*η x*U x))-
      2*(∫ x, (η x*coordPartial U i x)*(coordPartial η i x*U x)) := by
  have h := integral_mul_partial (smooth_partial hU i) ((hη.mul hη).mul hU)
    hc.mul_right.mul_right i
  have hi₁ := integrable_mul_compact_left (hη.mul (smooth_partial hU i))
    (hη.mul (smooth_partial hU i)) hc.mul_right
  have hi₂ := integrable_mul_compact_left (hη.mul (smooth_partial hU i))
    ((smooth_partial hη i).mul hU) hc.mul_right
  have heq : (∫ x, coordPartial U i x*coordPartial (fun y => η y*η y*U y) i x) =
      l2sq (fun x => η x*coordPartial U i x)+
      2*(∫ x, (η x*coordPartial U i x)*(coordPartial η i x*U x)) := by
    calc
      _ = ∫ x, (η x*coordPartial U i x)*(η x*coordPartial U i x)+
          2*((η x*coordPartial U i x)*(coordPartial η i x*U x)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [partial_mul (hη.mul hη) hU, partial_mul hη hη]
        ring
      _ = _ := by rw [integral_add hi₁ (hi₂.const_mul 2), integral_const_mul]; rfl
  linarith only [h, heq]

lemma weighted_energy_identity {η U : Plane → ℝ} (hη : Smooth η) (hU : Smooth U)
    (hc : HasCompactSupport η) :
    (∑ i : Fin 2, l2sq (fun x => η x*coordPartial U i x)) =
      -(∫ x, euclideanLaplacian U x*(η x*η x*U x))-
      2*(∑ i : Fin 2, ∫ x, (η x*coordPartial U i x)*(coordPartial η i x*U x)) := by
  rw [show (∫ x, euclideanLaplacian U x*(η x*η x*U x)) =
      ∑ i : Fin 2, ∫ x, coordPartial (coordPartial U i) i x*(η x*η x*U x) from
    integral_sum_mul Finset.univ (fun i _ => smooth_partial (smooth_partial hU i) i)
      ((hη.mul hη).mul hU) hc.mul_right.mul_right]
  simp only [Fin.sum_univ_two, weighted_energy_component hη hU hc]
  ring

theorem caccioppoli {η U p : Plane → ℝ} {K Cp : ℝ}
    (hη : Smooth η) (hU : Smooth U) (hp : Smooth p) (hc : HasCompactSupport η)
    (hCp : 0≤Cp) (hpb : ∀ x ∈ tsupport η, |p x|≤Cp)
    (hPDE : ∀ x ∈ tsupport η, euclideanLaplacian U x+K^2*p x*U x=0) :
    (∑ i : Fin 2, l2sq (fun x => η x*coordPartial U i x)) ≤
      2*K^2*Cp*l2sq (fun x => η x*U x)+
      4*(∑ i : Fin 2, l2sq (fun x => coordPartial η i x*U x)) := by
  have hE := weighted_energy_identity hη hU hc
  have hI : (∫ x, euclideanLaplacian U x*(η x*η x*U x)) =
      -K^2*(∫ x, p x*((η x*U x)*(η x*U x))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport η
    · have hh := hPDE x hx
      calc
        _ = (-K^2*p x*U x)*(η x*η x*U x) := by congr 1; linarith only [hh]
        _ = _ := by ring
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]
  rw [hI] at hE
  have hpI := integral_coefficient_square_abs_le hp (hη.mul hU) hc.mul_right hCp
    (fun x hx => hpb x (tsupport_mul_subset_left hx))
  have hpI' : (∫ x, p x*((η x*U x)*(η x*U x))) ≤ Cp*l2sq (fun x => η x*U x) :=
    (le_abs_self _).trans hpI
  have hY (i : Fin 2) := young_pairing (hη.mul (smooth_partial hU i))
    ((smooth_partial hη i).mul hU) hc.mul_right (compact_partial hc i).mul_right
  have hYsum := add_le_add (hY 0) (hY 1)
  simp only [Fin.sum_univ_two] at hE ⊢
  nlinarith only [hE, hYsum, mul_le_mul_of_nonneg_left hpI' (sq_nonneg K)]

lemma l2sq_cutoff_comparison {a φ F : Plane → ℝ} {C : ℝ}
    (ha : Smooth a) (hφ : Smooth φ) (hF : Smooth F) (hcφ : HasCompactSupport φ)
    (hC : 0≤C) (haC : ∀ x, |a x|≤C) (hφ1 : ∀ x ∈ tsupport a, φ x=1) :
    l2sq (fun x => a x*F x) ≤ C ^ 2*l2sq (fun x => φ x*F x) := by
  have heq : (fun x => a x*F x)=(fun x => a x*(φ x*F x)) := by
    funext x
    by_cases hx : a x=0
    · simp only [hx, zero_mul]
    · rw [hφ1 x (subset_closure hx), one_mul]
  rw [heq]
  exact l2sq_coefficient_mul_le ha (hφ.mul hF) hcφ.mul_right hC (fun x _ => haC x)

theorem exponential_caccioppoli {θ φ T U p : Plane → ℝ} {K Cp Cθ Ct : ℝ}
    (hθ : Smooth θ) (hφ : Smooth φ) (hT : Smooth T) (hU : Smooth U) (hp : Smooth p)
    (hcθ : HasCompactSupport θ) (hcφ : HasCompactSupport φ)
    (hφ1 : ∀ x ∈ tsupport θ, φ x=1)
    (hCp : 0≤Cp) (hCθ : 0≤Cθ) (hCt : 0≤Ct)
    (hθb : ∀ x, |θ x|≤Cθ) (hθg : ∀ i x, |coordPartial θ i x|≤Cθ)
    (hTb : ∀ i x, x ∈ tsupport θ → |coordPartial T i x|≤Ct)
    (hpb : ∀ x ∈ tsupport θ, |p x|≤Cp)
    (hPDE : ∀ x ∈ tsupport θ, euclideanLaplacian U x+K^2*p x*U x=0) :
    (∑ i : Fin 2, l2sq (fun x => (Real.exp (T x)*θ x)*coordPartial U i x)) ≤
      (2*K^2*Cp*Cθ^2+16*Cθ^2+16*Ct^2*Cθ^2)*
        l2sq (fun x => φ x*(Real.exp (T x)*U x)) := by
  let η : Plane → ℝ := fun x => Real.exp (T x)*θ x
  let M := l2sq (fun x => φ x*(Real.exp (T x)*U x))
  have hη : Smooth η := hT.exp.mul hθ
  have hcη : HasCompactSupport η := hcθ.mul_left
  have hsupη : tsupport η ⊆ tsupport θ := tsupport_mul_subset_right
  have hηbound : l2sq (fun x => η x*U x) ≤ Cθ^2*M := by
    have hh := l2sq_cutoff_comparison hθ hφ (hT.exp.mul hU) hcφ hCθ hθb hφ1
    simpa only [η, M, mul_left_comm, mul_assoc, mul_comm] using hh
  have hpartbound (i : Fin 2) : l2sq (fun x => coordPartial η i x*U x) ≤
      (2*Cθ^2+2*Ct^2*Cθ^2)*M := by
    have heq : (fun x => coordPartial η i x*U x)=
        (fun x => coordPartial θ i x*(Real.exp (T x)*U x)+coordPartial T i x*(η x*U x)) := by
      funext x
      dsimp [η]
      rw [partial_exp_mul hT hθ]
      ring
    rw [heq]
    have hsum := l2sq_add_le ((smooth_partial hθ i).mul (hT.exp.mul hU))
      ((smooth_partial hT i).mul (hη.mul hU)) (compact_partial hcθ i).mul_right hcη.mul_right.mul_left
    have hfirst := l2sq_cutoff_comparison (smooth_partial hθ i) hφ (hT.exp.mul hU) hcφ hCθ
      (hθg i) (fun x hx => hφ1 x (partial_tsupport_subset θ i hx))
    have hsecond := l2sq_coefficient_mul_le (smooth_partial hT i) (hη.mul hU) hcη.mul_right hCt
      (fun x hx => hTb i x (hsupη (tsupport_mul_subset_left hx)))
    have hh := mul_le_mul_of_nonneg_left hηbound (sq_nonneg Ct)
    dsimp [M] at hηbound ⊢
    nlinarith only [hsum, hfirst, hsecond, hh]
  have hbasic := caccioppoli hη hU hp hcη hCp
    (fun x hx => hpb x (hsupη hx)) (fun x hx => hPDE x (hsupη hx))
  have hpotential := mul_le_mul_of_nonneg_left hηbound
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ)≤2) (sq_nonneg K)) hCp)
  have h₀ := hpartbound 0
  have h₁ := hpartbound 1
  simp only [Fin.sum_univ_two] at hbasic ⊢
  dsimp [η] at hbasic
  dsimp [M] at hpotential h₀ h₁
  nlinarith only [hbasic, hpotential, h₀, h₁]

lemma partial2_mul {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (i : Fin 2) (x : Plane) :
    coordPartial (coordPartial (fun y => f y*g y) i) i x =
      coordPartial (coordPartial f i) i x*g x+2*coordPartial f i x*coordPartial g i x+
      f x*coordPartial (coordPartial g i) i x := by
  rw [show coordPartial (fun y => f y*g y) i =
      (fun y => coordPartial f i y*g y+f y*coordPartial g i y) from funext (partial_mul hf hg i)]
  rw [partial_add ((smooth_partial hf i).mul hg) (hf.mul (smooth_partial hg i)),
    partial_mul (smooth_partial hf i) hg, partial_mul hf (smooth_partial hg i)]
  ring

lemma laplacian_mul {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g) (x : Plane) :
    euclideanLaplacian (fun y => f y*g y) x =
      euclideanLaplacian f x*g x+2*(∑ i : Fin 2, coordPartial f i x*coordPartial g i x)+
      f x*euclideanLaplacian g x := by
  simp only [euclideanLaplacian, Fin.sum_univ_two, partial2_mul hf hg]
  ring

lemma cutoff_residual {ζ U p : Plane → ℝ} {K : ℝ} (hζ : Smooth ζ) (hU : Smooth U)
    (hPDE : ∀ x ∈ tsupport ζ, euclideanLaplacian U x+K^2*p x*U x=0) (x : Plane) :
    euclideanLaplacian (fun y => ζ y*U y) x+K^2*p x*(ζ x*U x) =
      euclideanLaplacian ζ x*U x+2*(∑ i : Fin 2, coordPartial ζ i x*coordPartial U i x) := by
  rw [laplacian_mul hζ hU]
  have hz : ζ x*(euclideanLaplacian U x+K^2*p x*U x)=0 := by
    by_cases hx : x ∈ tsupport ζ
    · rw [hPDE x hx, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  nlinarith only [hz]

lemma weighted_cutoff_residual {ζ θ φ T U p : Plane → ℝ} {K Cp Cζ Cθ Ct : ℝ}
    (hζ : Smooth ζ) (hθ : Smooth θ) (hφ : Smooth φ) (hT : Smooth T) (hU : Smooth U)
    (hp : Smooth p) (hcζ : HasCompactSupport ζ) (hcθ : HasCompactSupport θ)
    (hcφ : HasCompactSupport φ)
    (hθ1 : ∀ i x, x ∈ tsupport (coordPartial ζ i) → θ x=1)
    (hφ1 : ∀ x ∈ tsupport θ, φ x=1)
    (hφlap : ∀ x ∈ tsupport (euclideanLaplacian ζ), φ x=1)
    (hCp : 0≤Cp) (hCζ : 0≤Cζ) (hCθ : 0≤Cθ) (hCt : 0≤Ct)
    (hζlap : ∀ x, |euclideanLaplacian ζ x|≤Cζ)
    (hζg : ∀ i x, |coordPartial ζ i x|≤Cζ)
    (hθb : ∀ x, |θ x|≤Cθ) (hθg : ∀ i x, |coordPartial θ i x|≤Cθ)
    (hTb : ∀ i x, x ∈ tsupport θ → |coordPartial T i x|≤Ct)
    (hpb : ∀ x ∈ tsupport θ, |p x|≤Cp)
    (hPDEζ : ∀ x ∈ tsupport ζ, euclideanLaplacian U x+K^2*p x*U x=0)
    (hPDEθ : ∀ x ∈ tsupport θ, euclideanLaplacian U x+K^2*p x*U x=0) :
    l2sq (fun x => Real.exp (T x)*(euclideanLaplacian (fun y => ζ y*U y) x+
      K^2*p x*(ζ x*U x))) ≤
      Cζ^2*(2+16*(2*K^2*Cp*Cθ^2+16*Cθ^2+16*Ct^2*Cθ^2))*
        l2sq (fun x => φ x*(Real.exp (T x)*U x)) := by
  let a : Plane → ℝ := fun x => euclideanLaplacian ζ x*(Real.exp (T x)*U x)
  let b : Fin 2 → Plane → ℝ := fun i x => coordPartial ζ i x*(Real.exp (T x)*coordPartial U i x)
  let M := l2sq (fun x => φ x*(Real.exp (T x)*U x))
  have ha : Smooth a := (smooth_laplacian hζ).mul (hT.exp.mul hU)
  have hb (i : Fin 2) : Smooth (b i) := (smooth_partial hζ i).mul (hT.exp.mul (smooth_partial hU i))
  have hca : HasCompactSupport a := (compact_laplacian hcζ).mul_right
  have hcb (i : Fin 2) : HasCompactSupport (b i) := (compact_partial hcζ i).mul_right
  have heq : (fun x => Real.exp (T x)*(euclideanLaplacian (fun y => ζ y*U y) x+
      K^2*p x*(ζ x*U x)))=(fun x => a x+2*(b 0 x+b 1 x)) := by
    funext x
    rw [cutoff_residual hζ hU hPDEζ, Fin.sum_univ_two]
    dsimp [a, b]; ring
  rw [heq]
  have hsum := l2sq_add_le (g := fun x => 2*(b 0 x+b 1 x)) ha (contDiff_const.mul ((hb 0).add (hb 1))) hca
    ((hcb 0).add (hcb 1)).mul_left
  rw [l2sq_const_mul] at hsum
  have hsum' := l2sq_add_le (hb 0) (hb 1) (hcb 0) (hcb 1)
  have haM : l2sq a≤Cζ^2*M :=
    l2sq_cutoff_comparison (smooth_laplacian hζ) hφ (hT.exp.mul hU) hcφ hCζ hζlap hφlap
  have hbM (i : Fin 2) : l2sq (b i)≤Cζ^2*l2sq (fun x => (Real.exp (T x)*θ x)*coordPartial U i x) := by
    have hh := l2sq_cutoff_comparison (smooth_partial hζ i) hθ
      (hT.exp.mul (smooth_partial hU i)) hcθ hCζ (hζg i) (hθ1 i)
    simpa only [b, mul_left_comm, mul_assoc, mul_comm] using hh
  have hcac := exponential_caccioppoli hθ hφ hT hU hp hcθ hcφ hφ1 hCp hCθ hCt
    hθb hθg hTb hpb hPDEθ
  have hh := mul_le_mul_of_nonneg_left hcac (sq_nonneg Cζ)
  have hb0 := hbM 0
  have hb1 := hbM 1
  simp only [Fin.sum_univ_two] at hh
  dsimp [M] at haM
  nlinarith only [hsum, hsum', haM, hb0, hb1, hh]

lemma cutoff_prefactor_bound {K D Cp Cζ Cθ Ct : ℝ}
    (hD : 1≤D) (hK : K^2≤D^2) (hCp : 0≤Cp) :
    Cζ^2*(2+16*(2*K^2*Cp*Cθ^2+16*Cθ^2+16*(Ct*D)^2*Cθ^2)) ≤
      (Cζ^2*(2+16*(2*Cp*Cθ^2+16*Cθ^2+16*Ct^2*Cθ^2)))*D^2 := by
  have hDsq : 1≤D^2 := by nlinarith only [hD]
  have h1 := mul_le_mul_of_nonneg_right hK
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ)≤2) hCp) (sq_nonneg Cθ))
  have h2 := mul_le_mul_of_nonneg_left hDsq (sq_nonneg Cθ)
  apply (mul_le_mul_of_nonneg_left (show
    2+16*(2*K^2*Cp*Cθ^2+16*Cθ^2+16*(Ct*D)^2*Cθ^2) ≤
    (2+16*(2*Cp*Cθ^2+16*Cθ^2+16*Ct^2*Cθ^2))*D^2 from by
      nlinarith only [h1, h2, hDsq]) (sq_nonneg Cζ)).trans_eq
  ring

lemma cancel_carleman_frequency {S D c C : ℝ} {f g : Plane → ℝ}
    (hS : 0≤S) (hD : 0<D) (hc : 0 < c)
    (hcar : c*Real.sqrt S*D*l2norm f≤l2norm g)
    (herror : l2sq g≤C*D^2) : S*l2sq f≤C/c^2 := by
  have hleft : 0 ≤ c*Real.sqrt S*D*l2norm f := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hc.le (Real.sqrt_nonneg _)) hD.le)
      (Real.sqrt_nonneg _)
  have hsq := (sq_le_sq₀ hleft (Real.sqrt_nonneg _)).mpr hcar
  have heq : (c*Real.sqrt S*D*l2norm f)^2=c^2*S*D^2*l2sq f := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hS, l2norm_sq]
  change (c*Real.sqrt S*D*l2norm f)^2 ≤ (l2norm g)^2 at hsq
  rw [heq, l2norm_sq] at hsq
  have hh : (c^2*(S*l2sq f))*D^2≤C*D^2 := by nlinarith only [hsq, herror]
  have hh' := (mul_le_mul_iff_left₀ (sq_pos_of_pos hD)).mp hh
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  nlinarith only [hh']

end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_MassComparison
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

namespace SharpNodal
namespace Profiles
open Carleman

lemma tsupport_subset_compl_of_zero {f : Plane → ℝ} {G : Set Plane}
    (hG : IsOpen G) (hf : ∀ x ∈ G, f x = 0) : tsupport f ⊆ Gᶜ := by
  apply closure_minimal _ hG.isClosed_compl
  intro x hx h
  exact hx (hf x h)

lemma partial_tsupport_outside {f : Plane → ℝ} {x₀ : Plane} {r c : ℝ}
    (hf : ∀ x ∈ Metric.ball x₀ r, f x=c) (i : Fin 2) :
    tsupport (coordPartial f i) ⊆ (Metric.ball x₀ r)ᶜ := by
  apply tsupport_subset_compl_of_zero Metric.isOpen_ball
  intro x hx
  have he : f =ᶠ[𝓝 x] (fun _ => c) :=
    Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hx) fun y hy => hf y hy
  rw [(partial_eventuallyEq he i).eq_of_nhds, partial_const]

lemma laplacian_const (c : ℝ) (x : Plane) : euclideanLaplacian (fun _ => c) x=0 := by
  unfold euclideanLaplacian
  apply Finset.sum_eq_zero
  intro i _
  have h : coordPartial (fun _ => c) i=(fun _ => 0) := funext (partial_const c i)
  rw [h, partial_const]

lemma laplacian_tsupport_outside {f : Plane → ℝ} {x₀ : Plane} {r c : ℝ}
    (hf : ∀ x ∈ Metric.ball x₀ r, f x=c) :
    tsupport (euclideanLaplacian f) ⊆ (Metric.ball x₀ r)ᶜ := by
  apply tsupport_subset_compl_of_zero Metric.isOpen_ball
  intro x hx
  have he : f =ᶠ[𝓝 x] (fun _ => c) :=
    Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hx) fun y hy => hf y hy
  rw [(laplacian_eventuallyEq he).eq_of_nhds]
  exact laplacian_const _ _

lemma laplacian_tsupport_subset (f : Plane → ℝ) :
    tsupport (euclideanLaplacian f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have he : f =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hn
  apply hx
  rw [(laplacian_eventuallyEq he).eq_of_nhds]
  exact laplacian_const _ _

lemma annular_cutoff_support {x₀ : Plane} (a b : ContDiffBump x₀) :
    tsupport (fun x => a x * (1-b x)) ⊆
      Metric.closedBall x₀ a.rOut ∩ (Metric.ball x₀ b.rIn)ᶜ := by
  apply Set.subset_inter
  · exact tsupport_mul_subset_left.trans (by rw [a.tsupport_eq])
  · apply tsupport_subset_compl_of_zero Metric.isOpen_ball
    intro x hx
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)]
    ring

lemma annular_cutoff_one {x₀ x : Plane} (a b : ContDiffBump x₀)
    (ha : dist x x₀ ≤ a.rIn) (hb : b.rOut ≤ dist x x₀) : a x * (1-b x)=1 := by
  rw [a.one_of_mem_closedBall ha, b.zero_of_le_dist hb]
  norm_num

lemma annular_cutoff_bounds {x₀ : Plane} (a b : ContDiffBump x₀) (x : Plane) :
    0 ≤ a x*(1-b x) ∧ a x*(1-b x) ≤ 1 := by
  constructor
  · exact mul_nonneg a.nonneg (sub_nonneg.mpr b.le_one)
  · exact (mul_le_mul_of_nonneg_left (sub_le_self _ b.nonneg) a.nonneg).trans (by simpa using a.le_one (x:=x))

theorem exists_profile_cutoffs {x₀ : Plane} {r : ℝ} (hr : 0 < r) :
    ∃ (ζ θ φ : Plane → ℝ) (ρ : ℝ), 0<ρ ∧
      Smooth ζ ∧ Smooth θ ∧ Smooth φ ∧
      HasCompactSupport ζ ∧ HasCompactSupport θ ∧ HasCompactSupport φ ∧
      tsupport ζ ⊆ Metric.ball x₀ r ∧
      tsupport θ ⊆ Metric.ball x₀ r ∧
      tsupport φ ⊆ Metric.ball x₀ r ∧
      (∀ x ∈ Metric.ball x₀ ρ, ζ x=1) ∧
      (∀ x ∈ tsupport φ, x≠x₀) ∧
      (∀ x, 0≤φ x ∧ φ x≤1) ∧
      (∀ i x, x ∈ tsupport (coordPartial ζ i) → θ x=1) ∧
      (∀ x ∈ tsupport θ, φ x=1) ∧
      (∀ x ∈ tsupport (euclideanLaplacian ζ), φ x=1) := by
  let ζ : ContDiffBump x₀ := ⟨r/4, r/3, by positivity, by linarith⟩
  let θo : ContDiffBump x₀ := ⟨r/2, 2*r/3, by positivity, by linarith⟩
  let θi : ContDiffBump x₀ := ⟨r/8, r/4, by positivity, by linarith⟩
  let φo : ContDiffBump x₀ := ⟨3*r/4, 7*r/8, by positivity, by linarith⟩
  let φi : ContDiffBump x₀ := ⟨r/16, r/8, by positivity, by linarith⟩
  let θ : Plane → ℝ := fun x => θo x*(1-θi x)
  let φ : Plane → ℝ := fun x => φo x*(1-φi x)
  have hζ1 : ∀ x ∈ Metric.ball x₀ (r/4), ζ x=1 :=
    fun _ hx => ζ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  have hζsup : tsupport (ζ : Plane → ℝ) ⊆ Metric.closedBall x₀ (r/3) := by
    rw [ζ.tsupport_eq]
  have hθsup := annular_cutoff_support θo θi
  have hφsup := annular_cutoff_support φo φi
  refine ⟨ζ, θ, φ, r/4, by positivity, ζ.contDiff,
    θo.contDiff.mul (contDiff_const.sub θi.contDiff),
    φo.contDiff.mul (contDiff_const.sub φi.contDiff),
    ζ.hasCompactSupport, θo.hasCompactSupport.mul_right, φo.hasCompactSupport.mul_right,
    hζsup.trans (Metric.closedBall_subset_ball (by linarith)), ?_, ?_, hζ1, ?_,
    annular_cutoff_bounds φo φi, ?_, ?_, ?_⟩
  · exact (hθsup.trans Set.inter_subset_left).trans (Metric.closedBall_subset_ball (by dsimp [θo]; linarith))
  · exact (hφsup.trans Set.inter_subset_left).trans (Metric.closedBall_subset_ball (by dsimp [φo]; linarith))
  · intro x hx heq
    have hh := (hφsup hx).2
    rw [heq] at hh
    exact hh (Metric.mem_ball_self (by dsimp [φi]; positivity))
  · intro i x hx
    have hu := hζsup (partial_tsupport_subset (ζ : Plane → ℝ) i hx)
    have hl := partial_tsupport_outside hζ1 i hx
    apply annular_cutoff_one θo θi
    · dsimp [θo]; exact hu.trans (by linarith)
    · dsimp [θi]; exact le_of_not_gt hl
  · intro x hx
    obtain ⟨hu, hl⟩ := hθsup hx
    apply annular_cutoff_one φo φi
    · change dist x x₀ ≤ 3*r/4
      change dist x x₀ ≤ 2*r/3 at hu
      linarith
    · exact le_of_not_gt hl
  · intro x hx
    have hu := hζsup (laplacian_tsupport_subset _ hx)
    have hl := laplacian_tsupport_outside hζ1 hx
    apply annular_cutoff_one φo φi
    · dsimp [φo]; exact hu.trans (by linarith)
    · dsimp [φi]; have hh : r/4≤dist x x₀ := le_of_not_gt hl; linarith

lemma exists_abs_bound {f : Plane → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, |f x|≤C := by
  obtain ⟨C, hC⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hc.norm
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  exact (hC (Set.mem_range_self x)).trans (le_max_left _ _)

lemma exists_partial_abs_bound {f : Plane → ℝ} (hf : Smooth f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0≤C ∧ ∀ i x, |coordPartial f i x|≤C := by
  obtain ⟨C₀, h₀, hb₀⟩ := exists_abs_bound (smooth_partial hf 0).continuous (compact_partial hc 0)
  obtain ⟨C₁, h₁, hb₁⟩ := exists_abs_bound (smooth_partial hf 1).continuous (compact_partial hc 1)
  refine ⟨max C₀ C₁, h₀.trans (le_max_left _ _), fun i x => ?_⟩
  fin_cases i
  · exact (hb₀ x).trans (le_max_left _ _)
  · exact (hb₁ x).trans (le_max_right _ _)

lemma exists_partial_abs_bound_on {f : Plane → ℝ} {F : Set Plane}
    (hf : Smooth f) (hF : IsCompact F) :
    ∃ C : ℝ, 0≤C ∧ ∀ i x, x∈F → |coordPartial f i x|≤C := by
  obtain ⟨C₀, hb₀⟩ := hF.exists_bound_of_continuousOn (smooth_partial hf 0).continuous.continuousOn
  obtain ⟨C₁, hb₁⟩ := hF.exists_bound_of_continuousOn (smooth_partial hf 1).continuous.continuousOn
  refine ⟨max (max C₀ C₁) 0, le_max_right _ _, fun i x hx => ?_⟩
  fin_cases i
  · exact (hb₀ x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hb₁ x hx).trans ((le_max_right _ _).trans (le_max_left _ _))

lemma tilted_gradient_bound {χ : Plane → ℝ} {B : Plane} {S D C : ℝ} {F : Set Plane}
    (hχ : Smooth χ) (hS : 0≤S) (hSD : S≤D) (hBD : ‖B‖≤D) (_hC : 0≤C)
    (hχb : ∀ i x, x∈F → |coordPartial χ i x|≤C) :
    ∀ i x, x∈F → |coordPartial (tiltedWeight B S χ) i x|≤(1+C)*D := by
  intro i x hx
  rw [partial_tiltedWeight _ _ hχ]
  have hB : |B i|≤D := (PiLp.norm_apply_le B i).trans hBD
  calc
    |-B i-S*coordPartial χ i x| ≤ |-B i|+|S*coordPartial χ i x| := abs_sub _ _
    _ = |B i|+S*|coordPartial χ i x| := by rw [abs_neg, abs_mul, abs_of_nonneg hS]
    _ ≤ D+D*C := add_le_add hB (mul_le_mul hSD (hχb i x hx) (abs_nonneg _) (hS.trans hSD))
    _ = (1+C)*D := by ring

theorem cutoff_mass_comparison {p U : ℕ → Plane → ℝ} {χ : Plane → ℝ}
    {B : ℕ → Plane} {S D K e : ℕ → ℝ} {b : Plane} {d Cp r₀ : ℝ} {x₀ : Plane}
    (hχ : Smooth χ) (hp : ∀ j, Smooth (p j)) (hU : ∀ j, Smooth (U j)) (hr₀ : 0 < r₀)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hDdef : ∀ j, D j=S j+‖B j‖)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x ∈ Metric.ball x₀ r₀ → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x ∈ Metric.ball x₀ r₀ →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (hPDE : ∀ j x, x ∈ Metric.ball x₀ r₀ →
      euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (htrace : euclideanLaplacian χ x₀<0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0) :
    ∃ (ζ φ : Plane → ℝ) (ρ C : ℝ), 0<ρ ∧ 0<C ∧
      Smooth ζ ∧ Smooth φ ∧ HasCompactSupport ζ ∧ HasCompactSupport φ ∧
      tsupport ζ ⊆ Metric.ball x₀ r₀ ∧ tsupport φ ⊆ Metric.ball x₀ r₀ ∧
      (∀ x ∈ Metric.ball x₀ ρ, ζ x=1) ∧
      (∀ x ∈ tsupport φ, x≠x₀) ∧ (∀ x, 0≤φ x ∧ φ x≤1) ∧
      ∀ᶠ j in atTop,
        S j*l2sq (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*(ζ x*U j x)) ≤
        C*l2sq (fun x => φ x*(Real.exp (tiltedWeight (B j) (S j) χ x)*U j x)) := by
  have hD (j : ℕ) : S j≤D j := by rw [hDdef]; exact le_add_of_nonneg_right (norm_nonneg _)
  have hBD (j : ℕ) : ‖B j‖≤D j := by rw [hDdef]; exact le_add_of_nonneg_left (hSpos j).le
  have hDpos (j : ℕ) : 0<D j := (hSpos j).trans_le (hD j)
  obtain ⟨r, hr, c, hc, j₀, hcar⟩ := local_carleman hχ hp hr₀ hSpos hS hD hb hd hK hpbound he hpgrad htrace ha
  obtain ⟨ζ, θ, φ, ρ, hρ, hζ, hθ, hφ, hcζ, hcθ, hcφ, hζsup, hθsup, hφsup,
    hζ1, hφaway, hφb, hθ1, hφ1, hφlap⟩ := exists_profile_cutoffs (x₀:=x₀) (lt_min hr hr₀)
  obtain ⟨C₁, hC₁, hζlap⟩ := exists_abs_bound (smooth_laplacian hζ).continuous (compact_laplacian hcζ)
  obtain ⟨C₂, hC₂, hζg⟩ := exists_partial_abs_bound hζ hcζ
  obtain ⟨C₃, hC₃, hθb⟩ := exists_abs_bound hθ.continuous hcθ
  obtain ⟨C₄, hC₄, hθg⟩ := exists_partial_abs_bound hθ hcθ
  obtain ⟨Cχ, hCχ, hχb⟩ := exists_partial_abs_bound_on hχ hcθ
  let Cζ := max C₁ C₂
  let Cθ := max C₃ C₄
  let CP := max Cp 0
  let CT := 1+Cχ
  let P := Cζ^2*(2+16*(2*CP*Cθ^2+16*Cθ^2+16*CT^2*Cθ^2))
  have hCP : 0≤CP := le_max_right _ _
  have hP : 0≤P := by dsimp [P]; positivity
  have hCZ : 0≤Cζ := hC₁.trans (le_max_left _ _)
  have hCT : 0≤Cθ := hC₃.trans (le_max_left _ _)
  have hCt : 0≤CT := by dsimp [CT]; linarith
  have hζr : tsupport ζ ⊆ Metric.ball x₀ r := hζsup.trans (Metric.ball_subset_ball (min_le_left _ _))
  have hζr₀ : tsupport ζ ⊆ Metric.ball x₀ r₀ := hζsup.trans (Metric.ball_subset_ball (min_le_right _ _))
  have hθr₀ : tsupport θ ⊆ Metric.ball x₀ r₀ := hθsup.trans (Metric.ball_subset_ball (min_le_right _ _))
  have hφr₀ : tsupport φ ⊆ Metric.ball x₀ r₀ := hφsup.trans (Metric.ball_subset_ball (min_le_right _ _))
  refine ⟨ζ, φ, ρ, P/c^2+1, hρ, by positivity, hζ, hφ, hcζ, hcφ, hζr₀, hφr₀,
    hζ1, hφaway, hφb, ?_⟩
  have heS : ∀ᶠ j in atTop, 1≤S j := hS.eventually (eventually_ge_atTop 1)
  have heK : ∀ᶠ j in atTop, |K j/D j|≤1 := by
    simpa only [abs_zero] using hK.abs.eventually_le_const (by norm_num : |(0:ℝ)|<1)
  filter_upwards [heS, heK, eventually_ge_atTop j₀] with j hSj hKj hj₀
  have hDj : 1≤D j := hSj.trans (hD j)
  have hKsq : (K j)^2≤(D j)^2 := by
    have hh : |K j|≤D j := by simpa only [one_mul] using abs_le_mul_of_div (hDpos j) hKj
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (hDpos j).le).mpr hh
  have hTb := tilted_gradient_bound hχ (hSpos j).le (hD j) (hBD j) hCχ hχb
  have herr := weighted_cutoff_residual hζ hθ hφ (smooth_tiltedWeight _ _ hχ) (hU j) (hp j)
    hcζ hcθ hcφ hθ1 hφ1 hφlap hCP hCZ hCT (mul_nonneg hCt (hDpos j).le)
    (fun x => (hζlap x).trans (le_max_left _ _))
    (fun i x => (hζg i x).trans (le_max_right _ _))
    (fun x => (hθb x).trans (le_max_left _ _))
    (fun i x => (hθg i x).trans (le_max_right _ _)) hTb
    (fun x hx => (hpbound j x (hθr₀ hx)).trans (le_max_left _ _))
    (fun x hx => hPDE j x (hζr₀ hx)) (fun x hx => hPDE j x (hθr₀ hx))
  have hpre := cutoff_prefactor_bound (Cp:=CP) (Cζ:=Cζ) (Cθ:=Cθ) (Ct:=CT) hDj hKsq hCP
  have herr' : l2sq (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*
      (euclideanLaplacian (fun y => ζ y*U j y) x+(K j)^2*p j x*(ζ x*U j x))) ≤
      (P*l2sq (fun x => φ x*(Real.exp (tiltedWeight (B j) (S j) χ x)*U j x)))*(D j)^2 := by
    exact herr.trans ((mul_le_mul_of_nonneg_right hpre (l2sq_nonneg _)).trans_eq (by dsimp [P]; ring))
  have hcar' := hcar j hj₀ (fun x => ζ x*U j x) (hζ.mul (hU j)) hcζ.mul_right
    (tsupport_mul_subset_left.trans hζr)
  have hh := cancel_carleman_frequency (hSpos j).le (hDpos j) hc hcar' herr'
  apply hh.trans
  have hnn := l2sq_nonneg (fun x => φ x*(Real.exp (tiltedWeight (B j) (S j) χ x)*U j x))
  rw [mul_div_right_comm]
  nlinarith only [hnn]

theorem cutoff_mass_comparison_on {Ω : Set Plane} {p U : ℕ → Plane → ℝ} {χ : Plane → ℝ}
    {B : ℕ → Plane} {S D K e : ℕ → ℝ} {b : Plane} {d Cp r₀ : ℝ} {x₀ : Plane}
    (hΩ : IsOpen Ω) (hx₀ : x₀∈Ω)
    (hχ : ContDiffOn ℝ ∞ χ Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω)
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) Ω) (hr₀ : 0 < r₀)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hDdef : ∀ j, D j=S j+‖B j‖)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x ∈ Metric.ball x₀ r₀ → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x ∈ Metric.ball x₀ r₀ →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (hPDE : ∀ j x, x ∈ Metric.ball x₀ r₀ →
      euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (htrace : euclideanLaplacian χ x₀<0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0) :
    ∃ (ζ φ : Plane → ℝ) (ρ C : ℝ), 0<ρ ∧ 0<C ∧
      Smooth ζ ∧ Smooth φ ∧ HasCompactSupport ζ ∧ HasCompactSupport φ ∧
      tsupport ζ ⊆ Metric.ball x₀ r₀ ∧ tsupport φ ⊆ Metric.ball x₀ r₀ ∧
      (∀ x ∈ Metric.ball x₀ ρ, ζ x=1) ∧
      (∀ x ∈ tsupport φ, x≠x₀) ∧ (∀ x, 0≤φ x ∧ φ x≤1) ∧
      ∀ᶠ j in atTop,
        S j*l2sq (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*(ζ x*U j x)) ≤
        C*l2sq (fun x => φ x*(Real.exp (tiltedWeight (B j) (S j) χ x)*U j x)) := by
  obtain ⟨η, rη, hrη, hη, _, hηsub, hη1⟩ := exists_smooth_cutoff (hΩ.mem_nhds hx₀)
  let χ' : Plane → ℝ := fun x => η x*χ x
  let p' : ℕ → Plane → ℝ := fun j x => η x*p j x
  let U' : ℕ → Plane → ℝ := fun j x => η x*U j x
  have hχ' : Smooth χ' := smooth_cutoff_mul hΩ hη hηsub hχ
  have hp' (j : ℕ) : Smooth (p' j) := smooth_cutoff_mul hΩ hη hηsub (hp j)
  have hU' (j : ℕ) : Smooth (U' j) := smooth_cutoff_mul hΩ hη hηsub (hU j)
  have hχeq (x : Plane) (hx : x∈Metric.ball x₀ rη) : χ' x=χ x := by
    dsimp [χ']; rw [hη1 x hx, one_mul]
  have hpeq (j : ℕ) (x : Plane) (hx : x∈Metric.ball x₀ rη) : p' j x=p j x := by
    dsimp [p']; rw [hη1 x hx, one_mul]
  have hUeq (j : ℕ) (x : Plane) (hx : x∈Metric.ball x₀ rη) : U' j x=U j x := by
    dsimp [U']; rw [hη1 x hx, one_mul]
  have hχev : χ' =ᶠ[𝓝 x₀] χ := Filter.Eventually.mono
    (Metric.ball_mem_nhds x₀ hrη) fun x hx => hχeq x hx
  have hpev (j : ℕ) (x : Plane) (hx : x∈Metric.ball x₀ rη) : p' j =ᶠ[𝓝 x] p j :=
    Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hx) fun y hy => hpeq j y hy
  have hUev (j : ℕ) (x : Plane) (hx : x∈Metric.ball x₀ rη) : U' j =ᶠ[𝓝 x] U j :=
    Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hx) fun y hy => hUeq j y hy
  have hpb' (j : ℕ) (x : Plane) (hx : x∈Metric.ball x₀ (min rη r₀)) : |p' j x|≤Cp := by
    rw [hpeq j x (Metric.ball_subset_ball (min_le_left _ _) hx)]
    exact hpbound j x (Metric.ball_subset_ball (min_le_right _ _) hx)
  have hpg' (j : ℕ) (i : Fin 2) (x : Plane) (hx : x∈Metric.ball x₀ (min rη r₀)) :
      |(K j)^2*coordPartial (p' j) i x/(S j*D j)|≤e j := by
    rw [(partial_eventuallyEq (hpev j x (Metric.ball_subset_ball (min_le_left _ _) hx)) i).eq_of_nhds]
    exact hpgrad j i x (Metric.ball_subset_ball (min_le_right _ _) hx)
  have hPDE' (j : ℕ) (x : Plane) (hx : x∈Metric.ball x₀ (min rη r₀)) :
      euclideanLaplacian (U' j) x+(K j)^2*p' j x*U' j x=0 := by
    have hxη := Metric.ball_subset_ball (min_le_left rη r₀) hx
    rw [(laplacian_eventuallyEq (hUev j x hxη)).eq_of_nhds, hpeq j x hxη, hUeq j x hxη]
    exact hPDE j x (Metric.ball_subset_ball (min_le_right _ _) hx)
  have htr' : euclideanLaplacian χ' x₀<0 := by
    rw [(laplacian_eventuallyEq hχev).eq_of_nhds]; exact htrace
  have ha' : b+d • coordinateGradient χ' x₀ ≠ 0 := by
    rw [gradient_eq_of_eventuallyEq hχev]; exact ha
  obtain ⟨ζ, φ, ρ, C, hρ, hC, hζ, hφ, hcζ, hcφ, hζsub, hφsub,
    hζ1, hφaway, hφb, hcomp⟩ := cutoff_mass_comparison hχ' hp' hU' (lt_min hrη hr₀)
      hSpos hS hDdef hb hd hK hpb' he hpg' hPDE' htr' ha'
  refine ⟨ζ, φ, ρ, C, hρ, hC, hζ, hφ, hcζ, hcφ,
    hζsub.trans (Metric.ball_subset_ball (min_le_right _ _)),
    hφsub.trans (Metric.ball_subset_ball (min_le_right _ _)), hζ1, hφaway, hφb, ?_⟩
  have hweight (a : Plane → ℝ) (hasub : tsupport a ⊆ Metric.ball x₀ (min rη r₀)) (j : ℕ) :
      (fun x => Real.exp (tiltedWeight (B j) (S j) χ' x)*(a x*U' j x)) =
      (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*(a x*U j x)) := by
    funext x
    by_cases hx : x∈tsupport a
    · have hh := Metric.ball_subset_ball (min_le_left rη r₀) (hasub hx)
      simp only [tiltedWeight, hχeq x hh, hUeq j x hh]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]
  filter_upwards [hcomp] with j hj
  rw [hweight ζ hζsub] at hj
  have heq : (fun x => φ x*(Real.exp (tiltedWeight (B j) (S j) χ' x)*U' j x)) =
      (fun x => φ x*(Real.exp (tiltedWeight (B j) (S j) χ x)*U j x)) := by
    simpa only [mul_left_comm] using hweight φ hφsub j
  rwa [heq] at hj

end Profiles
end SharpNodal

noncomputable section
open scoped Topology ENNReal
open MeasureTheory Filter Set
namespace SharpNodal.Profiles

lemma ereal_pos_mul_lt_coe_iff {c : ℝ} (hc : 0 < c) (a : EReal) (b : ℝ) :
    (c:EReal)*a < (b:EReal) ↔ a < ((b/c : ℝ):EReal) := by
  cases a using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top => simp [EReal.coe_mul_top_of_pos hc]
  | coe a =>
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    simp only [lt_div_iff₀ hc, mul_comm]

lemma ereal_coe_lt_pos_mul_iff {c : ℝ} (hc : 0 < c) (a : EReal) (b : ℝ) :
    (b:EReal) < (c:EReal)*a ↔ ((b/c : ℝ):EReal) < a := by
  cases a using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top => simp [EReal.coe_mul_top_of_pos hc]
  | coe a =>
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    simp only [div_lt_iff₀ hc, mul_comm]

lemma logRate_lt_iff {S a : ℝ} (hS : 0<S) (m : ℝ≥0∞) :
    logRate S m < (a:EReal) ↔ m < ENNReal.ofReal (Real.exp (2*S*a)) := by
  rw [logRate, ereal_pos_mul_lt_coe_iff (inv_pos.mpr (by positivity : 0<2*S))]
  rw [div_inv_eq_mul, show a*(2*S)=2*S*a by ring]
  rw [show ((2*S*a : ℝ):EReal)=(ENNReal.ofReal (Real.exp (2*S*a))).log by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]]
  exact ENNReal.log_lt_log_iff

lemma lt_logRate_iff {S a : ℝ} (hS : 0<S) (m : ℝ≥0∞) :
    (a:EReal) < logRate S m ↔ ENNReal.ofReal (Real.exp (2*S*a)) < m := by
  rw [logRate, ereal_coe_lt_pos_mul_iff (inv_pos.mpr (by positivity : 0<2*S))]
  rw [div_inv_eq_mul, show a*(2*S)=2*S*a by ring]
  rw [show ((2*S*a : ℝ):EReal)=(ENNReal.ofReal (Real.exp (2*S*a))).log by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]]
  exact ENNReal.log_lt_log_iff

lemma exponential_gap {S : ℕ → ℝ} {a b C : ℝ} (hS : Tendsto S atTop atTop)
    (hgap : a<b) (hC : 0<C) :
    ∀ᶠ j in atTop, C*Real.exp (2*S j*a)<Real.exp (2*S j*b) := by
  have hδ : 0<2*(b-a) := by linarith
  have he : ∀ᶠ j in atTop, Real.log C/(2*(b-a))<S j :=
    hS.eventually (eventually_gt_atTop _)
  filter_upwards [he] with j hj
  have hj' : Real.log C<2*S j*(b-a) := by
    have hh := (div_lt_iff₀ hδ).mp hj
    nlinarith only [hh]
  rw [← Real.exp_log hC, ← Real.exp_add, Real.exp_lt_exp]
  nlinarith only [hj']

lemma no_exponential_gap {S : ℕ → ℝ} {A B : ℕ → ℝ≥0∞} {a b C : ℝ}
    (hS : Tendsto S atTop atTop) (hgap : a<b) (hC : 0<C)
    (hA : ∀ᶠ j in atTop, A j≤ENNReal.ofReal (Real.exp (2*S j*a)))
    (hB : ∀ᶠ j in atTop, ENNReal.ofReal (Real.exp (2*S j*b))≤B j)
    (hcomp : ∀ᶠ j in atTop, B j≤ENNReal.ofReal C*A j) : False := by
  have hg := exponential_gap hS hgap hC
  obtain ⟨j, hAj, hBj, hcj, hgj⟩ := (hA.and (hB.and (hcomp.and hg))).exists
  have hle := hBj.trans (hcj.trans (mul_le_mul' le_rfl hAj))
  rw [← ENNReal.ofReal_mul hC.le] at hle
  have hle' : Real.exp (2*S j*b)≤C*Real.exp (2*S j*a) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  exact (not_le_of_gt hgj) hle'

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma tiltedMass_neg (S : ℝ) (B : Plane) (U : Plane → ℝ) (c : ℝ)
    (χ : Plane → ℝ) (E : Set Plane) :
    tiltedMass S B U c (fun x => -χ x) E =
      ∫⁻ x in E, ENNReal.ofReal (c*(Real.exp (tiltedWeight B S χ x)*U x)^2) := by
  simp only [tiltedMass, neg_neg]

lemma integral_square_mass {g : Plane → ℝ} {c : ℝ}
    (hg : Integrable (fun x => g x*g x)) (hc : 0 ≤ c) :
    ENNReal.ofReal c*ENNReal.ofReal (l2sq g) = ∫⁻ x, ENNReal.ofReal (c*(g x)^2) := by
  rw [← ENNReal.ofReal_mul hc, l2sq, ← integral_const_mul]
  simpa only [pow_two] using ofReal_integral_eq_lintegral_ofReal (hg.const_mul c)
    (Filter.Eventually.of_forall fun x => mul_nonneg hc (mul_self_nonneg (g x)))

lemma cutoff_square_integrable_on {Ω : Set Plane} {a g : Plane → ℝ}
    (hΩ : IsOpen Ω) (ha : Smooth a) (hca : HasCompactSupport a)
    (haΩ : tsupport a⊆Ω) (hg : ContDiffOn ℝ ∞ g Ω) :
    Integrable (fun x => (a x*g x)*(a x*g x)) := by
  have hsm := smooth_cutoff_mul hΩ ha haΩ hg
  exact (hsm.mul hsm).continuous.integrable_of_hasCompactSupport hca.mul_right.mul_right

lemma cutoff_square_mass_lower {a g : Plane → ℝ} {c : ℝ} {G : Set Plane}
    (hc : 0 ≤ c) (hGm : MeasurableSet G) (hG : ∀ x∈G, a x=1)
    (hi : Integrable (fun x => (a x*g x)*(a x*g x))) :
    (∫⁻ x in G, ENNReal.ofReal (c*(g x)^2)) ≤
      ENNReal.ofReal c*ENNReal.ofReal (l2sq (fun x => a x*g x)) := by
  rw [integral_square_mass hi hc]
  calc
    _ = ∫⁻ x in G, ENNReal.ofReal (c*(a x*g x)^2) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hGm] with x hx
      rw [hG x hx, one_mul]
    _ ≤ _ := setLIntegral_le_lintegral _ _

lemma cutoff_square_mass_upper {a g : Plane → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (ha : ∀ x, 0≤a x ∧ a x≤1)
    (hi : Integrable (fun x => (a x*g x)*(a x*g x))) :
    ENNReal.ofReal c*ENNReal.ofReal (l2sq (fun x => a x*g x)) ≤
      ∫⁻ x in tsupport a, ENNReal.ofReal (c*(g x)^2) := by
  rw [integral_square_mass hi hc, ← lintegral_indicator (isClosed_tsupport a).measurableSet]
  apply lintegral_mono
  intro x
  by_cases hx : x∈tsupport a
  · rw [Set.indicator_of_mem hx]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hc
    have hh : (a x)^2≤1 := by nlinarith only [(ha x).1, (ha x).2]
    nlinarith only [mul_le_mul_of_nonneg_right hh (sq_nonneg (g x))]
  · simp [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]

lemma smooth_tiltedWeight_on {Ω : Set Plane} {χ : Plane → ℝ}
    (hχ : ContDiffOn ℝ ∞ χ Ω) (B : Plane) (S : ℝ) :
    ContDiffOn ℝ ∞ (tiltedWeight B S χ) Ω := by
  unfold tiltedWeight
  exact (innerSL ℝ B).contDiff.contDiffOn.neg.sub (contDiffOn_const.mul hχ)

theorem tilted_mass_comparison_on {Ω : Set Plane} {p U : ℕ → Plane → ℝ} {χ : Plane → ℝ}
    {B : ℕ → Plane} {S D K e c : ℕ → ℝ} {b : Plane} {d Cp r₀ : ℝ} {x₀ : Plane}
    (hΩ : IsOpen Ω) (hx₀ : x₀∈Ω) (hball : Metric.ball x₀ r₀⊆Ω)
    (hχ : ContDiffOn ℝ ∞ χ Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω)
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) Ω) (hr₀ : 0 < r₀)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hc : ∀ j, 0 < c j) (hDdef : ∀ j, D j=S j+‖B j‖)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x ∈ Metric.ball x₀ r₀ → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x ∈ Metric.ball x₀ r₀ →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (hPDE : ∀ j x, x ∈ Metric.ball x₀ r₀ →
      euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (htrace : euclideanLaplacian χ x₀<0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0) :
    ∃ (F G : Set Plane) (C : ℝ), IsCompact F ∧ IsOpen G ∧ 0<C ∧
      F⊆Metric.ball x₀ r₀ ∧ G⊆Metric.ball x₀ r₀ ∧ x₀∉F ∧ x₀∈G ∧
      ∀ᶠ j in atTop,
        tiltedMass (S j) (B j) (U j) (c j) (fun x => -χ x) G ≤
          ENNReal.ofReal C*tiltedMass (S j) (B j) (U j) (c j) (fun x => -χ x) F := by
  obtain ⟨ζ, φ, ρ, C, hρ, hC, hζ, hφ, hcζ, hcφ, hζsub, hφsub,
    hζ1, hφaway, hφb, hcomp⟩ := cutoff_mass_comparison_on hΩ hx₀ hχ hp hU hr₀
      hSpos hS hDdef hb hd hK hpbound he hpgrad hPDE htrace ha
  let G := Metric.ball x₀ (min ρ r₀)
  have hG : G⊆Metric.ball x₀ ρ := Metric.ball_subset_ball (min_le_left _ _)
  refine ⟨tsupport φ, G, C, hcφ, Metric.isOpen_ball, hC, hφsub,
    Metric.ball_subset_ball (min_le_right _ _), fun hh => hφaway x₀ hh rfl,
    Metric.mem_ball_self (lt_min hρ hr₀), ?_⟩
  have heS : ∀ᶠ j in atTop, 1≤S j := hS.eventually (eventually_ge_atTop 1)
  filter_upwards [hcomp, heS] with j hj hSj
  let g : Plane → ℝ := fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*U j x
  have hg : ContDiffOn ℝ ∞ g Ω :=
    (smooth_tiltedWeight_on hχ (B j) (S j)).exp.mul (hU j)
  have hiζ := cutoff_square_integrable_on hΩ hζ hcζ (hζsub.trans hball) hg
  have hiφ := cutoff_square_integrable_on hΩ hφ hcφ (hφsub.trans hball) hg
  have hleft := cutoff_square_mass_lower (hc j).le Metric.isOpen_ball.measurableSet (fun x hx => hζ1 x (hG hx)) hiζ
  have hright := cutoff_square_mass_upper (hc j).le hφb hiφ
  have hnorm : l2sq (fun x => ζ x*g x) ≤ C*l2sq (fun x => φ x*g x) := by
    have hj' : S j*l2sq (fun x => ζ x*g x) ≤ C*l2sq (fun x => φ x*g x) := by
      simpa only [g, mul_left_comm] using hj
    exact (le_mul_of_one_le_left (l2sq_nonneg _) hSj).trans hj'
  rw [tiltedMass_neg, tiltedMass_neg]
  apply hleft.trans
  calc
    _ ≤ ENNReal.ofReal (c j)*(ENNReal.ofReal C*ENNReal.ofReal (l2sq (fun x => φ x*g x))) := by
      apply mul_le_mul' le_rfl
      rw [← ENNReal.ofReal_mul hC.le]
      exact ENNReal.ofReal_le_ofReal hnorm
    _ = ENNReal.ofReal C*(ENNReal.ofReal (c j)*ENNReal.ofReal (l2sq (fun x => φ x*g x))) := by ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl hright

end SharpNodal.Profiles

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ProfileTests
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set

namespace SharpNodal.Profiles
open Carleman

lemma upperSemicontinuousOn_add_real {Ω : Set Plane} {V : Plane → EReal}
    {f : Plane → ℝ} (hV : UpperSemicontinuousOn V Ω) (hf : ContinuousOn f Ω) :
    UpperSemicontinuousOn (fun x => V x+(f x:EReal)) Ω := by
  apply hV.add' (continuous_coe_real_ereal.comp_continuousOn hf).upperSemicontinuousOn
  intro x hx
  exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))

lemma compact_strict_gap {F : Set Plane} {W : Plane → EReal} (hF : IsCompact F)
    (hW : UpperSemicontinuousOn W F) (hneg : ∀ x∈F, W x<0) :
    (⨆ x∈F, W x)<0 := by
  rcases F.eq_empty_or_nonempty with h | h
  · simp [h]
  · obtain ⟨x, hx, hmax⟩ := hW.exists_isMaxOn h hF
    apply lt_of_le_of_lt _ (hneg x hx)
    exact iSup_le fun y => iSup_le fun hy => hmax hy

theorem strict_contact_mass_contradiction
    {Ω F G : Set Plane} {S c : ℕ → ℝ} {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    {V : Plane → EReal} {f : Plane → ℝ} {x₀ : Plane} {C : ℝ}
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop) (hC : 0<C)
    (hV : UpperSemicontinuousOn V Ω) (hprofile : WeightedProfileBounds Ω S B U c V)
    (hf : ContinuousOn f Ω) (hF : IsCompact F) (hFΩ : F⊆Ω)
    (hG : IsOpen G) (hGΩ : G⊆Ω) (hx₀ : x₀∈G)
    (hneg : ∀ x∈F, V x+(f x:EReal)<0) (hzero : V x₀+(f x₀:EReal)=0)
    (hcomp : ∀ᶠ j in atTop, tiltedMass (S j) (B j) (U j) (c j) f G ≤
      ENNReal.ofReal C*tiltedMass (S j) (B j) (U j) (c j) f F) : False := by
  have hW := (upperSemicontinuousOn_add_real hV hf).mono hFΩ
  have hgap := compact_strict_gap hF hW hneg
  obtain ⟨a, hsa, ha⟩ := EReal.lt_iff_exists_real_btwn.mp hgap
  have ha' : a<0 := by exact_mod_cast ha
  let b := a/2
  have hab : a<b := by dsimp [b]; linarith
  have hb : b<0 := by dsimp [b]; linarith
  have hupper := hprofile.upper f hf F hF hFΩ
  have hlower := hprofile.lower f hf G hG hGΩ
  have hlow0 : (0:EReal)≤⨆ x∈G, V x+(f x:EReal) := by
    rw [← hzero]
    exact le_iSup_of_le x₀ (le_iSup_of_le hx₀ le_rfl)
  have hA := eventually_lt_of_limsup_lt (hupper.trans_lt hsa)
  have hB := eventually_lt_of_lt_liminf
    ((show (b:EReal)<0 by exact_mod_cast hb).trans_le (hlow0.trans hlower))
  apply no_exponential_gap hS hab hC _ _ hcomp
  · filter_upwards [hA] with j hj
    exact ((logRate_lt_iff (hSpos j) _).mp hj).le
  · filter_upwards [hB] with j hj
    exact ((lt_logRate_iff (hSpos j) _).mp hj).le

theorem laplacian_nonneg_of_strict_contact
    {Ω : Set Plane} {p U : ℕ → Plane → ℝ} {χ : Plane → ℝ} {V : Plane → EReal}
    {B : ℕ → Plane} {S D K e c : ℕ → ℝ} {b : Plane} {d Cp r₀ : ℝ} {x₀ : Plane}
    (hΩ : IsOpen Ω) (hx₀ : x₀∈Ω) (hball : Metric.ball x₀ r₀⊆Ω)
    (hχ : ContDiffOn ℝ ∞ χ Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω)
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) Ω) (hr₀ : 0 < r₀)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hc : ∀ j, 0 < c j) (hDdef : ∀ j, D j=S j+‖B j‖)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x ∈ Metric.ball x₀ r₀ → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x ∈ Metric.ball x₀ r₀ →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (hPDE : ∀ j x, x ∈ Metric.ball x₀ r₀ →
      euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0)
    (hV : UpperSemicontinuousOn V Ω) (hprofile : WeightedProfileBounds Ω S B U c V)
    (hcontact : V x₀+(-χ x₀:EReal)=0)
    (hstrict : ∀ x∈Metric.ball x₀ r₀, x≠x₀ → V x+(-χ x:EReal)<0) :
    0≤euclideanLaplacian χ x₀ := by
  by_contra hn
  have htrace := lt_of_not_ge hn
  obtain ⟨F, G, C, hF, hG, hC, hFsub, hGsub, hFaway, hxG, hcomp⟩ :=
    tilted_mass_comparison_on hΩ hx₀ hball hχ hp hU hr₀ hSpos hS hc hDdef hb hd hK
      hpbound he hpgrad hPDE htrace ha
  apply strict_contact_mass_contradiction hSpos hS hC hV hprofile hχ.continuousOn.neg
    hF (hFsub.trans hball) hG (hGsub.trans hball) hxG _ hcontact hcomp
  intro x hx
  apply hstrict x (hFsub hx)
  intro heq
  exact hFaway (heq ▸ hx)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma smooth_radiusSquare (x₀ : Plane) : Smooth (radiusSquare x₀) :=
  (contDiff_id.sub contDiff_const).norm_sq ℝ

lemma radiusSquare_self (x₀ : Plane) : radiusSquare x₀ x₀=0 := by simp [radiusSquare]

lemma radiusSquare_pos {x₀ x : Plane} (hx : x≠x₀) : 0 < radiusSquare x₀ x := by
  exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) 2

lemma radiusSquare_partial_self (x₀ : Plane) (i : Fin 2) :
    coordPartial (radiusSquare x₀) i x₀=0 := by
  have hq : HasFDerivAt (𝕜:=ℝ) (radiusSquare x₀) 0 x₀ := by
    convert! ((hasFDerivAt_id (𝕜:=ℝ) x₀).sub_const x₀).norm_sq using 1
    all_goals try with_reducible_and_instances rfl
    simp
  simp [coordPartial, hq.fderiv]

lemma smooth_contactQuartic (x₀ : Plane) : Smooth (contactQuartic x₀) :=
  (smooth_radiusSquare x₀).mul (smooth_radiusSquare x₀)

lemma contactQuartic_self (x₀ : Plane) : contactQuartic x₀ x₀=0 := by
  simp [contactQuartic, radiusSquare_self]

lemma contactQuartic_pos {x₀ x : Plane} (hx : x≠x₀) : 0 < contactQuartic x₀ x :=
  mul_pos (radiusSquare_pos hx) (radiusSquare_pos hx)

lemma contactQuartic_partial_self (x₀ : Plane) (i : Fin 2) :
    coordPartial (contactQuartic x₀) i x₀=0 := by
  unfold contactQuartic
  rw [partial_mul (smooth_radiusSquare x₀) (smooth_radiusSquare x₀)]
  simp [radiusSquare_self]

lemma contactQuartic_laplacian_self (x₀ : Plane) :
    euclideanLaplacian (contactQuartic x₀) x₀=0 := by
  unfold contactQuartic
  rw [laplacian_mul (smooth_radiusSquare x₀) (smooth_radiusSquare x₀)]
  simp [radiusSquare_self, radiusSquare_partial_self]

lemma strictify_gradient {χ : Plane → ℝ} (hχ : Smooth χ) (x₀ : Plane) :
    coordinateGradient (fun x => χ x+contactQuartic x₀ x) x₀=coordinateGradient χ x₀ := by
  ext i
  simp only [coordinateGradient_apply, partial_add hχ (smooth_contactQuartic x₀),
    contactQuartic_partial_self, add_zero]

lemma strictify_laplacian {χ : Plane → ℝ} (hχ : Smooth χ) (x₀ : Plane) :
    euclideanLaplacian (fun x => χ x+contactQuartic x₀ x) x₀=euclideanLaplacian χ x₀ := by
  rw [laplacian_add hχ (smooth_contactQuartic x₀), contactQuartic_laplacian_self, add_zero]

lemma strictify_contact {V : Plane → EReal} {χ : Plane → ℝ} {x₀ : Plane}
    (hcontact : V x₀=(χ x₀:EReal)) :
    V x₀+((-(χ x₀+contactQuartic x₀ x₀):ℝ):EReal)=0 := by
  rw [contactQuartic_self, add_zero, hcontact, ← EReal.coe_add]
  simp

lemma strictify_strict {V : Plane → EReal} {χ : Plane → ℝ} {x₀ x : Plane}
    (hdom : V x≤(χ x:EReal)) (hx : x≠x₀) :
    V x+((-(χ x+contactQuartic x₀ x):ℝ):EReal)<0 := by
  apply lt_of_le_of_lt (add_le_add hdom le_rfl) _
  rw [← EReal.coe_add]
  norm_cast
  have hq := contactQuartic_pos hx
  linarith

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma smooth_centeredQuadratic (A : BilinearForm) (x₀ : Plane) :
    Smooth (centeredQuadratic A x₀) := by
  exact contDiff_const.mul ((contDiff_const.clm_apply (contDiff_id.sub contDiff_const)).clm_apply
    (contDiff_id.sub contDiff_const))

lemma hasFDerivAt_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ x : Plane) : HasFDerivAt (centeredQuadratic A x₀) (A (x-x₀)) x := by
  have ht := (hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀
  have hAt : HasFDerivAt (fun y => A (y-x₀)) A x := by
    convert! A.hasFDerivAt.comp x ht using 1
    all_goals try with_reducible_and_instances rfl
  convert! (hAt.clm_apply ht).const_mul (1/2:ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, id_eq]
  rw [hA y (x-x₀)]
  ring

lemma fderiv_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A) (x₀ : Plane) :
    fderiv ℝ (centeredQuadratic A x₀) = fun x => A (x-x₀) :=
  funext fun x => (hasFDerivAt_centeredQuadratic hA x₀ x).fderiv

lemma partial_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ : Plane) (i : Fin 2) (x : Plane) :
    coordPartial (centeredQuadratic A x₀) i x=A (x-x₀) (EuclideanSpace.single i 1) := by
  rw [coordPartial, fderiv_centeredQuadratic hA]

lemma partial2_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ : Plane) (i j : Fin 2) (x : Plane) :
    coordPartial (coordPartial (centeredQuadratic A x₀) i) j x=
      A (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
  rw [show coordPartial (centeredQuadratic A x₀) i =
    fun y => A (y-x₀) (EuclideanSpace.single i 1) from funext (partial_centeredQuadratic hA x₀ i)]
  have ht := (hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀
  have hh : HasFDerivAt (fun y => A (y-x₀) (EuclideanSpace.single i 1))
      (A.flip (EuclideanSpace.single i 1)) x := by
    convert! (A.flip (EuclideanSpace.single i 1)).hasFDerivAt.comp x ht using 1
    all_goals try with_reducible_and_instances rfl
  simp only [coordPartial, hh.fderiv, ContinuousLinearMap.flip_apply]

lemma symmetric_hessian {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) :
    SymmetricForm (fderiv ℝ (fderiv ℝ f) x₀) := by
  intro x y
  exact (hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞)≤⊤))).eq x y

lemma hessian_on_basis {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) (i j : Fin 2) :
    fderiv ℝ (fderiv ℝ f) x₀ (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)=
      coordPartial (coordPartial f i) j x₀ := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by simp : (∞:ℕ∞ω)+1≤(∞:ℕ∞ω))).differentiable (by simp)
  unfold coordPartial
  rw [fderiv_clm_apply hdf.differentiableAt (differentiableAt_const _)]
  simp

lemma secondTaylorPolynomial_self (f : Plane → ℝ) (x₀ : Plane) :
    secondTaylorPolynomial f x₀ x₀=f x₀ := by
  simp [secondTaylorPolynomial, centeredQuadratic]

lemma hasFDerivAt_secondTaylorPolynomial {f : Plane → ℝ} (hf : Smooth f) (x₀ x : Plane) :
    HasFDerivAt (secondTaylorPolynomial f x₀)
      (fderiv ℝ f x₀+fderiv ℝ (fderiv ℝ f) x₀ (x-x₀)) x := by
  apply HasFDerivAt.add _ (hasFDerivAt_centeredQuadratic (symmetric_hessian hf x₀) x₀ x)
  apply HasFDerivAt.const_add
  convert! (fderiv ℝ f x₀).hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀) using 1
  all_goals try with_reducible_and_instances rfl

theorem secondTaylorPolynomial_remainder {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) :
    (fun x => f x-secondTaylorPolynomial f x₀ x) =o[𝓝 x₀] (fun x => ‖x-x₀‖^2) := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by simp : (∞:ℕ∞ω)+1≤(∞:ℕ∞ω))).differentiable (by simp)
  have hd := (hdf x₀).hasFDerivAt.isLittleO.norm_right
  have hder (x : Plane) : HasFDerivAt (fun y => f y-secondTaylorPolynomial f x₀ y)
      (fderiv ℝ f x-fderiv ℝ f x₀-fderiv ℝ (fderiv ℝ f) x₀ (x-x₀)) x := by
    convert! ((hf.differentiable (by simp) x).hasFDerivAt).sub
      (hasFDerivAt_secondTaylorPolynomial hf x₀ x) using 1
    all_goals try with_reducible_and_instances rfl
    abel
  have hh := (convex_univ : Convex ℝ (Set.univ : Set Plane)).isLittleO_pow_succ
    (mem_univ x₀) (fun x _ => (hder x).hasFDerivWithinAt) (n:=1)
      (by simpa only [nhdsWithin_univ, pow_one] using hd)
  simpa only [nhdsWithin_univ, secondTaylorPolynomial_self, sub_self, sub_zero] using hh

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma smooth_quadraticAffine (c : ℝ) (L : Plane →L[ℝ] ℝ) (A : BilinearForm)
    (x₀ : Plane) : Smooth (quadraticAffine c L A x₀) :=
  (contDiff_const.add (L.contDiff.comp (contDiff_id.sub contDiff_const))).add
    (smooth_centeredQuadratic A x₀)

lemma partial_clm_shift (L : Plane →L[ℝ] ℝ) (x₀ x : Plane) (i : Fin 2) :
    coordPartial (fun y => L (y-x₀)) i x=L (EuclideanSpace.single i 1) := by
  have hd : HasFDerivAt (fun y => L (y-x₀)) L x := by
    convert! L.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀) using 1
    all_goals try with_reducible_and_instances rfl
  simp only [coordPartial, hd.fderiv]

lemma partial_quadraticAffine {A : BilinearForm} (hA : SymmetricForm A)
    (c : ℝ) (L : Plane →L[ℝ] ℝ) (x₀ x : Plane) (i : Fin 2) :
    coordPartial (quadraticAffine c L A x₀) i x=
      L (EuclideanSpace.single i 1)+A (x-x₀) (EuclideanSpace.single i 1) := by
  have hL : Smooth (fun y => L (y-x₀)) :=
    contDiff_const.clm_apply (contDiff_id.sub contDiff_const)
  unfold quadraticAffine
  rw [partial_add (contDiff_const.add hL)
    (smooth_centeredQuadratic A x₀), partial_add contDiff_const hL, partial_const,
    partial_clm_shift, partial_centeredQuadratic hA, zero_add]

lemma laplacian_quadraticAffine {A : BilinearForm} (hA : SymmetricForm A)
    (c : ℝ) (L : Plane →L[ℝ] ℝ) (x₀ x : Plane) :
    euclideanLaplacian (quadraticAffine c L A x₀) x=formTrace A := by
  unfold euclideanLaplacian formTrace
  apply Finset.sum_congr rfl
  intro i _
  rw [show coordPartial (quadraticAffine c L A x₀) i =
    fun y => L (EuclideanSpace.single i 1)+coordPartial (centeredQuadratic A x₀) i y by
      ext y; rw [partial_quadraticAffine hA, partial_centeredQuadratic hA]]
  rw [partial_add contDiff_const (smooth_partial (smooth_centeredQuadratic A x₀) i),
    partial_const, zero_add, partial2_centeredQuadratic hA]

lemma quadraticAffine_self (c : ℝ) (L : Plane →L[ℝ] ℝ) (A : BilinearForm) (x₀ : Plane) :
    quadraticAffine c L A x₀ x₀=c := by simp [quadraticAffine, centeredQuadratic]

lemma innerForm_apply (x y : Plane) : innerForm x y=inner ℝ x y := rfl

lemma symmetric_innerForm : SymmetricForm innerForm := by
  intro x y
  exact real_inner_comm y x

lemma formTrace_innerForm : formTrace innerForm=2 := by
  simp [formTrace, innerForm_apply]

lemma formTrace_add (A B : BilinearForm) : formTrace (A+B)=formTrace A+formTrace B := by
  simp [formTrace, Finset.sum_add_distrib]

lemma formTrace_smul (c : ℝ) (A : BilinearForm) : formTrace (c • A)=c*formTrace A := by
  simp only [formTrace, smul_apply, smul_eq_mul, Finset.mul_sum]

lemma formTrace_hessian {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) :
    formTrace (fderiv ℝ (fderiv ℝ f) x₀)=euclideanLaplacian f x₀ := by
  simp only [formTrace, euclideanLaplacian, hessian_on_basis hf]

lemma centeredQuadratic_add (A B : BilinearForm) (x₀ x : Plane) :
    centeredQuadratic (A+B) x₀ x=centeredQuadratic A x₀ x+centeredQuadratic B x₀ x := by
  simp [centeredQuadratic]; ring

lemma centeredQuadratic_inner_smul (δ : ℝ) (x₀ x : Plane) :
    centeredQuadratic ((2*δ) • innerForm) x₀ x=δ*‖x-x₀‖^2 := by
  simp only [centeredQuadratic, smul_apply, smul_eq_mul, innerForm_apply,
    real_inner_self_eq_norm_sq]
  ring

theorem exists_strict_quadratic_test {Ω : Set Plane} {V : Plane → EReal}
    {f : Plane → ℝ} {x₀ : Plane} (hΩ : IsOpen Ω) (hx₀ : x₀∈Ω)
    (hf : Smooth f) (htest : IsUpperTest V f x₀) (hΔ : euclideanLaplacian f x₀<0) :
    ∃ (A : BilinearForm) (r : ℝ), SymmetricForm A ∧ formTrace A<0 ∧ 0 < r ∧
      Metric.closedBall x₀ r⊆Ω ∧
      (∀ x∈Metric.closedBall x₀ r,
        V x≤(quadraticAffine (f x₀) (fderiv ℝ f x₀) A x₀ x:EReal)) ∧
      (∀ x∈Metric.closedBall x₀ r, x≠x₀ →
        V x<(quadraticAffine (f x₀) (fderiv ℝ f x₀) A x₀ x:EReal)) := by
  let δ := -euclideanLaplacian f x₀/8
  have hδ : 0<δ := by dsimp [δ]; linarith
  let A : BilinearForm := fderiv ℝ (fderiv ℝ f) x₀+(2*δ) • innerForm
  have hA : SymmetricForm A := by
    intro x y
    dsimp [A]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [symmetric_hessian hf x₀ x y, symmetric_innerForm x y]
  have htrace : formTrace A<0 := by
    dsimp [A]
    rw [formTrace_add, formTrace_smul, formTrace_innerForm, formTrace_hessian hf]
    dsimp [δ]
    linarith
  have heq (x : Plane) : quadraticAffine (f x₀) (fderiv ℝ f x₀) A x₀ x=
      secondTaylorPolynomial f x₀ x+δ*‖x-x₀‖^2 := by
    dsimp only [quadraticAffine, A, secondTaylorPolynomial]
    rw [centeredQuadratic_add, centeredQuadratic_inner_smul]
    ring
  have hrem := (secondTaylorPolynomial_remainder hf x₀).bound (half_pos hδ)
  have hevent : ∀ᶠ x in 𝓝 x₀, x∈Ω ∧ V x≤(f x:EReal) ∧
      ‖f x-secondTaylorPolynomial f x₀ x‖≤δ/2*‖x-x₀‖^2 := by
    filter_upwards [hΩ.mem_nhds hx₀, htest.2, hrem] with x hx hd hr
    refine ⟨hx, hd, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x-x₀‖)] using hr
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨A, r/2, hA, htrace, half_pos hr, ?_, ?_, ?_⟩
  · intro x hx
    exact (hsub (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith)))).1
  · intro x hx
    obtain ⟨_, hd, hb⟩ := hsub (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith)))
    apply hd.trans
    apply EReal.coe_le_coe_iff.mpr
    rw [heq]
    rw [Real.norm_eq_abs] at hb
    have hm := le_trans (le_abs_self (f x-secondTaylorPolynomial f x₀ x)) hb
    have hp := sq_nonneg ‖x-x₀‖
    nlinarith
  · intro x hx hne
    obtain ⟨_, hd, hb⟩ := hsub (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith)))
    apply hd.trans_lt
    apply EReal.coe_lt_coe_iff.mpr
    rw [heq]
    rw [Real.norm_eq_abs] at hb
    have hm := le_trans (le_abs_self (f x-secondTaylorPolynomial f x₀ x)) hb
    have hp : 0<‖x-x₀‖^2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) _
    nlinarith

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ProfileExtraction
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace

noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma upper_test_of_maximum {V : Plane → EReal} {q : Plane → ℝ} {F : Set Plane}
    {x₀ : Plane} (hx₀ : x₀∈interior F) (hfinite : V x₀≠⊤ ∧ V x₀≠⊥)
    (hmax : IsMaxOn (fun x => V x+((-q x:ℝ):EReal)) F x₀) :
    IsUpperTest V (fun x => q x+(V x₀).toReal-q x₀) x₀ := by
  have hv := EReal.coe_toReal hfinite.1 hfinite.2
  refine ⟨?_, ?_⟩
  · simp only [add_sub_cancel_left, hv]
  · filter_upwards [mem_interior_iff_mem_nhds.mp hx₀] with x hx
    apply (EReal.addLECancellable_coe (-q x)).add_le_add_iff_right.mp
    have hh : V x+((-q x:ℝ):EReal) ≤ V x₀+((-q x₀:ℝ):EReal) := hmax hx
    rw [← hv, ← EReal.coe_add] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [← EReal.coe_add]
    congr 1
    ring

lemma negative_trace_coordinate {A : BilinearForm} (hA : formTrace A<0) :
    ∃ i : Fin 2, A (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)<0 := by
  by_contra hn
  push Not at hn
  exact (not_le_of_gt hA) (Finset.sum_nonneg fun i _ => hn i)

theorem full_test_of_nonexceptional {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : IsOpen Ω) (hV : UpperSemicontinuousOn V Ω)
    (hnon : NonexceptionalTestProperty Ω V) : FullTestProperty Ω V := by
  intro f hf x₀ hx₀ ht
  by_contra hn
  have hΔ : euclideanLaplacian f x₀<0 := lt_of_not_ge hn
  have hgrad : coordinateGradient f x₀=0 := by
    by_contra hg
    exact (not_le_of_gt hΔ) (hnon f hf x₀ hx₀ ht hg)
  obtain ⟨A,r,hA,htr,hr,hball,hdom,hstrict⟩ :=
    exists_strict_quadratic_test hΩ hx₀ hf ht hΔ
  obtain ⟨i,hi⟩ := negative_trace_coordinate htr
  let L : Plane →L[ℝ] ℝ := A (EuclideanSpace.single i 1)
  let q := quadraticAffine (f x₀) (fderiv ℝ f x₀) A x₀
  have hq : Smooth q := smooth_quadraticAffine _ _ _ _
  have hq₀ : q x₀=f x₀ := quadraticAffine_self _ _ _ _
  have hgrad_i : (fderiv ℝ f x₀) (EuclideanSpace.single i 1)=0 := by
    have hh := congrArg (fun v : Plane => v i) hgrad
    simpa only [coordinateGradient_apply, coordPartial, PiLp.zero_apply] using hh
  let H := Metric.sphere x₀ r
  have hH : IsCompact H := isCompact_sphere x₀ r
  have hHball : H⊆Metric.closedBall x₀ r := Metric.sphere_subset_closedBall
  have hW := upperSemicontinuousOn_add_real (hV.mono (hHball.trans hball)) hq.continuous.neg.continuousOn
  have hgap : (⨆ x∈H, V x+((-q x:ℝ):EReal))<0 := by
    apply compact_strict_gap hH hW
    intro x hx
    have hne : x≠x₀ := by
      intro he
      have : r=0 := by simpa [H, he] using (Metric.mem_sphere.mp hx).symm
      linarith
    have hxq := hstrict x (hHball hx) hne
    calc V x+((-q x:ℝ):EReal) < (q x:EReal)+((-q x:ℝ):EReal) :=
          EReal.add_lt_add_right_coe hxq (-q x)
      _ = 0 := by rw [← EReal.coe_add]; simp
  obtain ⟨a,ha,ha0⟩ := EReal.lt_iff_exists_real_btwn.mp hgap
  have ha0' : a<0 := by exact_mod_cast ha0
  let C := ‖L‖*r+1
  have hC : 0<C := by dsimp [C]; positivity
  let t := -a/(2*C)
  have htpos : 0<t := div_pos (neg_pos.mpr ha0') (mul_pos (by norm_num) hC)
  have htC : t*C= -a/2 := by dsimp [t]; field_simp
  let qt := quadraticAffine (f x₀) (fderiv ℝ f x₀-t • L) A x₀
  have hqt : Smooth qt := smooth_quadraticAffine _ _ _ _
  have hqt_eq (x : Plane) : qt x=q x-t*L (x-x₀) := by
    dsimp [qt,q,quadraticAffine]
    simp only [sub_apply,smul_apply,smul_eq_mul]
    ring
  have ht_bound (x : Plane) (hx : x∈Metric.closedBall x₀ r) : t*L (x-x₀)≤ -a/2 := by
    apply le_trans _ htC.le
    apply mul_le_mul_of_nonneg_left _ htpos.le
    have hx' : ‖x-x₀‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    calc L (x-x₀) ≤ ‖L (x-x₀)‖ := le_abs_self _
      _ ≤ ‖L‖*‖x-x₀‖ := L.le_opNorm _
      _ ≤ ‖L‖*r := mul_le_mul_of_nonneg_left hx' (norm_nonneg _)
      _ ≤ C := by dsimp [C]; linarith
  have hbdry : ∀ x∈H, V x+((-qt x:ℝ):EReal)<0 := by
    intro x hx
    have hbase : V x+((-q x:ℝ):EReal)<(a:EReal) :=
      (le_iSup₂_of_le x hx le_rfl).trans_lt ha
    have hb := ht_bound x (hHball hx)
    rw [hqt_eq, neg_sub, sub_eq_add_neg, EReal.coe_add]
    rw [add_comm ((t*L (x-x₀):ℝ):EReal), ← add_assoc]
    calc V x+((-q x:ℝ):EReal)+((t*L (x-x₀):ℝ):EReal)
        < (a:EReal)+((t*L (x-x₀):ℝ):EReal) :=
            EReal.add_lt_add_right_coe hbase (t*L (x-x₀))
      _ ≤ (a:EReal)+((-a/2:ℝ):EReal) := add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hb)
      _ < 0 := by rw [← EReal.coe_add]; exact_mod_cast (by linarith : a+-a/2<0)
  have hWball := upperSemicontinuousOn_add_real (hV.mono hball) hqt.continuous.neg.continuousOn
  obtain ⟨xt,hxt,hmax⟩ := hWball.exists_isMaxOn ⟨x₀,Metric.mem_closedBall_self hr.le⟩
    (isCompact_closedBall x₀ r)
  have hzero : V x₀+((-qt x₀:ℝ):EReal)=0 := by
    rw [ht.1, hqt_eq, sub_self, map_zero, mul_zero, sub_zero, hq₀, ← EReal.coe_add]
    simp
  have hmax0 : 0≤V xt+((-qt xt:ℝ):EReal) := by
    rw [← hzero]
    exact hmax (Metric.mem_closedBall_self hr.le)
  have hxtball : xt∈Metric.ball x₀ r := by
    apply Metric.mem_ball.mpr
    apply lt_of_le_of_ne (Metric.mem_closedBall.mp hxt)
    intro he
    exact (not_lt_of_ge hmax0) (hbdry xt (Metric.mem_sphere.mpr he))
  have hfinite : V xt≠⊤ ∧ V xt≠⊥ := by
    constructor
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (hdom xt hxt)
    · intro he
      have hh : (0:EReal)≤⊥ := by simpa only [he, EReal.bot_add] using hmax0
      exact (not_le_of_gt EReal.bot_lt_zero) hh
  have hLpos : 0≤L (xt-x₀) := by
    have hupper := add_le_add (hdom xt hxt) (le_refl ((-qt xt:ℝ):EReal))
    change V xt+((-qt xt:ℝ):EReal)≤(q xt:EReal)+((-qt xt:ℝ):EReal) at hupper
    rw [← EReal.coe_add] at hupper
    have hboth := hmax0.trans hupper
    rw [hqt_eq] at hboth
    have hreal : 0≤q xt+-(q xt-t*L (xt-x₀)) := by
      exact_mod_cast hboth
    have hmul : 0≤t*L (xt-x₀) := by linarith
    exact nonneg_of_mul_nonneg_right hmul htpos
  let ψ := fun x => qt x+(V xt).toReal-qt xt
  have hψ : Smooth ψ := (hqt.add contDiff_const).sub contDiff_const
  have htest : IsUpperTest V ψ xt :=
    upper_test_of_maximum (Metric.ball_subset_interior_closedBall hxtball) hfinite hmax
  have hψgrad : coordinateGradient ψ xt≠0 := by
    intro he
    have hiψ : coordPartial ψ i xt=0 := by
      have hh := congrArg (fun v : Plane => v i) he
      simpa only [coordinateGradient_apply, PiLp.zero_apply] using hh
    have hpartial : coordPartial ψ i xt=L (xt-x₀)-t*A (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
      dsimp only [ψ]
      rw [partial_sub (hqt.add contDiff_const) contDiff_const,
        partial_add hqt contDiff_const]
      simp only [partial_const, add_zero, sub_zero]
      rw [partial_quadraticAffine hA]
      simp only [sub_apply,smul_apply,smul_eq_mul,hgrad_i,zero_sub]
      rw [hA (xt-x₀) (EuclideanSpace.single i 1)]
      dsimp [L]
      ring
    rw [hpartial] at hiψ
    have hprod := mul_neg_of_pos_of_neg htpos hi
    linarith
  have hψΔ : euclideanLaplacian ψ xt=formTrace A := by
    have hψeq : ψ=fun x => qt x+((V xt).toReal-qt xt) := by funext x; dsimp [ψ]; ring
    rw [hψeq, laplacian_add hqt contDiff_const]
    rw [laplacian_const, add_zero]
    exact laplacian_quadraticAffine hA _ _ _ _
  have hh := hnon ψ hψ xt (hball hxt) htest hψgrad
  rw [hψΔ] at hh
  exact (not_le_of_gt htr) hh

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

theorem shifted_test_of_profile
    {Ω : Set Plane} {p U : ℕ → Plane → ℝ} {V : Plane → EReal}
    {B : ℕ → Plane} {S D K e c : ℕ → ℝ} {b : Plane} {d Cp : ℝ}
    (hΩ : IsOpen Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω)
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) Ω)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hc : ∀ j, 0 < c j) (hDdef : ∀ j, D j=S j+‖B j‖)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x∈Ω → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x∈Ω →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (hPDE : ∀ j x, x∈Ω → euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (hV : UpperSemicontinuousOn V Ω) (hprofile : WeightedProfileBounds Ω S B U c V) :
    ShiftedTestProperty Ω V b d := by
  intro f hf x₀ hx₀ ht ha
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.Eventually.and (hΩ.mem_nhds hx₀) ht.2)
  have hball : Metric.ball x₀ r⊆Ω := fun x hx => (hsub hx).1
  have hs := laplacian_nonneg_of_strict_contact hΩ hx₀ hball
    (hf.add (smooth_contactQuartic x₀)).contDiffOn hp hU hr hSpos hS hc hDdef
    hb hd hK (fun j x hx => hpbound j x (hball hx)) he
    (fun j i x hx => hpgrad j i x (hball hx))
    (fun j x hx => hPDE j x (hball hx))
    (by simpa only [strictify_gradient hf] using ha) hV hprofile
    (by simpa only [EReal.coe_neg] using strictify_contact (x₀:=x₀) ht.1)
    (fun x hx hne => by simpa only [EReal.coe_neg] using strictify_strict (hsub hx).2 hne)
  simpa only [strictify_laplacian hf] using hs

lemma gradient_sub_linear (B : Plane) {f : Plane → ℝ} (hf : Smooth f) (x : Plane) :
    coordinateGradient (fun y => f y-inner ℝ B y) x=coordinateGradient f x-B := by
  have hL : Smooth (fun y : Plane => inner ℝ B y) := (innerSL ℝ B).contDiff
  ext i
  simp only [coordinateGradient_apply, PiLp.sub_apply, partial_sub hf hL,partial_linear]

lemma laplacian_sub_linear (B : Plane) {f : Plane → ℝ} (hf : Smooth f) (x : Plane) :
    euclideanLaplacian (fun y => f y-inner ℝ B y) x=euclideanLaplacian f x := by
  have hL : Smooth (fun y : Plane => inner ℝ B y) := (innerSL ℝ B).contDiff
  unfold euclideanLaplacian
  apply Finset.sum_congr rfl
  intro i _
  rw [show coordPartial (fun y => f y-inner ℝ B y) i =fun y => coordPartial f i y-B i by
    ext y; rw [partial_sub hf hL,partial_linear]]
  rw [partial_sub (smooth_partial hf i) contDiff_const,partial_const,sub_zero]

lemma upperTest_sub_real {V : Plane → EReal} {f L : Plane → ℝ} {x : Plane}
    (ht : IsUpperTest (fun y => V y+(L y:EReal)) f x) :
    IsUpperTest V (fun y => f y-L y) x := by
  have hcancel (y : Plane) : (V y+(L y:EReal))+((-L y:ℝ):EReal)=V y := by
    rw [add_assoc,← EReal.coe_add]; simp
  constructor
  · have ht₀ : V x+(L x:EReal)=(f x:EReal) := ht.1
    rw [← hcancel x,ht₀,← EReal.coe_add]
    rfl
  · filter_upwards [ht.2] with y hy
    have hh := add_le_add hy (le_refl ((-L y:ℝ):EReal))
    simpa only [hcancel,← EReal.coe_add,sub_eq_add_neg] using hh

lemma upperTest_add_real {V : Plane → EReal} {f L : Plane → ℝ} {x : Plane}
    (ht : IsUpperTest V f x) :
    IsUpperTest (fun y => V y+(L y:EReal)) (fun y => f y+L y) x := by
  constructor
  · change V x+(L x:EReal)=((f x+L x:ℝ):EReal)
    rw [ht.1,EReal.coe_add]
  · filter_upwards [ht.2] with y hy
    rw [EReal.coe_add]
    exact add_le_add hy le_rfl

theorem full_test_of_shifted {Ω : Set Plane} {V : Plane → EReal} {b : Plane} {d : ℝ}
    (hΩ : IsOpen Ω) (hV : UpperSemicontinuousOn V Ω) (hd : 0≤d)
    (hnorm : d+‖b‖=1) (hshift : ShiftedTestProperty Ω V b d) :
    FullTestProperty Ω V := by
  rcases hd.eq_or_lt with hd | hd
  · have hb : b≠0 := by intro he; simp [← hd,he] at hnorm
    intro f hf x hx ht
    apply hshift f hf x hx ht
    simpa only [← hd,zero_smul,add_zero] using hb
  · let B : Plane := d⁻¹ • b
    let W : Plane → EReal := fun x => V x+(inner ℝ B x:EReal)
    have hW : UpperSemicontinuousOn W Ω :=
      upperSemicontinuousOn_add_real hV (innerSL ℝ B).continuous.continuousOn
    have hnon : NonexceptionalTestProperty Ω W := by
      intro f hf x hx ht hgrad
      have hs := hshift (fun y => f y-inner ℝ B y) (hf.sub (innerSL ℝ B).contDiff)
        x hx (upperTest_sub_real ht) ?_
      · simpa only [laplacian_sub_linear B hf] using hs
      · rw [gradient_sub_linear B hf,smul_sub,show d • B=b by
          dsimp [B]; rw [smul_smul,mul_inv_cancel₀ hd.ne',one_smul]]
        rw [show b+(d • coordinateGradient f x-b)=d • coordinateGradient f x by abel]
        exact smul_ne_zero hd.ne' hgrad
    have hfull := full_test_of_nonexceptional hΩ hW hnon
    intro f hf x hx ht
    have hs := hfull (fun y => f y+inner ℝ B y) (hf.add (innerSL ℝ B).contDiff)
      x hx (upperTest_add_real ht)
    have heq : (fun y => f y+inner ℝ B y)=(fun y => f y-inner ℝ (-B) y) := by
      ext y; simp
    rw [heq,laplacian_sub_linear (-B) hf] at hs
    exact hs
end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Subharmonic
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

theorem extract_normalized_parameters (S : ℕ → ℝ) (B : ℕ → Plane)
    (hS : ∀ j, 0 < S j) :
    ∃ (φ : ℕ → ℕ) (d : ℝ) (b : Plane), StrictMono φ ∧ 0 ≤ d ∧ d + ‖b‖ = 1 ∧
      Tendsto (fun j => S (φ j) / (S (φ j) + ‖B (φ j)‖)) atTop (𝓝 d) ∧
      Tendsto (fun j => (S (φ j) + ‖B (φ j)‖)⁻¹ • B (φ j)) atTop (𝓝 b) := by
  let x : ℕ → ℝ × Plane := fun j =>
    (S j / (S j + ‖B j‖), (S j + ‖B j‖)⁻¹ • B j)
  have hD (j : ℕ) : 0 < S j + ‖B j‖ := add_pos_of_pos_of_nonneg (hS j) (norm_nonneg _)
  have hxnorm (j : ℕ) : ‖(x j).2‖ = ‖B j‖ / (S j + ‖B j‖) := by
    dsimp [x]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hD j))]
    ring
  have hxpos (j : ℕ) : 0 ≤ (x j).1 := (div_pos (hS j) (hD j)).le
  have hxunit (j : ℕ) : (x j).1 + ‖(x j).2‖ = 1 := by
    rw [hxnorm]
    change S j / (S j + ‖B j‖) + ‖B j‖ / (S j + ‖B j‖) = 1
    rw [← add_div,div_self (hD j).ne']
  have hx (j : ℕ) : x j ∈ Metric.closedBall (0 : ℝ × Plane) 1 := by
    rw [Metric.mem_closedBall,dist_zero_right,norm_prod_le_iff]
    constructor
    · rw [Real.norm_eq_abs,abs_of_nonneg (hxpos j)]
      nlinarith [hxunit j,norm_nonneg (x j).2]
    · nlinarith [hxunit j,hxpos j]
  obtain ⟨a,_,φ,hφ,hlim⟩ := (isCompact_closedBall (0 : ℝ × Plane) 1).tendsto_subseq hx
  have hd : Tendsto (fun j => (x (φ j)).1) atTop (𝓝 a.1) :=
    continuous_fst.tendsto a |>.comp hlim
  have hb : Tendsto (fun j => (x (φ j)).2) atTop (𝓝 a.2) :=
    continuous_snd.tendsto a |>.comp hlim
  refine ⟨φ,a.1,a.2,hφ,?_,?_,hd,hb⟩
  · exact ge_of_tendsto hd (Eventually.of_forall fun j => hxpos (φ j))
  · have hsum := hd.add hb.norm
    have hconst : (fun j => (x (φ j)).1 + ‖(x (φ j)).2‖) = fun _ => (1:ℝ) :=
      funext fun j => hxunit (φ j)
    rw [hconst] at hsum
    exact tendsto_nhds_unique hsum tendsto_const_nhds
end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma WeightedProfileBounds.subseq {Ω : Set Plane} {S c : ℕ → ℝ} {B : ℕ → Plane}
    {U : ℕ → Plane → ℝ} {V : Plane → EReal}
    (h : WeightedProfileBounds Ω S B U c V) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    WeightedProfileBounds Ω (S∘φ) (B∘φ) (U∘φ) (c∘φ) V := by
  constructor
  · intro f hf F hF hFΩ
    exact hφ.limsup_comp_le_limsup.trans (h.upper f hf F hF hFΩ)
  · intro f hf G hG hGΩ
    exact (h.lower f hf G hG hGΩ).trans hφ.liminf_le_liminf_comp

theorem full_test_of_profile_oai
    {Ω : Set Plane} {p U : ℕ → Plane → ℝ} {V : Plane → EReal}
    {B : ℕ → Plane} {S K e c : ℕ → ℝ} {Cp : ℝ}
    (hΩ : IsOpen Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω)
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) Ω)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hc : ∀ j, 0 < c j)
    (hK : Tendsto (fun j => K j/(S j+‖B j‖)) atTop (𝓝 0))
    (hpbound : ∀ j x, x∈Ω → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x∈Ω →
      |(K j)^2*coordPartial (p j) i x/(S j*(S j+‖B j‖))|≤e j)
    (hPDE : ∀ j x, x∈Ω → euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (hV : UpperSemicontinuousOn V Ω) (hprofile : WeightedProfileBounds Ω S B U c V) :
    FullTestProperty Ω V := by
  obtain ⟨φ,d,b,hφ,hd,hdb,hSd,hBb⟩ := extract_normalized_parameters S B hSpos
  apply full_test_of_shifted hΩ hV hd hdb
  apply shifted_test_of_profile (S:=S∘φ) (B:=B∘φ) (p:=p∘φ) (U:=U∘φ)
    (D:=fun j => S (φ j)+‖B (φ j)‖) (K:=K∘φ) (e:=e∘φ) (c:=c∘φ)
    hΩ (fun j => hp (φ j)) (fun j => hU (φ j)) (fun j => hSpos (φ j))
    (hS.comp hφ.tendsto_atTop) (fun j => hc (φ j)) (fun _ => rfl)
    hBb hSd (hK.comp hφ.tendsto_atTop) (fun j => hpbound (φ j))
    (he.comp hφ.tendsto_atTop) (fun j => hpgrad (φ j)) (fun j => hPDE (φ j))
    hV (hprofile.subseq hφ.tendsto_atTop)

end SharpNodal.Profiles

end
end
end

end OAI
end

theorem solution : type_of% @OAI.SharpNodal.Profiles.full_test_of_profile_oai := @OAI.SharpNodal.Profiles.full_test_of_profile_oai
