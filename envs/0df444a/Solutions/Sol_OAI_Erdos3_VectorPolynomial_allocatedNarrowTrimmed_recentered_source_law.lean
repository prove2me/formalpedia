-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_recentered_source_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T22:04:05.935918+00:00
-- url     : https://prove2.me/submissions/43747f1a-054f-47a0-b394-c0db9e97ef08

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B159
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedNarrowTrimmed_shifted_vector_site_error

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Matrix ENNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integerResidueMatrix_eq_iff_dvd_sub {I J : Type*}
    (C D : Matrix I J ℤ) (m : ℕ) :
    integerResidueMatrix C m = integerResidueMatrix D m ↔
      ∀ i j, (m : ℤ) ∣ C i j - D i j := by
  constructor
  · intro h i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (C i j - D i j) m).mp
    rw [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun (congrFun h i) j)
  · intro h
    ext i j
    change (C i j : ZMod m) = (D i j : ZMod m)
    apply sub_eq_zero.mp
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (C i j - D i j) m).mpr (h i j)
    simpa only [Int.cast_sub] using hz

theorem integerResidueMatrix_reduce {I J : Type*} (C D : Matrix I J ℤ)
    {m n : ℕ} (hmn : m ∣ n) (h : integerResidueMatrix C n = integerResidueMatrix D n) :
    integerResidueMatrix C m = integerResidueMatrix D m := by
  apply (integerResidueMatrix_eq_iff_dvd_sub C D m).mpr
  have hd : (m : ℤ) ∣ (n : ℤ) := by exact_mod_cast hmn
  exact fun i j => hd.trans ((integerResidueMatrix_eq_iff_dvd_sub C D n).mp h i j)

theorem residueMatrixShift_spec {I J : Type*} [Fintype I] [Fintype J]
    (C D : Matrix I J ℤ) (q m : ℕ) (hq : 0 < q)
    (h : integerResidueMatrix C (q * m) = integerResidueMatrix D (q * m)) (r : J → ℤ) :
    (∀ i, (q : ℤ) * residueMatrixShift C D q r i = ((C - D) *ᵥ r) i) ∧
      residueMatrixShift C D q r ∈ integerScalarLattice I (m : ℤ) := by
  classical
  have hd (i) (j) : (q : ℤ) * (m : ℤ) ∣ C i j - D i j := by
    simpa only [Nat.cast_mul] using (integerResidueMatrix_eq_iff_dvd_sub C D (q * m)).mp h i j
  choose Z hZ using hd
  let t : I → ℤ := fun i => ∑ j, Z i j * r j
  have he (i) : ((C - D) *ᵥ r) i = (q : ℤ) * ((m : ℤ) * t i) := by
    change (∑ j, (C i j - D i j) * r j) = _
    simp_rw [hZ]
    dsimp only [t]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hs (i) : residueMatrixShift C D q r i = (m : ℤ) * t i := by
    unfold residueMatrixShift
    rw [he, Int.mul_ediv_cancel_left _ hq0]
  refine ⟨fun i => by rw [hs, he], ?_⟩
  refine ⟨t, ?_⟩
  funext i
  exact (hs i).symm

theorem residueMatrixShift_bound {I J : Type*} [Fintype I] [Fintype J]
    (C D : Matrix I J ℤ) (q m : ℕ) (hq : 0 < q)
    (h : integerResidueMatrix C (q * m) = integerResidueMatrix D (q * m))
    (r : J → ℤ) (hr : ∀ j, |(r j : ℝ)| ≤ q) (i : I) :
    |(residueMatrixShift C D q r i : ℝ)| ≤ ∑ j, |((C i j - D i j : ℤ) : ℝ)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have he := (residueMatrixShift_spec C D q m hq h r).1 i
  have heR : (q : ℝ) * (residueMatrixShift C D q r i : ℝ) = (((C - D) *ᵥ r) i : ℝ) := by
    exact_mod_cast he
  have hm : (q : ℝ) * |(residueMatrixShift C D q r i : ℝ)| =
      |∑ j, ((C i j - D i j : ℤ) : ℝ) * (r j : ℝ)| := by
    rw [← abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q), ← abs_mul, heR]
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Int.cast_sum, Int.cast_mul]
  apply (mul_le_mul_iff_right₀ hqR).mp
  rw [hm]
  calc
    _ ≤ ∑ j, |((C i j - D i j : ℤ) : ℝ) * (r j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |((C i j - D i j : ℤ) : ℝ)| * (q : ℝ) :=
      Finset.sum_le_sum (fun j _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hr j) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm.trans (mul_comm _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedDensityL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem positive_mass_inverse_difference {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    J * |1 / I - 1 / J| = |I - J| / I := by
  have he : 1 / I - 1 / J = (J - I) / (I * J) := by field_simp
  rw [he, abs_div, abs_mul, abs_of_pos hI, abs_of_pos hJ, abs_sub_comm J I]
  field_simp

theorem normalized_density_l1 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hg0 : ∀ x, 0 ≤ g x) (hI : 0 < ∫ x, f x ∂μ) (hJ : 0 < ∫ x, g x ∂μ) :
    (∫ x, |f x / (∫ y, f y ∂μ) - g x / (∫ y, g y ∂μ)| ∂μ) ≤
      2 * (∫ x, |f x - g x| ∂μ) / (∫ x, f x ∂μ) := by
  let I := ∫ x, f x ∂μ
  let J := ∫ x, g x ∂μ
  have hI' : 0 < I := hI
  have hJ' : 0 < J := hJ
  have habs : Integrable (fun x => |f x - g x|) μ := (hf.sub hg).abs
  have hpoint (x : X) : |f x / I - g x / J| ≤
      |f x - g x| / I + g x * |1 / I - 1 / J| := by
    have he : f x / I - g x / J = (f x - g x) / I + g x * (1 / I - 1 / J) := by ring
    rw [he]
    simpa only [abs_div, abs_of_pos hI', abs_mul, abs_of_nonneg (hg0 x)] using
      abs_add_le ((f x - g x) / I) (g x * (1 / I - 1 / J))
  have hbound := integral_mono ((hf.div_const I).sub (hg.div_const J)).abs
    ((habs.div_const I).add (hg.mul_const |1 / I - 1 / J|)) hpoint
  dsimp only [Pi.sub_apply, Pi.add_apply] at hbound
  rw [integral_add (habs.div_const I) (hg.mul_const _), integral_div, integral_mul_const] at hbound
  change (∫ x, |f x / I - g x / J| ∂μ) ≤
    (∫ x, |f x - g x| ∂μ) / I + J * |1 / I - 1 / J| at hbound
  rw [positive_mass_inverse_difference hI' hJ'] at hbound
  have hm := abs_integral_le_integral_abs (f := fun x => f x - g x) (μ := μ)
  rw [integral_sub hf hg] at hm
  have hd := div_le_div_of_nonneg_right hm hI'.le
  change |I - J| / I ≤ (∫ x, |f x - g x| ∂μ) / I at hd
  change (∫ x, |f x / I - g x / J| ∂μ) ≤ 2 * (∫ x, |f x - g x| ∂μ) / I
  calc
    _ ≤ (∫ x, |f x - g x| ∂μ) / I + |I - J| / I := hbound
    _ ≤ (∫ x, |f x - g x| ∂μ) / I + (∫ x, |f x - g x| ∂μ) / I :=
      by linarith
    _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SampledWeightCellLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem abs_sub_eq_add_sub_two_min (x y : ℝ) : |x - y| = x + y - 2 * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem measured_density_overlap {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfmass : (∫ x, f x ∂μ) = 1) (hgmass : (∫ x, g x ∂μ) = 1) :
    (∫ x, min (f x) (g x) ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      (∫ x, |f x-g x| ∂μ) = 2 - 2 * ∫ x, min (f x) (g x) ∂μ := by
  have hm : Integrable (fun x => min (f x) (g x)) μ := hf.inf hg
  have hsum : Integrable (fun x => f x + g x) μ := hf.add hg
  constructor
  · exact ⟨integral_nonneg (fun x => le_min (hf0 x) (hg0 x)),
      (integral_mono hm hf (fun x => min_le_left _ _)).trans_eq hfmass⟩
  · simp_rw [abs_sub_eq_add_sub_two_min]
    rw [integral_sub hsum (hm.const_mul 2), integral_add hf hg,
      integral_const_mul, hfmass, hgmass]
    norm_num

theorem tensor_density_l1_le_sum {D : Type*} [Fintype D] [DecidableEq D]
    {X : D → Type*} [∀ d, MeasurableSpace (X d)] (μ : ∀ d, Measure (X d)) [∀ d, SigmaFinite (μ d)]
    (f g : ∀ d, X d → ℝ) (hf : ∀ d, Integrable (f d) (μ d)) (hg : ∀ d, Integrable (g d) (μ d))
    (hf0 : ∀ d x, 0 ≤ f d x) (hg0 : ∀ d x, 0 ≤ g d x)
    (hfmass : ∀ d, (∫ x, f d x ∂μ d) = 1) (hgmass : ∀ d, (∫ x, g d x ∂μ d) = 1) :
    (∫ x, |(∏ d, f d (x d)) - ∏ d, g d (x d)| ∂Measure.pi μ) ≤
      ∑ d, ∫ x, |f d x-g d x| ∂μ d := by
  let F := fun x : ∀ d, X d => ∏ d, f d (x d)
  let G := fun x : ∀ d, X d => ∏ d, g d (x d)
  let H := fun x : ∀ d, X d => ∏ d, min (f d (x d)) (g d (x d))
  let mass := fun d => ∫ x, min (f d x) (g d x) ∂μ d
  have hF : Integrable F (Measure.pi μ) := Integrable.fintype_prod_dep hf
  have hG : Integrable G (Measure.pi μ) := Integrable.fintype_prod_dep hg
  have hH : Integrable H (Measure.pi μ) := Integrable.fintype_prod_dep (fun d => (hf d).inf (hg d))
  have hpoint (x : ∀ d, X d) : |F x-G x| ≤ F x+G x-2*H x := by
    have hl : H x ≤ F x := Finset.prod_le_prod
      (fun d _ => le_min (hf0 d _) (hg0 d _)) (fun d _ => min_le_left _ _)
    have hr : H x ≤ G x := Finset.prod_le_prod
      (fun d _ => le_min (hf0 d _) (hg0 d _)) (fun d _ => min_le_right _ _)
    rw [abs_sub_eq_add_sub_two_min]
    have hh := le_min hl hr
    linarith
  have hFm : (∫ x, F x ∂Measure.pi μ) = 1 := by
    rw [show F = (fun x => ∏ d, f d (x d)) from rfl, integral_fintype_prod_eq_prod]
    simp only [hfmass, Finset.prod_const_one]
  have hGm : (∫ x, G x ∂Measure.pi μ) = 1 := by
    rw [show G = (fun x => ∏ d, g d (x d)) from rfl, integral_fintype_prod_eq_prod]
    simp only [hgmass, Finset.prod_const_one]
  have hHm : (∫ x, H x ∂Measure.pi μ) = ∏ d, mass d :=
    integral_fintype_prod_eq_prod (fun d x => min (f d x) (g d x))
  have hsum : Integrable (fun x => F x + G x) (Measure.pi μ) := hF.add hG
  have he := integral_mono (hF.sub hG).abs ((hF.add hG).sub (hH.const_mul 2)) hpoint
  change (∫ x, |F x-G x| ∂Measure.pi μ) ≤
    ∫ x, F x+G x-2*H x ∂Measure.pi μ at he
  rw [integral_sub hsum (hH.const_mul 2), integral_add hF hG,
    integral_const_mul, hFm, hGm, hHm] at he
  have hm (d) := measured_density_overlap (μ d) (f d) (g d) (hf d) (hg d)
    (hf0 d) (hg0 d) (hfmass d) (hgmass d)
  have hp := one_sub_sum_le_positive_prod Finset.univ mass (fun d => 1-mass d)
    (fun d _ => (hm d).1.1) (fun d _ => ⟨by linarith [(hm d).1.2], by linarith [(hm d).1.1]⟩)
    (fun d _ => by linarith)
  have hh : (∑ d, ∫ x, |f d x-g d x| ∂μ d) = 2 * ∑ d, (1-mass d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [(hm d).2]
    dsimp only [mass]
    ring
  rw [hh]
  change (∫ x, |F x-G x| ∂Measure.pi μ) ≤ _
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ENNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_real_mass {X : Type*} (p : PMF X) : (∑' x, (p x).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (p.apply_ne_top), p.tsum_coe, ENNReal.toReal_one]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Function _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_finite_sum {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (y : Y) :
    (p.map F y).toReal = ∑ x ∈ S, (p x).toReal * (if F x = y then 1 else 0) := by
  rw [pmf_map_toReal_indicator]
  exact (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hp x hx, zero_mul])).tsum_eq

theorem pmf_image_finite_expectation {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (hT : ∀ x ∈ S, F x ∈ T) (φ : Y → ℂ) :
    (∑' x, ((p x).toReal : ℂ) * φ (F x)) =
      ∑ y ∈ T, ((p.map F y).toReal : ℂ) * φ y := by
  have hs : (∑' x, ((p x).toReal : ℂ) * φ (F x)) =
      ∑ x ∈ S, ((p x).toReal : ℂ) * φ (F x) :=
    (hasSum_sum_of_ne_finset_zero (fun x hx => by
      rw [hp x hx, Complex.ofReal_zero, zero_mul])).tsum_eq
  rw [hs]
  simp_rw [pmf_map_finite_sum p S hp F, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single (F x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · intro hn
    exact (hn (hT x hx)).elim

theorem pmf_image_finite_test_error {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (hT : ∀ x ∈ S, F x ∈ T)
    (ψ φ : Y → ℂ) {A E : ℝ} (hA : 0 < A)
    (he : ∀ y ∈ T, ‖((A * (p.map F y).toReal : ℝ) : ℂ) - ψ y‖ ≤ E) :
    ‖(∑' x, ((p x).toReal : ℂ) * φ (F x)) -
      ∑ y ∈ T, (ψ y / (A : ℂ)) * φ y‖ ≤
        (E / A) * ∑ y ∈ T, ‖φ y‖ := by
  rw [pmf_image_finite_expectation p S hp F T hT φ, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ y ∈ T, (E / A) * ‖φ y‖ := by
      apply Finset.sum_le_sum
      intro y hy
      have hid : ((p.map F y).toReal : ℂ) - ψ y / (A : ℂ) =
          (((A * (p.map F y).toReal : ℝ) : ℂ) - ψ y) / (A : ℂ) := by
        rw [Complex.ofReal_mul, sub_div, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hA.ne')]
      rw [← sub_mul, norm_mul, hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (he y hy) hA.le) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_add_right {Y : Type*} [AddGroup Y] (p : PMF Y) (s y : Y) :
    p.map (fun v => v + s) y = p (y - s) := by
  have h := pmf_map_injective_at p (fun v => v + s) (fun _ _ h => add_right_cancel h) (y-s)
  simpa only [sub_add_cancel] using h

theorem pmf_map_image_add_right {X Y : Type*} [AddGroup Y]
    (p : PMF X) (F : X → Y) (s y : Y) :
    p.map (fun x => F x + s) y = p.map F (y-s) := by
  rw [show (fun x => F x + s) = (fun v => v+s) ∘ F from rfl, ← PMF.map_comp]
  exact pmf_map_add_right (p.map F) s y

theorem pmf_image_shifted_finite_test_error {X Y : Type*} [AddGroup Y] [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (s : Y) (T : Finset Y) (hT : ∀ x ∈ S, F x + s ∈ T)
    (ψ φ : Y → ℂ) {A E : ℝ} (hA : 0 < A)
    (he : ∀ y ∈ T, ‖((A * (p.map F (y-s)).toReal : ℝ) : ℂ) - ψ y‖ ≤ E) :
    ‖(∑' x, ((p x).toReal : ℂ) * φ (F x+s)) -
      ∑ y ∈ T, (ψ y / (A : ℂ)) * φ y‖ ≤ (E/A) * ∑ y ∈ T, ‖φ y‖ := by
  apply pmf_image_finite_test_error p S hp (fun x => F x+s) T hT ψ φ hA
  simpa only [pmf_map_image_add_right] using he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialStarCoordinates
namespace OAI

section

namespace Erdos3

theorem spatialStar_vertex {I R : Type*} [AddCommMonoid R] (v : (Unit ⊕ I) → R) (i : Unit ⊕ I) :
    spatialStar v i = v (.inl ()) + ∑ j ∈ spatialStarVertex i, v (.inr j) := by
  cases i with
  | inl i => cases i; simp [spatialStar, spatialStarVertex]
  | inr i => simp [spatialStar, spatialStarVertex]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ENNReal

theorem pi_count_measure {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] [∀ i, Countable (X i)] :
    Measure.pi (fun i => (Measure.count : Measure (X i))) =
      (Measure.count : Measure (∀ i, X i)) := by
  apply Measure.ext_of_singleton
  intro x
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators ENNReal

variable {E I Z O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [Fintype I] [Fintype Z] (o : OrthonormalBasis I ℝ E)

variable [Fintype O]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SubspaceLayeredModeSmoothRemoval
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem smoothProductPMF_toReal_zero_off {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (x : I → ℤ)
    (hx : x ∉ rectangularWeightIndices 0 S 1) : (smoothProductPMF S hS x).toReal = 0 := by
  have hz := rectangularWeight_zero_off_indices (smoothProductProfile I) 0 S hS
    (smoothProductProfile_zero_outside I) x hx
  simp only [rectangularWeight, rectangularLatticePoint_zero_origin] at hz
  simp only [smoothProductPMF, realWeightPMF_apply, hz, zero_div]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators NNReal Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators NNReal Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators NNReal Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators NNReal Classical

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

theorem rectangularWeightIndices_zero_mono {I : Type*} [Fintype I]
    {V W : I → ℝ} (hVW : ∀ i, V i ≤ W i) :
    rectangularWeightIndices 0 V 1 ⊆ rectangularWeightIndices 0 W 1 := by
  intro z hz
  apply (mem_rectangularWeightIndices_zero_iff W z).mpr
  exact fun i => (rectangularWeightIndices_zero_bound V hz i).trans (hVW i)

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators

namespace BooleanCubeKernel

end BooleanCubeKernel

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace BooleanCubeKernel

end BooleanCubeKernel

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteCountDensityError
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem count_integrable_of_zero_off_finset {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (s : Finset X) (f : X → ℝ)
    (hs : ∀ x ∉ s, f x = 0) : Integrable f Measure.count := by
  apply integrable_count_iff.mpr
  exact (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hs x hx, norm_zero])).summable

theorem count_integral_eq_sum_of_zero_off_finset {X : Type*} [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (s : Finset X) (f : X → ℝ) (hs : ∀ x ∉ s, f x = 0) :
    (∫ x, f x ∂Measure.count) = ∑ x ∈ s, f x := by
  rw [integral_countable (count_integrable_of_zero_off_finset s f hs)]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  exact (hasSum_sum_of_ne_finset_zero hs).tsum_eq

theorem count_density_l1_le_card {X : Type*} [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (s : Finset X) (f g : X → ℝ) (hf : ∀ x ∉ s, f x = 0) (hg : ∀ x ∉ s, g x = 0)
    {ε : ℝ} (he : ∀ x ∈ s, |f x - g x| ≤ ε) :
    (∫ x, |f x - g x| ∂Measure.count) ≤ (s.card : ℝ) * ε := by
  rw [count_integral_eq_sum_of_zero_off_finset s _ (fun x hx => by
    rw [hf x hx, hg x hx, sub_self, abs_zero])]
  exact (Finset.sum_le_sum he).trans_eq (by simp)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ControlledJointGrid
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_real_integral_count {X : Type*} [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : PMF X) :
    (∫ x, (p x).toReal ∂Measure.count) = 1 := by
  rw [integral_countable (pmf_real_integrable p)]
  simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    using pmf_real_mass p

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem realDensityMeasure_integral_complex {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (φ : X → ℂ) :
    (∫ x, φ x ∂realDensityMeasure μ f) = ∫ x, (f x : ℂ) * φ x ∂μ := by
  unfold realDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), Complex.real_smul]

theorem density_bounded_complex_test_error {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (φ : X → ℂ) (hφ : Measurable φ) {B : ℝ} (hb : ∀ x, ‖φ x‖ ≤ B) :
    ‖(∫ x, (f x : ℂ) * φ x ∂μ) - ∫ x, (g x : ℂ) * φ x ∂μ‖ ≤
      B * ∫ x, |f x - g x| ∂μ := by
  have hfi : Integrable (fun x => (f x : ℂ) * φ x) μ :=
    hf.ofReal.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hgi : Integrable (fun x => (g x : ℂ) * φ x) μ :=
    hg.ofReal.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  rw [← integral_sub hfi hgi]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    _ ≤ ∫ x, B * |f x - g x| ∂μ := by
      apply integral_mono (hfi.sub hgi).norm ((hf.sub hg).abs.const_mul B)
      intro x
      change ‖(f x : ℂ) * φ x - (g x : ℂ) * φ x‖ ≤ B * |f x - g x|
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simpa only [mul_comm B] using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg (f x - g x))
    _ = _ := integral_const_mul _ _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalSpatialSiteComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem principalSpatialColumns_residue {D α N : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} (m : ℕ) (c : N → ℤ) (index : N → PrincipalTupleIndex B h)
    (y : PrincipalIntegerTuples B h α L) :
    integerResidueMatrix (principalSpatialColumns c index y) m =
      principalSpatialResidueColumns m c index (principalResidueLabel m y) := by
  ext i n
  cases i <;> simp [integerResidueMatrix, principalSpatialColumns, scalarTupleSpatialColumns,
    tupleColumnMatrix, scalarTupleColumn, principalSpatialResidueColumns, principalResidueLabel]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PhysicalCubeMatrix
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

theorem physicalCubeRootDifferences_star {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) (x : X) (i : Unit ⊕ α) :
    spatialStar (physicalCubeRootDifferences root D base z x) i =
      jointIntegerPhysicalSite (integerAffineCube root D (spatialStarVertex i)) (base, z) x := by
  rw [spatialStar_vertex, physicalCubeRootDifferences_vertex]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem trimmedSpatial_residue_scale {K X : Type*} (B τ : ℝ) (N modulus : X → ℕ) (x : X) :
    (fun k => residueProfileWidth modulus (trimmedSpatialWidths (K := K) B τ N) (k, x)) =
      physicalSpatialInputScale K (trimmedSpatialRootScale τ N modulus x)
        (trimmedSpatialSlopeScale B τ N modulus x) := by
  funext k
  cases k <;> simp only [residueProfileWidth, trimmedSpatialWidths, centeredSpatialWidths,
    physicalSpatialInputScale, Option.elim', trimmedSpatialRootScale, trimmedSpatialSlopeScale, one_mul] <;> ring

theorem trimmedSpatial_scales_pos {X : Type*} {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 < τ)
    (N modulus : X → ℕ) (x : X) (hN : 0 < N x) (hq : 0 < modulus x) :
    0 < trimmedSpatialRootScale τ N modulus x ∧ 0 < trimmedSpatialSlopeScale B τ N modulus x := by
  have hn : (0 : ℝ) < N x := by exact_mod_cast hN
  have hq' : (0 : ℝ) < modulus x := by exact_mod_cast hq
  unfold trimmedSpatialRootScale trimmedSpatialSlopeScale
  constructor <;> positivity

theorem trimmedSpatial_scale_ratio {X : Type*} {B τ : ℝ} (hB : 0 ≤ B)
    (N modulus : X → ℕ) (x : X) :
    trimmedSpatialRootScale τ N modulus x =
      (1 + B) * trimmedSpatialSlopeScale B τ N modulus x := by
  have hb : 1 + B ≠ 0 := ne_of_gt (by linarith)
  unfold trimmedSpatialRootScale trimmedSpatialSlopeScale
  field_simp

theorem trimmedSpatial_scale_lower {X : Type*} {B τ ρ : ℝ}
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (N modulus : X → ℕ) (x : X) (hq : 0 < modulus x)
    (hlarge : 8 * (1 + B) * (modulus x : ℝ) * ρ ≤ τ * (N x : ℝ)) :
    ρ ≤ trimmedSpatialRootScale τ N modulus x ∧ ρ ≤ trimmedSpatialSlopeScale B τ N modulus x := by
  have hq' : (0 : ℝ) < modulus x := by exact_mod_cast hq
  have hb : (0 : ℝ) < 8 * (1 + B) := by positivity
  have hs : ρ ≤ trimmedSpatialSlopeScale B τ N modulus x := by
    unfold trimmedSpatialSlopeScale
    apply (le_div_iff₀ hq').mpr
    apply (le_div_iff₀ hb).mpr
    nlinarith [hlarge]
  refine ⟨?_, hs⟩
  unfold trimmedSpatialRootScale
  apply (le_div_iff₀ hq').mpr
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  nlinarith [mul_nonneg hB (mul_nonneg hq'.le hρ)]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalAmbientVolumeRatio
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

theorem centeredPhysicalCubeMap_eq {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) :
    centeredPhysicalCubeMap (X := X) root D = physicalCubeRootDifferences root D 0 := by
  funext z d i
  cases i <;> simp only [centeredPhysicalCubeMap, physicalCubeRootDifferences,
    physicalCubeOffset, Pi.zero_apply, zero_add, Matrix.mulVec, dotProduct]

theorem centeredPhysicalCubeMap_mem_window {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (Q : Option K × X → ℝ)
    (z : Option K × X → ℤ) (hz : z ∈ rectangularWeightIndices 0 Q 1) :
    centeredPhysicalCubeMap root D z ∈ centeredPhysicalCubeWindow root D Q := by
  classical
  exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

theorem spatialStarVertex_root_sum {K α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) {W : ℝ} (hW : 0 ≤ W)
    (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (hD : ∀ i, (∑ k, |(D i k : ℝ)|) ≤ W) (i : Unit ⊕ α) :
    (∑ k, |(integerAffineCube root D (spatialStarVertex i) k : ℝ)|) ≤ 2 * W := by
  cases i with
  | inl i =>
    simpa only [spatialStarVertex, Sum.elim_inl, integerAffineCube, Finset.sum_empty,
      add_zero] using hroot.trans (by linarith : W ≤ 2 * W)
  | inr i =>
    simp only [spatialStarVertex, Sum.elim_inr, integerAffineCube, Finset.sum_singleton, Int.cast_add]
    calc
      _ ≤ ∑ k, (|(root k : ℝ)| + |(D i k : ℝ)|) :=
        Finset.sum_le_sum (fun _ _ => abs_add_le _ _)
      _ = (∑ k, |(root k : ℝ)|) + ∑ k, |(D i k : ℝ)| := Finset.sum_add_distrib
      _ ≤ 2 * W := by linarith [hD i]

theorem centeredPhysicalCubeWindow_star_bound {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (Q : Option K × X → ℝ) (H T : X → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hH : ∀ d, 0 < H d) (hT : ∀ d, 0 ≤ T d)
    (hscale : ∀ d, H d = (1 + W) * T d)
    (hQ : ∀ d, (fun k => Q (k, d)) = physicalSpatialInputScale K (H d) (T d))
    (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (hD : ∀ i, (∑ k, |(D i k : ℝ)|) ≤ W)
    (v : X → (Unit ⊕ α) → ℤ) (hv : v ∈ centeredPhysicalCubeWindow root D Q) :
    ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ 3 := by
  classical
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  intro d i
  have hb := integerPhysicalSite_abs_bound (integerAffineCube root D (spatialStarVertex i)) Q z
    (rectangularWeightIndices_zero_bound Q hz) d
  have hq0 : Q (none, d) = H d := congrFun (hQ d) none
  have hqs (k : K) : Q (some k, d) = T d := congrFun (hQ d) (some k)
  simp only [physicalSiteWidth, hq0, hqs, ← Finset.sum_mul] at hb
  have hs := mul_le_mul_of_nonneg_right (spatialStarVertex_root_sum root D hW hroot hD i) (hT d)
  have hbound : |(integerPhysicalSite (integerAffineCube root D (spatialStarVertex i)) z d : ℝ)| ≤
      3 * H d := by nlinarith [hscale d, hT d]
  rw [centeredPhysicalCubeMap_eq, physicalCubeRootDifferences_star]
  simpa only [jointIntegerPhysicalSite, zero_add, abs_div, abs_of_pos (hH d)] using
    (div_le_iff₀ (hH d)).mpr hbound

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialShiftedWindowError
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

theorem spatialStar_add {I R : Type*} [AddCommMonoid R]
    (v w : (Unit ⊕ I) → R) : spatialStar (v + w) = spatialStar v + spatialStar w := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => simp only [spatialStar, Sum.elim_inr, Pi.add_apply]; abel

namespace BooleanCubeKernel

open scoped BigOperators

theorem mem_spatialWindow_scaled_iff {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ d, 0 < H d) (b : ℝ) (v : X → (Unit ⊕ α) → ℤ) :
    v ∈ spatialWindow H b ↔ ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b := by
  rw [mem_spatialWindow_iff]
  simp only [abs_div, abs_of_pos (hH _), div_le_iff₀ (hH _), mul_comm]

theorem spatialWindow_add {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) {a b : ℝ} {v s : X → (Unit ⊕ α) → ℤ}
    (hv : v ∈ spatialWindow H a) (hs : s ∈ spatialWindow H b) :
    v + s ∈ spatialWindow H (a + b) := by
  apply (mem_spatialWindow_iff H (a+b) _).mpr
  intro d i
  change |((spatialStar (v d + s d) i : ℤ) : ℝ)| ≤ _
  rw [spatialStar_add, Pi.add_apply, Int.cast_add]
  calc
    _ ≤ |((spatialStar (v d) i : ℤ) : ℝ)| + |((spatialStar (s d) i : ℤ) : ℝ)| := abs_add_le _ _
    _ ≤ H d * a + H d * b := add_le_add
      ((mem_spatialWindow_iff H a v).mp hv d i) ((mem_spatialWindow_iff H b s).mp hs d i)
    _ = _ := (mul_add _ _ _).symm

theorem spatialWindow_of_coordinate_bound {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ d, 0 ≤ H d) {t : ℝ} (ht : 0 ≤ t)
    (s : X → (Unit ⊕ α) → ℤ) (hs : ∀ d i, |(s d i : ℝ)| ≤ H d * t) :
    s ∈ spatialWindow H (2*t) := by
  apply (mem_spatialWindow_iff H (2*t) s).mpr
  intro d i
  cases i with
  | inl i =>
    change |(s d (.inl ()) : ℝ)| ≤ _
    nlinarith [hs d (.inl ()), mul_nonneg (hH d) ht]
  | inr i =>
    change |((s d (.inl ()) + s d (.inr i) : ℤ) : ℝ)| ≤ _
    rw [Int.cast_add]
    exact (abs_add_le _ _).trans (by nlinarith [hs d (.inl ()), hs d (.inr i)])

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

namespace BooleanCubeKernel

variable {X I : Type*} [Fintype X] [Fintype I]

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

variable {X I : Type*} [Fintype X] [Fintype I]

end BooleanCubeKernel
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedProductTestError
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedSmoothSamples_count_integral (a S : ℝ) (hS : 0 < S) :
    (∫ k : ℤ, smoothProbabilityProfile (((k : ℝ) - a) / S) ∂Measure.count) =
      shiftedSmoothSampleSum a S := by
  have hi := count_integrable_of_zero_off_finset (sampledWeightIndices a S 1)
    (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - a) / S))
    (sampledWeight_zero_off_indices smoothProbabilityProfile hS smoothProbabilityProfile_zero_outside)
  simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul,
    shiftedSmoothSampleSum] using integral_countable hi

theorem shiftedSmoothSamples_center_l1 (a b S : ℝ) (hS : 1 ≤ S) :
    (∫ k : ℤ, |smoothProbabilityProfile (((k : ℝ) - a) / S) -
      smoothProbabilityProfile (((k : ℝ) - b) / S)| ∂Measure.count) ≤
      6 * S * ((probabilityProfileLipschitz : ℝ) * (|a - b| / S)) := by
  classical
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  let U := sampledWeightIndices a S 1 ∪ sampledWeightIndices b S 1
  have ha (k : ℤ) (hk : k ∉ U) : smoothProbabilityProfile (((k : ℝ) - a) / S) = 0 :=
    sampledWeight_zero_off_indices smoothProbabilityProfile hS0 smoothProbabilityProfile_zero_outside
      k (fun h => hk (Finset.mem_union_left _ h))
  have hb (k : ℤ) (hk : k ∉ U) : smoothProbabilityProfile (((k : ℝ) - b) / S) = 0 :=
    sampledWeight_zero_off_indices smoothProbabilityProfile hS0 smoothProbabilityProfile_zero_outside
      k (fun h => hk (Finset.mem_union_right _ h))
  have hc : (U.card : ℝ) ≤ 6 * S := by
    have hu : (U.card : ℝ) ≤ (sampledWeightIndices a S 1).card +
        ((sampledWeightIndices b S 1).card : ℝ) := by
      exact_mod_cast Finset.card_union_le (sampledWeightIndices a S 1) (sampledWeightIndices b S 1)
    have hca := sampledWeightIndices_card_le a S 1 hS0.le zero_le_one
    have hcb := sampledWeightIndices_card_le b S 1 hS0.le zero_le_one
    linarith
  have he (k : ℤ) : |smoothProbabilityProfile (((k : ℝ) - a) / S) -
      smoothProbabilityProfile (((k : ℝ) - b) / S)| ≤
      (probabilityProfileLipschitz : ℝ) * (|a - b| / S) := by
    have h := smoothProbabilityProfile_lipschitz.norm_sub_le
      (((k : ℝ) - a) / S) (((k : ℝ) - b) / S)
    have hid : ((k : ℝ) - a) / S - ((k : ℝ) - b) / S = (b - a) / S := by ring
    simpa only [Real.norm_eq_abs, hid, abs_div, abs_of_pos hS0, abs_sub_comm b a] using h
  exact (count_density_l1_le_card U _ _ ha hb (fun k _ => he k)).trans
    (mul_le_mul_of_nonneg_right hc (by positivity))

theorem shiftedSmoothCoefficientPMF_center_l1 (a b S : ℝ) (hS : 0 < S)
    (hZa : 0 < shiftedSmoothSampleSum a S) (hZb : 0 < shiftedSmoothSampleSum b S)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) :
    (∫ k : ℤ, |(shiftedSmoothCoefficientPMF a S hS hZa k).toReal -
      (shiftedSmoothCoefficientPMF b S hS hZb k).toReal| ∂Measure.count) ≤
      24 * (probabilityProfileLipschitz : ℝ) * |a - b| / S := by
  have hS1 : 1 ≤ S := by linarith [probabilityProfileLipschitz_one_le]
  have hi (c : ℝ) := count_integrable_of_zero_off_finset (sampledWeightIndices c S 1)
    (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - c) / S))
    (sampledWeight_zero_off_indices smoothProbabilityProfile hS smoothProbabilityProfile_zero_outside)
  have h := normalized_density_l1 Measure.count _ _ (hi a) (hi b)
    (fun _ => (smoothProbabilityProfile_range _).1)
    (by rw [shiftedSmoothSamples_count_integral a S hS]; exact hZa)
    (by rw [shiftedSmoothSamples_count_integral b S hS]; exact hZb)
  rw [shiftedSmoothSamples_count_integral a S hS, shiftedSmoothSamples_count_integral b S hS] at h
  simp only [shiftedSmoothCoefficientPMF_apply]
  apply h.trans
  have hr : S / shiftedSmoothSampleSum a S ≤ 2 :=
    (div_le_iff₀ hZa).mpr (by linarith [(shiftedSmoothSampleSum_bounds a hlarge).1])
  calc
    _ ≤ 2 * (6 * S * ((probabilityProfileLipschitz : ℝ) * (|a - b| / S))) /
        shiftedSmoothSampleSum a S :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (shiftedSmoothSamples_center_l1 a b S hS1) (by norm_num)) hZa.le
    _ = 12 * (S / shiftedSmoothSampleSum a S) *
        ((probabilityProfileLipschitz : ℝ) * (|a - b| / S)) := by ring
    _ ≤ 12 * 2 * ((probabilityProfileLipschitz : ℝ) * (|a - b| / S)) := by
      gcongr
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {X Y : Type*} [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [Countable Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

theorem pmf_image_complex_sum_eq_count_integral (p : PMF X) (f : X → Y)
    (φ : Y → ℂ) {B : ℝ} (hb : ∀ y, ‖φ y‖ ≤ B) :
    (∑' x, ((p x).toReal : ℂ) * φ (f x)) =
      ∫ y, (((p.map f) y).toReal : ℂ) * φ y ∂Measure.count := by
  have hi : Integrable (fun x => φ (f x)) p.toMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable B
      (ae_of_all _ (fun x => hb (f x)))
  calc
    _ = ∫ x, φ (f x) ∂p.toMeasure := by
      simpa only [Complex.real_smul] using (p.integral_eq_tsum (fun x => φ (f x)) hi).symm
    _ = ∫ y, φ y ∂(p.map f).toMeasure := by
      rw [← PMF.toMeasure_map f p (measurable_of_countable f)]
      exact (integral_map (measurable_of_countable f).aemeasurable
        (measurable_of_countable φ).aestronglyMeasurable).symm
    _ = _ := by
      rw [pmf_realDensity_count]
      exact realDensityMeasure_integral_complex Measure.count _ (measurable_of_countable _)
        (fun _ => ENNReal.toReal_nonneg) φ

theorem pmf_image_count_test_error (p : PMF X) (f : X → Y) (g : Y → ℝ)
    (hg : Integrable g Measure.count) {ε B : ℝ} (hB : 0 ≤ B)
    (he : (∫ y, |((p.map f) y).toReal - g y| ∂Measure.count) ≤ ε)
    (φ : Y → ℂ) (hb : ∀ y, ‖φ y‖ ≤ B) :
    ‖(∑' x, ((p x).toReal : ℂ) * φ (f x)) -
      ∫ y, (g y : ℂ) * φ y ∂Measure.count‖ ≤ B * ε := by
  rw [pmf_image_complex_sum_eq_count_integral p f φ hb]
  exact (density_bounded_complex_test_error Measure.count _ _ (pmf_real_integrable (p.map f)) hg
    φ (measurable_of_countable φ) hb).trans (mul_le_mul_of_nonneg_left he hB)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedSmoothProductMass_pos_of_large {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i) :
    0 < shiftedSmoothProductMass a S := by
  rw [shiftedSmoothProductMass_eq_prod a S (fun i => smoothSamplingScale_pos (hS i))]
  exact Finset.prod_pos (fun i _ => shiftedSmoothSampleSum_pos (a i) (hS i))

theorem shiftedSmoothProductPMF_zero {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass 0 S) :
    shiftedSmoothProductPMF 0 S hS hZ = smoothProductPMF S hS := by
  have hz (z : I → ℤ) : rectangularLatticePoint 0 S z = fun i => (z i : ℝ) / S i := by
    funext i
    change ((z i : ℝ) - 0) / S i = (z i : ℝ) / S i
    rw [sub_zero]
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [shiftedSmoothProductPMF_toReal, smoothProductPMF, realWeightPMF_apply,
    shiftedSmoothProductMass, rectangularWeight, hz]

theorem shiftedSmoothProductPMF_center_l1 {I : Type*} [Fintype I]
    (a b S : I → ℝ) (hS : ∀ i, 0 < S i)
    (hZa : 0 < shiftedSmoothProductMass a S) (hZb : 0 < shiftedSmoothProductMass b S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i) :
    (∫ z, |(shiftedSmoothProductPMF a S hS hZa z).toReal -
      (shiftedSmoothProductPMF b S hS hZb z).toReal| ∂Measure.count) ≤
      24 * (probabilityProfileLipschitz : ℝ) * ∑ i, |a i - b i| / S i := by
  classical
  let pa := fun i => shiftedSmoothCoefficientPMF (a i) (S i) (hS i)
    (shiftedSmoothProductMass_coordinate_pos a S hS hZa i)
  let pb := fun i => shiftedSmoothCoefficientPMF (b i) (S i) (hS i)
    (shiftedSmoothProductMass_coordinate_pos b S hS hZb i)
  have h := tensor_density_l1_le_sum (fun _ : I => (Measure.count : Measure ℤ))
    (fun i k => (pa i k).toReal) (fun i k => (pb i k).toReal)
    (fun i => pmf_real_integrable (pa i)) (fun i => pmf_real_integrable (pb i))
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
    (fun i => pmf_real_integral_count (pa i)) (fun i => pmf_real_integral_count (pb i))
  rw [pi_count_measure] at h
  simp only [shiftedSmoothProductPMF_eq_independent, independentProductPMF_toReal]
  apply h.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_div_assoc] using shiftedSmoothCoefficientPMF_center_l1 (a i) (b i) (S i)
    (hS i) (shiftedSmoothProductMass_coordinate_pos a S hS hZa i)
    (shiftedSmoothProductMass_coordinate_pos b S hS hZb i) (hlarge i)

theorem shiftedSmoothProductPMF_center_test {I : Type*} [Fintype I]
    (a b S : I → ℝ) (hS : ∀ i, 0 < S i)
    (hZa : 0 < shiftedSmoothProductMass a S) (hZb : 0 < shiftedSmoothProductMass b S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (φ : (I → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((shiftedSmoothProductPMF a S hS hZa z).toReal : ℂ) * φ z) -
      ∑' z, ((shiftedSmoothProductPMF b S hS hZb z).toReal : ℂ) * φ z‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ i, |a i - b i| / S i) := by
  have h := pmf_image_count_test_error (shiftedSmoothProductPMF a S hS hZa) id
    (fun z => (shiftedSmoothProductPMF b S hS hZb z).toReal)
    (pmf_real_integrable _) hB
    (by simpa only [PMF.map_id] using shiftedSmoothProductPMF_center_l1 a b S hS hZa hZb hlarge) φ hφ
  have hq := pmf_image_complex_sum_eq_count_integral (shiftedSmoothProductPMF b S hS hZb) id φ hφ
  simp only [id_eq, PMF.map_id] at h hq
  rwa [← hq] at h

theorem shiftedSmoothProductPMF_recenter_test {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZa : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (φ : (I → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((shiftedSmoothProductPMF a S hS hZa z).toReal : ℂ) * φ z) -
      ∑' z, ((smoothProductPMF S hS z).toReal : ℂ) * φ z‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ i, |a i| / S i) := by
  have hZb := shiftedSmoothProductMass_pos_of_large (0 : I → ℝ) S hlarge
  have h := shiftedSmoothProductPMF_center_test a 0 S hS hZa hZb hlarge φ hB hφ
  simpa only [shiftedSmoothProductPMF_zero, Pi.zero_apply, sub_zero] using h

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

variable {K X : Type*} [Fintype K] [Fintype X]
variable {I : X → Type*} [∀ x, Fintype (I x)]

variable [DecidableEq K] [∀ x, DecidableEq (I x)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

variable {K X : Type*} [Fintype K] [DecidableEq K] [Fintype X]
variable {I : X → Type*} [∀ x, Fintype (I x)] [∀ x, DecidableEq (I x)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueRefinementMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K X : Type*} [Fintype K] [Fintype X]

theorem selectedResidue_bounded_mixture_error (modulus : X → ℕ)
    (hmodulus : ∀ x, 0 < modulus x) (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V)) (φ : (K × X → ℤ) → ℂ)
    (target : T → ℂ) (ε : T → ℝ)
    (he : ∀ r : T, ‖(∑' z, ((residueSmoothPMF (boundedColumnResidueRepresentative modulus r.val)
      modulus hmodulus V hV (hc r) z).toReal : ℂ) * φ z) - target r‖ ≤ ε r) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * φ z) -
      ∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) * target r‖ ≤
      ∑ r : T, selectedResidueCellWeight modulus T V r * ε r := by
  rw [selectedResidueSmoothPMF_bounded_mixture modulus hmodulus T V hV hZ hc φ,
    ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (selectedResidueCellWeight_nonneg modulus T V r)]
  exact mul_le_mul_of_nonneg_left (he r) (selectedResidueCellWeight_nonneg modulus T V r)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residueProfile_center_ratio {K X : Type*}
    (r : K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z) (z : K × X) :
    |residueProfileCenter r q z| / residueProfileWidth q V z = |(r z : ℝ)| / V z := by
  have hq0 : (0 : ℝ) < q z.2 := by exact_mod_cast hq z.2
  simp only [residueProfileCenter, residueProfileWidth, abs_div, abs_neg, abs_of_pos hq0]
  field_simp [hq0.ne', (hV z).ne']

theorem residueSmoothIndexPMF_recenter_test {K X : Type*} [Fintype K] [Fintype X]
    (r : K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hc : 0 < shiftedSmoothProductMass (residueProfileCenter r q) (residueProfileWidth q V))
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (K × X → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((residueSmoothIndexPMF r q hq V hV hc z).toReal : ℂ) * φ z) -
      ∑' z, ((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) * φ z‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z, |(r z : ℝ)| / V z) := by
  have h := shiftedSmoothProductPMF_recenter_test (residueProfileCenter r q)
    (residueProfileWidth q V) (residueProfileWidth_pos q V hq hV) hc hlarge φ hB hφ
  simpa only [residueSmoothIndexPMF, residueProfile_center_ratio r q hq V hV] using h

theorem residueSmoothPMF_recenter_test {K X : Type*} [Fintype K] [Fintype X]
    (r : K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hc : 0 < shiftedSmoothProductMass (residueProfileCenter r q) (residueProfileWidth q V))
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (K × X → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((residueSmoothPMF r q hq V hV hc z).toReal : ℂ) * φ z) -
      ∑' z, ((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) * φ (residueLatticeArray r q z)‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z, |(r z : ℝ)| / V z) := by
  rw [residueSmoothPMF_expectation]
  exact residueSmoothIndexPMF_recenter_test r q hq V hV hc hlarge
    (fun z => φ (residueLatticeArray r q z)) hB (fun z => hφ _)

theorem boundedResidueSmoothPMF_recenter_test {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (r : ColumnResiduePattern K X q)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hc : 0 < shiftedSmoothProductMass (residueProfileCenter (boundedColumnResidueRepresentative q r) q)
      (residueProfileWidth q V))
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (K × X → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((residueSmoothPMF (boundedColumnResidueRepresentative q r) q hq V hV hc z).toReal : ℂ) * φ z) -
      ∑' z, ((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
          φ (residueLatticeArray (boundedColumnResidueRepresentative q r) q z)‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : K × X, (q z.2 : ℝ) / V z) := by
  apply (residueSmoothPMF_recenter_test (boundedColumnResidueRepresentative q r) q hq V hV hc
    hlarge φ hB hφ).trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro z _
  have hr := boundedColumnResidueRepresentative_bounds q hq r z
  have hr0 : (0 : ℝ) ≤ boundedColumnResidueRepresentative q r z := by exact_mod_cast hr.1
  apply div_le_div_of_nonneg_right _ (hV z).le
  rw [abs_of_nonneg hr0]
  exact_mod_cast hr.2.le

theorem selectedResidueSmoothPMF_recenter_test {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (T : Finset (ColumnResiduePattern K X q))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (K × X → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hZ z).toReal : ℂ) * φ z) -
      ∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' z, ((smoothProductPMF (residueProfileWidth q V)
          (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
            φ (residueLatticeArray (boundedColumnResidueRepresentative q r.val) q z)‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : K × X, (q z.2 : ℝ) / V z) := by
  have hc (r : T) := shiftedSmoothProductMass_pos_of_large
    (residueProfileCenter (boundedColumnResidueRepresentative q r.val) q) (residueProfileWidth q V) hlarge
  have h := selectedResidue_bounded_mixture_error q hq T V hV hZ hc φ _
    (fun _ => B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : K × X, (q z.2 : ℝ) / V z))
    (fun r => boundedResidueSmoothPMF_recenter_test q hq r.val V hV (hc r) hlarge φ hB hφ)
  simpa only [← Finset.sum_mul, selectedResidueCellWeight_sum q T V hV hZ, one_mul] using h

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {K X Y : Type*} [Fintype K] [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {K X : Type*} [Fintype K] [Fintype X]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalResidueOffsetShift
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalCubeRootDifferences_residue {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (z : Option K × X → ℤ) :
    physicalCubeRootDifferences root D base (residueLatticeArray residue modulus z) =
      physicalCubeResidueCoordinates root D base residue modulus z := by
  funext x i
  have hoff : physicalCubeOffset (0 : X → ℤ) x i = 0 := by cases i <;> rfl
  simp only [physicalCubeResidueCoordinates, physicalCubeRootDifferences,
    residueLatticeArray, hoff, zero_add, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators Matrix

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalSelectedResidue_recenter_test {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (T : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {B Z : ℝ}
    (hB : 0 ≤ B) (hφ : ∀ v, ‖φ v‖ ≤ B) (hZ : 0 < Z) :
    ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root D base z)) / (Z : ℂ) -
      (∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' z, ((smoothProductPMF (residueProfileWidth q V)
          (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
            φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q r.val) q z)) /
          (Z : ℂ)‖ ≤
      (B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : Option K × X, (q z.2 : ℝ) / V z)) / Z := by
  have h := selectedResidueSmoothPMF_recenter_test q hq T V hV hmass hlarge
    (fun z => φ (physicalCubeRootDifferences root D base z)) hB (fun z => hφ _)
  simp_rw [physicalCubeRootDifferences_residue] at h
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  exact div_le_div_of_nonneg_right h hZ.le

theorem trimmedSpatial_residue_width_lower {K X : Type*} {W τ ρ : ℝ}
    (hW : 0 ≤ W) (hρ : 0 ≤ ρ) (N q : X → ℕ) (hq : ∀ x, 0 < q x)
    (hsize : ∀ x, 8 * (1 + W) * (q x : ℝ) * ρ ≤ τ * (N x : ℝ))
    (z : Option K × X) :
    ρ ≤ residueProfileWidth q (trimmedSpatialWidths W τ N) z := by
  have h := trimmedSpatial_scale_lower hW hρ N q z.2 (hq z.2) (hsize z.2)
  have he := congrFun (trimmedSpatial_residue_scale (K := K) W τ N q z.2) z.1
  rw [he]
  cases z.1
  · exact h.1
  · exact h.2

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalResidueReconstruction_centered {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (z : Option K × X → ℤ) :
    physicalResidueReconstruction root D base residue q (centeredPhysicalCubeMap root D z) =
      physicalCubeResidueCoordinates root D base residue q z := by
  rw [centeredPhysicalCubeMap_eq]
  rfl

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalSelectedResidue_width_recenter {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (T : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    {ρ : ℝ} (hρ : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (hwidth : ∀ z, ρ ≤ residueProfileWidth q V z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {B Z : ℝ}
    (hB : 0 ≤ B) (hφ : ∀ v, ‖φ v‖ ≤ B) (hZ : 0 < Z) :
    ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root D base z)) / (Z : ℂ) -
      (∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' z, ((smoothProductPMF (residueProfileWidth q V)
          (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
            φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q r.val) q z)) /
          (Z : ℂ)‖ ≤
      (B * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option K × X) / ρ)) / Z := by
  have hρ0 : 0 < ρ := by linarith [probabilityProfileLipschitz_one_le]
  have hratio (z : Option K × X) : (q z.2 : ℝ) / V z ≤ 1 / ρ := by
    have hq0 : (0 : ℝ) < q z.2 := by exact_mod_cast hq z.2
    have h := (le_div_iff₀ hq0).mp (hwidth z)
    apply (div_le_div_iff₀ (hV z) hρ0).mpr
    linarith
  have hsum : (∑ z : Option K × X, (q z.2 : ℝ) / V z) ≤ Fintype.card (Option K × X) / ρ := by
    apply (Finset.sum_le_sum (fun z _ => hratio z)).trans_eq
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
  apply (physicalSelectedResidue_recenter_test root D base q hq T V hV hmass
    (fun z => hρ.trans (hwidth z)) φ hB hφ hZ).trans
  apply div_le_div_of_nonneg_right _ hZ.le
  apply mul_le_mul_of_nonneg_left _ hB
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 24 * (probabilityProfileLipschitz : ℝ) by positivity)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

theorem physicalResidueOffsetShift_mem {K X α : Type*} [Fintype K] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ d, 0 < q d) (m : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * m) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * m)) (d : X) :
    physicalResidueOffsetShift root root₀ D D₀ r q d ∈ integerScalarLattice (Unit ⊕ α) (m : ℤ) :=
  (residueMatrixShift_spec _ _ (q d) m (hq d) (hres d) (fun k => r (k, d))).2

theorem physicalResidueReconstruction_offset_shift {K X α : Type*} [Fintype K] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ d, 0 < q d) (m : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * m) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * m))
    (v : X → (Unit ⊕ α) → ℤ) :
    physicalResidueReconstruction root D base r q v =
      physicalResidueReconstruction root₀ D₀ base r q
        (v + physicalResidueOffsetShift root root₀ D D₀ r q) := by
  funext d i
  have hs := (residueMatrixShift_spec _ _ (q d) m (hq d) (hres d) (fun k => r (k, d))).1 i
  change (q d : ℤ) * physicalResidueOffsetShift root root₀ D D₀ r q d i = _ at hs
  change physicalCubeOffset base d i +
      (physicalCubeCoefficient root D *ᵥ (fun k => r (k, d))) i + (q d : ℤ) * v d i =
    physicalCubeOffset base d i +
      (physicalCubeCoefficient root₀ D₀ *ᵥ (fun k => r (k, d))) i +
        (q d : ℤ) * (v d i + physicalResidueOffsetShift root root₀ D D₀ r q d i)
  rw [mul_add, hs, Matrix.sub_mulVec, Pi.sub_apply]
  ring

theorem physicalResidueOffsetShift_bound {K X α : Type*} [Fintype K] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ d, 0 < q d) (m : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * m) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * m))
    (hr : ∀ k d, |(r (k, d) : ℝ)| ≤ q d) (d : X) (i : Unit ⊕ α) :
    |(physicalResidueOffsetShift root root₀ D D₀ r q d i : ℝ)| ≤
      ∑ k, |((physicalCubeCoefficient root D i k - physicalCubeCoefficient root₀ D₀ i k : ℤ) : ℝ)| :=
  residueMatrixShift_bound _ _ (q d) m (hq d) (hres d) (fun k => r (k, d)) (fun k => hr k d) i

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

omit [Fintype α] in
theorem allocatedPhysicalCube_principal_columns (i : Unit ⊕ α)
    (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) i (some (.inr j)) =
      principalSpatialColumns (fun j => c (.inr j)) id y i j := by
  cases i <;> rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

open BooleanCubeKernel Polynomial

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

theorem allocatedPhysicalEntryBudget_one_le : 1 ≤ allocatedPhysicalEntryBudget B U basis S c := by
  have h := allocatedPhysicalRootBudget_nonneg B U basis S c
  unfold allocatedPhysicalEntryBudget
  linarith [Nat.cast_nonneg (α := ℝ) S.value]

omit [Fintype α] in
theorem allocatedPhysicalCube_root_entry_bound (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)| ≤ allocatedPhysicalEntryBudget B U basis S c := by
  apply (allocatedPhysicalCube_root_budget B U basis S c x y k).trans
  unfold allocatedPhysicalEntryBudget
  linarith [Nat.cast_nonneg (α := ℝ) S.value]

omit [Fintype α] in
theorem allocatedPhysicalCube_direction_entry_bound (i : α) (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)| ≤ allocatedPhysicalEntryBudget B U basis S c := by
  apply (allocatedPhysicalCube_directions_bound B U basis S x y i k).trans
  have h := allocatedPhysicalRootBudget_nonneg B U basis S c
  unfold allocatedPhysicalEntryBudget
  linarith

variable [DecidableEq α] [DecidableEq G]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators NNReal

theorem anisotropicSpatialError_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (N : Type*) [Fintype N] (B : ℕ) {κ C ρ ξ : ℝ}
    (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hξ : 0 ≤ ξ) :
    0 ≤ anisotropicSpatialError s N B κ C ρ ξ := by
  unfold anisotropicSpatialError normalizedFiberErrorConstant integerFiberErrorConstant
    anisotropicSpatialDetAllowance physicalSpatialInverseBound spatialKernelErrorConstant
  positivity

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

omit [Fintype α] in
theorem allocatedPhysicalCube_direction_sum (i : α) :
    (∑ k, |(allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)|) ≤
      allocatedPhysicalRootBudget B U basis S c := by
  calc
    _ ≤ ∑ _k : LayerSamplerVariables G I n B, (S.value : ℝ) :=
      Finset.sum_le_sum (fun k _ => allocatedPhysicalCube_directions_bound B U basis S x y i k)
    _ = Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) := by simp
    _ ≤ _ := le_add_of_nonneg_left (Finset.sum_nonneg (fun k _ => abs_nonneg (c k : ℝ)))

theorem allocatedTrimmedSpatial_window_bound {X : Type*} [Fintype X]
    (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (v : X → (Unit ⊕ α) → ℤ)
    (hv : v ∈ centeredPhysicalCubeWindow (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (residueProfileWidth q (trimmedSpatialWidths (K := LayerSamplerVariables G I n B) W τ N))) :
    ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / trimmedSpatialRootScale τ N q d| ≤ 3 := by
  apply centeredPhysicalCubeWindow_star_bound _ _ _ _ (fun d => trimmedSpatialSlopeScale W τ N q d)
    hW (fun d => (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1)
    (fun d => (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).2.le)
    (fun d => trimmedSpatial_scale_ratio hW N q d)
    (fun d => trimmedSpatial_residue_scale W τ N q d)
    ((allocatedPhysicalCube_root_sum B U basis S c x y).trans hbudget)
    (fun i => (allocatedPhysicalCube_direction_sum B U basis S c x y i).trans hbudget) v hv

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedWholeResidueShift
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

omit [Fintype α] [DecidableEq α] in
theorem allocatedPhysicalCube_coefficient_entry_bound
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    (i : Unit ⊕ α) (k : Option vars) :
    |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) i k : ℝ)| ≤
        allocatedPhysicalEntryBudget B U basis S c := by
  cases k with
  | none =>
    cases i with
    | inl i =>
      simpa only [physicalCubeCoefficient, Int.cast_one, abs_one] using
        allocatedPhysicalEntryBudget_one_le B U basis S c
    | inr i =>
      simpa only [physicalCubeCoefficient, Int.cast_zero, abs_zero] using
        zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U basis S c)
  | some k =>
    cases i with
    | inl i => exact allocatedPhysicalCube_root_entry_bound B U basis S c x y k
    | inr i => exact allocatedPhysicalCube_direction_entry_bound B U basis S c x y i k

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

omit [Fintype α] [DecidableEq α] in
theorem allocatedPhysicalCube_residue_of_whole_label
    (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    (modulus : ℕ) (hlabel : principalResidueLabel modulus y = principalResidueLabel modulus y₀) :
    integerResidueMatrix (physicalCubeCoefficient
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y)) modulus =
    integerResidueMatrix (physicalCubeCoefficient
      (allocatedPhysicalCubeRoot B U basis S c x y₀)
      (allocatedPhysicalCubeDirections B U basis S x y₀)) modulus := by
  have hc : integerResidueMatrix (principalSpatialColumns (fun j => c (Sum.inr j)) id
      y) modulus =
    integerResidueMatrix (principalSpatialColumns (fun j => c (Sum.inr j)) id
      y₀) modulus := by
    rw [principalSpatialColumns_residue, principalSpatialColumns_residue, hlabel]
  ext i k
  cases k with
  | none => cases i <;> rfl
  | some k =>
    cases k with
    | inl g => cases i <;> rfl
    | inr j =>
      cases i with
      | inl i => exact congrFun (congrFun hc (.inl i)) j
      | inr i => exact congrFun (congrFun hc (.inr i)) j

omit [DecidableEq α] in
theorem allocatedPhysicalResidue_whole_offset_shift
    (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    {X : Type*} (base : X → ℤ) (r : Option vars × X → ℤ)
    (q : X → ℕ) (hq : ∀ d, 0 < q d) (period modulus : ℕ)
    (hdiv : ∀ d, q d * period ∣ modulus)
    (hlabel : principalResidueLabel modulus y = principalResidueLabel modulus y₀)
    (hr : ∀ k d, |(r (k, d) : ℝ)| ≤ q d) :
    let root := allocatedPhysicalCubeRoot B U basis S c x y
    let root₀ := allocatedPhysicalCubeRoot B U basis S c x y₀
    let dirs := allocatedPhysicalCubeDirections B U basis S x y
    let dirs₀ := allocatedPhysicalCubeDirections B U basis S x y₀
    let shift := physicalResidueOffsetShift root root₀ dirs dirs₀ r q
    (∀ d, shift d ∈ integerScalarLattice (Unit ⊕ α) (period : ℤ)) ∧
    (∀ v, physicalResidueReconstruction root dirs base r q v =
      physicalResidueReconstruction root₀ dirs₀ base r q (v + shift)) ∧
    (∀ d i, |(shift d i : ℝ)| ≤
      Fintype.card (Option vars) * (2 * allocatedPhysicalEntryBudget B U basis S c)) := by
  intro root root₀ dirs dirs₀ shift
  have hres (d) : integerResidueMatrix (physicalCubeCoefficient root dirs) (q d * period) =
      integerResidueMatrix (physicalCubeCoefficient root₀ dirs₀) (q d * period) :=
    integerResidueMatrix_reduce _ _ (hdiv d)
      (allocatedPhysicalCube_residue_of_whole_label B U basis S c x y y₀ modulus hlabel)
  refine ⟨fun d => physicalResidueOffsetShift_mem root root₀ dirs dirs₀ r q hq period hres d,
    fun v => physicalResidueReconstruction_offset_shift root root₀ dirs dirs₀ base r q hq period hres v, ?_⟩
  intro d i
  apply (physicalResidueOffsetShift_bound root root₀ dirs dirs₀ r q hq period hres hr d i).trans
  calc
    _ ≤ ∑ _k : Option vars, 2 * allocatedPhysicalEntryBudget B U basis S c := by
      apply Finset.sum_le_sum
      intro k _
      rw [Int.cast_sub]
      apply (abs_sub _ _).trans
      have h₁ := allocatedPhysicalCube_coefficient_entry_bound B U basis S c x y i k
      have h₂ := allocatedPhysicalCube_coefficient_entry_bound B U basis S c x y₀ i k
      linarith
    _ = _ := by simp

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedReferenceWindowTest
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem smoothPhysicalResidue_reference_window_error {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ d, 0 < q d) (modulus : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * modulus) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * modulus))
    (Q : Option K × X → ℝ) (hQ : ∀ z, 0 < Q z)
    (window : Finset (X → (Unit ⊕ α) → ℤ))
    (hwindow : ∀ v ∈ centeredPhysicalCubeWindow root D Q,
      v + physicalResidueOffsetShift root root₀ D D₀ r q ∈ window)
    (ψ φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {A E : ℝ} (hA : 0 < A)
    (he : ∀ v ∈ window,
      ‖((A * (((smoothProductPMF Q hQ).map (centeredPhysicalCubeMap root D))
        (v - physicalResidueOffsetShift root root₀ D D₀ r q)).toReal : ℝ) : ℂ) - ψ v‖ ≤ E) :
    ‖(∑' z, ((smoothProductPMF Q hQ z).toReal : ℂ) *
        φ (physicalCubeResidueCoordinates root D base r q z)) -
      ∑ v ∈ window, (ψ v / (A : ℂ)) *
        φ (physicalResidueReconstruction root₀ D₀ base r q v)‖ ≤
      (E/A) * ∑ v ∈ window, ‖φ (physicalResidueReconstruction root₀ D₀ base r q v)‖ := by
  classical
  have h := pmf_image_shifted_finite_test_error (smoothProductPMF Q hQ)
    (rectangularWeightIndices 0 Q 1) (smoothProductPMF_toReal_zero_off Q hQ)
    (centeredPhysicalCubeMap root D) (physicalResidueOffsetShift root root₀ D D₀ r q)
    window (fun z hz => hwindow _ (centeredPhysicalCubeMap_mem_window root D Q z hz)) ψ
    (fun v => φ (physicalResidueReconstruction root₀ D₀ base r q v)) hA he
  simpa only [← physicalResidueReconstruction_offset_shift root root₀ D D₀ base r q hq modulus hres,
    physicalResidueReconstruction_centered] using h

theorem physicalCenteredResidueMixture_reference_error {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ d, 0 < q d) (modulus : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * modulus) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * modulus))
    (cells : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (window : Finset (X → (Unit ⊕ α) → ℤ))
    (hwindow : ∀ a : cells, ∀ v ∈ centeredPhysicalCubeWindow root D (residueProfileWidth q V),
      v + physicalResidueOffsetShift root root₀ D D₀ (boundedColumnResidueRepresentative q a.val) q ∈ window)
    (ψ φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {A E Z : ℝ} (hA : 0 < A) (hZ : 0 < Z)
    (he : ∀ a : cells, ∀ v ∈ window,
      ‖((A * (((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV)).map (centeredPhysicalCubeMap root D))
          (v - physicalResidueOffsetShift root root₀ D D₀
            (boundedColumnResidueRepresentative q a.val) q)).toReal : ℝ) : ℂ) - ψ v‖ ≤ E) :
    let Q := residueProfileWidth q V
    let hQ := residueProfileWidth_pos q V hq hV
    let F := fun a : cells => physicalResidueReconstruction root₀ D₀ base
      (boundedColumnResidueRepresentative q a.val) q
    ‖(∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑' z, ((smoothProductPMF Q hQ z).toReal : ℂ) *
          φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q a.val) q z)) /
          (Z : ℂ) -
      (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ window, (ψ v / (A : ℂ)) * φ (F a v)) / (Z : ℂ)‖ ≤
      (∑ a : cells, selectedResidueCellWeight q cells V a *
        ((E/A) * ∑ v ∈ window, ‖φ (F a v)‖)) / Z := by
  classical
  intro Q hQ F
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  apply div_le_div_of_nonneg_right _ hZ.le
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (selectedResidueCellWeight_nonneg q cells V a)]
  exact mul_le_mul_of_nonneg_left
    (smoothPhysicalResidue_reference_window_error root root₀ D D₀ base
      (boundedColumnResidueRepresentative q a.val) q hq modulus hres Q hQ window
      (hwindow a) ψ φ hA (he a)) (selectedResidueCellWeight_nonneg q cells V a)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

omit [DecidableEq G] [Fintype α] [DecidableEq α] in
include x in
theorem allocatedPrincipalColumns_difference_sum_bound (i : Unit ⊕ α) :
    (∑ j, |((cols i j - refcols i j : ℤ) : ℝ)|) ≤
      Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
        (2 * allocatedPhysicalEntryBudget B U basis S c) := by
  have hentry (z : PrincipalIntegerTuples B (layerSamplerDegree I n) α
      (allocatedPrincipalSides B U basis S)) (j) :
      |(principalSpatialColumns (fun j => c (Sum.inr j)) id z i j : ℝ)| ≤
        allocatedPhysicalEntryBudget B U basis S c := by
    rw [← allocatedPhysicalCube_principal_columns B U basis S c x z i j]
    exact allocatedPhysicalCube_coefficient_entry_bound B U basis S c x z i (some (Sum.inr j))
  calc
    _ ≤ ∑ _j : PrincipalTupleIndex B (layerSamplerDegree I n),
        2 * allocatedPhysicalEntryBudget B U basis S c := by
      apply Finset.sum_le_sum
      intro j _
      rw [Int.cast_sub]
      exact (abs_sub _ _).trans (by linarith [hentry y j, hentry y₀ j])
    _ = _ := by simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (w w₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "y" => principalAxisJoin grid u w
local notation "y₀" => principalAxisJoin grid u w₀

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y
local notation "root₀" => allocatedPhysicalCubeRoot B U basis S c x y₀
local notation "dirs₀" => allocatedPhysicalCubeDirections B U basis S x y₀

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω R : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq R]
variable (p : FiniteProbabilityWeights Ω) (label : Ω → R)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open BooleanCubeKernel

theorem narrowTrimmedSpatial_scale_lower {X : Type*}
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (hρ : 0 ≤ ρ)
    (N q : X → ℕ) (x : X) (hN : 0 < N x) (hq : 0 < q x)
    (hsize : 8 * (1 + W) * (q x : ℝ) * ρ ≤ (ξ * τ) * (N x : ℝ)) :
    ρ ≤ trimmedSpatialRootScale τ N q x ∧
      ρ ≤ trimmedSpatialSlopeScale W τ N q x ∧
      ρ ≤ ξ * trimmedSpatialSlopeScale W τ N q x := by
  have h := trimmedSpatial_scale_lower hW hρ N q x hq hsize
  have hH : trimmedSpatialRootScale (ξ * τ) N q x = ξ * trimmedSpatialRootScale τ N q x := by
    unfold trimmedSpatialRootScale
    ring
  have hT : trimmedSpatialSlopeScale W (ξ * τ) N q x = ξ * trimmedSpatialSlopeScale W τ N q x := by
    unfold trimmedSpatialSlopeScale
    ring
  rw [hH, hT] at h
  have hp := trimmedSpatial_scales_pos hW hτ N q x hN hq
  exact ⟨h.1.trans (mul_le_of_le_one_left hp.1.le hξ1),
    h.2.trans (mul_le_of_le_one_left hp.2.le hξ1), h.2⟩

theorem narrowTrimmedSpatial_residue_width_lower {G J X : Type*}
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (hρ : 0 ≤ ρ)
    (N q : X → ℕ) (hN : ∀ x, 0 < N x) (hq : ∀ x, 0 < q x)
    (hsize : ∀ x, 8 * (1 + W) * (q x : ℝ) * ρ ≤ (ξ * τ) * (N x : ℝ))
    (z : Option (G ⊕ J) × X) :
    ρ ≤ residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z := by
  apply (trimmedSpatial_residue_width_lower hW hρ N q hq hsize z).trans
  exact div_le_div_of_nonneg_right (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
    (Nat.cast_nonneg _)

namespace BooleanCubeKernel

theorem centeredPhysicalCubeWindow_mono {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) {V W : Option K × X → ℝ}
    (hVW : ∀ z, V z ≤ W z) :
    centeredPhysicalCubeWindow root D V ⊆ centeredPhysicalCubeWindow root D W := by
  classical
  exact Finset.image_subset_image (rectangularWeightIndices_zero_mono hVW)

theorem narrowTrimmedSpatial_window_subset {G J X α : Type*}
    [Fintype G] [Fintype J] [Fintype X] [Fintype α]
    (root : G ⊕ J → ℤ) (D : Matrix α (G ⊕ J) ℤ)
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (N q : X → ℕ) (hN : ∀ x, 0 < N x) :
    centeredPhysicalCubeWindow root D (residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N)) ⊆
      centeredPhysicalCubeWindow root D (residueProfileWidth q (trimmedSpatialWidths W τ N)) := by
  apply centeredPhysicalCubeWindow_mono
  intro z
  exact div_le_div_of_nonneg_right (narrowTrimmedSpatialWidths_le hW hτ hξ1 N hN z)
    (Nat.cast_nonneg _)

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

variable {G J X : Type*} [Fintype G] [Fintype J] [Fintype X] [DecidableEq X]
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
variable (N : X → ℕ) (hN : ∀ x, 0 < N x)
variable (hτ1 : τ ≤ 1 / 2) (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))

variable {dim : ℕ} (root : G ⊕ J → ℤ) (dirs : Matrix (Fin dim) (G ⊕ J) ℤ)
variable (hsite : ∀ s : Finset (Fin dim), (∑ k, |(integerAffineCube root dirs s k : ℝ)|) ≤ W)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (c : LayerSamplerVariables G I n B → ℤ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hx : ∀ g, (integerScalarCubeWeights (Fin dim) S.value S.positive).weight (x g) ≠ 0)
variable (hy : (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).weight y ≠ 0)

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {W τ ξ : ℝ} (hbudget : allocatedPhysicalRootBudget B U b S c ≤ W)
variable (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (N : X → ℕ) (hN : ∀ a, 0 < N a)
variable (hτ1 : τ ≤ 1 / 2) (hsize : ∀ a, 4 ≤ τ * (N a : ℝ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule
open scoped BigOperators Classical Matrix

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedNarrowReferenceTest
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

omit [DecidableEq α] in
theorem allocatedTrimmedSpatial_whole_reference_window
    (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    {X : Type*} [Fintype X] (N q : X → ℕ)
    (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (r : Option vars × X → ℤ) (hr : ∀ k d, |(r (k,d) : ℝ)| ≤ q d)
    (period modulus : ℕ) (hdiv : ∀ d, q d * period ∣ modulus)
    (hlabel : principalResidueLabel modulus y = principalResidueLabel modulus y₀)
    (hsmall : ∀ d, 2 * (Fintype.card (Option vars) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ trimmedSpatialRootScale τ N q d)
    (v : X → (Unit ⊕ α) → ℤ)
    (hv : v ∈ centeredPhysicalCubeWindow
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (residueProfileWidth q (trimmedSpatialWidths (K := vars) W τ N))) :
    v + physicalResidueOffsetShift
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeRoot B U basis S c x y₀)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (allocatedPhysicalCubeDirections B U basis S x y₀) r q ∈
      spatialWindow (trimmedSpatialRootScale τ N q) 4 := by
  let H := trimmedSpatialRootScale τ N q
  let shift := physicalResidueOffsetShift
    (allocatedPhysicalCubeRoot B U basis S c x y)
    (allocatedPhysicalCubeRoot B U basis S c x y₀)
    (allocatedPhysicalCubeDirections B U basis S x y)
    (allocatedPhysicalCubeDirections B U basis S x y₀) r q
  have hH (d) : 0 < H d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1
  have hbound := (allocatedPhysicalResidue_whole_offset_shift B U basis S c x y y₀
    (0 : X → ℤ) r q hq period modulus hdiv hlabel hr).2.2
  have hs : shift ∈ spatialWindow H 1 := by
    have hcoord : ∀ d i, |(shift d i : ℝ)| ≤ H d * (1/2) := by
      intro d i
      have h := hbound d i
      have hh := hsmall d
      change |(shift d i : ℝ)| ≤ _ at h
      change 2 * _ ≤ H d at hh
      linarith
    have h := spatialWindow_of_coordinate_bound H (fun d => (hH d).le)
      (by norm_num : (0 : ℝ) ≤ 1/2) shift hcoord
    norm_num only at h
    exact h
  have hv' : v ∈ spatialWindow H 3 :=
    (mem_spatialWindow_scaled_iff H hH 3 v).mpr
      (allocatedTrimmedSpatial_window_bound B U basis S c x y
        N q hN hq hW hτ hbudget v hv)
  have h := spatialWindow_add H hv' hs
  norm_num only at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y
local notation "root₀" => allocatedPhysicalCubeRoot B U basis S c x y₀
local notation "dirs₀" => allocatedPhysicalCubeDirections B U basis S x y₀

theorem allocatedNarrowTrimmed_whole_reference_mass_test (selection : α ↪ G) {M : ℕ}
    {X : Type*} [Fintype X] (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ κ C₀ ρ ξ δ r : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hsize : ∀ d, 8 * (1 + W) * (q d : ℝ) * ρ ≤ (ξ * τ) * (N d : ℝ))
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (modulus : ℕ) [NeZero modulus]
    (hperiod : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection))
    (refined : ℕ) (hdiv : ∀ d, q d * modulus ∣ refined)
    (hlabel : principalResidueLabel refined y = principalResidueLabel refined y₀)
    (hδ : 0 ≤ δ)
    (hρshift : 2 * (Fintype.card (Option vars) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ ρ)
    (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U basis S c) ≤ δ * ρ)
    (hr : 0 < r) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option vars) X q))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells (narrowTrimmedSpatialWidths W τ ξ N) z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {Cφ Z : ℝ}
    (hCφ : 0 ≤ Cφ) (hφ : ∀ v, ‖φ v‖ ≤ Cφ) (hZ : 0 < Z) :
    let H := fun d => trimmedSpatialRootScale τ N q d
    let T := fun d => trimmedSpatialSlopeScale W τ N q d
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let _Q := residueProfileWidth q V
    let hpivot := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hpivot W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let ψ := fun v : X → (Unit ⊕ α) → ℤ => ∏ d,
      spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix refcols modulus))) modulus f (H d) 4 r (v d)
    let A := ∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) S.value i
    let E₀ := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ
    let G₀ := (modulus : ℝ) ^ Fintype.card (Unit ⊕ α)
    let E₁ := E₀ + G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * δ
    let E := Fintype.card X * (E₁ + 4 * G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * r) *
      (1 + G₀ * anisotropicSpatialDensityCap selection κ + E₁) ^ Fintype.card X
    let window := spatialWindow H 4
    let F := fun a : cells => physicalResidueReconstruction root₀ dirs₀ base
      (boundedColumnResidueRepresentative q a.val) q
    ‖(∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root dirs base z)) / (Z : ℂ) -
      (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ window, (ψ v / (A : ℂ)) * φ (F a v)) / (Z : ℂ)‖ ≤
      Cφ * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option vars × X) / ρ) / Z +
        (∑ a : cells, selectedResidueCellWeight q cells V a *
          ((E / A) * ∑ v ∈ window, ‖φ (F a v)‖)) / Z := by
  classical
  intro H T V hV Q hpivot f ψ A E₀ G₀ E₁ E window F
  have hH (d) : 0 < H d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1
  have hT (d) : 0 < T d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).2
  have hshiftSmall (d) : 2 * (Fintype.card (Option vars) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ H d :=
    hρshift.trans (narrowTrimmedSpatial_scale_lower hW hτ hξ1 hρ.le N q d (hN d) (hq d) (hsize d)).1
  have hmoveSmall (d) : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U basis S c) ≤ δ * H d :=
    hρmove.trans (mul_le_mul_of_nonneg_left
      (narrowTrimmedSpatial_scale_lower hW hτ hξ1 hρ.le N q d (hN d) (hq d) (hsize d)).1 hδ)
  have hA : 0 < A := Finset.prod_pos (fun d _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos α (hH d) (hT d) (Nat.cast_pos.mpr S.positive) i))
  have hCR (d) : integerResidueMatrix cols (q d * modulus) =
      integerResidueMatrix refcols (q d * modulus) := by
    apply integerResidueMatrix_reduce _ _ (hdiv d)
    rw [principalSpatialColumns_residue, principalSpatialColumns_residue, hlabel]
  have hphysical (d) : integerResidueMatrix (physicalCubeCoefficient root dirs) (q d * modulus) =
      integerResidueMatrix (physicalCubeCoefficient root₀ dirs₀) (q d * modulus) :=
    integerResidueMatrix_reduce _ _ (hdiv d)
      (allocatedPhysicalCube_residue_of_whole_label B U basis S c x y y₀ refined hlabel)
  have hrep (a : cells) (k) (d) :
      |(boundedColumnResidueRepresentative q a.val (k,d) : ℝ)| ≤ q d := by
    have h := boundedColumnResidueRepresentative_bounds q hq a.val (k,d)
    rw [abs_of_nonneg (by exact_mod_cast h.1 :
      (0 : ℝ) ≤ boundedColumnResidueRepresentative q a.val (k,d))]
    exact_mod_cast h.2.le
  have hwindow (a : cells) (v) (hv : v ∈ centeredPhysicalCubeWindow root dirs Q) :
      v + physicalResidueOffsetShift root root₀ dirs dirs₀
        (boundedColumnResidueRepresentative q a.val) q ∈ window :=
    allocatedTrimmedSpatial_whole_reference_window B U basis S c x y y₀ N q hN hq hW hτ hbudget
      (boundedColumnResidueRepresentative q a.val) (hrep a) modulus refined hdiv hlabel hshiftSmall v
        (narrowTrimmedSpatial_window_subset root dirs hW hτ hξ1 N q hN hv)
  have he (a : cells) (v) (hv : v ∈ window) :
      ‖((A * (((smoothProductPMF Q (residueProfileWidth_pos q V hq hV)).map
        (centeredPhysicalCubeMap root dirs))
          (v - physicalResidueOffsetShift root root₀ dirs dirs₀
            (boundedColumnResidueRepresentative q a.val) q)).toReal : ℝ) : ℂ) - ψ v‖ ≤ E :=
    allocatedNarrowTrimmed_shifted_vector_site_error B U basis S c x y y₀ selection N q hN hq
      hW hτ hκ hρ hx hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh
      modulus hperiod (boundedColumnResidueRepresentative q a.val) (hrep a) hCR hδ
      (fun d i => (allocatedPrincipalColumns_difference_sum_bound B U basis S c x y y₀ i).trans (hmoveSmall d))
      (by norm_num : (0 : ℝ) < 4) hr v ((mem_spatialWindow_scaled_iff H hH 4 v).mp hv)
  have hwidth (z : Option vars × X) : ρ ≤ residueProfileWidth q V z :=
    narrowTrimmedSpatial_residue_width_lower hW hτ hξ1 hρ.le N q hN hq hsize z
  have hrec := physicalSelectedResidue_width_recenter root dirs base q hq cells V hV hmass
    hρ8 hwidth φ hCφ hφ hZ
  have hsite := physicalCenteredResidueMixture_reference_error root root₀ dirs dirs₀ base q hq modulus hphysical
    cells V hV window hwindow ψ φ hA hZ he
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hrec hsite)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (w w₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "y" => principalAxisJoin grid u w
local notation "y₀" => principalAxisJoin grid u w₀

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y
local notation "root₀" => allocatedPhysicalCubeRoot B U basis S c x y₀
local notation "dirs₀" => allocatedPhysicalCubeDirections B U basis S x y₀

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedMassTupleComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "whole" => principalTupleWeights B (layerSamplerDegree I n) sides
  (allocatedPrincipalSides_pos B U b S)

variable (period : ℕ) [NeZero period] (hp : 0 < period)
variable (hsize : ∀ t, (Fintype.card α + 1) * period ≤
  principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S) t)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable (f : X → PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U b S) → ℂ)
variable (hf : ∀ y, Integrable (fun p => f p y) μ)

include hf

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem complexMean_div_const {A : Type*} [Fintype A]
    (p : FiniteProbabilityWeights A) (f : A → ℂ) (Z : ℂ) :
    p.complexMean (fun a => f a / Z) = p.complexMean f / Z := by
  simp only [complexMean, mul_div_assoc, Finset.sum_div]

end Erdos3.FiniteProbabilityWeights

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "whole" => principalTupleWeights B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)

variable (period : ℕ) [NeZero period] (hp : 0 < period)
variable (hsize : ∀ t, (Fintype.card α + 1) * period ≤
  principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t)

variable {D N : Type*} [Fintype D] [Fintype N]
variable (x : G → IntegerScalarCubeBox α S.value) (spatialRoot : G → ℤ)
variable (c : D → N → ℤ) (index : D → N → PrincipalTupleIndex B (layerSamplerDegree I n))
variable (H : D → ℝ) (Q : D → N → ℝ) (hH : ∀ t, 0 < H t) (hQ : ∀ t j, 0 < Q t j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := α) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z η : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedLongResidueProfile
namespace OAI

section

namespace Erdos3

theorem principalResidueLabel_eq_of_dvd {D α : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ}
    (y y₀ : PrincipalIntegerTuples B h α L) {q refined : ℕ}
    (hdiv : q ∣ refined)
    (hlabel : principalResidueLabel refined y = principalResidueLabel refined y₀) :
    principalResidueLabel q y = principalResidueLabel q y₀ := by
  exact integerResidueMatrix_reduce (fun j i => (y j i : ℤ))
    (fun j i => (y₀ j i : ℤ)) hdiv hlabel

namespace VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

variable (u : PrincipalAxisTuples (B := B) (h := layerSamplerDegree I n) (α := α)
  (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v v₀ : PrincipalAxisTuples (B := B) (h := layerSamplerDegree I n) (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSlicedSpatialToCoarse
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "spatialError" => allocatedTupleSpatialError (Fintype.card X) selection
  (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus C₀ ρ ξ W δ mesh
local notation "boundaryError" => (24 * (probabilityProfileLipschitz : ℝ) *
  Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ)

include hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos htest in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedNarrowTrimmed_recentered_profile_error
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple)
    (hwhole : principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) =
      principalResidueLabel refined y)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg) (hcap : ∀ v, ‖profile y (point v)‖ ≤ Cg) (hZ : 0 < Z) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y
    let dirs := allocatedPhysicalCubeDirections B U b S x y
    ‖(∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences root dirs base z) *
          profile y (point (physicalCubeRootDifferences root dirs base z)))) / (Z : ℂ) -
      allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile y / (Z : ℂ)‖ ≤
      Cg * boundaryError / Z + spatialError * allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile y / Z := by
  intro V hV root dirs
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hE : 0 ≤ spatialError := by
    have he := anisotropicSpatialError_nonneg selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M
      hκ.le (zero_le_one.trans hC₀) hρ.le hξ.le
    have hl := anisotropicSpatialDensityLip_nonneg selection hκ.le
    have hc := anisotropicSpatialDensityCap_nonneg selection hκ.le
    unfold allocatedTupleSpatialError
    dsimp only
    positivity
  have hA : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i := by
    apply Finset.prod_pos
    intro t _
    apply Finset.prod_pos
    intro i _
    have hp := trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)
    exact physicalSpatialOutputScale_pos (Fin dim) hp.1 hp.2 (Nat.cast_pos.mpr S.positive) i
  have he := allocatedNarrowTrimmed_whole_reference_mass_test B U b S (fun _ => 0) x y
    (wholeReference (principalResidueLabel refined y)) selection N q hN hq hW hτ hκ hρ hx
    hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 modulus hperiod refined
    (stride_mul_dvd_residueRefinedPeriod modulus q) hwhole.symm hδ hρshift hρmove hmeshpos base cells hmass
    (fun v => test v * profile y (point v)) hCg
    (fun v => by rw [norm_mul]; exact (mul_le_mul_of_nonneg_right (htest v) (norm_nonneg _)).trans (by simpa using hcap v)) hZ
  dsimp only at he
  have hcoarse := principalResidueLabel_eq_of_dvd _ _
    (show modulus ∣ residueRefinedPeriod modulus q from ⟨∏ t, q t, rfl⟩) hwhole
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y)
  have hcompare : ‖(∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences root dirs base z) *
          profile y (point (physicalCubeRootDifferences root dirs base z)))) / (Z : ℂ) -
      allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile y / (Z : ℂ)‖ ≤
      Cg * boundaryError / Z +
        (∑ a : cells, selectedResidueCellWeight q cells V a * ((spatialError / A) *
          ∑ v ∈ window, ‖test (reconstruct a.val v) * profile y (point (reconstruct a.val v))‖)) / Z := by
    simpa only [allocatedRecenteredProfileTerm, allocatedWholeResidueReconstruction,
      allocatedResidueSpatialKernel, principalSpatialColumns_residue, hcoarse,
      allocatedTupleSpatialError, mul_assoc, A, reconstruct] using he
  refine hcompare.trans (add_le_add le_rfl ?_)
  apply div_le_div_of_nonneg_right _ hZ.le
  unfold allocatedRecenteredProfileMass
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [mul_left_comm spatialError]
  apply mul_le_mul_of_nonneg_left _ (selectedResidueCellWeight_nonneg _ _ _ _)
  change spatialError / _ * _ ≤ spatialError * (_ / _)
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hA.le
  apply mul_le_mul_of_nonneg_left _ hE
  apply Finset.sum_le_sum
  intro v _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (htest _) (norm_nonneg _)).trans_eq (one_mul _)

include hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos htest in
theorem allocatedNarrowTrimmed_recentered_profile_error_law
    (law : FiniteProbabilityWeights fullTuple)
    (hwhole : ∀ y, law.weight y ≠ 0 →
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg)
    (hcap : ∀ y, law.weight y ≠ 0 → ∀ v, ‖profile y (point v)‖ ≤ Cg) (hZ : 0 < Z) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let projected := fun y => ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
          profile y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)))
    ‖law.complexMean projected / (Z : ℂ) -
      law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ)‖ ≤
      Cg * boundaryError / Z + spatialError * law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile) / Z := by
  intro V hV projected
  let recentered := allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
    B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile
  let mass := allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
    B U b S X modulus q wholeReference x N base cells point profile
  have he := law.norm_complexMean_sub_le (fun y => projected y / (Z : ℂ))
    (fun y => recentered y / (Z : ℂ)) (fun y => Cg * boundaryError / Z + spatialError * mass y / Z)
    (fun y hy => allocatedNarrowTrimmed_recentered_profile_error B U b S X modulus q wholeReference
      x hM selection hx N hW mesh base cells point test hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1
      hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos hmass htest profile y (hwhole y hy) hCg (hcap y hy) hZ)
  rw [FiniteProbabilityWeights.complexMean_div_const, FiniteProbabilityWeights.complexMean_div_const,
    FiniteProbabilityWeights.mean_add, FiniteProbabilityWeights.mean_const] at he
  have hm : law.mean (fun y => spatialError * mass y / Z) = spatialError * law.mean mass / Z := by
    simp only [FiniteProbabilityWeights.mean, mul_div_assoc, Finset.sum_div]
    rw [Finset.mul_sum]
    congr 1
    funext y
    ring
  rw [hm] at he
  exact he

include hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos htest in
theorem allocatedNarrowTrimmed_recentered_source_law
    (law : FiniteProbabilityWeights fullTuple)
    (hwhole : ∀ y, law.weight y ≠ 0 →
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg)
    (hcap : ∀ y, law.weight y ≠ 0 → ∀ v, ‖profile y (point v)‖ ≤ Cg) (hZ : 1 / 2 ≤ Z) {target κ : ℝ}
    (hmassBound : law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) ≤
        coarseReferenceMassConstant dim X W S.value)
    (hboundary : Cg * boundaryError ≤ normalizedSpatialShare target / 2)
    (hsite : spatialError * coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare target / 2) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let projected := fun y => ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
          profile y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)))
    κ ≤ (law.complexMean projected / (Z : ℂ)).re →
    Z * (κ - Real.exp (-target)) ≤
      (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile)).re := by
  intro V hV projected hsource
  have hZpos : 0 < Z := by linarith
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hE : 0 ≤ spatialError := by
    have he := anisotropicSpatialError_nonneg selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M
      hκ.le (zero_le_one.trans hC₀) hρ.le hξ.le
    have hl := anisotropicSpatialDensityLip_nonneg selection hκ.le
    have hc := anisotropicSpatialDensityCap_nonneg selection hκ.le
    unfold allocatedTupleSpatialError
    dsimp only
    positivity
  have he := allocatedNarrowTrimmed_recentered_profile_error_law B U b S X modulus q wholeReference
    x hM selection hx N hW mesh base cells point test hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1
    hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos hmass htest law hwhole profile hCg hcap hZpos
  have hb : Cg * boundaryError / Z ≤ normalizedSpatialShare target := by
    apply (div_le_iff₀ hZpos).mpr
    have hp : 0 < normalizedSpatialShare target := Real.exp_pos _
    nlinarith
  have hs : spatialError * law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) / Z ≤ normalizedSpatialShare target := by
    apply (div_le_iff₀ hZpos).mpr
    have hp : 0 < normalizedSpatialShare target := Real.exp_pos _
    have hh := (mul_le_mul_of_nonneg_left hmassBound hE).trans hsite
    nlinarith
  have hsmall : 2 * normalizedSpatialShare target ≤ Real.exp (-target) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-(target + 2)) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hnorm := he.trans (show _ ≤ Real.exp (-target) by linarith only [hb, hs, hsmall])
  have hre := (Complex.re_le_norm _).trans hnorm
  rw [Complex.sub_re] at hre
  have hout : κ - Real.exp (-target) ≤
      (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ)).re := by
    linarith only [hsource, hre]
  rw [Complex.div_ofReal_re] at hout
  exact (mul_comm Z _).le.trans ((le_div_iff₀ hZpos).mp hout)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "spatialError" => allocatedTupleSpatialError (Fintype.card X) selection
  (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus C₀ ρ ξ W δ mesh
local notation "boundaryError" => (24 * (probabilityProfileLipschitz : ℝ) *
  Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ)

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_recentered_source_law.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_recentered_source_law.{u_1, u_2, u_3, u_4, u_5, u_6}
