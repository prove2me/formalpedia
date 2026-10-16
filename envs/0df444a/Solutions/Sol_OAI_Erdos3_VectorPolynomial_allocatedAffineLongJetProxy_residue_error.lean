-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_residue_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-15T21:59:02.368536+00:00
-- url     : https://prove2.me/submissions/4227d085-dc83-49a6-9bed-24da2dcf3829

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B136
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedNormalizedLongJetDensity_parameter_bounds

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RectangularLatticeCells
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem latticeSample_measurable (a S : ℝ) : Measurable (latticeSample a S) := by
  unfold latticeSample
  fun_prop

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

variable {J : Type*} [Fintype J]

omit [Fintype J] in
theorem rectangularLatticeSample_measurable (a S : J → ℝ) :
    Measurable (rectangularLatticeSample a S) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (latticeSample_measurable (a j) (S j)).comp (measurable_pi_apply j)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

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

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finiteRectangularHistogram_mul_test {J : Type*} [Fintype J]
    (s : Finset (J → ℤ)) (w f : (J → ℤ) → ℝ) (a S : J → ℝ) (hS : ∀ j, 0 < S j) (x : J → ℝ) :
    finiteRectangularHistogram s w a S x * f (rectangularLatticeRound a S x) =
      finiteRectangularHistogram s (fun k => w k * f k) a S x := by
  unfold finiteRectangularHistogram
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hx : x ∈ rectangularLatticeCell a S k
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      (rectangularLatticeCell_iff a S hS x k).mp hx]
  · simp only [Set.indicator_of_notMem hx, zero_mul]

theorem finiteRectangularHistogram_test_integral {J : Type*} [Fintype J]
    (s : Finset (J → ℤ)) (w f : (J → ℤ) → ℝ) (a S : J → ℝ) (hS : ∀ j, 0 < S j) :
    (∫ x, finiteRectangularHistogram s w a S x * f (rectangularLatticeRound a S x)) =
      (∑ k ∈ s, w k * f k) / (∏ j, S j) := by
  simp_rw [finiteRectangularHistogram_mul_test s w f a S hS]
  exact finiteRectangularHistogram_integral s _ a S hS

theorem finiteRectangularHistogram_normalized_mean {J : Type*} [Fintype J]
    (s : Finset (J → ℤ)) (f : (J → ℤ) → ℝ) (a S : J → ℝ) (hS : ∀ j, 0 < S j) :
    (∫ x, (finiteRectangularHistogram s (fun _ => 1) a S x /
      (∫ y, finiteRectangularHistogram s (fun _ => 1) a S y)) * f (rectangularLatticeRound a S x)) =
      𝔼 k ∈ s, f k := by
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div, finiteRectangularHistogram_test_integral s (fun _ => 1) f a S hS,
    finiteRectangularHistogram_integral s (fun _ => 1) a S hS]
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hP : (∏ j, S j) ≠ 0 := (Finset.prod_pos (fun j _ => hS j)).ne'
  rw [div_div_div_cancel_right₀ hP]
  exact (Finset.expect_eq_sum_div_card s f).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
namespace OAI

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem progression_slice_endpoint_geometry {L step H : ℕ} (c : ℤ)
    (hL : 0 < L) (hstep : 0 < step) (hH : 2 ≤ H) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hdense : δ * L ≤ ((integerProgressionSupport c (step : ℤ) H).card : ℝ)) :
    let lower := (c : ℝ) / L
    let width := (step : ℝ) * ((H : ℝ) - 1) / L
    0 ≤ lower ∧ δ / 2 ≤ width ∧ |lower| + |width| ≤ 1 ∧
      (step : ℝ) / L ≤ 2 / ((H : ℝ) - 1) := by
  have hbase := hsubset (integerProgressionSupport_point c step H hstep 0 (by omega))
  have hlast := hsubset (integerProgressionSupport_point c step H hstep (H - 1) (by omega))
  have hc : (0 : ℝ) ≤ c := by
    have hh : 0 ≤ c := by simpa using (Finset.mem_Ico.mp hbase).1
    exact_mod_cast hh
  have hh : (c : ℝ) + (step : ℝ) * ((H : ℝ) - 1) < L := by
    have hh := (Finset.mem_Ico.mp hlast).2
    have he : (c : ℝ) + (step : ℝ) * ((H - 1 : ℕ) : ℝ) < L := by exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one] using he
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hstep1 : (1 : ℝ) ≤ step := by exact_mod_cast hstep
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  rw [card_integerProgressionSupport c step H hstep] at hdense
  have hwidth : δ / 2 ≤ (step : ℝ) * ((H : ℝ) - 1) / L := by
    apply (le_div_iff₀ hLp).mpr
    have h1 : (H : ℝ) / 2 ≤ (H : ℝ) - 1 := by linarith
    have h2 : (H : ℝ) - 1 ≤ (step : ℝ) * ((H : ℝ) - 1) := by nlinarith
    nlinarith
  have hw0 : 0 ≤ (step : ℝ) * ((H : ℝ) - 1) / L := (half_pos hδ).le.trans hwidth
  refine ⟨div_nonneg hc hLp.le, hwidth, ?_, ?_⟩
  · rw [abs_of_nonneg (div_nonneg hc hLp.le), abs_of_nonneg hw0, ← add_div]
    exact (div_le_one hLp).mpr hh.le
  · apply (le_div_iff₀ (by linarith : 0 < (H : ℝ) - 1)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hLp).mpr
    linarith

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

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeMeasure_integral {α : Type*} [Fintype α] [DecidableEq α]
    (f : (Option α → ℝ) → ℝ) :
    (∫ a, f a ∂scalarCubeMeasure α) = scalarCubeDomainDensity α * ∫ a in scalarCubeDomain α, f a := by
  rw [scalarCubeMeasure, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  rfl

theorem scalarCubeMeasure_ae_domain (α : Type*) [Fintype α] [DecidableEq α] :
    ∀ᵐ a ∂scalarCubeMeasure α, a ∈ scalarCubeDomain α := by
  apply ae_iff.mpr
  change scalarCubeMeasure α (scalarCubeDomain α)ᶜ = 0
  simp [scalarCubeMeasure, Measure.smul_apply,
    Measure.restrict_apply (scalarCubeDomain_isOpen α).measurableSet.compl]

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

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeFaceSlab
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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem halfOpenScalarCubeDomain_measurable (I : Type*) [Fintype I] [DecidableEq I] :
    MeasurableSet (halfOpenScalarCubeDomain I) := by
  have he : halfOpenScalarCubeDomain I = ⋂ t : Finset I,
      (fun x => scalarCubeValue x t) ⁻¹' Set.Ico (0 : ℝ) 1 := by
    ext x
    simp only [halfOpenScalarCubeDomain, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [he]
  exact MeasurableSet.iInter (fun (t : Finset I) =>
    measurableSet_Ico.preimage (scalarCubeValue_contDiff t).continuous.measurable)

theorem scalarCubeDomain_subset_halfOpen (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomain I ⊆ halfOpenScalarCubeDomain I :=
  fun _ hx t => ⟨(hx t).1.le, (hx t).2⟩

theorem halfOpenScalarCubeDomain_ae (I : Type*) [Fintype I] [DecidableEq I] :
    halfOpenScalarCubeDomain I =ᵐ[volume] scalarCubeDomain I := by
  filter_upwards [scalarCubeDomain_ae_closed I] with x hx
  apply propext
  have hx' : x ∈ scalarCubeDomain I ↔ x ∈ closedScalarCubeDomain I := iff_of_eq hx
  constructor
  · intro h
    exact hx'.mpr (halfOpenScalarCubeDomain_subset_closed I h)
  · exact fun h => scalarCubeDomain_subset_halfOpen I h

theorem scalarCubeIndicator_range (I : Type*) [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) : 0 ≤ scalarCubeIndicator I x ∧ scalarCubeIndicator I x ≤ 1 := by
  unfold scalarCubeIndicator
  split_ifs <;> norm_num

theorem scalarCubeIndicator_integrable (I : Type*) [Fintype I] [DecidableEq I] :
    Integrable (scalarCubeIndicator I) := by
  change Integrable ((halfOpenScalarCubeDomain I).indicator (fun _ => (1 : ℝ)))
  exact (integrableOn_const ((measure_mono (halfOpenScalarCubeDomain_subset_closed I)).trans_lt
    (closedScalarCubeDomain_compact I).measure_lt_top).ne).integrable_indicator
    (halfOpenScalarCubeDomain_measurable I)

theorem scalarCubeIndicator_integral (I : Type*) [Fintype I] [DecidableEq I] :
    (∫ x, scalarCubeIndicator I x) = volume.real (scalarCubeDomain I) := by
  have he : scalarCubeIndicator I =ᵐ[volume] (scalarCubeDomain I).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [halfOpenScalarCubeDomain_ae I] with x hx
    have hx' : (x ∈ halfOpenScalarCubeDomain I) = (x ∈ scalarCubeDomain I) := hx
    change (if x ∈ halfOpenScalarCubeDomain I then 1 else 0) =
      if x ∈ scalarCubeDomain I then 1 else 0
    rw [hx']
  rw [integral_congr_ae he]
  exact integral_indicator_one (scalarCubeDomain_isOpen I).measurableSet

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

theorem scalarCubeFaceSlab_measurable {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) (u : ℝ) : MeasurableSet (scalarCubeFaceSlab i u) :=
  measurableSet_closedBall.inter (measurableSet_le
    (scalarCubeFace_contDiff i).continuous.abs.measurable measurable_const)

theorem scalarCubeFaceSlab_finite {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) (u : ℝ) : volume (scalarCubeFaceSlab i u) ≠ ⊤ :=
  ne_of_lt ((measure_mono Set.inter_subset_left).trans_lt (isCompact_closedBall _ _).measure_lt_top)

theorem scalarCubeFaceSlab_fiber_bound {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) {u : ℝ} (hu : 0 ≤ u) (b : I → ℝ) :
    volume.real {y | scalarCubeJoin (b, y) ∈ scalarCubeFaceSlab i u} ≤ 2*u := by
  let c : ℝ := if i.1 then 1 - ∑ k ∈ i.2, b k else -(∑ k ∈ i.2, b k)
  have hsub : {y | scalarCubeJoin (b, y) ∈ scalarCubeFaceSlab i u} ⊆ Set.Icc (c-u) (c+u) := by
    intro y hy
    have hraw : |scalarCubeFace i (scalarCubeJoin (b,y))| ≤ u := hy.2
    have h := abs_le.mp hraw
    rw [scalarCubeJoin_face] at h
    dsimp only [c]
    split_ifs at h ⊢ <;> constructor <;> linarith
  have hv : volume.real (Set.Icc (c-u) (c+u)) = 2*u := by
    rw [Real.volume_real_Icc]
    simp only [show c+u-(c-u) = 2*u by ring, max_eq_left (by positivity : 0 ≤ 2*u)]
  exact (measureReal_mono (μ := volume) hsub (by simp [Real.volume_Icc])).trans_eq hv

theorem scalarCubeFaceSlab_volume_le {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) {u : ℝ} (hu : 0 ≤ u) :
    volume.real (scalarCubeFaceSlab i u) ≤ (4 : ℝ)^Fintype.card I * (2*u) := by
  let s := scalarCubeJoin ⁻¹' scalarCubeFaceSlab i u
  have hs : MeasurableSet s := (scalarCubeFaceSlab_measurable i u).preimage (scalarCubeJoin_measurable I)
  have hm := (scalarCubeJoin_measurePreserving I).measure_preimage (scalarCubeFaceSlab_measurable i u).nullMeasurableSet
  have hmr := (scalarCubeJoin_measurePreserving I).measureReal_preimage (scalarCubeFaceSlab_measurable i u).nullMeasurableSet
  have hfin : (volume : Measure ((I → ℝ) × ℝ)) s ≠ ⊤ := by
    change volume (scalarCubeJoin ⁻¹' scalarCubeFaceSlab i u) ≠ ⊤
    rw [hm]
    exact scalarCubeFaceSlab_finite i u
  have hb : ∀ z ∈ s, z.1 ∈ Metric.closedBall (0 : I → ℝ) 2 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro k
    have hh : ‖scalarCubeJoin z‖ ≤ 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
    exact (norm_le_pi_norm (scalarCubeJoin z) (some k)).trans hh
  have h := product_measureReal_le_of_fiber_bound
    (volume : Measure (I → ℝ)) (volume : Measure ℝ) s hs hfin
    (Metric.closedBall (0 : I → ℝ) 2) measurableSet_closedBall (isCompact_closedBall _ _).measure_ne_top
    hb (scalarCubeFaceSlab_fiber_bound i hu)
  change volume.real s ≤ _ at h
  rw [hmr] at h
  have hbase : volume.real (Metric.closedBall (0 : I → ℝ) 2) = (4 : ℝ)^Fintype.card I := by
    rw [measureReal_def, Real.volume_pi_closedBall _ (by norm_num)]
    norm_num
  rwa [hbase] at h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledCubeProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeProductMeasure_ae_domain (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] :
    ∀ᵐ x ∂scalarCubeProductMeasure ι α, x ∈ scalarCubeProductDomain ι α := by
  change ∀ᵐ x ∂Measure.pi (fun _ : ι => scalarCubeMeasure α),
    x ∈ Set.univ.pi (fun _ => scalarCubeDomain α)
  have h : ∀ i : ι, ∀ᵐ x ∂Measure.pi (fun _ : ι => scalarCubeMeasure α),
      x i ∈ scalarCubeDomain α := fun _ =>
    Measure.tendsto_eval_ae_ae.eventually (scalarCubeMeasure_ae_domain α)
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact fun i _ => hx i

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable (ι : Type*) [Fintype ι]

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

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarCubeLatticeGeometry
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem scalarCubeValue_sub_bound {I : Type*} [Fintype I] [DecidableEq I]
    (x y : Option I → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (he : ‖x-y‖ ≤ δ) (t : Finset I) :
    |scalarCubeValue x t - scalarCubeValue y t| ≤ (Fintype.card I + 1 : ℝ)*δ := by
  have hi (i : Option I) : |x i-y i| ≤ δ := (norm_le_pi_norm (x-y) i).trans he
  have hsum : |∑ i ∈ t, (x (some i)-y (some i))| ≤ (t.card : ℝ)*δ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i ∈ t) => hi (some i))
  have hcard : (t.card : ℝ) ≤ Fintype.card I := by exact_mod_cast t.card_le_univ
  have hid : scalarCubeValue x t - scalarCubeValue y t =
      (x none-y none) + ∑ i ∈ t, (x (some i)-y (some i)) := by
    simp only [scalarCubeValue_formula, Finset.sum_sub_distrib]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add (hi none) hsum).trans (by nlinarith))

theorem scalarCubeIndicator_disagreement {I : Type*} [Fintype I] [DecidableEq I]
    (x y : Option I → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (he : ‖y-x‖ ≤ δ)
    (hne : scalarCubeIndicator I y ≠ scalarCubeIndicator I x) :
    ∃ i : Bool × Finset I, x ∈ scalarCubeFaceSlab i ((Fintype.card I + 1 : ℝ)*δ) := by
  have hv (t : Finset I) := scalarCubeValue_sub_bound y x hδ he t
  have hxnorm (hy : y ∈ halfOpenScalarCubeDomain I) : ‖x‖ ≤ 2 := by
    have ht : ‖x‖ ≤ ‖y-x‖ + ‖y‖ := by
      calc
        ‖x‖ = ‖-(y-x)+y‖ := by congr 1; abel
        _ ≤ ‖-(y-x)‖ + ‖y‖ := norm_add_le _ _
        _ = _ := by rw [norm_neg]
    linarith [halfOpenScalarCubeDomain_norm_le hy]
  by_cases hx : x ∈ halfOpenScalarCubeDomain I
  · have hy : y ∉ halfOpenScalarCubeDomain I := by
      intro hy
      exact hne (by simp only [scalarCubeIndicator, hx, hy, ite_true])
    obtain ⟨t, ht⟩ := not_forall.mp hy
    have hbox : x ∈ Metric.closedBall 0 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        (halfOpenScalarCubeDomain_norm_le hx).trans (by norm_num : (1 : ℝ) ≤ 2)
    have hxval := hx t
    have hdiff := abs_le.mp (hv t)
    by_cases hlo : scalarCubeValue y t < 0
    · refine ⟨(false,t), hbox, ?_⟩
      change |scalarCubeValue x t| ≤ _
      rw [abs_of_nonneg hxval.1]
      linarith [hxval.1, hxval.2, hdiff.1, hdiff.2]
    · have hhi : 1 ≤ scalarCubeValue y t := by
        by_contra! hn
        exact ht ⟨le_of_not_gt hlo, hn⟩
      refine ⟨(true,t), hbox, ?_⟩
      change |1-scalarCubeValue x t| ≤ _
      rw [abs_of_nonneg (by linarith [hxval.2])]
      linarith [hxval.1, hxval.2, hdiff.1, hdiff.2]
  · have hy : y ∈ halfOpenScalarCubeDomain I := by
      by_contra hy
      exact hne (by simp only [scalarCubeIndicator, hx, hy, ite_false])
    obtain ⟨t, ht⟩ := not_forall.mp hx
    have hbox : x ∈ Metric.closedBall 0 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hxnorm hy
    have hyval := hy t
    have hdiff := abs_le.mp (hv t)
    by_cases hlo : scalarCubeValue x t < 0
    · refine ⟨(false,t), hbox, ?_⟩
      change |scalarCubeValue x t| ≤ _
      rw [abs_of_neg hlo]
      linarith [hyval.1, hyval.2, hdiff.1, hdiff.2]
    · have hhi : 1 ≤ scalarCubeValue x t := by
        by_contra! hn
        exact ht ⟨le_of_not_gt hlo, hn⟩
      refine ⟨(true,t), hbox, ?_⟩
      change |1-scalarCubeValue x t| ≤ _
      rw [abs_of_nonpos (by linarith)]
      linarith [hyval.1, hyval.2, hdiff.1, hdiff.2]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SigmaProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem sigmaProductMeasure_flatten {D : Type*} [Fintype D] {I : D → Type*}
    [∀ d, Fintype (I d)] {X : (Σ d, I d) → Type*}
    [∀ s, MeasurableSpace (X s)] (μ : ∀ s, Measure (X s)) [∀ s, IsProbabilityMeasure (μ s)] :
    (Measure.pi (fun d => Measure.pi (fun i => μ ⟨d, i⟩))).map
      (fun x (s : Σ d, I d) => x s.1 s.2) = Measure.pi μ := by
  have hm : Measurable (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) :=
    measurable_pi_iff.mpr (fun index =>
      (measurable_pi_apply index.2).comp (measurable_pi_apply index.1))
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi (fun i => s ⟨d, i⟩)) := by
    ext x
    constructor
    · intro hx d _ i _
      exact hx ⟨d, i⟩ (Set.mem_univ _)
    · intro hx t _
      exact hx t.1 (Set.mem_univ _) t.2 (Set.mem_univ _)
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_sigma]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem principalTupleFlatten_norm_apply_le {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (α : Type*) [Fintype α]
    (x : PrincipalTupleIndex B h → Option α → ℝ) : ‖principalTupleFlatten B h α x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro z
  exact (norm_le_pi_norm (x ⟨z.1, z.2.1, z.2.2.1⟩) z.2.2.2).trans
    (norm_le_pi_norm x ⟨z.1, z.2.1, z.2.2.1⟩)

theorem principalTupleFlatten_lipschitz {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (α : Type*) [Fintype α] :
    LipschitzWith 1 (principalTupleFlatten B h α) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
  exact principalTupleFlatten_norm_apply_le B h α (x-y)

theorem jointBooleanSource_eq_principalTuple_map {D α : Type*} [Fintype D] [Fintype α]
    [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) :
    jointBooleanSource (B := B) (α := α) h =
      (scalarCubeProductMeasure (PrincipalTupleIndex B h) α).map (principalTupleFlatten B h α) := by
  let F : (∀ d, (B d × Fin (h d)) → Option α → ℝ) → (PrincipalTupleIndex B h → Option α → ℝ) :=
    fun x j => x j.1 j.2
  have hF : Measurable F :=
    measurable_pi_iff.mpr (fun j => (measurable_pi_apply j.2).comp (measurable_pi_apply j.1))
  have ht : (Measure.pi (fun d => scalarCubeProductMeasure (B d × Fin (h d)) α)).map F =
      scalarCubeProductMeasure (PrincipalTupleIndex B h) α :=
    sigmaProductMeasure_flatten (fun _ => scalarCubeMeasure α)
  have hblock : Measurable (fun (x : ∀ d, (B d × Fin (h d)) → Option α → ℝ) d =>
      blockCubeFlatten (B d) (Fin (h d)) α (x d)) :=
    measurable_pi_iff.mpr (fun d => (blockCubeFlatten (B d) (Fin (h d)) α).continuous.measurable.comp
      (measurable_pi_apply d))
  rw [jointBooleanSource, sigmaAxisMeasure]
  simp_rw [blockCubeMeasure]
  rw [← Measure.pi_map_pi (fun d => (blockCubeFlatten (B d) (Fin (h d)) α).continuous.measurable.aemeasurable)]
  rw [Measure.map_map (sigmaAxisCoordinates (fun d => BlockParameter (B d) (Fin (h d)) α)).symm.continuous.measurable
    hblock]
  rw [← ht, Measure.map_map (principalTupleFlatten B h α).continuous.measurable hF]
  rfl

theorem jointBooleanSource_principalTuple_integral {D α : Type*} [Fintype D] [Fintype α]
    [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (φ : (JointBlockParameter B h α → ℝ) → ℝ) :
    (∫ x, φ x ∂jointBooleanSource h) =
      ∫ x, φ (principalTupleFlatten B h α x) ∂scalarCubeProductMeasure (PrincipalTupleIndex B h) α := by
  rw [jointBooleanSource_eq_principalTuple_map]
  exact (principalTupleFlatten B h α).toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map φ

end Erdos3

namespace Erdos3

open MeasureTheory

theorem scalarCubeProductMeasure_ae_closedBall (J I : Type*) [Fintype J] [Fintype I]
    [DecidableEq I] : ∀ᵐ x ∂scalarCubeProductMeasure J I, x ∈ Metric.closedBall 0 1 := by
  filter_upwards [scalarCubeProductMeasure_ae_domain J I] with x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  exact (scalarCubeDomain_coordinate_abs_lt_one (hx j (Set.mem_univ _)) i).le

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityTestParameter
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem density_bounded_test_error {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (φ : X → ℝ) (hφ : Measurable φ) {B : ℝ} (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(∫ x, f x * φ x ∂μ) - ∫ x, g x * φ x ∂μ| ≤ B * ∫ x, |f x-g x| ∂μ := by
  rw [← integral_sub (hf.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb))
    (hg.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb))]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ x, B * |f x-g x| ∂μ := by
      apply integral_mono
      · exact ((hf.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)).sub
          (hg.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb))).abs
      · exact (hf.sub hg).abs.const_mul B
      · intro x
        change |f x * φ x - g x * φ x| ≤ B * |f x-g x|
        rw [← sub_mul, abs_mul, mul_comm B]
        exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hb x) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

theorem density_rounding_test_error {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hg0 : ∀ x, 0 ≤ g x) (hgmass : (∫ x, g x ∂μ) = 1)
    (R : X → X) (hR : Measurable R) {δ ε B : ℝ} (hB : 0 ≤ B)
    (herr : ∫ x, |f x-g x| ∂μ ≤ ε) (hmove : ∀ x, dist (R x) x ≤ δ)
    (φ : X → ℝ) {K : ℝ≥0} (hφ : LipschitzWith K φ) (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(∫ x, f x * φ (R x) ∂μ) - ∫ x, g x * φ x ∂μ| ≤ B*ε + K*δ := by
  have hφR : Measurable (fun x => φ (R x)) := hφ.continuous.measurable.comp hR
  have hfirst := density_bounded_test_error μ f g hf hg (φ ∘ R) hφR (fun x => hb (R x))
  have hsecond : |(∫ x, g x * φ (R x) ∂μ) - ∫ x, g x * φ x ∂μ| ≤ K*δ := by
    rw [← integral_sub (hg.mul_bdd hφR.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => hb (R x))))
      (hg.mul_bdd hφ.continuous.measurable.aestronglyMeasurable (Filter.Eventually.of_forall hb))]
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ x, g x * (K*δ) ∂μ := by
        apply integral_mono
        · exact ((hg.mul_bdd hφR.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => hb (R x)))).sub
            (hg.mul_bdd hφ.continuous.measurable.aestronglyMeasurable (Filter.Eventually.of_forall hb))).abs
        · exact hg.mul_const _
        · intro x
          change |g x * φ (R x) - g x * φ x| ≤ g x * (K*δ)
          rw [← mul_sub, abs_mul, abs_of_nonneg (hg0 x)]
          apply mul_le_mul_of_nonneg_left _ (hg0 x)
          exact (hφ.dist_le_mul (R x) x).trans (mul_le_mul_of_nonneg_left (hmove x) K.coe_nonneg)
      _ = _ := by rw [integral_mul_const, hgmass, one_mul]
  have ht := abs_sub_le (∫ x, f x * φ (R x) ∂μ) (∫ x, g x * φ (R x) ∂μ) (∫ x, g x * φ x ∂μ)
  exact ht.trans (add_le_add (hfirst.trans (mul_le_mul_of_nonneg_left herr hB)) hsecond)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPathSlicedGridMeshBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem scalarCubeGridHistogram_eq (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) (x : Option I → ℝ) :
    scalarCubeGridHistogram I a S x = scalarCubeIndicator I (rectangularLatticeSample a S x) :=
  rectangularWeightHistogram_eq _ a S hS (scalarCubeIndicator_zero_outside I) x

theorem scalarCubeGridHistogram_integrable (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) : Integrable (scalarCubeGridHistogram I a S) :=
  rectangularWeightHistogram_integrable _ a S 1

theorem scalarCubeGridHistogram_point_error (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) (x : Option I → ℝ) :
    |scalarCubeGridHistogram I a S x - scalarCubeIndicator I x| ≤
      ∑ i : Bool × Finset I, (scalarCubeFaceSlab i ((Fintype.card I + 1 : ℝ)*δ)).indicator
        (fun _ => (1 : ℝ)) x := by
  rw [scalarCubeGridHistogram_eq I a S hS]
  have hnonneg (i : Bool × Finset I) : 0 ≤
      (scalarCubeFaceSlab i ((Fintype.card I + 1 : ℝ)*δ)).indicator (fun _ => (1 : ℝ)) x := by
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases heq : scalarCubeIndicator I (rectangularLatticeSample a S x) = scalarCubeIndicator I x
  · rw [heq, sub_self, abs_zero]
    exact Finset.sum_nonneg (fun i _ => hnonneg i)
  · obtain ⟨i, hi⟩ := scalarCubeIndicator_disagreement x (rectangularLatticeSample a S x)
      hδ hδ1 (rectangularLatticeSample_error a S hS hδ hmesh x) heq
    have hle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Bool × Finset I))) => hnonneg j)
      (Finset.mem_univ i)
    rw [Set.indicator_of_mem hi] at hle
    have h₁ := scalarCubeIndicator_range I (rectangularLatticeSample a S x)
    have h₂ := scalarCubeIndicator_range I x
    exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans hle

theorem scalarCubeGridHistogram_l1_error (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) :
    (∫ x, |scalarCubeGridHistogram I a S x - scalarCubeIndicator I x|) ≤
      scalarCubeGridBoundaryConstant I * δ := by
  let u := (Fintype.card I + 1 : ℝ)*δ
  have hi (i : Bool × Finset I) : Integrable ((scalarCubeFaceSlab i u).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (scalarCubeFaceSlab_finite i u)).integrable_indicator (scalarCubeFaceSlab_measurable i u)
  have h := integral_mono ((scalarCubeGridHistogram_integrable I a S).sub (scalarCubeIndicator_integrable I)).abs
    (integrable_finsetSum _ (fun i _ => hi i)) (scalarCubeGridHistogram_point_error I a S hS hδ hδ1 hmesh)
  calc
    _ ≤ ∫ x, ∑ i : Bool × Finset I, (scalarCubeFaceSlab i u).indicator (fun _ => (1 : ℝ)) x := h
    _ = ∑ i : Bool × Finset I, volume.real (scalarCubeFaceSlab i u) := by
      rw [integral_finsetSum _ (fun i _ => hi i)]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_indicator_one (scalarCubeFaceSlab_measurable i u)
    _ ≤ ∑ _i : Bool × Finset I, (4 : ℝ)^Fintype.card I * (2*u) :=
      Finset.sum_le_sum (fun i _ => scalarCubeFaceSlab_volume_le i (by dsimp [u]; positivity))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, u, scalarCubeGridBoundaryConstant]; ring

theorem scalarCubeGridHistogram_mass_error (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) :
    |(∫ x, scalarCubeGridHistogram I a S x) - volume.real (scalarCubeDomain I)| ≤
      scalarCubeGridBoundaryConstant I * δ := by
  rw [← scalarCubeIndicator_integral I, ← integral_sub (scalarCubeGridHistogram_integrable I a S)
    (scalarCubeIndicator_integrable I)]
  exact (abs_integral_le_integral_abs).trans (scalarCubeGridHistogram_l1_error I a S hS hδ hδ1 hmesh)

theorem scalarCubeGridHistogram_mass_pos (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : scalarCubeGridBoundaryConstant I * δ < volume.real (scalarCubeDomain I)) :
    0 < ∫ x, scalarCubeGridHistogram I a S x := by
  have h := (abs_le.mp (scalarCubeGridHistogram_mass_error I a S hS hδ hδ1 hmesh)).1
  linarith

theorem scalarCubeGridHistogram_normalized_l1 (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) (hpos : 0 < ∫ x, scalarCubeGridHistogram I a S x) :
    (∫ x, |scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y) -
      scalarCubeIndicator I x / volume.real (scalarCubeDomain I)|) ≤
      2 * scalarCubeGridBoundaryConstant I * δ / volume.real (scalarCubeDomain I) := by
  have hV : 0 < volume.real (scalarCubeDomain I) := by
    exact ENNReal.toReal_pos (scalarCubeDomain_volume_pos I).ne' (scalarCubeDomain_volume_lt_top I).ne
  have hn := normalized_density_l1 volume (scalarCubeIndicator I) (scalarCubeGridHistogram I a S)
    (scalarCubeIndicator_integrable I) (scalarCubeGridHistogram_integrable I a S)
    (fun x => by rw [scalarCubeGridHistogram_eq I a S hS]; exact (scalarCubeIndicator_range I _).1)
    (by rwa [scalarCubeIndicator_integral I]) hpos
  rw [scalarCubeIndicator_integral I] at hn
  have he := scalarCubeGridHistogram_l1_error I a S hS hδ hδ1 hmesh
  have hn' : (∫ x, |scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y) -
      scalarCubeIndicator I x / volume.real (scalarCubeDomain I)|) ≤
      2 * (∫ x, |scalarCubeGridHistogram I a S x - scalarCubeIndicator I x|) /
        volume.real (scalarCubeDomain I) := by
    simpa only [abs_sub_comm] using hn
  apply hn'.trans
  calc
    _ ≤ 2 * (scalarCubeGridBoundaryConstant I * δ) / volume.real (scalarCubeDomain I) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) hV.le
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem scalarCubeGridHistogram_finite (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) : scalarCubeGridHistogram I a S =
      finiteRectangularHistogram (scalarCubeGridSet I a S) (fun _ => 1) a S := by
  funext x
  unfold scalarCubeGridHistogram rectangularWeightHistogram finiteRectangularHistogram scalarCubeGridSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : rectangularLatticePoint a S k ∈ halfOpenScalarCubeDomain I
  · simp only [rectangularWeight, scalarCubeIndicator, hk, ite_true]
  · simp only [rectangularWeight, scalarCubeIndicator, hk, ite_false, Set.indicator_zero]

theorem scalarCubeGridHistogram_mean (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) (φ : (Option I → ℝ) → ℝ) :
    (∫ x, (scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y)) *
      φ (rectangularLatticeSample a S x)) =
      𝔼 k ∈ scalarCubeGridSet I a S, φ (rectangularLatticePoint a S k) := by
  rw [scalarCubeGridHistogram_finite]
  exact finiteRectangularHistogram_normalized_mean (scalarCubeGridSet I a S)
    (fun k => φ (rectangularLatticePoint a S k)) a S hS

theorem scalarCubeIndicator_test (I : Type*) [Fintype I] [DecidableEq I]
    (φ : (Option I → ℝ) → ℝ) :
    (∫ x, (scalarCubeIndicator I x / volume.real (scalarCubeDomain I)) * φ x) =
      ∫ x, φ x ∂scalarCubeMeasure I := by
  rw [scalarCubeMeasure_integral]
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div]
  have he : (fun x => scalarCubeIndicator I x * φ x) =ᵐ[volume]
      (scalarCubeDomain I).indicator φ := by
    filter_upwards [halfOpenScalarCubeDomain_ae I] with x hx
    have hx' : (x ∈ halfOpenScalarCubeDomain I) = (x ∈ scalarCubeDomain I) := hx
    simp only [scalarCubeIndicator, hx']
    by_cases h : x ∈ scalarCubeDomain I
    · simp only [h, ite_true, one_mul, Set.indicator_of_mem h]
    · simp only [h, ite_false, zero_mul, Set.indicator_of_notMem h]
  rw [integral_congr_ae he, integral_indicator (scalarCubeDomain_isOpen I).measurableSet]
  simp only [scalarCubeDomainDensity, div_eq_mul_inv, mul_comm]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

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

theorem scalarCubeResidueWeights_grid_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1)*M ≤ L)
    (φ : (Option I → ℝ) → ℝ) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean
      (fun z => φ (fun i => (z i : ℝ) / L)) =
      𝔼 k ∈ scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m),
        φ (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k) := by
  rw [scalarCubeResidueWeights_mean]
  let e := scalarCubeResidueGridEquiv I L hL m r hm
  have he (k : ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m))) :
      rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k.val =
        fun i => ((e k).val i : ℝ) / L := by
    rw [scalarResidueGrid_normalized hL m r hm]
    funext i
    rfl
  calc
    _ = 𝔼 k : ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)),
        φ (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k.val) := by
      symm
      exact Fintype.expect_equiv e _ _ (fun k => congrArg φ (he k))
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe]
      congr 1
      exact Finset.sum_coe_sort _ (fun k =>
        φ (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k))

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
open scoped NNReal BigOperators

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

section

namespace Erdos3

open scoped BigOperators

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeHistogramMeasure
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators Classical

theorem imageMeasure_probability {X Y : Type*} [Fintype X] [MeasurableSpace Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) : IsProbabilityMeasure (p.imageMeasure F) := by
  constructor
  simp only [imageMeasure, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => p.nonneg x), p.total, ENNReal.ofReal_one]

theorem imageMeasure_apply {X Y : Type*} [Fintype X] [MeasurableSpace Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (s : Set Y) (hs : MeasurableSet s) :
    p.imageMeasure F s = ∑ x, if F x ∈ s then ENNReal.ofReal (p.weight x) else 0 := by
  simp only [imageMeasure, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply' _ hs,
    Set.indicator_apply, Pi.one_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem imageMeasure_integral {X Y : Type*} [Fintype X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (φ : Y → ℝ) :
    (∫ y, φ y ∂p.imageMeasure F) = p.mean (fun x => φ (F x)) := by
  rw [imageMeasure, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (p.nonneg _),
      smul_eq_mul, mean]
  · intro x _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators Classical

theorem imageMeasure_pi {D : Type*} [Fintype D] [DecidableEq D]
    {X Y : D → Type*} [∀ d, Fintype (X d)] [∀ d, MeasurableSpace (Y d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (F : ∀ d, X d → Y d) :
    Measure.pi (fun d => (p d).imageMeasure (F d)) =
      (pi p).imageMeasure (fun x d => F d (x d)) := by
  let : ∀ d, IsProbabilityMeasure ((p d).imageMeasure (F d)) := fun d => imageMeasure_probability _ _
  apply Measure.pi_eq
  intro s hs
  rw [imageMeasure_apply _ _ _ (MeasurableSet.univ_pi hs)]
  simp_rw [imageMeasure_apply _ _ _ (hs _)]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hw : ENNReal.ofReal ((pi p).weight x) = ∏ d, ENNReal.ofReal ((p d).weight (x d)) :=
    ENNReal.ofReal_prod_of_nonneg (fun d _ => (p d).nonneg (x d))
  rw [hw]
  by_cases hx : ∀ d, F d (x d) ∈ s d
  · have hm : (fun d => F d (x d)) ∈ Set.univ.pi s := fun d _ => hx d
    simp only [hm, ite_true, hx]
  · have hm : (fun d => F d (x d)) ∉ Set.univ.pi s := fun h => hx (fun d => h d (Set.mem_univ _))
    rw [if_neg hm]
    obtain ⟨d,hd⟩ := not_forall.mp hx
    exact (Finset.prod_eq_zero (Finset.mem_univ d) (if_neg hd)).symm

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeProbabilityDensity_measurable (I : Type*) [Fintype I] [DecidableEq I] :
    Measurable (scalarCubeProbabilityDensity I) := by
  have hm : Measurable (scalarCubeIndicator I) :=
    measurable_const.indicator (halfOpenScalarCubeDomain_measurable I)
  exact hm.div_const _

theorem scalarCubeProbabilityDensity_spec (I : Type*) [Fintype I] [DecidableEq I] :
    Integrable (scalarCubeProbabilityDensity I) ∧
      (∀ x, 0 ≤ scalarCubeProbabilityDensity I x) ∧ (∫ x, scalarCubeProbabilityDensity I x) = 1 := by
  have hV := scalarCubeDomain_volumeReal_pos I
  refine ⟨(scalarCubeIndicator_integrable I).div_const _,
    fun x => div_nonneg (scalarCubeIndicator_range I x).1 hV.le, ?_⟩
  change (∫ x, scalarCubeIndicator I x / volume.real (scalarCubeDomain I)) = 1
  rw [integral_div, scalarCubeIndicator_integral, div_self hV.ne']

theorem scalarCubeProbabilityDensity_measure (I : Type*) [Fintype I] [DecidableEq I] :
    realDensityMeasure volume (scalarCubeProbabilityDensity I) = scalarCubeMeasure I := by
  have h := scalarCubeProbabilityDensity_spec I
  let : IsFiniteMeasure (realDensityMeasure volume (scalarCubeProbabilityDensity I)) :=
    realDensityMeasure_finite volume _ h.1 h.2.1
  apply finiteMeasure_eq_of_integrals
  intro φ _
  rw [realDensityMeasure_integral _ _ (scalarCubeProbabilityDensity_measurable I) h.2.1]
  exact scalarCubeIndicator_test I φ

theorem scalarCubeGridDensity_measurable (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) : Measurable (scalarCubeGridDensity I a S) := by
  have hm : Measurable (scalarCubeIndicator I) :=
    measurable_const.indicator (halfOpenScalarCubeDomain_measurable I)
  have hh : Measurable (scalarCubeGridHistogram I a S) := by
    have he : scalarCubeGridHistogram I a S =
        fun x => scalarCubeIndicator I (rectangularLatticeSample a S x) :=
      funext (scalarCubeGridHistogram_eq I a S hS)
    rw [he]
    exact hm.comp (rectangularLatticeSample_measurable a S)
  exact hh.div_const _

theorem scalarCubeGridDensity_spec (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) (hpos : 0 < ∫ x, scalarCubeGridHistogram I a S x) :
    Integrable (scalarCubeGridDensity I a S) ∧ (∀ x, 0 ≤ scalarCubeGridDensity I a S x) ∧
      (∫ x, scalarCubeGridDensity I a S x) = 1 := by
  refine ⟨(scalarCubeGridHistogram_integrable I a S).div_const _, ?_, ?_⟩
  · intro x
    unfold scalarCubeGridDensity
    rw [scalarCubeGridHistogram_eq I a S hS]
    exact div_nonneg (scalarCubeIndicator_range I _).1 hpos.le
  · unfold scalarCubeGridDensity
    rw [integral_div, div_self hpos.ne']

theorem scalarCubeResidue_imageMeasure (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1)*M ≤ L)
    (hpos : 0 < ∫ x, scalarCubeGridHistogram I (scalarResidueGridOffset m r) (scalarResidueGridScale L m) x) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).imageMeasure
      (fun z i => (z i : ℝ) / L) =
      (realDensityMeasure volume (scalarCubeGridDensity I (scalarResidueGridOffset m r) (scalarResidueGridScale L m))).map
        (rectangularLatticeSample (scalarResidueGridOffset m r) (scalarResidueGridScale L m)) := by
  have hS := scalarResidueGridScale_pos hL m hm
  have hs := scalarCubeGridDensity_spec I _ _ hS hpos
  have hmeas := scalarCubeGridDensity_measurable I (scalarResidueGridOffset m r)
    (scalarResidueGridScale L m) hS
  let : IsProbabilityMeasure ((scalarCubeResidueWeights I L M hL m r hm hmM hsize).imageMeasure
      (fun z i => (z i : ℝ) / L)) := FiniteProbabilityWeights.imageMeasure_probability _ _
  let : IsFiniteMeasure (realDensityMeasure volume
      (scalarCubeGridDensity I (scalarResidueGridOffset m r) (scalarResidueGridScale L m))) :=
    realDensityMeasure_finite _ _ hs.1 hs.2.1
  apply finiteMeasure_eq_of_integrals
  intro φ hφ
  rw [FiniteProbabilityWeights.imageMeasure_integral,
    integral_map (rectangularLatticeSample_measurable _ _).aemeasurable hφ.aestronglyMeasurable,
    realDensityMeasure_integral _ _ hmeas hs.2.1]
  rw [scalarCubeResidueWeights_grid_mean]
  exact (scalarCubeGridHistogram_mean I _ _ hS φ).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointCoefficientRetainedTest
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
open scoped NNReal BigOperators

theorem product_density_rounding_error {J X : Type*} [Fintype J] [DecidableEq J]
    [PseudoMetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : J → Measure X) [∀ j, SigmaFinite (μ j)] (f g : J → X → ℝ)
    (hf : ∀ j, Integrable (f j) (μ j)) (hg : ∀ j, Integrable (g j) (μ j))
    (hf0 : ∀ j x, 0 ≤ f j x) (hg0 : ∀ j x, 0 ≤ g j x)
    (hfm : ∀ j, (∫ x, f j x ∂μ j) = 1) (hgm : ∀ j, (∫ x, g j x ∂μ j) = 1)
    (R : J → X → X) (hR : ∀ j, Measurable (R j)) (δ ε : J → ℝ)
    (hδ : ∀ j, 0 ≤ δ j) (he : ∀ j, (∫ x, |f j x-g j x| ∂μ j) ≤ ε j)
    (hm : ∀ j x, dist (R j x) x ≤ δ j)
    (φ : (J → X) → ℝ) {K : ℝ≥0} {B : ℝ} (hφ : LipschitzWith K φ)
    (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(∫ x, (∏ j, f j (x j)) * φ (fun j => R j (x j)) ∂Measure.pi μ) -
      ∫ x, (∏ j, g j (x j)) * φ x ∂Measure.pi μ| ≤ B * (∑ j, ε j) + K * (∑ j, δ j) := by
  have herr := (tensor_density_l1_le_sum μ f g hf hg hf0 hg0 hfm hgm).trans
    (Finset.sum_le_sum (fun j _ => he j))
  have hmove (x : J → X) : dist (fun j => R j (x j)) x ≤ ∑ j, δ j := by
    apply (dist_pi_le_iff (Finset.sum_nonneg (fun j _ => hδ j))).mpr
    intro j
    exact (hm j (x j)).trans (Finset.single_le_sum (fun k _ => hδ k) (Finset.mem_univ j))
  have hmass : (∫ x, (∏ j, g j (x j)) ∂Measure.pi μ) = 1 := by
    rw [integral_fintype_prod_eq_prod]
    simp only [hgm, Finset.prod_const_one]
  exact density_rounding_test_error (Measure.pi μ) _ _ (Integrable.fintype_prod_dep hf)
    (Integrable.fintype_prod_dep hg) (fun x => Finset.prod_nonneg (fun j _ => hg0 j (x j)))
    hmass (fun x j => R j (x j)) (measurable_pi_iff.mpr (fun j => (hR j).comp (measurable_pi_apply j)))
    hB herr hmove φ hφ hb

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

theorem scalarCubeProductDensity_measure (J I : Type*) [Fintype J] [Fintype I] [DecidableEq I] :
    scalarCubeProductMeasure J I =
      realDensityMeasure volume (tensorCutoffWeight (fun _ : J => scalarCubeProbabilityDensity I)) := by
  rw [scalarCubeProductMeasure, ← scalarCubeProbabilityDensity_measure I]
  exact realDensityMeasure_pi (fun _ => volume) _
    (fun _ => (scalarCubeProbabilityDensity_spec I).1)
    (fun _ => (scalarCubeProbabilityDensity_spec I).2.1)

theorem scalarCubeResidue_pi_imageMeasure {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1)*M j ≤ L j)
    (hpos : ∀ j, 0 < ∫ x, scalarCubeGridHistogram I (scalarResidueGridOffset (m j) (r j))
      (scalarResidueGridScale (L j) (m j)) x) :
    (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).imageMeasure (fun z j i => (z j i : ℝ) / L j) =
      (realDensityMeasure volume (tensorCutoffWeight (fun j =>
        scalarCubeGridDensity I (scalarResidueGridOffset (m j) (r j)) (scalarResidueGridScale (L j) (m j))))).map
      (fun x j => rectangularLatticeSample (scalarResidueGridOffset (m j) (r j))
        (scalarResidueGridScale (L j) (m j)) (x j)) := by
  let f := fun j => scalarCubeGridDensity I (scalarResidueGridOffset (m j) (r j))
    (scalarResidueGridScale (L j) (m j))
  have hs (j : J) := scalarCubeGridDensity_spec I _ _ (scalarResidueGridScale_pos (hL j) (m j) (hm j)) (hpos j)
  let : ∀ j, IsFiniteMeasure (realDensityMeasure volume (f j)) :=
    fun j => realDensityMeasure_finite volume (f j) (hs j).1 (hs j).2.1
  rw [← FiniteProbabilityWeights.imageMeasure_pi
    (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j) (m j) (r j) (hm j) (hmM j) (hsize j))
    (fun j z i => (z i : ℝ) / L j)]
  simp_rw [scalarCubeResidue_imageMeasure I _ _ _ _ _ _ _ _ (hpos _)]
  rw [← Measure.pi_map_pi (fun j => (rectangularLatticeSample_measurable
    (scalarResidueGridOffset (m j) (r j)) (scalarResidueGridScale (L j) (m j))).aemeasurable)]
  rw [realDensityMeasure_pi (fun _ => volume) f (fun j => (hs j).1) (fun j => (hs j).2.1)]
  rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem scalarCubeResidueWeights_pi_riemann {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant I * ((M j : ℝ)/L j) <
      volume.real (scalarCubeDomain I))
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {B : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (fun j i => (z j i : ℝ) / L j)) -
      ∫ x, φ x ∂scalarCubeProductMeasure J I| ≤
      (2 * B * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K) *
        ∑ j, (M j : ℝ)/L j := by
  let a := fun j => scalarResidueGridOffset (m j) (r j)
  let S := fun j => scalarResidueGridScale (L j) (m j)
  let δ := fun j => (M j : ℝ)/L j
  let f := fun j => scalarCubeGridDensity I (a j) (S j)
  let g := fun _ : J => scalarCubeProbabilityDensity I
  have hS (j) : ∀ i, 0 < S j i := scalarResidueGridScale_pos (hL j) (m j) (hm j)
  have hδ (j) : 0 ≤ δ j := by dsimp only [δ]; positivity
  have hδ1 (j) : δ j ≤ 1 := by
    have hML : M j ≤ L j := by nlinarith [hsize j]
    exact (div_le_one (by exact_mod_cast hL j)).mpr (by exact_mod_cast hML)
  have hmesh (j) (i : Option I) : 1 / S j i ≤ δ j := by
    dsimp only [S, δ, scalarResidueGridScale]
    rw [one_div_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmM j i) (by positivity)
  have hpos (j) : 0 < ∫ x, scalarCubeGridHistogram I (a j) (S j) x :=
    scalarCubeGridHistogram_mass_pos I _ _ (hS j) (hδ j) (hδ1 j) (hmesh j) (hsmall j)
  have hf (j) := scalarCubeGridDensity_spec I (a j) (S j) (hS j) (hpos j)
  have hg := scalarCubeProbabilityDensity_spec I
  have hfm : Measurable (tensorCutoffWeight f) := by
    apply Finset.measurable_prod
    intro j _
    exact (scalarCubeGridDensity_measurable I (a j) (S j) (hS j)).comp (measurable_pi_apply j)
  have hgm : Measurable (tensorCutoffWeight g) := by
    apply Finset.measurable_prod
    intro j _
    exact (scalarCubeProbabilityDensity_measurable I).comp (measurable_pi_apply j)
  have hR : Measurable (fun (x : J → Option I → ℝ) j => rectangularLatticeSample (a j) (S j) (x j)) :=
    measurable_pi_iff.mpr (fun j => (rectangularLatticeSample_measurable _ _).comp (measurable_pi_apply j))
  rw [← FiniteProbabilityWeights.imageMeasure_integral _ _ φ,
    scalarCubeResidue_pi_imageMeasure L M hL m r hm hmM hsize hpos,
    integral_map hR.aemeasurable hφ.continuous.measurable.aestronglyMeasurable,
    realDensityMeasure_integral _ _ hfm (tensorCutoffWeight_nonneg f (fun j => (hf j).2.1)),
    scalarCubeProductDensity_measure,
    realDensityMeasure_integral _ _ hgm (tensorCutoffWeight_nonneg g (fun _ => hg.2.1))]
  have he (j) : (∫ x, |f j x-g j x|) ≤
      (2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I)) * δ j :=
    (scalarCubeGridHistogram_normalized_l1 I (a j) (S j) (hS j) (hδ j) (hδ1 j)
      (hmesh j) (hpos j)).trans_eq (by ring)
  have hmove (j) (x) : dist (rectangularLatticeSample (a j) (S j) x) x ≤ δ j := by
    rw [dist_eq_norm]
    exact rectangularLatticeSample_error _ _ (hS j) (hδ j) (hmesh j) x
  exact (product_density_rounding_error (fun _ => volume) f g
    (fun j => (hf j).1) (fun _ => hg.1) (fun j => (hf j).2.1) (fun _ => hg.2.1)
    (fun j => (hf j).2.2) (fun _ => hg.2.2) (fun j => rectangularLatticeSample (a j) (S j))
    (fun j => rectangularLatticeSample_measurable (a j) (S j)) δ _ hδ he hmove φ hφ hB hb).trans_eq
      (by rw [← Finset.mul_sum]; dsimp only [δ]; ring)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

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
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineKernelEndpointGeometry
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J I : Type*} [Fintype J] [Fintype I]

theorem affineCubeTuple_lipschitz (lower width : J → ℝ) (K : ℝ≥0)
    (hw : ∀ j, |width j| ≤ K) : LipschitzWith K (affineCubeTuple (I := I) lower width) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).mpr
  intro j
  apply (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).mpr
  intro i
  simp only [affineCubeTuple, dist_add_left, Real.dist_eq, ← mul_sub, abs_mul]
  simpa only [Real.dist_eq] using mul_le_mul (hw j)
    ((dist_le_pi_dist (x j) (y j) i).trans (dist_le_pi_dist x y j))
    dist_nonneg K.coe_nonneg

theorem affineCubeTuple_width_dist (lower w v : J → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ j, |w j - v j| ≤ ε) (x : J → Option I → ℝ) (hx : ‖x‖ ≤ 1) :
    dist (affineCubeTuple lower w x) (affineCubeTuple lower v x) ≤ ε := by
  apply (dist_pi_le_iff hε).mpr
  intro j
  apply (dist_pi_le_iff hε).mpr
  intro i
  have hxj : |x j i| ≤ 1 := by
    exact (norm_le_pi_norm (x j) i).trans ((norm_le_pi_norm x j).trans hx)
  simp only [affineCubeTuple, dist_add_left, Real.dist_eq, ← sub_mul, abs_mul]
  exact (mul_le_mul (hw j) hxj (abs_nonneg _) hε).trans_eq (mul_one _)

theorem affineCubeTuple_integral_width_error [DecidableEq I]
    (lower w v : J → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hw : ∀ j, |w j - v j| ≤ ε)
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzWith K φ) (_hA : 0 ≤ A) (hb : ∀ x, ‖φ x‖ ≤ A) :
    |(∫ x, φ (affineCubeTuple lower w x) ∂scalarCubeProductMeasure J I) -
      ∫ x, φ (affineCubeTuple lower v x) ∂scalarCubeProductMeasure J I| ≤ K * ε := by
  have hm (v : J → ℝ) : Measurable (affineCubeTuple (I := I) lower v) := by
    unfold affineCubeTuple
    fun_prop
  have hi (v : J → ℝ) : Integrable (fun x => φ (affineCubeTuple lower v x)) (scalarCubeProductMeasure J I) :=
    Integrable.mono' (integrable_const A) (hφ.continuous.measurable.comp (hm v)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => hb _))
  rw [← integral_sub (hi w) (hi v)]
  have he : ∀ᵐ x ∂scalarCubeProductMeasure J I,
      ‖φ (affineCubeTuple lower w x) - φ (affineCubeTuple lower v x)‖ ≤ K * ε := by
    filter_upwards [scalarCubeProductMeasure_ae_closedBall J I] with x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [← dist_eq_norm]
    exact (hφ.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (affineCubeTuple_width_dist lower w v hε hw x hx) K.coe_nonneg)
  have ht := norm_integral_le_of_norm_le (integrable_const ((K : ℝ) * ε) (μ := scalarCubeProductMeasure J I)) he
  simpa only [Real.norm_eq_abs, integral_const, probReal_univ, one_smul] using ht

theorem affineCubeTuple_residue_riemann [DecidableEq J] [DecidableEq I]
    (H M : J → ℕ) (hH : ∀ j, 0 < H j) (modulus : J → Option I → ℕ)
    (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant I * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain I))
    (lower w v : J → ℝ) (W : ℝ≥0) (hw : ∀ j, |w j| ≤ W)
    {ε : ℝ} (hε : 0 ≤ ε) (hwidth : ∀ j, |w j - v j| ≤ ε)
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzWith K φ) (hA : 0 ≤ A) (hb : ∀ x, ‖φ x‖ ≤ A) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (H j) (M j) (hH j)
      (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (affineCubeTuple lower w (fun j i => (z j i : ℝ) / H j))) -
      ∫ x, φ (affineCubeTuple lower v x) ∂scalarCubeProductMeasure J I| ≤
      (2 * A * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K * W) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  have htest := hφ.comp (affineCubeTuple_lipschitz lower w W hw)
  have he := scalarCubeResidueWeights_pi_riemann H M hH modulus residue hm hmM hsize hsmall
    (φ ∘ affineCubeTuple lower w) htest hA (fun x => hb _)
  have hi := affineCubeTuple_integral_width_error lower w v hε hwidth φ hφ hA hb
  exact (abs_sub_le _ _ _).trans (add_le_add he hi)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical
variable {G : Type*} [Fintype G]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProgressionTupleSliceRiemann
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]

theorem progressionTuple_residue_riemann
    (L step H M : J → ℕ) (c : J → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : J → Option I → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant I * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain I))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzWith K φ) (hA : 0 ≤ A) (hb : ∀ x, ‖φ x‖ ≤ A) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (fun j i =>
          ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j)) -
      ∫ x, φ (affineCubeTuple (fun j => (c j : ℝ) / L j)
        (fun j => (step j : ℝ) * ((H j : ℝ) - 1) / L j) x) ∂scalarCubeProductMeasure J I| ≤
      (2 * A * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  have hHp (j) : 0 < H j := by have := hH j; omega
  let lower := fun j => (c j : ℝ) / L j
  let w := fun j => (step j : ℝ) * H j / L j
  let v := fun j => (step j : ℝ) * ((H j : ℝ) - 1) / L j
  have hw (j) : |w j| ≤ (2 : ℝ≥0) := by
    have he := (progression_slice_geometry (c j) (hL j) (hstep j) (hH j) hδ (hsubset j) (hdense j)).2.1
    dsimp only [w]
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (by exact_mod_cast hL j : (0 : ℝ) < L j)).mpr
    simpa only [Nat.cast_mul, NNReal.coe_ofNat] using he.le
  have hv (j) : |w j - v j| ≤ ε := by
    have he : w j - v j = (step j : ℝ) / L j := by dsimp [w, v]; ring
    rw [he, abs_of_nonneg (by positivity)]
    exact hmesh j
  have he := affineCubeTuple_residue_riemann H M hHp modulus residue hm hmM hsize hsmall
    lower w v 2 hw hε hv φ hφ hA hb
  have hid (z : ∀ j, IntegerScalarCubeBox I (H j)) :
      affineCubeTuple lower w (fun j i => (z j i : ℝ) / H j) =
        fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j := by
    funext j i
    have hH0 : (H j : ℝ) ≠ 0 := by exact_mod_cast (hHp j).ne'
    dsimp only [affineCubeTuple, lower, w]
    split_ifs <;> field_simp
    ring
  simp_rw [hid] at he
  exact he

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionTupleSliceSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

theorem condition_weight_pos_iff {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < p.mass S) (x : Ω) :
    0 < (p.condition S hS).weight x ↔ x ∈ S ∧ 0 < p.weight x := by
  change 0 < (if x ∈ S then p.weight x else 0) / p.mass S ↔ _
  rw [lt_div_iff₀ hS, zero_mul]
  by_cases hx : x ∈ S <;> simp [hx]

theorem pi_weight_pos_component {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (x : ∀ j, Ω j) (hx : 0 < (pi p).weight x) (j : J) : 0 < (p j).weight (x j) := by
  apply lt_of_le_of_ne ((p j).nonneg (x j))
  intro he
  have hz : (pi p).weight x = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ j) he.symm
  linarith

end FiniteProbabilityWeights

theorem scalarCubeResidueWeights_cube_support (I : Type*) [Fintype I] [DecidableEq I]
    (H M : ℕ) (hH : 0 < H) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ H) (z : IntegerScalarCubeBox I H)
    (hz : 0 < (scalarCubeResidueWeights I H M hH m r hm hmM hsize).weight z) :
    IntegerScalarCube H (fun i => (z i : ℤ)) := by
  have h1 := (FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ z).mp hz
  have h2 := (FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ z).mp h1.2
  exact (mem_integerScalarCubeSet H z).mp h2.1

theorem integerScalarCube_endpoint_normalized_norm_le {I : Type*} [Fintype I] [DecidableEq I]
    {H : ℕ} (hH : 2 ≤ H) (z : Option I → ℤ) (hz : IntegerScalarCube H z) :
    ‖fun i => (z i : ℝ) / ((H : ℝ) - 1)‖ ≤ 1 := by
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hi := integerScalarCube_coordinates hz i
  have hzi : -(H : ℤ) + 1 ≤ z i ∧ z i ≤ (H : ℤ) - 1 := by omega
  have hr : |(z i : ℝ)| ≤ (H : ℝ) - 1 := by
    apply abs_le.mpr
    have hl : -(H : ℝ) + 1 ≤ (z i : ℝ) := by exact_mod_cast hzi.1
    have hu : (z i : ℝ) ≤ (H : ℝ) - 1 := by exact_mod_cast hzi.2
    constructor <;> linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : 0 < (H : ℝ) - 1)]
  exact (div_le_one (by linarith)).mpr hr

theorem affineCubeTuple_norm_le {J I : Type*} [Fintype J] [Fintype I]
    (lower width : J → ℝ) (hw : ∀ j, |lower j| + |width j| ≤ 1)
    (x : J → Option I → ℝ) (hx : ‖x‖ ≤ 1) : ‖affineCubeTuple lower width x‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hxi : |x j i| ≤ 1 :=
    (norm_le_pi_norm (x j) i).trans ((norm_le_pi_norm x j).trans hx)
  have hc : |if i = none then lower j else 0| ≤ |lower j| := by
    split_ifs <;> simp
  exact (abs_add_le _ _).trans ((add_le_add hc
    ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left hxi (abs_nonneg _)))).trans
      (by simpa using hw j))

theorem progressionTuple_norm_le {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (L step H : J → ℕ) (c : J → ℤ) (hH : ∀ j, 2 ≤ H j)
    (hw : ∀ j, |(c j : ℝ) / L j| + |(step j : ℝ) * ((H j : ℝ) - 1) / L j| ≤ 1)
    (z : ∀ j, IntegerScalarCubeBox I (H j))
    (hz : ∀ j, IntegerScalarCube (H j) (fun i => (z j i : ℤ))) :
    ‖fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j‖ ≤ 1 := by
  have hn : ‖fun j i => (z j i : ℝ) / ((H j : ℝ) - 1)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    exact integerScalarCube_endpoint_normalized_norm_le (hH j) _ (hz j)
  have he := affineCubeTuple_norm_le (fun j => (c j : ℝ) / L j)
    (fun j => (step j : ℝ) * ((H j : ℝ) - 1) / L j) hw _ hn
  convert he using 2
  funext j i
  have hd : (H j : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ H j := by exact_mod_cast hH j
    linarith
  dsimp only [affineCubeTuple]
  split_ifs <;> field_simp
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OneCubePrincipalSliceRiemann
namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]

theorem progressionTuple_residue_riemann_on_box
    (L step H M : J → ℕ) (c : J → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : J → Option I → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant I * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain I))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzOnWith K φ (Metric.closedBall 0 1)) (hA : 0 ≤ A)
    (hb : ∀ x ∈ Metric.closedBall 0 1, ‖φ x‖ ≤ A) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (fun j i =>
          ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j)) -
      ∫ x, φ (affineCubeTuple (fun j => (c j : ℝ) / L j)
        (fun j => (step j : ℝ) * ((H j : ℝ) - 1) / L j) x) ∂scalarCubeProductMeasure J I| ≤
      (2 * A * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  obtain ⟨g, hg, heq, hgb⟩ := exists_real_lipschitz_extension_interval φ (Metric.closedBall 0 1)
    K hφ (-A) A (neg_le_self hA)
    (fun x hx => abs_le.mp (by simpa only [Real.norm_eq_abs] using hb x hx))
  have hHp (j) : 0 < H j := by have := hH j; omega
  let p := FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (H j) (M j)
    (hHp j) (modulus j) (residue j) (hm j) (hmM j) (hsize j))
  let F := fun (z : ∀ j, IntegerScalarCubeBox I (H j)) j i =>
    ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j
  let lower := fun j => (c j : ℝ) / L j
  let width := fun j => (step j : ℝ) * ((H j : ℝ) - 1) / L j
  have hw (j) : |lower j| + |width j| ≤ 1 :=
    (progression_slice_endpoint_geometry (c j) (hL j) (hstep j) (hH j) hδ
      (hsubset j) (hdense j)).2.2.1
  have hd (z) (hz : 0 < p.weight z) : F z ∈ Metric.closedBall 0 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply progressionTuple_norm_le L step H c hH hw z
    intro j
    exact scalarCubeResidueWeights_cube_support I (H j) (M j) (hHp j) (modulus j) (residue j)
      (hm j) (hmM j) (hsize j) (z j)
      (FiniteProbabilityWeights.pi_weight_pos_component _ z hz j)
  have hmean : p.mean (φ ∘ F) = p.mean (g ∘ F) := by
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : p.weight z = 0
    · simp only [hz, zero_mul]
    · rw [Function.comp_apply, Function.comp_apply,
        heq (hd z (lt_of_le_of_ne (p.nonneg z) (Ne.symm hz)))]
  have hint : (∫ x, φ (affineCubeTuple lower width x) ∂scalarCubeProductMeasure J I) =
      ∫ x, g (affineCubeTuple lower width x) ∂scalarCubeProductMeasure J I := by
    apply integral_congr_ae
    filter_upwards [scalarCubeProductMeasure_ae_closedBall J I] with x hx
    apply heq
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    exact affineCubeTuple_norm_le lower width hw x hx
  change |p.mean (φ ∘ F) - ∫ x, φ (affineCubeTuple lower width x) ∂scalarCubeProductMeasure J I| ≤ _
  rw [hmean, hint]
  exact progressionTuple_residue_riemann L step H M c hL hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh g hg hA
    (fun x => by simpa only [Real.norm_eq_abs] using abs_le.mpr (hgb x))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators NNReal

theorem principalProgressionSlice_residue_riemann
    {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ)
    (L step H M : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : PrincipalTupleIndex B h → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
    (φ : (JointBlockParameter B h α → ℝ) → ℝ)
    {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzOnWith K φ (Metric.closedBall 0 1)) (hA : 0 ≤ A)
    (hb : ∀ x ∈ Metric.closedBall 0 1, ‖φ x‖ ≤ A) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (principalTupleFlatten B h α
          (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j))) -
      ∫ x, φ (fun i => principalProgressionSliceCenter (α := α) B h L c i +
          principalProgressionSliceWidth (α := α) B h L H step i * x i)
        ∂jointBooleanSource h| ≤
      (2 * A * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  let F := principalTupleFlatten B h α
  have hF : Set.MapsTo F (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    exact (principalTupleFlatten_norm_apply_le _ _ _ x).trans hx
  have hlip : LipschitzOnWith K (φ ∘ F) (Metric.closedBall 0 1) := by
    simpa only [mul_one] using hφ.comp
      (principalTupleFlatten_lipschitz _ _ _).lipschitzOnWith hF
  rw [jointBooleanSource_principalTuple_integral]
  change |(FiniteProbabilityWeights.pi _).mean _ -
    ∫ x, (φ ∘ F) (affineCubeTuple (fun j => (c j : ℝ) / L j)
      (fun j => (step j : ℝ) * ((H j : ℝ) - 1) / L j) x)
      ∂scalarCubeProductMeasure (PrincipalTupleIndex B h) α| ≤ _
  exact progressionTuple_residue_riemann_on_box L step H M c hL hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh (φ ∘ F) hlip hA (fun x hx => hb _ (hF hx))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

variable {D : Type*} [Fintype D] {B : D → Type*} [∀ d, Fintype (B d)]
variable (h : D → ℕ) (P : D → Prop) [DecidablePred P]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EarlyAllocatedAffineResidueSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B α O P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedAffineLongJetProxy_residue_error (hσ1 : ∀ j, σ j ≤ 1)
    (L step H M : Tuple → ℕ) (c : Tuple → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Tuple → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε) (z : Jet → ℝ) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
          (principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) α
            (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z) -
      allocatedAffineLongJetProxy B U basis S x u rows s hA
        (principalProgressionSliceCenter (α := α) (fun a : {a // ¬grid a} => B a.val)
          (fun a => degree a.val) L c)
        (principalProgressionSliceWidth (α := α) (fun a : {a // ¬grid a} => B a.val)
          (fun a => degree a.val) L H step) z| ≤
      (2 * (cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
        (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε := by
  have hb := allocatedNormalizedLongJetDensity_parameter_bounds B U basis hR hσ S x
    rows s hA hMk hi hP hMkP hRP hRi hσi hcount u hσ1 z
  exact principalProgressionSlice_residue_riemann
    (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val)
    L step H M c hL hstep hH hδ hsubset hdense modulus residue hm hmM hsize hsmall hε hmesh
    (fun y => allocatedNormalizedLongJetDensity B U basis S x u rows s hA y z)
    hb.2 (NNReal.coe_nonneg cap) (fun y _ => hb.1 y)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [dG : DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value

include hR hσ hM hi hP hMP hRP hRi hσi hcount

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B α O P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_residue_error.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_residue_error.{u_1, u_2, u_3, u_4, u_5, u_6}
