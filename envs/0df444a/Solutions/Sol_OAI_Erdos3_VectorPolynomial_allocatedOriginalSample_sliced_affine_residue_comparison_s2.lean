-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_sliced_affine_residue_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:45:26.916187+00:00
-- url     : https://prove2.me/submissions/e99d1cdb-cd9c-49bb-8ab0-c9d326abd4d9

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B177
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedOriginalSampleFullSliceMap_supported_lipschitzOn_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedOriginalSample_slice_complex_perturbation_s2
import Theorems.Thm_OAI_Erdos3_progressionTuple_residue_riemann_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

theorem scalarResidue_card_mul_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r ≤ b - a + r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := Int.Ico_filter_modEq_card a b hr v
  have hcQ := congrArg (fun n : ℤ => (n : ℚ)) hc
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hcQ
  have hn : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) / r :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hrQ.le
  have hbound : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) ≤
      ((b - a : ℤ) : ℚ) / r + 1 := by
    rw [hcQ]
    apply max_le
    · have hx := Int.ceil_lt_add_one (((b : ℚ) - v) / r)
      have hy := Int.le_ceil (((a : ℚ) - v) / r)
      have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
        push_cast
        ring
      linarith
    · linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r + 1) * r = (b - a : ℤ) + (r : ℚ) := by
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_real_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) ≤
      ((b - a : ℤ) : ℝ) / r + 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_mul_le a b r v hab hr
  have hR : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r ≤
      ((b - a : ℤ) : ℝ) + r := by exact_mod_cast h
  have heq : ((b - a : ℤ) : ℝ) + r = (((b - a : ℤ) : ℝ) / r + 1) * r := by
    field_simp
  rw [heq] at hR
  exact (mul_le_mul_iff_left₀ hrR).mp hR

end Erdos3

end

section

namespace Erdos3

theorem scalarResidue_card_mul_ge (a b r v : ℤ) (hr : 0 < r) :
    b - a - r ≤ ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := congrArg (fun n : ℤ => (n : ℚ)) (Int.Ico_filter_modEq_card a b hr v)
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hc
  have hbound : ((b - a : ℤ) : ℚ) / r - 1 ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) := by
    rw [hc]
    apply le_trans _ (le_max_left _ _)
    have hx := Int.le_ceil (((b : ℚ) - v) / r)
    have hy := Int.ceil_lt_add_one (((a : ℚ) - v) / r)
    have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
      push_cast
      ring
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r - 1) * r = ((b - a - r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) -
      ((b - a : ℤ) : ℝ) / r| ≤ 1 := by
  have hu := scalarResidue_card_real_le a b r v hab hr
  have hl : ((b - a - r : ℤ) : ℝ) ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r := by
    exact_mod_cast scalarResidue_card_mul_ge a b r v hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heq : (((b - a : ℤ) : ℝ) / r - 1) * r = ((b - a - r : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [← heq] at hl
  have hlow := (mul_le_mul_iff_left₀ hrR).mp hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmbeddedFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem norm_complexMean_sub_le_weight_l1 {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.complexMean f - q.complexMean f‖ ≤ ∑ x, |p.weight x - q.weight x| := by
  simp only [complexMean, ← Finset.sum_sub_distrib, ← sub_mul, ← Complex.ofReal_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)).trans_eq (mul_one _)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeMeasure_ae_domain (α : Type*) [Fintype α] [DecidableEq α] :
    ∀ᵐ a ∂scalarCubeMeasure α, a ∈ scalarCubeDomain α := by
  apply ae_iff.mpr
  change scalarCubeMeasure α (scalarCubeDomain α)ᶜ = 0
  simp [scalarCubeMeasure, Measure.smul_apply,
    Measure.restrict_apply (scalarCubeDomain_isOpen α).measurableSet.compl]

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

theorem unitBoxMeasure_eq_pi :
    unitBoxMeasure ι = Measure.pi (fun _ : ι => unitScalarMeasure) := by
  change (Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict
    (Set.univ.pi (fun _ => Set.Ioc (0 : ℝ) 1)) = _
  exact Measure.restrict_pi_pi _ _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeDomain_empty :
    scalarCubeDomain Empty =
      (fun x : Option Empty → ℝ => x none) ⁻¹' Set.Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    simpa only [Set.mem_preimage, scalarCubeValue_empty] using hx ∅
  · intro hx t
    have ht : t = ∅ := Subsingleton.elim _ _
    simpa only [ht, scalarCubeValue_empty, Set.mem_preimage] using hx

theorem scalarCubeDomain_empty_volume : volume (scalarCubeDomain Empty) = 1 := by
  have hm : MeasurePreserving (fun x : Option Empty → ℝ => x none) volume volume :=
    volume_preserving_funUnique (Option Empty) ℝ
  rw [scalarCubeDomain_empty, hm.measure_preimage measurableSet_Ioo.nullMeasurableSet]
  simp

theorem scalarCubeMeasure_empty_map :
    (scalarCubeMeasure Empty).map (fun x => x none) = unitScalarMeasure := by
  have hm : MeasurePreserving (fun x : Option Empty → ℝ => x none) volume volume :=
    volume_preserving_funUnique (Option Empty) ℝ
  rw [scalarCubeMeasure, scalarCubeDomain_empty_volume, inv_one, one_smul,
    scalarCubeDomain_empty, (hm.restrict_preimage measurableSet_Ioo).map_eq]
  exact restrict_Ioo_eq_restrict_Ioc

theorem scalarCubeProductMeasure_empty_map (J : Type*) [Fintype J] :
    (scalarCubeProductMeasure J Empty).map (fun x j => x j none) = unitBoxMeasure J := by
  have hm : MeasurePreserving (fun x : Option Empty → ℝ => x none)
      (scalarCubeMeasure Empty) unitScalarMeasure :=
    ⟨measurable_pi_apply none, scalarCubeMeasure_empty_map⟩
  have hp := (measurePreserving_pi (fun _ : J => scalarCubeMeasure Empty)
    (fun _ : J => unitScalarMeasure) (fun _ => hm)).map_eq
  simpa only [scalarCubeProductMeasure, unitBoxMeasure_eq_pi] using hp

theorem scalarCubeProductMeasure_empty_integral (J : Type*) [Fintype J]
    (φ : (J → ℝ) → ℝ) (hφ : Measurable φ) :
    (∫ x, φ (fun j => x j none) ∂scalarCubeProductMeasure J Empty) =
      ∫ y, φ y ∂unitBoxMeasure J := by
  have hm : Measurable (fun x : J → Option Empty → ℝ => fun j => x j none) := by fun_prop
  rw [← scalarCubeProductMeasure_empty_map J]
  exact (integral_map hm.aemeasurable hφ.aestronglyMeasurable).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]

theorem pi_condition (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (G : ∀ j, Finset (Ω j)) (hG : ∀ j, 0 < (p j).mass (G j)) :
    pi (fun j => (p j).condition (G j) (hG j)) =
      (pi p).condition (piRestrictionSet G) (piRestriction_mass_pos p G hG) := by
  classical
  apply ext_weight
  funext x
  change (∏ j, (if x j ∈ G j then (p j).weight (x j) else 0) / (p j).mass (G j)) =
    (if x ∈ piRestrictionSet G then ∏ j, (p j).weight (x j) else 0) /
      (pi p).mass (piRestrictionSet G)
  rw [piRestriction_mass, Finset.prod_div_distrib]
  congr 1
  by_cases hx : ∀ j, x j ∈ G j
  · simp only [hx, ite_true, (mem_piRestrictionSet G x).mpr hx]
  · rw [if_neg ((mem_piRestrictionSet G x).not.mpr hx)]
    obtain ⟨j, hj⟩ := not_forall.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerBoxCharacterBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerInterval_indicator_expect (a b : ℤ) (hab : a ≤ b) (E : ℤ → Prop)
    [DecidablePred E] :
    (𝔼 x : Finset.Ico a b, if E x then (1 : ℝ) else 0) =
      ((Finset.filter E (Finset.Ico a b)).card : ℝ) / ((b - a : ℤ) : ℝ) := by
  classical
  rw [Fintype.expect_eq_sum_div_card,
    Finset.sum_coe_sort (Finset.Ico a b) (fun x : ℤ => if E x then (1 : ℝ) else 0),
    Fintype.card_coe]
  have hcard : ((Finset.Ico a b).card : ℝ) = ((b - a : ℤ) : ℝ) := by
    exact_mod_cast Int.card_Ico_of_le a b hab
  rw [hcard]
  congr 1
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3


open scoped BigOperators

theorem integerScalarCubeWeights_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L : ℕ) (hL : 0 < L) (f : IntegerScalarCubeBox I L → ℝ) :
    (integerScalarCubeWeights I L hL).mean f = 𝔼 x : integerScalarCubeSet I L, f x := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  exact FiniteProbabilityWeights.uniform_condition_mean (integerScalarCubeSet I L)
    (integerScalarCubeReference_mass_pos I L hL) f

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI


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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IntervalDivisorProbability
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem intervalUniformWeights_mean (a b : ℤ) (hab : a < b) (f : Finset.Ico a b → ℝ) :
    (intervalUniformWeights a b hab).mean f = 𝔼 x, f x := by
  let : Nonempty (Finset.Ico a b) := ⟨⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩⟩
  unfold intervalUniformWeights
  exact FiniteProbabilityWeights.uniform_mean f

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

theorem FiniteProbabilityWeights.complexMean_im {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (F : X → ℂ) :
    (p.complexMean F).im = p.mean (fun x => (F x).im) := by
  simp [complexMean, mean, Complex.mul_im]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedSliceFamilyLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerScalarCubeWeights_zero_mean (α : Type*) [Fintype α]
    [DecidableEq α] [IsEmpty α] (L : ℕ) (hL : 0 < L) (f : ℤ → ℝ) :
    (integerScalarCubeWeights α L hL).mean (fun x => f (x none : ℤ)) =
      (intervalUniformWeights 0 (L : ℤ) (by exact_mod_cast hL)).mean
        (fun x => f x.val) := by
  rw [integerScalarCubeWeights_mean, intervalUniformWeights_mean]
  exact Fintype.expect_equiv (zeroScalarCubeIntervalEquiv α L) _ _ (fun _ => rfl)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedIntegerBoxZeroCube
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem FiniteProbabilityWeights.pi_uniform_complexMean
    {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (f : (∀ i, A i) → ℂ) :
    (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (A i))).complexMean f =
      𝔼 x, f x := by
  change (∑ x : ∀ i, A i, ((∏ i, (Fintype.card (A i) : ℝ)⁻¹ : ℝ) : ℂ) * f x) = _
  have hcard : (∏ i, (Fintype.card (A i) : ℝ)⁻¹) =
      (Fintype.card (∀ i, A i) : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    simp only [Fintype.card_pi, Nat.cast_prod]
  rw [hcard]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem FiniteProbabilityWeights.scaled_condition_complexMean {X : Type*}
    [Fintype X] [DecidableEq X] (p : FiniteProbabilityWeights X) (G : Finset X)
    (hG : 0 < p.mass G) (f : X → ℂ) :
    (p.mass G : ℂ) * (p.condition G hG).complexMean f =
      p.complexMean (fun x => if x ∈ G then f x else 0) := by
  unfold FiniteProbabilityWeights.complexMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hM : (p.mass G : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  by_cases hx : x ∈ G
  · simp only [FiniteProbabilityWeights.condition, hx, ite_true, Complex.ofReal_div]
    field_simp
  · simp [FiniteProbabilityWeights.condition, hx]

theorem FiniteProbabilityWeights.complexMean_disintegrate {X R : Type*}
    [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R)
    (hp : ∀ r, 0 < p.mass (Finset.univ.filter (fun x => F x = r))) (f : R → X → ℂ) :
    p.complexMean (fun x => f (F x) x) =
      (p.fiberLaw F).complexMean (fun r =>
        (p.condition (Finset.univ.filter (fun x => F x = r)) (hp r)).complexMean (f r)) := by
  change _ = ∑ r, ((p.fiberLaw F).weight r : ℂ) * _
  simp_rw [p.fiberLaw_weight_eq_mass, p.scaled_condition_complexMean]
  unfold FiniteProbabilityWeights.complexMean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IndependentEmbeddedMixture
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
  [∀ j, DecidableEq (R j)]

theorem pi_condition_fiber (p : ∀ j, FiniteProbabilityWeights (X j))
    (F : ∀ j, X j → R j) (r : ∀ j, R j)
    (hr : ∀ j, 0 < (p j).mass (Finset.univ.filter (fun x => F j x = r j))) :
    (pi p).condition (Finset.univ.filter (fun x => (fun j => F j (x j)) = r))
        (pi_fiber_mass_pos p F r hr) =
      pi (fun j => (p j).condition (Finset.univ.filter (fun x => F j x = r j)) (hr j)) := by
  simpa only [← pi_fiber_set F r] using
    (pi_condition p (fun j => Finset.univ.filter (fun x => F j x = r j)) hr).symm

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRelativeChildSliceGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleSliceSubstitution_eval (y : Input → ℝ) (k : vars) :
    MvPolynomial.eval y (allocatedOriginalSampleSliceSubstitution B U basis S x u lower width k) =
      allocatedOriginalSampleSliceInput B U basis S x u lower width y k := by
  rcases k with g | ⟨a, b, i⟩
  · simp only [allocatedOriginalSampleSliceSubstitution, allocatedOriginalSampleSliceInput,
      MvPolynomial.eval_C]
  · by_cases ha : short a <;>
      simp [allocatedOriginalSampleSliceSubstitution, allocatedOriginalSampleSliceInput, ha]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OneCubePrincipalSliceRiemann
namespace OAI

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
  exact progressionTuple_residue_riemann_s2 L step H M c hL hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh g hg hA
    (fun x => by simpa only [Real.norm_eq_abs] using abs_le.mpr (hgb x))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleFullSliceLipschitz
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleFullSliceMap_eq_eval (sample : Sample) (y : Input → ℝ) (o : Output) :
    allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y o =
      MvPolynomial.eval (allocatedOriginalSampleSliceInput B U basis S x u lower width y)
        (monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val)) /
          R o.1.val.1 := by
  simp only [allocatedOriginalSampleFullSliceMap, allocatedOriginalSampleSliceSubstitution_eval]

theorem allocatedOriginalSampleFullSliceMap_measurable (sample : Sample) :
    Measurable (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample) := by
  apply measurable_pi_iff.mpr
  intro o
  have hi : Continuous (fun y : Input → ℝ => fun k => MvPolynomial.eval y
      (allocatedOriginalSampleSliceSubstitution B U basis S x u lower width k)) :=
    continuous_pi (fun k => MvPolynomial.continuous_eval _)
  exact (((MvPolynomial.continuous_eval
    (monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val))).comp hi).div_const
      (R o.1.val.1)).measurable

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

theorem allocatedOriginalSampleFullSliceMap_affine (sample : Sample)
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ) (y : Input → ℝ) :
    allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1) sample
        (fun j => lower j.1 j.2 + width j.1 j.2 * y j) =
      allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y := by
  have hi : allocatedOriginalSampleSliceInput B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
      (fun j => lower j.1 j.2 + width j.1 j.2 * y j) =
      allocatedOriginalSampleSliceInput B U basis S x u lower width y := by
    funext k
    rcases k with g | ⟨a, b, i⟩
    · rfl
    · by_cases ha : short a <;> simp [allocatedOriginalSampleSliceInput, ha]
  funext o
  simp only [allocatedOriginalSampleFullSliceMap_eq_eval, hi]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductWeightL1
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

private theorem abs_sub_min_identity (x y : ℝ) :
    |x - y| = x + y - 2 * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem pi_weight_l1_le_sum {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p q : ∀ j, FiniteProbabilityWeights (Ω j)) :
    (∑ x, |(pi p).weight x - (pi q).weight x|) ≤
      ∑ j, ∑ x, |(p j).weight x - (q j).weight x| := by
  classical
  let h : ∀ j, Ω j → ℝ := fun j x => min ((p j).weight x) ((q j).weight x)
  let a : J → ℝ := fun j => ∑ x, h j x
  have hh (j) (x : Ω j) : 0 ≤ h j x := le_min ((p j).nonneg x) ((q j).nonneg x)
  have ha0 (j) : 0 ≤ a j := Finset.sum_nonneg (fun x _ => hh j x)
  have ha1 (j) : a j ≤ 1 := by
    calc
      a j ≤ ∑ x, (p j).weight x := Finset.sum_le_sum (fun x _ => min_le_left _ _)
      _ = 1 := (p j).total
  have hlower := one_sub_sum_le_positive_prod Finset.univ a (fun j => 1 - a j)
    (fun j _ => ha0 j) (fun j _ => ⟨sub_nonneg.mpr (ha1 j), by linarith [ha0 j]⟩)
    (fun j _ => by simp)
  have hpoint (x : ∀ j, Ω j) :
      |(pi p).weight x - (pi q).weight x| ≤
        (pi p).weight x + (pi q).weight x - 2 * ∏ j, h j (x j) := by
    rw [abs_sub_min_identity]
    have hp : (∏ j, h j (x j)) ≤ (pi p).weight x :=
      Finset.prod_le_prod (fun j _ => hh j (x j)) (fun j _ => min_le_left _ _)
    have hq : (∏ j, h j (x j)) ≤ (pi q).weight x :=
      Finset.prod_le_prod (fun j _ => hh j (x j)) (fun j _ => min_le_right _ _)
    linarith [le_min hp hq]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  have hprod : (∑ x : ∀ j, Ω j, ∏ j, h j (x j)) = ∏ j, a j :=
    (Fintype.prod_sum h).symm
  have hcoord (j) : (∑ x, |(p j).weight x - (q j).weight x|) = 2 * (1 - a j) := by
    simp_rw [abs_sub_min_identity]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      (p j).total, (q j).total]
    change 1 + 1 - 2 * a j = _
    ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    (pi p).total, (pi q).total, hprod] at hsum
  simp_rw [hcoord]
  rw [← Finset.mul_sum]
  linarith

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelProductFiber
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] [DecidableEq J]
  {Ω R : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
  [∀ j, Fintype (R j)] [∀ j, DecidableEq (R j)]

theorem pi_fiberLaw (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (residue : ∀ j, Ω j → R j) :
    (pi p).fiberLaw (fun x j => residue j (x j)) =
      pi (fun j => (p j).fiberLaw (residue j)) := by
  apply ext_weight
  funext r
  rw [fiberLaw_weight_eq_mass, pi_fiber_mass]
  change (∏ j, (p j).mass _) = ∏ j, ((p j).fiberLaw (residue j)).weight (r j)
  simp only [fiberLaw_weight_eq_mass]

theorem pi_complexMean_disintegrate (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (residue : ∀ j, Ω j → R j)
    (hp : ∀ j r, 0 < (p j).mass (Finset.univ.filter (fun x => residue j x = r)))
    (test : (∀ j, R j) → (∀ j, Ω j) → ℂ) :
    (pi p).complexMean (fun x => test (fun j => residue j (x j)) x) =
      (pi (fun j => (p j).fiberLaw (residue j))).complexMean (fun r =>
        (pi (fun j => (p j).condition
          (Finset.univ.filter (fun x => residue j x = r j)) (hp j (r j)))).complexMean
            (test r)) := by
  rw [(pi p).complexMean_disintegrate (fun x j => residue j (x j))
    (fun r => pi_fiber_mass_pos p residue r (fun j => hp j (r j))) test]
  rw [pi_fiberLaw]
  congr 1
  funext r
  rw [pi_condition_fiber]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.OriginalKernelResidueRetained
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem intervalUniformWeights_residue_weight (a b : ℤ) (hab : a < b)
    (q : ℕ) [NeZero q] (v : ℤ) :
    ((intervalUniformWeights a b hab).fiberLaw
      (fun x => ((x : ℤ) : ZMod q))).weight (v : ZMod q) =
      ((Finset.filter (fun x => x ≡ v [ZMOD (q : ℤ)])
        (Finset.Ico a b)).card : ℝ) / ((b - a : ℤ) : ℝ) := by
  simp only [FiniteProbabilityWeights.fiberLaw, FiniteProbabilityWeights.fiberMean]
  simp only [ZMod.intCast_eq_intCast_iff]
  rw [intervalUniformWeights_mean]
  exact @integerInterval_indicator_expect a b hab.le
    (fun x : ℤ => x ≡ v [ZMOD (q : ℤ)]) (fun _ => Int.instDecidableModEq)

theorem intervalUniformWeights_residue_weight_error (a b : ℤ) (hab : a < b)
    (q : ℕ) [NeZero q] (r : ZMod q) :
    |((intervalUniformWeights a b hab).fiberLaw
      (fun x => ((x : ℤ) : ZMod q))).weight r - 1 / (q : ℝ)| ≤
      1 / ((b - a : ℤ) : ℝ) := by
  have hL : (0 : ℝ) < ((b - a : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr hab
  have hq : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  have hr : (((r.val : ℕ) : ℤ) : ZMod q) = r := by simp
  rw [← hr, intervalUniformWeights_residue_weight]
  have hc := scalarResidue_card_absolute_error a b q r.val hab.le hq
  have heq :
      ((Finset.filter (fun x => x ≡ (r.val : ℤ) [ZMOD (q : ℤ)])
        (Finset.Ico a b)).card : ℝ) / ((b - a : ℤ) : ℝ) - 1 / (q : ℝ) =
      (((Finset.filter (fun x => x ≡ (r.val : ℤ) [ZMOD (q : ℤ)])
        (Finset.Ico a b)).card : ℝ) - ((b - a : ℤ) : ℝ) / (q : ℝ)) /
          ((b - a : ℤ) : ℝ) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right (by simpa only [Int.cast_natCast] using hc) hL.le

theorem intervalUniformWeights_residue_l1_error (a b : ℤ) (hab : a < b)
    (q : ℕ) [NeZero q] :
    (∑ r : ZMod q, |((intervalUniformWeights a b hab).fiberLaw
      (fun x => ((x : ℤ) : ZMod q))).weight r - 1 / (q : ℝ)|) ≤
      (q : ℝ) / ((b - a : ℤ) : ℝ) := by
  calc
    _ ≤ ∑ _r : ZMod q, 1 / ((b - a : ℤ) : ℝ) := by
      exact Finset.sum_le_sum (fun r _ => intervalUniformWeights_residue_weight_error a b hab q r)
    _ = _ := by simp [ZMod.card, div_eq_mul_inv]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerScalarCubeWeights_empty_residue_law (L q : ℕ) (hL : 0 < L)
    [NeZero q] :
    (integerScalarCubeWeights Empty L hL).fiberLaw
        (fun x => ((x none : ℤ) : ZMod q)) =
      (intervalUniformWeights 0 (L : ℤ) (by exact_mod_cast hL)).fiberLaw
        (fun x => (x.val : ZMod q)) := by
  apply FiniteProbabilityWeights.ext_weight
  funext r
  simpa only [FiniteProbabilityWeights.fiberLaw, FiniteProbabilityWeights.fiberMean] using
    integerScalarCubeWeights_zero_mean Empty L hL
      (fun z => if (z : ZMod q) = r then 1 else 0)

theorem integerScalarCubeWeights_empty_residue_condition
    (L q : ℕ) (hL : 0 < L) (hq : 0 < q) (hqL : q ≤ L) (r : ZMod q) :
    (integerScalarCubeWeights Empty L hL).condition
      (Finset.univ.filter (fun x => ((x none : ℤ) : ZMod q) = r))
      (integerScalarCubeWeights_empty_residue_mass_pos L q hL hq hqL r) =
    scalarCubeResidueWeights Empty L q hL (fun _ => q) (fun _ => r)
      (fun _ => hq) (fun _ => le_rfl) (by simpa using hqL) := by
  unfold scalarCubeResidueWeights
  congr 1
  exact (scalarCubeResidueSet_empty_eq_filter L q r).symm

theorem integerScalarCubeWeights_empty_residue_l1
    (L q : ℕ) (hL : 0 < L) [NeZero q] :
    (∑ r : ZMod q,
      |((integerScalarCubeWeights Empty L hL).fiberLaw
        (fun x => ((x none : ℤ) : ZMod q))).weight r -
          (FiniteProbabilityWeights.uniform (ZMod q)).weight r|) ≤ (q : ℝ) / L := by
  rw [integerScalarCubeWeights_empty_residue_law]
  simpa only [FiniteProbabilityWeights.uniform, ZMod.card, one_div, Int.cast_sub,
    Int.cast_natCast, Int.cast_zero, sub_zero] using
    intervalUniformWeights_residue_l1_error 0 L (by exact_mod_cast hL) q

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem integerScalarCubeWeights_empty_pi_residue_disintegration_varying
    {G : Type*} [Fintype G] [DecidableEq G]
    (L : G → ℕ) (q : ℕ) [NeZero q] (hL : ∀ g, 0 < L g) (hq : 0 < q) (hqL : ∀ g, q ≤ L g)
    (test : (G → ZMod q) → (∀ g, IntegerScalarCubeBox Empty (L g)) → ℂ) :
    (FiniteProbabilityWeights.pi (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))).complexMean
      (fun x => test (fun g => ((x g none : ℤ) : ZMod q)) x) =
    (FiniteProbabilityWeights.pi (fun g : G =>
      (integerScalarCubeWeights Empty (L g) (hL g)).fiberLaw
        (fun x => ((x none : ℤ) : ZMod q)))).complexMean (fun r =>
      (FiniteProbabilityWeights.pi (fun g : G => scalarCubeResidueWeights Empty (L g) q (hL g)
        (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl)
          (by simpa using hqL g))).complexMean (test r)) := by
  rw [FiniteProbabilityWeights.pi_complexMean_disintegrate
    (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))
    (fun _ x => ((x none : ℤ) : ZMod q))
    (fun g r => integerScalarCubeWeights_empty_residue_mass_pos (L g) q (hL g) hq (hqL g) r) test]
  apply congrArg (FiniteProbabilityWeights.pi (fun g : G =>
    (integerScalarCubeWeights Empty (L g) (hL g)).fiberLaw
      (fun x => ((x none : ℤ) : ZMod q)))).complexMean
  funext r
  apply congrArg (fun p : FiniteProbabilityWeights (∀ g, IntegerScalarCubeBox Empty (L g)) =>
    p.complexMean (test r))
  apply congrArg FiniteProbabilityWeights.pi
  funext g
  exact integerScalarCubeWeights_empty_residue_condition (L g) q (hL g) hq (hqL g) (r g)

theorem integerScalarCubeWeights_empty_pi_uniform_residue_error_varying
    {G : Type*} [Fintype G] [DecidableEq G]
    (L : G → ℕ) (q : ℕ) [NeZero q] (hL : ∀ g, 0 < L g) (hq : 0 < q) (hqL : ∀ g, q ≤ L g)
    (test : (G → ZMod q) → (∀ g, IntegerScalarCubeBox Empty (L g)) → ℂ)
    (hbound : ∀ r x, ‖test r x‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))).complexMean
      (fun x => test (fun g => ((x g none : ℤ) : ZMod q)) x) -
      𝔼 r : G → ZMod q,
        (FiniteProbabilityWeights.pi (fun g : G => scalarCubeResidueWeights Empty (L g) q (hL g)
          (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl)
            (by simpa using hqL g))).complexMean (test r)‖ ≤
      ∑ g, (q : ℝ) / L g := by
  let μ := fun g => (integerScalarCubeWeights Empty (L g) (hL g)).fiberLaw
    (fun x => ((x none : ℤ) : ZMod q))
  let ν := FiniteProbabilityWeights.uniform (ZMod q)
  let F (r : G → ZMod q) :=
    (FiniteProbabilityWeights.pi (fun g : G => scalarCubeResidueWeights Empty (L g) q (hL g)
      (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl)
        (by simpa using hqL g))).complexMean (test r)
  have hF (r : G → ZMod q) : ‖F r‖ ≤ 1 := by
    apply (FiniteProbabilityWeights.norm_complexMean_le_mean_norm _ _).trans
    exact (FiniteProbabilityWeights.mean_mono _ (hbound r)).trans_eq
      (FiniteProbabilityWeights.mean_const _ 1)
  rw [integerScalarCubeWeights_empty_pi_residue_disintegration_varying L q hL hq hqL test,
    ← FiniteProbabilityWeights.pi_uniform_complexMean]
  exact (FiniteProbabilityWeights.norm_complexMean_sub_le_weight_l1
    (FiniteProbabilityWeights.pi (fun g : G => μ g))
    (FiniteProbabilityWeights.pi (fun _ : G => ν)) F hF).trans
      ((FiniteProbabilityWeights.pi_weight_l1_le_sum (fun g : G => μ g) (fun _ : G => ν)).trans
        (Finset.sum_le_sum (fun g _ => integerScalarCubeWeights_empty_residue_l1 (L g) q (hL g))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedFixedPathSlicedKernelResidueRiemann
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

include hR hσ in
theorem allocatedOriginalSampleFullSlice_residue_riemann (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (step H M : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Input → Option Empty → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((M j : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (φ : (Output → ℝ) → ℝ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights Empty (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j)
        (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))).mean
        (fun z => φ (allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))) -
      ∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
        ∂unitBoxMeasure Input| ≤
      (2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  classical
  intro lower width K
  let F := allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1) sample
  let project := fun x : Input → Option Empty → ℝ => fun j => x j none
  have hproj : LipschitzWith 1 project := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro j
    exact (dist_le_pi_dist (x j) (y j) none).trans (dist_le_pi_dist x y j)
  have hball : Set.MapsTo project (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    exact (norm_le_pi_norm (x j) none).trans ((norm_le_pi_norm x j).trans hx)
  have hF := allocatedOriginalSampleFullSliceMap_supported_lipschitzOn_s2 B U basis hR hσ S x u sample hs
    (fun _ _ => 0) (fun _ _ => 1) (by intro _ _; norm_num) ht hσbound
  have htest : LipschitzOnWith K (fun x => φ (F (project x))) (Metric.closedBall 0 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    calc
      _ ≤ Kφ * dist (F (project x)) (F (project y)) := hφ.dist_le_mul _ _
      _ ≤ Kφ * ((allocatedOriginalSampleFullSliceLip B U basis S t : ℝ) *
          dist (project x) (project y)) :=
        mul_le_mul_of_nonneg_left (hF.dist_le_mul _ (hball hx) _ (hball hy)) Kφ.coe_nonneg
      _ ≤ Kφ * ((allocatedOriginalSampleFullSliceLip B U basis S t : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by simpa using hproj.dist_le_mul x y)
            (allocatedOriginalSampleFullSliceLip B U basis S t).coe_nonneg) Kφ.coe_nonneg
      _ = K * dist x y := by simp only [K, NNReal.coe_mul, mul_assoc]
  have he := progressionTuple_residue_riemann_on_box (fun _ : Input => S.value)
    step H M c (fun _ => S.positive) hstep hH hδ hsubset hdense modulus residue hm hmM
    (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)
    (fun j => by simpa only [Measure.real, scalarCubeDomain_empty_volume, ENNReal.toReal_one]
      using hsmall j) hε hmesh (fun x => φ (F (project x))) htest zero_le_one
    (fun x _ => hφone _)
  have hid (z : Input → Option Empty → ℝ) :
      F (project (affineCubeTuple (fun j => (c j : ℝ) / S.value)
        (fun j => (step j : ℝ) * ((H j : ℝ) - 1) / S.value) z)) =
      allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample (project z) := by
    exact allocatedOriginalSampleFullSliceMap_affine B U basis S x u sample lower width (project z)
  simp_rw [hid] at he
  have hmeas : Measurable (fun y =>
      φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)) :=
    hφ.continuous.measurable.comp
      (allocatedOriginalSampleFullSliceMap_measurable B U basis S x u lower width sample)
  rw [scalarCubeProductMeasure_empty_integral Input _ hmeas] at he
  simpa only [F, project, ite_true, Measure.real, scalarCubeDomain_empty_volume,
    ENNReal.toReal_one, mul_one, div_one] using he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleSlicedPerturbedRiemann
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

include hR hσ in
theorem allocatedOriginalSampleFullSlice_sliced_residue_complex_riemann (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (step H M : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Input → Option Empty → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((M j : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (φ : (Output → ℝ) → ℂ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    ‖(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights Empty (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j)
        (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))).complexMean
        (fun z => φ (allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))) -
      ∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
        ∂unitBoxMeasure Input‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε) := by
  classical
  intro lower width K
  let p := FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights Empty (H j) (M j)
    (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j)
    (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))
  let F := allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1) sample
  let f := fun (z : ∀ j : Input, IntegerScalarCubeBox Empty (H j)) => φ (F (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))
  let g := fun y => φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
  have hig : Integrable g (unitBoxMeasure Input) :=
    ⟨(hφ.continuous.measurable.comp
      (allocatedOriginalSampleFullSliceMap_measurable B U basis S x u lower width sample)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun y => hφone _))⟩
  have hφre : LipschitzWith Kφ (fun y => (φ y).re) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [Real.dist_eq, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (by simpa only [dist_eq_norm] using hφ.dist_le_mul v w)
  have hφim : LipschitzWith Kφ (fun y => (φ y).im) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [Real.dist_eq, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans (by simpa only [dist_eq_norm] using hφ.dist_le_mul v w)
  have hre := allocatedOriginalSampleFullSlice_residue_riemann B U basis hR hσ S x u
    sample hs ht hσbound step H M c hstep hH hδ hsubset hdense modulus residue hm hmM
    hsize hsmall hε hmesh (fun y => (φ y).re) hφre
    (fun y => (Complex.abs_re_le_norm _).trans (hφone y))
  have him := allocatedOriginalSampleFullSlice_residue_riemann B U basis hR hσ S x u
    sample hs ht hσbound step H M c hstep hH hδ hsubset hdense modulus residue hm hmM
    hsize hsmall hε hmesh (fun y => (φ y).im) hφim
    (fun y => (Complex.abs_im_le_norm _).trans (hφone y))
  have hgre : (∫ y, g y ∂unitBoxMeasure Input).re = ∫ y, (g y).re ∂unitBoxMeasure Input := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hig).symm
  have hgim : (∫ y, g y ∂unitBoxMeasure Input).im = ∫ y, (g y).im ∂unitBoxMeasure Input := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im hig).symm
  change ‖p.complexMean f - ∫ y, g y ∂unitBoxMeasure Input‖ ≤ _
  calc
    _ ≤ |(p.complexMean f - ∫ y, g y ∂unitBoxMeasure Input).re| +
        |(p.complexMean f - ∫ y, g y ∂unitBoxMeasure Input).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε) +
        ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε) := by
      apply add_le_add
      · rw [Complex.sub_re, FiniteProbabilityWeights.complexMean_re, hgre]
        exact hre
      · rw [Complex.sub_im, FiniteProbabilityWeights.complexMean_im, hgim]
        exact him
    _ = _ := by ring

include hR hσ in
theorem allocatedOriginalSample_sliced_residue_perturbed_riemann (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (step H M : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Input → Option Empty → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((M j : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (hδone : δ ≤ 1) (b : ∀ a : Active, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
    (φ : (Output → ℝ) → ℂ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    ‖(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights Empty (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j)
        (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))).complexMean
        (fun z => φ (allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))) -
      ∫ y, φ (allocatedOriginalSampleLiftMap B U basis S lower width sample y)
        ∂unitBoxMeasure Input‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε) + 2 * η := by
  classical
  intro lower width K
  have hg (a : Active) (p : B a.val × Fin (degree a.val)) :=
    progression_slice_endpoint_geometry (c ⟨a,p⟩) S.positive (hstep _) (hH _)
      hδ (hsubset _) (hdense _)
  have hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1 := fun a p => (hg a p).2.2.1
  have hp := allocatedOriginalSample_slice_complex_perturbation_s2 B U basis hR hσ S x u lower width
    sample hs hwidth b (δ := δ / 2) (half_pos hδ) (by linarith) hη
    (fun a i => (hg a (b a, i)).2.1) (fun a i => (hg a (b a, i)).1)
    A hA ht hσbound htail φ hφ.continuous.measurable hφone
  have hq := allocatedOriginalSampleFullSlice_sliced_residue_complex_riemann
    B U basis hR hσ S x u sample hs ht hσbound step H M c hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh φ hφ hφone
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
      ∂unitBoxMeasure Input) _).trans (add_le_add hq ((norm_sub_rev _ _).trans_le hp))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedChildActiveResidueComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

include hR hσ in
theorem allocatedOriginalSample_sliced_affine_residue_comparison_s2_oai (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) [NeZero q] (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (hδone : δ ≤ 1) (b : ∀ a : Active, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
    (φ : (Input → ZMod q) → (Output → ℝ) → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ r, LipschitzWith Kφ (φ r)) (hφone : ∀ r y, ‖φ r y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    ‖(FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j)
        (by have := hH j; omega))).complexMean
        (fun z => φ (fun j => ((c j + (step j : ℤ) * (z j none : ℤ) : ℤ) : ZMod q))
          (allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
            sample (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))) -
      𝔼 r : Input → ZMod q,
        ∫ y, φ (fun j => (c j : ZMod q) + (step j : ZMod q) * r j)
          (allocatedOriginalSampleLiftMap B U basis S lower width sample y)
          ∂unitBoxMeasure Input‖ ≤
      (∑ j, (q : ℝ) / H j) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) + 2 * η) := by
  classical
  intro lower width K
  let hHpos : ∀ j, 0 < H j := fun j => by have := hH j; omega
  let law := FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j) (hHpos j))
  let residues := FiniteProbabilityWeights.uniform (Input → ZMod q)
  let conditioned := fun r : Input → ZMod q => FiniteProbabilityWeights.pi
    (fun j : Input => scalarCubeResidueWeights Empty (H j) q (hHpos j)
      (fun _ => q) (fun _ => r j) (fun _ => NeZero.pos q) (fun _ => le_rfl)
      (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))
  let F := allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1) sample
  let value := fun (r : Input → ZMod q) (z : ∀ j : Input, IntegerScalarCubeBox Empty (H j)) =>
    φ (fun j => (c j : ZMod q) + (step j : ZMod q) * r j)
      (F (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))
  let reference := fun r : Input → ZMod q =>
    ∫ y, φ (fun j => (c j : ZMod q) + (step j : ZMod q) * r j)
      (allocatedOriginalSampleLiftMap B U basis S lower width sample y) ∂unitBoxMeasure Input
  let error := 2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
    ∑ j, (q : ℝ) / H j + K * ε) + 2 * η
  have hc (r : Input → ZMod q) :
      ‖(conditioned r).complexMean (value r) - reference r‖ ≤ error := by
    exact allocatedOriginalSample_sliced_residue_perturbed_riemann B U basis hR hσ S x u
      sample hs ht hσbound step H (fun _ => q) c hstep hH hδ hsubset hdense
      (fun _ _ => q) (fun j _ => r j) (fun _ _ => NeZero.pos q) (fun _ _ => le_rfl)
      hsize hsmall hε hmesh hδone b hη A hA htail (φ _) (hφ _) (hφone _)
  have hm := integerScalarCubeWeights_empty_pi_uniform_residue_error_varying
    H q hHpos (NeZero.pos q) hsize value (fun r z => hφone _ _)
  have hm' : ‖law.complexMean (fun z => value (fun j => ((z j none : ℤ) : ZMod q)) z) -
      residues.complexMean (fun r => (conditioned r).complexMean (value r))‖ ≤
      ∑ j, (q : ℝ) / H j := by
    simpa only [law, residues, conditioned, FiniteProbabilityWeights.uniform_complexMean] using hm
  have ha : ‖residues.complexMean (fun r => (conditioned r).complexMean (value r)) -
      residues.complexMean reference‖ ≤ error :=
    (residues.norm_complexMean_sub_le _ _ (fun _ => error) (fun r _ => hc r)).trans_eq
      (residues.mean_const error)
  have he := (norm_sub_le_norm_sub_add_norm_sub
    (law.complexMean (fun z => value (fun j => ((z j none : ℤ) : ZMod q)) z))
    (residues.complexMean (fun r => (conditioned r).complexMean (value r)))
    (residues.complexMean reference)).trans
      (add_le_add hm' ha)
  simpa only [law, residues, conditioned, value, reference, error, F,
    FiniteProbabilityWeights.uniform_complexMean, Int.cast_add, Int.cast_mul, Int.cast_natCast] using he

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_sliced_affine_residue_comparison_s2_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_sliced_affine_residue_comparison_s2_oai.{u_1, u_2, u_3, u_4}
