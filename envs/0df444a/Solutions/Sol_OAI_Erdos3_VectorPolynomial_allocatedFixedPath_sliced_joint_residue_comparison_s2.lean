-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_joint_residue_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:45:24.771639+00:00
-- url     : https://prove2.me/submissions/04d11375-e9e1-49d6-a4e4-c924f7e8fb14

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B177
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedOriginalSample_sliced_affine_residue_comparison_s2
import Theorems.Thm_OAI_Erdos3_scalarCubeResidueWeights_pi_complex_riemann_s2

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


open scoped BigOperators Classical

theorem integerScalarCubeWeights_root_bounds {α : Type*} [Fintype α] [DecidableEq α]
    {H : ℕ} (hH : 0 < H) (z : IntegerScalarCubeBox α H)
    (hz : (integerScalarCubeWeights α H hH).weight z ≠ 0) :
    0 ≤ (z none : ℤ) ∧ (z none : ℤ) ≤ ((H - 1 : ℕ) : ℤ) := by
  have hmem : z ∈ integerScalarCubeSet α H := by
    by_contra hn
    apply hz
    simp only [integerScalarCubeWeights, FiniteProbabilityWeights.condition,
      hn, ite_false, zero_div]
  have hr := ((mem_integerScalarCubeSet H z).mp hmem) ∅
  simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at hr
  exact ⟨hr.1, by omega⟩

theorem integerScalarCubePi_root_bounds {G : Type*} [Fintype G]
    (H : G → ℕ) (hH : ∀ g, 0 < H g)
    (z : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hz : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight z ≠ 0)
    (g : G) :
    0 ≤ (z g none : ℤ) ∧ (z g none : ℤ) ≤ ((H g - 1 : ℕ) : ℤ) := by
  apply integerScalarCubeWeights_root_bounds (hH g) (z g)
  change (∏ g, (integerScalarCubeWeights Empty (H g) (hH g)).weight (z g)) ≠ 0 at hz
  exact Finset.prod_ne_zero_iff.mp hz g (Finset.mem_univ g)

theorem integerScalarCubePi_root_real_bounds {G : Type*} [Fintype G]
    (H : G → ℕ) (hH : ∀ g, 0 < H g)
    (z : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hz : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight z ≠ 0)
    (g : G) :
    0 ≤ ((z g none : ℤ) : ℝ) ∧ ((z g none : ℤ) : ℝ) ≤ ((H g - 1 : ℕ) : ℝ) := by
  have hb := integerScalarCubePi_root_bounds H hH z hz g
  exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩

theorem affineKernelEndpoint_error {H S step z : ℝ} (lower : ℝ)
    (hH : 0 < H) (hS : 0 < S) (hz0 : 0 ≤ z) (hzH : z ≤ H - 1)
    (hstep : 0 ≤ step) (hwidth : step * (H - 1) ≤ S) :
    |(lower + step * z) / S - (lower + step * (H - 1) * (z / H)) / S| ≤ 1 / H := by
  have he : (lower + step * z) / S - (lower + step * (H - 1) * (z / H)) / S =
      (step * z / S) / H := by
    field_simp
    ring
  rw [he, abs_of_nonneg (div_nonneg (div_nonneg (mul_nonneg hstep hz0) hS.le) hH.le)]
  apply div_le_div_of_nonneg_right _ hH.le
  apply (div_le_one hS).mpr
  exact (mul_le_mul_of_nonneg_left hzH hstep).trans hwidth

theorem affineKernelEndpoint_error_nat {H : ℕ} {S step z : ℝ} (lower : ℝ)
    (hH : 0 < H) (hS : 0 < S) (hz0 : 0 ≤ z) (hzH : z ≤ ((H - 1 : ℕ) : ℝ))
    (hstep : 0 ≤ step) (hwidth : step * ((H - 1 : ℕ) : ℝ) ≤ S) :
    |(lower + step * z) / S -
      (lower + step * ((H - 1 : ℕ) : ℝ) * (z / H)) / S| ≤ 1 / H := by
  have hcast : ((H - 1 : ℕ) : ℝ) = (H : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one]
  rw [hcast] at hzH hwidth ⊢
  exact affineKernelEndpoint_error lower (Nat.cast_pos.mpr hH) hS hz0 hzH hstep hwidth

end Erdos3


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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledCubeProductMeasure
namespace OAI

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

end Erdos3

end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineKernelEndpointGeometry
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal Classical
variable {G : Type*} [Fintype G]

theorem affineKernelContinuousPoint_lipschitz (lower : G → ℝ) (step S : ℝ) (H : G → ℕ)
    (hS : 0 < S) (hstep : 0 ≤ step)
    (hspan : ∀ g, step * ((H g - 1 : ℕ) : ℝ) ≤ S) :
    LipschitzWith 1 (affineKernelContinuousPoint lower step S H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro g
  have hw0 : 0 ≤ step * ((H g - 1 : ℕ) : ℝ) := mul_nonneg hstep (Nat.cast_nonneg _)
  have hw : step * ((H g - 1 : ℕ) : ℝ) / S ≤ 1 := (div_le_one hS).mpr (hspan g)
  have hx : |x g none - y g none| ≤ dist x y :=
    (dist_le_pi_dist (x g) (y g) none).trans (dist_le_pi_dist x y g)
  change |(lower g + step * ((H g - 1 : ℕ) : ℝ) * x g none) / S -
      (lower g + step * ((H g - 1 : ℕ) : ℝ) * y g none) / S| ≤ _
  rw [← sub_div, add_sub_add_left_eq_sub, ← mul_sub, abs_div, abs_mul,
    abs_of_nonneg hw0, abs_of_pos hS]
  calc
    _ = (step * ((H g - 1 : ℕ) : ℝ) / S) * |x g none - y g none| := by ring
    _ ≤ 1 * dist x y := mul_le_mul hw hx (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem affineKernelEndpoint_dist_le (lower : G → ℝ) (step S : ℝ) (H : G → ℕ)
    (hH : ∀ g, 0 < H g) (hS : 0 < S) (hstep : 0 ≤ step)
    (hspan : ∀ g, step * ((H g - 1 : ℕ) : ℝ) ≤ S)
    (z : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hz : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight z ≠ 0) :
    dist (affineKernelDiscretePoint lower step S z)
      (affineKernelContinuousPoint lower step S H (fun g i => (z g i : ℝ) / H g)) ≤
        ∑ g, (1 : ℝ) / H g := by
  have hsum : 0 ≤ ∑ g, (1 : ℝ) / H g := Finset.sum_nonneg (fun g _ => by positivity)
  apply (dist_pi_le_iff hsum).mpr
  intro g
  have hz' := integerScalarCubePi_root_real_bounds H hH z hz g
  have he := affineKernelEndpoint_error_nat (lower g) (hH g) hS hz'.1 hz'.2 hstep (hspan g)
  change |(lower g + step * (z g none : ℝ)) / S -
    (lower g + step * ((H g - 1 : ℕ) : ℝ) * ((z g none : ℝ) / H g)) / S| ≤ _
  exact he.trans (Finset.single_le_sum (f := fun j => (1 : ℝ) / H j)
    (fun j _ => by positivity) (Finset.mem_univ g))

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedProgressionCubeLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem complexMean_commute {I J : Type*} [Fintype I] [Fintype J]
    (p : FiniteProbabilityWeights I) (q : FiniteProbabilityWeights J) (f : I → J → ℂ) :
    p.complexMean (fun i => q.complexMean (f i)) =
      q.complexMean (fun j => p.complexMean (fun i => f i j)) := by
  simp only [complexMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end FiniteProbabilityWeights

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

open MeasureTheory
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
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleLiftMap_apply (sample : Sample) (x : Input → ℝ) (o : Output) :
    allocatedOriginalSampleLiftMap B U basis S lower width sample x o =
      allocatedSampleNormalizedCoefficients B U basis S sample o.1.val
        (constantCoefficientSlot vars (degree o.1.val)) / R o.1.val.1 +
      ∑ b, (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val
        (principalCoefficientSlot degree o.1.val b) / R o.1.val.1) *
        ∏ v, (lower o.1 (b, v) + width o.1 (b, v) * x ⟨o.1, b, v⟩) := rfl

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

theorem allocatedOriginalSampleLiftMap_measurable :
    Measurable (fun p : Sample × (Input → ℝ) =>
      allocatedOriginalSampleLiftMap B U basis S lower width p.1 p.2) := by
  apply measurable_pi_iff.mpr
  rintro ⟨⟨⟨j, i⟩, ha⟩, u⟩
  cases i with
  | inl i =>
    simp only [allocatedOriginalSampleLiftMap_apply, allocatedSampleNormalizedCoefficients]
    fun_prop
  | inr i =>
    simp only [allocatedOriginalSampleLiftMap_apply, allocatedSampleNormalizedCoefficients]
    fun_prop

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineKernelResidueRetained
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem originalKernel_residue_slow_quadrature_varying
    {G : Type*} [Fintype G] [DecidableEq G]
    (L : G → ℕ) (q : ℕ) [NeZero q]
    (hL : ∀ g, 0 < L g) (hq : 0 < q) (hqL : ∀ g, q ≤ L g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / L g) <
      volume.real (scalarCubeDomain Empty))
    (F : (G → ZMod q) → (G → Option Empty → ℝ) → ℂ)
    {K : ℝ≥0} (hF : ∀ r, LipschitzWith K (F r))
    (hbound : ∀ r x, ‖F r x‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))).complexMean
        (fun z => F (fun g => ((z g none : ℤ) : ZMod q))
          (fun g i => (z g i : ℝ) / L g)) -
      𝔼 r : G → ZMod q, ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty /
        volume.real (scalarCubeDomain Empty) + K)) *
          (∑ g, (q : ℝ) / L g) := by
  let test := fun (r : G → ZMod q) (z : ∀ g, IntegerScalarCubeBox Empty (L g)) =>
    F r (fun g i => (z g i : ℝ) / L g)
  let law := fun (r : G → ZMod q) => FiniteProbabilityWeights.pi
    (fun g : G => scalarCubeResidueWeights Empty (L g) q (hL g)
      (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl) (by simpa using hqL g))
  let e : ℝ := 2 * (2 * scalarCubeGridBoundaryConstant Empty /
    volume.real (scalarCubeDomain Empty) + K) * (∑ g, (q : ℝ) / L g)
  have hcond (r : G → ZMod q) :
      ‖(law r).complexMean (test r) - ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ ≤ e := by
    simpa only [law, test, e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      scalarCubeResidueWeights_pi_complex_riemann_s2 L (fun _ => q) hL
        (fun (_ : G) (_ : Option Empty) => q) (fun g _ => r g) (fun _ _ => hq)
        (fun _ _ => le_rfl) (fun g => by simpa using hqL g)
        hsmall (F r) (hF r) zero_le_one (hbound r)
  have hmix := integerScalarCubeWeights_empty_pi_uniform_residue_error_varying L q hL hq hqL
    test (fun r z => hbound r _)
  have havg : ‖(𝔼 r : G → ZMod q, (law r).complexMean (test r)) -
      𝔼 r : G → ZMod q, ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ ≤ e := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact (Finset.expect_le_expect (fun r _ => hcond r)).trans_eq (by simp)
  calc
    _ ≤ ‖(FiniteProbabilityWeights.pi (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))).complexMean
        (fun z => test (fun g => ((z g none : ℤ) : ZMod q)) z) -
          𝔼 r : G → ZMod q, (law r).complexMean (test r)‖ +
        ‖(𝔼 r : G → ZMod q, (law r).complexMean (test r)) -
          𝔼 r : G → ZMod q, ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (∑ g, (q : ℝ) / L g) + e := add_le_add hmix havg
    _ = _ := by dsimp only [e]; ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {G R : Type*} [Fintype G] [DecidableEq G]

theorem affineKernel_residue_slow_quadrature
    (H : G → ℕ) (q : ℕ) [NeZero q] (hH : ∀ g, 0 < H g)
    (hq : 0 < q) (hqH : ∀ g, q ≤ H g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H g) <
      volume.real (scalarCubeDomain Empty))
    (lower : G → ℝ) (step S : ℝ) (hS : 0 < S) (hstep : 0 ≤ step)
    (hspan : ∀ g, step * ((H g - 1 : ℕ) : ℝ) ≤ S)
    (residueMap : (G → ZMod q) → R) (F : R → (G → ℝ) → ℂ)
    {K : ℝ≥0} (hF : ∀ r, LipschitzWith K (F r))
    (hbound : ∀ r x, ‖F r x‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (H g) (hH g))).complexMean
        (fun z => F (residueMap (fun g => ((z g none : ℤ) : ZMod q)))
          (fun g => (lower g + step * (z g none : ℝ)) / S)) -
      𝔼 r : G → ZMod q, ∫ x,
        F (residueMap r) (affineKernelContinuousPoint lower step S H x)
          ∂scalarCubeProductMeasure G Empty‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty /
        volume.real (scalarCubeDomain Empty) + K) + K) * ∑ g, (q : ℝ) / H g := by
  let p := FiniteProbabilityWeights.pi
    (fun g => integerScalarCubeWeights Empty (H g) (hH g))
  let test := fun r x => F (residueMap r) (affineKernelContinuousPoint lower step S H x)
  have htest (r : G → ZMod q) : LipschitzWith K (test r) := by
    simpa only [test, Function.comp_def, mul_one] using (hF (residueMap r)).comp
      (affineKernelContinuousPoint_lipschitz lower step S H hS hstep hspan)
  have hquad := originalKernel_residue_slow_quadrature_varying H q hH hq hqH
    hsmall test htest (fun r x => hbound _ _)
  have hsum : (∑ g, (1 : ℝ) / H g) ≤ ∑ g, (q : ℝ) / H g := by
    apply Finset.sum_le_sum
    intro g _
    exact div_le_div_of_nonneg_right (by exact_mod_cast hq) (by positivity)
  have hpoint :
      ‖p.complexMean (fun z => F (residueMap (fun g => ((z g none : ℤ) : ZMod q)))
          (fun g => (lower g + step * (z g none : ℝ)) / S)) -
        p.complexMean (fun z => test (fun g => ((z g none : ℤ) : ZMod q))
          (fun g i => (z g i : ℝ) / H g))‖ ≤ (K : ℝ) * ∑ g, (q : ℝ) / H g := by
    apply (p.norm_complexMean_sub_le _ _ (fun _ => (K : ℝ) * ∑ g, (q : ℝ) / H g) ?_).trans_eq
      (p.mean_const _)
    intro z hz
    rw [← dist_eq_norm]
    exact ((hF _).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
      ((affineKernelEndpoint_dist_le lower step S H hH hS hstep hspan z hz).trans hsum)
      K.coe_nonneg)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add hpoint hquad).trans_eq (by ring))

omit [Fintype G] [DecidableEq G] in

theorem affineKernel_span_of_contained
    (H : G → ℕ) (hH : ∀ g, 0 < H g) (start : G → ℤ)
    (step S : ℕ) (hstep : 0 < step)
    (hcontained : ∀ g, integerProgressionSupport (start g) (step : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ)) :
    ∀ g, (step : ℝ) * ((H g - 1 : ℕ) : ℝ) ≤ S := by
  intro g
  have hfirst := hcontained g
    (integerProgressionSupport_point (start g) step (H g) hstep 0 (hH g))
  have hlast := hcontained g
    (integerProgressionSupport_point (start g) step (H g) hstep (H g - 1) (by
      have := hH g
      omega))
  have hc : (0 : ℤ) ≤ start g := by simpa using (Finset.mem_Ico.mp hfirst).1
  have he : start g + (step : ℤ) * ((H g - 1 : ℕ) : ℤ) < S :=
    (Finset.mem_Ico.mp hlast).2
  have hs : (step : ℤ) * ((H g - 1 : ℕ) : ℤ) ≤ S := by omega
  exact_mod_cast hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.GenericProbabilityProductMapIntegral
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace Ω]

omit [MeasurableSpace α] [MeasurableSpace β] in
theorem probability_partial_map_integral_norm_le
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → β)
    (φ : α × β → ℂ) {C : ℝ} (hC : ∀ p, ‖φ p‖ ≤ C) (a : α) :
    ‖∫ x, φ (a, f x) ∂ν‖ ≤ C := by
  simpa using norm_integral_le_of_norm_le_const
    (μ := ν) (Filter.Eventually.of_forall (fun x => hC (a, f x)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleForecastMeanRiemann
namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

namespace VectorPolynomial

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleLiftMap_fixed_measurable (sample : Sample) :
    Measurable (allocatedOriginalSampleLiftMap B U basis S lower width sample) :=
  (allocatedOriginalSampleLiftMap_measurable B U basis S lower width).comp
    (measurable_const.prodMk measurable_id)

variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

omit [Fintype X] in
theorem allocatedOriginalSampleForecastPartial_norm_le
    (sample : Sample) (φ : Domain → ℂ) {C : ℝ} (hC : ∀ p, ‖φ p‖ ≤ C)
    (z : Spatial → ℝ) :
    ‖∫ x, φ (z, allocatedOriginalSampleLiftMap B U basis S lower width sample x)
      ∂unitBoxMeasure Input‖ ≤ C := by
  exact probability_partial_map_integral_norm_le (unitBoxMeasure Input)
    (allocatedOriginalSampleLiftMap B U basis S lower width sample) φ hC z

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical NNReal
variable {G X : Type*} [Fintype G] [Fintype X]

theorem fixedSpatialKernelMap_lipschitz (W L : ℝ) (z : Option G × X → ℝ)
    (hz : ∀ g x, |z (some g, x)| ≤ 1) :
    LipschitzWith ((Fintype.card G : ℝ≥0) * ‖L / (1 + W)‖₊)
      (fixedSpatialKernelMap W L z) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)).mpr
  intro a
  change |(z (none, a.1) + _ * _) - (z (none, a.1) + _ * _)| ≤ _
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul]
  have hsum : |(∑ g, z (some g, a.1) * t g) - ∑ g, z (some g, a.1) * u g| ≤
      (Fintype.card G : ℝ) * dist t u := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ g, |z (some g, a.1) * t g - z (some g, a.1) * u g| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _g : G, dist t u := by
        apply Finset.sum_le_sum
        intro g _
        rw [← mul_sub, abs_mul]
        exact (mul_le_mul_of_nonneg_right (hz g a.1) (abs_nonneg _)).trans
          (by simpa only [one_mul, Real.dist_eq] using dist_le_pi_dist t u g)
      _ = _ := by simp
  have h := mul_le_mul_of_nonneg_left hsum (abs_nonneg (L / (1 + W)))
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, coe_nnnorm, Real.norm_eq_abs,
    mul_left_comm, mul_assoc] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelSlowBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

theorem allocatedKernelNormalizedSlope_nonneg :
    0 ≤ (S.value : ℝ) / (1 + budget) :=
  div_nonneg (Nat.cast_nonneg _) (by
    have h := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    linarith)

theorem allocatedKernelSlowBudget_le_one :
    (Fintype.card G : ℝ) * (S.value : ℝ) / (1 + budget) ≤ 1 := by
  have hcard : Fintype.card G ≤ Fintype.card (LayerSamplerVariables G I n B) :=
    Fintype.card_le_of_injective (Sum.inl : G → LayerSamplerVariables G I n B) Sum.inl_injective
  have hc : (Fintype.card G : ℝ) ≤ Fintype.card (LayerSamplerVariables G I n B) :=
    Nat.cast_le.mpr hcard
  have hden : 0 < 1 + budget := by
    have h := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    linarith
  apply (div_le_one hden).mpr
  rw [allocatedPhysicalRootBudget_zero]
  exact (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)).trans (le_add_of_nonneg_left zero_le_one)

theorem allocatedKernelSlowBudget_abs_le_one :
    (Fintype.card G : ℝ) * |(S.value : ℝ) / (1 + budget)| ≤ 1 := by
  rw [abs_of_nonneg (allocatedKernelNormalizedSlope_nonneg B U basis S), ← mul_div_assoc]
  exact allocatedKernelSlowBudget_le_one B U basis S

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedKernelForecastSourceDecoupling
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

omit [DecidableEq G] in

theorem allocatedOriginalSampleForecastPartial_lipschitz
    (sample : Sample) (φ : Domain → ℂ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    LipschitzWith K (fun z : Spatial =>
      ∫ v, φ (z, allocatedOriginalSampleLiftMap B U basis S lower width sample v)
        ∂unitBoxMeasure Input) := by
  let F := allocatedOriginalSampleLiftMap B U basis S lower width sample
  have hi (z : Spatial) : Integrable (fun v => φ (z, F v)) (unitBoxMeasure Input) :=
    ⟨(hφ.continuous.measurable.comp (measurable_const.prodMk
      (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample))).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun v => hbound _))⟩
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, ← integral_sub (hi z) (hi w)]
  have hb : ∀ᵐ v ∂unitBoxMeasure Input,
      ‖φ (z, F v) - φ (w, F v)‖ ≤ (K : ℝ) * dist z w := by
    apply Filter.Eventually.of_forall
    intro v
    have hd := hφ.dist_le_mul (z, F v) (w, F v)
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] at hd
    simpa only [dist_eq_norm] using hd
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

end Erdos3.VectorPolynomial

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

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

omit hR hσ [DecidableEq G] in
theorem allocatedFixedSpatialKernelMap_lipschitz
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1) :
    LipschitzWith 1 (fixedSpatialKernelMap budget (S.value : ℝ) z) := by
  apply (fixedSpatialKernelMap_lipschitz budget (S.value : ℝ) z hz).weaken
  change (Fintype.card G : ℝ) * ‖(S.value : ℝ) / (1 + budget)‖ ≤ 1
  simpa only [Real.norm_eq_abs] using allocatedKernelSlowBudget_abs_le_one B U basis S

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
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

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

omit hR hσ in
theorem allocatedFixedPath_sliced_kernel_residue_riemann
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (sample : Sample)
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (H : G → ℕ) (hH : ∀ g, 0 < H g) (start : G → ℤ)
    (step : ℕ) (hstep : 0 < step)
    (hcontained : ∀ g, integerProgressionSupport (start g) (step : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (q : ℕ) [NeZero q] (hsize : ∀ g, q ≤ H g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H g) < 1)
    (φ : (G → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ r, LipschitzWith Kφ (φ r)) (hbound : ∀ r y, ‖φ r y‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (H g) (hH g))).complexMean
        (fun x => ∫ v, φ (fun g => ((start g + (step : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((start g : ℝ) + (step : ℝ) * (x g none : ℝ)) / S.value),
            allocatedOriginalSampleLiftMap B U basis S lower width sample v) ∂unitBoxMeasure Input) -
      (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun r =>
        ∫ k, ∫ v, φ (fun g => (start g : ZMod q) + (step : ZMod q) * r g)
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * k g) / S.value),
            allocatedOriginalSampleLiftMap B U basis S lower width sample v)
          ∂unitBoxMeasure Input ∂unitBoxMeasure G)‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) *
        ∑ g, (q : ℝ) / H g := by
  classical
  let F := fun (r : G → ZMod q) (k : G → ℝ) =>
    ∫ v, φ r (fixedSpatialKernelMap budget (S.value : ℝ) z k,
      allocatedOriginalSampleLiftMap B U basis S lower width sample v) ∂unitBoxMeasure Input
  have hF (r : G → ZMod q) : LipschitzWith Kφ (F r) := by
    simpa only [mul_one, Function.comp_def, F] using
      (allocatedOriginalSampleForecastPartial_lipschitz B U basis S lower width sample
        (φ r) (hφ r) (hbound r)).comp
          (allocatedFixedSpatialKernelMap_lipschitz B U basis S z hz)
  have hFb (r : G → ZMod q) (k : G → ℝ) : ‖F r k‖ ≤ 1 :=
    allocatedOriginalSampleForecastPartial_norm_le B U basis S lower width sample
      (φ r) (hbound r) _
  have hspan := affineKernel_span_of_contained H hH start step S.value hstep hcontained
  have he := affineKernel_residue_slow_quadrature H q hH (NeZero.pos q) hsize
    (fun g => by simpa only [Measure.real, scalarCubeDomain_empty_volume, ENNReal.toReal_one] using hsmall g)
    (fun g => (start g : ℝ)) (step : ℝ) (S.value : ℝ) (by exact_mod_cast S.positive)
    (Nat.cast_nonneg _) hspan
    (fun r g => (start g : ZMod q) + (step : ZMod q) * r g) F hF hFb
  have hid (r : G → ZMod q) :
      (∫ k, F (fun g => (start g : ZMod q) + (step : ZMod q) * r g)
        (affineKernelContinuousPoint (fun g => (start g : ℝ)) (step : ℝ) (S.value : ℝ) H k)
        ∂scalarCubeProductMeasure G Empty) =
      ∫ k, F (fun g => (start g : ZMod q) + (step : ZMod q) * r g)
        (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * k g) / S.value)
        ∂unitBoxMeasure G := by
    rw [← scalarCubeProductMeasure_empty_map G]
    exact (integral_map (by fun_prop : Measurable
        (fun k : G → Option Empty → ℝ => fun g => k g none)).aemeasurable
      (show AEStronglyMeasurable (fun k : G → ℝ =>
        F (fun g => (start g : ZMod q) + (step : ZMod q) * r g)
          (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * k g) / S.value))
          ((scalarCubeProductMeasure G Empty).map (fun k => fun g => k g none)) from
        ((hF _).continuous.comp (by fun_prop)).measurable.aestronglyMeasurable)).symm
  simpa only [hid, F, FiniteProbabilityWeights.uniform_complexMean, Measure.real,
    scalarCubeDomain_empty_volume, ENNReal.toReal_one, div_one,
    Int.cast_add, Int.cast_mul, Int.cast_natCast] using he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedJointComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
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

variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => Spatial × (Output → ℝ)
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

include hR hσ in
theorem allocatedFixedPath_sliced_joint_residue_comparison_s2_oai
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (HG : G → ℕ) (hHG : ∀ g, 0 < HG g) (cG : G → ℤ)
    (stepG : ℕ) (hstepG : 0 < stepG)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (sample : Sample)
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
    (q : ℕ) [NeZero q]
    (hsizeG : ∀ g, q ≤ HG g)
    (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1) (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (hδone : δ ≤ 1) (b : ∀ a : Active, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
    (φ : (G → ZMod q) → (Input → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ rG r, LipschitzWith Kφ (φ rG r)) (hφone : ∀ rG r y, ‖φ rG r y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (HG g) (hHG g))
    let active := FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j)
      (by have := hH j; omega))
    let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
      containedProgressionCubeMap Empty S.value (HG g) stepG (cG g) S.positive (hcontainedG g) (x g)
    ‖kernel.complexMean (fun x => active.complexMean (fun v =>
        φ (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
          (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((cG g : ℝ) + (stepG : ℝ) * (x g none : ℝ)) / S.value),
            allocatedOriginalSampleFullSliceMap B U basis S (embed x) u (fun _ _ => 0) (fun _ _ => 1)
              sample (fun j => ((c j : ℝ) + (step j : ℝ) * (v j none : ℝ)) / S.value)))) -
      (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun rA =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          ∫ k, ∫ v, φ (fun g => (cG g : ZMod q) + (stepG : ZMod q) * rG g)
            (fun j => (c j : ZMod q) + (step j : ZMod q) * rA j)
            (fixedSpatialKernelMap budget (S.value : ℝ) z
              (fun g => ((cG g : ℝ) + (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) * k g) / S.value),
              allocatedOriginalSampleLiftMap B U basis S lower width sample v)
            ∂unitBoxMeasure Input ∂unitBoxMeasure G))‖ ≤
      ((∑ j, (q : ℝ) / H j) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) * ∑ g, (q : ℝ) / HG g := by
  classical
  intro lower width K kernel active embed
  let residues := FiniteProbabilityWeights.uniform (Input → ZMod q)
  let EA := (∑ j, (q : ℝ) / H j) +
    (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
      ∑ j, (q : ℝ) / H j + K * ε) + 2 * η)
  let EG := (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) *
    ∑ g, (q : ℝ) / HG g
  let rkernel := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
    ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q)
  let point := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) =>
    fixedSpatialKernelMap budget (S.value : ℝ) z
      (fun g => ((cG g : ℝ) + (stepG : ℝ) * (x g none : ℝ)) / S.value)
  let source := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) =>
    active.complexMean (fun v =>
      φ (rkernel x) (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
        (point x, allocatedOriginalSampleFullSliceMap B U basis S (embed x) u
          (fun _ _ => 0) (fun _ _ => 1) sample
          (fun j => ((c j : ℝ) + (step j : ℝ) * (v j none : ℝ)) / S.value)))
  let reference := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) (rA : Input → ZMod q) =>
    ∫ v, φ (rkernel x) (fun j => (c j : ZMod q) + (step j : ZMod q) * rA j)
      (point x, allocatedOriginalSampleLiftMap B U basis S lower width sample v) ∂unitBoxMeasure Input
  have hfirst0 (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) :
      ‖source x - residues.complexMean (reference x)‖ ≤ EA := by
    let test := fun (rA : Input → ZMod q) (y : Output → ℝ) => φ (rkernel x) rA (point x, y)
    have htest (rA : Input → ZMod q) : LipschitzWith Kφ (test rA) := by
      apply LipschitzWith.of_dist_le_mul
      intro v w
      simpa only [test, Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
        (hφ (rkernel x) rA).dist_le_mul (point x, v) (point x, w)
    simpa only [source, reference, EA, K, lower, width, active, test, residues,
      FiniteProbabilityWeights.uniform_complexMean] using
      allocatedOriginalSample_sliced_affine_residue_comparison_s2 B U basis hR hσ S (embed x) u
        sample hs ht hσbound step H c hstep hH hδ hsubset hdense q hsize hsmall hε hmesh
        hδone b hη A hA htail test htest (fun rA y => hφone _ _ _)
  have hfirst := (kernel.norm_complexMean_sub_le source
    (fun x => residues.complexMean (reference x)) (fun _ => EA)
      (fun x _ => hfirst0 x)).trans_eq (kernel.mean_const EA)
  have hlast := (residues.norm_complexMean_sub_le
    (fun rA => kernel.complexMean (fun x => reference x rA))
    (fun rA => (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
      ∫ k, ∫ v, φ (fun g => (cG g : ZMod q) + (stepG : ZMod q) * rG g)
        (fun j => (c j : ZMod q) + (step j : ZMod q) * rA j)
        (fixedSpatialKernelMap budget (S.value : ℝ) z
          (fun g => ((cG g : ℝ) + (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) * k g) / S.value),
          allocatedOriginalSampleLiftMap B U basis S lower width sample v)
        ∂unitBoxMeasure Input ∂unitBoxMeasure G)) (fun _ => EG) (fun rA _ =>
      allocatedFixedPath_sliced_kernel_residue_riemann B U basis S z hz sample lower width
        HG hHG cG stepG hstepG hcontainedG q hsizeG hsmallG
        (fun rG => φ rG (fun j => (c j : ZMod q) + (step j : ZMod q) * rA j))
        (fun rG => hφ rG _) (fun rG y => hφone rG _ y))).trans_eq (residues.mean_const EG)
  rw [← FiniteProbabilityWeights.complexMean_commute kernel residues] at hlast
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfirst hlast)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_joint_residue_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_joint_residue_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5}
