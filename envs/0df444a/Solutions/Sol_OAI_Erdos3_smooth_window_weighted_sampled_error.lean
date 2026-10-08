-- Prove2me | solution 1 for OAI.Erdos3.smooth_window_weighted_sampled_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:31:17.580986+00:00
-- url     : https://prove2.me/submissions/e7f07999-271a-45c3-92cb-2e0d5ff4afe5

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B016

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw
namespace OAI

section

namespace Erdos3

open scoped ENNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem baseArrayJoin_injective {K I X : Type*} (tail : K × I → X) :
    Function.Injective (baseArrayJoin tail) := by
  intro b c he
  funext i
  exact congrFun he (none,i)

theorem independentProductPMF_base_split {K I X : Type*} [Fintype K] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option K × I → PMF X) :
    independentProductPMF p =
      (independentProductPMF (fun k : K × I => p (some k.1,k.2))).bind
        (fun tail => (independentProductPMF (fun i => p (none,i))).map (baseArrayJoin tail)) := by
  ext z
  let tail := fun k : K × I => z (some k.1,k.2)
  let base := fun i : I => z (none,i)
  have hz : baseArrayJoin tail base = z := baseArrayJoin_eta z
  rw [← hz, PMF.bind_apply, tsum_eq_single tail]
  · rw [pmf_map_injective_at _ _ (baseArrayJoin_injective tail)]
    simp only [independentProductPMF_apply, Fintype.prod_prod_type, Fintype.prod_option, baseArrayJoin]
    exact mul_comm _ _
  · intro other hother
    have hr : baseArrayJoin tail base ∉ Set.range (baseArrayJoin other) := by
      rintro ⟨b, he⟩
      apply hother
      funext k
      exact congrFun he (some k.1,k.2)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

theorem independentProductPMF_base_cap {K I X Y : Type*} [Fintype K] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option K × I → PMF X) (f : (Option K × I → X) → Y)
    (hf : ∀ tail, Function.Injective (fun base => f (baseArrayJoin tail base)))
    (C : I → ℝ) (hC : ∀ i, 0 ≤ C i) (hp : ∀ i x, (p (none,i) x).toReal ≤ C i) (y : Y) :
    ((independentProductPMF p).map f y).toReal ≤ ∏ i, C i := by
  rw [independentProductPMF_base_split, PMF.map_bind]
  simp_rw [PMF.map_comp]
  apply pmf_bind_injective_toReal_cap _ _ _ hf (Finset.prod_nonneg (fun i _ => hC i))
  intro base
  rw [independentProductPMF_toReal]
  exact Finset.prod_le_prod (fun i _ => ENNReal.toReal_nonneg) (fun i _ => hp i (base i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem pmf_image_finite_real_mean {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (hT : ∀ x ∈ S, F x ∈ T) (φ : Y → ℝ) :
    (∑' x, (p x).toReal * φ (F x)) = ∑ y ∈ T, (p.map F y).toReal * φ y := by
  have hs : (∑' x, (p x).toReal * φ (F x)) = ∑ x ∈ S, (p x).toReal * φ (F x) :=
    (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hp x hx, zero_mul])).tsum_eq
  rw [hs]
  simp_rw [pmf_map_finite_sum p S hp F, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single (F x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · intro hn
    exact (hn (hT x hx)).elim

theorem pmf_image_energy_of_point_cap {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (e : Y → ℝ) (he : ∀ y ∉ T, e y = 0)
    {C : ℝ} (hcap : ∀ y, (p.map F y).toReal ≤ C) :
    (∑' x, (p x).toReal * e (F x) ^ 2) ≤ C * ∑ y ∈ T, e y ^ 2 := by
  let U := T ∪ S.image F
  have hU : ∀ x ∈ S, F x ∈ U := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hsum : (∑ y ∈ U, e y ^ 2) = ∑ y ∈ T, e y ^ 2 := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro y _ hy
    rw [he y hy, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [pmf_image_finite_real_mean p S hp F U hU (fun y => e y ^ 2)]
  calc
    _ ≤ ∑ y ∈ U, C * e y ^ 2 :=
      Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hcap y) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum, hsum]

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

theorem shiftedSmoothProductPMF_base_cap {K I Y : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (Option K × I → ℤ) → Y)
    (hf : ∀ tail, Function.Injective (fun base => f (baseArrayJoin tail base)))
    (hbase : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ S (none,i)) (y : Y) :
    ((shiftedSmoothProductPMF a S hS hZ).map f y).toReal ≤ ∏ i, 2 / S (none,i) := by
  rw [shiftedSmoothProductPMF_eq_independent]
  apply independentProductPMF_base_cap _ f hf (fun i => 2 / S (none,i))
    (fun i => div_nonneg (by norm_num) (hS (none,i)).le)
  intro i k
  exact shiftedSmoothCoefficientPMF_le (a (none,i)) (hbase i) k

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem smoothProbabilityProfile_inner_lower (x : ℝ) (hx : |x| ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ smoothProbabilityProfile x := by
  have hx' : probabilityProfileBump x = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simpa [probabilityProfileBump, Real.dist_eq] using hx)
  have hi := probabilityProfileBump.integral_le_measure_closedBall volume
  norm_num [probabilityProfileBump] at hi
  change (∫ y, probabilityProfileBump y) ≤ 3 / 2 at hi
  change (1 / 2 : ℝ) ≤ probabilityProfileBump x / ∫ y, probabilityProfileBump y
  rw [hx']
  apply (le_div_iff₀ probabilityProfileBump.integral_pos).mpr
  linarith

theorem shiftedSmoothCoefficientPMF_inner_lower (a : ℝ) {S : ℝ}
    (hscale : 8 * (probabilityProfileLipschitz : ℝ) ≤ S)
    (hS : 0 < S) (hZ : 0 < shiftedSmoothSampleSum a S) (k : ℤ)
    (hk : |(k : ℝ) - a| ≤ S / 2) :
    1 / (3 * S) ≤ (shiftedSmoothCoefficientPMF a S hS hZ k).toReal := by
  have hk' : |((k : ℝ) - a) / S| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hS]
    exact (div_le_iff₀ hS).mpr (by linarith)
  rw [shiftedSmoothCoefficientPMF_apply]
  have hp := smoothProbabilityProfile_inner_lower _ hk'
  have hb := (shiftedSmoothSampleSum_bounds a hscale).2
  apply (div_le_div_iff₀ (by positivity : 0 < 3 * S) hZ).mpr
  nlinarith

theorem shiftedSmoothProductPMF_inner_lower {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (z : I → ℤ) (hz : ∀ i, |(z i : ℝ) - a i| ≤ S i / 2) :
    (∏ i, 1 / (3 * S i)) ≤ (shiftedSmoothProductPMF a S hS hZ z).toReal := by
  rw [shiftedSmoothProductPMF_eq_independent, independentProductPMF_toReal]
  apply Finset.prod_le_prod
  · intro i _
    exact div_nonneg zero_le_one (mul_nonneg (by norm_num) (hS i).le)
  · intro i _
    exact shiftedSmoothCoefficientPMF_inner_lower (a i) (hscale i) (hS i)
      (shiftedSmoothProductMass_coordinate_pos a S hS hZ i) (z i) (hz i)

theorem shiftedSmoothProductPMF_inner_mass {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (z : I → ℤ) (hz : ∀ i, |(z i : ℝ) - a i| ≤ S i / 2) :
    1 ≤ (∏ i, 3 * S i) * (shiftedSmoothProductPMF a S hS hZ z).toReal := by
  have hprod : 0 < ∏ i, 3 * S i :=
    Finset.prod_pos (fun i _ => mul_pos (by norm_num) (hS i))
  have h := shiftedSmoothProductPMF_inner_lower a S hS hZ hscale z hz
  rw [Finset.prod_div_distrib] at h
  simp only [Finset.prod_const_one] at h
  exact (div_le_iff₀ hprod).mp h |>.trans_eq (mul_comm _ _)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_mul_const {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → ℝ) (c : ℝ) : p.mean (fun x => f x * c) = p.mean f * c := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]

end FiniteProbabilityWeights

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothIntegerTranslation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem smoothAffineSample_base_injective {K I : Type*} [Fintype K]
    (t : K → ℤ) (tail : K × I → ℤ) :
    Function.Injective (fun base => smoothAffineSample t (baseArrayJoin tail base)) := by
  intro b c h
  funext i
  have hi := congrFun h i
  change b i + (∑ k, t k * tail (k, i)) = c i + (∑ k, t k * tail (k, i)) at hi
  exact add_right_cancel hi

theorem smoothAffineSample_point_cap {K I : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hbase : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S (none, i))
    (t : K → ℤ) (y : I → ℤ) :
    ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffineSample t) y).toReal ≤
      ∏ i, 2 / S (none, i) :=
  shiftedSmoothProductPMF_base_cap a S hS hZ (smoothAffineSample t)
    (smoothAffineSample_base_injective t) hbase y

theorem smoothAffineSample_energy {K I : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hbase : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S (none, i))
    (t : K → ℤ) (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0) :
    (∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal * e (smoothAffineSample t z) ^ 2) ≤
      (∏ i, 2 / S (none, i)) * ∑ y ∈ T, e y ^ 2 :=
  pmf_image_energy_of_point_cap (shiftedSmoothProductPMF a S hS hZ)
    (rectangularWeightIndices a S 1) (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)
    (smoothAffineSample t) T e he (smoothAffineSample_point_cap a S hS hZ hbase t)

theorem smoothAffineSample_energy_of_sum_bound {K I : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hbase : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S (none, i))
    (t : K → ℤ) (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0)
    {E : ℝ} (henergy : (∑ y ∈ T, e y ^ 2) ≤ E * T.card) :
    (∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal * e (smoothAffineSample t z) ^ 2) ≤
      (∏ i, 2 / S (none, i)) * (E * T.card) := by
  exact (smoothAffineSample_energy a S hS hZ hbase t T e he).trans
    (mul_le_mul_of_nonneg_left henergy (Finset.prod_nonneg (fun i _ => div_nonneg (by norm_num) (hS (none, i)).le)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

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

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothWindowChange
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_window_change_of_measure {X : Type*} [DecidableEq X]
    (S W : Finset X) (hWS : W ⊆ S) (p : FiniteProbabilityWeights S)
    {D : ℝ} (hD : 0 < D)
    (hlower : ∀ z : S, z.val ∈ W → 1 ≤ D * p.weight z) :
    ∃ w : S → ℝ, (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
      ∀ f : X → ℝ, (𝔼 z ∈ W, f z) =
        (D / W.card) * p.mean (fun z => w z * f z.val) := by
  let w : S → ℝ := fun z => if z.val ∈ W then 1 / (D * p.weight z) else 0
  have hw (z : S) : 0 ≤ w z ∧ w z ≤ 1 := by
    dsimp only [w]
    split_ifs with hz
    · have hpos : 0 < D * p.weight z := lt_of_lt_of_le zero_lt_one (hlower z hz)
      exact ⟨div_nonneg zero_le_one hpos.le, (div_le_one hpos).mpr (hlower z hz)⟩
    · exact ⟨le_rfl, zero_le_one⟩
  refine ⟨w, hw, fun f => ?_⟩
  have hpoint (z : S) : D * (p.weight z * (w z * f z.val)) =
      if z.val ∈ W then f z.val else 0 := by
    by_cases hz : z.val ∈ W
    · have hp : p.weight z ≠ 0 := by
        intro h
        have hh := hlower z hz
        norm_num [h] at hh
      simp only [w, hz, ite_true]
      field_simp
    · simp [w, hz]
  have hsum : D * p.mean (fun z => w z * f z.val) = ∑ z ∈ W, f z := by
    unfold FiniteProbabilityWeights.mean
    rw [Finset.mul_sum]
    simp_rw [hpoint]
    rw [Finset.sum_coe_sort S (fun z => if z ∈ W then f z else 0)]
    calc
      _ = ∑ z ∈ W, if z ∈ W then f z else 0 :=
        (Finset.sum_subset hWS (fun z _ hz => by simp [hz])).symm
      _ = _ := Finset.sum_congr rfl (fun z hz => by simp [hz])
  rw [Finset.expect_eq_sum_div_card, ← hsum]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothSourceFiniteWeights_mean {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (J → ℤ) → ℝ) :
    (smoothSourceFiniteWeights a S hS hZ).mean (fun z => f z.val) =
      ∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal * f z := by
  unfold FiniteProbabilityWeights.mean
  change (∑ z : rectangularWeightIndices a S 1,
    (shiftedSmoothProductPMF a S hS hZ z.val).toReal * f z.val) = _
  rw [Finset.sum_coe_sort (rectangularWeightIndices a S 1)
    (fun z => (shiftedSmoothProductPMF a S hS hZ z).toReal * f z)]
  exact (hasSum_sum_of_ne_finset_zero (fun z hz => by
    rw [shiftedSmoothProductPMF_toReal_zero_off a S hS hZ z hz, zero_mul])).tsum_eq.symm

theorem smoothSourceFiniteWeights_energy {K I : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hbase : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S (none, i))
    (t : K → ℤ) (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0)
    {E : ℝ} (henergy : (∑ y ∈ T, e y ^ 2) ≤ E * T.card) :
    (smoothSourceFiniteWeights a S hS hZ).mean (fun z => e (smoothAffineSample t z.val) ^ 2) ≤
      (∏ i, 2 / S (none, i)) * (E * T.card) := by
  rw [smoothSourceFiniteWeights_mean a S hS hZ (fun z => e (smoothAffineSample t z) ^ 2)]
  exact smoothAffineSample_energy_of_sum_bound a S hS hZ hbase t T e he henergy

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smooth_inner_mem_indices {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (z : I → ℤ) (hz : ∀ i, |(z i : ℝ) - a i| ≤ S i / 2) :
    z ∈ rectangularWeightIndices a S 1 := by
  classical
  by_contra hn
  have h := shiftedSmoothProductPMF_inner_mass a S hS hZ hscale z hz
  rw [shiftedSmoothProductPMF_toReal_zero_off a S hS hZ z hn, mul_zero] at h
  norm_num at h

theorem smooth_window_change_of_measure {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (W : Finset (I → ℤ)) (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - a i| ≤ S i / 2) :
    ∃ w : rectangularWeightIndices a S 1 → ℝ,
      (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
      ∀ f : (I → ℤ) → ℝ, (𝔼 z ∈ W, f z) =
        ((3 : ℝ) ^ Fintype.card I * (∏ i, S i) / W.card) *
          (smoothSourceFiniteWeights a S hS hZ).mean (fun z => w z * f z.val) := by
  classical
  have hsub : W ⊆ rectangularWeightIndices a S 1 :=
    fun z hz => smooth_inner_mem_indices a S hS hZ hscale z (hW z hz)
  have hD : 0 < ∏ i, 3 * S i :=
    Finset.prod_pos (fun i _ => mul_pos (by norm_num) (hS i))
  have h := finite_window_change_of_measure (rectangularWeightIndices a S 1) W hsub
    (smoothSourceFiniteWeights a S hS hZ) hD
    (fun z hz => shiftedSmoothProductPMF_inner_mass a S hS hZ hscale z.val (hW z.val hz))
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedSmoothSampledError
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem finite_mean_square_as_pair {T : Type*} [Fintype T]
    (q : FiniteProbabilityWeights T) (f : T → ℝ) :
    (q.mean f) ^ 2 = (q.prod q).mean (fun t => f t.1 * f t.2) := by
  rw [FiniteProbabilityWeights.mean_prod]
  simp only [q.mean_const_mul, q.mean_mul_const, pow_two]

theorem sampled_second_moment_identity {Ω T : Type*} [Fintype Ω] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights T) (e : Ω → T → ℝ) :
    p.mean (fun x => (q.mean (e x)) ^ 2) =
      (q.prod q).mean (fun t => p.mean (fun x => e x t.1 * e x t.2)) := by
  simp_rw [finite_mean_square_as_pair q]
  exact p.mean_comm (q.prod q) (fun x t => e x t.1 * e x t.2)

theorem finite_mean_bad_event_bound {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (Bad : X → Prop) (f : X → ℝ) {C epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hbad : ∀ x, Bad x → f x ≤ C)
    (hgood : ∀ x, ¬ Bad x → f x ≤ epsilon) :
    p.mean f ≤ C * p.eventProbability Bad + epsilon := by
  have hpoint (x : X) : f x ≤ C * (if Bad x then (1 : ℝ) else 0) + epsilon := by
    by_cases hx : Bad x
    · simp only [hx, ite_true, mul_one]
      linarith [hbad x hx]
    · simpa only [hx, ite_false, mul_zero, zero_add] using hgood x hx
  apply (p.mean_mono hpoint).trans_eq
  rw [p.mean_add, p.mean_const_mul, p.mean_const]
  rfl

theorem sampled_second_moment_bad_pairs {Ω T : Type*} [Fintype Ω] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights T) (e : Ω → T → ℝ)
    (Bad : T × T → Prop) {C epsilon beta : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hbad : ∀ t, Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ C)
    (hgood : ∀ t, ¬ Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ epsilon) :
    p.mean (fun x => (q.mean (e x)) ^ 2) ≤ C * beta + epsilon := by
  rw [sampled_second_moment_identity]
  have h := finite_mean_bad_event_bound (q.prod q) Bad
    (fun t => p.mean (fun x => e x t.1 * e x t.2)) hepsilon
    (fun t ht => (le_abs_self _).trans (hbad t ht))
    (fun t ht => (le_abs_self _).trans (hgood t ht))
  have hm := mul_le_mul_of_nonneg_left hmass hC
  linarith

theorem sampled_weighted_error_of_bad_pairs {Ω T : Type*} [Fintype Ω] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights T) (e : Ω → T → ℝ)
    (Bad : T × T → Prop) {C epsilon beta : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hbad : ∀ t, Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ C)
    (hgood : ∀ t, ¬ Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ epsilon)
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    |p.mean (fun x => w x * q.mean (e x))| ≤ Real.sqrt (C * beta + epsilon) := by
  have he := sampled_second_moment_bad_pairs p q e Bad hC hepsilon hmass hbad hgood
  have hw2 : p.mean (fun x => w x ^ 2) ≤ 1 := by
    apply (p.mean_mono (g := fun _ => 1) ?_).trans_eq (p.mean_const 1)
    intro x
    have h := hw x
    nlinarith
  have he0 := p.mean_nonneg (fun x => sq_nonneg (q.mean (e x)))
  have hc := p.mean_mul_sq_le w (fun x => q.mean (e x))
  have hm := mul_le_mul_of_nonneg_right hw2 he0
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  nlinarith only [hc, hm, he]

theorem sampled_pair_correlation_cap {Ω T : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (e : Ω → T → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ t, p.mean (fun x => e x t ^ 2) ≤ C) (t u : T) :
    |p.mean (fun x => e x t * e x u)| ≤ C := by
  apply abs_le_of_sq_le_sq _ hC
  calc
    _ ≤ p.mean (fun x => e x t ^ 2) * p.mean (fun x => e x u ^ 2) :=
      p.mean_mul_sq_le (fun x => e x t) (fun x => e x u)
    _ ≤ C * C := mul_le_mul (henergy t) (henergy u) (p.mean_nonneg (fun x => sq_nonneg _)) hC
    _ = C ^ 2 := by ring

theorem sampled_weighted_error_of_energy {Ω T : Type*} [Fintype Ω] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights T) (e : Ω → T → ℝ)
    (Bad : T × T → Prop) {C epsilon beta : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (henergy : ∀ t, p.mean (fun x => e x t ^ 2) ≤ C)
    (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hgood : ∀ t, ¬ Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ epsilon)
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    |p.mean (fun x => w x * q.mean (e x))| ≤ Real.sqrt (C * beta + epsilon) :=
  sampled_weighted_error_of_bad_pairs p q e Bad hC hepsilon hmass
    (fun t _ => sampled_pair_correlation_cap p e hC henergy t.1 t.2) hgood w hw

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

theorem smooth_window_weighted_sampled_error {K I P : Type*}
    [Fintype K] [Fintype I] [Fintype P]
    (a S : Option K × I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (W : Finset (Option K × I → ℤ))
    (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - a i| ≤ S i / 2)
    (q : FiniteProbabilityWeights P) (t : P → K → ℤ)
    (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0)
    {E epsilon beta : ℝ} (hE : 0 ≤ E) (hepsilon : 0 ≤ epsilon)
    (henergy : (∑ y ∈ T, e y ^ 2) ≤ E * T.card)
    (Bad : P × P → Prop) (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hgood : ∀ u, ¬ Bad u → |(smoothSourceFiniteWeights a S hS hZ).mean
      (fun z => e (smoothAffineSample (t u.1) z.val) * e (smoothAffineSample (t u.2) z.val))| ≤ epsilon)
    (v : (Option K × I → ℤ) → ℝ) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) :
    |𝔼 z ∈ W, v z * q.mean (fun u => e (smoothAffineSample (t u) z))| ≤
      ((3 : ℝ) ^ Fintype.card (Option K × I) * (∏ i, S i) / W.card) *
        Real.sqrt (((∏ i, 2 / S (none, i)) * (E * T.card)) * beta + epsilon) := by
  obtain ⟨w, hw, hchange⟩ := smooth_window_change_of_measure a S hS hZ hscale W hW
  have hC : 0 ≤ (∏ i, 2 / S (none, i)) * (E * T.card) := by
    exact mul_nonneg (Finset.prod_nonneg (fun i _ => div_nonneg (by norm_num) (hS (none, i)).le))
      (mul_nonneg hE (Nat.cast_nonneg _))
  have hprod (z : rectangularWeightIndices a S 1) : 0 ≤ w z * v z.val ∧ w z * v z.val ≤ 1 :=
    ⟨mul_nonneg (hw z).1 (hv z.val).1,
      (mul_le_mul (hw z).2 (hv z.val).2 (hv z.val).1 zero_le_one).trans_eq (one_mul 1)⟩
  have hsample := sampled_weighted_error_of_energy (smoothSourceFiniteWeights a S hS hZ) q
    (fun z u => e (smoothAffineSample (t u) z.val)) Bad hC hepsilon
    (fun u => smoothSourceFiniteWeights_energy a S hS hZ (fun i => hscale (none, i)) (t u) T e he henergy)
    hmass hgood (fun z => w z * v z.val) hprod
  have hfactor : 0 ≤ (3 : ℝ) ^ Fintype.card (Option K × I) * (∏ i, S i) / W.card := by
    exact div_nonneg (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => (hS i).le))) (Nat.cast_nonneg _)
  rw [hchange (fun z => v z * q.mean (fun u => e (smoothAffineSample (t u) z))), abs_mul, abs_of_nonneg hfactor]
  exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hsample) hfactor

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.smooth_window_weighted_sampled_error.{u_1, u_2, u_3} := @OAI.Erdos3.smooth_window_weighted_sampled_error.{u_1, u_2, u_3}
