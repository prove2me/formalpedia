-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.eq27_er1_clbi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T03:00:56.359507+00:00
-- url     : https://prove2.me/submissions/e22786b7-134f-4781-b04a-5528d436f476

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
open MeasureTheory ProbabilityTheory

namespace NestedSeatAlloc.IntPolicy

theorem solution_right_interval {s : ℝ} (hs : 0 ≤ s) :
    ∃ m : ℕ, (m : ℝ) ≤ s ∧ s < (m : ℝ) + 1 := by
  refine ⟨⌊s⌋₊, Nat.floor_le hs, ?_⟩
  exact_mod_cast Nat.lt_floor_add_one s

theorem solution_left_interval {s : ℝ} (hs : 0 < s) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) - 1 < s ∧ s ≤ (m : ℝ) := by
  let n : ℕ := ⌊s⌋₊
  by_cases heq : s = (n : ℝ)
  · have hn : 0 < n := by
      exact_mod_cast (show (0 : ℝ) < (n : ℝ) by simpa [heq] using hs)
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    refine ⟨n, hn, ?_, ?_⟩
    · rw [heq]
      linarith
    · exact le_of_eq heq
  · refine ⟨n + 1, Nat.succ_pos n, ?_, ?_⟩
    · have hfloor : (n : ℝ) ≤ s := by
        exact Nat.floor_le hs.le
      have hstrict : (n : ℝ) < s :=
        lt_of_le_of_ne hfloor (by
          intro he
          exact heq he.symm)
      simpa [n, Nat.cast_add] using hstrict
    · have hlt : s < (n : ℝ) + 1 := by
        exact_mod_cast Nat.lt_floor_add_one s
      simpa [n, Nat.cast_add] using hlt.le

private theorem solution_normed_add_group_eq_real_add_group :
    NormedAddCommGroup.toAddCommGroup = Real.instAddCommGroup := by
  apply AddCommGroup.ext
  funext x y
  rfl

private theorem solution_normed_space_eq_real_module :
    NormedSpace.toModule = (inferInstance : Module ℝ ℝ) := by
  apply Module.ext
  funext r x
  rfl

private theorem solution_normed_topology_eq_real_topology :
    UniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace ℝ) := by
  apply TopologicalSpace.ext
  funext s
  rfl

private theorem solution_normed_mul_eq_real_mul :
    @Distrib.toMul ℝ
      (@instDistribOfSemiring ℝ
        (@Ring.toSemiring ℝ
          (@NormedRing.toRing ℝ
            (@NormedCommRing.toNormedRing ℝ Real.normedCommRing)))) = Real.instMul := by
  have hmul :
      (@Distrib.toMul ℝ
        (@instDistribOfSemiring ℝ
          (@Ring.toSemiring ℝ
            (@NormedRing.toRing ℝ
              (@NormedCommRing.toNormedRing ℝ Real.normedCommRing))))).mul =
        Real.instMul.mul := by
    funext x y
    rfl
  exact congrArg (fun m : ℝ → ℝ → ℝ => (⟨m⟩ : Mul ℝ)) hmul

/-
These bridges align the normed structures used by the derivative API with
the canonical real algebra/topology structures used in the theorem statement.
The projections infer their carrier/scalar parameters from the equality type;
the operations are identified extensionally.
-/

theorem solution_right_affine_derivative
    {g : ℝ → ℝ} {m : ℕ} {a b s : ℝ}
    (hlo : (m : ℝ) ≤ s) (hhi : s < (m : ℝ) + 1)
    (haff : ∀ t ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1), g t = a + b * t) :
    HasDerivWithinAt g b (Set.Ici s) s := by
  have hlin' := ((hasDerivAt_id s).const_mul b).add_const a
  have hlin : HasDerivAt (fun t : ℝ => a + b * t) b s := by
    simpa [solution_normed_add_group_eq_real_add_group,
      solution_normed_space_eq_real_module,
      solution_normed_topology_eq_real_topology,
      solution_normed_mul_eq_real_mul, add_comm] using hlin'
  refine hlin.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hhi)] with t ht hupper
    exact haff t ⟨hlo.trans ht, le_of_lt hupper⟩
  · exact haff s ⟨hlo, hhi.le⟩

theorem solution_left_affine_derivative
    {g : ℝ → ℝ} {m : ℕ} {a b s : ℝ}
    (hlo : (m : ℝ) - 1 < s) (hhi : s ≤ (m : ℝ))
    (haff : ∀ t ∈ Set.Icc ((m : ℝ) - 1) (m : ℝ), g t = a + b * t) :
    HasDerivWithinAt g b (Set.Iic s) s := by
  have hlin' := ((hasDerivAt_id s).const_mul b).add_const a
  have hlin : HasDerivAt (fun t : ℝ => a + b * t) b s := by
    simpa [solution_normed_add_group_eq_real_add_group,
      solution_normed_space_eq_real_module,
      solution_normed_topology_eq_real_topology,
      solution_normed_mul_eq_real_mul, add_comm] using hlin'
  refine hlin.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlo)] with t ht hlower
    exact haff t ⟨le_of_lt hlower, ht.trans hhi⟩
  · exact haff s ⟨hlo.le, hhi⟩

theorem solution_right_tail_event
    {Ω : Type*} [MeasurableSpace Ω] {s : ℝ} {m : ℕ}
    (X : ℕ → Ω → ℝ) (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hlo : (m : ℝ) ≤ s) (hhi : s < (m : ℝ) + 1) :
    {ω | (m : ℝ) < X 1 ω} = {ω | s < X 1 ω} := by
  ext ω
  obtain ⟨n, hn⟩ := hint 1 ω
  change (m : ℝ) < X 1 ω ↔ s < X 1 ω
  rw [hn]
  constructor
  · intro hmn
    have hnext : (m : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (by exact_mod_cast hmn))
    linarith
  · intro hsn
    by_contra hmn
    have hnm : n ≤ m := Nat.le_of_not_gt (by exact_mod_cast hmn)
    have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith

theorem solution_left_tail_event
    {Ω : Type*} [MeasurableSpace Ω] {s : ℝ} {m : ℕ}
    (X : ℕ → Ω → ℝ) (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hlo : (m : ℝ) - 1 < s) (hhi : s ≤ (m : ℝ)) :
    {ω | (m : ℝ) - 1 < X 1 ω} = {ω | s ≤ X 1 ω} := by
  ext ω
  obtain ⟨n, hn⟩ := hint 1 ω
  change (m : ℝ) - 1 < X 1 ω ↔ s ≤ X 1 ω
  rw [hn]
  by_cases hmn : m ≤ n
  · have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    constructor <;> intro h <;> linarith
  · have hnm : n < m := Nat.lt_of_not_ge hmn
    have hcast : (n : ℝ) ≤ (m : ℝ) - 1 := by
      have hsucc : n + 1 ≤ m := Nat.succ_le_iff.mpr hnm
      have hsucc' : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hsucc
      linarith
    constructor
    · intro hleft
      exact False.elim ((not_lt_of_ge hcast) hleft)
    · intro hright
      exact False.elim
        ((not_le_of_gt (lt_of_le_of_lt hcast hlo)) hright)

theorem solution_integer_demand_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) (k : ℕ) (ω : Ω) :
    0 ≤ X k ω := by
  rcases hint k ω with ⟨n, hn⟩
  rw [hn]
  exact_mod_cast (Nat.zero_le n)

theorem solution_branch_slope_integral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (m : ℕ) :
    (∫ ω, (if (m : ℝ) < X 1 ω then f 1 else 0) ∂P) =
      f 1 * P.real {ω | (m : ℝ) < X 1 ω} := by
  letI : IsProbabilityMeasure P := hM.isProb
  have hE : MeasurableSet {ω | (m : ℝ) < X 1 ω} :=
    measurableSet_lt measurable_const (hM.meas 1)
  have hindicator :
      (fun ω => if (m : ℝ) < X 1 ω then f 1 else 0) =
        {ω | (m : ℝ) < X 1 ω}.indicator (fun _ => f 1) := by
    funext ω
    simp [Set.indicator_apply]
  rw [hindicator]
  rw [integral_indicator hE]
  rw [integral_const]
  simp [Measure.restrict_apply_univ {ω | (m : ℝ) < X 1 ω}, Measure.real] <;> ring

theorem solution_branchwise_affine_coefficients
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hf1 : 0 ≤ f 1) (m : ℕ) :
    ∃ c d : Ω → ℝ,
      Integrable c P ∧ Integrable d P ∧
      d = (fun ω => if (m : ℝ) < X 1 ω then f 1 else 0) ∧
      ∀ s, s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1) → ∀ ω,
        f 1 * min s (X 1 ω) = c ω + d ω * s := by
  letI : IsProbabilityMeasure P := hM.isProb
  let A : Set Ω := {ω | X 1 ω ≤ (m : ℝ)}
  let B : Set Ω := {ω | (m : ℝ) < X 1 ω}
  let c : Ω → ℝ := A.indicator (fun ω => f 1 * X 1 ω)
  let d : Ω → ℝ := B.indicator (fun _ => f 1)
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_le (hM.meas 1) measurable_const
  have hB : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_lt measurable_const (hM.meas 1)
  have hcMeas : Measurable c := by
    dsimp [c]
    exact (measurable_const.mul (hM.meas 1)).indicator hA
  have hdMeas : Measurable d := by
    dsimp [d]
    exact measurable_const.indicator hB
  have hcBound : 0 ≤ f 1 * ((m : ℝ) + 1) :=
    mul_nonneg hf1 (by positivity)
  have hX_nonneg : ∀ ω, 0 ≤ X 1 ω :=
    fun ω => solution_integer_demand_nonneg X hint 1 ω
  have hc : Integrable c P := by
    apply Integrable.of_bound hcMeas.aestronglyMeasurable
      (f 1 * ((m : ℝ) + 1))
    filter_upwards [] with ω
    change ‖if ω ∈ A then f 1 * X 1 ω else 0‖ ≤ f 1 * ((m : ℝ) + 1)
    by_cases hω : ω ∈ A
    · have hX : X 1 ω ≤ (m : ℝ) := by simpa [A] using hω
      simp only [hω, if_pos]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hf1 (hX_nonneg ω))]
      exact mul_le_mul_of_nonneg_left
        (le_trans hX (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)) hf1
    · simpa [hω] using hcBound
  have hd : Integrable d P := by
    apply Integrable.of_bound hdMeas.aestronglyMeasurable (f 1)
    filter_upwards [] with ω
    change ‖if ω ∈ B then f 1 else 0‖ ≤ f 1
    by_cases hω : ω ∈ B
    · simp only [hω, if_pos]
      rw [Real.norm_eq_abs, abs_of_nonneg hf1]
    · simpa [hω] using hf1
  have hdeq : d = (fun ω => if (m : ℝ) < X 1 ω then f 1 else 0) := by
    funext ω
    simp [d, B, Set.indicator_apply]
  refine ⟨c, d, hc, hd, hdeq, ?_⟩
  intro s hs ω
  obtain ⟨n, hn⟩ := hint 1 ω
  by_cases hnm : n ≤ m
  · have hX : X 1 ω ≤ (m : ℝ) := by
      rw [hn]
      exact_mod_cast hnm
    have hXs : X 1 ω ≤ s := le_trans hX hs.1
    have hAω : ω ∈ A := by simpa [A] using hX
    have hBω : ω ∉ B := by
      simp only [B, Set.mem_setOf_eq]
      exact not_lt_of_ge hX
    simp [c, d, hAω, hBω, min_eq_right hXs]
  · have hmn : m < n := Nat.lt_of_not_ge hnm
    have hX : (m : ℝ) + 1 ≤ X 1 ω := by
      rw [hn]
      exact_mod_cast (Nat.succ_le_of_lt hmn)
    have hXm : (m : ℝ) < X 1 ω := by linarith
    have hsX : s ≤ X 1 ω := le_trans hs.2 hX
    have hAω : ω ∉ A := by
      simp only [A, Set.mem_setOf_eq]
      exact not_le_of_gt hXm
    have hBω : ω ∈ B := by simpa [B] using hXm
    simp [c, d, hAω, hBω, min_eq_left hsX]

theorem solution_revenue_one_min (f p x : ℕ → ℝ) (t : ℝ) :
    revenue f p x 1 t = f 1 * min t (x 1) := by
  by_cases ht : t < x 1
  · simp [revenue, ht, min_eq_left (le_of_lt ht)]
  · have hx : x 1 ≤ t := le_of_not_gt ht
    simp [revenue, ht, min_eq_right hx]

theorem solution_integrable_truncated
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (s : ℝ) (hf1 : 0 ≤ f 1) :
    Integrable (fun ω => f 1 * min s (X 1 ω)) P := by
  letI : IsProbabilityMeasure P := hM.isProb
  have hX_nonneg : ∀ ω, 0 ≤ X 1 ω :=
    fun ω => solution_integer_demand_nonneg X hint 1 ω
  by_cases hs : 0 ≤ s
  · have hmeas : Measurable (fun ω => f 1 * min s (X 1 ω)) :=
      measurable_const.mul (measurable_const.min (hM.meas 1))
    apply Integrable.of_bound hmeas.aestronglyMeasurable (f 1 * s)
    filter_upwards [] with ω
    have hmin_nonneg : 0 ≤ min s (X 1 ω) := by
      by_cases h : s ≤ X 1 ω
      · rw [min_eq_left h]
        exact hs
      · rw [min_eq_right (le_of_lt (not_le.mp h))]
        exact hX_nonneg ω
    have hmin_le : min s (X 1 ω) ≤ s := min_le_left _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hf1 hmin_nonneg)]
    exact mul_le_mul_of_nonneg_left hmin_le hf1
  · have hsneg : s < 0 := lt_of_not_ge hs
    have hEq : (fun ω => f 1 * min s (X 1 ω)) = fun _ => f 1 * s := by
      funext ω
      rw [min_eq_left (le_trans (le_of_lt hsneg) (hX_nonneg ω))]
    rw [hEq]
    exact integrable_const _

theorem solution_pointwise_concave (a x : ℝ) (ha : 0 ≤ a) :
    ConcaveOn ℝ (Set.Ici 0) (fun s : ℝ => a * min s x) := by
  refine ⟨convex_Ici (0 : ℝ), ?_⟩
  intro s hs t ht u v hu hv huv
  have hmix_le_linear :
      u * min s x + v * min t x ≤ u * s + v * t := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hu)
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hv)
  have hmix_le_const :
      u * min s x + v * min t x ≤ x := by
    calc
      u * min s x + v * min t x ≤ u * x + v * x := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (min_le_right _ _) hu)
          (mul_le_mul_of_nonneg_left (min_le_right _ _) hv)
      _ = x := by rw [← add_mul, huv, one_mul]
  have hmin :
      u * min s x + v * min t x ≤ min (u * s + v * t) x :=
    le_min hmix_le_linear hmix_le_const
  have hscaled := mul_le_mul_of_nonneg_left hmin ha
  convert hscaled using 1 <;> ring

theorem solution_expected_concave
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) (hf1 : 0 ≤ f 1) :
    ConcaveOn ℝ (Set.Ici 0) (fun s => expRevenue P X f p 1 s) := by
  let F : Ω → ℝ → ℝ := fun ω s => f 1 * min s (X 1 ω)
  have hpoint : ∀ᵐ ω ∂P,
      ConcaveOn ℝ (Set.Ici 0) (fun s : ℝ => F ω s) := by
    filter_upwards [] with ω
    exact solution_pointwise_concave (f 1) (X 1 ω) hf1
  have hslice : ∀ s ∈ Set.Ici (0 : ℝ), Integrable (fun ω => F ω s) P := by
    intro s hs
    simpa [F] using solution_integrable_truncated P X f hM hint s hf1
  have hconc : ConcaveOn ℝ (Set.Ici 0)
      (fun s : ℝ => ∫ ω, F ω s ∂P) :=
    MeasureTheory.integral_concaveOn_of_integrand_ae
      (convex_Ici (0 : ℝ)) hpoint hslice
  have hrev : (fun s : ℝ => expRevenue P X f p 1 s) =
      fun s => ∫ ω, F ω s ∂P := by
    funext s
    simp only [expRevenue, F]
    simp_rw [solution_revenue_one_min]
  rw [hrev]
  exact hconc

theorem solution_expected_affine_unit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) (hf1 : 0 ≤ f 1) :
    ∀ m : ℕ, ∃ a b : ℝ,
      (∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        expRevenue P X f p 1 s = a + b * s) ∧
      b = f 1 * P.real {ω | (m : ℝ) < X 1 ω} := by
  intro m
  obtain ⟨c, d, hc, hd, hdeq, haff⟩ :=
    solution_branchwise_affine_coefficients P X f hM hint hf1 m
  let F : Ω → ℝ → ℝ := fun ω s => f 1 * min s (X 1 ω)
  letI : IsProbabilityMeasure P := hM.isProb
  have hrev (s : ℝ) : expRevenue P X f p 1 s = ∫ ω, F ω s ∂P := by
    simp only [expRevenue, F]
    simp_rw [solution_revenue_one_min]
  refine ⟨∫ ω, c ω ∂P, ∫ ω, d ω ∂P, ?_⟩
  constructor
  · intro s hs
    have hpoint : ∀ᵐ ω ∂P, F ω s = c ω + d ω * s :=
      Filter.Eventually.of_forall (haff s hs)
    have hdc : Integrable (fun ω => d ω * s) P := hd.mul_const s
    calc
      expRevenue P X f p 1 s = ∫ ω, F ω s ∂P := hrev s
      _ = ∫ ω, c ω + d ω * s ∂P := integral_congr_ae hpoint
      _ = (∫ ω, c ω ∂P) + ∫ ω, d ω * s ∂P := integral_add hc hdc
      _ = (∫ ω, c ω ∂P) + (∫ ω, d ω ∂P) * s := by rw [integral_mul_const]
  · calc
      (∫ ω, d ω ∂P) = ∫ ω, (if (m : ℝ) < X 1 ω then f 1 else 0) ∂P := by
        rw [hdeq]
      _ = f 1 * P.real {ω | (m : ℝ) < X 1 ω} :=
        solution_branch_slope_integral P X f hM m

end NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) (hf1 : 0 ≤ f 1) :
    IsCLBI (expRevenue P X f p 1) ∧
      (∀ s, 0 ≤ s →
        HasDerivWithinAt (expRevenue P X f p 1) (f 1 * P.real {ω | s < X 1 ω}) (Set.Ici s) s) ∧
      (∀ s, 0 < s →
        HasDerivWithinAt (expRevenue P X f p 1) (f 1 * P.real {ω | s ≤ X 1 ω}) (Set.Iic s) s) := by
  have hclbi : IsCLBI (expRevenue P X f p 1) := by
    change ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p 1) ∧
      ∀ m : ℕ, ∃ a b : ℝ, ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        expRevenue P X f p 1 s = a + b * s
    constructor
    · exact solution_expected_concave P X f p hM hint hf1
    · intro m
      have h_expected_affine_unit :=
        solution_expected_affine_unit P X f p hM hint hf1 m
      obtain ⟨a, b, haff, _hslope⟩ := h_expected_affine_unit
      exact ⟨a, b, haff⟩
  refine ⟨hclbi, ?_, ?_⟩
  · intro s hs
    obtain ⟨m, hlo, hhi⟩ := solution_right_interval hs
    have h_expected_affine_unit_right :=
      solution_expected_affine_unit P X f p hM hint hf1 m
    obtain ⟨a, b, haff, hslope_right⟩ := h_expected_affine_unit_right
    have hder := solution_right_affine_derivative hlo hhi haff
    have hevent := solution_right_tail_event X hint hlo hhi
    have hslope' : b = f 1 * P.real {ω | s < X 1 ω} := by
      rw [hslope_right, hevent]
    rw [hslope'] at hder
    exact hder
  · intro s hs
    obtain ⟨m, hmpos, hlo, hhi⟩ := solution_left_interval hs
    have hmadd : m - 1 + 1 = m :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmpos))
    have hmcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
      exact_mod_cast hmadd
    have hmcast_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      linarith
    have h_expected_affine_unit_left :=
      solution_expected_affine_unit P X f p hM hint hf1 (m - 1)
    obtain ⟨a, b, haff, hslope_left⟩ := h_expected_affine_unit_left
    have haff_left : ∀ t ∈ Set.Icc ((m : ℝ) - 1) (m : ℝ),
        expRevenue P X f p 1 t = a + b * t := by
      intro t ht
      have ht' : t ∈ Set.Icc ((m - 1 : ℕ) : ℝ)
          (((m - 1 : ℕ) : ℝ) + 1) := by
        simpa [hmcast_sub, hmcast] using ht
      exact haff t ht'
    have hder := solution_left_affine_derivative hlo hhi haff_left
    have hevent := solution_left_tail_event X hint hlo hhi
    rw [← hmcast_sub] at hevent
    have hslope' : b = f 1 * P.real {ω | s ≤ X 1 ω} := by
      rw [hslope_left, hevent]
    rw [hslope'] at hder
    exact hder
