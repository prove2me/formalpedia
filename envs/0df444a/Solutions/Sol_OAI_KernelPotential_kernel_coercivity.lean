-- Prove2me | solution 1 for OAI.KernelPotential.kernel_coercivity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:02:22.110594+00:00
-- url     : https://prove2.me/submissions/8056e65d-e832-41b4-a532-fd16f24029c7

import Mathlib
import Definitions.Def_GaussianInformation_003
import Definitions.Def_OAIQWRLC001

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Covers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Geometry
section Cover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma card_separated_le (s : Finset E) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hs : ∀ c ∈ s, ‖c‖ ≤ R)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ ((2 * R + δ) / δ) ^ Module.finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hsmall : 0 < δ / 2 := by positivity
  have hlarge : 0 < R + δ / 2 := by positivity
  let A := ⋃ c ∈ s, ball c (δ / 2)
  have hdisj : (s : Set E).PairwiseDisjoint (fun c => ball c (δ / 2)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert hsep c hc d hd hcd using 1
    ring
  have hsub : A ⊆ ball (0 : E) (R + δ / 2) := by
    refine iUnion₂_subset fun x hx => ball_subset_ball' ?_
    rw [dist_zero_right]
    linarith [hs x hx]
  have hb : (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2)^Module.finrank ℝ E) *
       μ (ball 0 1) ≤ ENNReal.ofReal ((R + δ / 2)^Module.finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hsmall, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball 0 (R + δ / 2)) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hlarge
  have hb' := (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ (0 : E) zero_lt_one).ne'
    measure_ball_lt_top.ne).mp hb
  have hbR : (s.card : ℝ) * (δ / 2)^Module.finrank ℝ E ≤
      (R + δ / 2)^Module.finrank ℝ E := by
    simpa [ENNReal.toReal_ofReal (pow_nonneg hsmall.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hlarge.le _) hb'
  calc
    (s.card : ℝ) ≤ (R + δ / 2)^Module.finrank ℝ E / (δ / 2)^Module.finrank ℝ E :=
      (le_div_iff₀ (pow_pos hsmall _)).mpr hbR
    _ = ((2 * R + δ) / δ)^Module.finrank ℝ E := by
      rw [← div_pow]
      congr 1
      field_simp

lemma exists_ball_cover_card_le {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ s : Finset E, (∀ c ∈ s, ‖c‖ ≤ R) ∧
      (∀ x : E, ‖x‖ ≤ R → ∃ c ∈ s, dist x c ≤ δ) ∧
      (s.card : ℝ) ≤ ((2 * R + δ) / δ)^Module.finrank ℝ E := by
  classical
  let ε : ℝ≥0 := ⟨δ, hδ.le⟩
  let A := closedBall (0 : E) R
  have hεpos : 0 < ε := hδ
  have hε : ε ≠ 0 := ne_of_gt hεpos
  obtain ⟨N, _, hNfin, hNcov⟩ := Metric.exists_finite_isCover_of_isCompact
    (s := A) (ε := ε / 2) (by positivity) (isCompact_closedBall _ _)
  have hp : Metric.packingNumber ε A < ⊤ := by
    calc
      _ = Metric.packingNumber (2 * (ε / 2)) A := by congr 1; ring
      _ ≤ Metric.externalCoveringNumber (ε / 2) A :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ N.encard := hNcov.externalCoveringNumber_le_encard
      _ < ⊤ := hNfin.encard_lt_top
  let S := Metric.maximalSeparatedSet ε A
  have hSfin : S.Finite := Set.encard_lt_top_iff.mp (by
    change (Metric.maximalSeparatedSet ε A).encard < ⊤
    rw [Metric.encard_maximalSeparatedSet hp.ne]
    exact hp)
  have hSsub : ∀ c ∈ hSfin.toFinset, ‖c‖ ≤ R := by
    intro c hc
    have : c ∈ S := by simpa using hc
    simpa [A] using (Metric.maximalSeparatedSet_subset this)
  refine ⟨hSfin.toFinset, hSsub, ?_, card_separated_le _ hR hδ hSsub ?_⟩
  · intro x hx
    have hcov := Metric.isCover_iff_subset_iUnion_closedBall.mp
      (Metric.isCover_maximalSeparatedSet hp.ne)
    have hm : x ∈ A := by simpa [A] using hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hcov hm)
    exact ⟨c, by simpa using hc, hxc⟩
  · intro c hc d hd hcd
    have hs := Metric.isSeparated_maximalSeparatedSet (ε := ε) (A := A)
      (by simpa using hc) (by simpa using hd) hcd
    have ht := ENNReal.toReal_mono (edist_ne_top c d) hs.le
    change δ ≤ (edist c d).toReal at ht
    simpa [ε, edist_dist, dist_eq_norm] using ht

end Cover

section PlaneCover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_affine_tube_cover (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ s : Finset E,
      (∀ x : E, ‖x‖ ≤ R → infDist x (V : Set E) ≤ δ → ∃ c ∈ s, dist x c ≤ 2 * δ) ∧
      (s.card : ℝ) ≤ ((4 * R + 5 * δ) / δ)^Module.finrank ℝ V.direction := by
  classical
  by_cases hempty : {x : E | ‖x‖ ≤ R ∧ infDist x (V : Set E) ≤ δ}.Nonempty
  · obtain ⟨x₀, hx₀n, hx₀d⟩ := hempty
    obtain ⟨v₀, hv₀V, hv₀d⟩ := V.closed_of_finiteDimensional.exists_infDist_eq_dist hV x₀
    have hn₀ : ‖v₀‖ ≤ R + δ := by
      have ht := dist_triangle v₀ x₀ 0
      rw [dist_zero_right, dist_zero_right, dist_comm v₀ x₀, ← hv₀d] at ht
      linarith
    obtain ⟨s, _, hcover, hcard⟩ := exists_ball_cover_card_le (E := V.direction)
      (R := 2 * (R + δ)) (δ := δ) (by positivity) hδ
    let f : V.direction ↪ E := ⟨fun v => (v : E) + v₀, by
      intro v w h
      exact Subtype.ext (add_right_cancel h)⟩
    refine ⟨s.map f, ?_, ?_⟩
    · intro x hxn hxd
      obtain ⟨v, hvV, hvd⟩ := V.closed_of_finiteDimensional.exists_infDist_eq_dist hV x
      have hnv : ‖v‖ ≤ R + δ := by
        have ht := dist_triangle v x 0
        rw [dist_zero_right, dist_zero_right, dist_comm v x, ← hvd] at ht
        linarith
      let u : V.direction := ⟨v - v₀, V.vsub_mem_direction hvV hv₀V⟩
      have hnu : ‖u‖ ≤ 2 * (R + δ) := by
        change ‖v - v₀‖ ≤ _
        exact (norm_sub_le v v₀).trans (by linarith)
      obtain ⟨a, ha, hu⟩ := hcover u hnu
      refine ⟨f a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
      have he : dist v (f a) = dist u a := by
        rw [dist_eq_norm, dist_eq_norm]
        change ‖v - ((a : E) + v₀)‖ = ‖(v - v₀) - (a : E)‖
        congr 1
        abel
      calc
        dist x (f a) ≤ dist x v + dist v (f a) := dist_triangle _ _ _
        _ ≤ δ + δ := add_le_add (hvd ▸ hxd) (he ▸ hu)
        _ = 2 * δ := by ring
    · simpa only [Finset.card_map, show 2 * (2 * (R + δ)) + δ = 4 * R + 5 * δ by ring] using hcard
  · refine ⟨∅, ?_, ?_⟩
    · intro x hxn hxd
      exact (hempty ⟨x, hxn, hxd⟩).elim
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity

end PlaneCover

end Geometry
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_SmallBalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Geometry
lemma inv_pow_dyadic_majorant (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (hk : 0 < k) :
    ENNReal.ofReal (x⁻¹ ^ k) ≤ 1 + ∑' j : ℕ,
      ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))) x := by
  by_cases hx0 : x = 0
  · simp [hx0, hk.ne']
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  by_cases hx1 : 1 ≤ x
  · have hle : ENNReal.ofReal (x⁻¹ ^ k) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_one₀ (inv_nonneg.mpr hx) ((inv_le_one₀ hxpos).mpr hx1)
    exact hle.trans (le_add_right le_rfl)
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near_of_lt_one hxpos
    (le_of_not_ge hx1) (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hbound : x⁻¹ ^ k ≤ (2 : ℝ) ^ ((j + 1) * k) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (inv_nonneg.mpr hx)
    have hinv := (inv_le_inv₀ hxpos (pow_pos (by norm_num : 0 < (1 / 2 : ℝ)) (j+1))).mpr hj.le
    simpa only [one_div, inv_pow, inv_inv] using hinv
  calc
    ENNReal.ofReal (x⁻¹ ^ k) ≤ ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k)) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))) x := by
      simp only [Set.indicator, Set.mem_ofPred_eq, hj', ite_true]
    _ ≤ ∑' j : ℕ, ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))) x :=
      ENNReal.le_tsum (f := fun index : ℕ =>
        ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ index}).indicator
          (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((index + 1) * k))) x) j
    _ ≤ 1 + ∑' j : ℕ, ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))) x := le_add_left le_rfl

lemma dyadic_weight_product (j k : ℕ) :
    (2 : ℝ) ^ ((j + 1) * k) * (1 / 2 : ℝ) ^ ((k + 1) * j) =
      (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ j := by
  simp only [Nat.add_mul, one_mul, pow_add, one_div, inv_pow]
  have hpow : (2 : ℝ) ^ (k * j) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Nat.mul_comm j k]
  field_simp

theorem inverseMoment_of_dyadic_tails {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (D : α → ℝ) (hD : Measurable D) (hD0 : ∀ x, 0 ≤ D x)
    (k : ℕ) (hk : 0 < k) (A : ℝ≥0∞)
    (htail : ∀ j : ℕ, μ {x | D x ≤ (1 / 2 : ℝ) ^ j} ≤
      A * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((k + 1) * j))) :
    (∫⁻ x, ENNReal.ofReal ((D x)⁻¹ ^ k) ∂μ) ≤
      μ univ + A * ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) := by
  let S : ℕ → Set α := fun j => {x | D x ≤ (1 / 2 : ℝ) ^ j}
  let w : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))
  have hS : ∀ j, MeasurableSet (S j) := fun j => measurableSet_le hD measurable_const
  have hmeas : ∀ j, Measurable ((S j).indicator (fun _ => w j)) :=
    fun j => measurable_const.indicator (hS j)
  calc
    (∫⁻ x, ENNReal.ofReal ((D x)⁻¹ ^ k) ∂μ) ≤
        ∫⁻ x, (1 + ∑' j, (S j).indicator (fun _ => w j) x) ∂μ := by
      apply lintegral_mono
      intro x
      simpa only [S, w, Set.indicator, Set.mem_ofPred_eq] using
        inv_pow_dyadic_majorant (D x) (hD0 x) k hk
    _ = μ univ + ∑' j, w j * μ (S j) := by
      rw [lintegral_add_left measurable_const,
        lintegral_tsum (fun j => (hmeas j).aemeasurable)]
      simp only [lintegral_const, one_mul, lintegral_indicator (hS _), Measure.restrict_apply_univ]
    _ ≤ μ univ + ∑' j, w j * (A * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((k + 1) * j))) := by
      gcongr with j
      exact htail j
    _ = μ univ + ∑' j, (A * ENNReal.ofReal ((2 : ℝ) ^ k)) * ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
      congr 1
      apply tsum_congr
      intro j
      dsimp [w]
      rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity), dyadic_weight_product,
        ENNReal.ofReal_mul (by positivity)]
      ac_rfl
    _ = μ univ + A * ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) := by
      simp only [ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 2 : ℝ)), ENNReal.tsum_mul_left,
        ENNReal.tsum_geometric]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div, ENNReal.one_sub_inv_two,
        inv_inv, pow_succ, ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k),
        ENNReal.ofReal_ofNat, mul_assoc]

theorem zeroSet_null_of_dyadic_tails {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (D : α → ℝ) (k : ℕ) (A : ℝ≥0∞) (hA : A ≠ ∞)
    (htail : ∀ j : ℕ, μ {x | D x ≤ (1 / 2 : ℝ) ^ j} ≤
      A * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((k + 1) * j))) :
    μ {x | D x = 0} = 0 := by
  have hr : ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have ht := ENNReal.Tendsto.const_mul
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr hA)
  apply le_antisymm _ bot_le
  change μ {x | D x = 0} ≤ (0 : ℝ≥0∞)
  apply ge_of_tendsto' (show Tendsto
    (fun j : ℕ => A * ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) ^ j) atTop (𝓝 (0 : ℝ≥0∞)) from
    by simpa only [mul_zero] using ht)
  intro j
  calc
    μ {x | D x = 0} ≤ μ {x | D x ≤ (1 / 2 : ℝ) ^ j} := by
      apply measure_mono
      intro x hx
      simp only [mem_ofPred_eq] at hx ⊢
      rw [hx]
      positivity
    _ ≤ A * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((k + 1) * j)) := htail j
    _ = A * ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) ^ j := by
      rw [pow_mul, ENNReal.ofReal_pow (by positivity)]

end Geometry
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_MixedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Geometry
section MixedGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma tube_ball_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) {a k : ℕ} {B R t : ℝ}
    (hB : 0 ≤ B) (hR : 0 < R) (ht : 0 < t) (ht1 : t ≤ 1)
    (hball : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (B*r^a))
    (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    (hdim : Module.finrank ℝ V.direction + (k+1) ≤ a) :
    μ {x | ‖x‖ ≤ R ∧ infDist x (V : Set E) ≤ R*t} ≤
      ENNReal.ofReal (B * 9^(Module.finrank ℝ V.direction) * 3^a * R^a * t^(k+1)) := by
  classical
  let j := Module.finrank ℝ V.direction
  obtain ⟨s, hs, hcard⟩ := exists_affine_tube_cover V hV hR.le (mul_pos hR ht)
  have hsub : {x | ‖x‖ ≤ R ∧ infDist x (V : Set E) ≤ R*t} ⊆
      ⋃ c ∈ s, ball c (3*(R*t)) := by
    intro x hx
    obtain ⟨c,hc,hxc⟩ := hs x hx.1 hx.2
    exact mem_iUnion₂.mpr ⟨c,hc,lt_of_le_of_lt hxc (by nlinarith)⟩
  have hc : (s.card : ℝ) ≤ (9/t)^j := by
    apply hcard.trans
    apply pow_le_pow_left₀ (by positivity)
    calc
      (4*R+5*(R*t))/(R*t) ≤ (9*R)/(R*t) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left ht1 hR.le]
      _ = 9/t := by field_simp
  have halg : (9/t)^j * (B*(3*(R*t))^a) ≤
      B*9^j*3^a*R^a*t^(k+1) := by
    obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le hdim
    have htj : t^j ≠ 0 := pow_ne_zero _ ht.ne'
    have hte : t^e ≤ 1 := pow_le_one₀ ht.le ht1
    have heq : (9/t)^j * (B*(3*(R*t))^a) =
        (B*9^j*3^a*R^a*t^(k+1))*t^e := by
      simp only [he, j, mul_pow, div_pow, pow_add]
      field_simp
    rw [heq]
    exact mul_le_of_le_one_right (by positivity) hte

  calc
    _ ≤ ∑ c ∈ s, μ (ball c (3*(R*t))) := (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _c ∈ s, ENNReal.ofReal (B*(3*(R*t))^a) := by gcongr; exact hball _ _ (by positivity)
    _ = ENNReal.ofReal ((s.card:ℝ)*(B*(3*(R*t))^a)) := by
      simp [ENNReal.ofReal_mul, hB]
    _ ≤ ENNReal.ofReal (B*9^j*3^a*R^a*t^(k+1)) := by
      apply ENNReal.ofReal_le_ofReal
      exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans halg

lemma inverseMoment_extended_of_tails {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (D : E → ℝ)
    (hD : Measurable D) (hD0 : ∀ x, 0 ≤ D x) (k : ℕ) (hk : 0 < k)
    (A : ℝ≥0∞) (hA : A ≠ ∞)
    (htail : ∀ j : ℕ, μ {x | D x ≤ (1/2:ℝ)^j} ≤
      A * ENNReal.ofReal ((1/2:ℝ)^((k+1)*j))) :
    (∫⁻ x, (ENNReal.ofReal (D x))⁻¹^k ∂μ) ≤
      μ univ + A*ENNReal.ofReal ((2:ℝ)^(k+1)) := by
  have hz : ∀ᵐ x ∂μ, D x ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using zeroSet_null_of_dyadic_tails μ D k A hA htail
  have heq : (fun x => (ENNReal.ofReal (D x))⁻¹^k) =ᵐ[μ]
      (fun x => ENNReal.ofReal ((D x)⁻¹^k)) := by
    filter_upwards [hz] with x hx
    rw [ENNReal.ofReal_pow (inv_nonneg.mpr (hD0 x)),
      ENNReal.ofReal_inv_of_pos (lt_of_le_of_ne (hD0 x) hx.symm)]
  rw [lintegral_congr_ae heq]
  exact inverseMoment_of_dyadic_tails μ D hD hD0 k hk A htail

end MixedGeometry

end Geometry

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Sphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Sphere
open KernelPotential.Geometry

lemma unit_ball_pos (d : ℕ) : 0 < volume (ball (0 : Ambient d) 1) :=
  measure_ball_pos volume _ zero_lt_one

lemma unit_ball_ne_top (d : ℕ) : volume (ball (0 : Ambient d) 1) ≠ ∞ :=
  measure_ball_lt_top.ne

lemma unitVolume_ball (d : ℕ) (z : Ambient d) {r : ℝ} (hr : 0 < r) :
    unitVolume d (ball z r) = ENNReal.ofReal (r^d) := by
  rw [unitVolume,Measure.smul_apply,smul_eq_mul,volume.addHaar_ball_of_pos z hr]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [mul_left_comm, ENNReal.inv_mul_cancel (unit_ball_pos d).ne' (unit_ball_ne_top d),mul_one]

lemma measurable_radial (d : ℕ) : Measurable (@radial d) :=
  measurable_norm.inv.smul measurable_id

lemma sphereProbability_eq (d : ℕ) :
    sphereProbability d = ((unitVolume d).restrict (ball 0 1)).map radial := by
  simp only [sphereProbability,unitVolume,Measure.restrict_smul]

instance sphereProbability_probability (d : ℕ) : IsProbabilityMeasure (sphereProbability d) := by
  rw [sphereProbability_eq]
  have : IsProbabilityMeasure ((unitVolume d).restrict (ball 0 1)) := by
    constructor
    simp only [Measure.restrict_apply_univ, unitVolume_ball d _ zero_lt_one, one_pow, ENNReal.ofReal_one]
  exact Measure.isProbabilityMeasure_map_iff (measurable_radial d).aemeasurable |>.mpr inferInstance

lemma radial_rescale {d : ℕ} (x : Ambient d) : ‖x‖ • radial x = x := by
  by_cases hx : x = 0
  · simp [hx,radial]
  · simp only [radial,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]

lemma norm_radial {d : ℕ} (x : Ambient d) (hx : x ≠ 0) : ‖radial x‖ = 1 := by
  rw [radial,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma ae_unit_norm {d : ℕ} (hd : 0 < d) : ∀ᵐ s ∂sphereProbability d, ‖s‖ = 1 := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have : Nontrivial (Ambient d) := inferInstance
  rw [sphereProbability_eq]
  apply (ae_map_iff (measurable_radial d).aemeasurable (measurableSet_eq_fun measurable_norm measurable_const)).mpr
  have hz : ∀ᵐ x ∂((unitVolume d).restrict (ball 0 1)), x ≠ 0 := by
    have ha : ((unitVolume d).restrict (ball 0 1)) ≪ (volume : Measure (Ambient d)) :=
      Measure.absolutelyContinuous_restrict.trans Measure.smul_absolutelyContinuous
    apply ha.ae_le
    exact ae_iff.mpr (by simp)
  filter_upwards [hz] with x hx
  exact norm_radial x hx

lemma singleton_span_finrank_le {d : ℕ} (z : Ambient d) :
    Module.finrank ℝ (Submodule.span ℝ ({z} : Set (Ambient d))) ≤ 1 := by
  by_cases hz : z = 0
  · rw [hz,Submodule.span_singleton_eq_bot.mpr rfl,finrank_bot]
    omega
  · exact (finrank_span_singleton hz).le

lemma preimage_cap_tube {d : ℕ} (z : Ambient d) {r : ℝ} (_hr : 0 < r) :
    radial ⁻¹' ball z r ∩ ball 0 1 ⊆
      {x | ‖x‖ ≤ 1 ∧ infDist x (Submodule.span ℝ ({z} : Set (Ambient d)) : Set (Ambient d)) ≤ r} := by
  intro x hx
  have hxn : ‖x‖ < 1 := by simpa using hx.2
  have hxz : dist (radial x) z < r := hx.1
  refine ⟨hxn.le, ?_⟩
  have hz : ‖x‖ • z ∈ Submodule.span ℝ ({z} : Set (Ambient d)) :=
    Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  apply (infDist_le_dist_of_mem hz).trans
  calc
    dist x (‖x‖ • z) = ‖x‖ * dist (radial x) z := by
      calc
        _ = dist (‖x‖ • radial x) (‖x‖ • z) := congrArg (fun y => dist y (‖x‖ • z)) (radial_rescale x).symm
        _ = _ := by rw [dist_smul₀,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    _ ≤ 1*r := mul_le_mul hxn.le hxz.le dist_nonneg (by norm_num)
    _ = r := one_mul _

lemma cap_bound {d : ℕ} (hd : 2 ≤ d) (z : Ambient d) {r : ℝ} (hr : 0 < r) :
    sphereProbability d (ball z r) ≤ ENNReal.ofReal ((9*3^d:ℝ)*r^(d-1)) := by
  by_cases hr1 : r ≤ 1
  · let V : AffineSubspace ℝ (Ambient d) := (Submodule.span ℝ ({z} : Set (Ambient d))).toAffineSubspace
    have hdim : Module.finrank ℝ V.direction + ((d-2)+1) ≤ d := by
      have hz := singleton_span_finrank_le z
      change Module.finrank ℝ (Submodule.span ℝ ({z} : Set (Ambient d))).toAffineSubspace.direction + _ ≤ d
      rw [Submodule.toAffineSubspace_direction]
      omega
    have ht := tube_ball_bound (unitVolume d) (a := d) (k := d-2) (B := 1) (R := 1)
      (by norm_num) (by norm_num) hr hr1 (fun z r hr => by simpa using (unitVolume_ball d z hr).le)
      V ⟨0,Submodule.zero_mem _⟩ hdim
    calc
      _ = unitVolume d (radial ⁻¹' ball z r ∩ ball 0 1) := by
        rw [sphereProbability_eq,Measure.map_apply (measurable_radial d) measurableSet_ball,
          Measure.restrict_apply ((measurable_radial d) measurableSet_ball)]
      _ ≤ unitVolume d {x | ‖x‖ ≤ 1 ∧ infDist x (V : Set (Ambient d)) ≤ 1*r} :=
        measure_mono (by
          change radial ⁻¹' ball z r ∩ ball 0 1 ⊆ {x | ‖x‖ ≤ 1 ∧
            infDist x (Submodule.span ℝ ({z} : Set (Ambient d)) : Set (Ambient d)) ≤ 1*r}
          simpa only [one_mul] using preimage_cap_tube z hr)
      _ ≤ ENNReal.ofReal (1 * 9^(Module.finrank ℝ V.direction) * 3^d * 1^d * r^((d-2)+1)) := ht
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [show (d-2)+1=d-1 by omega]
        simp only [one_mul,one_pow,mul_one]
        gcongr
        calc
          (9:ℝ)^(Module.finrank ℝ V.direction) ≤ 9^1 := by
            apply pow_le_pow_right₀ (by norm_num)
            change Module.finrank ℝ (Submodule.span ℝ ({z} : Set (Ambient d))).toAffineSubspace.direction ≤ 1
            rw [Submodule.toAffineSubspace_direction]
            exact singleton_span_finrank_le z
          _ = 9 := pow_one _
  · apply (prob_le_one (μ := sphereProbability d)).trans
    apply ENNReal.one_le_ofReal.mpr
    have h3 : (1:ℝ) ≤ 3^d := one_le_pow₀ (by norm_num)
    have hrp : (1:ℝ) ≤ r^(d-1) := one_le_pow₀ (by linarith : (1:ℝ) ≤ r)
    nlinarith

end Sphere

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace EntropySupport

lemma continuous_xlog : Continuous xlog := Real.continuous_mul_log
lemma xlog_zero : xlog 0 = 0 := by simp [xlog]

lemma xlog_lower_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    xlog y + (Real.log y+1)*(x-y) ≤ xlog x := by
  have h := Real.self_sub_one_le_mul_log (div_nonneg hx hy.le)
  by_cases hx0 : x = 0
  · simp only [hx0, xlog]
    nlinarith
  rw [Real.log_div hx0 hy.ne'] at h
  have H := mul_le_mul_of_nonneg_left h hy.le
  dsimp [xlog]
  field_simp at H
  nlinarith

lemma integrable_bounded_measurable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ := by
  apply Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, Function.comp_def] using hC x)

lemma integrable_xlog_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {M : ℝ} (hfM : ∀ x,f x ≤ M) : Integrable (fun x => xlog (f x)) μ := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc (a := (0:ℝ)) (b := M)).image continuous_xlog).isBounded.exists_norm_le
  apply integrable_bounded_measurable μ _ (continuous_xlog.measurable.comp hf)
  intro x
  simpa only [Real.norm_eq_abs,Function.comp_def] using hC _ (Set.mem_image_of_mem _ ⟨hf0 x,hfM x⟩)

lemma klDiv_withDensity_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {M : ℝ} (hfM : ∀ x,f x ≤ M)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))] :
    InformationTheory.klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ =
      ENNReal.ofReal (∫ x,xlog (f x) ∂μ) := by
  have hif := integrable_bounded_measurable μ f hf (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfM x)
  have hix := integrable_xlog_bounded μ f hf hf0 hfM
  have hib : Integrable (fun x => InformationTheory.klFun (f x)) μ :=
    (hix.add (integrable_const 1)).sub hif
  have hfint : ∫ x,f x ∂μ = 1 := by
    have h := measure_univ (μ := μ.withDensity (fun x => ENNReal.ofReal (f x)))
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hif (ae_of_all _ hf0)] at h
    exact (ENNReal.ofReal_eq_one.mp h)
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous μ _)]
  have hrn := Measure.rnDeriv_withDensity μ hf.ennreal_ofReal
  have he : (fun x => ENNReal.ofReal (InformationTheory.klFun (((μ.withDensity
      (fun x => ENNReal.ofReal (f x))).rnDeriv μ x).toReal))) =ᵐ[μ]
      (fun x => ENNReal.ofReal (InformationTheory.klFun (f x))) := by
    filter_upwards [hrn] with x hx
    rw [hx,ENNReal.toReal_ofReal (hf0 x)]
  rw [lintegral_congr_ae he,← ofReal_integral_eq_lintegral_ofReal hib
    (ae_of_all _ (fun x => InformationTheory.klFun_nonneg (hf0 x)))]
  congr 1
  change (∫ x,xlog (f x)+1-f x ∂μ) = _
  rw [integral_sub (f := fun x => xlog (f x)+1) (hix.add (integrable_const 1)) hif,
    integral_add hix (integrable_const 1),hfint]
  simp

end EntropySupport

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Coercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Coercivity
open _root_.OAI.KernelPotential.Geometry Sphere

lemma inverse_kernel_bound {d n q : ℕ} (μ : Measure (Ambient d)) [IsProbabilityMeasure μ]
    {C : ℝ} (hC : 0 ≤ C) (hq : 0 < q) (hqn : q+1 ≤ n)
    (hball : ∀ s r, 0 < r → μ (ball s r) ≤ ENNReal.ofReal (C*r^n)) (s : Ambient d) :
    (∫⁻ u, (ENNReal.ofReal ‖u-s‖)⁻¹^q ∂μ) ≤ ENNReal.ofReal (1+C*2^(n+q+1)) := by
  have ht : ∀ j : ℕ, μ {u | ‖u-s‖ ≤ (1/2:ℝ)^j} ≤
      ENNReal.ofReal (C*2^n)*ENNReal.ofReal ((1/2:ℝ)^((q+1)*j)) := by
    intro j
    calc
      _ ≤ μ (ball s (2*(1/2:ℝ)^j)) := measure_mono (by
        intro u hu
        change dist u s < _
        rw [dist_eq_norm]
        have hp : 0 < (1/2:ℝ)^j := by positivity
        change ‖u-s‖ ≤ (1/2:ℝ)^j at hu
        linarith)
      _ ≤ ENNReal.ofReal (C*(2*(1/2:ℝ)^j)^n) := hball _ _ (by positivity)
      _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_pow, ← mul_assoc, Nat.mul_comm (q+1) j, pow_mul]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_of_le_one (by positivity : 0 ≤ (1/2:ℝ)^j) (pow_le_one₀ (by norm_num) (by norm_num)) hqn
  have h := inverseMoment_extended_of_tails μ (fun u => ‖u-s‖)
    (measurable_id.sub_const s).norm (fun u => norm_nonneg _) q hq
    (ENNReal.ofReal (C*2^n)) ENNReal.ofReal_ne_top ht
  apply h.trans_eq
  rw [measure_univ, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  congr 1
  rw [mul_assoc, ← pow_add]
  congr 3

lemma integral_square_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x,f x ∂μ)^2 ≤ ∫⁻ x,(f x)^2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (p := (2:ℝ)) (q := (2:ℝ)) (Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩)
    hf.aemeasurable (measurable_const (a := (1:ℝ≥0∞))).aemeasurable
  simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_one,measure_univ] at h
  have H := pow_le_pow_left₀ zero_le h 2
  simpa only [← ENNReal.rpow_natCast, Nat.cast_ofNat, ← ENNReal.rpow_mul,
    show (1/(2:ℝ))*(2:ℝ)=1 by norm_num,ENNReal.rpow_one] using H

lemma measurable_kernel {d q : ℕ} :
    Measurable (fun x : Ambient d × Ambient d => (ENNReal.ofReal ‖x.1-x.2‖)⁻¹^q) :=
  ((measurable_fst.sub measurable_snd).norm.ennreal_ofReal.inv).pow_const q

lemma measurable_J {d : ℕ} (ν : Measure (Ambient d)) [SFinite ν] : Measurable (J ν) := by
  unfold J
  apply Measurable.lintegral_prod_right
  exact ((measurable_snd.sub measurable_fst).norm.ennreal_ofReal.inv).pow_const _

lemma J_square_integral {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] :
    (∫⁻ s,(J ν s)^2 ∂sphereProbability d) ≤
      ENNReal.ofReal (1+(9*3^d:ℝ)*2^((d-1)+4*(d/16)+1)) := by
  have hk : 0 < d/16 := Nat.div_pos (by omega) (by norm_num)
  calc
    _ ≤ ∫⁻ s,∫⁻ u, ((ENNReal.ofReal ‖u-s‖)⁻¹^(2*(d/16)))^2 ∂ν ∂sphereProbability d := by
      apply lintegral_mono
      intro s
      exact integral_square_le ν _ (((measurable_id.sub_const s).norm.ennreal_ofReal.inv).pow_const _)
    _ = ∫⁻ u,∫⁻ s, (ENNReal.ofReal ‖u-s‖)⁻¹^(4*(d/16)) ∂sphereProbability d ∂ν := by
      simp_rw [← pow_mul, show 2*(d/16)*2=4*(d/16) by omega]
      exact lintegral_lintegral_swap (measurable_kernel.comp measurable_swap).aemeasurable
    _ ≤ ∫⁻ u, ENNReal.ofReal (1+(9*3^d:ℝ)*2^((d-1)+4*(d/16)+1)) ∂ν := by
      apply lintegral_mono
      intro u
      simp_rw [norm_sub_rev u]
      exact inverse_kernel_bound (sphereProbability d) (by positivity) (by omega)
        (by omega) (fun s r hr => cap_bound (by omega) s hr) u
    _ = _ := by simp

lemma bounded_density_representation {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • μ) :
    ∃ f : α → ℝ, Measurable f ∧ (∀ x,0 ≤ f x) ∧ (∀ x,f x ≤ H) ∧
      ν = μ.withDensity (fun x => ENNReal.ofReal (f x)) := by
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
  have hr : ν.rnDeriv μ ≤ᵐ[μ] fun _ => ENNReal.ofReal H := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν μ)
    intro s hs _
    calc
      _ ≤ ν s := Measure.setLIntegral_rnDeriv_le s
      _ ≤ (ENNReal.ofReal H • μ) s := hν s
      _ = _ := by simp [Measure.smul_apply]
  let f : α → ℝ := fun x => min H (ν.rnDeriv μ x).toReal
  refine ⟨f,measurable_const.min (Measure.measurable_rnDeriv ν μ).ennreal_toReal,
    fun x => le_min hH.le ENNReal.toReal_nonneg,fun x => min_le_left _ _,?_⟩
  rw [← Measure.withDensity_rnDeriv_eq ν μ hac]
  apply withDensity_congr_ae
  filter_upwards [hr] with x hx
  dsimp [f]
  have hxt : ν.rnDeriv μ x ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
  have hxH : (ν.rnDeriv μ x).toReal ≤ H := by
    exact (ENNReal.toReal_le_toReal hxt ENNReal.ofReal_ne_top).mpr hx |>.trans_eq (ENNReal.toReal_ofReal hH.le)
  rw [min_eq_right hxH, ENNReal.ofReal_toReal hxt]

lemma bounded_J {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) :
    J ν s ≤ ENNReal.ofReal (H*(1+(9*3^d:ℝ)*2^((d-1)+2*(d/16)+1))) := by
  have hk : 0 < d/16 := Nat.div_pos (by omega) (by norm_num)
  calc
    J ν s ≤ ∫⁻ u,(ENNReal.ofReal ‖u-s‖)⁻¹^(2*(d/16)) ∂(ENNReal.ofReal H • sphereProbability d) :=
      lintegral_mono' hν (le_refl _)
    _ = ENNReal.ofReal H * J (sphereProbability d) s := by rw [J,lintegral_smul_measure,smul_eq_mul]
    _ ≤ ENNReal.ofReal H * ENNReal.ofReal (1+(9*3^d:ℝ)*2^((d-1)+2*(d/16)+1)) := by
      gcongr
      exact inverse_kernel_bound (sphereProbability d) (by positivity) (by omega)
        (by omega) (fun s r hr => cap_bound (by omega) s hr) s
    _ = _ := (ENNReal.ofReal_mul hH.le).symm

lemma lower_J_on_sphere {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ u ∂ν, ‖u‖=1) (s : Ambient d) (hs : ‖s‖=1) :
    ENNReal.ofReal ((1/2:ℝ)^(2*(d/16))) ≤ J ν s := by
  calc
    _ = ∫⁻ u, ENNReal.ofReal ((1/2:ℝ)^(2*(d/16))) ∂ν := by simp
    _ ≤ J ν s := by
      apply lintegral_mono_ae
      filter_upwards [hν] with u hu
      have hn : ‖u-s‖ ≤ 2 := by calc
        ‖u-s‖ ≤ ‖u‖+‖s‖ := norm_sub_le _ _
        _ = 2 := by rw [hu,hs]; norm_num
      rw [ENNReal.ofReal_pow (by norm_num),show ENNReal.ofReal (1/2:ℝ)=(ENNReal.ofReal (2:ℝ))⁻¹ by rw [one_div,ENNReal.ofReal_inv_of_pos (by norm_num)]]
      exact pow_le_pow_left₀ zero_le (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hn)) _

lemma integrable_log_of_bounds {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    {a b : ℝ} (ha : 0 < a)
    (hbound : ∀ᵐ x ∂μ, a ≤ f x ∧ f x ≤ b) : Integrable (fun x => Real.log (f x)) μ := by
  apply Integrable.mono' (integrable_const (|Real.log a|+|Real.log b|)) hf.log.aestronglyMeasurable
  filter_upwards [hbound] with x hx
  have hl := Real.log_le_log ha hx.1
  have hu := Real.log_le_log (ha.trans_le hx.1) hx.2
  simp only [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hh := neg_abs_le (Real.log a)
    have hb0 := abs_nonneg (Real.log b)
    linarith
  · have hh := le_abs_self (Real.log b)
    have ha0 := abs_nonneg (Real.log a)
    linarith

lemma J_real_bounds {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1) :
    (1/2:ℝ)^(2*(d/16)) ≤ (J ν s).toReal ∧
      (J ν s).toReal ≤ H*(1+(9*3^d:ℝ)*2^((d-1)+2*(d/16)+1)) := by
  have hu := bounded_J hd ν hH hν s
  have ht := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have hnorm : ∀ᵐ u ∂ν, ‖u‖=1 := (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega))
  have hl := lower_J_on_sphere ν hnorm s hs
  constructor
  · convert ENNReal.toReal_mono ht hl using 1
    rw [ENNReal.toReal_ofReal (by positivity)]
  · convert ENNReal.toReal_mono ENNReal.ofReal_ne_top hu using 1
    rw [ENNReal.toReal_ofReal (by positivity)]

lemma integrable_log_J {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (hν : BoundedDensity ν) (μ : Measure (Ambient d))
    [IsFiniteMeasure μ] (hμ : ∀ᵐ s ∂μ, ‖s‖=1) :
    Integrable (fun s => Real.log (J ν s).toReal) μ := by
  obtain ⟨H,hH,hνH⟩ := hν
  apply integrable_log_of_bounds μ _ (measurable_J ν).ennreal_toReal (by positivity : 0 < (1/2:ℝ)^(2*(d/16)))
  filter_upwards [hμ] with s hs
  exact J_real_bounds hd ν hH hνH s hs

open EntropySupport

lemma density_integral_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {H : ℝ} (hfH : ∀ x,f x ≤ H)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))] :
    ∫ x,f x ∂μ = 1 := by
  have hif := integrable_bounded_measurable μ f hf (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfH x)
  have h := measure_univ (μ := μ.withDensity (fun x => ENNReal.ofReal (f x)))
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hif (ae_of_all _ hf0)] at h
  exact ENNReal.ofReal_eq_one.mp h

lemma density_entropy_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {H : ℝ} (hfH : ∀ x,f x ≤ H)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))] :
    0 ≤ ∫ x,xlog (f x) ∂μ := by
  have hif := integrable_bounded_measurable μ f hf (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfH x)
  have hix := integrable_xlog_bounded μ f hf hf0 hfH
  have h := integral_mono (hif.sub (integrable_const 1)) hix
    (fun x => Real.self_sub_one_le_mul_log (hf0 x))
  change (∫ x,f x-1 ∂μ) ≤ _ at h
  rw [integral_sub hif (integrable_const 1),density_integral_one μ f hf hf0 hfH] at h
  simpa using h

lemma entropy_young {f j M : ℝ} (hf : 0 ≤ f) (hj : 0 < j) (hM : 0 < M) :
    2*f*Real.log j ≤ xlog f+f*(Real.log M-1)+j^2/M := by
  have h := xlog_lower_tangent hf (div_pos (sq_pos_of_pos hj) hM)
  have hl : Real.log (j^2/M) = 2*Real.log j-Real.log M := by
    rw [Real.log_div (pow_ne_zero _ hj.ne') hM.ne',Real.log_pow]; norm_num
  dsimp [xlog] at h ⊢
  rw [hl] at h
  nlinarith

lemma sphereMoment_pos (d : ℕ) : 0 < sphereMoment d := by dsimp [sphereMoment]; positivity

lemma square_integrable_bound {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (hν : BoundedDensity ν) :
    Integrable (fun s => (J ν s).toReal^2) (sphereProbability d) ∧
      (∫ s,(J ν s).toReal^2 ∂sphereProbability d) ≤ sphereMoment d := by
  have hb := J_square_integral hd ν
  have ht : (∫⁻ s,(J ν s)^2 ∂sphereProbability d) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hm := (measurable_J ν).pow_const 2
  obtain ⟨H,hH,hνH⟩ := hν
  have hp : ∀ s,(J ν s)^2 < ∞ := fun s =>
    ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (bounded_J hd ν hH hνH s)))
  constructor
  · simpa only [ENNReal.toReal_pow] using integrable_toReal_of_lintegral_ne_top hm.aemeasurable ht
  · have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    change _ ≤ (ENNReal.ofReal (sphereMoment d)).toReal at hh
    rw [ENNReal.toReal_ofReal (sphereMoment_pos d).le] at hh
    simpa only [← ENNReal.toReal_pow, integral_toReal hm.aemeasurable (ae_of_all _ hp)] using hh

lemma Phi_density_formula {d : ℕ} (hd : 16 ≤ d) (f : Ambient d → ℝ)
    (hf : Measurable f) (hf0 : ∀ x,0 ≤ f x) {H : ℝ} (hfH : ∀ x,f x ≤ H)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (hν : BoundedDensity ν)
    (heq : ν = (sphereProbability d).withDensity (fun x => ENNReal.ofReal (f x))) :
    Phi ν = ∫ s, xlog (f s)-f s*Real.log (J ν s).toReal ∂sphereProbability d := by
  have : IsProbabilityMeasure ((sphereProbability d).withDensity (fun x => ENNReal.ofReal (f x))) := heq ▸ inferInstance
  have hix := integrable_xlog_bounded (sphereProbability d) f hf hf0 hfH
  have hil := integrable_log_J hd ν hν (sphereProbability d) (ae_unit_norm (by omega))
  have hib := hil.bdd_mul hf.aestronglyMeasurable (ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hf0 x)]; exact hfH x))
  have hD : (InformationTheory.klDiv ν (sphereProbability d)).toReal = ∫ s,xlog (f s) ∂sphereProbability d := by
    rw [heq,klDiv_withDensity_bounded _ f hf hf0 hfH,
      ENNReal.toReal_ofReal (density_entropy_nonneg _ f hf hf0 hfH)]
  have hB : B ν = ∫ s,f s*Real.log (J ν s).toReal ∂sphereProbability d := by
    unfold B
    nth_rw 1 [heq]
    rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hf0 _),smul_eq_mul]
  rw [Phi,hD,hB,integral_sub hix hib]

lemma B_entropy_bound {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (hν : BoundedDensity ν) :
    2*B ν ≤ (InformationTheory.klDiv ν (sphereProbability d)).toReal+Real.log (sphereMoment d) := by
  obtain ⟨H,hH,hνH⟩ := hν
  obtain ⟨f,hf,hf0,hfH,heq⟩ := bounded_density_representation (sphereProbability d) ν hH hνH
  have : IsProbabilityMeasure ((sphereProbability d).withDensity (fun x => ENNReal.ofReal (f x))) := heq ▸ inferInstance
  have hif := integrable_bounded_measurable (sphereProbability d) f hf
    (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfH x)
  have hix := integrable_xlog_bounded (sphereProbability d) f hf hf0 hfH
  have hil := integrable_log_J hd ν ⟨H,hH,hνH⟩ (sphereProbability d) (ae_unit_norm (by omega))
  have hib := hil.bdd_mul hf.aestronglyMeasurable (ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hf0 x)]; exact hfH x))
  obtain ⟨hij,hijbound⟩ := square_integrable_bound hd ν ⟨H,hH,hνH⟩
  have hpoint : ∀ᵐ s ∂sphereProbability d,
      2*(f s*Real.log (J ν s).toReal) ≤
        xlog (f s)+f s*(Real.log (sphereMoment d)-1)+(J ν s).toReal^2/sphereMoment d := by
    filter_upwards [ae_unit_norm (by omega : 0 < d)] with s hs
    have hj := (J_real_bounds hd ν hH hνH s hs).1
    have hjpos : 0 < (J ν s).toReal := lt_of_lt_of_le (by positivity) hj
    simpa only [mul_assoc] using entropy_young (hf0 s) hjpos (sphereMoment_pos d)
  have h := integral_mono_ae (hib.const_mul 2)
    ((hix.add (hif.mul_const _)).add (hij.div_const _)) hpoint
  change (∫ s,2*(f s*Real.log (J ν s).toReal) ∂sphereProbability d) ≤
    (∫ s,xlog (f s)+f s*(Real.log (sphereMoment d)-1)+(J ν s).toReal^2/sphereMoment d ∂sphereProbability d) at h
  rw [integral_const_mul,integral_add (f := fun s => xlog (f s)+f s*(Real.log (sphereMoment d)-1))
      (g := fun s => (J ν s).toReal^2/sphereMoment d) (hix.add (hif.mul_const _)) (hij.div_const _),
    integral_add hix (hif.mul_const (Real.log (sphereMoment d)-1)),integral_mul_const,integral_div,
    density_integral_one _ f hf hf0 hfH,one_mul] at h
  have hrat : (∫ s,(J ν s).toReal^2 ∂sphereProbability d)/sphereMoment d ≤ 1 :=
    (div_le_one (sphereMoment_pos d)).mpr hijbound
  have hD : (InformationTheory.klDiv ν (sphereProbability d)).toReal = ∫ s,xlog (f s) ∂sphereProbability d := by
    rw [heq,klDiv_withDensity_bounded _ f hf hf0 hfH,
      ENNReal.toReal_ofReal (density_entropy_nonneg _ f hf hf0 hfH)]
  have hB : B ν = ∫ s,f s*Real.log (J ν s).toReal ∂sphereProbability d := by
    unfold B
    nth_rw 1 [heq]
    rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hf0 _),smul_eq_mul]
  rw [hD,hB]
  linarith

lemma log_sphereMoment_le {d : ℕ} (hd : 16 ≤ d) : Real.log (sphereMoment d) ≤ 20*d := by
  let e := (d-1)+4*(d/16)+1
  have he : e ≤ 2*d := by dsimp [e]; omega
  have heR : (e:ℝ) ≤ 2*d := by exact_mod_cast he
  have hdR : (16:ℝ) ≤ d := by exact_mod_cast hd
  have h3 : (1:ℝ) ≤ 3^d := one_le_pow₀ (by norm_num)
  have h2 : (1:ℝ) ≤ 2^e := one_le_pow₀ (by norm_num)
  have hQ : (1:ℝ) ≤ 9*3^d*2^e := by nlinarith
  have hM : sphereMoment d ≤ 18*3^d*2^e := by dsimp [sphereMoment,e] at *; nlinarith
  have hl := Real.log_le_log (sphereMoment_pos d) hM
  have heq : Real.log (18*3^d*2^e:ℝ) = Real.log 18+(d:ℝ)*Real.log 3+(e:ℝ)*Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow]
  rw [heq] at hl
  have hl18 : Real.log (18:ℝ) ≤ 17 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 18)]
  have hl3 : Real.log (3:ℝ) ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)]
  have hl2 : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have he0 : (0:ℝ) ≤ e := Nat.cast_nonneg e
  nlinarith [mul_le_mul_of_nonneg_left hl3 (Nat.cast_nonneg d),mul_le_mul_of_nonneg_left hl2 he0]

lemma coercivity {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (hν : BoundedDensity ν) :
    (1/2:ℝ)*(InformationTheory.klDiv ν (sphereProbability d)).toReal-10*d ≤ Phi ν := by
  have h := B_entropy_bound hd ν hν
  have hl := log_sphereMoment_le hd
  unfold Phi
  linarith

lemma Phi_uniform_le {d : ℕ} (hd : 16 ≤ d) :
    Phi (sphereProbability d) ≤ (2*(d/16):ℕ)*Real.log 2 := by
  have hσ : BoundedDensity (sphereProbability d) := ⟨1,by norm_num,by simp⟩
  have hil := integrable_log_J hd (sphereProbability d) hσ (sphereProbability d) (ae_unit_norm (by omega))
  have hl : ∀ᵐ s ∂sphereProbability d,
      -((2*(d/16):ℕ):ℝ)*Real.log 2 ≤ Real.log (J (sphereProbability d) s).toReal := by
    filter_upwards [ae_unit_norm (by omega : 0 < d)] with s hs
    have hlow := (J_real_bounds hd (sphereProbability d) (by norm_num : (0:ℝ) < 1) (by simp) s hs).1
    have h := Real.log_le_log (by positivity : 0 < (1/2:ℝ)^(2*(d/16))) hlow
    rw [Real.log_pow,Real.log_div one_ne_zero (by norm_num),Real.log_one,zero_sub] at h
    simpa only [mul_neg,neg_mul] using h
  have h := integral_mono_ae (integrable_const (-((2*(d/16):ℕ):ℝ)*Real.log 2)) hil hl
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at h
  rw [Phi,InformationTheory.klDiv_self,ENNReal.toReal_zero,zero_sub]
  change -B (sphereProbability d) ≤ _
  change _ ≤ B (sphereProbability d) at h
  linarith

end Coercivity
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Mixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Coercivity
open KernelPotential.Geometry Sphere
open EntropySupport
lemma log_ratio_lower {a b P : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hP : 0 < P) (hz : b = 0 → a = 0) :
    a*(Real.log P+1)-P*b ≤ a*Real.log (a/b) := by
  by_cases hb0 : b = 0
  · simp [hb0,hz hb0]
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have h := xlog_lower_tangent (div_nonneg ha hb) hP
  have H := mul_le_mul_of_nonneg_left h hb
  dsimp [xlog] at H
  field_simp at H
  nlinarith

lemma log_ratio_mul {a b : ℝ} (hb : b ≠ 0) :
    a*Real.log (a/b) = xlog a-a*Real.log b := by
  by_cases ha : a = 0
  · simp [ha,xlog_zero]
  rw [Real.log_div ha hb]
  simp [xlog,mul_sub]

lemma perspective_sum_le {ι : Type*} [Fintype ι] (w x y : ι → ℝ)
    (hw : ∀ i,0 ≤ w i) (hx : ∀ i,0 ≤ x i) (hy : ∀ i,0 < y i)
    (hQ : 0 < ∑ i,w i*y i) :
    xlog (∑ i,w i*x i)-(∑ i,w i*x i)*Real.log (∑ i,w i*y i) ≤
      ∑ i,w i*(xlog (x i)-x i*Real.log (y i)) := by
  have hF0 : 0 ≤ ∑ i,w i*x i := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hx i))
  by_cases hF : ∑ i,w i*x i = 0
  · have hz : ∀ i,w i*x i=0 := fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hw i) (hx i))).mp hF i (Finset.mem_univ i)
    have hz' : ∀ i,w i*(xlog (x i)-x i*Real.log (y i))=0 := by
      intro i
      rcases mul_eq_zero.mp (hz i) with hi|hi <;> simp [hi,xlog_zero]
    simp [hF,hz',xlog_zero]
  have hFp : 0 < ∑ i,w i*x i := lt_of_le_of_ne hF0 (Ne.symm hF)
  let P := (∑ i,w i*x i)/(∑ i,w i*y i)
  have hP : 0 < P := div_pos hFp hQ
  have hi (i : ι) : w i*(x i*(Real.log P+1)-P*y i) ≤
      w i*(xlog (x i)-x i*Real.log (y i)) := by
    have h := log_ratio_lower (hx i) (hy i).le hP (fun hz => ((hy i).ne' hz).elim)
    rw [log_ratio_mul (hy i).ne'] at h
    exact mul_le_mul_of_nonneg_left h (hw i)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  have he : (∑ i,w i*(x i*(Real.log P+1)-P*y i)) =
      (∑ i,w i*x i)*(Real.log P+1)-P*(∑ i,w i*y i) := by
    simp_rw [mul_sub,← mul_assoc]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at h
  have hlog : Real.log P = Real.log (∑ i,w i*x i)-Real.log (∑ i,w i*y i) :=
    Real.log_div hFp.ne' hQ.ne'
  have hmul : P*(∑ i,w i*y i)=(∑ i,w i*x i) := div_mul_cancel₀ _ hQ.ne'
  rw [hlog,hmul] at h
  dsimp [xlog] at h ⊢
  nlinarith

lemma mixture_probability {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (w : ι → ℝ) (hw0 : ∀ i,0 ≤ w i) (hw1 : ∑ i,w i=1)
    (ν : ι → Measure α) (hν : ∀ i,IsProbabilityMeasure (ν i)) :
    IsProbabilityMeasure (∑ i,ENNReal.ofReal (w i) • ν i) := by
  have (i : ι) : IsProbabilityMeasure (ν i) := hν i
  constructor
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i),hw1,ENNReal.ofReal_one]

lemma mixture_density {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (w : ι → ℝ) (hw0 : ∀ i,0 ≤ w i)
    (f : ι → α → ℝ) (hf : ∀ i,Measurable (f i)) (hf0 : ∀ i x,0 ≤ f i x) :
    (∑ i,ENNReal.ofReal (w i) • μ.withDensity (fun x => ENNReal.ofReal (f i x))) =
      μ.withDensity (fun x => ENNReal.ofReal (∑ i,w i*f i x)) := by
  ext s hs
  rw [Measure.finsetSum_apply,withDensity_apply _ hs]
  simp only [Measure.smul_apply,smul_eq_mul,withDensity_apply _ hs]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw0 i) (hf0 i _)),
    ENNReal.ofReal_mul (hw0 _)]
  rw [lintegral_finsetSum (f := fun i x => ENNReal.ofReal (w i)*ENNReal.ofReal (f i x)) Finset.univ
    (fun i _ => measurable_const.mul (hf i).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro i _
  exact (lintegral_const_mul _ (hf i).ennreal_ofReal).symm

lemma density_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (f : α → ℝ) {H : ℝ} (hfH : ∀ x,f x ≤ H) :
    μ.withDensity (fun x => ENNReal.ofReal (f x)) ≤ ENNReal.ofReal H • μ := by
  intro s
  rw [withDensity_apply' _ s,Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∫⁻ x in s, ENNReal.ofReal H ∂μ := lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hfH x))
    _ = _ := by simp

lemma J_mixture {d q : ℕ} (hd : 16 ≤ d) (w : Fin q → ℝ) (hw : ∀ i,0 ≤ w i)
    (ν : Fin q → Measure (Ambient d)) (hνp : ∀ i,IsProbabilityMeasure (ν i))
    (hνb : ∀ i,BoundedDensity (ν i)) (s : Ambient d) :
    (J (∑ i,ENNReal.ofReal (w i) • ν i) s).toReal = ∑ i,w i*(J (ν i) s).toReal := by
  have (i : Fin q) : IsProbabilityMeasure (ν i) := hνp i
  have ht (i : Fin q) : J (ν i) s ≠ ∞ := by
    obtain ⟨H,hH,hνH⟩ := hνb i
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (bounded_J hd (ν i) hH hνH s)
  unfold J
  rw [lintegral_finsetSum_measure]
  simp_rw [lintegral_smul_measure,smul_eq_mul]
  change (∑ i,ENNReal.ofReal (w i)*J (ν i) s).toReal = _
  rw [ENNReal.toReal_sum (f := fun i => ENNReal.ofReal (w i)*J (ν i) s)
    (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ht i))]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (hw _),J]

lemma finite_convexity {d : ℕ} (hd : 16 ≤ d) (q : ℕ) (w : Fin q → ℝ)
    (hw0 : ∀ i,0 ≤ w i) (hw1 : ∑ i,w i=1)
    (ν : Fin q → Measure (Ambient d)) (hνp : ∀ i,IsProbabilityMeasure (ν i))
    (hνb : ∀ i,BoundedDensity (ν i)) :
    Phi (∑ i,ENNReal.ofReal (w i) • ν i) ≤ ∑ i,w i*Phi (ν i) := by
  have (i : Fin q) : IsProbabilityMeasure (ν i) := hνp i
  have hνb' := hνb
  choose H hH hνH using hνb'
  choose f hf hf0 hfH heq using fun i => bounded_density_representation (sphereProbability d) (ν i) (hH i) (hνH i)
  let F : Ambient d → ℝ := fun x => ∑ i,w i*f i x
  let M : ℝ := 1+∑ i,w i*H i
  let τ := ∑ i,ENNReal.ofReal (w i) • ν i
  have hτeq : τ = (sphereProbability d).withDensity (fun x => ENNReal.ofReal (F x)) := by
    dsimp [τ,F]
    simp_rw [heq]
    exact mixture_density (sphereProbability d) w hw0 f hf hf0
  have hF : Measurable F := Finset.measurable_sum _ (fun i _ => measurable_const.mul (hf i))
  have hF0 : ∀ x,0 ≤ F x := fun x => Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i) (hf0 i x))
  have hFM : ∀ x,F x ≤ M := by
    intro x
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left (hfH i x) (hw0 i))
    dsimp [F,M]
    linarith
  have hM : 0 < M := by
    have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ => mul_nonneg (hw0 i) (hH i).le)
    dsimp [M]
    linarith
  have hτH : τ ≤ ENNReal.ofReal M • sphereProbability d := by
    rw [hτeq]; exact density_bounded _ F hFM
  have hτb : BoundedDensity τ := ⟨M,hM,hτH⟩
  have : IsProbabilityMeasure τ := mixture_probability w hw0 hw1 ν hνp
  have hix : ∀ i, Integrable (fun s => xlog (f i s)-f i s*Real.log (J (ν i) s).toReal) (sphereProbability d) := by
    intro i
    apply (integrable_xlog_bounded _ _ (hf i) (hf0 i) (hfH i)).sub
    exact (integrable_log_J hd (ν i) (hνb i) _ (ae_unit_norm (by omega))).bdd_mul
      (hf i).aestronglyMeasurable (ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hf0 i x)]; exact hfH i x))
  have hiF : Integrable (fun s => xlog (F s)-F s*Real.log (J τ s).toReal) (sphereProbability d) := by
    apply (integrable_xlog_bounded _ _ hF hF0 hFM).sub
    exact (integrable_log_J hd τ hτb _ (ae_unit_norm (by omega))).bdd_mul
      hF.aestronglyMeasurable (ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hF0 x)]; exact hFM x))
  have hpoint : ∀ᵐ s ∂sphereProbability d,
      xlog (F s)-F s*Real.log (J τ s).toReal ≤
        ∑ i,w i*(xlog (f i s)-f i s*Real.log (J (ν i) s).toReal) := by
    filter_upwards [ae_unit_norm (by omega : 0 < d)] with s hs
    have hji : ∀ i,0 < (J (ν i) s).toReal := fun i =>
      lt_of_lt_of_le (by positivity) (J_real_bounds hd (ν i) (hH i) (hνH i) s hs).1
    have hjτ : 0 < (J τ s).toReal := lt_of_lt_of_le (by positivity) (J_real_bounds hd τ hM hτH s hs).1
    have hJ := J_mixture hd w hw0 ν hνp hνb s
    change (J τ s).toReal = _ at hJ
    rw [hJ] at hjτ ⊢
    exact perspective_sum_le w (fun i => f i s) (fun i => (J (ν i) s).toReal) hw0 (fun i => hf0 i s) hji hjτ
  have h := integral_mono_ae hiF (integrable_finsetSum _ (fun i _ => (hix i).const_mul (w i))) hpoint
  rw [integral_finsetSum _ (fun i _ => (hix i).const_mul (w i))] at h
  simp only [integral_const_mul] at h
  have hrhs : (∑ i,w i*Phi (ν i)) =
      ∑ i,w i*(∫ s,xlog (f i s)-f i s*Real.log (J (ν i) s).toReal ∂sphereProbability d) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Phi_density_formula hd (f i) (hf i) (hf0 i) (hfH i) (ν i) (hνb i) (heq i)]
  change Phi τ ≤ _
  rw [Phi_density_formula hd F hF hF0 hFM τ hτb hτeq,hrhs]
  exact h

end Coercivity

theorem kernel_coercivity_oai : CoercivityStatement := by
  refine ⟨10,by norm_num,16,?_⟩
  intro d hd
  refine ⟨?_,Coercivity.Phi_uniform_le hd,?_⟩
  · intro ν hν hνb
    have := hν
    exact Coercivity.coercivity hd ν hνb
  · exact Coercivity.finite_convexity hd

end KernelPotential

end OAI
end

theorem solution : type_of% @OAI.KernelPotential.kernel_coercivity_oai := @OAI.KernelPotential.kernel_coercivity_oai
