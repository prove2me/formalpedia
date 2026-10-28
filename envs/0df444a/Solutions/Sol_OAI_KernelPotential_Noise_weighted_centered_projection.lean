-- Prove2me | solution 1 for OAI.KernelPotential.Noise.weighted_centered_projection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:02:24.821733+00:00
-- url     : https://prove2.me/submissions/7e5e2ad7-64da-4793-aed0-2b35413541d0

import Mathlib
import Definitions.Def_GaussianInformation_003
import Definitions.Def_OAIQWRLC001

section
-- module Solutions.OAIQW_RepeatedLocalization.Compat
namespace OAI
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434


end OAI
end

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

lemma angular_integral_ball (μ : Measure E) {a k : ℕ} {B R : ℝ}
    (hB : 0 ≤ B) (hR : 0 < R) (hk : 0 < k)
    (hball : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (B*r^a))
    (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    (hdim : Module.finrank ℝ V.direction + (k+1) ≤ a) :
    (∫⁻ x in closedBall 0 R, (ENNReal.ofReal (infDist x (V : Set E)/R))⁻¹^k ∂μ) ≤
      ENNReal.ofReal (B * 9^(Module.finrank ℝ V.direction) * 3^a * R^a * 2^(k+2)) := by
  let C := B * 9^(Module.finrank ℝ V.direction) * 3^a * R^a
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : (μ.restrict (closedBall 0 R)) univ ≤ ENNReal.ofReal C := by
    rw [Measure.restrict_apply_univ]
    calc
      μ (closedBall 0 R) ≤ μ (ball 0 (2*R)) := measure_mono (closedBall_subset_ball (by linarith))
      _ ≤ ENNReal.ofReal (B*(2*R)^a) := hball _ _ (by positivity)
      _ ≤ ENNReal.ofReal C := by
        apply ENNReal.ofReal_le_ofReal
        have h9 : (1:ℝ) ≤ 9^(Module.finrank ℝ V.direction) := one_le_pow₀ (by norm_num)
        dsimp [C]
        rw [mul_pow]
        calc
          B * (2^a * R^a) ≤ B * (3^a * R^a) := by gcongr; norm_num
          _ ≤ B * 9^(Module.finrank ℝ V.direction) * 3^a * R^a := by
            nlinarith [mul_nonneg (mul_nonneg hB (pow_nonneg (by norm_num : (0:ℝ) ≤ 3) a))
              (pow_nonneg hR.le a)]
  have ht : ∀ j : ℕ, (μ.restrict (closedBall 0 R)) {x | infDist x (V : Set E)/R ≤ (1/2:ℝ)^j} ≤
      ENNReal.ofReal C * ENNReal.ofReal ((1/2:ℝ)^((k+1)*j)) := by
    intro j
    rw [Measure.restrict_apply (measurableSet_le ((continuous_infDist_pt _).measurable.div_const R) measurable_const)]
    have heq : {x | infDist x (V : Set E)/R ≤ (1/2:ℝ)^j} ∩ closedBall 0 R =
        {x | ‖x‖ ≤ R ∧ infDist x (V : Set E) ≤ R*(1/2:ℝ)^j} := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, mem_closedBall, dist_zero_right]
      rw [div_le_iff₀ hR, mul_comm ((1/2:ℝ)^j) R]
      tauto
    rw [heq]
    convert tube_ball_bound μ hB hR (by positivity : 0 < (1/2:ℝ)^j)
      (pow_le_one₀ (by norm_num) (by norm_num)) hball V hV hdim using 1
    rw [← ENNReal.ofReal_mul hC]
    dsimp [C]
    congr 1
    rw [← pow_mul, Nat.mul_comm j (k+1)]
  have hh := inverseMoment_extended_of_tails (μ.restrict (closedBall 0 R))
    (fun x => infDist x (V : Set E)/R) ((continuous_infDist_pt _).measurable.div_const R)
    (fun _ => div_nonneg infDist_nonneg hR.le) k hk (ENNReal.ofReal C) ENNReal.ofReal_ne_top ht
  calc
    _ ≤ (μ.restrict (closedBall 0 R)) univ + ENNReal.ofReal C*ENNReal.ofReal ((2:ℝ)^(k+1)) := hh
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal C*ENNReal.ofReal ((2:ℝ)^(k+1)) := by gcongr
    _ ≤ ENNReal.ofReal (C * 2^(k+2)) := by
      rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_add hC (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hp : (1:ℝ) ≤ 2^(k+1) := one_le_pow₀ (by norm_num)
      have he : (2:ℝ)^(k+2) = 2^(k+1)*2 := by rw [show k+2=(k+1)+1 by omega,pow_succ]
      rw [he]
      nlinarith

lemma inverse_normalized (y R : ℝ) (hR : 0 < R) (k : ℕ) :
    (ENNReal.ofReal y)⁻¹^k = ENNReal.ofReal (R⁻¹^k) *
      (ENNReal.ofReal (y/R))⁻¹^k := by
  have hR0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  rw [ENNReal.ofReal_pow (inv_nonneg.mpr hR.le), ENNReal.ofReal_inv_of_pos hR,
    ENNReal.ofReal_div_of_pos hR,
    ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inl hR0),
    div_eq_mul_inv, mul_pow, ← mul_assoc, ← mul_pow,
    ENNReal.inv_mul_cancel hR0 ENNReal.ofReal_ne_top]
  simp

lemma mixed_integral_shell (μ : Measure E) {a k : ℕ} {B R : ℝ}
    (hB : 0 ≤ B) (hR : 0 < R) (hk : 0 < k) (ha : 2*k ≤ a)
    (hball : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (B*r^a))
    (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    (hdim : Module.finrank ℝ V.direction + (k+1) ≤ a) :
    (∫⁻ x in {x | R/2 < ‖x‖ ∧ ‖x‖ ≤ R},
      (ENNReal.ofReal ‖x‖)⁻¹^k * (ENNReal.ofReal (infDist x (V : Set E)))⁻¹^k ∂μ) ≤
      ENNReal.ofReal (B * 9^(Module.finrank ℝ V.direction) * 3^a * 2^(2*k+2) * R^(a-2*k)) := by
  let g : E → ℝ≥0∞ := fun x => (ENNReal.ofReal (infDist x (V : Set E)/R))⁻¹^k
  have hg : Measurable g := ((continuous_infDist_pt _).measurable.div_const R).ennreal_ofReal.inv.pow_const _
  let c : ℝ := (R/2)⁻¹^k * R⁻¹^k
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpoint : ∀ x ∈ {x : E | R/2 < ‖x‖ ∧ ‖x‖ ≤ R},
      (ENNReal.ofReal ‖x‖)⁻¹^k * (ENNReal.ofReal (infDist x (V : Set E)))⁻¹^k ≤
      ENNReal.ofReal c * g x := by
    intro x hx
    calc
      _ ≤ (ENNReal.ofReal (R/2))⁻¹^k * (ENNReal.ofReal (infDist x (V : Set E)))⁻¹^k := by
        gcongr
        exact hx.1.le
      _ = ENNReal.ofReal c * g x := by
        rw [inverse_normalized (infDist x (V : Set E)) R hR k,
          ← ENNReal.ofReal_inv_of_pos (show 0 < R/2 by positivity),
          ← ENNReal.ofReal_pow (by positivity), ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
  calc
    _ ≤ ∫⁻ x in {x : E | R/2 < ‖x‖ ∧ ‖x‖ ≤ R}, ENNReal.ofReal c*g x ∂μ :=
      setLIntegral_mono (measurable_const.mul hg) hpoint
    _ ≤ ∫⁻ x in closedBall 0 R, ENNReal.ofReal c*g x ∂μ :=
      lintegral_mono_set (fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hx.2)
    _ = ENNReal.ofReal c * ∫⁻ x in closedBall 0 R, g x ∂μ := lintegral_const_mul _ hg
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (B*9^(Module.finrank ℝ V.direction)*3^a*R^a*2^(k+2)) :=
      mul_le_mul_right (angular_integral_ball μ hB hR hk hball V hV hdim) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le ha
      simp only [he, Nat.add_sub_cancel_left, c, inv_pow, div_pow,
        pow_add, pow_mul, pow_succ]
      field_simp
      ring_nf
      simp only [Nat.mul_comm k 2, pow_mul]
      norm_num

lemma ball_bound_zero_null {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) {a : ℕ} {B : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    (hball : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (B*r^a)) :
    μ {x | ‖x‖ = 0} = 0 := by
  have hr : ENNReal.ofReal ((1/2:ℝ)^a) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact pow_lt_one₀ (by norm_num) (by norm_num) ha.ne'
  have ht := ENNReal.Tendsto.const_mul
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr ENNReal.ofReal_ne_top :
      (0:ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal B ≠ ∞)
  apply le_antisymm _ bot_le
  apply ge_of_tendsto' (show Tendsto (fun j : ℕ => ENNReal.ofReal B *
    ENNReal.ofReal ((1/2:ℝ)^a)^j) atTop (𝓝 (0:ℝ≥0∞)) from by simpa using ht)
  intro j
  calc
    μ {x | ‖x‖ = 0} ≤ μ (ball 0 ((1/2:ℝ)^j)) := by
      apply measure_mono
      intro x hx
      change ‖x‖ = 0 at hx
      simpa only [mem_ball, dist_zero_right, hx] using (by positivity : (0:ℝ) < (1/2:ℝ)^j)
    _ ≤ ENNReal.ofReal (B*(((1/2:ℝ)^j)^a)) := hball _ _ (by positivity)
    _ = _ := by rw [ENNReal.ofReal_mul hB, ← pow_mul, Nat.mul_comm j a, pow_mul,
      ENNReal.ofReal_pow (by positivity)]

lemma logarithmic_series_bound (f : ℕ → ℝ≥0∞) {A D : ℝ} (hA : 0 ≤ A) (_hD : 0 ≤ D)
    (L : ℕ) (hDA : D ≤ A*2^L)
    (hfirst : ∀ j, f j ≤ ENNReal.ofReal A)
    (hsecond : ∀ j, f j ≤ ENNReal.ofReal (D*(1/2:ℝ)^j)) :
    (∑' j, f j) ≤ ENNReal.ofReal (A*((L:ℝ)+2)) := by
  rw [← (ENNReal.summable (f := fun i => f (i+L))).sum_add_tsum_nat_add']
  have ht : ∀ i : ℕ, f (i+L) ≤ ENNReal.ofReal A * ENNReal.ofReal ((1/2:ℝ)^i) := by
    intro i
    apply (hsecond _).trans
    rw [← ENNReal.ofReal_mul hA]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (A*2^L)*(1/2:ℝ)^(i+L) := mul_le_mul_of_nonneg_right hDA (by positivity)
      _ = _ := by
        rw [pow_add]
        simp only [one_div,inv_pow]
        field_simp
  calc
    _ ≤ (∑ _i ∈ Finset.range L, ENNReal.ofReal A) +
        ∑' i, ENNReal.ofReal A * ENNReal.ofReal ((1/2:ℝ)^i) := by
      exact add_le_add (Finset.sum_le_sum (fun i _ => hfirst i)) (ENNReal.tsum_le_tsum ht)
    _ = ENNReal.ofReal (A*((L:ℝ)+2)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2), ENNReal.tsum_mul_left,
        ENNReal.tsum_geometric]
      norm_num [ENNReal.ofReal_div_of_pos]
      rw [← ENNReal.ofReal_natCast L, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul hA,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

lemma mixed_integral_logarithmic (μ : Measure E) {n k : ℕ} {B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hk : 0 < k) (hn : 2*k < n)
    (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ 2)
    (hballB : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (B*r^(2*k)))
    (hballD : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (D*r^n))
    (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    (hdim : Module.finrank ℝ V.direction ≤ k-1) (L : ℕ) (hDB : D ≤ B*2^L) :
    (∫⁻ x, (ENNReal.ofReal ‖x‖)⁻¹^k * (ENNReal.ofReal (infDist x (V : Set E)))⁻¹^k ∂μ) ≤
      ENNReal.ofReal ((9^(Module.finrank ℝ V.direction) * 3^n * 2^(n+2*k+2)) * B * ((L:ℝ)+2)) := by
  let K : ℝ := 9^(Module.finrank ℝ V.direction) * 3^n * 2^(n+2*k+2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let R : ℕ → ℝ := fun j => 2*(1/2:ℝ)^j
  let S : ℕ → Set E := fun j => {x | R j/2 < ‖x‖ ∧ ‖x‖ ≤ R j}
  let f : E → ℝ≥0∞ := fun x => (ENNReal.ofReal ‖x‖)⁻¹^k * (ENNReal.ofReal (infDist x (V : Set E)))⁻¹^k
  have hdimB : Module.finrank ℝ V.direction + (k+1) ≤ 2*k := by omega
  have hdimD : Module.finrank ℝ V.direction + (k+1) ≤ n := by omega
  have hz : ∀ᵐ x ∂μ, ‖x‖ ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using ball_bound_zero_null μ (by omega : 0 < 2*k) hB hballB
  have hcov : ∀ᵐ x ∂μ, x ∈ ⋃ j, S j := by
    filter_upwards [hsupport,hz] with x hx hx0
    obtain ⟨j,hj,hj'⟩ := exists_nat_pow_near_of_lt_one
      (div_pos (lt_of_le_of_ne (norm_nonneg _) hx0.symm) (by norm_num : (0:ℝ) < 2))
      (by linarith : ‖x‖/2 ≤ 1) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
    apply mem_iUnion.mpr ⟨j,?_⟩
    dsimp [S,R]
    rw [pow_succ] at hj
    constructor <;> linarith
  have hiB : ∀ j, (∫⁻ x in S j, f x ∂μ) ≤ ENNReal.ofReal (K*B) := by
    intro j
    apply (mixed_integral_shell μ hB (by dsimp [R]; positivity : 0 < R j) hk le_rfl hballB V hV hdimB).trans
    apply ENNReal.ofReal_le_ofReal
    simp only [Nat.sub_self, pow_zero, mul_one]
    have h3 : (3:ℝ)^(2*k) ≤ 3^n := pow_le_pow_right₀ (by norm_num) hn.le
    have h2 : (2:ℝ)^(2*k+2) ≤ 2^(n+2*k+2) := pow_le_pow_right₀ (by norm_num) (by omega)
    dsimp [K]
    calc
      _ ≤ B*9^(Module.finrank ℝ V.direction)*3^n*2^(n+2*k+2) := by gcongr
      _ = _ := by ring
  have hiD : ∀ j, (∫⁻ x in S j, f x ∂μ) ≤ ENNReal.ofReal ((K*D)*(1/2:ℝ)^j) := by
    intro j
    apply (mixed_integral_shell μ hD (by dsimp [R]; positivity : 0 < R j) hk hn.le hballD V hV hdimD).trans
    apply ENNReal.ofReal_le_ofReal
    have hp : R j^(n-2*k) ≤ 2^n*(1/2:ℝ)^j := by
      dsimp [R]
      rw [mul_pow]
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      · simpa only [pow_one] using pow_le_pow_of_le_one
          (by positivity : 0 ≤ (1/2:ℝ)^j) (pow_le_one₀ (by norm_num) (by norm_num)) (by omega : 1 ≤ n-2*k)
      · positivity
      · positivity
    calc
      _ ≤ D*9^(Module.finrank ℝ V.direction)*3^n*2^(2*k+2)*(2^n*(1/2:ℝ)^j) := by gcongr
      _ = _ := by dsimp [K]; rw [show n+2*k+2=n+(2*k+2) by omega,pow_add]; ring
  calc
    (∫⁻ x, f x ∂μ) = ∫⁻ x in ⋃ j,S j, f x ∂μ := by rw [Measure.restrict_eq_self_of_ae_mem hcov]
    _ ≤ ∑' j, ∫⁻ x in S j,f x ∂μ := lintegral_iUnion_le S f
    _ ≤ ENNReal.ofReal ((K*B)*((L:ℝ)+2)) := logarithmic_series_bound _
      (mul_nonneg hK hB) (mul_nonneg hK hD) L
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hDB hK) hiB hiD

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

open EntropySupport

end Coercivity
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_BoxKernels
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
namespace Projection

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace Support

lemma lintegral_pi_product {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (f : α → ℝ≥0∞) (hf : Measurable f) (m : ℕ) :
    (∫⁻ z : Fin m → α, ∏ i, f (z i) ∂Measure.pi (fun _ => μ)) = (∫⁻ z, f z ∂μ)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [((measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => μ) 0).symm).lintegral_map_equiv]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Fin.prod_univ_succ, Fin.zero_succAbove]
    change (∫⁻ z : α × (Fin m → α), f z.1 * ∏ i, f (z.2 i)
      ∂μ.prod (Measure.pi (fun _ => μ))) = _
    rw [lintegral_prod_mul (μ := μ) (ν := Measure.pi (fun _ : Fin m => μ))
      (g := fun z : Fin m → α => ∏ i, f (z i)) hf.aemeasurable (by
      exact (Finset.measurable_prod _ fun i _ => hf.comp (measurable_pi_apply i)).aemeasurable),
      ih, pow_succ']

lemma measurable_boxKernel {k : ℕ} (η : ℝ) :
    Measurable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => boxKernel η p.1 p.2) := by
  have hs : MeasurableSet {p : (Fin k → ℝ) × (Fin k → ℝ) | ∀ i, |p.2 i-p.1 i| ≤ η} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le
      (((measurable_pi_apply i).comp measurable_snd).sub
        ((measurable_pi_apply i).comp measurable_fst)).abs measurable_const
  exact measurable_const.indicator hs

lemma boxKernel_le {k : ℕ} (η : ℝ) (c u : Fin k → ℝ) :
    boxKernel η c u ≤ boxScale k η := Set.indicator_le_self (closedBox c η) (fun _ => boxScale k η) u

lemma boxKernel_ne_zero_mem {k : ℕ} {η : ℝ} {c u : Fin k → ℝ}
    (h : boxKernel η c u ≠ 0) : u ∈ closedBox c η := by
  by_contra hu
  exact h (Set.indicator_of_notMem hu _)

end Support

open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

end Projection
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_GramVolume
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
namespace Projection
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace Support

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gram_linearCombination {ι : Type*} [Fintype ι] (g : ι → E)
    (T : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, T i j • g i) = Tᵀ * Matrix.gram ℝ g * T := by
  ext i j
  simp only [Matrix.gram_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma gramTriangular_expansion {q : ℕ} (f : Fin q → E) (j : Fin q) :
    f j = ∑ i, gramTriangular f i j • gramSchmidt ℝ f i := by
  rw [gramSchmidt_def'' ℝ f j]
  have hfin : (Finset.univ.filter fun i : Fin q => i < j) = Finset.Iio j := by
    ext i
    simp
  simp only [gramTriangular, add_smul, Finset.sum_add_distrib, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_filter, hfin]
  simp only [RCLike.ofReal_real_eq_id, id_eq]

lemma gramTriangular_det {q : ℕ} (f : Fin q → E) : (gramTriangular f).det = 1 := by
  have htri : (gramTriangular f).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp only [gramTriangular, ite_eq_right (ne_of_gt hij), ite_eq_right (not_lt.mpr (le_of_lt hij)),
      zero_add]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [gramTriangular]

lemma gram_gramSchmidt {q : ℕ} (f : Fin q → E) :
    Matrix.gram ℝ (gramSchmidt ℝ f) =
      Matrix.diagonal (fun i => ‖gramSchmidt ℝ f i‖ ^ 2) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [h, gramSchmidt_orthogonal ℝ f h]

lemma gram_det_eq_prod_gramSchmidt {q : ℕ} (f : Fin q → E) :
    (Matrix.gram ℝ f).det = (∏ i, ‖gramSchmidt ℝ f i‖)^2 := by
  have he : f = (fun j => ∑ i, gramTriangular f i j • gramSchmidt ℝ f i) :=
    funext (gramTriangular_expansion f)
  calc
    (Matrix.gram ℝ f).det =
        ((gramTriangular f)ᵀ * Matrix.gram ℝ (gramSchmidt ℝ f) * gramTriangular f).det := by
      conv_lhs => rw [he]
      rw [gram_linearCombination]
    _ = (∏ i, ‖gramSchmidt ℝ f i‖)^2 := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        gramTriangular_det, one_mul, mul_one, gram_gramSchmidt, Matrix.det_diagonal,
        Finset.prod_pow]

lemma sqrt_gram_det_eq_prod_gramSchmidt {q : ℕ} (f : Fin q → E) :
    Real.sqrt (Matrix.gram ℝ f).det = ∏ i, ‖gramSchmidt ℝ f i‖ := by
  rw [gram_det_eq_prod_gramSchmidt, Real.sqrt_sq (Finset.prod_nonneg fun _ _ => norm_nonneg _)]

lemma gramSchmidt_real_def {q : ℕ} (f : Fin q → E) (j : Fin q) :
    gramSchmidt ℝ f j = f j - ∑ i ∈ Finset.Iio j,
      (⟪gramSchmidt ℝ f i, f j⟫ / ‖gramSchmidt ℝ f i‖ ^ 2) • gramSchmidt ℝ f i := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [RCLike.ofReal_real_eq_id, id_eq] using (gramSchmidt_def'' ℝ f j).symm

lemma measurable_gramSchmidt {q : ℕ} [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (j : Fin q) :
    Measurable (fun f : Fin q → E => gramSchmidt ℝ f j) := by
  induction j using (wellFounded_lt (α := Fin q)).induction with
  | h j ih =>
    simp_rw [gramSchmidt_real_def (j := j)]
    refine (measurable_pi_apply j).sub (Finset.measurable_fun_sum _ fun i hi => ?_)
    have hmi := ih i (Finset.mem_Iio.mp hi)
    exact ((hmi.inner (measurable_pi_apply j)).div (hmi.norm.pow_const 2)).smul hmi

lemma gramSchmidt_residual_mem_span {q : ℕ} (f : Fin q → E) (j : Fin q) :
    f j - gramSchmidt ℝ f j ∈ Submodule.span ℝ (f '' Set.Iio j) := by
  rw [gramSchmidt_real_def, sub_sub_cancel]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  rw [← span_gramSchmidt_Iio ℝ f j]
  exact Submodule.subset_span (mem_image_of_mem _ (Finset.mem_Iio.mp hi))

end Support

end Projection
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ReplicaMoments
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
namespace Projection
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace Support
open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gramSchmidt_castSucc {q : ℕ} (f : Fin (q+1) → E) (j : Fin q) :
    gramSchmidt ℝ f j.castSucc = gramSchmidt ℝ (fun i => f i.castSucc) j := by
  induction j using (wellFounded_lt (α := Fin q)).induction with
  | h j ih =>
    rw [gramSchmidt_real_def, gramSchmidt_real_def, Fin.sum_Iio_castSucc]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [ih i (Finset.mem_Iio.mp hi)]

lemma replicaPlane_nonempty {q : ℕ} (b : E) (f : Fin q → E) :
    (replicaPlane b f : Set E).Nonempty := by
  exact ⟨b, AffineSubspace.self_mem_mk' _ _⟩

lemma replicaPlane_finrank_le {q : ℕ} (b : E) (f : Fin q → E) :
    Module.finrank ℝ (replicaPlane b f).direction ≤ q := by
  unfold replicaPlane
  rw [AffineSubspace.direction_mk']
  simpa [Set.finrank] using (finrank_range_le_card (R := ℝ) f)

lemma lastPlane_infDist_le {q : ℕ} (b : E) (f : Fin (q+1) → E) :
    infDist (f (Fin.last q) + b) (replicaPlane b (fun i => f i.castSucc) : Set E) ≤
      ‖gramSchmidt ℝ f (Fin.last q)‖ := by
  have hset : f '' Iio (Fin.last q) = range (fun i : Fin q => f i.castSucc) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.castSucc, i.isLt, rfl⟩
  have hm := gramSchmidt_residual_mem_span f (Fin.last q)
  rw [hset] at hm
  have hpoint : f (Fin.last q) - gramSchmidt ℝ f (Fin.last q) + b ∈
      replicaPlane b (fun i => f i.castSucc) := by
    apply AffineSubspace.mem_mk'.mpr
    simpa using hm
  convert infDist_le_dist_of_mem (x := f (Fin.last q)+b) hpoint using 1
  rw [dist_eq_norm]
  congr 1
  abel

lemma gramInverseProduct_succ {q : ℕ} (k : ℕ) (f : Fin (q+1) → E) :
    gramInverseProduct k f = gramInverseProduct k (fun i => f i.castSucc) *
      (ENNReal.ofReal ‖gramSchmidt ℝ f (Fin.last q)‖)⁻¹ ^ k := by
  unfold gramInverseProduct
  rw [Fin.prod_univ_castSucc]
  simp_rw [gramSchmidt_castSucc]

lemma measurable_gramInverseProduct {q : ℕ} [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (k : ℕ) :
    Measurable (gramInverseProduct (E := E) (q := q) k) := by
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gramSchmidt i).norm.ennreal_ofReal.inv.pow_const _

lemma lintegral_gramInverseProduct_le {α : Type*} [MeasurableSpace α]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) [SigmaFinite μ] (a : α → E) (ha : Measurable a)
    (k p : ℕ) (M : ℝ≥0∞)
    (hcond : ∀ V : AffineSubspace ℝ E, (V : Set E).Nonempty →
      Module.finrank ℝ V.direction ≤ p →
      (∫⁻ z, (ENNReal.ofReal (infDist (a z) (V : Set E)))⁻¹ ^ k ∂μ) ≤ M)
    (q : ℕ) (hq : q ≤ p+1) (b : E) :
    (∫⁻ z : Fin q → α, gramInverseProduct k (fun i => a (z i)-b)
      ∂Measure.pi (fun _ => μ)) ≤ M^q := by
  induction q with
  | zero => simp [gramInverseProduct]
  | succ q ih =>
    have hq' : q ≤ p := by omega
    have hmeas : Measurable (fun z : Fin (q+1) → α =>
        gramInverseProduct k (fun i => a (z i)-b)) :=
      (measurable_gramInverseProduct k).comp
        (Measurable.of_eval fun i => (ha.comp (measurable_pi_apply i)).sub measurable_const)
    rw [((measurePreserving_piFinSuccAbove (fun _ : Fin (q+1) => μ) (Fin.last q)).symm).lintegral_map_equiv]
    rw [lintegral_prod_symm _ (by
      exact (hmeas.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q+1) => α)
        (Fin.last q)).symm.measurable).aemeasurable)]
    have hlast : ∀ (z : Fin q → α),
        (∫⁻ x, gramInverseProduct k (fun i => a (Fin.snoc (α := fun _ : Fin (q+1) => α) z x i)-b) ∂μ) ≤
          gramInverseProduct k (fun i => a (z i)-b) * M := by
      intro z
      let V := replicaPlane b (fun i => a (z i)-b)
      have hV := replicaPlane_nonempty b (fun i => a (z i)-b)
      have hr := (replicaPlane_finrank_le b (fun i => a (z i)-b)).trans hq'
      calc
        _ ≤ ∫⁻ x, gramInverseProduct k (fun i => a (z i)-b) *
            (ENNReal.ofReal (infDist (a x) (V : Set E)))⁻¹ ^ k ∂μ := by
          apply lintegral_mono
          intro x
          dsimp only
          rw [gramInverseProduct_succ]
          simp only [Fin.snoc_castSucc]
          apply mul_le_mul_right
          apply pow_le_pow_left'
          apply ENNReal.inv_le_inv.mpr
          apply ENNReal.ofReal_le_ofReal
          simpa only [V, Fin.snoc_last, Fin.snoc_castSucc, sub_add_cancel] using
            (lastPlane_infDist_le b (fun i => a (Fin.snoc (α := fun _ : Fin (q+1) => α) z x i)-b))
        _ = gramInverseProduct k (fun i => a (z i)-b) *
            ∫⁻ x, (ENNReal.ofReal (infDist (a x) (V : Set E)))⁻¹ ^ k ∂μ := by
          exact lintegral_const_mul _ (by
            exact ((((continuous_infDist_pt (V : Set E)).measurable.comp ha).ennreal_ofReal.inv).pow_const k))
        _ ≤ gramInverseProduct k (fun i => a (z i)-b) * M := mul_le_mul_right (hcond V hV hr) _
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_last]
    calc
      _ ≤ ∫⁻ z : Fin q → α, gramInverseProduct k (fun i => a (z i)-b) * M
          ∂Measure.pi (fun _ => μ) := lintegral_mono hlast
      _ = (∫⁻ z : Fin q → α, gramInverseProduct k (fun i => a (z i)-b)
          ∂Measure.pi (fun _ => μ)) * M := by
        exact lintegral_mul_const _ ((measurable_gramInverseProduct k).comp
          (Measurable.of_eval fun i => (ha.comp (measurable_pi_apply i)).sub measurable_const))
      _ ≤ M^q * M := mul_le_mul_left (ih (by omega)) M
      _ = M^(q+1) := (pow_succ _ _).symm

lemma gramInverseProduct_eq_inverseVolume {q : ℕ} (k : ℕ) (f : Fin q → E) :
    gramInverseProduct k f = (ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ f).det))⁻¹ ^ k := by
  rw [sqrt_gram_det_eq_prod_gramSchmidt,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _),
    ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr ENNReal.ofReal_ne_top),
    ← Finset.prod_pow]
  rfl

end Support

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

end Projection
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_GaussianImages
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
namespace Projection
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Support

lemma finiteProduct_le {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] {μ ν : ∀ i, Measure (E i)}
    (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.pi, Measure.pi, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  have ho : (OuterMeasure.pi fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi fun i => (ν i).toOuterMeasure := by
    apply OuterMeasure.le_pi.mpr
    intro t _
    exact (OuterMeasure.pi_pi_le _ _).trans
      (Finset.prod_le_prod' fun i _ => h i (t i))
  exact ho s

lemma standardGaussianPDF_le_one (x : ℝ) : gaussianPDF 0 1 x ≤ 1 := by
  apply ENNReal.ofReal_le_one.mpr
  change (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(x - 0)^2 / (2 * 1)) ≤ 1
  simp only [mul_one, sub_zero]
  have hs : 1 ≤ Real.sqrt (2 * Real.pi) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hi : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  have he : Real.exp (-(x^2) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans (by simpa using hi)

lemma standardGaussian_le_volume : gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero]
  conv_rhs => rw [← withDensity_one (μ := (volume : Measure ℝ))]
  exact withDensity_mono (ae_of_all _ standardGaussianPDF_le_one)

lemma iidGaussian_le_volume (ι : Type*) [Fintype ι] :
    Measure.pi (fun _ : ι => gaussianReal 0 1) ≤ (volume : Measure (ι → ℝ)) :=
  finiteProduct_le fun _ => standardGaussian_le_volume

lemma gaussian_square_map_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (Matrix.toLin' M) ≤
      ENNReal.ofReal (|M.det|⁻¹) • (volume : Measure (ι → ℝ)) := by
  have hmap := Measure.map_mono (iidGaussian_le_volume ι)
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hM, abs_inv] at hmap
  exact hmap

open Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder

lemma rectangularGaussian_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ) :
    (stdGaussian (EuclideanSpace ℝ κ)).map
      (LinearMap.toContinuousLinearMap A.toEuclideanLin) =
      multivariateGaussian 0 (A * Aᵀ) := by
  have hA : (A * Aᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose A
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian, map_zero]
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
      covarianceBilin_multivariateGaussian hA, innerSL_apply_apply ℝ,
      ← LinearMap.adjoint_toContinuousLinearMap,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
      Matrix.conjTranspose_eq_transpose_of_trivial, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial]
    change (Aᵀ *ᵥ y) ⬝ᵥ (Aᵀ *ᵥ x) = x ⬝ᵥ (A * Aᵀ) *ᵥ y
    rw [dotProduct_comm (Aᵀ *ᵥ y)]
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose]
    simp [Matrix.dotProduct_mulVec]

lemma rectangularGaussian_squareRoot_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).map (Matrix.toLin' A) =
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map
      (Matrix.toLin' (CFC.sqrt (A * Aᵀ))) := by
  have he := congrArg (fun μ : Measure (EuclideanSpace ℝ ι) => μ.map ofLp)
    (rectangularGaussian_eq A)
  unfold multivariateGaussian at he
  simp only [zero_add] at he
  rw [← map_pi_eq_stdGaussian, ← map_pi_eq_stdGaussian] at he
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at he
  exact he

lemma gaussian_rectangular_map_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ)
    (hA : (A * Aᵀ).det ≠ 0) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).map (Matrix.toLin' A) ≤
      ENNReal.ofReal ((Real.sqrt (A * Aᵀ).det)⁻¹) • (volume : Measure (ι → ℝ)) := by
  have hpos : (A * Aᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose A
  have hd : (CFC.sqrt (A * Aᵀ)).det = Real.sqrt (A * Aᵀ).det := by
    rw [hpos.det_sqrt, RCLike.sqrt_of_nonneg hpos.det_nonneg]
    rfl
  have hD : (CFC.sqrt (A * Aᵀ)).det ≠ 0 := by
    rw [hd]
    exact Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hpos.det_nonneg hA.symm)
  rw [rectangularGaussian_squareRoot_eq]
  convert gaussian_square_map_le (CFC.sqrt (A * Aᵀ)) hD using 1
  rw [hd, abs_of_nonneg (Real.sqrt_nonneg _)]

lemma gaussian_rectangular_box_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ)
    (hA : (A * Aᵀ).det ≠ 0) (η : ℝ) (hη : 0 ≤ η) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1))
      {x | ∀ i, |(A *ᵥ x) i| ≤ η} ≤
      ENNReal.ofReal ((Real.sqrt (A * Aᵀ).det)⁻¹ * (2 * η) ^ Fintype.card ι) := by
  have he : {x : κ → ℝ | ∀ i, |(A *ᵥ x) i| ≤ η} =
      (Matrix.toLin' A) ⁻¹' (Set.univ.pi fun _ : ι => Set.Icc (-η) η) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      forall_true_left, Matrix.toLin'_apply, Set.mem_Icc, abs_le]
  rw [he, ← Measure.map_apply (Matrix.toLin' A).continuous_of_finiteDimensional.measurable
    (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc)]
  refine (gaussian_rectangular_map_le A hA _).trans_eq ?_
  rw [Measure.smul_apply, smul_eq_mul, volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, sub_neg_eq_add, ← two_mul, Finset.prod_const,
    Finset.card_univ]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]

lemma gaussian_multirow_box_le {ρ ι κ : Type*} [Fintype ρ] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ)
    (hA : (A * Aᵀ).det ≠ 0) (η : ℝ) (hη : 0 ≤ η) :
    (Measure.pi (fun _ : ρ => Measure.pi (fun _ : κ => gaussianReal 0 1)))
      {X | ∀ r i, |(A *ᵥ X r) i| ≤ η} ≤
      ENNReal.ofReal (((Real.sqrt (A * Aᵀ).det)⁻¹ * (2 * η)^Fintype.card ι)^Fintype.card ρ) := by
  have he : {X : ρ → κ → ℝ | ∀ r i, |(A *ᵥ X r) i| ≤ η} =
      Set.univ.pi (fun _ : ρ => {x : κ → ℝ | ∀ i, |(A *ᵥ x) i| ≤ η}) := by
    ext x
    simp
  rw [he, Measure.pi_pi, ENNReal.ofReal_pow (by positivity)]
  simpa using Finset.prod_le_prod' (s := (Finset.univ : Finset ρ))
    (fun _ _ => gaussian_rectangular_box_le A hA η hη)

end Support

namespace Support
open Matrix WithLp
open scoped MatrixOrder RealInnerProductSpace

lemma gaussian_multirow_box_le_extended {ρ ι κ : Type*} [Fintype ρ] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (hρ : 0 < Fintype.card ρ)
    (A : Matrix ι κ ℝ) (η : ℝ) (hη : 0 < η) :
    (Measure.pi (fun _ : ρ => Measure.pi (fun _ : κ => gaussianReal 0 1)))
      {X | ∀ r i, |(A *ᵥ X r) i| ≤ η} ≤
      (ENNReal.ofReal (Real.sqrt (A * Aᵀ).det))⁻¹ ^ Fintype.card ρ *
        ENNReal.ofReal ((2*η)^(Fintype.card ι * Fintype.card ρ)) := by
  by_cases hA : (A * Aᵀ).det ≠ 0
  · refine (gaussian_multirow_box_le A hA η hη.le).trans_eq ?_
    have hpos : (A * Aᵀ).PosSemidef := by
      simpa using Matrix.posSemidef_self_mul_conjTranspose A
    have hd : 0 < Real.sqrt (A * Aᵀ).det := Real.sqrt_pos.mpr
      (lt_of_le_of_ne hpos.det_nonneg hA.symm)
    rw [mul_pow, ← pow_mul, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos hd]
  · simp only [not_ne_iff] at hA
    rw [hA, Real.sqrt_zero, ENNReal.ofReal_zero, ENNReal.inv_zero,
      ENNReal.top_pow hρ.ne', ENNReal.top_mul (by positivity)]
    exact le_top

lemma rowMatrix_gram {q d : ℕ} (f : Fin q → EuclideanSpace ℝ (Fin d)) :
    rowMatrix f * (rowMatrix f)ᵀ = Matrix.gram ℝ f := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowMatrix, Matrix.gram_apply,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro k _
  ring

end Support

end Projection
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ProjectionMoments
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
namespace Projection
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Support
open Metric Matrix WithLp

lemma projectVector_rowMatrix {k q d : ℕ} (X : Fin k → Fin d → ℝ)
    (v : Fin q → EuclideanSpace ℝ (Fin d)) (r : Fin k) (i : Fin q) :
    projectVector X (v i) r = (rowMatrix v *ᵥ X r) i := by
  simp only [projectVector, mulVec, dotProduct, rowMatrix]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma measurable_replicated {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {m : ℕ}
    (f : β × α → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun x : β × (Fin m → α) => ∏ i, f (x.1,x.2 i)) := by
  apply Finset.measurable_prod
  intro i _
  exact hf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

end Support

open Support _root_.OAI.KernelPotential.Geometry
lemma measurable_zero_kernel {k d : ℕ} (η : ℝ) :
    Measurable (fun x : (Fin k → Fin d → ℝ) × EuclideanSpace ℝ (Fin d) =>
      boxKernel η (projectVector x.1 x.2) 0) :=
  (measurable_boxKernel η).comp
    (continuous_projectVector.measurable.prodMk measurable_const)

end Projection
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_MixedProjection
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
namespace Projection
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open Support _root_.OAI.KernelPotential.Geometry

lemma fixed_center_replicas {k q d : ℕ} (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (v : Fin q → EuclideanSpace ℝ (Fin d)) :
    (∫⁻ X, ∏ i, boxKernel η (projectVector X (v i)) 0 ∂gaussianRows k d) ≤
      gramInverseProduct k v := by
  classical
  let D := {X : Fin k → Fin d → ℝ | ∀ r i, |(rowMatrix v *ᵥ X r) i| ≤ η}
  have hD : MeasurableSet D := by
    dsimp only [D]
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro r
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  have hpoint : ∀ X, (∏ i, boxKernel η (projectVector X (v i)) 0) ≤
      D.indicator (fun _ => boxScale k η ^ q) X := by
    intro X
    by_cases hX : X ∈ D
    · rw [indicator_of_mem hX]
      calc
        _ ≤ ∏ _i : Fin q, boxScale k η := Finset.prod_le_prod'
          (fun _ _ => boxKernel_le η _ _)
        _ = _ := by simp
    · rw [indicator_of_notMem hX]
      change ¬ ∀ r i, |(rowMatrix v *ᵥ X r) i| ≤ η at hX
      push Not at hX
      obtain ⟨r,i,hi⟩ := hX
      apply le_of_eq
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      by_contra hh
      have hm := boxKernel_ne_zero_mem hh
      have hx := hm r
      simp only [Pi.zero_apply, zero_sub, abs_neg] at hx
      rw [projectVector_rowMatrix] at hx
      exact (not_le.mpr hi) hx
  calc
    _ ≤ ∫⁻ X, D.indicator (fun _ => boxScale k η ^ q) X ∂gaussianRows k d := lintegral_mono hpoint
    _ = boxScale k η ^ q * gaussianRows k d D := by rw [lintegral_indicator hD,lintegral_const,Measure.restrict_apply_univ]
    _ ≤ boxScale k η ^ q * ((ENNReal.ofReal (Real.sqrt (rowMatrix v * (rowMatrix v)ᵀ).det))⁻¹^k *
        ENNReal.ofReal ((2*η)^(q*k))) := by
      apply mul_le_mul_right
      simpa only [gaussianRows,Fintype.card_fin] using
        gaussian_multirow_box_le_extended (ρ := Fin k) (by simpa using hk) (rowMatrix v) η hη
    _ = gramInverseProduct k v := by
      rw [rowMatrix_gram, ← gramInverseProduct_eq_inverseVolume]
      have hc : boxScale k η ^ q * ENNReal.ofReal ((2*η)^(q*k)) = 1 := by
        rw [Nat.mul_comm q k,pow_mul,ENNReal.ofReal_pow (by positivity),boxScale,
          ← mul_pow, ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top,one_pow]
      calc
        _ = gramInverseProduct k v * (boxScale k η ^ q * ENNReal.ofReal ((2*η)^(q*k))) := by ac_rfl
        _ = _ := by rw [hc,mul_one]

lemma fixed_center_moment {α : Type*} [MeasurableSpace α] {k d : ℕ}
    (μ : Measure α) [SigmaFinite μ] (a : α → EuclideanSpace ℝ (Fin d))
    (ha : Measurable a) (hk : 0 < k) (p : ℕ) (M : ℝ≥0∞)
    (hcond : ∀ V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
      (V : Set (EuclideanSpace ℝ (Fin d))).Nonempty →
      Module.finrank ℝ V.direction ≤ p →
      (∫⁻ z,(ENNReal.ofReal (infDist (a z) (V : Set (EuclideanSpace ℝ (Fin d)))))⁻¹^k ∂μ) ≤ M)
    (q : ℕ) (hq : q ≤ p+1) (η : ℝ) (hη : 0 < η) :
    (∫⁻ X, (∫⁻ z,boxKernel η (projectVector X (a z)) 0 ∂μ)^q ∂gaussianRows k d) ≤ M^q := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have hm : Measurable (fun x : (Fin k → Fin d → ℝ) × α =>
      boxKernel η (projectVector x.1 (a x.2)) 0) :=
    (measurable_zero_kernel (k := k) (d := d) η).comp
      (f := fun x : (Fin k → Fin d → ℝ) × α => (x.1,a x.2))
      (measurable_fst.prodMk (ha.comp measurable_snd))
  have hrep := measurable_replicated (m := q) _ hm
  calc
    _ = ∫⁻ X, ∫⁻ z : Fin q → α, ∏ i,boxKernel η (projectVector X (a (z i))) 0
        ∂Measure.pi (fun _ => μ) ∂gaussianRows k d := by
      apply lintegral_congr
      intro X
      exact (lintegral_pi_product μ _ (hm.comp (measurable_const.prodMk measurable_id)) q).symm
    _ = ∫⁻ z : Fin q → α, ∫⁻ X, ∏ i,boxKernel η (projectVector X (a (z i))) 0
        ∂gaussianRows k d ∂Measure.pi (fun _ => μ) := lintegral_lintegral_swap hrep.aemeasurable
    _ ≤ ∫⁻ z : Fin q → α, gramInverseProduct k (fun i => a (z i)) ∂Measure.pi (fun _ => μ) :=
      lintegral_mono (fun z => fixed_center_replicas hk η hη _)
    _ ≤ M^q := by
      simpa only [sub_zero] using lintegral_gramInverseProduct_le μ a ha k p M hcond q hq 0

lemma fresh_rows_kernel_le {k d : ℕ} (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (x : EuclideanSpace ℝ (Fin d)) :
    (∫⁻ Z, boxKernel η (projectVector Z x) 0 ∂gaussianRows k d) ≤
      (ENNReal.ofReal ‖x‖)⁻¹^k := by
  have h := fixed_center_replicas hk η hη (fun _ : Fin 1 => x)
  have he : gramInverseProduct k (fun _ : Fin 1 => x) = (ENNReal.ofReal ‖x‖)⁻¹^k := by
    simp only [gramInverseProduct, Fin.prod_univ_one]
    rw [show (0 : Fin 1) = ⊥ from rfl, gramSchmidt_bot]
  simpa only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, he] using h

lemma auxiliary_average_le {k d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [SigmaFinite μ] (hk : 0 < k) (η : ℝ) (hη : 0 < η) (X : Fin k → Fin d → ℝ) :
    (∫⁻ Z,mixedCubeAverage μ η X Z ∂gaussianRows k d) ≤
      ∫⁻ x,boxKernel η (projectVector X x) 0 * (ENNReal.ofReal ‖x‖)⁻¹^k ∂μ := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have hm : Measurable (fun x : (Fin k → Fin d → ℝ) × EuclideanSpace ℝ (Fin d) =>
      boxKernel η (projectVector X x.2) 0 * boxKernel η (projectVector x.1 x.2) 0) :=
    ((measurable_zero_kernel (k := k) (d := d) η).comp
      (f := fun x : (Fin k → Fin d → ℝ) × EuclideanSpace ℝ (Fin d) => (X,x.2))
      (measurable_const.prodMk measurable_snd)).mul
      (measurable_zero_kernel (k := k) (d := d) η)
  unfold mixedCubeAverage
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_mono
  intro x
  dsimp only
  have hmX : Measurable (fun Z : Fin k → Fin d → ℝ => boxKernel η (projectVector Z x) 0) :=
    (measurable_zero_kernel (k := k) (d := d) η).comp
      (f := fun Z : Fin k → Fin d → ℝ => (Z,x)) (measurable_id.prodMk measurable_const)
  rw [lintegral_const_mul _ hmX]
  exact mul_le_mul_right (fresh_rows_kernel_le hk η hη x) _

theorem mixed_fixed_origin_moment {k d n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [SigmaFinite μ]
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hk : 0 < k) (hn : 2*k < n)
    (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ 2)
    (hballB : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (B*r^(2*k)))
    (hballD : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (D*r^n))
    (L : ℕ) (hDB : D ≤ B*2^L) (η : ℝ) (hη : 0 < η) :
    (∫⁻ X, (∫⁻ Z, mixedCubeAverage μ η X Z ∂gaussianRows k d)^k ∂gaussianRows k d) ≤
      ENNReal.ofReal ((9^(k-1)*3^n*2^(n+2*k+2))*B*((L:ℝ)+2))^k := by
  let w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x => (ENNReal.ofReal ‖x‖)⁻¹^k
  have hw : Measurable w := measurable_norm.ennreal_ofReal.inv.pow_const _
  have hz : ∀ᵐ x ∂μ, ‖x‖ ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using ball_bound_zero_null μ (by omega : 0 < 2*k) hB hballB
  have : SigmaFinite (μ.withDensity w) := SigmaFinite.withDensity_of_ne_top (by
    filter_upwards [hz] with x hx
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by
      exact (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (norm_nonneg x) hx.symm)).ne')))
  let M : ℝ≥0∞ := ENNReal.ofReal ((9^(k-1)*3^n*2^(n+2*k+2))*B*((L:ℝ)+2))
  have hcond : ∀ V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
      (V : Set (EuclideanSpace ℝ (Fin d))).Nonempty → Module.finrank ℝ V.direction ≤ k-1 →
      (∫⁻ x,(ENNReal.ofReal (infDist x (V : Set (EuclideanSpace ℝ (Fin d)))))⁻¹^k
        ∂μ.withDensity w) ≤ M := by
    intro V hV hdim
    have hg : Measurable (fun x : EuclideanSpace ℝ (Fin d) =>
        (ENNReal.ofReal (infDist x (V : Set (EuclideanSpace ℝ (Fin d)))))⁻¹^k) :=
      (continuous_infDist_pt _).measurable.ennreal_ofReal.inv.pow_const _
    rw [lintegral_withDensity_eq_lintegral_mul μ hw hg]
    change (∫⁻ x, (ENNReal.ofReal ‖x‖)⁻¹^k *
      (ENNReal.ofReal (infDist x (V : Set (EuclideanSpace ℝ (Fin d)))))⁻¹^k ∂μ) ≤ M
    apply (mixed_integral_logarithmic μ hB hD hk hn hsupport hballB hballD V hV hdim L hDB).trans
    apply ENNReal.ofReal_le_ofReal
    have hp : (9:ℝ)^(Module.finrank ℝ V.direction) ≤ 9^(k-1) :=
      pow_le_pow_right₀ (by norm_num) hdim
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by positivity))
        (by positivity)) hB) (by positivity)
  calc
    _ ≤ ∫⁻ X, (∫⁻ x,boxKernel η (projectVector X x) 0 * w x ∂μ)^k ∂gaussianRows k d := by
      apply lintegral_mono
      intro X
      exact pow_le_pow_left' (auxiliary_average_le μ hk η hη X) k
    _ = ∫⁻ X,(∫⁻ x,boxKernel η (projectVector X x) 0 ∂μ.withDensity w)^k ∂gaussianRows k d := by
      apply lintegral_congr
      intro X
      congr 1
      have hg : Measurable (fun x : EuclideanSpace ℝ (Fin d) => boxKernel η (projectVector X x) 0) :=
        (measurable_zero_kernel (k := k) (d := d) η).comp
          (f := fun x : EuclideanSpace ℝ (Fin d) => (X,x)) (measurable_const.prodMk measurable_id)
      rw [lintegral_withDensity_eq_lintegral_mul μ hw hg]
      apply lintegral_congr
      intro x
      exact mul_comm _ _
    _ ≤ M^k := fixed_center_moment (μ.withDensity w) id measurable_id hk (k-1) M hcond k (by omega) η hη

end Projection

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Reweighting
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
namespace Reweight
open Coercivity Sphere

lemma rho_ac {d : ℕ} (ν : Measure (Ambient d)) : rho ν ≪ ν :=
  withDensity_absolutelyContinuous _ _

lemma local_lower_J {d : ℕ} (ν : Measure (Ambient d)) (z : Ambient d) {r : ℝ}
    (hr : 0 < r) (s : Ambient d) (hs : s ∈ ball z r) :
    ν (ball z r) / ENNReal.ofReal ((2*r)^(2*(d/16))) ≤ J ν s := by
  rw [div_eq_mul_inv]
  calc
    _ = ∫⁻ u in ball z r, (ENNReal.ofReal ((2*r)^(2*(d/16))))⁻¹ ∂ν := by simp [mul_comm]
    _ ≤ ∫⁻ u in ball z r,(ENNReal.ofReal ‖u-s‖)⁻¹^(2*(d/16)) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
      rw [ENNReal.ofReal_pow (by positivity),ENNReal.inv_pow]
      have hdist : ‖u-s‖ ≤ 2*r := by
        rw [← dist_eq_norm]
        exact le_of_lt (calc dist u s ≤ dist u z+dist z s := dist_triangle _ _ _
          _ < r+r := add_lt_add hu (by simpa [dist_comm] using hs)
          _ = 2*r := by ring)
      exact pow_le_pow_left₀ zero_le (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hdist)) _
    _ ≤ J ν s := lintegral_mono' Measure.restrict_le_self (le_refl _)

lemma rho_ball {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (z : Ambient d) {r : ℝ} (hr : 0 < r) :
    rho ν (ball z r) ≤ ENNReal.ofReal ((2*r)^(2*(d/16))) := by
  by_cases hm : ν (ball z r) = 0
  · have hz := rho_ac ν hm
    rw [hz]; exact bot_le
  have hmt : ν (ball z r) ≠ ∞ := measure_ne_top _ _
  unfold rho
  rw [withDensity_apply _ measurableSet_ball]
  calc
    _ ≤ ∫⁻ s in ball z r, ENNReal.ofReal ((2*r)^(2*(d/16))) / ν (ball z r) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with s hs
      have h := ENNReal.inv_le_inv.mpr (local_lower_J ν z hr s hs)
      simpa only [ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inr hm)] using h
    _ = _ := by
      simp only [lintegral_const,Measure.restrict_apply_univ]
      rw [ENNReal.div_mul_cancel hm hmt]

lemma rho_le {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) : rho ν ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))) • ν := by
  intro E
  unfold rho
  rw [withDensity_apply' _ E,Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∫⁻ s in E, ENNReal.ofReal ((2:ℝ)^(2*(d/16))) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hν] with s hs
      have h := ENNReal.inv_le_inv.mpr (lower_J_on_sphere ν hν s hs)
      simpa only [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),ENNReal.inv_pow,
        show (ENNReal.ofReal (1/2:ℝ))⁻¹ = ENNReal.ofReal (2:ℝ) by rw [← ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num,
        ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)] using h
    _ = _ := by simp

lemma rho_bounded {d : ℕ} (hd : 0 < d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) :
    rho ν ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*H) • sphereProbability d := by
  have hac : ν ≪ sphereProbability d := Measure.absolutelyContinuous_of_le_smul hν
  have hsupport : ∀ᵐ s ∂ν, ‖s‖=1 := hac.ae_le (ae_unit_norm hd)
  calc
    rho ν ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))) • ν := rho_le ν hsupport
    _ ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))) • (ENNReal.ofReal H • sphereProbability d) := by
      intro E
      simp only [Measure.smul_apply,smul_eq_mul]
      gcongr; exact hν E
    _ = _ := by rw [smul_smul,← ENNReal.ofReal_mul' hH.le]

lemma rho_finite {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) : IsFiniteMeasure (rho ν) := by
  have := Measure.smul_finite ν (c := ENNReal.ofReal ((2:ℝ)^(2*(d/16)))) ENNReal.ofReal_ne_top
  exact isFiniteMeasure_of_le _ (rho_le ν hν)

lemma rho_two_ball_bounds {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (z : Ambient d) {r : ℝ} (hr : 0 < r) :
    rho ν (ball z r) ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*r^(2*(d/16))) ∧
    rho ν (ball z r) ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*H*(9*3^d)*r^(d-1)) := by
  refine ⟨by simpa only [mul_pow] using rho_ball ν z hr,?_⟩
  calc
    _ ≤ (ENNReal.ofReal ((2:ℝ)^(2*(d/16))*H) • sphereProbability d) (ball z r) := rho_bounded (by omega) ν hH hν _
    _ = ENNReal.ofReal ((2:ℝ)^(2*(d/16))*H) * sphereProbability d (ball z r) := by rw [Measure.smul_apply,smul_eq_mul]
    _ ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*H) * ENNReal.ofReal ((9*3^d:ℝ)*r^(d-1)) := by gcongr; exact cap_bound (by omega) z hr
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

lemma centered_ball {d : ℕ} (ν : Measure (Ambient d)) (s z : Ambient d) (r : ℝ) :
    centeredRho ν s (ball z r)=rho ν (ball (z+s) r) := by
  rw [centeredRho,Measure.map_apply (f := fun u : Ambient d => u-s) (measurable_id.sub measurable_const) measurableSet_ball]
  congr 1
  ext u
  simp only [mem_preimage,mem_ball,dist_eq_norm]
  abel_nf

lemma centered_finite {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) (s : Ambient d) : IsFiniteMeasure (centeredRho ν s) := by
  have := rho_finite ν hν
  unfold centeredRho
  infer_instance

lemma centered_support {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) (s : Ambient d) (hs : ‖s‖=1) :
    ∀ᵐ u ∂centeredRho ν s, ‖u‖ ≤ 2 := by
  apply (ae_map_iff (measurable_id.sub measurable_const).aemeasurable
    (measurableSet_le measurable_norm measurable_const)).mpr
  filter_upwards [(rho_ac ν).ae_le hν] with u hu
  calc ‖u-s‖ ≤ ‖u‖+‖s‖ := norm_sub_le _ _
    _ = 2 := by rw [hu,hs]; norm_num

lemma centered_mixed_moment {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1)
    (L : ℕ) (hL : H*(9*3^d:ℝ) ≤ 2^L) (η : ℝ) (hη : 0 < η) :
    (∫⁻ X, (∫⁻ Z, Projection.mixedCubeAverage (centeredRho ν s) η X Z
      ∂Projection.Support.gaussianRows (d/16) d)^(d/16)
      ∂Projection.Support.gaussianRows (d/16) d) ≤
      ENNReal.ofReal ((9^(d/16-1)*3^(d-1)*2^((d-1)+4*(d/16)+2):ℝ)*((L:ℝ)+2))^(d/16) := by
  have hac : ν ≪ sphereProbability d := Measure.absolutelyContinuous_of_le_smul hν
  have hsupport := hac.ae_le (ae_unit_norm (by omega : 0 < d))
  have := centered_finite ν hsupport s
  have hB (z : Ambient d) (r : ℝ) (hr : 0 < r) :
      centeredRho ν s (ball z r) ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*r^(2*(d/16))) := by
    rw [centered_ball]
    exact (rho_two_ball_bounds hd ν hH hν (z+s) hr).1
  have hD (z : Ambient d) (r : ℝ) (hr : 0 < r) :
      centeredRho ν s (ball z r) ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*H*(9*3^d)*r^(d-1)) := by
    rw [centered_ball]
    exact (rho_two_ball_bounds hd ν hH hν (z+s) hr).2
  have hDB : (2:ℝ)^(2*(d/16))*H*(9*3^d) ≤ 2^(2*(d/16))*2^L := by
    nlinarith [mul_le_mul_of_nonneg_left hL (by positivity : (0:ℝ) ≤ 2^(2*(d/16)))]
  have h := Projection.mixed_fixed_origin_moment (centeredRho ν s) (B := (2:ℝ)^(2*(d/16)))
    (D := (2:ℝ)^(2*(d/16))*H*(9*3^d)) (by positivity) (by positivity)
    (by omega : 0 < d/16) (by omega : 2*(d/16) < d-1)
    (centered_support ν hsupport s hs) hB hD L hDB η hη
  convert h using 3
  congr 1
  have he : (d-1)+4*(d/16)+2=((d-1)+2*(d/16)+2)+2*(d/16) := by omega
  rw [he,pow_add]
  ring

end Reweight
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoiseLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection.Support Projection Reweight

lemma boxScale_ne_top (k : ℕ) {η : ℝ} (hη : 0 < η) : boxScale k η ≠ ∞ := by
  unfold boxScale
  exact ENNReal.inv_ne_top.mpr (by positivity)

end KernelPotential.Noise

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_EntropyDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential.DriftTools

lemma log_young {u v a : ℝ} (hu : 0 ≤ u) (hv : 0 < v) (ha : 0 < a) :
    u*Real.log v ≤ u*Real.log u-u*Real.log a-u+a*v := by
  by_cases hu0 : u=0
  · simp only [hu0,zero_mul,sub_zero,zero_add]
    positivity
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have h := Real.log_le_sub_one_of_pos (div_pos (mul_pos ha hv) hup)
  rw [Real.log_div (mul_ne_zero ha.ne' hv.ne') hu0,Real.log_mul ha.ne' hv.ne'] at h
  have hh := mul_le_mul_of_nonneg_left h hu
  have hc : u*(a*v/u-1)=a*v-u := by field_simp
  rw [hc] at hh
  nlinarith

lemma weighted_log_moment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (u v : α → ℝ) (hu : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hv : ∀ᵐ x ∂μ, 0 < v x) (hui : Integrable u μ) (hvi : Integrable v μ)
    (huli : Integrable (fun x => u x*Real.log (u x)) μ)
    (huvi : Integrable (fun x => u x*Real.log (v x)) μ)
    {r G : ℝ} (hr : 0 < r) (hG : 0 < G)
    (hur : ∫ x,u x ∂μ=r) (hvG : (∫ x,v x ∂μ) ≤ G) :
    (∫ x,u x*Real.log (v x) ∂μ) ≤
      (∫ x,u x*Real.log (u x) ∂μ)-r*Real.log (r/G) := by
  have hpoint : ∀ᵐ x ∂μ,u x*Real.log (v x) ≤
      u x*Real.log (u x)-u x*Real.log (r/G)-u x+(r/G)*v x := by
    filter_upwards [hu,hv] with x hx hy
    exact log_young hx hy (div_pos hr hG)
  have hright : Integrable (fun x => u x*Real.log (u x)-u x*Real.log (r/G)-u x+(r/G)*v x) μ :=
    ((huli.sub (hui.mul_const _)).sub hui).add (hvi.const_mul _)
  have h := integral_mono_ae huvi hright hpoint
  rw [integral_add (f := fun x => u x*Real.log (u x)-u x*Real.log (r/G)-u x)
      (g := fun x => (r/G)*v x) ((huli.sub (hui.mul_const _)).sub hui) (hvi.const_mul _),
    integral_sub (f := fun x => u x*Real.log (u x)-u x*Real.log (r/G)) (g := u)
      (huli.sub (hui.mul_const _)) hui,
    integral_sub (f := fun x => u x*Real.log (u x)) (g := fun x => u x*Real.log (r/G)) huli (hui.mul_const _),
    integral_mul_const,integral_const_mul,hur] at h
  have hb := mul_le_mul_of_nonneg_left hvG (div_nonneg hr.le hG.le)
  rw [div_mul_cancel₀ _ hG.ne'] at hb
  linarith

lemma integral_log_le_log_of_integral_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (v : α → ℝ)
    (hv : ∀ᵐ x ∂μ,0 < v x) (hvi : Integrable v μ)
    (hvlog : Integrable (fun x => Real.log (v x)) μ)
    {a : ℝ} (ha : 0 < a) (hva : (∫ x,v x ∂μ) ≤ a) :
    (∫ x,Real.log (v x) ∂μ) ≤ Real.log a := by
  have hpoint : ∀ᵐ x ∂μ,Real.log (v x) ≤ v x/a-1+Real.log a := by
    filter_upwards [hv] with x hx
    have h := Real.log_le_sub_one_of_pos (div_pos hx ha)
    rw [Real.log_div hx.ne' ha.ne'] at h
    linarith
  have h := integral_mono_ae hvlog (((hvi.div_const a).sub (integrable_const 1)).add (integrable_const (Real.log a))) hpoint
  have he : (∫ x,v x/a-1+Real.log a ∂μ) = (∫ x,v x ∂μ)/a-1+Real.log a := by
    rw [integral_add (f := fun x => v x/a-1) (g := fun _ => Real.log a)
        ((hvi.div_const a).sub (integrable_const 1)) (integrable_const _),
      integral_sub (f := fun x => v x/a) (g := fun _ => (1:ℝ)) (hvi.div_const a) (integrable_const 1),
      integral_div]
    simp
  change (∫ x,Real.log (v x) ∂μ) ≤ (∫ x,v x/a-1+Real.log a ∂μ) at h
  rw [he] at h
  have hb : (∫ x,v x ∂μ)/a ≤ 1 := (div_le_one ha).mpr hva
  linarith

lemma pow_one_add_le {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (1+x)^k ≤ 2^k*(1+x^k) := by
  have h : 1+x ≤ 2*max 1 x := by have := le_max_left (1:ℝ) x; have := le_max_right (1:ℝ) x; linarith
  calc
    _ ≤ (2*max 1 x)^k := pow_le_pow_left₀ (by positivity) h k
    _ = 2^k*(max 1 x)^k := mul_pow _ _ _
    _ ≤ 2^k*(1+x^k) := by
      gcongr
      rcases le_total x 1 with hh|hh
      · rw [max_eq_left hh,one_pow]; have := pow_nonneg hx k; linarith
      · rw [max_eq_right hh]; linarith

lemma integrable_of_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ) (hf : AEStronglyMeasurable f μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf hC

lemma integral_weighted_log_moment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (u g : α → ℝ)
    (hu : Measurable u) (hg : Measurable g)
    (hu0 : ∀ x,0 ≤ u x) (hu1 : ∀ x,u x ≤ 1)
    (hg0 : ∀ x,0 ≤ g x) {M G : ℝ} (hgM : ∀ x,g x ≤ M) (hG : 0 ≤ G)
    (k : ℕ) (hk : 0 < k) (hmoment : (∫ x,(g x)^k ∂μ) ≤ G^k) :
    (∫ x,u x*Real.log (1+g x) ∂μ) ≤
      -(∫ x,u x ∂μ)*Real.log (∫ x,u x ∂μ)/(k:ℝ) +
        (∫ x,u x ∂μ)*Real.log (4*(1+G)) := by
  let r : ℝ := ∫ x,u x ∂μ
  have hui : Integrable u μ := integrable_of_bounded μ u hu.aestronglyMeasurable (C := 1)
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hu0 x)]; exact hu1 x))
  have hr : 0 ≤ r := integral_nonneg hu0
  have hgMi : Integrable (fun x => (g x)^k) μ :=
    integrable_of_bounded μ _ (hg.pow_const k).aestronglyMeasurable (C := M^k)
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hg0 x) k)]; exact pow_le_pow_left₀ (hg0 x) (hgM x) k))
  have hv0 (x : α) : 0 < (1+g x)^k := pow_pos (by linarith [hg0 x]) _
  have hvi : Integrable (fun x => (1+g x)^k) μ :=
    integrable_of_bounded μ _ ((measurable_const.add hg).pow_const k).aestronglyMeasurable (C := (1+M)^k)
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_pos (hv0 x)]; exact pow_le_pow_left₀ (by linarith [hg0 x]) (by linarith [hgM x]) k))
  have hlogi : Integrable (fun x => Real.log (1+g x)) μ :=
    integrable_of_bounded μ _ (measurable_const.add hg).log.aestronglyMeasurable (C := Real.log (1+M))
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith [hg0 x]))]
        exact Real.log_le_log (by linarith [hg0 x]) (by linarith [hgM x])))
  have huli : Integrable (fun x => u x*Real.log (u x)) μ := by
    obtain ⟨C,hC⟩ := ((isCompact_Icc (a := (0:ℝ)) (b := 1)).image Real.continuous_mul_log).isBounded.exists_norm_le
    exact integrable_of_bounded μ _ (Real.continuous_mul_log.measurable.comp hu).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => hC _ (mem_image_of_mem _ ⟨hu0 x,hu1 x⟩)))
  have huli0 : (∫ x,u x*Real.log (u x) ∂μ) ≤ 0 := integral_nonpos (fun x =>
    mul_nonpos_of_nonneg_of_nonpos (hu0 x) (Real.log_nonpos (hu0 x) (hu1 x)))
  have huwlog : Integrable (fun x => u x*Real.log (1+g x)) μ :=
    hlogi.bdd_mul hu.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hu0 x)]; exact hu1 x))
  have huvi : Integrable (fun x => u x*Real.log ((1+g x)^k)) μ := by
    simp_rw [Real.log_pow]
    convert huwlog.const_mul (k:ℝ) using 1
    ext x
    ring
  by_cases hr0 : r=0
  · have huae : u =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hu0) hui).mp hr0
    have hz : (∫ x,u x*Real.log (1+g x) ∂μ)=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [huae] with x hx
      simp [hx]
    change _ ≤ -r*Real.log r/(k:ℝ)+r*Real.log (4*(1+G))
    rw [hz,hr0]; simp
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hvG : (∫ x,(1+g x)^k ∂μ) ≤ (4*(1+G))^k := by
    calc
      _ ≤ ∫ x,2^k*(1+(g x)^k) ∂μ := integral_mono hvi
        (((integrable_const 1).add hgMi).const_mul _) (fun x => pow_one_add_le (hg0 x) k)
      _ = 2^k*(1+∫ x,(g x)^k ∂μ) := by rw [integral_const_mul,integral_add (integrable_const 1) hgMi]; simp
      _ ≤ 2^k*(1+G^k) := by gcongr
      _ ≤ 2^k*(2*(1+G)^k) := by gcongr; have h1 : (1:ℝ) ≤ (1+G)^k := one_le_pow₀ (by linarith); have h2 : G^k ≤ (1+G)^k := pow_le_pow_left₀ hG (by linarith) k; linarith
      _ ≤ 2^k*(2^k*(1+G)^k) := by gcongr; exact le_self_pow₀ (by norm_num) (by omega)
      _ = _ := by rw [mul_pow,show (4:ℝ)=2*2 by norm_num,mul_pow]; ring
  have h := weighted_log_moment μ u (fun x => (1+g x)^k)
    (Filter.Eventually.of_forall hu0) (Filter.Eventually.of_forall hv0) hui hvi huli huvi hrp
    (by positivity : 0 < (4*(1+G))^k) rfl hvG
  have he : (∫ x,u x*Real.log ((1+g x)^k) ∂μ) = (k:ℝ)*(∫ x,u x*Real.log (1+g x) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Real.log_pow]; ring
  rw [he, Real.log_div hrp.ne' (by positivity), Real.log_pow] at h
  change _ ≤ -r*Real.log r/(k:ℝ)+r*Real.log (4*(1+G))
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  apply (mul_le_mul_iff_right₀ hkR).mp
  have heq : (k:ℝ)*(-r*Real.log r/(k:ℝ)+r*Real.log (4*(1+G))) =
      -r*Real.log r+r*((k:ℝ)*Real.log (4*(1+G))) := by field_simp
  rw [heq]
  nlinarith

end KernelPotential.DriftTools

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Compensation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential.DriftTools
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

lemma fresh_weighted_log_moment {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : α → ℝ) (m : α × β → ℝ≥0∞)
    (hu : Measurable u) (hm : Measurable m)
    (hu0 : ∀ a,0 ≤ u a) (hu1 : ∀ a,u a ≤ 1)
    {B G c : ℝ} (hB : 0 ≤ B) (hG : 0 ≤ G) (hc : 0 ≤ c)
    (hmB : ∀ a b,m (a,b) ≤ ENNReal.ofReal B) (k : ℕ) (hk : 0 < k)
    (hmoment : (∫⁻ a,(∫⁻ b,m (a,b) ∂ν)^k ∂μ) ≤ ENNReal.ofReal G^k) :
    (∫ a,u a*(∫ b,Real.log (1+c*(m (a,b)).toReal) ∂ν) ∂μ) ≤
      -(∫ a,u a ∂μ)*Real.log (∫ a,u a ∂μ)/(k:ℝ)+
        (∫ a,u a ∂μ)*Real.log (4*(1+c*G)) := by
  let g : α → ℝ := fun a => (∫⁻ b,m (a,b) ∂ν).toReal
  have hgE : Measurable (fun a => ∫⁻ b,m (a,b) ∂ν) := Measurable.lintegral_prod_right hm
  have hg : Measurable g := hgE.ennreal_toReal
  have hmt (a : α) (b : β) : m (a,b) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmB a b)
  have hgBE (a : α) : (∫⁻ b,m (a,b) ∂ν) ≤ ENNReal.ofReal B := by
    calc
      _ ≤ ∫⁻ _b,ENNReal.ofReal B ∂ν := lintegral_mono (hmB a)
      _ = _ := by simp
  have hgt (a : α) : (∫⁻ b,m (a,b) ∂ν) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hgBE a)
  have hgB (a : α) : g a ≤ B := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hgBE a)).trans_eq (ENNReal.toReal_ofReal hB)
  have hmBr (a : α) (b : β) : (m (a,b)).toReal ≤ B :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmB a b)).trans_eq (ENNReal.toReal_ofReal hB)
  have hfi (a : α) : Integrable (fun b => (m (a,b)).toReal) ν :=
    integrable_of_bounded ν _ ((hm.comp (measurable_const.prodMk measurable_id)).ennreal_toReal.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun b => by rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]; exact hmBr a b))
  have hgeq (a : α) : (∫ b,(m (a,b)).toReal ∂ν)=g a :=
    integral_toReal (hm.comp (measurable_const.prodMk measurable_id)).aemeasurable
      (Filter.Eventually.of_forall (fun b => (hmt a b).lt_top))
  have hgmoment : (∫ a,(c*g a)^k ∂μ) ≤ (c*G)^k := by
    have he : (∫ a,(g a)^k ∂μ) = (∫⁻ a,(∫⁻ b,m (a,b) ∂ν)^k ∂μ).toReal := by
      dsimp only [g]
      simp_rw [← ENNReal.toReal_pow]
      exact integral_toReal (hgE.pow_const k).aemeasurable
        (Filter.Eventually.of_forall (fun a => (ENNReal.pow_ne_top (hgt a)).lt_top))
    have hb : (∫ a,(g a)^k ∂μ) ≤ G^k := by
      rw [he]
      have h := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hmoment
      simpa only [ENNReal.toReal_pow,ENNReal.toReal_ofReal hG] using h
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hb (pow_nonneg hc k)
  have hcg : Measurable (fun a => c*g a) := measurable_const.mul hg
  have hpoint (a : α) : (∫ b,Real.log (1+c*(m (a,b)).toReal) ∂ν) ≤ Real.log (1+c*g a) := by
    have hvpos (b : β) : 0 < 1+c*(m (a,b)).toReal := by positivity
    have hvlog : Integrable (fun b => Real.log (1+c*(m (a,b)).toReal)) ν := by
      apply integrable_of_bounded ν _
        ((measurable_const.add (measurable_const.mul
          (hm.comp (measurable_const.prodMk measurable_id)).ennreal_toReal)).log.aestronglyMeasurable)
        (C := Real.log (1+c*B))
      filter_upwards [] with b
      dsimp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply, id_eq]
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith [mul_nonneg hc (ENNReal.toReal_nonneg (a := m (a,b))) ]))]
      exact Real.log_le_log (hvpos b) (by nlinarith [hmBr a b])
    apply integral_log_le_log_of_integral_le ν _
      (Filter.Eventually.of_forall hvpos) ((integrable_const 1).add ((hfi a).const_mul c))
      hvlog (by dsimp [g]; positivity)
    rw [integral_add (integrable_const 1) ((hfi a).const_mul c),integral_const_mul,hgeq]
    simp
  have hlogM : ∀ a b, ‖Real.log (1+c*(m (a,b)).toReal)‖ ≤ Real.log (1+c*B) := by
    intro a b
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith [mul_nonneg hc (ENNReal.toReal_nonneg (a := m (a,b))) ]))]
    exact Real.log_le_log (by positivity) (by nlinarith [hmBr a b])
  have hlogint : Integrable (fun t : α × β => Real.log (1+c*(m t).toReal)) (μ.prod ν) :=
    integrable_of_bounded _ _
      ((measurable_const.add (measurable_const.mul hm.ennreal_toReal)).log.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun t => hlogM t.1 t.2))
  have hlefti : Integrable (fun a => u a*(∫ b,Real.log (1+c*(m (a,b)).toReal) ∂ν)) μ :=
    hlogint.integral_prod_left.bdd_mul hu.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun a => by rw [Real.norm_eq_abs,abs_of_nonneg (hu0 a)]; exact hu1 a))
  have hrighti : Integrable (fun a => u a*Real.log (1+c*g a)) μ := by
    have hi : Integrable (fun a => Real.log (1+c*g a)) μ := by
      apply integrable_of_bounded μ _ (measurable_const.add hcg).log.aestronglyMeasurable
        (C := Real.log (1+c*B))
      filter_upwards [] with a
      have hg0 : 0 ≤ g a := ENNReal.toReal_nonneg
      dsimp only [Pi.add_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith [mul_nonneg hc hg0]))]
      exact Real.log_le_log (by positivity) (by nlinarith [hgB a])
    exact hi.bdd_mul hu.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun a => by rw [Real.norm_eq_abs,abs_of_nonneg (hu0 a)]; exact hu1 a))
  calc
    _ ≤ ∫ a,u a*Real.log (1+c*g a) ∂μ := integral_mono hlefti hrighti
      (fun a => mul_le_mul_of_nonneg_left (hpoint a) (hu0 a))
    _ ≤ _ := integral_weighted_log_moment μ u (fun a => c*g a) hu hcg hu0 hu1
      (fun _ => mul_nonneg hc ENNReal.toReal_nonneg) (M := c*B)
      (fun a => mul_le_mul_of_nonneg_left (hgB a) hc) (mul_nonneg hc hG) k hk hgmoment

end KernelPotential.DriftTools

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoisyProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection.Support Projection Reweight EntropySupport DriftTools Sphere

lemma mixedCube_integrand_measurable {k d : ℕ} (η : ℝ) :
    Measurable (fun t : ((Fin k → Fin d → ℝ) × (Fin k → Fin d → ℝ)) × Ambient d =>
      boxKernel η (projectVector t.1.1 t.2) 0 * boxKernel η (projectVector t.1.2 t.2) 0) := by
  have hA := measurable_boxKernel (k := k) η
  have hP := continuous_projectVector (k := k) (d := d)
  fun_prop

lemma mixedCube_measurable {k d : ℕ} (μ : Measure (Ambient d)) [SFinite μ]
    (η : ℝ) : Measurable (fun t : (Fin k → Fin d → ℝ) × (Fin k → Fin d → ℝ) =>
      mixedCubeAverage μ η t.1 t.2) :=
  Measurable.lintegral_prod_right (mixedCube_integrand_measurable η)

lemma mixedCube_le {k d : ℕ} (μ : Measure (Ambient d)) (η : ℝ)
    (X Z : Fin k → Fin d → ℝ) :
    mixedCubeAverage μ η X Z ≤ boxScale k η^2*μ univ := by
  calc
    _ ≤ ∫⁻ _u,boxScale k η*boxScale k η ∂μ := lintegral_mono
      (fun _ => mul_le_mul' (boxKernel_le η _ _) (boxKernel_le η _ _))
    _ = _ := by simp [pow_two]

lemma centered_rho_mass {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) (s : Ambient d) :
    centeredRho ν s univ ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))) := by
  rw [centeredRho,Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [preimage_univ]
  exact (rho_le ν hν univ).trans_eq (by simp)

lemma momentConstant_pos (d L : ℕ) : 0 < momentConstant d L := by
  unfold momentConstant; positivity

lemma log_momentConstant (d L : ℕ) (hd : 16 ≤ d) :
    Real.log (4*(1+2^(2*(d/16))*momentConstant d L)) ≤
      10*(d:ℝ)+Real.log ((L:ℝ)+2) := by
  have hg : 1 ≤ momentConstant d L := by
    unfold momentConstant
    have h9 : (1:ℝ) ≤ 9^(d/16-1) := one_le_pow₀ (by norm_num)
    have h3 : (1:ℝ) ≤ 3^(d-1) := one_le_pow₀ (by norm_num)
    have h2 : (1:ℝ) ≤ 2^((d-1)+4*(d/16)+2) := one_le_pow₀ (by norm_num)
    have hL : (1:ℝ) ≤ (L:ℝ)+2 := by have := Nat.cast_nonneg (α := ℝ) L; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h9 h3) h2) hL
  have hc : (1:ℝ) ≤ 2^(2*(d/16)) := one_le_pow₀ (by norm_num)
  have hbig : 4*(1+2^(2*(d/16))*momentConstant d L) ≤
      8*2^(2*(d/16))*momentConstant d L := by nlinarith [one_le_mul_of_one_le_of_one_le hc hg]
  have hlog := Real.log_le_log (by have := momentConstant_pos d L; positivity) hbig
  have he : Real.log (8*2^(2*(d/16))*momentConstant d L) =
      Real.log 8+(2*(d/16):ℕ)*Real.log 2+(d/16-1:ℕ)*Real.log 9+
        (d-1:ℕ)*Real.log 3+((d-1)+4*(d/16)+2:ℕ)*Real.log 2+
        Real.log ((L:ℝ)+2) := by
    rw [momentConstant]
    repeat' rw [Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow]
    ring
  rw [he] at hlog
  have hl8 : Real.log 8 ≤ 7 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<8 by norm_num)]
  have hl9 : Real.log 9 ≤ 8 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<9 by norm_num)]
  have hl3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<3 by norm_num)]
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have hk : (d/16:ℕ) ≤ (d:ℝ)/16 := by
    have hh : (16*((d/16:ℕ):ℝ)) ≤ (d:ℝ) := by exact_mod_cast Nat.mul_div_le d 16
    linarith
  have hk1 : ((d/16-1:ℕ):ℝ) ≤ (d/16:ℕ) := by exact_mod_cast Nat.sub_le (d/16) 1
  have hd1 : ((d-1:ℕ):ℝ) ≤ (d:ℝ) := by exact_mod_cast Nat.sub_le d 1
  have hdR : (16:ℝ) ≤ d := by exact_mod_cast hd
  push_cast at hlog
  nlinarith [mul_le_mul_of_nonneg_left hl9 (show (0:ℝ) ≤ (d/16-1:ℕ) by positivity),
    mul_le_mul_of_nonneg_left hl3 (show (0:ℝ) ≤ (d-1:ℕ) by positivity),
    mul_le_mul_of_nonneg_left hl2 (show (0:ℝ) ≤ 2*(d/16:ℕ) by positivity),
    mul_le_mul_of_nonneg_left hl2 (show (0:ℝ) ≤ (d-1:ℕ)+4*(d/16:ℕ)+2 by positivity)]

lemma weighted_centered_projection_oai {d : ℕ} (hd : 16 ≤ d)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1)
    (L : ℕ) (hL : H*(9*3^d:ℝ) ≤ 2^L) {η : ℝ} (hη : 0 < η)
    (u : (Fin (d/16) → Fin d → ℝ) → ℝ) (hu : Measurable u)
    (hu0 : ∀ X,0 ≤ u X) (hu1 : ∀ X,u X ≤ 1) :
    (∫ X,u X*(∫ Z,Real.log (1+2^(2*(d/16))*
      (mixedCubeAverage (centeredRho ν s) η X Z).toReal) ∂gaussianRows (d/16) d)
      ∂gaussianRows (d/16) d) ≤
      -(∫ X,u X ∂gaussianRows (d/16) d)*Real.log (∫ X,u X ∂gaussianRows (d/16) d)/(d/16:ℕ)+
        (∫ X,u X ∂gaussianRows (d/16) d)*(10*(d:ℝ)+Real.log ((L:ℝ)+2)) := by
  have hnorm := (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega : 0 < d))
  have := centered_finite ν hnorm s
  have : IsProbabilityMeasure (gaussianRows (d/16) d) := by unfold gaussianRows; infer_instance
  let B : ℝ := (boxScale (d/16) η).toReal^2*2^(2*(d/16))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (X Z : Fin (d/16) → Fin d → ℝ) :
      mixedCubeAverage (centeredRho ν s) η X Z ≤ ENNReal.ofReal B := by
    calc
      _ ≤ boxScale (d/16) η^2*centeredRho ν s univ := mixedCube_le _ _ _ _
      _ ≤ boxScale (d/16) η^2*ENNReal.ofReal ((2:ℝ)^(2*(d/16))) :=
        mul_le_mul_right (centered_rho_mass ν hnorm s) _
      _ = _ := by
        dsimp [B]
        rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (boxScale_ne_top _ hη)]
  have h := fresh_weighted_log_moment (gaussianRows (d/16) d) (gaussianRows (d/16) d)
    u (fun t => mixedCubeAverage (centeredRho ν s) η t.1 t.2) hu (mixedCube_measurable _ _)
    hu0 hu1 hB (momentConstant_pos d L).le (by positivity : (0:ℝ) ≤ 2^(2*(d/16))) hb
    (d/16) (by omega) (centered_mixed_moment hd ν hH hν s hs L hL η hη)
  exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_left (log_momentConstant d L hd)
    (integral_nonneg hu0)) _)

end KernelPotential.Noise

end OAI
end

theorem solution : type_of% @OAI.KernelPotential.Noise.weighted_centered_projection_oai := @OAI.KernelPotential.Noise.weighted_centered_projection_oai
