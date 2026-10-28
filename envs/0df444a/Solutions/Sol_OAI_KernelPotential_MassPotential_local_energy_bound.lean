-- Prove2me | solution 1 for OAI.KernelPotential.MassPotential.local_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:02:23.44886+00:00
-- url     : https://prove2.me/submissions/bf2a597f-f245-4672-8b38-287e1d8863ff

import Mathlib
import Definitions.Def_GaussianInformation_003
import Definitions.Def_OAIQWRLC001
import Theorems.Thm_OAI_KernelPotential_Noise_weighted_centered_projection
import Theorems.Thm_OAI_KernelPotential_NoisyDrift_positive_noisy_comparison

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

lemma measurable_J {d : ℕ} (ν : Measure (Ambient d)) [SFinite ν] : Measurable (J ν) := by
  unfold J
  apply Measurable.lintegral_prod_right
  exact ((measurable_snd.sub measurable_fst).norm.ennreal_ofReal.inv).pow_const _

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

lemma density_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (f : α → ℝ) {H : ℝ} (hfH : ∀ x,f x ≤ H) :
    μ.withDensity (fun x => ENNReal.ofReal (f x)) ≤ ENNReal.ofReal H • μ := by
  intro s
  rw [withDensity_apply' _ s,Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∫⁻ x in s, ENNReal.ofReal H ∂μ := lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hfH x))
    _ = _ := by simp

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

lemma measurableSet_closedBox {k : ℕ} (c : Fin k → ℝ) (η : ℝ) :
    MeasurableSet (closedBox c η) := by
  simp only [closedBox, ofPred_forall]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le ((measurable_pi_apply i).sub measurable_const).abs measurable_const

lemma volume_closedBox {k : ℕ} (c : Fin k → ℝ) (η : ℝ) (hη : 0 ≤ η) :
    volume (closedBox c η) = ENNReal.ofReal ((2*η)^k) := by
  have heq : closedBox c η = univ.pi (fun i => Icc (c i-η) (c i+η)) := by
    ext u
    simp only [closedBox, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_true_left,
      mem_Icc, abs_le]
    congr! 1
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [heq, volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, show ∀ i, c i+η-(c i-η)=2*η from fun i => by ring,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

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

lemma lintegral_boxKernel {k : ℕ} (η : ℝ) (hη : 0 < η) (c : Fin k → ℝ) :
    (∫⁻ u, boxKernel η c u) = 1 := by
  change (∫⁻ u, (closedBox c η).indicator (fun _ => boxScale k η) u) = 1
  rw [lintegral_indicator (measurableSet_closedBox c η), lintegral_const,
    Measure.restrict_apply_univ, volume_closedBox c η hη.le]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

end Support

open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

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

lemma projectVector_sub {k d : ℕ} (X : Fin k → Fin d → ℝ)
    (v w : EuclideanSpace ℝ (Fin d)) : projectVector X (v-w) = projectVector X v-projectVector X w := by
  ext r
  simp only [projectVector, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply]

end Support

open Support _root_.OAI.KernelPotential.Geometry

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

lemma rho_finite {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) : IsFiniteMeasure (rho ν) := by
  have := Measure.smul_finite ν (c := ENNReal.ofReal ((2:ℝ)^(2*(d/16)))) ENNReal.ofReal_ne_top
  exact isFiniteMeasure_of_le _ (rho_le ν hν)

lemma centered_finite {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) (s : Ambient d) : IsFiniteMeasure (centeredRho ν s) := by
  have := rho_finite ν hν
  unfold centeredRho
  infer_instance

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

lemma measurable_noise_density {k : ℕ} (η : ℝ) : Measurable (boxKernel (k := k) η 0) :=
  (measurable_boxKernel η).comp (measurable_const.prodMk measurable_id)

lemma noise_probability (k : ℕ) {η : ℝ} (hη : 0 < η) : IsProbabilityMeasure (noiseLaw k η) := by
  constructor
  rw [noiseLaw,withDensity_apply _ MeasurableSet.univ]
  simpa using lintegral_boxKernel (k := k) η hη 0

lemma noise_support (k : ℕ) (η : ℝ) : ∀ᵐ e ∂noiseLaw k η, e ∈ closedBox 0 η := by
  rw [noiseLaw,ae_withDensity_iff (measurable_noise_density η)]
  filter_upwards [] with e
  intro he
  exact boxKernel_ne_zero_mem he

lemma boxScale_ne_top (k : ℕ) {η : ℝ} (hη : 0 < η) : boxScale k η ≠ ∞ := by
  unfold boxScale
  exact ENNReal.inv_ne_top.mpr (by positivity)

lemma boxScale_dilate (k : ℕ) {η : ℝ} (hη : 0 < η) :
    boxScale k η = ENNReal.ofReal ((2:ℝ)^k)*boxScale k (2*η) := by
  have he : ENNReal.ofReal ((2*(2*η))^k) =
      ENNReal.ofReal ((2:ℝ)^k)*ENNReal.ofReal ((2*η)^k) := by
    rw [← ENNReal.ofReal_mul' (pow_nonneg (mul_nonneg (by norm_num) hη.le) k)]
    congr 1
    rw [← mul_pow]
  unfold boxScale
  rw [he,ENNReal.mul_inv,← mul_assoc,
    ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top,one_mul]
  · exact Or.inl (by positivity)
  · exact Or.inl ENNReal.ofReal_ne_top

lemma shifted_box_le {k : ℕ} {η : ℝ} (hη : 0 < η) (a b e : Fin k → ℝ)
    (he : e ∈ closedBox 0 η) :
    boxKernel η a (b+e) ≤ ENNReal.ofReal ((2:ℝ)^k)*boxKernel (2*η) (a-b) 0 := by
  by_cases hab : b+e ∈ closedBox a η
  · have hd : (0 : Fin k → ℝ) ∈ closedBox (a-b) (2*η) := by
      intro i
      have ha := hab i
      have hb := he i
      simp only [Pi.add_apply,Pi.sub_apply,Pi.zero_apply,sub_zero] at ha hb ⊢
      have hx := abs_add_le (b i+e i-a i) (-e i)
      have hid : b i+e i-a i+-e i=b i-a i := by ring
      rw [hid,abs_neg] at hx
      rw [show (0:ℝ)-(a i-b i)=b i-a i by ring]
      linarith
    rw [boxKernel,Set.indicator_of_mem hab,boxKernel,Set.indicator_of_mem hd]
    exact (boxScale_dilate k hη).le
  · rw [boxKernel,Set.indicator_of_notMem hab]
    exact bot_le

lemma projectedReference_measurable {k d : ℕ} (ν : Measure (Ambient d)) [SFinite (rho ν)]
    (η : ℝ) : Measurable (fun t : ((Fin k → Fin d → ℝ) × (Fin k → Fin d → ℝ)) ×
      ((Fin k → ℝ) × (Fin k → ℝ)) => projectedReference ν η t.1.1 t.1.2 t.2.1 t.2.2) := by
  unfold projectedReference
  apply Measurable.lintegral_prod_right
  have hA := measurable_boxKernel (k := k) η
  have hP := continuous_projectVector (k := k) (d := d)
  fun_prop

lemma projectedReference_le {k d : ℕ} (ν : Measure (Ambient d)) (η : ℝ)
    (X Z : Fin k → Fin d → ℝ) (y z : Fin k → ℝ) :
    projectedReference ν η X Z y z ≤ boxScale k η^2*(rho ν Set.univ) := by
  calc
    _ ≤ ∫⁻ _u,boxScale k η*boxScale k η ∂rho ν :=
      lintegral_mono (fun _ => mul_le_mul' (boxKernel_le η _ _) (boxKernel_le η _ _))
    _ = _ := by simp [pow_two]

lemma projectedReference_shift_le {k d : ℕ} (ν : Measure (Ambient d))
    {η : ℝ} (hη : 0 < η) (X Z : Fin k → Fin d → ℝ) (s : Ambient d)
    (e e' : Fin k → ℝ) (he : e ∈ closedBox 0 η) (he' : e' ∈ closedBox 0 η) :
    projectedReference ν η X Z (projectVector X s+e) (projectVector Z s+e') ≤
      ENNReal.ofReal ((2:ℝ)^(2*k))*mixedCubeAverage (centeredRho ν s) (2*η) X Z := by
  have hm : Measurable (fun u : Ambient d => boxKernel (2*η) (projectVector X u) 0*
      boxKernel (2*η) (projectVector Z u) 0) := by
    have hX : Measurable (fun u : Ambient d => projectVector X u) := by unfold projectVector; fun_prop
    have hZ : Measurable (fun u : Ambient d => projectVector Z u) := by unfold projectVector; fun_prop
    exact ((measurable_boxKernel (2*η)).comp (hX.prodMk measurable_const)).mul
      ((measurable_boxKernel (2*η)).comp (hZ.prodMk measurable_const))
  have hshift : Measurable (fun u : Ambient d => u-s) := by fun_prop
  rw [mixedCubeAverage,centeredRho,lintegral_map hm hshift]
  have hms : Measurable (fun u : Ambient d => boxKernel (2*η) (projectVector X (u-s)) 0 *
      boxKernel (2*η) (projectVector Z (u-s)) 0) := hm.comp hshift
  rw [← lintegral_const_mul _ hms]
  unfold projectedReference
  apply lintegral_mono
  intro u
  have hX := shifted_box_le hη (projectVector X u) (projectVector X s) e he
  have hZ := shifted_box_le hη (projectVector Z u) (projectVector Z s) e' he'
  have hprod := mul_le_mul' hX hZ
  rw [← projectVector_sub,← projectVector_sub] at hprod
  calc
    _ ≤ _ := hprod
    _ = _ := by
      rw [show 2*k=k+k by omega,pow_add,ENNReal.ofReal_mul (by positivity)]
      ring

end KernelPotential.Noise

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

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

end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Scaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential

namespace Scale
open KernelPotential.Geometry Sphere Coercivity

lemma radius_pos (j : ℕ) : 0 < radius j := by unfold radius; positivity

end Scale

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_SampleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection.Support Projection Reweight

lemma boxKernel_translate {k : ℕ} (η : ℝ) (a e : Fin k → ℝ) :
    boxKernel η a (a+e)=boxKernel η 0 e := by
  have he : a+e ∈ closedBox a η ↔ e ∈ closedBox 0 η := by
    simp [closedBox,Pi.add_apply]
  unfold boxKernel
  by_cases h : e ∈ closedBox 0 η
  · rw [Set.indicator_of_mem (he.mpr h),Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun hh => h (he.mp hh)),Set.indicator_of_notMem h]

lemma lintegral_noisy_translate {k : ℕ} (η : ℝ) (a : Fin k → ℝ)
    (f : (Fin k → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y,boxKernel η a y*f y ∂volume)=∫⁻ e,f (a+e) ∂noiseLaw k η := by
  rw [noiseLaw]
  have hm : Measurable (fun e : Fin k → ℝ => f (a+e)) := hf.comp (measurable_const.add measurable_id)
  rw [lintegral_withDensity_eq_lintegral_mul volume (measurable_noise_density η) hm]
  rw [← lintegral_add_left_eq_self (fun y => boxKernel η a y*f y) a]
  simp only [Pi.mul_apply,boxKernel_translate]

lemma observationKernel_measurable {k d : ℕ} (η : ℝ) :
    Measurable (Function.uncurry (observationKernel (k := k) (d := d) η)) := by
  have hA := measurable_boxKernel (k := k) η
  have hP := continuous_projectVector (k := k) (d := d)
  unfold observationKernel Function.uncurry
  fun_prop

lemma observationKernel_probability {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d) :
    (∫⁻ z,observationKernel (k := k) η z s ∂observationBase k d)=1 := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  rw [observationBase,lintegral_prod _ (by
    exact ((observationKernel_measurable η).comp (measurable_id.prodMk measurable_const)).aemeasurable)]
  have inner (X Z : Fin k → Fin d → ℝ) :
      (∫⁻ yz : (Fin k → ℝ) × (Fin k → ℝ),
        boxKernel η (projectVector X s) yz.1*boxKernel η (projectVector Z s) yz.2
        ∂(volume : Measure (Fin k → ℝ)).prod volume)=1 := by
    have hm (c : Fin k → ℝ) : Measurable (boxKernel η c) :=
      (measurable_boxKernel η).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod_mul (hm _).aemeasurable (hm _).aemeasurable,
      lintegral_boxKernel η hη,lintegral_boxKernel η hη,one_mul]
  simp only [observationKernel,inner,lintegral_one,measure_univ]

lemma observation_lintegral {k d : ℕ} (η : ℝ) (hη : 0 < η) (s : Ambient d)
    (f : Observation k d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z,observationKernel η z s*f z ∂observationBase k d)=
      ∫⁻ X,∫⁻ Z,∫⁻ e,∫⁻ e',f ((X,Z),(projectVector X s+e,projectVector Z s+e'))
        ∂noiseLaw k η ∂noiseLaw k η ∂gaussianRows k d ∂gaussianRows k d := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have := noise_probability k hη
  have hM : Measurable (fun z : Observation k d => observationKernel η z s*f z) :=
    ((observationKernel_measurable η).comp (measurable_id.prodMk measurable_const)).mul hf
  rw [observationBase,lintegral_prod _ hM.aemeasurable,lintegral_prod]
  · apply lintegral_congr; intro X
    apply lintegral_congr; intro Z
    have hz : Measurable (fun yz : (Fin k → ℝ) × (Fin k → ℝ) =>
        observationKernel η ((X,Z),yz) s*f ((X,Z),yz)) :=
      hM.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ hz.aemeasurable]
    dsimp only [observationKernel]
    have hinside (y : Fin k → ℝ) :
        (∫⁻ z,boxKernel η (projectVector X s) y*boxKernel η (projectVector Z s) z*f ((X,Z),(y,z)))=
          boxKernel η (projectVector X s) y*(∫⁻ e',f ((X,Z),(y,projectVector Z s+e')) ∂noiseLaw k η) := by
      simp_rw [mul_assoc]
      rw [lintegral_const_mul]
      · congr 1
        exact lintegral_noisy_translate η (projectVector Z s) (fun z => f ((X,Z),(y,z)))
          (hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
      · exact ((measurable_boxKernel η).comp (measurable_const.prodMk measurable_id)).mul
          (hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    simp_rw [hinside]
    apply lintegral_noisy_translate
    have hi : Measurable (fun yz : (Fin k → ℝ) × (Fin k → ℝ) =>
        f ((X,Z),(yz.1,projectVector Z s+yz.2))) := by fun_prop
    exact Measurable.lintegral_prod_right hi
  · exact (Measurable.lintegral_prod_right hM).aemeasurable

end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_SampleEquivalence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection Projection.Support

lemma sampling_lintegral {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d)
    (f : Observation k d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t,f (sampleEquiv s t) ∂samplingLaw k d η)=
      ∫⁻ X,∫⁻ Z,∫⁻ e,∫⁻ e',f ((X,Z),(projectVector X s+e,projectVector Z s+e'))
        ∂noiseLaw k η ∂noiseLaw k η ∂gaussianRows k d ∂gaussianRows k d := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have := noise_probability k hη
  have hm : Measurable (fun t : Observation k d => f (sampleEquiv s t)) := hf.comp (sampleEquiv s).measurable
  rw [samplingLaw,lintegral_prod _ hm.aemeasurable,lintegral_prod]
  · apply lintegral_congr; intro X
    apply lintegral_congr; intro Z
    have hi : Measurable (fun ef : (Fin k → ℝ) × (Fin k → ℝ) =>
        f (sampleEquiv s ((X,Z),ef))) := hm.comp (measurable_const.prodMk measurable_id)
    exact lintegral_prod _ hi.aemeasurable
  · exact (Measurable.lintegral_prod_right hm).aemeasurable

attribute [local irreducible] sampleEquiv

lemma sample_measurePreserving {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d) :
    MeasurePreserving (sampleEquiv (k := k) s) (samplingLaw k d η)
      ((observationBase k d).withDensity (fun z => observationKernel η z s)) := by
  refine ⟨(sampleEquiv s).measurable,?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  have hk : Measurable (fun z : Observation k d => observationKernel η z s) := by
    have hK := observationKernel_measurable (k := k) (d := d) η
    fun_prop
  calc
    _ = ∫⁻ t,f (sampleEquiv s t) ∂samplingLaw k d η := lintegral_map hf (sampleEquiv s).measurable
    _ = ∫⁻ X,∫⁻ Z,∫⁻ e,∫⁻ e',f ((X,Z),(projectVector X s+e,projectVector Z s+e'))
        ∂noiseLaw k η ∂noiseLaw k η ∂gaussianRows k d ∂gaussianRows k d := sampling_lintegral hη s f hf
    _ = ∫⁻ z,observationKernel η z s*f z ∂observationBase k d := (observation_lintegral η hη s f hf).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul (observationBase k d) hk hf).symm

lemma sampling_probability (k d : ℕ) {η : ℝ} (hη : 0 < η) :
    IsProbabilityMeasure (samplingLaw k d η) := by
  have := noise_probability k hη
  unfold samplingLaw gaussianRows
  infer_instance

lemma sample_integral {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d)
    (f : Observation k d → ℝ) :
    (∫ z,f z ∂(observationBase k d).withDensity (fun z => observationKernel η z s))=
      ∫ t,f (sampleEquiv s t) ∂samplingLaw k d η :=
  ((sample_measurePreserving hη s).integral_comp (sampleEquiv s).measurableEmbedding f).symm

end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Bayes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.Bayes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open EntropySupport Coercivity Sphere

lemma integrable_rule {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (r : α → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1) : Integrable r ν :=
  integrable_bounded_measurable ν r hr (fun s => by rw [abs_of_nonneg (hr0 s)]; exact hr1 s)

lemma mass_bounds {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (r : α → ℝ) (hr : Measurable r) {ε : ℝ} (hε : 0 < ε)
    (hrε : ∀ s,ε ≤ r s) (hr1 : ∀ s,r s ≤ 1) : ε ≤ mass ν r ∧ mass ν r ≤ 1 := by
  have hi := integrable_rule ν r hr (fun s => hε.le.trans (hrε s)) hr1
  constructor
  · simpa [mass] using integral_mono (integrable_const ε) hi hrε
  · simpa [mass] using integral_mono hi (integrable_const 1) hr1

lemma post_probability {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (r : α → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1)
    (ha : 0 < mass ν r) : IsProbabilityMeasure (post ν r) := by
  have hi := integrable_rule ν r hr hr0 hr1
  constructor
  rw [post,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _) (ae_of_all _ (fun s => div_nonneg (hr0 s) ha.le)),
    integral_div]
  change ENNReal.ofReal (mass ν r/mass ν r)=1
  simp [ha.ne']

lemma post_le {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    (r : α → ℝ) (hr1 : ∀ s,r s ≤ 1) (ha : 0 < mass ν r) :
    post ν r ≤ ENNReal.ofReal (1/mass ν r) • ν :=
  density_bounded ν _ (fun s => div_le_div_of_nonneg_right (hr1 s) ha.le)

lemma post_bounded {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (r : Ambient d → ℝ) (hr1 : ∀ s,r s ≤ 1) (ha : 0 < mass ν r) :
    post ν r ≤ ENNReal.ofReal (H/mass ν r) • sphereProbability d := by
  calc
    _ ≤ ENNReal.ofReal (1/mass ν r) • ν := post_le ν r hr1 ha
    _ ≤ ENNReal.ofReal (1/mass ν r) • (ENNReal.ofReal H • sphereProbability d) := smul_le_smul_left _ hν
    _ = _ := by rw [smul_smul,← ENNReal.ofReal_mul' hH.le]; congr 2; ring

lemma post_density {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    (f r : α → ℝ) (hf : Measurable f) (hf0 : ∀ s,0 ≤ f s) (hr : Measurable r)
    (hν : ν=μ.withDensity (fun s => ENNReal.ofReal (f s))) :
    post ν r = μ.withDensity (fun s => ENNReal.ofReal (f s*r s/mass ν r)) := by
  unfold post
  nth_rw 1 [hν]
  rw [← withDensity_mul _ hf.ennreal_ofReal (hr.div_const _).ennreal_ofReal]
  congr 1
  ext s
  simp only [Pi.mul_apply,← ENNReal.ofReal_mul (hf0 s),mul_div_assoc]

end KernelPotential.Bayes

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_JointCompensation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.DriftTools

namespace FiniteReference
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma joint_integral_nonneg (ν : Measure α) (Λ : Measure β) [SigmaFinite ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K))
    (hκ : Measurable (Function.uncurry κ))
    (f : α × β × ι → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x,f x ∂joint ν Λ K κ) = ∫⁻ s,∫⁻ z,∑ w,K z s*κ z w*f (s,z,w) ∂Λ ∂ν := by
  rw [joint,lintegral_withDensity_eq_lintegral_mul]
  · rw [lintegral_prod]
    · apply lintegral_congr; intro s
      rw [lintegral_prod]
      · apply lintegral_congr; intro z
        simp only [lintegral_count,tsum_fintype]
        rfl
      · fun_prop
    · fun_prop
  · fun_prop
  · exact hf

lemma joint_probability (ν : Measure α) (Λ : Measure β) [IsProbabilityMeasure ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1) (hκ1 : ∀ z,∑ w,κ z w=1) :
    IsProbabilityMeasure (joint ν Λ K κ) := by
  constructor
  rw [← lintegral_one,(joint_integral_nonneg ν Λ K κ hK hκ _ measurable_const)]
  simp only [mul_one,← Finset.mul_sum,hκ1,mul_one,hK1,lintegral_one,measure_univ]

end FiniteReference

end KernelPotential.DriftTools

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ReferenceMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.DriftTools.FiniteReference
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma joint_integral (ν : Measure α) (Λ : Measure β) [SigmaFinite ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hKfin : ∀ z s,K z s ≠ ∞) (hκfin : ∀ z w,κ z w ≠ ∞)
    (f : α × β × ι → ℝ) (hi : Integrable f (joint ν Λ K κ)) :
    (∫ t,f t ∂joint ν Λ K κ)=∫ s,∫ z,∑ w,(K z s).toReal*(κ z w).toReal*f (s,z,w) ∂Λ ∂ν := by
  have hm : Measurable (fun t : α × β × ι => K t.2.1 t.1*κ t.2.1 t.2.2) := by fun_prop
  have hfin : ∀ᵐ t ∂ν.prod (Λ.prod Measure.count),K t.2.1 t.1*κ t.2.1 t.2.2 < ∞ :=
    ae_of_all _ (fun t => ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (hKfin _ _)) (lt_top_iff_ne_top.mpr (hκfin _ _)))
  have hweight : Integrable (fun t : α × β × ι =>
      (K t.2.1 t.1).toReal*(κ t.2.1 t.2.2).toReal*f t) (ν.prod (Λ.prod Measure.count)) := by
    simpa only [joint,ENNReal.toReal_mul,smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul' hm hfin).mp hi
  rw [joint,integral_withDensity_eq_integral_toReal_smul hm hfin]
  simp only [ENNReal.toReal_mul,smul_eq_mul]
  rw [integral_prod _ hweight]
  apply integral_congr_ae
  filter_upwards [hweight.prod_right_ae] with s hs
  rw [integral_prod _ hs]
  congr 1
  ext z
  rw [integral_count]

lemma likelihood_bounds {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Λ : Measure β) [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    {ε : ℝ≥0∞} (hκε : ∀ z w,ε ≤ κ z w) (hκ1 : ∀ z w,κ z w ≤ 1) (s : α) (w : ι) :
    ε ≤ ∫⁻ z,K z s*κ z w ∂Λ ∧ (∫⁻ z,K z s*κ z w ∂Λ) ≤ 1 := by
  have hm : Measurable (fun z => K z s) := hK.comp (measurable_id.prodMk measurable_const)
  constructor
  · calc
      ε = ∫⁻ z,K z s*ε ∂Λ := by rw [lintegral_mul_const _ hm,hK1,one_mul]
      _ ≤ _ := lintegral_mono (fun z => mul_le_mul_right (hκε z w) _)
  · calc
      _ ≤ ∫⁻ z,K z s*1 ∂Λ := lintegral_mono (fun z => mul_le_mul_right (hκ1 z w) _)
      _ = 1 := by simp only [mul_one,hK1]
end KernelPotential.DriftTools.FiniteReference

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_DriftCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.DriftCutoff

lemma level_lower (d : ℕ) (H : ℝ) : 2*Real.log H+20*(d:ℝ) ≤ (level d H:ℝ) := by
  have h := Nat.le_ceil (2*Real.log H+20*(d:ℝ))
  unfold level
  push_cast
  linarith

lemma level_upper (d : ℕ) {H : ℝ} (hH : 1 ≤ H) :
    (level d H:ℝ) ≤ 2*Real.log H+20*(d:ℝ)+2 := by
  have hh := Real.log_nonneg hH
  have h := Nat.ceil_lt_add_one (show 0 ≤ 2*Real.log H+20*(d:ℝ) by positivity)
  unfold level
  push_cast
  linarith

lemma log_constant_bound (d : ℕ) (hd : 16 ≤ d) {H : ℝ} (hH : 1 ≤ H) :
    Real.log (H*(9*3^d)*(4:ℝ)^(d-1)*(2:ℝ)^(2*(d/16)+1)) ≤
      (level d H:ℝ)*Real.log 2 := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hlog2 : 1/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hu2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hu3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<3 by norm_num)]
  have hu4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num)]
  have hu9 : Real.log 9 ≤ 8 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<9 by norm_num)]
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_mul hHpos.ne' (by positivity),Real.log_mul (by norm_num) (by positivity)]
  simp only [Real.log_pow]
  have hdR : 16 ≤ (d:ℝ) := by exact_mod_cast hd
  have hn : ((d-1:ℕ):ℝ) ≤ (d:ℝ) := by exact_mod_cast Nat.sub_le d 1
  have hk : ((2*(d/16)+1:ℕ):ℝ) ≤ (d:ℝ)+1 := by
    exact_mod_cast (show 2*(d/16)+1 ≤ d+1 by have hh := Nat.div_mul_le_self d 16; omega)
  have hL := level_lower d H
  have hp := mul_le_mul_of_nonneg_left hlog2 (show (0:ℝ) ≤ level d H by positivity)
  have h3 := mul_le_mul_of_nonneg_left hu3 (show (0:ℝ) ≤ d by positivity)
  have h4 := mul_le_mul_of_nonneg_left hu4 (show (0:ℝ) ≤ (d-1:ℕ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hu2 (show (0:ℝ) ≤ (2*(d/16)+1:ℕ) by positivity)
  linarith

lemma moment_cut (d : ℕ) (hd : 16 ≤ d) {H : ℝ} (hH : 1 ≤ H) :
    H*(9*3^d:ℝ) ≤ 2^(level d H) := by
  have hp := Real.le_pow_of_log_le (show (0:ℝ)<2 by norm_num) (log_constant_bound d hd hH)
  have h4 : (1:ℝ) ≤ 4^(d-1) := one_le_pow₀ (by norm_num)
  have h2 : (1:ℝ) ≤ 2^(2*(d/16)+1) := one_le_pow₀ (by norm_num)
  calc
    _ ≤ H*(9*3^d:ℝ)*4^(d-1)*2^(2*(d/16)+1) := by
      have hpos : 0 ≤ H*(9*3^d:ℝ) := by positivity
      calc
        _ ≤ H*(9*3^d:ℝ)*4^(d-1) := le_mul_of_one_le_right hpos h4
        _ ≤ _ := le_mul_of_one_le_right (by positivity) h2
    _ ≤ _ := hp

lemma log_level_bound (d : ℕ) (hd : 1 ≤ d) {H : ℝ} (hH : 1 ≤ H) :
    Real.log ((level d H:ℝ)+2) ≤ 2*Real.log H/(d:ℝ)+25*(d:ℝ) := by
  have hdR : 1 ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : 0 < (d:ℝ) := by linarith
  have hLpos : 0 < (level d H:ℝ)+2 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hLpos hdpos)
  rw [Real.log_div hLpos.ne' hdpos.ne'] at hlog
  have hlogd := Real.log_le_sub_one_of_pos hdpos
  have hLu := level_upper d hH
  have hbound : ((level d H:ℝ)+2)/(d:ℝ) ≤ 2*Real.log H/(d:ℝ)+24 := by
    apply (div_le_iff₀ hdpos).mpr
    have he : (2*Real.log H/(d:ℝ)+24)*(d:ℝ)=2*Real.log H+24*(d:ℝ) := by field_simp
    rw [he]
    linarith
  linarith

end KernelPotential.DriftCutoff

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ReferenceCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian
lemma sampling_integral_bounded {k d : ℕ} {η : ℝ} (hη : 0 < η)
    (f : Observation k d → ℝ) (hf : Measurable f) {M : ℝ} (hb : ∀ t,‖f t‖ ≤ M) :
    (∫ t,f t ∂samplingLaw k d η)=∫ X,∫ Z,∫ e,∫ e',f ((X,Z),(e,e'))
      ∂noiseLaw k η ∂noiseLaw k η ∂gaussianRows k d ∂gaussianRows k d := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have := noise_probability k hη
  have := sampling_probability k d hη
  have hi := Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hb)
    (μ := samplingLaw k d η)
  rw [samplingLaw,integral_prod _ hi]
  have hi' : Integrable (fun XZ : (Mat k d) × (Mat k d) =>
      ∫ e : (Fin k → ℝ) × (Fin k → ℝ),f (XZ,e) ∂(noiseLaw k η).prod (noiseLaw k η))
        ((gaussianRows k d).prod (gaussianRows k d)) := hi.integral_prod_left
  rw [integral_prod _ hi']
  apply integral_congr_ae
  filter_upwards [] with X
  apply integral_congr_ae
  filter_upwards [] with Z
  exact integral_prod _ (Integrable.of_bound (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable M
    (ae_of_all _ (fun e => hb ((X,Z),e))))

lemma observationKernel_ne_top {k d : ℕ} {η : ℝ} (hη : 0 < η) (z : Observation k d) (s : Ambient d) :
    observationKernel η z s ≠ ∞ :=
  ENNReal.mul_ne_top (ne_top_of_le_ne_top (boxScale_ne_top k hη) (boxKernel_le η _ _))
    (ne_top_of_le_ne_top (boxScale_ne_top k hη) (boxKernel_le η _ _))

lemma noiseAverage_measurable {k d : ℕ} {η : ℝ} (hη : 0 < η) (φ : ((Mat k d) × (Fin k → ℝ)) → ℝ)
    (hφ : Measurable φ) (s : Ambient d) :
    Measurable (fun X : Mat k d => ∫ e,φ (X,projectVector X s+e) ∂noiseLaw k η) := by
  have hP : Measurable (fun X : Mat k d => projectVector X s) := by
    have := continuous_projectVector (k := k) (d := d)
    fun_prop
  have := noise_probability k hη
  have hm : Measurable (fun t : (Mat k d) × (Fin k → ℝ) => φ (t.1,projectVector t.1 s+t.2)) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma first_rule_integral {k d : ℕ} {η : ℝ} (hη : 0 < η)
    (φ : ((Mat k d) × (Fin k → ℝ)) → ℝ) (hφ : Measurable φ)
    (hφ0 : ∀ t,0 ≤ φ t) (hφ1 : ∀ t,φ t ≤ 1) (s : Ambient d) :
    (∫ z : Observation k d,φ (z.1.1,z.2.1)
      ∂(observationBase k d).withDensity (fun z => observationKernel η z s))=
      ∫ X,∫ e,φ (X,projectVector X s+e) ∂noiseLaw k η ∂gaussianRows k d := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have := noise_probability k hη
  rw [sample_integral hη s]
  have hm : Measurable (fun t : Observation k d => φ ((sampleEquiv s t).1.1,(sampleEquiv s t).2.1)) :=
    hφ.comp (((sampleEquiv s).measurable.fst.fst).prodMk (sampleEquiv s).measurable.snd.fst)
  rw [sampling_integral_bounded hη _ hm (M := 1) (fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hφ0 _)]; exact hφ1 _)]
  simp only [sampleEquiv,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk,integral_const,probReal_univ,one_smul]
end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoisyRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian DriftTools.FiniteReference Bayes

lemma likelihood_sum {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Λ : Measure β) [SigmaFinite Λ] (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1) (hκ1 : ∀ z,∑ w,κ z w=1) (s : α) :
    ∑ w,likelihood Λ K κ s w=1 := by
  have hb (z : β) (w : ι) : κ z w ≤ 1 := by
    rw [← hκ1 z]; exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ w)
  have hfin (w : ι) : (∫⁻ z,K z s*κ z w ∂Λ) ≠ ∞ :=
    ne_of_lt (((likelihood_bounds Λ K κ hK hK1 (ε := 0) (fun _ _ => bot_le) hb s w).2).trans_lt (by norm_num))
  unfold likelihood
  rw [← ENNReal.toReal_sum (fun w _ => hfin w),← lintegral_finsetSum]
  · simp only [← Finset.mul_sum,hκ1,mul_one,hK1,ENNReal.toReal_one]
  · intro w _; fun_prop

lemma likelihood_real_bounds {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Λ : Measure β) [SigmaFinite Λ] (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    {ε : ℝ} (hε : 0 ≤ ε) (hκε : ∀ z w,ENNReal.ofReal ε ≤ κ z w) (hκ1 : ∀ z w,κ z w ≤ 1)
    (s : α) (w : ι) : ε ≤ likelihood Λ K κ s w ∧ likelihood Λ K κ s w ≤ 1 := by
  obtain ⟨hl,hu⟩ := likelihood_bounds Λ K κ hK hK1 hκε hκ1 s w
  have hfin := ne_of_lt (hu.trans_lt (by norm_num : (1:ℝ≥0∞)<∞))
  exact ⟨by simpa [likelihood,ENNReal.toReal_ofReal hε] using ENNReal.toReal_mono hfin hl,
    by simpa [likelihood] using ENNReal.toReal_mono ENNReal.one_ne_top hu⟩

lemma likelihood_first {d k : ℕ} {η : ℝ} (hη : 0 < η)
    (φ : ((Mat k d) × (Fin k → ℝ)) → ℝ) (hφ : Measurable φ)
    (hφ0 : ∀ t,0 ≤ φ t) (hφ1 : ∀ t,φ t ≤ 1) (s : Ambient d) :
    ((∫⁻ z : Observation k d,observationKernel η z s*ENNReal.ofReal (φ (z.1.1,z.2.1))
      ∂observationBase k d).toReal)=
      ∫ X,∫ e,φ (X,projectVector X s+e) ∂noiseLaw k η ∂gaussianRows k d := by
  have hm : Measurable (fun z : Observation k d => φ (z.1.1,z.2.1)) :=
    hφ.comp (measurable_fst.fst.prodMk measurable_snd.fst)
  have hK := observationKernel_measurable (k := k) (d := d) η
  have hKs : Measurable (fun z : Observation k d => observationKernel η z s) := by fun_prop
  have he := first_rule_integral hη φ hφ hφ0 hφ1 s
  rw [integral_withDensity_eq_integral_toReal_smul hKs
    (ae_of_all _ (fun z => lt_top_iff_ne_top.mpr (observationKernel_ne_top hη z s)))] at he
  have hi : Measurable (fun z : Observation k d => observationKernel η z s*ENNReal.ofReal (φ (z.1.1,z.2.1))) := by fun_prop
  rw [← integral_toReal hi.aemeasurable (ae_of_all _ (fun z => ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (observationKernel_ne_top hη z s)) ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (hφ0 _),smul_eq_mul] using he

end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_PositiveRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference

namespace PositiveRule
variable {k d N : ℕ} (rule : PositiveRule k d N)
lemma nonneg (t) (w) : 0 ≤ rule.prob t w := rule.lower_pos.le.trans (rule.lower_prob t w)
lemma le_one (t) (w) : rule.prob t w ≤ 1 := by
  rw [← rule.sum_prob t]
  exact Finset.single_le_sum (fun v _ => rule.nonneg t v) (Finset.mem_univ w)
lemma measurable (w) : Measurable (fun t => rule.prob t w) :=
  rule.measurable_prob.comp (measurable_id.prodMk measurable_const)
lemma measurable_kernel : Measurable (Function.uncurry rule.kernel) := by
  unfold kernel
  exact (rule.measurable_prob.comp ((measurable_fst.fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd)).ennreal_ofReal
lemma sum_kernel (z) : ∑ w,rule.kernel z w=1 := by
  unfold kernel
  rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => rule.nonneg _ w),rule.sum_prob,ENNReal.ofReal_one]
lemma kernel_le_one (z) (w) : rule.kernel z w ≤ 1 :=
  ENNReal.ofReal_le_one.mpr (rule.le_one _ _)
lemma lower_kernel (z) (w) : ENNReal.ofReal rule.lower ≤ rule.kernel z w :=
  ENNReal.ofReal_le_ofReal (rule.lower_prob _ _)
lemma measurable_response (η : ℝ) (w : Fin N) : Measurable (rule.response η w) := by
  have hK : Measurable (Function.uncurry (observationKernel (k := k) (d := d) η)) := observationKernel_measurable η
  have hκ : Measurable (fun z : Observation k d => rule.kernel z w) :=
    rule.measurable_kernel.comp (measurable_id.prodMk measurable_const)
  have hm : Measurable (fun a : Ambient d × Observation k d => observationKernel η a.2 a.1*rule.kernel a.2 w) :=
    (hK.comp measurable_swap).mul (hκ.comp measurable_snd)
  unfold response likelihood
  exact hm.lintegral_prod_right.ennreal_toReal
lemma response_bounds {η : ℝ} (hη : 0 < η) (w) (s) :
    rule.lower ≤ rule.response η w s ∧ rule.response η w s ≤ 1 :=
  likelihood_real_bounds (observationBase k d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) (observationKernel_probability hη) rule.lower_pos.le
    rule.lower_kernel rule.kernel_le_one s w
lemma response_sum {η : ℝ} (hη : 0 < η) (s) : ∑ w,rule.response η w s=1 :=
  likelihood_sum (observationBase k d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) rule.measurable_kernel (observationKernel_probability hη)
    rule.sum_kernel s
lemma response_average {η : ℝ} (hη : 0 < η) (w) (s) :
    rule.response η w s=∫ X,∫ e,rule.prob (X,projectVector X s+e) w ∂noiseLaw k η ∂gaussianRows k d :=
  likelihood_first hη _ (rule.measurable w) (fun t => rule.nonneg t w) (fun t => rule.le_one t w) s
lemma mass_pos {η : ℝ} (hη : 0 < η) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (w) :
    0 < mass ν (rule.response η w) :=
  rule.lower_pos.trans_le (mass_bounds ν _ (rule.measurable_response η w) rule.lower_pos
    (fun s => (rule.response_bounds hη w s).1) (fun s => (rule.response_bounds hη w s).2)).1
lemma mass_le_one {η : ℝ} (hη : 0 < η) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (w) :
    mass ν (rule.response η w) ≤ 1 :=
  (mass_bounds ν _ (rule.measurable_response η w) rule.lower_pos
    (fun s => (rule.response_bounds hη w s).1) (fun s => (rule.response_bounds hη w s).2)).2
lemma mass_sum {η : ℝ} (hη : 0 < η) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] :
    ∑ w,mass ν (rule.response η w)=1 := by
  unfold mass
  rw [← integral_finsetSum _ (fun w _ => integrable_rule ν _ (rule.measurable_response η w)
    (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1) (fun s => (rule.response_bounds hη w s).2))]
  simp_rw [rule.response_sum hη]
  simp
lemma post_prob {η : ℝ} (hη : 0 < η) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (w) :
    IsProbabilityMeasure (post ν (rule.response η w)) :=
  post_probability ν _ (rule.measurable_response η w)
    (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1)
    (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w)
end PositiveRule
end KernelPotential.NoisyDrift

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoiseContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian

lemma noise_norm_le {k : ℕ} {η : ℝ} (hη : 0 ≤ η) :
    ∀ᵐ e ∂noiseLaw k η, ‖e‖ ≤ η := by
  filter_upwards [noise_support k η] with e he
  apply (pi_norm_le_iff_of_nonneg hη).mpr
  intro i
  simpa [closedBox,Real.norm_eq_abs] using he i

lemma tendsto_noise_average {k : ℕ} (φ : (Fin k → ℝ) → ℝ) (hφ : Continuous φ)
    (hφ0 : ∀ e,0 ≤ φ e) (hφ1 : ∀ e,φ e ≤ 1) (y : Fin k → ℝ)
    (η : ℕ → ℝ) (hη : ∀ n,0 < η n) (hlim : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun n => ∫ e,φ (y+e) ∂noiseLaw k (η n)) atTop (𝓝 (φ y)) := by
  have hi (n) : Integrable (fun e => φ (y+e)) (noiseLaw k (η n)) := by
    have := noise_probability k (hη n)
    refine Integrable.of_bound (hφ.comp (continuous_const.add continuous_id)).measurable.aestronglyMeasurable 1 ?_
    filter_upwards [] with e
    rw [Real.norm_eq_abs,abs_of_nonneg (hφ0 _)]
    exact hφ1 _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hh⟩ := Metric.continuousAt_iff.mp (hφ.continuousAt (x := y)) (ε/2) (half_pos hε)
  filter_upwards [hlim.eventually (eventually_lt_nhds hδ)] with n hn
  have := noise_probability k (hη n)
  have hb : ∀ᵐ e ∂noiseLaw k (η n),‖φ (y+e)-φ y‖ ≤ ε/2 := by
    filter_upwards [noise_norm_le (hη n).le] with e he
    have hdist : dist (y+e) y < δ := by
      simpa only [dist_eq_norm,add_sub_cancel_left] using he.trans_lt hn
    simpa only [dist_eq_norm] using (hh hdist).le
  have hb' := norm_integral_le_of_norm_le_const hb
  rw [integral_sub (hi n) (integrable_const _)] at hb'
  simp only [integral_const,probReal_univ,one_smul,mul_one] at hb'
  rw [dist_eq_norm]
  exact hb'.trans_lt (half_lt_self hε)

end KernelPotential.Noise
namespace KernelPotential.NoisyDrift.PositiveRule
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference
variable {k d N : ℕ} (rule : PositiveRule k d N)
lemma measurable_exactResponse (w : Fin N) : Measurable (rule.exactResponse w) := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have hm : Measurable (fun t : Ambient d × Mat k d => rule.prob (t.2,projectVector t.2 t.1) w) := by
    apply (rule.measurable w).comp
    exact measurable_snd.prodMk ((continuous_projectVector.comp (continuous_snd.prodMk continuous_fst)).measurable)
  exact hm.stronglyMeasurable.integral_prod_right.measurable
lemma exactResponse_bounds (w : Fin N) (s : Ambient d) :
    rule.lower ≤ rule.exactResponse w s ∧ rule.exactResponse w s ≤ 1 := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have hi : Integrable (fun X => rule.prob (X,projectVector X s) w) (gaussianRows k d) := by
    refine Integrable.of_bound ((rule.measurable w).comp (measurable_id.prodMk ((continuous_projectVector.comp (continuous_id.prodMk continuous_const)).measurable))).aestronglyMeasurable 1 ?_
    filter_upwards [] with X
    rw [Real.norm_eq_abs,abs_of_nonneg (rule.nonneg _ _)]
    exact rule.le_one _ _
  constructor
  · have h := integral_mono (integrable_const rule.lower) hi (fun X => rule.lower_prob _ w)
    simpa [exactResponse] using h
  · have h := integral_mono hi (integrable_const (1:ℝ)) (fun X => rule.le_one _ w)
    simpa [exactResponse] using h
lemma tendsto_response (hc : ∀ w,Continuous (fun t => rule.prob t w)) (w : Fin N) (s : Ambient d)
    (η : ℕ → ℝ) (hη : ∀ n,0 < η n) (hlim : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun n => rule.response (η n) w s) atTop (𝓝 (rule.exactResponse w s)) := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have he (n) : rule.response (η n) w s = ∫ X,∫ e,rule.prob (X,projectVector X s+e) w ∂noiseLaw k (η n) ∂gaussianRows k d :=
    likelihood_first (hη n) _ (rule.measurable w) (fun t => rule.nonneg t w) (fun t => rule.le_one t w) s
  simp_rw [he]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    (fun n => (noiseAverage_measurable (hη n) _ (rule.measurable w) s).aestronglyMeasurable)
    (integrable_const 1)
  · intro n
    have := noise_probability k (hη n)
    filter_upwards [] with X
    have hb := norm_integral_le_of_norm_le_const (μ := noiseLaw k (η n)) (f := fun e => rule.prob (X,projectVector X s+e) w)
      (ae_of_all _ (fun e => by rw [Real.norm_eq_abs,abs_of_nonneg (rule.nonneg _ _)]; exact rule.le_one _ _))
    simpa using hb
  · filter_upwards [] with X
    exact tendsto_noise_average _ ((hc w).comp (continuous_const.prodMk continuous_id))
      (fun e => rule.nonneg _ _) (fun e => rule.le_one _ _) _ η hη hlim
end KernelPotential.NoisyDrift.PositiveRule

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_LocalRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference
namespace LocalRule
variable {k d N : ℕ} (rule : LocalRule k d N)
lemma le_one (t) (w) : rule.prob t w ≤ 1 := by
  rw [← rule.sum t]
  exact Finset.single_le_sum (fun v _ => rule.nonneg t v) (Finset.mem_univ w)
lemma integrable_eval (w : Fin N) (s : Ambient d) :
    Integrable (fun X => rule.prob (X,projectVector X s) w) (gaussianRows k d) := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  apply Integrable.of_bound ((rule.measurable w).comp (measurable_id.prodMk
    ((continuous_projectVector.comp (continuous_id.prodMk continuous_const)).measurable))).aestronglyMeasurable 1
  filter_upwards [] with X
  change ‖rule.prob (X,projectVector X s) w‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (rule.nonneg _ _)]
  exact rule.le_one _ _
lemma measurable_response (w : Fin N) : Measurable (rule.response w) := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have hm : Measurable (fun t : Ambient d × Mat k d => rule.prob (t.2,projectVector t.2 t.1) w) :=
    (rule.measurable w).comp (measurable_snd.prodMk ((continuous_projectVector.comp (continuous_snd.prodMk continuous_fst)).measurable))
  exact hm.stronglyMeasurable.integral_prod_right.measurable
lemma response_bounds (w : Fin N) (s : Ambient d) : 0 ≤ rule.response w s ∧ rule.response w s ≤ 1 := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  exact ⟨integral_nonneg (fun _ => rule.nonneg _ _),by
    simpa [response] using integral_mono (rule.integrable_eval w s) (integrable_const (1:ℝ)) (fun _ => rule.le_one _ _)⟩
lemma positive_response (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (w : Fin N) (s : Ambient d) :
    (rule.positive hN ε hε hε1).exactResponse w s=(1-ε)*rule.response w s+ε/(N:ℝ) := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  change (∫ X,(1-ε)*rule.prob (X,projectVector X s) w+ε/(N:ℝ) ∂gaussianRows k d)=_
  rw [integral_add ((rule.integrable_eval w s).const_mul _) (integrable_const _),integral_const_mul]
  simp [response]
end LocalRule
end KernelPotential.NoisyDrift

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_MassPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.MassPotential
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Coercivity Sphere
lemma normalized_probability {d : ℕ} (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] (hρ : ρ univ≠0) :
    IsProbabilityMeasure (normalized ρ) := by
  constructor
  simp only [normalized,Measure.smul_apply,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hρ (measure_ne_top _ _)
lemma proper_probability {d : ℕ} (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] : IsProbabilityMeasure (proper ρ) := by
  unfold proper
  split_ifs with h
  · infer_instance
  · exact normalized_probability ρ h
lemma mass_smul_proper {d : ℕ} (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] :
    ENNReal.ofReal (ρ univ).toReal • proper ρ=ρ := by
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  by_cases h : ρ univ=0
  · rw [h,zero_smul]
    exact (Measure.measure_univ_eq_zero.mp h).symm
  · rw [proper,ite_eq_right h,normalized,smul_smul,ENNReal.mul_inv_cancel h (measure_ne_top _ _),one_smul]
lemma energy_proper {d : ℕ} (ρ : Measure (Ambient d)) : energy ρ=(ρ univ).toReal*Phi (proper ρ) := by
  unfold energy proper
  split_ifs with h
  · simp [h]
  · rfl
lemma energy_smul_probability {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (a : ℝ) (ha : 0 ≤ a) : energy (ENNReal.ofReal a • ν)=a*Phi ν := by
  by_cases haz : a=0
  · simp [haz,energy,normalized]
  · have hp := lt_of_le_of_ne ha (Ne.symm haz)
    have hz : ENNReal.ofReal a≠0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
    have hu : (ENNReal.ofReal a • ν) univ=ENNReal.ofReal a := by simp
    unfold energy normalized
    rw [hu,ENNReal.toReal_ofReal ha,smul_smul,ENNReal.inv_mul_cancel hz ENNReal.ofReal_ne_top,one_smul]
end KernelPotential.MassPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_EnergyBayes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.MassPotential
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Coercivity Bayes
lemma energy_zero {d : ℕ} : energy (0 : Measure (Ambient d))=0 := by simp [energy]
lemma energy_smul {d : ℕ} (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] (a : ℝ) (ha : 0 ≤ a) :
    energy (ENNReal.ofReal a • ρ)=a*energy ρ := by
  have := proper_probability ρ
  calc energy (ENNReal.ofReal a • ρ) = energy (ENNReal.ofReal (a*(ρ univ).toReal) • proper ρ) := by
         rw [ENNReal.ofReal_mul ha,mul_smul,mass_smul_proper]
       _ = (a*(ρ univ).toReal)*Phi (proper ρ) := energy_smul_probability _ _ (mul_nonneg ha ENNReal.toReal_nonneg)
       _ = a*energy ρ := by rw [energy_proper]; ring
lemma density_mass {d : ℕ} (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (r : Ambient d → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1) :
    (ν.withDensity (fun s => ENNReal.ofReal (r s))) univ=ENNReal.ofReal (mass ν r) := by
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_rule ν r hr hr0 hr1) (ae_of_all _ hr0)).symm
lemma density_le {d : ℕ} (ν : Measure (Ambient d)) [SFinite ν] (r : Ambient d → ℝ) (hr1 : ∀ s,r s ≤ 1) :
    ν.withDensity (fun s => ENNReal.ofReal (r s)) ≤ ν := by
  simpa using density_bounded ν r hr1
lemma density_finite {d : ℕ} (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (r : Ambient d → ℝ) (hr1 : ∀ s,r s ≤ 1) :
    IsFiniteMeasure (ν.withDensity (fun s => ENNReal.ofReal (r s))) := isFiniteMeasure_of_le ν (density_le ν r hr1)
lemma energy_density {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (r : Ambient d → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1) :
    energy (ν.withDensity (fun s => ENNReal.ofReal (r s)))=mass ν r*Phi (post ν r) := by
  have ha : 0 ≤ mass ν r := integral_nonneg hr0
  by_cases haz : mass ν r=0
  · have hz : ν.withDensity (fun s => ENNReal.ofReal (r s))=0 := Measure.measure_univ_eq_zero.mp (by
      rw [density_mass ν r hr hr0 hr1,haz,ENNReal.ofReal_zero])
    simp [hz,haz,energy_zero]
  · have hap := lt_of_le_of_ne ha (Ne.symm haz)
    have := post_probability ν r hr hr0 hr1 hap
    have he : ν.withDensity (fun s => ENNReal.ofReal (r s))=ENNReal.ofReal (mass ν r) • post ν r := by
      rw [post,← withDensity_smul _ (hr.div_const _).ennreal_ofReal]
      congr 1
      ext s
      change ENNReal.ofReal (r s)=ENNReal.ofReal (mass ν r)*ENNReal.ofReal (r s/mass ν r)
      rw [ENNReal.ofReal_div_of_pos hap,div_eq_mul_inv,mul_left_comm,
        ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hap).ne' ENNReal.ofReal_ne_top,mul_one]
    rw [he,energy_smul_probability _ _ ha]
end KernelPotential.MassPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_SimplexApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference

lemma continuous_ae_approx {k d N : ℕ}
    (μ : Measure ((Mat k d) × (Fin k → ℝ))) [IsFiniteMeasure μ]
    (f : ((Mat k d) × (Fin k → ℝ)) → (Fin N → ℝ)) (hf : Integrable f μ) :
    ∃ g : ℕ → BoundedContinuousFunction ((Mat k d) × (Fin k → ℝ)) (Fin N → ℝ),
      ∀ᵐ t ∂μ,Tendsto (fun n => g n t) atTop (𝓝 (f t)) := by
  have he (n : ℕ) : ENNReal.ofReal (1/((n:ℝ)+1)) ≠ 0 := by positivity
  choose g hg _hgi using fun n => hf.exists_boundedContinuous_lintegral_sub_le (he n)
  have ht : Tendsto (fun n => eLpNorm ((g n : _ → _)-f) 1 μ) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => ENNReal.ofReal (1/((n:ℝ)+1))) atTop (𝓝 0) := by
      simpa only [Function.comp_def,ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hp (fun _ => bot_le)
    intro n
    simpa only [eLpNorm_one_eq_lintegral_enorm,
      Pi.sub_apply,enorm_sub_rev] using hg n
  obtain ⟨ns,_hns,hconv⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (p := (1:ℝ≥0∞)) (by norm_num)
    (fun n => (g n).continuous.aestronglyMeasurable) hf.aestronglyMeasurable ht).exists_seq_tendsto_ae
  exact ⟨fun n => g (ns n),hconv⟩

end KernelPotential.NoisyDrift
namespace KernelPotential.NoisyDrift.Simplex
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
lemma clip_lower (ε x : ℝ) : ε ≤ clip ε x := le_max_left _ _
lemma clip_upper {ε : ℝ} (hε : ε ≤ 1) (x : ℝ) : clip ε x ≤ 1 := max_le hε (min_le_left _ _)
lemma total_pos {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (x : Fin N → ℝ) : 0 < total ε x := by
  have h : (N:ℝ)*ε ≤ total ε x := by
    simpa [total] using Finset.sum_le_sum (s := Finset.univ) (fun w _ => clip_lower ε (x w))
  exact (mul_pos (by exact_mod_cast hN) hε).trans_le h
lemma total_upper {N : ℕ} {ε : ℝ} (hε : ε ≤ 1) (x : Fin N → ℝ) : total ε x ≤ (N:ℝ) := by
  simpa [total] using Finset.sum_le_sum (s := Finset.univ) (fun w _ => clip_upper hε (x w))
lemma normalize_lower {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x : Fin N → ℝ) (w : Fin N) :
    ε/(N:ℝ) ≤ normalize ε x w := by
  exact (div_le_div_of_nonneg_left hε.le (total_pos hN hε x) (total_upper hε1 x)).trans
    (div_le_div_of_nonneg_right (clip_lower ε (x w)) (total_pos hN hε x).le)
lemma normalize_sum {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (x : Fin N → ℝ) :
    ∑ w,normalize ε x w=1 := by
  unfold normalize
  rw [← Finset.sum_div]
  exact div_self (total_pos hN hε x).ne'
lemma continuous_normalize {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) : Continuous (normalize (N := N) ε) := by
  have hc (w : Fin N) : Continuous (fun x : Fin N → ℝ => clip ε (x w)) := continuous_const.max (continuous_const.min (continuous_apply w))
  have ht : Continuous (fun x : Fin N → ℝ => total ε x) := continuous_finsetSum _ (fun w _ => hc w)
  exact continuous_pi (fun w => (hc w).div ht (fun x => (total_pos hN hε x).ne'))
lemma normalize_eq {N : ℕ} {ε : ℝ} (x : Fin N → ℝ) (hl : ∀ w,ε ≤ x w) (hu : ∀ w,x w ≤ 1) (hs : ∑ w,x w=1) :
    normalize ε x=x := by
  have he (w) : clip ε (x w)=x w := by rw [clip,min_eq_right (hu w),max_eq_right (hl w)]
  ext w
  simp only [normalize,total,he,hs,div_one]
end KernelPotential.NoisyDrift.Simplex

namespace KernelPotential.NoisyDrift.PositiveRule
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference
variable {k d N : ℕ} (rule : PositiveRule k d N)
lemma lower_le_one (hN : 0 < N) : rule.lower ≤ 1 :=
  (rule.lower_prob (0,0) ⟨0,hN⟩).trans (rule.le_one _ _)
lemma exists_continuous_approx (hN : 0 < N) (μ : Measure ((Mat k d) × (Fin k → ℝ))) [IsFiniteMeasure μ] :
    ∃ R : ℕ → PositiveRule k d N,
      (∀ n w,Continuous (fun t => (R n).prob t w)) ∧
      (∀ n,(R n).lower=rule.lower/(N:ℝ)) ∧
      (∀ᵐ t ∂μ,∀ w,Tendsto (fun n => (R n).prob t w) atTop (𝓝 (rule.prob t w))) := by
  have hm : Measurable rule.prob := Measurable.of_eval (fun message => rule.measurable message)
  have hi : Integrable rule.prob μ := by
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards [] with t
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro w
    rw [Real.norm_eq_abs,abs_of_nonneg (rule.nonneg _ _)]
    exact rule.le_one _ _
  obtain ⟨g,hg⟩ := continuous_ae_approx μ rule.prob hi
  let R : ℕ → PositiveRule k d N := fun n => {
    prob := fun t => Simplex.normalize rule.lower (g n t)
    measurable_prob := by
      apply measurable_from_prod_countable_left
      intro w
      exact ((continuous_apply w).comp ((Simplex.continuous_normalize hN rule.lower_pos).comp (g n).continuous)).measurable
    sum_prob := fun _ => Simplex.normalize_sum hN rule.lower_pos _
    lower := rule.lower/(N:ℝ)
    lower_pos := div_pos rule.lower_pos (by exact_mod_cast hN)
    lower_prob := fun _ _ => Simplex.normalize_lower hN rule.lower_pos (rule.lower_le_one hN) _ _ }
  refine ⟨R,?_,fun _ => rfl,?_⟩
  · intro n w
    exact (continuous_apply w).comp ((Simplex.continuous_normalize hN rule.lower_pos).comp (g n).continuous)
  · filter_upwards [hg] with t ht
    have hh := ((Simplex.continuous_normalize hN rule.lower_pos).tendsto _).comp ht
    rw [Simplex.normalize_eq _ (rule.lower_prob t) (rule.le_one t) (rule.sum_prob t)] at hh
    intro w
    exact (continuous_apply w).tendsto _ |>.comp hh
end KernelPotential.NoisyDrift.PositiveRule

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoisyCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Reweight Sphere DriftTools

lemma sampling_noise_mem {k d : ℕ} {η : ℝ} (hη : 0 < η) :
    ∀ᵐ t ∂samplingLaw k d η,t.2.1 ∈ closedBox 0 η ∧ t.2.2 ∈ closedBox 0 η := by
  have := noise_probability k hη
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have h1 : ∀ᵐ e ∂(noiseLaw k η).prod (noiseLaw k η),e.1 ∈ closedBox 0 η :=
    measurePreserving_fst.quasiMeasurePreserving.ae (noise_support k η)
  have h2 : ∀ᵐ e ∂(noiseLaw k η).prod (noiseLaw k η),e.2 ∈ closedBox 0 η :=
    measurePreserving_snd.quasiMeasurePreserving.ae (noise_support k η)
  exact measurePreserving_snd.quasiMeasurePreserving.ae (h1.and h2)

lemma projectedReference_real_bound {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν,‖s‖=1) {η : ℝ} (hη : 0 < η) (z : Observation k d) :
    (projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2).toReal ≤
      (boxScale k η).toReal^2*2^(2*(d/16)) := by
  have hb := (rho_le ν hν Set.univ).trans_eq (by simp :
    ((ENNReal.ofReal ((2:ℝ)^(2*(d/16)))) • ν) Set.univ=ENNReal.ofReal ((2:ℝ)^(2*(d/16))))
  have hc := (projectedReference_le ν η z.1.1 z.1.2 z.2.1 z.2.2).trans (mul_le_mul_right hb _)
  apply (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top (boxScale_ne_top k hη)) ENNReal.ofReal_ne_top) hc).trans_eq
  simp [ENNReal.toReal_mul,ENNReal.toReal_pow]

lemma mixedCube_real_bound {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ u ∂ν,‖u‖=1) (s : Ambient d) {η : ℝ} (hη : 0 < η) (X Z : Mat k d) :
    (mixedCubeAverage (centeredRho ν s) η X Z).toReal ≤
      (boxScale k η).toReal^2*2^(2*(d/16)) := by
  have hb := (mixedCube_le (centeredRho ν s) η X Z).trans
    (mul_le_mul_right (centered_rho_mass ν hν s) _)
  apply (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top (boxScale_ne_top k hη)) ENNReal.ofReal_ne_top) hb).trans_eq
  simp [ENNReal.toReal_mul,ENNReal.toReal_pow]

lemma mixedCube_finite {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ u ∂ν,‖u‖=1) (s : Ambient d) {η : ℝ} (hη : 0 < η) (X Z : Mat k d) :
    mixedCubeAverage (centeredRho ν s) η X Z ≠ ∞ := by
  have := centered_finite ν hν s
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (boxScale_ne_top k hη)) (measure_ne_top _ _))
    (mixedCube_le (centeredRho ν s) η X Z)

lemma projected_log_bounded {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν,‖s‖=1) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ z : Observation k d,
      0 ≤ Real.log (1+(projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2).toReal) ∧
      Real.log (1+(projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2).toReal) ≤ M := by
  refine ⟨Real.log (1+(boxScale k η).toReal^2*2^(2*(d/16))),Real.log_nonneg (by
      have hb : 0 ≤ (boxScale k η).toReal^2*2^(2*(d/16)) := by positivity
      linarith),?_⟩
  intro z
  exact ⟨Real.log_nonneg (by have := ENNReal.toReal_nonneg (a := projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2); linarith),
    Real.log_le_log (by positivity) (add_le_add_right (projectedReference_real_bound ν hν hη z) _)⟩

lemma mixed_log_bounded {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ u ∂ν,‖u‖=1) (s : Ambient d) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ X Z : Mat k d,
      0 ≤ Real.log (1+2^(2*k)*(mixedCubeAverage (centeredRho ν s) η X Z).toReal) ∧
      Real.log (1+2^(2*k)*(mixedCubeAverage (centeredRho ν s) η X Z).toReal) ≤ M := by
  have hB : 0 ≤ (2:ℝ)^(2*k)*((boxScale k η).toReal^2*2^(2*(d/16))) := by positivity
  refine ⟨Real.log (1+2^(2*k)*((boxScale k η).toReal^2*2^(2*(d/16)))),
    Real.log_nonneg (by linarith),?_⟩
  intro X Z
  constructor
  · apply Real.log_nonneg
    have : 0 ≤ (2:ℝ)^(2*k)*(mixedCubeAverage (centeredRho ν s) η X Z).toReal := by positivity
    linarith
  · exact Real.log_le_log (by positivity)
      (add_le_add_right (mul_le_mul_of_nonneg_left (mixedCube_real_bound ν hν s hη X Z) (by positivity : (0:ℝ) ≤ 2^(2*k))) _)

lemma noisy_weighted_projection {d : ℕ} (hd : 16 ≤ d)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1)
    (L : ℕ) (hL : H*(9*3^d:ℝ) ≤ 2^L) {η : ℝ} (hη : 0 < η)
    (φ : ((Mat (d/16) d) × (Fin (d/16) → ℝ)) → ℝ) (hφ : Measurable φ)
    (hφ0 : ∀ t,0 ≤ φ t) (hφ1 : ∀ t,φ t ≤ 1) :
    (∫ z : Observation (d/16) d,φ (z.1.1,z.2.1)*
      Real.log (1+(projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2).toReal)
      ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s)) ≤
      -(∫ X,∫ e,φ (X,projectVector X s+e) ∂noiseLaw (d/16) η ∂gaussianRows (d/16) d)*
        Real.log (∫ X,∫ e,φ (X,projectVector X s+e) ∂noiseLaw (d/16) η ∂gaussianRows (d/16) d)/(d/16:ℕ)+
      (∫ X,∫ e,φ (X,projectVector X s+e) ∂noiseLaw (d/16) η ∂gaussianRows (d/16) d)*
        (10*(d:ℝ)+Real.log ((L:ℝ)+2)) := by
  have hnorm := (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega : 0 < d))
  have := rho_finite ν hnorm
  have := centered_finite ν hnorm s
  have := sampling_probability (d/16) d hη
  have := noise_probability (d/16) hη
  have : IsProbabilityMeasure (gaussianRows (d/16) d) := by unfold gaussianRows; infer_instance
  let u : Mat (d/16) d → ℝ := fun X => ∫ e,φ (X,projectVector X s+e) ∂noiseLaw (d/16) η
  have hu := noiseAverage_measurable hη φ hφ s
  have hu0 (X) : 0 ≤ u X := integral_nonneg (fun _ => hφ0 _)
  have hu1 (X) : u X ≤ 1 := by
    have him : Measurable (fun e => φ (X,projectVector X s+e)) := by fun_prop
    have hi := Integrable.of_bound him.aestronglyMeasurable 1
      (ae_of_all (noiseLaw (d/16) η) (fun _ => by rw [Real.norm_eq_abs,abs_of_nonneg (hφ0 _)]; exact hφ1 _))
    simpa [u] using integral_mono hi (integrable_const 1) (fun _ => hφ1 _)
  let F : Mat (d/16) d × Mat (d/16) d → ℝ := fun XZ =>
    Real.log (1+2^(2*(d/16))*(mixedCubeAverage (centeredRho ν s) (2*η) XZ.1 XZ.2).toReal)
  have hF : Measurable F := by
    have hh := mixedCube_measurable (k := d/16) (centeredRho ν s) (2*η)
    exact (measurable_const.add (measurable_const.mul hh.ennreal_toReal)).log
  obtain ⟨M,_hM,hFb⟩ := mixed_log_bounded (k := d/16) ν hnorm s (by positivity : 0 < 2*η)
  obtain ⟨T,_hT,hPb⟩ := projected_log_bounded (k := d/16) ν hnorm hη
  let g : Observation (d/16) d → ℝ := fun t => φ ((sampleEquiv s t).1.1,(sampleEquiv s t).2.1)*
    Real.log (1+(projectedReference ν η (sampleEquiv s t).1.1 (sampleEquiv s t).1.2
      (sampleEquiv s t).2.1 (sampleEquiv s t).2.2).toReal)
  let f : Observation (d/16) d → ℝ := fun t => φ ((sampleEquiv s t).1.1,(sampleEquiv s t).2.1)*F t.1
  have hφs : Measurable (fun t : Observation (d/16) d => φ ((sampleEquiv s t).1.1,(sampleEquiv s t).2.1)) :=
    hφ.comp ((sampleEquiv s).measurable.fst.fst.prodMk (sampleEquiv s).measurable.snd.fst)
  have hg : Measurable g := by
    have hP := (projectedReference_measurable (k := d/16) ν η).comp (sampleEquiv s).measurable
    exact hφs.mul (measurable_const.add hP.ennreal_toReal).log
  have hf : Measurable f := hφs.mul (hF.comp measurable_fst)
  have hgb (t) : ‖g t‖ ≤ T := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hφ0 _) (hPb _).1)]
    exact (mul_le_mul_of_nonneg_right (hφ1 _) (hPb _).1).trans (by simpa using (hPb _).2)
  have hfb (t) : ‖f t‖ ≤ M := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hφ0 _) (hFb _ _).1)]
    exact (mul_le_mul_of_nonneg_right (hφ1 _) (hFb _ _).1).trans (by simpa using (hFb _ _).2)
  have hfg : (∫ t,g t ∂samplingLaw (d/16) d η) ≤ ∫ t,f t ∂samplingLaw (d/16) d η := by
    apply integral_mono_ae (Integrable.of_bound hg.aestronglyMeasurable T (ae_of_all _ hgb))
      (Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hfb))
    filter_upwards [sampling_noise_mem (d := d) hη] with t ht
    apply mul_le_mul_of_nonneg_left _ (hφ0 _)
    apply Real.log_le_log (by positivity)
    apply add_le_add_right
    have hh := projectedReference_shift_le ν hη t.1.1 t.1.2 s t.2.1 t.2.2 ht.1 ht.2
    have hfin := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := (2:ℝ)^(2*(d/16))))
      (mixedCube_finite ν hnorm s (by positivity : 0 < 2*η) t.1.1 t.1.2)
    have hhR := ENNReal.toReal_mono hfin hh
    simpa only [sampleEquiv,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2^(2*(d/16)))] using hhR
  rw [sample_integral hη s]
  change (∫ t,g t ∂samplingLaw (d/16) d η) ≤ _
  apply hfg.trans
  rw [sampling_integral_bounded hη f hf hfb]
  have he : (∫ X,∫ Z,∫ e,∫ e',f ((X,Z),(e,e')) ∂noiseLaw (d/16) η ∂noiseLaw (d/16) η
      ∂gaussianRows (d/16) d ∂gaussianRows (d/16) d)=
      ∫ X,u X*(∫ Z,F (X,Z) ∂gaussianRows (d/16) d) ∂gaussianRows (d/16) d := by
    simp only [f,sampleEquiv,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk,integral_const,
      probReal_univ,one_smul,integral_mul_const,integral_const_mul,u]
  rw [he]
  exact weighted_centered_projection hd ν hH hν s hs L hL (by positivity : 0 < 2*η) u hu hu0 hu1
end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_JointRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.DriftTools.FiniteReference
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
lemma kernel_average_measurable (Λ : Measure β) [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (hK : Measurable (Function.uncurry K))
    (hKfin : ∀ z s,K z s ≠ ∞) (g : β → ℝ) (hg : Measurable g) :
    Measurable (fun s => ∫ z,g z ∂Λ.withDensity (fun z => K z s)) := by
  have hm : Measurable (fun t : α × β => (K t.2 t.1).toReal*g t.2) := by fun_prop
  have hh := (hm.stronglyMeasurable.integral_prod_right' (ν := Λ)).measurable
  convert hh using 1
  ext s
  have hKs : Measurable (fun z => K z s) := hK.comp (measurable_id.prodMk measurable_const)
  rw [integral_withDensity_eq_integral_toReal_smul hKs
    (ae_of_all _ (fun z => lt_top_iff_ne_top.mpr (hKfin z s)))]
  simp only [smul_eq_mul]

lemma kernel_average_integrable (ν : Measure α) [IsFiniteMeasure ν] (Λ : Measure β) [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (hK : Measurable (Function.uncurry K))
    (hKfin : ∀ z s,K z s ≠ ∞) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    (g : β → ℝ) (hg : Measurable g) {M : ℝ} (hgM : ∀ z,‖g z‖ ≤ M) :
    Integrable (fun s => ∫ z,g z ∂Λ.withDensity (fun z => K z s)) ν := by
  refine Integrable.of_bound (kernel_average_measurable Λ K hK hKfin g hg).aestronglyMeasurable M ?_
  filter_upwards [] with s
  have : IsProbabilityMeasure (Λ.withDensity (fun z => K z s)) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,hK1]
  simpa using norm_integral_le_of_norm_le_const (μ := Λ.withDensity (fun z => K z s))
    (ae_of_all _ hgM)
end KernelPotential.DriftTools.FiniteReference

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity Sphere

lemma measurable_postCharge {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    {H : ℝ} (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    Measurable (Function.uncurry (postCharge ν rule η)) := by
  apply measurable_from_prod_countable_left
  intro w
  have := rule.post_prob hη ν w
  have hnorm : ∀ᵐ s ∂ν,‖s‖=1 := (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega : 0 < d))
  have := Reweight.rho_finite (post ν (rule.response η w)) (withDensity_absolutelyContinuous _ _ |>.ae_le hnorm)
  exact (measurable_const.add (projectedReference_measurable (post ν (rule.response η w)) η).ennreal_toReal).log

lemma postCharge_uniform_bound {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ z w,0 ≤ postCharge ν rule η z w ∧ postCharge ν rule η z w ≤ M := by
  classical
  have hh (w : Fin N) : ∃ M : ℝ,0 ≤ M ∧ ∀ z,0 ≤ postCharge ν rule η z w ∧ postCharge ν rule η z w ≤ M := by
    have := rule.post_prob hη ν w
    have hb := post_bounded ν hH hν (rule.response η w) (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w)
    have hnorm : ∀ᵐ s ∂post ν (rule.response η w),‖s‖=1 :=
      (Measure.absolutelyContinuous_of_le_smul hb).ae_le (ae_unit_norm (by omega : 0 < d))
    exact projected_log_bounded (post ν (rule.response η w)) hnorm hη
  choose M hM hb using hh
  refine ⟨∑ w,M w,Finset.sum_nonneg (fun w _ => hM w),fun z w => ⟨(hb w z).1,(hb w z).2.trans ?_⟩⟩
  exact Finset.single_le_sum (fun v _ => hM v) (Finset.mem_univ w)

lemma postCharge_pointwise {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) (w : Fin N)
    {s : Ambient d} (hs : ‖s‖=1) :
    (∫ z : Observation (d/16) d,rule.prob (z.1.1,z.2.1) w*postCharge ν rule η z w
      ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s)) ≤
      -xlog (rule.response η w s)/(d/16:ℕ)+rule.response η w s*
        (10*(d:ℝ)+Real.log ((DriftCutoff.level d (H/mass ν (rule.response η w)):ℝ)+2)) := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have ha := rule.mass_pos hη ν w
  have hHdiv : 1 ≤ H/mass ν (rule.response η w) :=
    (le_div_iff₀ ha).mpr (by simpa using (rule.mass_le_one hη ν w).trans hH)
  have := rule.post_prob hη ν w
  have hpost := post_bounded ν hHp hν _ (fun s => (rule.response_bounds hη w s).2) ha
  have hc := noisy_weighted_projection hd (post ν (rule.response η w)) (div_pos hHp ha) hpost s hs
    (DriftCutoff.level d (H/mass ν (rule.response η w))) (DriftCutoff.moment_cut d hd hHdiv)
    hη (fun t => rule.prob t w) (rule.measurable w) (fun t => rule.nonneg t w) (fun t => rule.le_one t w)
  simpa only [← rule.response_average hη,xlog,postCharge,neg_mul] using hc

lemma integrable_postCharge_average {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hHp : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) (w : Fin N) :
    Integrable (fun s => ∫ z : Observation (d/16) d,rule.prob (z.1.1,z.2.1) w*postCharge ν rule η z w
      ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s)) ν := by
  obtain ⟨M,hM,hMb⟩ := postCharge_uniform_bound hd ν hHp hν rule hη
  have hm1 : Measurable (fun z : Observation (d/16) d => rule.prob (z.1.1,z.2.1) w) :=
    (rule.measurable w).comp (show Measurable (fun z : Observation (d/16) d => (z.1.1,z.2.1)) from measurable_fst.fst.prodMk measurable_snd.fst)
  have hm2 : Measurable (fun z : Observation (d/16) d => postCharge ν rule η z w) :=
    (measurable_postCharge hd ν hν rule hη).comp (f := fun z : Observation (d/16) d => (z,w)) (show Measurable (fun z : Observation (d/16) d => (z,w)) from measurable_id.prodMk measurable_const)
  have hg : Measurable (fun z : Observation (d/16) d => rule.prob (z.1.1,z.2.1) w*postCharge ν rule η z w) := hm1.mul hm2
  have hgb (z : Observation (d/16) d) : ‖rule.prob (z.1.1,z.2.1) w*postCharge ν rule η z w‖ ≤ M := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (rule.nonneg _ w) (hMb z w).1)]
    exact (mul_le_mul_of_nonneg_right (rule.le_one _ w) (hMb z w).1).trans (by simpa using (hMb z w).2)
  exact kernel_average_integrable ν (observationBase (d/16) d) (observationKernel η)
    (observationKernel_measurable η) (observationKernel_ne_top hη) (observationKernel_probability hη) _ hg hgb

lemma integrated_postCharge {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) (w : Fin N) :
    (∫ s,∫ z : Observation (d/16) d,rule.prob (z.1.1,z.2.1) w*postCharge ν rule η z w
      ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s) ∂ν) ≤
      -(∫ s,xlog (rule.response η w s) ∂ν)/(d/16:ℕ)+
        mass ν (rule.response η w)*(10*(d:ℝ)+Real.log ((DriftCutoff.level d (H/mass ν (rule.response η w)):ℝ)+2)) := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have ha := rule.mass_pos hη ν w
  have ha1 := rule.mass_le_one hη ν w
  have hHdiv : 1 ≤ H/mass ν (rule.response η w) := (le_div_iff₀ ha).mpr (by simpa using ha1.trans hH)
  have := rule.post_prob hη ν w
  have hpost := post_bounded ν hHp hν (rule.response η w) (fun s => (rule.response_bounds hη w s).2) ha
  have hnorm : ∀ᵐ s ∂ν,‖s‖=1 :=
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega : 0 < d))
  have hi := integrable_postCharge_average hd ν hHp hν rule hη w
  have hir := integrable_rule ν _ (rule.measurable_response η w)
    (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1) (fun s => (rule.response_bounds hη w s).2)
  have hix := integrable_xlog_bounded ν _ (rule.measurable_response η w)
    (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1) (fun s => (rule.response_bounds hη w s).2)
  let L := DriftCutoff.level d (H/mass ν (rule.response η w))
  have hh := integral_mono_ae hi ((hix.neg.div_const (d/16:ℕ)).add (hir.mul_const (10*(d:ℝ)+Real.log ((L:ℝ)+2)))) (by
    filter_upwards [hnorm] with s hs
    exact postCharge_pointwise hd ν hH hν rule hη w hs)
  have hi1 : Integrable (fun s => -xlog (rule.response η w s)/(d/16:ℕ)) ν := hix.neg.div_const _
  have hi2 : Integrable (fun s => rule.response η w s*(10*(d:ℝ)+Real.log ((L:ℝ)+2))) ν := hir.mul_const _
  change _ ≤ ∫ s, -xlog (rule.response η w s)/(d/16:ℕ)+rule.response η w s*(10*(d:ℝ)+Real.log ((L:ℝ)+2)) ∂ν at hh
  rw [integral_add hi1 hi2,integral_div,integral_neg,integral_mul_const] at hh
  exact hh
end KernelPotential.NoisyDrift

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_JointEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open EntropySupport Coercivity
lemma finite_entropy_bound {N : ℕ} (hN : 0 < N) (r : Fin N → ℝ)
    (hr : ∀ w,0 ≤ r w) (h1 : ∑ w,r w=1) :
    ∑ w,-r w*Real.log (r w) ≤ Real.log (N:ℝ) := by
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hN
  have hh (w : Fin N) := xlog_lower_tangent (hr w) (inv_pos.mpr hNR)
  have ht (w : Fin N) : -r w*Real.log (N:ℝ)+r w-(N:ℝ)⁻¹ ≤ r w*Real.log (r w) := by
    have h := hh w
    simp only [xlog,Real.log_inv] at h
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun w _ => ht w)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,neg_mul,Finset.sum_neg_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,h1] at hs
  have he : (N:ℝ)*(N:ℝ)⁻¹=1 := mul_inv_cancel₀ hNR.ne'
  rw [he] at hs
  have hn : (∑ w : Fin N,-r w*Real.log (r w))=-(∑ w : Fin N,r w*Real.log (r w)) := by
    simp only [neg_mul,Finset.sum_neg_distrib]
  rw [← Finset.sum_mul,h1,one_mul] at hs
  rw [hn]
  linarith

lemma weighted_log_ratio {N : ℕ} (r : Fin N → ℝ) (hr : ∀ w,0 < r w) (h1 : ∑ w,r w=1)
    {H : ℝ} (hH : 0 < H) :
    (∑ w,r w*Real.log (H/r w))=Real.log H+∑ w,-r w*Real.log (r w) := by
  simp_rw [Real.log_div hH.ne' (hr _).ne',mul_sub,Finset.sum_sub_distrib,
    ← Finset.sum_mul,h1,one_mul,neg_mul,Finset.sum_neg_distrib]
  ring
end KernelPotential.NoisyDrift

namespace KernelPotential.DriftTools.FiniteReference
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma joint_integral_by_message (ν : Measure α) (Λ : Measure β) [IsProbabilityMeasure ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hKfin : ∀ z s,K z s ≠ ∞) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    (hκ1 : ∀ z,∑ w,κ z w=1)
    (f : β → ι → ℝ) (hf : Measurable (Function.uncurry f)) {M : ℝ}
    (hfM : ∀ z w,‖f z w‖ ≤ M) :
    (∫ t,f t.2.1 t.2.2 ∂joint ν Λ K κ)=
      ∑ w,∫ s,∫ z,(κ z w).toReal*f z w ∂Λ.withDensity (fun z => K z s) ∂ν := by
  classical
  have hb (z : β) (w : ι) : κ z w ≤ 1 := by
    rw [← hκ1 z]; exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ w)
  have hκfin (z : β) (w : ι) : κ z w ≠ ∞ := ne_of_lt ((hb z w).trans_lt (by norm_num))
  have hκR (z : β) (w : ι) : (κ z w).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hb z w)
  have hKprob (s : α) : IsProbabilityMeasure (Λ.withDensity (fun z => K z s)) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,hK1]
  have hKs (s : α) : Measurable (fun z => K z s) := hK.comp (measurable_id.prodMk measurable_const)
  have hg (w : ι) : Measurable (fun z => (κ z w).toReal*f z w) := by fun_prop
  have hgb (z : β) (w : ι) : ‖(κ z w).toReal*f z w‖ ≤ M := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact (mul_le_mul_of_nonneg_right (hκR z w) (norm_nonneg _)).trans (by simpa using hfM z w)
  have hgi (s : α) (w : ι) : Integrable (fun z => (κ z w).toReal*f z w) (Λ.withDensity (fun z => K z s)) := by
    have := hKprob s
    exact Integrable.of_bound (hg w).aestronglyMeasurable M (ae_of_all _ (fun z => hgb z w))
  have hzi (s : α) (w : ι) : Integrable (fun z => (K z s).toReal*(κ z w).toReal*f z w) Λ := by
    have hi := (integrable_withDensity_iff_integrable_smul' (hKs s)
      (ae_of_all _ (fun z => lt_top_iff_ne_top.mpr (hKfin z s)))).mp (hgi s w)
    simpa only [smul_eq_mul,mul_assoc] using hi
  have he (s : α) (w : ι) : (∫ z,(K z s).toReal*(κ z w).toReal*f z w ∂Λ)=
      ∫ z,(κ z w).toReal*f z w ∂Λ.withDensity (fun z => K z s) := by
    rw [integral_withDensity_eq_integral_toReal_smul (hKs s)
      (ae_of_all _ (fun z => lt_top_iff_ne_top.mpr (hKfin z s)))]
    simp only [smul_eq_mul,mul_assoc]
  have hui (w : ι) : Integrable (fun s => ∫ z,(K z s).toReal*(κ z w).toReal*f z w ∂Λ) ν := by
    have hm : Measurable (fun t : α × β => (K t.2 t.1).toReal*(κ t.2 w).toReal*f t.2 w) := by fun_prop
    apply Integrable.of_bound hm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable M
    filter_upwards [] with s
    rw [he]
    have := hKprob s
    simpa using norm_integral_le_of_norm_le_const (μ := Λ.withDensity (fun z => K z s)) (ae_of_all _ (fun z => hgb z w))
  have := joint_probability ν Λ K κ hK hκ hK1 hκ1
  have hi : Integrable (fun t : α × β × ι => f t.2.1 t.2.2) (joint ν Λ K κ) :=
    Integrable.of_bound (hf.comp measurable_snd).aestronglyMeasurable M (ae_of_all _ (fun t => hfM _ _))
  rw [joint_integral ν Λ K κ hK hκ hKfin hκfin _ hi]
  simp_rw [integral_finsetSum _ (fun w _ => hzi _ w)]
  rw [integral_finsetSum _ (fun w _ => hui w)]
  simp_rw [he]
end KernelPotential.DriftTools.FiniteReference

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoisySums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity
lemma response_entropy_bound {d N : ℕ} (hN : 0 < N) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    -(∑ w,∫ s,xlog (rule.response η w s) ∂ν) ≤ Real.log (N:ℝ) := by
  have hi (w) : Integrable (fun s => xlog (rule.response η w s)) ν := integrable_xlog_bounded ν _
    (rule.measurable_response η w) (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1)
    (fun s => (rule.response_bounds hη w s).2)
  rw [← integral_finsetSum _ (fun w _ => hi w),← integral_neg]
  have hh := integral_mono_ae (integrable_finsetSum _ (fun w _ => hi w)).neg (integrable_const (Real.log (N:ℝ))) (by
    filter_upwards [] with s
    have h := finite_entropy_bound hN (fun w => rule.response η w s)
      (fun w => rule.lower_pos.le.trans (rule.response_bounds hη w s).1) (rule.response_sum hη s)
    simpa only [xlog,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib] using h)
  simpa using hh

lemma cutoff_mass_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    (∑ w,mass ν (rule.response η w)*Real.log ((DriftCutoff.level d (H/mass ν (rule.response η w)):ℝ)+2)) ≤
      2*Real.log H/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+25*(d:ℝ) := by
  let a := fun w => mass ν (rule.response η w)
  have ha (w) : 0 < a w := rule.mass_pos hη ν w
  have ha1 (w) : a w ≤ 1 := rule.mass_le_one hη ν w
  have has : ∑ w,a w=1 := rule.mass_sum hη ν
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hHd (w) : 1 ≤ H/a w := (le_div_iff₀ (ha w)).mpr (by simpa using (ha1 w).trans hH)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun w _ =>
    mul_le_mul_of_nonneg_left (DriftCutoff.log_level_bound d (by omega) (hHd w)) (ha w).le)
  have he : (∑ w,a w*(2*Real.log (H/a w)/(d:ℝ)+25*(d:ℝ)))=
      (2/(d:ℝ))*(∑ w,a w*Real.log (H/a w))+25*(d:ℝ) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib,← Finset.sum_mul,has,one_mul,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [he,weighted_log_ratio a ha has hHp] at hh
  have hE := finite_entropy_bound hN a (fun w => (ha w).le) has
  have hm := mul_le_mul_of_nonneg_left hE (show 0 ≤ 2/(d:ℝ) by positivity)
  calc
    _ ≤ (2/(d:ℝ))*(Real.log H+∑ w,-a w*Real.log (a w))+25*(d:ℝ) := hh
    _ ≤ (2/(d:ℝ))*(Real.log H+Real.log (N:ℝ))+25*(d:ℝ) := by linarith
    _ = _ := by ring

lemma joint_postCharge_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    (∫ t : Ambient d × Observation (d/16) d × Fin N,postCharge ν rule η t.2.1 t.2.2
      ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel) ≤
      35*(d:ℝ)+2*Real.log H/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  obtain ⟨M,_,hb⟩ := postCharge_uniform_bound hd ν hHp hν rule hη
  rw [joint_integral_by_message ν (observationBase (d/16) d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) rule.measurable_kernel (observationKernel_ne_top hη)
    (observationKernel_probability hη) rule.sum_kernel _ (measurable_postCharge hd ν hν rule hη)
    (fun z w => by rw [Real.norm_eq_abs,abs_of_nonneg (hb z w).1]; exact (hb z w).2)]
  simp only [PositiveRule.kernel,ENNReal.toReal_ofReal (rule.nonneg _ _)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun w _ => integrated_postCharge hd ν hH hν rule hη w)
  have hE := div_le_div_of_nonneg_right (response_entropy_bound hN ν rule hη) (show (0:ℝ) ≤ (d/16:ℕ) by positivity)
  have hL := cutoff_mass_bound hd hN ν hH rule hη
  simp_rw [mul_add] at hs
  simp only [Finset.sum_add_distrib,← Finset.sum_div,Finset.sum_neg_distrib,← Finset.sum_mul,rule.mass_sum hη ν,one_mul] at hs
  linarith

lemma positive_noisy_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η)
    (hηL : η ≤ Scale.radius (DriftCutoff.level d H)) :
    (∑ w,mass ν (rule.response η w)*Phi (post ν (rule.response η w))) ≤
      Phi ν+95*(d:ℝ)+6*Real.log H/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) := by
  have h1 := positive_noisy_comparison hd ν hH hν rule hη hηL
  have h2 := joint_postCharge_bound hd hN ν hH hν rule hη
  have h3 := DriftCutoff.log_level_bound d (by omega) hH
  linear_combination h1+h2+2*h3
end KernelPotential.NoisyDrift

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_PotentialContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.Continuity
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
open Coercivity Sphere EntropySupport

lemma tendsto_J {d : ℕ} (hd : 16 ≤ d) (f : ℕ → Ambient d → ℝ) (g : Ambient d → ℝ)
    (hf : ∀ n,Measurable (f n)) (hg : Measurable g) (_hf0 : ∀ n x,0 ≤ f n x) {H : ℝ} (_hH : 0 ≤ H)
    (hfH : ∀ n x,f n x ≤ H)
    (hlim : ∀ᵐ x ∂sphereProbability d,Filter.Tendsto (fun n => f n x) Filter.atTop (𝓝 (g x)))
    (s : Ambient d) :
    Filter.Tendsto (fun n => J (densityLaw (f n)) s) Filter.atTop (𝓝 (J (densityLaw g) s)) := by
  let K := fun u : Ambient d => (ENNReal.ofReal ‖u-s‖)⁻¹^(2*(d/16))
  have hK : Measurable K := ((measurable_id.sub_const s).norm.ennreal_ofReal.inv).pow_const _
  have hKI : (∫⁻ u,K u ∂sphereProbability d) ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact inverse_kernel_bound (sphereProbability d) (by positivity : 0 ≤ (9*3^d:ℝ))
      (by omega) (by omega) (fun z r hr => cap_bound (by omega) z hr) s
  have hl (h : Ambient d → ℝ) (hh : Measurable h) : J (densityLaw h) s =
      ∫⁻ u,ENNReal.ofReal (h u)*K u ∂sphereProbability d := by
    unfold J densityLaw
    exact lintegral_withDensity_eq_lintegral_mul _ hh.ennreal_ofReal hK
  rw [hl g hg]
  simp_rw [hl _ (hf _)]
  apply tendsto_lintegral_of_dominated_convergence (fun u => ENNReal.ofReal H*K u)
    (fun n => (hf n).ennreal_ofReal.mul hK)
    (fun n => ae_of_all _ (fun u => mul_le_mul_left (ENNReal.ofReal_le_ofReal (hfH n u)) _))
  · rw [lintegral_const_mul _ hK]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKI
  · filter_upwards [hlim,ae_lt_top hK hKI] with u hu hKu
    exact ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hu) (Or.inr hKu.ne)

lemma tendsto_Phi {d : ℕ} (hd : 16 ≤ d) (f : ℕ → Ambient d → ℝ) (g : Ambient d → ℝ)
    (hf : ∀ n,Measurable (f n)) (hg : Measurable g)
    (hf0 : ∀ n x,0 ≤ f n x) (hg0 : ∀ x,0 ≤ g x)
    {H : ℝ} (hH : 0 < H) (hfH : ∀ n x,f n x ≤ H) (hgH : ∀ x,g x ≤ H)
    (hfp : ∀ n,IsProbabilityMeasure (densityLaw (f n)))
    (hgp : IsProbabilityMeasure (densityLaw g))
    (hlim : ∀ᵐ x ∂sphereProbability d,Filter.Tendsto (fun n => f n x) Filter.atTop (𝓝 (g x))) :
    Filter.Tendsto (fun n => Phi (densityLaw (f n))) Filter.atTop (𝓝 (Phi (densityLaw g))) := by
  have (n : ℕ) : IsProbabilityMeasure (densityLaw (f n)) := hfp n
  have : IsProbabilityMeasure (densityLaw g) := hgp
  have hfB (n : ℕ) : BoundedDensity (densityLaw (f n)) := ⟨H,hH,density_bounded _ _ (hfH n)⟩
  have hgB : BoundedDensity (densityLaw g) := ⟨H,hH,density_bounded _ _ hgH⟩
  have hformula (n : ℕ) := Phi_density_formula hd (f n) (hf n) (hf0 n) (hfH n) _ (hfB n) rfl
  have hgformula := Phi_density_formula hd g hg hg0 hgH _ hgB rfl
  rw [hgformula]
  simp_rw [hformula]
  let a : ℝ := (1/2:ℝ)^(2*(d/16))
  let b : ℝ := H*(1+(9*3^d:ℝ)*2^((d-1)+2*(d/16)+1))
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨C,hC⟩ := ((isCompact_Icc (a := (0:ℝ)) (b := H)).image continuous_xlog).isBounded.exists_norm_le
  have hbound (n : ℕ) : ∀ᵐ s ∂sphereProbability d,
      ‖xlog (f n s)-f n s*Real.log (J (densityLaw (f n)) s).toReal‖ ≤
        C+H*(|Real.log a|+|Real.log b|) := by
    filter_upwards [ae_unit_norm (by omega : 0 < d)] with s hs
    have hj := J_real_bounds hd (densityLaw (f n)) hH (density_bounded _ _ (hfH n)) s hs
    change a ≤ _ ∧ _ ≤ b at hj
    have hll := Real.log_le_log ha hj.1
    have hlu := Real.log_le_log (ha.trans_le hj.1) hj.2
    have hab : |Real.log (J (densityLaw (f n)) s).toReal| ≤ |Real.log a|+|Real.log b| := by
      apply abs_le.mpr
      constructor
      · have h := neg_abs_le (Real.log a); have hh := abs_nonneg (Real.log b); linarith
      · have h := le_abs_self (Real.log b); have hh := abs_nonneg (Real.log a); linarith
    have hfx : ‖xlog (f n s)‖ ≤ C := hC _ (mem_image_of_mem _ ⟨hf0 n s,hfH n s⟩)
    calc
      _ ≤ ‖xlog (f n s)‖+‖f n s*Real.log (J (densityLaw (f n)) s).toReal‖ := norm_sub_le _ _
      _ ≤ C+H*(|Real.log a|+|Real.log b|) := by
        rw [norm_mul,Real.norm_eq_abs (f n s),abs_of_nonneg (hf0 n s),Real.norm_eq_abs]
        exact add_le_add hfx (mul_le_mul (hfH n s) hab (abs_nonneg _) hH.le)
  apply tendsto_integral_of_dominated_convergence (fun _ => C+H*(|Real.log a|+|Real.log b|))
    (fun n => ((continuous_xlog.measurable.comp (hf n)).sub ((hf n).mul (measurable_J _).ennreal_toReal.log)).aestronglyMeasurable)
    (integrable_const _) hbound
  filter_upwards [hlim,ae_unit_norm (by omega : 0 < d)] with s hs hsn
  have hJt := tendsto_J hd f g hf hg hf0 hH.le hfH hlim s
  have hJfin : J (densityLaw g) s ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (bounded_J hd (densityLaw g) hH (density_bounded _ _ hgH) s)
  have hJp : 0 < (J (densityLaw g) s).toReal := ha.trans_le (J_real_bounds hd (densityLaw g) hH (density_bounded _ _ hgH) s hsn).1
  have hjr := (ENNReal.continuousAt_toReal hJfin).tendsto.comp hJt
  exact (continuous_xlog.continuousAt.tendsto.comp hs).sub (hs.mul ((Real.continuousAt_log hJp.ne').tendsto.comp hjr))

end KernelPotential.Continuity

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_BayesContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.Bayes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open EntropySupport Coercivity Sphere DriftTools Continuity
lemma tendsto_mass {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (r : ℕ → α → ℝ) (g : α → ℝ) (hr : ∀ n,Measurable (r n))
    (hr0 : ∀ n s,0 ≤ r n s) (hr1 : ∀ n s,r n s ≤ 1)
    (hlim : ∀ᵐ s ∂ν,Tendsto (fun n => r n s) atTop (𝓝 (g s))) :
    Tendsto (fun n => mass ν (r n)) atTop (𝓝 (mass ν g)) := by
  exact tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ)) (fun n => (hr n).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hr0 n s)]; exact hr1 n s)) hlim

lemma tendsto_weighted_Phi_positive {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (r : ℕ → Ambient d → ℝ) (g : Ambient d → ℝ) (hr : ∀ n,Measurable (r n)) (hg : Measurable g)
    {ε : ℝ} (hε : 0 < ε) (hrε : ∀ n s,ε ≤ r n s) (hgε : ∀ s,ε ≤ g s)
    (hr1 : ∀ n s,r n s ≤ 1) (hg1 : ∀ s,g s ≤ 1)
    (hlim : ∀ᵐ s ∂ν,Tendsto (fun n => r n s) atTop (𝓝 (g s))) :
    Tendsto (fun n => mass ν (r n)*Phi (post ν (r n))) atTop (𝓝 (mass ν g*Phi (post ν g))) := by
  have hr0 (n s) : 0 ≤ r n s := hε.le.trans (hrε n s)
  have hg0 (s) : 0 ≤ g s := hε.le.trans (hgε s)
  have ha (n) : ε ≤ mass ν (r n) := (mass_bounds ν (r n) (hr n) hε (hrε n) (hr1 n)).1
  have hap (n) := hε.trans_le (ha n)
  have hb : ε ≤ mass ν g := (mass_bounds ν g hg hε hgε hg1).1
  have hbp := hε.trans_le hb
  have hmass := tendsto_mass ν r g hr hr0 hr1 hlim
  obtain ⟨f,hf,hf0,hfH,hνf⟩ := bounded_density_representation (sphereProbability d) ν hH hν
  let F := fun n s => f s*r n s/mass ν (r n)
  let G := fun s => f s*g s/mass ν g
  have hF (n) : Measurable (F n) := (hf.mul (hr n)).div_const _
  have hG : Measurable G := (hf.mul hg).div_const _
  have hF0 (n s) : 0 ≤ F n s := div_nonneg (mul_nonneg (hf0 s) (hr0 n s)) (hap n).le
  have hG0 (s) : 0 ≤ G s := div_nonneg (mul_nonneg (hf0 s) (hg0 s)) hbp.le
  have hFb (n s) : F n s ≤ H/ε := by
    apply (div_le_div_of_nonneg_left (mul_nonneg (hf0 s) (hr0 n s)) hε (ha n)).trans
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left (hr1 n s) (hf0 s)).trans (by simpa using hfH s)) hε.le
  have hGb (s) : G s ≤ H/ε := by
    apply (div_le_div_of_nonneg_left (mul_nonneg (hf0 s) (hg0 s)) hε hb).trans
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left (hg1 s) (hf0 s)).trans (by simpa using hfH s)) hε.le
  have hpost (n) : post ν (r n)=densityLaw (F n) := post_density _ _ f _ hf hf0 (hr n) hνf
  have hpostg : post ν g=densityLaw G := post_density _ _ f _ hf hf0 hg hνf
  have hfp (n) : IsProbabilityMeasure (densityLaw (F n)) := by
    rw [← hpost n]; exact post_probability ν _ (hr n) (hr0 n) (hr1 n) (hap n)
  have hgp : IsProbabilityMeasure (densityLaw G) := by
    rw [← hpostg]; exact post_probability ν _ hg hg0 hg1 hbp
  have hlimf : ∀ᵐ s ∂sphereProbability d,Tendsto (fun n => F n s) atTop (𝓝 (G s)) := by
    rw [hνf,ae_withDensity_iff hf.ennreal_ofReal] at hlim
    filter_upwards [hlim] with s hs
    by_cases hfz : f s=0
    · simp only [F,G,hfz,zero_mul,zero_div]; exact tendsto_const_nhds
    · exact (tendsto_const_nhds.mul (hs (by simpa using (lt_of_le_of_ne (hf0 s) (Ne.symm hfz))))).div hmass hbp.ne'
  have hp := tendsto_Phi hd F G hF hG hF0 hG0 (div_pos hH hε) hFb hGb hfp hgp hlimf
  simp_rw [← hpost,← hpostg] at hp
  exact hmass.mul hp
end KernelPotential.Bayes

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ContinuousDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity

lemma positive_continuous_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) (hc : ∀ w,Continuous (fun t => rule.prob t w)) :
    (∑ w,mass ν (rule.exactResponse w)*Phi (post ν (rule.exactResponse w))) ≤
      Phi ν+95*(d:ℝ)+6*Real.log H/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) := by
  let R := Scale.radius (DriftCutoff.level d H)
  have hR : 0 < R := Scale.radius_pos _
  let η : ℕ → ℝ := fun n => R/((n:ℝ)+1)
  have hη (n) : 0 < η n := div_pos hR (by positivity)
  have hηR (n) : η n ≤ R := div_le_self hR.le (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have ht : Tendsto η atTop (𝓝 0) := by
    have hh := tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (a := R)
    simpa only [mul_one_div,mul_zero] using hh
  have hconv (w : Fin N) : Tendsto (fun n => mass ν (rule.response (η n) w)*Phi (post ν (rule.response (η n) w))) atTop
      (𝓝 (mass ν (rule.exactResponse w)*Phi (post ν (rule.exactResponse w)))) := by
    apply tendsto_weighted_Phi_positive hd ν (lt_of_lt_of_le zero_lt_one hH) hν
      (fun n => rule.response (η n) w) (rule.exactResponse w)
      (fun n => rule.measurable_response _ w) (rule.measurable_exactResponse w) rule.lower_pos
      (fun n s => (rule.response_bounds (hη n) w s).1)
      (fun s => (rule.exactResponse_bounds w s).1)
      (fun n s => (rule.response_bounds (hη n) w s).2)
      (fun s => (rule.exactResponse_bounds w s).2)
    exact ae_of_all _ (fun s => rule.tendsto_response hc w s η hη ht)
  exact le_of_tendsto_of_tendsto' (tendsto_finsetSum _ (fun w _ => hconv w)) tendsto_const_nhds
    (fun n => positive_noisy_bound hd hN ν hH hν rule (hη n) (hηR n))

end KernelPotential.NoisyDrift

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_BorelDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity

lemma positive_borel_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (rule : PositiveRule (d/16) d N) :
    (∑ w,mass ν (rule.exactResponse w)*Phi (post ν (rule.exactResponse w))) ≤
      Phi ν+95*(d:ℝ)+6*Real.log H/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) := by
  have : IsProbabilityMeasure (gaussianRows (d/16) d) := by unfold gaussianRows; infer_instance
  let T : Ambient d × Mat (d/16) d → Mat (d/16) d × (Fin (d/16) → ℝ) := fun z => (z.2,projectVector z.2 z.1)
  have hT : Measurable T := measurable_snd.prodMk ((continuous_projectVector.comp (continuous_snd.prodMk continuous_fst)).measurable)
  let μ := (ν.prod (gaussianRows (d/16) d)).map T
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hT.aemeasurable
  obtain ⟨R,hR,hRl,hconv⟩ := rule.exists_continuous_approx hN μ
  have hæ := Measure.ae_ae_of_ae_prod (ae_of_ae_map hT.aemeasurable hconv)
  have he (w : Fin N) : ∀ᵐ s ∂ν,Tendsto (fun n => (R n).exactResponse w s) atTop (𝓝 (rule.exactResponse w s)) := by
    filter_upwards [hæ] with s hs
    apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    · intro n
      exact ((R n).measurable w |>.comp (measurable_id.prodMk ((continuous_projectVector.comp (continuous_id.prodMk continuous_const)).measurable))).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      filter_upwards [] with X
      rw [Real.norm_eq_abs,abs_of_nonneg ((R n).nonneg _ _)]
      exact (R n).le_one _ _
    · filter_upwards [hs] with X hX
      exact hX w
  have heps : 0 < rule.lower/(N:ℝ) := div_pos rule.lower_pos (by exact_mod_cast hN)
  have hconvPhi (w : Fin N) := tendsto_weighted_Phi_positive hd ν (lt_of_lt_of_le zero_lt_one hH) hν
    (fun n => (R n).exactResponse w) (rule.exactResponse w)
    (fun n => (R n).measurable_exactResponse w) (rule.measurable_exactResponse w) heps
    (fun n s => by rw [← hRl n]; exact ((R n).exactResponse_bounds w s).1)
    (fun s => (div_le_self rule.lower_pos.le (by exact_mod_cast hN)).trans (rule.exactResponse_bounds w s).1)
    (fun n s => ((R n).exactResponse_bounds w s).2) (fun s => (rule.exactResponse_bounds w s).2) (he w)
  exact le_of_tendsto_of_tendsto' (tendsto_finsetSum _ (fun w _ => hconvPhi w)) tendsto_const_nhds
    (fun n => positive_continuous_bound hd hN ν hH hν (R n) (hR n))

end KernelPotential.NoisyDrift

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_MassContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.Bayes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open EntropySupport Coercivity Sphere DriftTools Continuity
lemma tendsto_weighted_Phi_mass_positive {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (r : ℕ → Ambient d → ℝ) (g : Ambient d → ℝ) (hr : ∀ n,Measurable (r n)) (hg : Measurable g)
    (hr0 : ∀ n s,0 ≤ r n s) (hg0 : ∀ s,0 ≤ g s)
    {ε : ℝ} (hε : 0 < ε) (ha : ∀ n,ε ≤ mass ν (r n)) (hb : ε ≤ mass ν g)
    (hr1 : ∀ n s,r n s ≤ 1) (hg1 : ∀ s,g s ≤ 1)
    (hlim : ∀ᵐ s ∂ν,Tendsto (fun n => r n s) atTop (𝓝 (g s))) :
    Tendsto (fun n => mass ν (r n)*Phi (post ν (r n))) atTop (𝓝 (mass ν g*Phi (post ν g))) := by
  have hap (n) := hε.trans_le (ha n)
  have hbp := hε.trans_le hb
  have hmass := tendsto_mass ν r g hr hr0 hr1 hlim
  obtain ⟨f,hf,hf0,hfH,hνf⟩ := bounded_density_representation (sphereProbability d) ν hH hν
  let F := fun n s => f s*r n s/mass ν (r n)
  let G := fun s => f s*g s/mass ν g
  have hF (n) : Measurable (F n) := (hf.mul (hr n)).div_const _
  have hG : Measurable G := (hf.mul hg).div_const _
  have hF0 (n s) : 0 ≤ F n s := div_nonneg (mul_nonneg (hf0 s) (hr0 n s)) (hap n).le
  have hG0 (s) : 0 ≤ G s := div_nonneg (mul_nonneg (hf0 s) (hg0 s)) hbp.le
  have hFb (n s) : F n s ≤ H/ε := by
    apply (div_le_div_of_nonneg_left (mul_nonneg (hf0 s) (hr0 n s)) hε (ha n)).trans
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left (hr1 n s) (hf0 s)).trans (by simpa using hfH s)) hε.le
  have hGb (s) : G s ≤ H/ε := by
    apply (div_le_div_of_nonneg_left (mul_nonneg (hf0 s) (hg0 s)) hε hb).trans
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left (hg1 s) (hf0 s)).trans (by simpa using hfH s)) hε.le
  have hpost (n) : post ν (r n)=densityLaw (F n) := post_density _ _ f _ hf hf0 (hr n) hνf
  have hpostg : post ν g=densityLaw G := post_density _ _ f _ hf hf0 hg hνf
  have hfp (n) : IsProbabilityMeasure (densityLaw (F n)) := by
    rw [← hpost n]; exact post_probability ν _ (hr n) (hr0 n) (hr1 n) (hap n)
  have hgp : IsProbabilityMeasure (densityLaw G) := by
    rw [← hpostg]; exact post_probability ν _ hg hg0 hg1 hbp
  have hlimf : ∀ᵐ s ∂sphereProbability d,Tendsto (fun n => F n s) atTop (𝓝 (G s)) := by
    rw [hνf,ae_withDensity_iff hf.ennreal_ofReal] at hlim
    filter_upwards [hlim] with s hs
    by_cases hfz : f s=0
    · simp only [F,G,hfz,zero_mul,zero_div]; exact tendsto_const_nhds
    · exact (tendsto_const_nhds.mul (hs (by simpa using (lt_of_le_of_ne (hf0 s) (Ne.symm hfz))))).div hmass hbp.ne'
  have hp := tendsto_Phi hd F G hF hG hF0 hG0 (div_pos hH hε) hFb hGb hfp hgp hlimf
  simp_rw [← hpost,← hpostg] at hp
  exact hmass.mul hp
end KernelPotential.Bayes

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_GeneralDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity
namespace LocalRule
lemma positive_mass {k d N : ℕ} (rule : LocalRule k d N) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (w : Fin N) :
    mass ν ((rule.positive hN ε hε hε1).exactResponse w)=(1-ε)*mass ν (rule.response w)+ε/(N:ℝ) := by
  simp_rw [mass,rule.positive_response]
  rw [integral_add ((integrable_rule ν _ (rule.measurable_response w)
    (fun s => (rule.response_bounds w s).1) (fun s => (rule.response_bounds w s).2)).const_mul _) (integrable_const _),integral_const_mul]
  simp
lemma positive_post_zero {k d N : ℕ} (rule : LocalRule k d N) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (w : Fin N) (ha : mass ν (rule.response w)=0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : post ν ((rule.positive hN ε hε hε1).exactResponse w)=ν := by
  have hr : rule.response w=ᵐ[ν] 0 := (integral_eq_zero_iff_of_nonneg
    (fun s => (rule.response_bounds w s).1) (integrable_rule ν _ (rule.measurable_response w)
      (fun s => (rule.response_bounds w s).1) (fun s => (rule.response_bounds w s).2))).mp ha
  have hp : 0 < ε/(N:ℝ) := div_pos hε (by exact_mod_cast hN)
  rw [post,rule.positive_mass hN ν ε hε hε1 w,ha,mul_zero,zero_add]
  calc
    _ = ν.withDensity (fun _ => (1:ℝ≥0∞)) := withDensity_congr_ae (by
      filter_upwards [hr] with s hs
      rw [rule.positive_response,hs,Pi.zero_apply,mul_zero,zero_add,div_self hp.ne']
      simp)
    _ = ν := by simp
end LocalRule

lemma borel_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (rule : LocalRule (d/16) d N) :
    (∑ w,mass ν (rule.response w)*Phi (post ν (rule.response w))) ≤
      Phi ν+95*(d:ℝ)+6*Real.log H/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) := by
  let ε : ℕ → ℝ := fun n => (1/2:ℝ)/((n:ℝ)+1)
  have hε (n) : 0 < ε n := div_pos (by norm_num) (by positivity)
  have hε2 (n) : ε n ≤ (1/2:ℝ) := div_le_self (by norm_num) (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hε1 (n) : ε n ≤ 1 := (hε2 n).trans (by norm_num)
  have ht : Tendsto ε atTop (𝓝 0) := by
    have hh := tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (a := (1/2:ℝ))
    simpa only [mul_one_div,mul_zero] using hh
  let R := fun n => rule.positive hN (ε n) (hε n) (hε1 n)
  have hconv (w : Fin N) : Tendsto (fun n => mass ν ((R n).exactResponse w)*Phi (post ν ((R n).exactResponse w))) atTop
      (𝓝 (mass ν (rule.response w)*Phi (post ν (rule.response w)))) := by
    have hg0 (s) := (rule.response_bounds w s).1
    have hg1 (s) := (rule.response_bounds w s).2
    have ha0 : 0 ≤ mass ν (rule.response w) := integral_nonneg hg0
    by_cases haz : mass ν (rule.response w)=0
    · have he (n) : post ν ((R n).exactResponse w)=ν := rule.positive_post_zero hN ν w haz (ε n) (hε n) (hε1 n)
      simp_rw [he,show ∀ n,mass ν ((R n).exactResponse w)=(1-ε n)*mass ν (rule.response w)+ε n/(N:ℝ) from
        fun _ => rule.positive_mass hN ν _ _ _ w,haz,mul_zero,zero_add,zero_mul]
      simpa using (ht.div_const (N:ℝ)).mul_const (Phi ν)
    · have hap : 0 < mass ν (rule.response w) := lt_of_le_of_ne ha0 (Ne.symm haz)
      apply tendsto_weighted_Phi_mass_positive hd ν (lt_of_lt_of_le zero_lt_one hH) hν
        (fun n => (R n).exactResponse w) (rule.response w)
        (fun n => (R n).measurable_exactResponse w) (rule.measurable_response w)
        (fun n s => (R n).lower_pos.le.trans ((R n).exactResponse_bounds w s).1) hg0 (half_pos hap)
        (fun n => ?_) (by linarith)
        (fun n s => ((R n).exactResponse_bounds w s).2) hg1
      · apply ae_of_all
        intro s
        simp_rw [show ∀ n,(R n).exactResponse w s=(1-ε n)*rule.response w s+ε n/(N:ℝ) from
          fun _ => rule.positive_response hN _ _ _ w s]
        simpa using (((tendsto_const_nhds (x := (1:ℝ))).sub ht).mul_const (rule.response w s)).add (ht.div_const (N:ℝ))
      · change _ ≤ mass ν ((rule.positive hN _ _ _).exactResponse w)
        rw [rule.positive_mass]
        have := hε2 n
        have hp : 0 ≤ ε n/(N:ℝ) := (div_pos (hε n) (by exact_mod_cast hN)).le
        nlinarith
  exact le_of_tendsto_of_tendsto' (tendsto_finsetSum _ (fun w _ => hconv w)) tendsto_const_nhds
    (fun n => positive_borel_bound hd hN ν hH hν (R n))
end KernelPotential.NoisyDrift

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_LocalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.MassPotential
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Coercivity Bayes NoisyDrift
lemma local_energy_bound_oai {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] (hρ : ρ ≤ sphereProbability d)
    (rule : LocalRule (d/16) d N) :
    (∑ w,energy (ρ.withDensity (fun s => ENNReal.ofReal (rule.response w s)))) ≤
      energy ρ+(ρ univ).toReal*(95*(d:ℝ)+6*Real.log (1/(ρ univ).toReal)/(d:ℝ)+
        2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ)) := by
  by_cases hz : ρ univ=0
  · have he := Measure.measure_univ_eq_zero.mp hz
    simp [he,energy_zero]
  · let a := (ρ univ).toReal
    have ha : 0 < a := ENNReal.toReal_pos hz (measure_ne_top _ _)
    have ha1 : a ≤ 1 := by
      have hh := hρ univ
      rw [measure_univ (μ := sphereProbability d)] at hh
      simpa [a] using ENNReal.toReal_mono ENNReal.one_ne_top hh
    let ν := proper ρ
    have : IsProbabilityMeasure ν := proper_probability ρ
    have hH : 1 ≤ 1/a := (le_div_iff₀ ha).mpr (by simpa using ha1)
    have hν : ν ≤ ENNReal.ofReal (1/a) • sphereProbability d := by
      have he : ENNReal.ofReal (1/a)=(ρ univ)⁻¹ := by
        rw [one_div,ENNReal.ofReal_inv_of_pos ha,ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rw [he]
      change proper ρ ≤ _
      rw [proper,ite_eq_right hz]
      exact smul_le_smul_left _ hρ
    have he (w : Fin N) : energy (ρ.withDensity (fun s => ENNReal.ofReal (rule.response w s)))=
        a*(mass ν (rule.response w)*Phi (post ν (rule.response w))) := by
      have := density_finite ν (rule.response w) (fun s => (rule.response_bounds w s).2)
      calc _ = energy (ENNReal.ofReal a • ν.withDensity (fun s => ENNReal.ofReal (rule.response w s))) := by
                 congr 1
                 rw [← withDensity_smul_measure]
                 congr 1
                 exact (mass_smul_proper ρ).symm
           _ = a*energy (ν.withDensity (fun s => ENNReal.ofReal (rule.response w s))) := energy_smul _ a ha.le
           _ = _ := by rw [energy_density ν _ (rule.measurable_response w)
                       (fun s => (rule.response_bounds w s).1) (fun s => (rule.response_bounds w s).2)]
    have hh := mul_le_mul_of_nonneg_left (borel_bound hd hN ν hH hν rule) ha.le
    simp_rw [he]
    rw [← Finset.mul_sum]
    rw [energy_proper]
    change _ ≤ a*Phi ν+a*(95*(d:ℝ)+6*Real.log (1/a)/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ))
    calc _ ≤ a*(Phi ν+95*(d:ℝ)+6*Real.log (1/a)/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ)) := hh
         _ = _ := by ring
end KernelPotential.MassPotential

end OAI
end

theorem solution : type_of% @OAI.KernelPotential.MassPotential.local_energy_bound_oai := @OAI.KernelPotential.MassPotential.local_energy_bound_oai
