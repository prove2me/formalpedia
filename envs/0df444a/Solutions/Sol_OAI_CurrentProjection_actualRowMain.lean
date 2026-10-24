-- Prove2me | solution 1 for OAI.CurrentProjection.actualRowMain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:58:05.079+00:00
-- url     : https://prove2.me/submissions/a558ee44-bfc0-4e34-822b-eff1b935c174

import Mathlib
import Definitions.Def_GaussianReplacement
import Definitions.Def_OAIQWCP000

section
-- module Solutions.OAIQW_CurrentProjection.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection

section InverseMoments

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
lemma inverse_pow_dyadic_majorant (f : X → ℝ) (m : ℕ) (hf : ∀ x, 0 ≤ f x) (x : X) :
    ENNReal.ofReal ((f x)⁻¹ ^ m) ≤
      1 + ∑' k : ℕ, ({x | f x ≤ (1 / 2 : ℝ) ^ k}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1)))) x := by
  classical
  by_cases hzero : f x = 0
  · simp only [hzero, inv_zero]
    exact le_add_of_le_left (by cases m <;> simp)
  have hxpos : 0 < f x := lt_of_le_of_ne (hf x) (Ne.symm hzero)
  by_cases hxone : 1 ≤ f x
  · apply le_add_of_le_left
    have h : (f x)⁻¹ ^ m ≤ 1 :=
      pow_le_one₀ (inv_nonneg.mpr (hf x)) (inv_le_one_of_one_le₀ hxone)
    simpa using ENNReal.ofReal_le_ofReal h
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near_of_lt_one hxpos
    (le_of_not_ge hxone) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hinv : (f x)⁻¹ ≤ (2 : ℝ) ^ (k + 1) := by
    have h := (inv_le_inv₀ hxpos (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _)).2 hklo.le
    simpa using h
  have hpow : ENNReal.ofReal ((f x)⁻¹ ^ m) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) := by
    apply ENNReal.ofReal_le_ofReal
    simpa [← pow_mul, Nat.mul_comm] using pow_le_pow_left₀ (inv_nonneg.mpr (hf x)) hinv m
  calc
    ENNReal.ofReal ((f x)⁻¹ ^ m) ≤ ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) := hpow
    _ = ({x | f x ≤ (1 / 2 : ℝ) ^ k}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1)))) x := by
      rw [Set.indicator_of_mem (show x ∈ {x | f x ≤ (1 / 2 : ℝ) ^ k} from hkhi)]
    _ ≤ ∑' j : ℕ, ({x | f x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (j + 1)))) x :=
      ENNReal.le_tsum (f := fun j => ({x | f x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (j + 1)))) x) k
    _ ≤ 1 + ∑' j : ℕ, ({x | f x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (j + 1)))) x := le_add_left le_rfl

lemma dyadic_power_cancel (m k : ℕ) :
    (2 : ℝ) ^ (m * (k + 1)) * ((1 / 2 : ℝ) ^ k) ^ (m + 1) =
      (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ k := by
  rw [Nat.mul_add, mul_one, pow_add, pow_succ]
  have h : (2 : ℝ) ^ (m * k) * ((1 / 2 : ℝ) ^ k) ^ m = 1 := by
    rw [Nat.mul_comm m k, pow_mul, ← mul_pow, ← mul_pow]
    norm_num
  calc
    2 ^ (m * k) * 2 ^ m * (((1 / 2 : ℝ) ^ k) ^ m * (1 / 2 : ℝ) ^ k) =
      (2 ^ (m * k) * ((1 / 2 : ℝ) ^ k) ^ m) * (2 ^ m * (1 / 2 : ℝ) ^ k) := by ring
    _ = _ := by rw [h, one_mul]




theorem inverse_moment_of_tube_bound (μ : Measure X) (f : X → ℝ) (m : ℕ)
    (hf : Measurable f) (hnonneg : ∀ x, 0 ≤ f x) (C : ℝ≥0∞)
    (htube : ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ {x | f x ≤ r} ≤ C * ENNReal.ofReal (r ^ (m + 1))) :
    ∫⁻ x, ENNReal.ofReal ((f x)⁻¹ ^ m) ∂μ ≤
      μ Set.univ + C * (2 : ℝ≥0∞) ^ (m + 1) := by
  classical
  let g : ℕ → X → ℝ≥0∞ := fun k =>
    ({x | f x ≤ (1 / 2 : ℝ) ^ k}).indicator
      (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))))
  have hg : ∀ k, Measurable (g k) := fun k =>
    measurable_const.indicator (measurableSet_le hf measurable_const)
  calc
    ∫⁻ x, ENNReal.ofReal ((f x)⁻¹ ^ m) ∂μ ≤ ∫⁻ x, 1 + ∑' k, g k x ∂μ :=
      lintegral_mono (inverse_pow_dyadic_majorant f m hnonneg)
    _ = μ Set.univ + ∑' k, ∫⁻ x, g k x ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_const, one_mul, lintegral_tsum (fun k => (hg k).aemeasurable)]
    _ ≤ μ Set.univ + ∑' k, C * ENNReal.ofReal ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ k) := by
      apply add_le_add le_rfl
      apply ENNReal.tsum_le_tsum
      intro k
      dsimp only [g]
      rw [lintegral_indicator (measurableSet_le hf measurable_const), lintegral_const,
        Measure.restrict_apply_univ]
      calc
        ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) * μ {x | f x ≤ (1 / 2 : ℝ) ^ k} ≤
            ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) *
              (C * ENNReal.ofReal (((1 / 2 : ℝ) ^ k) ^ (m + 1))) := by
          gcongr
          exact htube _ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
        _ = _ := by
          rw [← mul_assoc, mul_comm _ C, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            dyadic_power_cancel]
    _ = μ Set.univ + C * (2 : ℝ≥0∞) ^ (m + 1) := by
      simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ m),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      norm_num [pow_succ, mul_assoc, ENNReal.ofReal_div_of_pos]

end InverseMoments




section FrostmanGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


omit [BorelSpace E] in

theorem HasLocalMassBound.any_center {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (z : E) {r : ℝ} (hr : 0 < r) :
    ν (Metric.closedBall z r) ≤ ENNReal.ofReal ((2 * r) ^ a) := by
  by_cases hmass : ν (Metric.closedBall z r) = 0
  · simp [hmass]
  obtain ⟨t, htball, htsupp⟩ := ν.nonempty_inter_support_of_pos (pos_iff_ne_zero.mpr hmass)
  refine (measure_mono ?_).trans (hν t htsupp (2 * r) (by positivity))
  intro x hx
  apply Metric.mem_closedBall.mpr
  calc
    dist x t ≤ dist x z + dist z t := dist_triangle _ _ _
    _ ≤ r + r := add_le_add (Metric.mem_closedBall.mp hx)
      (by simpa [dist_comm] using Metric.mem_closedBall.mp htball)
    _ = 2 * r := by ring


theorem card_le_volume_ratio (s : Finset E) {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hs : ∀ x ∈ s, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) :
    (s.card : ℝ) ≤ ((R + r / 2) / (r / 2)) ^ Module.finrank ℝ E := by
  classical
  let ν : Measure E := Measure.addHaar
  let δ : ℝ := r / 2
  let ρ : ℝ := R + r / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A : Set E := ⋃ c ∈ s, Metric.ball c δ
  have hd : Set.Pairwise (s : Set E) (fun c d => Disjoint (Metric.ball c δ) (Metric.ball d δ)) := by
    intro c hc d hd hcd
    apply Metric.ball_disjoint_ball
    simpa [δ] using hsep c hc d hd hcd
  have hsub : A ⊆ Metric.ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply Metric.ball_subset_ball'
    dsimp [δ, ρ]
    rw [dist_zero_right]
    linarith [hs x hx]
  have I :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * ν (Metric.ball 0 1) ≤
        ENNReal.ofReal (ρ ^ Module.finrank ℝ E) * ν (Metric.ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * ν (Metric.ball 0 1) = ν A := by
        dsimp only [A]
        rw [measure_biUnion_finset hd (fun _ _ => Metric.isOpen_ball.measurableSet)]
        simp only [ν.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ν (Metric.ball (0 : E) ρ) := measure_mono hsub
      _ = _ := ν.addHaar_ball_of_pos 0 hρ
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (Metric.measure_ball_pos ν 0 zero_lt_one).ne'
      measure_ball_lt_top.ne).mp I
  have K : (s.card : ℝ) * δ ^ Module.finrank ℝ E ≤ ρ ^ Module.finrank ℝ E := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) J
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos hδ _)).mpr K

end FrostmanGeometry

section FiniteNets

variable {E : Type*} [PseudoMetricSpace E]



theorem exists_net_of_finite_packing_bound (A : Set E) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hcard : ∀ s : Finset E, (∀ x ∈ s, x ∈ A) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) → s.card ≤ N) :
    ∃ s : Finset E, (∀ x ∈ s, x ∈ A) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) ∧
      ∀ x ∈ A, ∃ y ∈ s, dist x y ≤ r := by
  classical
  let S : Set ℕ := {n | ∃ s : Finset E, (∀ x ∈ s, x ∈ A) ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) ∧ s.card = n}
  have hS : S.Finite := (Set.finite_Iic N).subset (by
    rintro n ⟨s, hs, hsep, rfl⟩
    exact hcard s hs hsep)
  have hS0 : S.Nonempty := ⟨0, ∅, by simp⟩
  obtain ⟨n, hn, hmax⟩ := Set.exists_max_image S id hS hS0
  obtain ⟨s, hs, hsep, rfl⟩ := hn
  refine ⟨s, hs, hsep, ?_⟩
  intro x hx
  by_contra! hnot
  have hxs : x ∉ s := by
    intro h
    have := hnot x h
    simpa using lt_of_le_of_lt hr this
  have hins : ∀ y ∈ insert x s, y ∈ A := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hx
    · exact hs y hy
  have hsep' : ∀ y ∈ insert x s, ∀ z ∈ insert x s, y ≠ z → r < dist y z := by
    intro y hy z hz hne
    rcases Finset.mem_insert.mp hy with hxy | hys
    · subst y
      rcases Finset.mem_insert.mp hz with hxz | hzs
      · exact (hne hxz.symm).elim
      · exact hnot z hzs
    · rcases Finset.mem_insert.mp hz with hxz | hzs
      · subst z
        simpa [dist_comm] using hnot y hys
      · exact hsep y hys z hzs hne
  have hinS : (insert x s).card ∈ S := ⟨insert x s, hins, hsep', rfl⟩
  have hh := hmax _ hinS
  simp only [id_eq, Finset.card_insert_of_notMem hxs] at hh
  omega

end FiniteNets

section EuclideanNets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]



theorem exists_unit_ball_net {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset E, (∀ x ∈ s, ‖x‖ ≤ 1) ∧
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ E ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ r := by
  classical
  have hbound : ∀ s : Finset E, (∀ x ∈ s, ‖x‖ ≤ 1) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) →
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ E := by
    intro s hs hsep
    refine (card_le_volume_ratio s hr zero_le_one hs
      (fun x hx y hy hne => (hsep x hx y hy hne).le)).trans ?_
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_div_iff₀ (by positivity : 0 < r / 2) hr).mpr
    nlinarith
  obtain ⟨s, hs, hsep, hnet⟩ := exists_net_of_finite_packing_bound
    {x : E | ‖x‖ ≤ 1} hr.le ⌈(3 / r) ^ Module.finrank ℝ E⌉₊
    (by
      intro s hs hsep
      exact_mod_cast (hbound s hs hsep).trans (Nat.le_ceil _))
  exact ⟨s, hs, hbound s hs hsep, hnet⟩

end EuclideanNets

section AffineTubes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open EuclideanGeometry



theorem exists_affine_tube_cover (L : AffineSubspace ℝ E) [Nonempty L]
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset L.direction,
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ L.direction ∧
      ∀ t : E, ‖t‖ ≤ 1 → Metric.infDist t L ≤ r →
        ∃ y ∈ s, dist t ((y : E) + (orthogonalProjection L 0 : E)) ≤ 2 * r := by
  classical
  obtain ⟨s, _, hcard, hnet⟩ := exists_unit_ball_net (E := L.direction) hr hr1
  refine ⟨s, hcard, ?_⟩
  intro t ht hdist
  obtain ⟨y, hy, hty⟩ := hnet (L.direction.orthogonalProjectionOnto t)
    ((L.direction.norm_orthogonalProjectionOnto_apply_le t).trans ht)
  refine ⟨y, hy, ?_⟩
  have hproj : (orthogonalProjection L t : E) =
      (L.direction.orthogonalProjectionOnto t : E) + (orthogonalProjection L 0 : E) := by
    have h := (orthogonalProjection L).map_vadd (0 : E) t
    simpa only [vadd_eq_add, add_zero, orthogonalProjection_contLinear,
      AffineSubspace.coe_vadd] using congrArg (fun x : L => (x : E)) h
  have hpdist : dist (orthogonalProjection L t : E)
      ((y : E) + (orthogonalProjection L 0 : E)) ≤ r := by
    rw [hproj, dist_add_right]
    exact hty
  have hd : dist t (orthogonalProjection L t : E) ≤ r := by
    rwa [dist_orthogonalProjection_eq_infDist]
  calc
    dist t ((y : E) + (orthogonalProjection L 0 : E)) ≤
        dist t (orthogonalProjection L t : E) +
          dist (orthogonalProjection L t : E) ((y : E) + (orthogonalProjection L 0 : E)) :=
      dist_triangle _ _ _
    _ ≤ r + r := add_le_add hd hpdist
    _ = 2 * r := by ring


theorem HasLocalMassBound.affine_tube {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ν {t | Metric.infDist t L ≤ r} ≤
      ENNReal.ofReal ((3 / r) ^ Module.finrank ℝ L.direction * (4 * r) ^ a) := by
  classical
  obtain ⟨s, hcard, hcover⟩ := exists_affine_tube_cover L hr hr1
  let c : L.direction → E := fun y => (y : E) + (orthogonalProjection L 0 : E)
  have hsub : {t | Metric.infDist t L ≤ r} ≤ᵐ[ν]
      ⋃ y ∈ s, Metric.closedBall (c y) (2 * r) := by
    filter_upwards [ν.support_mem_ae] with t ht
    intro hdist
    have htunit : ‖t‖ ≤ 1 := by simpa using hsupport ht
    obtain ⟨y, hy, hty⟩ := hcover t htunit hdist
    exact mem_iUnion₂.mpr ⟨y, hy, hty⟩
  calc
    ν {t | Metric.infDist t L ≤ r} ≤ ν (⋃ y ∈ s, Metric.closedBall (c y) (2 * r)) :=
      measure_mono_ae hsub
    _ ≤ ∑ y ∈ s, ν (Metric.closedBall (c y) (2 * r)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ s, ENNReal.ofReal ((4 * r) ^ a) := by
      refine Finset.sum_le_sum fun y _ => ?_
      simpa only [show (2 : ℝ) * (2 * r) = 4 * r by ring] using
        hν.any_center (c y) (r := 2 * r) (by positivity)
    _ = (s.card : ℝ≥0∞) * ENNReal.ofReal ((4 * r) ^ a) := by simp
    _ ≤ ENNReal.ofReal ((3 / r) ^ Module.finrank ℝ L.direction) *
        ENNReal.ofReal ((4 * r) ^ a) := by
      gcongr
      exact_mod_cast ENNReal.ofReal_le_ofReal hcard
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm


lemma tube_radius_factors (ℓ : ℕ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    (3 / r) ^ ℓ * (4 * r) ^ a =
      (3 : ℝ) ^ ℓ * (4 : ℝ) ^ a * r ^ (a - ℓ) := by
  rw [div_pow, Real.mul_rpow (by norm_num) hr.le,
    Real.rpow_sub_natCast hr.ne']
  ring


theorem HasLocalMassBound.affine_tube_pow {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] (k : ℕ)
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + k ≤ a)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ν {t | Metric.infDist t L ≤ r} ≤
      ENNReal.ofReal ((3 : ℝ) ^ Module.finrank ℝ L.direction * (4 : ℝ) ^ a) *
        ENNReal.ofReal (r ^ k) := by
  refine (hν.affine_tube hsupport L hr hr1).trans ?_
  rw [tube_radius_factors _ _ hr, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)



end AffineTubes




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.MixedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection

section MixedGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]


omit [MeasurableSpace E] [BorelSpace E] in
lemma infDist_eq_norm_sub_projection (V : Submodule ℝ E) (v : E) :
    Metric.infDist v (V : Set E) = ‖v - V.starProjection v‖ := by
  rw [Submodule.starProjection_minimal, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma infDist_submodule_smul (V : Submodule ℝ E) (v : E) (c : ℝ) :
    Metric.infDist (c • v) (V : Set E) = |c| * Metric.infDist v (V : Set E) := by
  simp only [infDist_eq_norm_sub_projection, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]


theorem exists_radial_tube_cover (V : Submodule ℝ E) (s : E)
    {R η : ℝ} (hR : 0 < R) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ t : Finset V, (t.card : ℝ) ≤ (3 / η) ^ Module.finrank ℝ V ∧
      ∀ u : E, ‖u - s‖ ≤ R → Metric.infDist (u - s) (V : Set E) ≤ η * R →
        ∃ y ∈ t, dist u (s + R • (y : E)) ≤ 2 * (η * R) := by
  classical
  obtain ⟨t, _, htcard, hnet⟩ := exists_unit_ball_net (E := V) hη hη1
  refine ⟨t, htcard, ?_⟩
  intro u hu huV
  let z : E := R⁻¹ • (u - s)
  have hz : ‖z‖ ≤ 1 := by
    dsimp [z]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_le_iff₀ hR).mpr (by simpa using hu)
  obtain ⟨y, hyt, hzy⟩ := hnet (V.orthogonalProjectionOnto z)
    ((V.norm_orthogonalProjectionOnto_apply_le z).trans hz)
  have hzV : ‖z - V.starProjection z‖ ≤ η := by
    rw [← infDist_eq_norm_sub_projection]
    dsimp [z]
    rw [infDist_submodule_smul, abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_le_iff₀ hR).mpr (by simpa [mul_comm] using huV)
  have hdist : dist z (y : E) ≤ 2 * η := by
    calc
      dist z (y : E) ≤ dist z (V.orthogonalProjectionOnto z : E) +
          dist (V.orthogonalProjectionOnto z : E) (y : E) := dist_triangle _ _ _
      _ ≤ η + η := add_le_add (by simpa [dist_eq_norm] using hzV) hzy
      _ = 2 * η := by ring
  refine ⟨y, hyt, ?_⟩
  have he : u = s + R • z := by
    dsimp [z]
    rw [smul_inv_smul₀ hR.ne']
    abel
  rw [he, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hR]
  nlinarith


theorem AmbientGrowth.radial_tube {μ : Measure E} {a : ℕ} {A : ℝ}
    (hμ : AmbientGrowth μ a A) (V : Submodule ℝ E) (s : E)
    {R η : ℝ} (hR : 0 < R) (hη : 0 < η) (hη1 : η ≤ 1) :
    μ {u | ‖u - s‖ ≤ R ∧ Metric.infDist (u - s) (V : Set E) ≤ η * R} ≤
      ENNReal.ofReal ((3 / η) ^ Module.finrank ℝ V * (A * (2 * (η * R)) ^ a)) := by
  classical
  obtain ⟨t, htcard, htcover⟩ := exists_radial_tube_cover V s hR hη hη1
  calc
    μ {u | ‖u - s‖ ≤ R ∧ Metric.infDist (u - s) (V : Set E) ≤ η * R} ≤
        μ (⋃ y ∈ t, Metric.closedBall (s + R • (y : E)) (2 * (η * R))) := by
      apply measure_mono
      intro u hu
      obtain ⟨y, hy, huy⟩ := htcover u hu.1 hu.2
      exact mem_iUnion.2 ⟨y, mem_iUnion.2 ⟨hy, huy⟩⟩
    _ ≤ ∑ y ∈ t, μ (Metric.closedBall (s + R • (y : E)) (2 * (η * R))) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ t, ENNReal.ofReal (A * (2 * (η * R)) ^ a) := by
      exact Finset.sum_le_sum fun y _ => hμ _ _ (by positivity)
    _ = (t.card : ℝ≥0∞) * ENNReal.ofReal (A * (2 * (η * R)) ^ a) := by simp
    _ ≤ ENNReal.ofReal ((3 / η) ^ Module.finrank ℝ V) *
        ENNReal.ofReal (A * (2 * (η * R)) ^ a) := by
      gcongr
      exact_mod_cast ENNReal.ofReal_le_ofReal htcard
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

end MixedGeometry


section MixedRadial
variable {E : Type*} [NormedAddCommGroup E] [innerProductSpaceRealE : InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma tube_radius_margin (h a k : ℕ) (A R η : ℝ)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hη : 0 < η) (hη1 : η ≤ 1) (hmargin : h+k ≤ a) :
    (3 / η) ^ h * (A * (2 * (η * R)) ^ a) ≤
      (3 ^ h * 2 ^ a * A * R ^ a) * η ^ k := by
  have he : η ^ a = η ^ h * η ^ (a-h) := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : h ≤ a)]
  calc
    (3 / η) ^ h * (A * (2 * (η * R)) ^ a) =
        (3 ^ h * 2 ^ a * A * R ^ a) * η ^ (a-h) := by
      simp only [div_pow, mul_pow]
      rw [he]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hη.le hη1 (by omega)) (by positivity)

lemma AmbientGrowth.radial_tube_pow {μ : Measure E} {a : ℕ} {A : ℝ}
    (hμ : AmbientGrowth μ a A) (hA : 0 ≤ A) (V : Submodule ℝ E) (s : E)
    (k : ℕ) (hmargin : Module.finrank ℝ V + k ≤ a)
    {R η : ℝ} (hR : 0 < R) (hη : 0 < η) (hη1 : η ≤ 1) :
    μ {u | ‖u - s‖ ≤ R ∧ Metric.infDist (u - s) (V : Set E) ≤ η * R} ≤
      ENNReal.ofReal (3 ^ Module.finrank ℝ V * 2 ^ a * A * R ^ a) *
        ENNReal.ofReal (η ^ k) := by
  refine (hμ.radial_tube V s hR hη hη1).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (tube_radius_margin _ _ k A R η hA hR.le hη hη1 hmargin)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma measurableSet_radialShell (s : E) (R : ℝ) : MeasurableSet (radialShell s R) := by
  have hf : Measurable (fun u : E => ‖u - s‖) := by fun_prop
  exact (measurableSet_lt measurable_const hf).inter (measurableSet_le hf measurable_const)


theorem AmbientGrowth.shell_normalized_inverse {μ : Measure E} {a m : ℕ} {A : ℝ}
    (hμ : AmbientGrowth μ a A) (hA : 0 ≤ A) (V : Submodule ℝ E) (s : E)
    (hmargin : Module.finrank ℝ V + (m+1) ≤ a) {R : ℝ} (hR : 0 < R) :
    ∫⁻ u in radialShell s R,
      ENNReal.ofReal (((Metric.infDist (u-s) (V : Set E) / R)⁻¹) ^ m) ∂μ ≤
      ENNReal.ofReal ((1 + 3 ^ Module.finrank ℝ V * 2 ^ (a+m+1)) * A * R ^ a) := by
  let f : E → ℝ := fun u => Metric.infDist (u-s) (V : Set E) / R
  have hf : Measurable f := by
    exact ((Metric.continuous_infDist_pt _).measurable.comp (by fun_prop)).div_const R
  have hnonneg : ∀ u, 0 ≤ f u := fun u => div_nonneg Metric.infDist_nonneg hR.le
  have htube (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
      (μ.restrict (radialShell s R)) {u | f u ≤ η} ≤
        ENNReal.ofReal (3 ^ Module.finrank ℝ V * 2 ^ a * A * R ^ a) *
          ENNReal.ofReal (η ^ (m+1)) := by
    rw [Measure.restrict_apply (measurableSet_le hf measurable_const)]
    refine (measure_mono ?_).trans (hμ.radial_tube_pow hA V s (m+1) hmargin hR hη hη1)
    intro u hu
    exact ⟨hu.2.2, (div_le_iff₀ hR).mp hu.1⟩
  have hmass : μ (radialShell s R) ≤ ENNReal.ofReal (A * R ^ a) := by
    refine (measure_mono ?_).trans (hμ s R hR)
    intro u hu
    exact (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hu.2))
  calc
    _ ≤ μ (radialShell s R) + ENNReal.ofReal (3 ^ Module.finrank ℝ V * 2 ^ a * A * R ^ a) *
        (2 : ℝ≥0∞) ^ (m+1) := by
      simpa only [f, Measure.restrict_apply_univ] using
        inverse_moment_of_tube_bound (μ.restrict (radialShell s R)) f m hf hnonneg _ htube
    _ ≤ ENNReal.ofReal (A * R ^ a) +
        ENNReal.ofReal (3 ^ Module.finrank ℝ V * 2 ^ a * A * R ^ a) * (2 : ℝ≥0∞)^(m+1) :=
      add_le_add hmass le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      rw [show a+m+1 = a+(m+1) by omega, pow_add]
      ring



omit [FiniteDimensional ℝ E] in
lemma measurable_mixedInverse (s : E) (V : Submodule ℝ E) (m r : ℕ) :
    Measurable (mixedInverse s V m r) := by
  have hf : Measurable (fun u : E => Metric.infDist (u-s) (V : Set E)) :=
    (Metric.continuous_infDist_pt _).measurable.comp (by fun_prop)
  exact Measurable.ennreal_ofReal ((by fun_prop : Measurable (fun u : E => ‖u-s‖⁻¹ ^ r)).mul
    (hf.inv.pow_const m))

lemma inverse_div_factor (x R : ℝ) (m : ℕ) (hR : R ≠ 0) :
    x⁻¹ ^ m = R⁻¹ ^ m * (x / R)⁻¹ ^ m := by
  rw [← mul_pow, inv_div, div_eq_mul_inv]
  simp [hR]

lemma radial_power_cancel (R : ℝ) (a k : ℕ) (hR : R ≠ 0) (hk : k ≤ a) :
    R⁻¹ ^ k * R ^ a = R ^ (a-k) := by
  have he : R ^ a = R ^ k * R ^ (a-k) := by rw [← pow_add, Nat.add_sub_of_le hk]
  rw [he, ← mul_assoc, ← mul_pow]
  simp [hR]


theorem AmbientGrowth.shell_mixed_inverse {μ : Measure E} {a m r : ℕ} {A : ℝ}
    (hμ : AmbientGrowth μ a A) (hA : 0 ≤ A) (V : Submodule ℝ E) (s : E)
    (hmargin : Module.finrank ℝ V + (m+1) ≤ a) (hdegree : m+r ≤ a)
    {R : ℝ} (hR : 0 < R) :
    ∫⁻ u in radialShell s R, mixedInverse s V m r u ∂μ ≤
      ENNReal.ofReal (shellConstant (Module.finrank ℝ V) a m r * A * R ^ (a-(m+r))) := by
  let f : E → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (((Metric.infDist (u-s) (V : Set E) / R)⁻¹) ^ m)
  have hf : Measurable f := by
    have hh := (Metric.continuous_infDist_pt (V : Set E)).measurable.comp
      (show Measurable (fun u : E => u-s) by fun_prop)
    exact ((hh.div_const R).inv.pow_const m).ennreal_ofReal
  have hbound : ∀ u ∈ radialShell s R,
      mixedInverse s V m r u ≤ ENNReal.ofReal (2 ^ r * R⁻¹ ^ (m+r)) * f u := by
    intro u hu
    have hu0 : 0 < ‖u-s‖ := lt_trans (by positivity : 0 < R/2) hu.1
    have hinv : ‖u-s‖⁻¹ ≤ 2 / R := by
      have h := (inv_le_inv₀ hu0 (by positivity : (0 : ℝ) < R/2)).mpr hu.1.le
      simpa only [inv_div] using h
    have hpow : ‖u-s‖⁻¹ ^ r ≤ (2 / R) ^ r :=
      pow_le_pow_left₀ (by positivity) hinv r
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      ‖u-s‖⁻¹ ^ r * (Metric.infDist (u-s) (V : Set E))⁻¹ ^ m ≤
          (2/R)^r * (Metric.infDist (u-s) (V : Set E))⁻¹ ^ m :=
        mul_le_mul_of_nonneg_right hpow (pow_nonneg (inv_nonneg.mpr Metric.infDist_nonneg) _)
      _ = _ := by
        rw [inverse_div_factor (Metric.infDist (u-s) (V : Set E)) R m hR.ne']
        simp only [div_eq_mul_inv, inv_pow, pow_add]
        ring
  calc
    _ ≤ ∫⁻ u in radialShell s R, ENNReal.ofReal (2 ^ r * R⁻¹ ^ (m+r)) * f u ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_radialShell s R)] with u hu
      exact hbound u hu
    _ = ENNReal.ofReal (2 ^ r * R⁻¹ ^ (m+r)) * ∫⁻ u in radialShell s R, f u ∂μ :=
      lintegral_const_mul _ hf
    _ ≤ ENNReal.ofReal (2 ^ r * R⁻¹ ^ (m+r)) *
        ENNReal.ofReal ((1 + 3 ^ Module.finrank ℝ V * 2 ^ (a+m+1)) * A * R ^ a) := by
      gcongr
      exact hμ.shell_normalized_inverse hA V s hmargin hR
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      calc
        _ = (2^r * (1 + 3 ^ Module.finrank ℝ V * 2 ^ (a+m+1)) * A) *
            (R⁻¹ ^ (m+r) * R ^ a) := by ring
        _ = _ := by rw [radial_power_cancel R a (m+r) hR.ne' hdegree]; rfl

end MixedRadial


lemma dyadic_min_sum_le (B D : ℝ) (hB : 0 < B) (hD : 0 < D) :
    (∑' i : ℕ, ENNReal.ofReal (min B (D * (1/2 : ℝ)^i))) ≤
      ENNReal.ofReal (3 * B * (1 + max (Real.log (D/B)) 0)) := by
  let L : ℝ := max (Real.log (D/B)) 0
  let N : ℕ := ⌈L / Real.log 2⌉₊
  have hL : 0 ≤ L := le_max_right _ _
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlog0 : 0 < Real.log 2 := by linarith
  have hN : L ≤ (N:ℝ) * Real.log 2 := by
    exact (div_le_iff₀ hlog0).mp (Nat.le_ceil _)
  have hDB : D / B ≤ (2:ℝ)^N := by
    apply (Real.log_le_log_iff (div_pos hD hB) (by positivity)).mp
    rw [Real.log_pow]
    exact (le_max_left _ _).trans hN
  have hcut : D * (1/2:ℝ)^N ≤ B := by
    have hh : D ≤ (2:ℝ)^N * B := (div_le_iff₀ hB).mp hDB
    calc
      D * (1/2:ℝ)^N ≤ ((2:ℝ)^N * B) * (1/2:ℝ)^N :=
        mul_le_mul_of_nonneg_right hh (by positivity)
      _ = B := by rw [mul_comm ((2:ℝ)^N), mul_assoc, ← mul_pow]; norm_num
  have hNupper : (N:ℝ) ≤ 2 * L + 1 := by
    have hh := (Nat.ceil_lt_add_one (div_nonneg hL hlog0.le)).le
    have hdiv : L / Real.log 2 ≤ 2 * L := by
      apply (div_le_iff₀ hlog0).mpr
      nlinarith
    dsimp [N]
    linarith
  let f : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (min B (D * (1/2:ℝ)^i))
  calc
    ∑' i, f i = (∑ i ∈ Finset.range N, f i) + ∑' i, f (i+N) := by
      exact ENNReal.summable.sum_add_tsum_nat_add'.symm
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal B +
        ∑' i : ℕ, ENNReal.ofReal B * (1/2:ℝ≥0∞)^i := by
      apply add_le_add
      · calc
          ∑ i ∈ Finset.range N, f i ≤ ∑ _i ∈ Finset.range N, ENNReal.ofReal B := by
            exact Finset.sum_le_sum fun i _ => ENNReal.ofReal_le_ofReal (min_le_left _ _)
          _ = _ := by simp
      · apply ENNReal.tsum_le_tsum
        intro i
        dsimp [f]
        rw [← (show ENNReal.ofReal (1/2:ℝ) = (1/2:ℝ≥0∞) by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num)]
        rw [← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),
          ← ENNReal.ofReal_mul hB.le]
        apply ENNReal.ofReal_le_ofReal
        refine (min_le_right _ _).trans ?_
        calc
          D * (1/2:ℝ)^(i+N) = (D * (1/2:ℝ)^N) * (1/2:ℝ)^i := by rw [pow_add]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcut (by positivity)
    _ = ENNReal.ofReal ((N:ℝ)*B + 2*B) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      norm_num
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_ofNat (n:=2), ← ENNReal.ofReal_mul hB.le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
    _ ≤ ENNReal.ofReal (3 * B * (1+L)) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith

lemma shellConstant_nonneg (h a m r : ℕ) : 0 ≤ shellConstant h a m r := by
  unfold shellConstant
  positivity

lemma shellConstant_mono (h m r : ℕ) {a b : ℕ} (hab : a ≤ b) :
    shellConstant h a m r ≤ shellConstant h b m r := by
  unfold shellConstant
  gcongr
  norm_num

section MixedRadialSum
variable {E : Type*} [NormedAddCommGroup E] [innerProductSpaceRealE : InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mem_radialShell_dyadic {s u : E} (hu : 0 < ‖u-s‖) (hu2 : ‖u-s‖ ≤ 2) :
    ∃ i : ℕ, u ∈ radialShell s (2 * (1/2:ℝ)^i) := by
  obtain ⟨i, hi, hj⟩ := exists_nat_pow_near_of_lt_one (show 0 < ‖u-s‖/2 by positivity)
    (show ‖u-s‖/2 ≤ 1 by linarith) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  refine ⟨i, ?_, ?_⟩
  · rw [pow_succ] at hi
    linarith
  · linarith



theorem AmbientGrowth.mixed_inverse_le {μ : Measure E} {n m r : ℕ} {B D : ℝ}
    (hBμ : AmbientGrowth μ (m+r) B) (hDμ : AmbientGrowth μ n D)
    (hB : 0 < B) (hD : 0 < D) (hr : 1 ≤ r) (hn : m+r < n)
    (V : Submodule ℝ E) (s : E) (hmargin : Module.finrank ℝ V + (m+1) ≤ m+r)
    (hsupp : ∀ᵐ u ∂μ, ‖u-s‖ ≤ 2) :
    ∫⁻ u, mixedInverse s V m r u ∂μ ≤
      ENNReal.ofReal (4 * shellConstant (Module.finrank ℝ V) n m r *
        B * (1 + max (Real.log (D/B)) 0)) := by
  let K : ℝ := shellConstant (Module.finrank ℝ V) n m r
  have hK : 0 ≤ K := shellConstant_nonneg _ _ _ _
  let S : ℕ → Set E := fun i => radialShell s (2 * (1/2:ℝ)^i)
  have hS : MeasurableSet (⋃ i, S i) := MeasurableSet.iUnion fun i => measurableSet_radialShell _ _
  have heq : (fun u => mixedInverse s V m r u) =ᵐ[μ]
      (⋃ i, S i).indicator (mixedInverse s V m r) := by
    filter_upwards [hsupp] with u hu
    by_cases hz : u = s
    · subst u
      simp [mixedInverse, Set.indicator, Nat.ne_of_gt (show 0 < r by omega)]
    · have hpos : 0 < ‖u-s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
      obtain ⟨i, hi⟩ := mem_radialShell_dyadic hpos hu
      exact (Set.indicator_of_mem (mem_iUnion.mpr ⟨i, hi⟩) _).symm
  have hzero : ∫⁻ u in S 0, mixedInverse s V m r u ∂μ ≤ ENNReal.ofReal (K*B) := by
    have hh := hBμ.shell_mixed_inverse hB.le V s hmargin le_rfl (by norm_num : (0:ℝ) < 2)
    have hk := shellConstant_mono (Module.finrank ℝ V) m r hn.le
    dsimp [S]
    simp only [pow_zero, mul_one, Nat.sub_self] at hh ⊢
    refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
    simpa [K] using mul_le_mul_of_nonneg_right hk hB.le
  have htail (i : ℕ) :
      ∫⁻ u in S (i+1), mixedInverse s V m r u ∂μ ≤
        ENNReal.ofReal K * ENNReal.ofReal (min B (D*(1/2:ℝ)^i)) := by
    have hR : 0 < (1/2:ℝ)^i := by positivity
    have hR1 : (1/2:ℝ)^i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hSi : S (i+1) = radialShell s ((1/2:ℝ)^i) := by
      dsimp [S]
      congr 1
      rw [pow_succ]
      ring
    rw [hSi, ← ENNReal.ofReal_mul hK]
    rw [mul_min_of_nonneg _ _ hK, ENNReal.ofReal_min]
    apply le_min
    · have hh := hBμ.shell_mixed_inverse hB.le V s hmargin le_rfl hR
      simp only [Nat.sub_self, pow_zero, mul_one] at hh
      refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (shellConstant_mono _ _ _ hn.le) hB.le
    · have hh := hDμ.shell_mixed_inverse hD.le V s (hmargin.trans hn.le) hn.le hR
      refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
      have hrpow : ((1/2:ℝ)^i)^(n-(m+r)) ≤ (1/2:ℝ)^i := by
        simpa using pow_le_pow_of_le_one hR.le hR1 (show 1 ≤ n-(m+r) by omega)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrpow (mul_nonneg hK hD.le)
  calc
    _ = ∫⁻ u in ⋃ i, S i, mixedInverse s V m r u ∂μ := by
      rw [← lintegral_indicator hS]
      exact lintegral_congr_ae heq
    _ ≤ ∑' i, ∫⁻ u in S i, mixedInverse s V m r u ∂μ := lintegral_iUnion_le _ _
    _ = (∫⁻ u in S 0, mixedInverse s V m r u ∂μ) +
        ∑' i, ∫⁻ u in S (i+1), mixedInverse s V m r u ∂μ := tsum_eq_zero_add' ENNReal.summable
    _ ≤ ENNReal.ofReal (K*B) + ENNReal.ofReal K *
        (∑' i : ℕ, ENNReal.ofReal (min B (D*(1/2:ℝ)^i))) := by
      rw [← ENNReal.tsum_mul_left]
      exact add_le_add hzero (ENNReal.tsum_le_tsum htail)
    _ ≤ ENNReal.ofReal (K*B) + ENNReal.ofReal K *
        ENNReal.ofReal (3 * B * (1+max (Real.log (D/B)) 0)) := by
      gcongr
      exact dyadic_min_sum_le B D hB hD
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul hK,
        ← ENNReal.ofReal_add (mul_nonneg hK hB.le) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hL : 0 ≤ max (Real.log (D/B)) 0 := le_max_right _ _
      have hh : 0 ≤ K * B * max (Real.log (D/B)) 0 := by positivity
      dsimp [K] at *
      nlinarith

end MixedRadialSum

lemma two_pow_le_exp (k : ℕ) : (2:ℝ)^k ≤ Real.exp (k:ℝ) := by
  calc
    (2:ℝ)^k ≤ (Real.exp 1)^k :=
      pow_le_pow_left₀ (by norm_num) (by have h := Real.add_one_le_exp (1:ℝ); linarith) k
    _ = _ := by rw [← Real.exp_nat_mul]; simp

lemma shellConstant_exp_bound (d h n m r : ℕ) (hd : 1 ≤ d)
    (hh : h ≤ d) (hn : n ≤ d) (hm : m ≤ d) (hr : r ≤ d) :
    4 * shellConstant h n m r ≤ Real.exp (9 * (d:ℝ)) := by
  have hA : 1 ≤ (3:ℝ)^h * 2^(n+m+1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hpow : (3:ℝ)^h ≤ 4^h := pow_le_pow_left₀ (by norm_num) (by norm_num) h
  calc
    4 * shellConstant h n m r ≤ 8 * (2:ℝ)^r * ((3:ℝ)^h * 2^(n+m+1)) := by
      unfold shellConstant
      have hp : 0 ≤ (2:ℝ)^r := by positivity
      nlinarith
    _ ≤ 8 * (2:ℝ)^r * ((4:ℝ)^h * 2^(n+m+1)) := by gcongr
    _ = (2:ℝ)^(r+2*h+n+m+4) := by
      norm_num [pow_add, pow_mul]
      ring
    _ ≤ (2:ℝ)^(9*d) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ ≤ Real.exp (9 * (d:ℝ)) := by simpa using two_pow_le_exp (9*d)


lemma LocalGrowth.sphereLift {d a : ℕ} {ρ : Measure (Sphere d)} {A : ℝ}
    (hρ : LocalGrowth ρ a A) : AmbientGrowth (sphereLift ρ) a A := by
  intro z t ht
  rw [CurrentProjection.sphereLift, Measure.map_apply continuous_subtype_val.measurable Metric.isClosed_closedBall.measurableSet]
  exact hρ z t ht

lemma sphereLift_ae_norm_sub_le {d : ℕ} (ρ : Measure (Sphere d)) (s : Sphere d) :
    ∀ᵐ u ∂sphereLift ρ, ‖u-(s:Vector d)‖ ≤ 2 := by
  apply (MeasurableEmbedding.ae_map_iff
    (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet)).mpr
  apply Filter.Eventually.of_forall
  intro u
  have hu : ‖(u:Vector d)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have hs : ‖(s:Vector d)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using s.property
  exact (norm_sub_le _ _).trans (by rw [hu, hs]; norm_num)




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection

open InnerProductSpace

section GramFactorization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]
lemma gram_linear_combination (w : ι → E) (T : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, (T i j) • w i) =
      T.transpose * Matrix.gram ℝ w * T := by
  ext a b
  simp only [Matrix.gram_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  congr 1
  ext j
  congr 1
  ext i
  ring

variable (n : ℕ)

lemma gsUpper_expansion (v : Fin n → E) (j : Fin n) :
    ∑ i, (gsUpper n v i j) • gramSchmidt ℝ v i = v j := by
  simp only [gsUpper, add_smul, Finset.sum_add_distrib]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_rhs => rw [gramSchmidt_def'' ℝ v j]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

lemma gsUpper_det (v : Fin n → E) : (gsUpper n v).det = 1 := by
  have htri : (gsUpper n v).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp [gsUpper, (ne_of_gt hij), (not_lt_of_ge hij.le)]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [gsUpper]

lemma gram_gramSchmidt_diagonal (v : Fin n → E) :
    Matrix.gram ℝ (gramSchmidt ℝ v) = Matrix.diagonal (fun i => ‖gramSchmidt ℝ v i‖ ^ 2) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.gram_apply]
  · simp [Matrix.gram_apply, hij,
      gramSchmidt_orthogonal ℝ v hij]



theorem det_gram_eq_prod_gramSchmidt (v : Fin n → E) :
    (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ ^ 2 := by
  have hv : (fun j => ∑ i, (gsUpper n v i j) • gramSchmidt ℝ v i) = v :=
    funext (gsUpper_expansion n v)
  have h := gram_linear_combination (gramSchmidt ℝ v) (gsUpper n v)
  rw [hv] at h
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, gsUpper_det,
    one_mul, mul_one, gram_gramSchmidt_diagonal, Matrix.det_diagonal]
end GramFactorization

section GramDistances
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}
omit [FiniteDimensional ℝ E] in
lemma sub_gramSchmidt_mem_span (v : Fin n → E) (j : Fin n) :
    v j - gramSchmidt ℝ v j ∈ Submodule.span ℝ (v '' Set.Iio j) := by
  rw [← span_gramSchmidt_Iio ℝ v j]
  conv => arg 2; lhs; rw [gramSchmidt_def'' ℝ v j]
  rw [add_sub_cancel_left]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)

omit [FiniteDimensional ℝ E] in
lemma gramSchmidt_mem_span_orthogonal (v : Fin n → E) (j : Fin n) :
    gramSchmidt ℝ v j ∈ (Submodule.span ℝ (v '' Set.Iio j))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, hi, rfl⟩
    exact gramSchmidt_inv_triangular ℝ v hi
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
  | smul c x _ hx => simp [inner_smul_right, hx]

lemma gramSchmidt_eq_sub_starProjection (v : Fin n → E) (j : Fin n) :
    gramSchmidt ℝ v j = v j -
      (Submodule.span ℝ (v '' Set.Iio j)).starProjection (v j) := by
  have h := (Submodule.span ℝ (v '' Set.Iio j)).eq_starProjection_of_mem_orthogonal
    (u := v j) (sub_gramSchmidt_mem_span v j)
    (by simpa using gramSchmidt_mem_span_orthogonal v j)
  rw [h, sub_sub_cancel]

lemma norm_gramSchmidt_eq_infDist (v : Fin n → E) (j : Fin n) :
    ‖gramSchmidt ℝ v j‖ = Metric.infDist (v j)
      (Submodule.span ℝ (v '' Set.Iio j) : Set E) := by
  rw [gramSchmidt_eq_sub_starProjection, Submodule.starProjection_minimal,
    Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma image_Iio_castSucc (v : Fin (n+1) → E) (j : Fin n) :
    v '' Set.Iio j.castSucc = (fun i => v i.castSucc) '' Set.Iio j := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hin : i.val < n := lt_trans hi j.isLt
    exact ⟨⟨i.val, hin⟩, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.castSucc, hi, rfl⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma image_Iio_last (v : Fin (n+1) → E) :
    v '' Set.Iio (Fin.last n) = Set.range (fun i : Fin n => v i.castSucc) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.castSucc, i.isLt, rfl⟩

lemma gramSchmidt_castSucc (v : Fin (n+1) → E) (j : Fin n) :
    gramSchmidt ℝ v j.castSucc = gramSchmidt ℝ (fun i => v i.castSucc) j := by
  rw [gramSchmidt_eq_sub_starProjection, gramSchmidt_eq_sub_starProjection,
    image_Iio_castSucc]

variable [MeasurableSpace E] [BorelSpace E]
lemma measurable_gramSchmidt (j : Fin n) :
    Measurable (fun v : Fin n → E => gramSchmidt ℝ v j) := by
  refine (wellFounded_lt : WellFounded ((· < ·) : Fin n → Fin n → Prop)).induction
    (C := fun j : Fin n => Measurable (fun v : Fin n → E => gramSchmidt ℝ v j)) j ?_
  intro j ih
  have heq : (fun v : Fin n → E => gramSchmidt ℝ v j) =
      fun v => v j - ∑ i ∈ Finset.Iio j,
        (⟪gramSchmidt ℝ v i, v j⟫ / ‖gramSchmidt ℝ v i‖ ^ 2) • gramSchmidt ℝ v i := by
    ext v
    rw [gramSchmidt_def]
    simp only [Submodule.starProjection_singleton]
    rfl
  rw [heq]
  apply (measurable_pi_apply j).sub
  apply Finset.measurable_sum
  intro i hi
  have hi' := ih i (Finset.mem_Iio.mp hi)
  exact ((hi'.inner (measurable_pi_apply j)).div (hi'.norm.pow_const 2)).smul hi'
end GramDistances

section PiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
lemma lintegral_pi_snoc (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v ∂Measure.pi (fun _ => ν) =
      ∫⁻ v : Fin n → E, ∫⁻ x, f (Fin.snoc v x) ∂ν ∂Measure.pi (fun _ => ν) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f,
    lintegral_prod_symm]
  · congr 1
    ext v
    congr 1
    ext x
    congr 1
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact Fin.insertNth_last' x v
  · exact (hf.comp (MeasurableEquiv.measurable _)).aemeasurable
end PiLast

section AePiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
lemma ae_pi_snoc {P : (Fin (n+1) → E) → Prop} (hP : MeasurableSet {v | P v}) :
    (∀ᵐ v ∂Measure.pi (fun _ => ν), P v) ↔
      ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν), ∀ᵐ x ∂ν, P (Fin.snoc v x) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm
  rw [← hp.map_eq, MeasurableEmbedding.ae_map_iff (MeasurableEquiv.measurableEmbedding _)]
  have heq : (fun z : E × (Fin n → E) =>
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) (Fin.last n)).symm z) =
      fun z => Fin.snoc z.2 z.1 := by
    ext z : 1
    change (Fin.last n).insertNth (α := fun _ => E) z.1 z.2 = _
    exact Fin.insertNth_last' z.1 z.2
  have hm : Measurable (fun z : E × (Fin n → E) => Fin.snoc (α := fun _ => E) z.2 z.1) := by
    rw [← heq]
    exact hp.measurable
  change (∀ᵐ z ∂ν.prod (Measure.pi (fun _ : Fin n => ν)),
      P ((fun z => (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E)
        (Fin.last n)).symm z) z)) ↔ _
  have hPP : MeasurableSet {z : E × (Fin n → E) | P (Fin.snoc z.2 z.1)} := hP.preimage hm
  rw [heq, Measure.ae_prod_iff_ae_ae hPP]
  exact Measure.ae_ae_comm hPP
end AePiLast

section ReplicaNondegenerate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurableSet_gramSchmidt_ne_zero (p : E) (n : ℕ) :
    MeasurableSet {v : Fin n → E | ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0} := by
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have h := (measurable_gramSchmidt i).comp
    (show Measurable (fun v : Fin n → E => fun j => v j - p) by fun_prop)
  exact (measurableSet_eq_fun h measurable_const).compl

end ReplicaNondegenerate

section GaussianDomination
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


lemma orthonormal_gaussian_map {n : ℕ} {u : Fin n → E} (hu : Orthonormal ℝ u) :
    (stdGaussian E).map (fun x => fun i => ⟪u i, x⟫) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  let f : E → EuclideanSpace ℝ (Fin n) := fun x => WithLp.toLp 2 (fun i => ⟪u i, x⟫)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he : (stdGaussian E).map f = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    apply Measure.ext_of_charFun
    ext t
    have hi (x : E) : ⟪f x, t⟫ = ⟪x, ∑ i, t i • u i⟫ := by
      simp [f, PiLp.inner_apply, inner_sum, inner_smul_right, real_inner_comm x]
    have hn : ‖∑ i, t i • u i‖ ^ 2 = ‖t‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hu.inner_sum, EuclideanSpace.real_norm_sq_eq]
      simp [pow_two]
    rw [charFun_apply, integral_map hf.aemeasurable (by fun_prop)]
    simp_rw [hi]
    change charFun (stdGaussian E) (∑ i, t i • u i) = _
    rw [charFun_stdGaussian, charFun_stdGaussian]
    congr 2
    exact_mod_cast congrArg Neg.neg hn
  have h := congrArg (Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))) he
  rw [← map_pi_eq_stdGaussian] at h
  simpa [Measure.map_map (WithLp.measurable_ofLp _ _) hf,
    Measure.map_map (WithLp.measurable_ofLp _ _) (WithLp.measurable_toLp _ _),
    Function.comp_def, f, WithLp.ofLp_toLp, Measure.map_id] using h

lemma gaussianReal_le_volume : gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
  conv_rhs => rw [← withDensity_one (μ := (volume : Measure ℝ))]
  apply withDensity_mono
  filter_upwards [] with x
  change ENNReal.ofReal (gaussianPDFReal 0 1 x) ≤ 1
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianPDFReal
  have hs : 1 ≤ Real.sqrt (2 * Real.pi * (1 : ℝ≥0)) := by
    norm_num only [NNReal.coe_one, mul_one]
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have he : Real.exp (-(x - 0)^2 / (2 * (1 : ℝ≥0))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  exact (mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hs)).trans he
lemma measure_pi_mono {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] {μ ν : ∀ i, Measure (X i)}
    (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  have ho : OuterMeasure.pi (fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    apply OuterMeasure.le_pi.mpr
    intro s _
    exact (OuterMeasure.pi_pi_le _ s).trans (Finset.prod_le_prod' fun i _ => h i (s i))
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.pi_def, Measure.pi_def, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  exact ho s

lemma pi_gaussianReal_le_volume (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) ≤ (volume : Measure (Fin n → ℝ)) :=
  measure_pi_mono (fun _ => gaussianReal_le_volume)
lemma gaussian_pairings_le {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹) •
        (volume : Measure (Fin n → ℝ)) := by
  let u := gramSchmidtNormed ℝ v
  let R : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => ‖gramSchmidt ℝ v i‖) * gsUpper n v
  have hu : Orthonormal ℝ u := gramSchmidtNormed_orthonormal hv
  have hn (i : Fin n) : ‖gramSchmidt ℝ v i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hv)
  have hexp (j : Fin n) : ∑ i, R i j • u i = v j := by
    rw [← gsUpper_expansion n v j]
    apply Finset.sum_congr rfl
    intro i _
    simp only [R, u, Matrix.diagonal_mul, gramSchmidtNormed, smul_smul]
    congr 1
    simp [hn i, mul_comm]
  have hdet : R.transpose.det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
    dsimp only [R]
    rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal, gsUpper_det, mul_one]
  have hd : R.transpose.det ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)
  have hpos : 0 ≤ R.transpose.det := by rw [hdet]; positivity
  have hf : Measurable (Matrix.toLin' R.transpose) :=
    (Matrix.toLin' R.transpose).continuous_of_finiteDimensional.measurable
  have heq : (fun x : E => fun j => ⟪v j, x⟫) =
      (Matrix.toLin' R.transpose) ∘ (fun x => fun i => ⟪u i, x⟫) := by
    funext x j
    rw [← hexp j]
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, sum_inner,
      inner_smul_left]
  rw [heq, ← Measure.map_map hf (by fun_prop), orthonormal_gaussian_map hu]
  calc
    _ ≤ (volume : Measure (Fin n → ℝ)).map (Matrix.toLin' R.transpose) :=
      Measure.map_mono (pi_gaussianReal_le_volume n) hf
    _ = _ := by
      rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hd,
        abs_of_nonneg (inv_nonneg.mpr hpos), hdet]
lemma measure_pi_smul {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (c : ℝ≥0∞) (hc : c ≠ ∞) :
    Measure.pi (fun i => c • μ i) = c ^ Fintype.card ι • Measure.pi μ := by
  lift c to ℝ≥0 using hc
  simp_rw [Measure.coe_nnreal_smul]
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]


lemma gaussian_rows_pairings_le {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v)
    (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map
      (fun A => fun j i => ⟪v i, A j⟫) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) •
        (volume : Measure (Fin m → Fin n → ℝ)) := by
  rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable
    (fun x : E => fun i => ⟪v i, x⟫)).aemeasurable)]
  have h := measure_pi_mono (fun _ : Fin m => gaussian_pairings_le v hv)
  rw [measure_pi_smul _ _ ENNReal.ofReal_ne_top] at h
  rw [ENNReal.ofReal_pow (by positivity)]
  simpa only [Fintype.card_fin, volume_pi] using h
end GaussianDomination

section ReplicaKernel
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

lemma lintegral_fin_prod (n : ℕ) (f : Fin n → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → X, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ) =
      ∏ i, ∫⁻ x, f i x ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [lintegral_pi_snoc μ _ (by fun_prop)]
    simp_rw [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    simp_rw [lintegral_const_mul _ (hf (Fin.last n))]
    rw [lintegral_mul_const _ (by fun_prop), ih _ (fun i => hf i.castSucc)]

lemma lintegral_pow_pi (f : X → ℝ≥0∞) (hf : Measurable f) (n : ℕ) :
    (∫⁻ x, f x ∂μ)^n =
      ∫⁻ x : Fin n → X, ∏ i, f (x i) ∂Measure.pi (fun _ => μ) := by
  rw [lintegral_fin_prod μ n _ (fun _ => hf)]
  simp

end ReplicaKernel




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.MixedReplica
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace

section MixedNondegenerate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


theorem AmbientGrowth.affine_span_null {μ : Measure E} {a : ℕ} {A : ℝ}
    (hμ : AmbientGrowth μ a A) (hA : 0 ≤ A) (V : Submodule ℝ E) (s : E)
    (hmargin : Module.finrank ℝ V + 1 ≤ a) (hsupp : ∀ᵐ u ∂μ, ‖u-s‖ ≤ 2) :
    μ {u | u-s ∈ V} = 0 := by
  let C : ℝ := 3 ^ Module.finrank ℝ V * 2 ^ a * A * 2 ^ a
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (j : ℕ) : μ {u | u-s ∈ V} ≤ ENNReal.ofReal (C * (1/2:ℝ)^j) := by
    have hj : 0 < (1/2:ℝ)^j := by positivity
    have hj1 : (1/2:ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc
      μ {u | u-s ∈ V} ≤ μ {u | ‖u-s‖ ≤ 2 ∧ Metric.infDist (u-s) (V:Set E) ≤ (1/2:ℝ)^j * 2} := by
        apply measure_mono_ae
        filter_upwards [hsupp] with u hu
        intro hv
        exact ⟨hu, by rw [Metric.infDist_zero_of_mem hv]; positivity⟩
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (((1/2:ℝ)^j)^1) :=
        hμ.radial_tube_pow hA V s 1 hmargin (by norm_num) hj hj1
      _ = _ := by rw [pow_one, ENNReal.ofReal_mul hC]
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (C * (1/2:ℝ)^j)) atTop (𝓝 0) := by
    convert ENNReal.tendsto_ofReal ((tendsto_const_nhds (x:=C)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1))) using 1
    simp
  exact le_antisymm (ge_of_tendsto' hlim hb) bot_le



theorem AmbientGrowth.ae_gramSchmidt_ne_zero {μ : Measure E} [SigmaFinite μ] {a : ℕ} {A : ℝ}
    (hμ : AmbientGrowth μ a A) (hA : 0 ≤ A) (s : E)
    (hsupp : ∀ᵐ u ∂μ, ‖u-s‖ ≤ 2) (k : ℕ) (hk : k ≤ a) :
    ∀ᵐ v : Fin k → E ∂Measure.pi (fun _ => μ),
      ∀ i, gramSchmidt ℝ (fun j => v j - s) i ≠ 0 := by
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ k ih =>
    rw [ae_pi_snoc μ (measurableSet_gramSchmidt_ne_zero s (k+1))]
    filter_upwards [ih (by omega)] with v hv
    let V := Submodule.span ℝ (Set.range (fun i : Fin k => v i - s))
    have hdim : Module.finrank ℝ V ≤ k := by
      simpa [V, Set.finrank] using finrank_range_le_card (R:=ℝ) (fun i : Fin k => v i-s)
    have hnull : μ {u | u-s ∈ V} = 0 := hμ.affine_span_null hA V s (by omega) hsupp
    have ha : ∀ᵐ u ∂μ, u-s ∉ V := by
      rw [ae_iff]
      simpa only [not_not] using hnull
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [norm_gramSchmidt_eq_infDist, image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact ne_of_gt ((V.closed_of_finiteDimensional.notMem_iff_infDist_pos
        ⟨0, V.zero_mem⟩).mp hx)
    | cast j => simpa only [gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

theorem AmbientGrowth.ae_replica_linearIndependent {μ : Measure E} [SigmaFinite μ]
    {a : ℕ} {A : ℝ} (hμ : AmbientGrowth μ a A) (hA : 0 ≤ A) (s : E)
    (hsupp : ∀ᵐ u ∂μ, ‖u-s‖ ≤ 2) (k : ℕ) (hk : k ≤ a) :
    ∀ᵐ v : Fin k → E ∂Measure.pi (fun _ => μ),
      LinearIndependent ℝ (fun j => v j-s) := by
  filter_upwards [hμ.ae_gramSchmidt_ne_zero hA s hsupp k hk] with v hv
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [det_gram_eq_prod_gramSchmidt]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hv i))

end MixedNondegenerate

section MixedReplica
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]


lemma measurable_mixedReplicaWeight (m r : ℕ) (s : E) (k : ℕ) :
    Measurable (mixedReplicaWeight m r s (k:=k)) := by
  have hs : Measurable (fun v : Fin k → E => fun j => v j-s) := by fun_prop
  exact Finset.measurable_prod _ fun i _ =>
    (((measurable_pi_apply i).sub measurable_const).norm.inv.pow_const r |>.mul
      (((measurable_gramSchmidt i).comp hs).norm.inv.pow_const m)).ennreal_ofReal

omit [MeasurableSpace E] [BorelSpace E] in
lemma mixedReplicaWeight_snoc (m r : ℕ) (s : E) {k : ℕ} (v : Fin k → E) (x : E) :
    mixedReplicaWeight m r s (Fin.snoc v x) = mixedReplicaWeight m r s v *
      mixedInverse s (Submodule.span ℝ (Set.range (fun i => v i-s))) m r x := by
  unfold mixedReplicaWeight
  rw [Fin.prod_univ_castSucc]
  simp only [gramSchmidt_castSucc, Fin.snoc_castSucc]
  rw [norm_gramSchmidt_eq_infDist, image_Iio_last]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  rfl

theorem AmbientGrowth.mixed_inverse_uniform {μ : Measure E} {d n m r : ℕ} {B D : ℝ}
    (hBμ : AmbientGrowth μ (m+r) B) (hDμ : AmbientGrowth μ n D)
    (hB : 0 < B) (hD : 0 < D) (hn : m+r < n) (hnd : n ≤ d)
    (V : Submodule ℝ E) (s : E) (hmargin : Module.finrank ℝ V + (m+1) ≤ m+r)
    (hsupp : ∀ᵐ u ∂μ, ‖u-s‖ ≤ 2) :
    ∫⁻ u, mixedInverse s V m r u ∂μ ≤ momentConstant 9 d B D := by
  refine (hBμ.mixed_inverse_le hDμ hB hD (by omega) hn V s hmargin hsupp).trans
    (ENNReal.ofReal_le_ofReal ?_)
  gcongr
  exact shellConstant_exp_bound d _ n m r (by omega) (by omega) hnd (by omega) (by omega)


theorem AmbientGrowth.mixed_replica_integral {μ : Measure E} [SigmaFinite μ]
    {d n m r : ℕ} {B D : ℝ}
    (hBμ : AmbientGrowth μ (m+r) B) (hDμ : AmbientGrowth μ n D)
    (hB : 0 < B) (hD : 0 < D) (hn : m+r < n) (hnd : n ≤ d)
    (s : E) (hsupp : ∀ᵐ u ∂μ, ‖u-s‖ ≤ 2) (k : ℕ) (hk : k ≤ r) :
    ∫⁻ v : Fin k → E, mixedReplicaWeight m r s v ∂Measure.pi (fun _ => μ) ≤
      (momentConstant 9 d B D)^k := by
  induction k with
  | zero => simp [mixedReplicaWeight]
  | succ k ih =>
    have hinner (v : Fin k → E) :
        ∫⁻ x, mixedReplicaWeight m r s (Fin.snoc v x) ∂μ ≤
          mixedReplicaWeight m r s v * momentConstant 9 d B D := by
      simp_rw [mixedReplicaWeight_snoc]
      rw [lintegral_const_mul _ (measurable_mixedInverse _ _ _ _)]
      gcongr
      apply hBμ.mixed_inverse_uniform hDμ hB hD hn hnd _ s _ hsupp
      have hdim := finrank_range_le_card (R:=ℝ) (fun i : Fin k => v i-s)
      simp only [Fintype.card_fin, Set.finrank] at hdim
      omega
    calc
      _ = ∫⁻ v : Fin k → E, ∫⁻ x, mixedReplicaWeight m r s (Fin.snoc v x) ∂μ
          ∂Measure.pi (fun _ => μ) := lintegral_pi_snoc μ _ (measurable_mixedReplicaWeight m r s (k+1))
      _ ≤ ∫⁻ v : Fin k → E, mixedReplicaWeight m r s v * momentConstant 9 d B D
          ∂Measure.pi (fun _ => μ) := lintegral_mono hinner
      _ = (∫⁻ v : Fin k → E, mixedReplicaWeight m r s v ∂Measure.pi (fun _ => μ)) *
          momentConstant 9 d B D := lintegral_mul_const _ (measurable_mixedReplicaWeight m r s k)
      _ ≤ (momentConstant 9 d B D)^k * momentConstant 9 d B D :=
        mul_le_mul' (ih (by omega)) le_rfl
      _ = _ := (pow_succ _ _).symm

end MixedReplica

section FixedGaussianKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


lemma gaussian_fixed_kernel_bound {k : ℕ} (v : Fin k → E) (hv : LinearIndependent ℝ v)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1) (m : ℕ) :
    ∫⁻ X : Fin m → E, ∏ i, ∏ j, φ ⟪v i, X j⟫
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) := by
  let H : (Fin m → Fin k → ℝ) → ℝ≥0∞ := fun z => ∏ j, ∏ i, φ (z j i)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hH1 : ∫⁻ z, H z = 1 := by
    rw [volume_pi, lintegral_fin_prod (volume : Measure (Fin k → ℝ)) m
      (fun _ z => ∏ i, φ (z i)) (by intro j; fun_prop)]
    conv_lhs => arg 2; ext j; rw [volume_pi, lintegral_fin_prod (volume : Measure ℝ) k
      (fun _ z => φ z) (fun _ => hφ)]
    simp [hφ1]
  have heq (X : Fin m → E) : (∏ i, ∏ j, φ ⟪v i, X j⟫) = H (fun j i => ⟪v i, X j⟫) := by
    exact Finset.prod_comm
  simp_rw [heq]
  rw [← lintegral_map hH (by fun_prop)]
  calc
    _ ≤ ∫⁻ z, H z ∂(ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) •
        (volume : Measure (Fin m → Fin k → ℝ))) :=
      lintegral_mono' (gaussian_rows_pairings_le v hv m) (fun _ => le_rfl)
    _ = _ := by rw [lintegral_smul_measure, hH1]; simp


lemma measurable_rowKernel_right (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ)
    (m : ℕ) (s u : E) : Measurable (rowKernel φ s u (m:=m)) := by
  change Measurable (fun X : Fin m → E => ∏ j, φ ⟪u-s, X j⟫)
  fun_prop

lemma measurable_rowKernel_left (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ)
    (m : ℕ) (s : E) (X : Fin m → E) : Measurable (fun u => rowKernel φ s u X) := by
  change Measurable (fun u : E => ∏ j, φ ⟪u-s, X j⟫)
  fun_prop

lemma gaussian_fresh_kernel_bound (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ z, φ z = 1) (r : ℕ) (s u : E) (hu : u ≠ s) :
    ∫⁻ Z : Fin r → E, rowKernel φ s u Z ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal (‖u-s‖⁻¹ ^ r) := by
  have hv : LinearIndependent ℝ (fun _ : Fin 1 => u-s) :=
    linearIndependent_unique_iff.mpr (sub_ne_zero.mpr hu)
  have hh := gaussian_fixed_kernel_bound (fun _ : Fin 1 => u-s) hv φ hφ hφ1 r
  have he : gramSchmidt ℝ (fun _ : Fin 1 => u-s) 0 = u-s := gramSchmidt_bot ℝ _
  simpa only [Fin.prod_univ_one, he, rowKernel] using hh

end FixedGaussianKernel

section MixedKernelMoment
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowKernel_append (φ : ℝ → ℝ≥0∞) {m r : ℕ} (s u : E)
    (X : Fin m → E) (Z : Fin r → E) :
    rowKernel φ s u (Fin.append X Z) = rowKernel φ s u X * rowKernel φ s u Z := by
  simp only [rowKernel, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mixedReplicaWeight_factor (m r : ℕ) (s : E) {k : ℕ} (v : Fin k → E) :
    mixedReplicaWeight m r s v =
      (∏ i, ENNReal.ofReal (‖v i-s‖⁻¹ ^ r)) *
        ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun j => v j-s) i‖)⁻¹ ^ m) := by
  unfold mixedReplicaWeight
  simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ‖v _-s‖⁻¹ ^ r)]
  rw [Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_pow,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]



theorem AmbientGrowth.mixed_kernel_moment {μ : Measure E} [SigmaFinite μ]
    {d n m r q : ℕ} {B D : ℝ}
    (hBμ : AmbientGrowth μ (m+r) B) (hDμ : AmbientGrowth μ n D)
    (hB : 0 < B) (hD : 0 < D) (hr : 1 ≤ r) (hn : m+r < n) (hnd : n ≤ d)
    (hq : q ≤ r) (s : E) (hsupp : ∀ᵐ u ∂μ, ‖u-s‖ ≤ 2)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1) :
    ∫⁻ X : Fin m → E,
      (∫⁻ Z : Fin r → E, ∫⁻ u, rowKernel φ s u (Fin.append X Z) ∂μ
        ∂Measure.pi (fun _ => stdGaussian E))^q
      ∂Measure.pi (fun _ => stdGaussian E) ≤ (momentConstant 9 d B D)^q := by
  have hnull : μ {u | u=s} = 0 := by
    have hh := hBμ.affine_span_null hB.le (⊥ : Submodule ℝ E) s (by simpa using (by omega : 1 ≤ m+r)) hsupp
    simpa only [Submodule.mem_bot, sub_eq_zero] using hh
  have ha : ∀ᵐ u ∂μ, u ≠ s := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  let F : E → (Fin m → E) → ℝ≥0∞ := fun u X =>
    ENNReal.ofReal (‖u-s‖⁻¹ ^ r) * rowKernel φ s u X
  have hF : Measurable (Function.uncurry F) := by dsimp [F, rowKernel, Function.uncurry]; fun_prop
  have hFX (X : Fin m → E) : Measurable (fun u => F u X) :=
    hF.comp (measurable_id.prodMk measurable_const)
  have hfresh (X : Fin m → E) :
      ∫⁻ Z : Fin r → E, ∫⁻ u, rowKernel φ s u (Fin.append X Z) ∂μ
        ∂Measure.pi (fun _ => stdGaussian E) ≤ ∫⁻ u, F u X ∂μ := by
    simp_rw [rowKernel_append]
    rw [lintegral_lintegral_swap (by simp only [rowKernel]; fun_prop)]
    apply lintegral_mono_ae
    filter_upwards [ha] with u hu
    rw [lintegral_const_mul _ (measurable_rowKernel_right φ hφ r s u)]
    simpa only [F, mul_comm] using mul_le_mul' (le_rfl : rowKernel φ s u X ≤ rowKernel φ s u X)
      (gaussian_fresh_kernel_bound φ hφ hφ1 r s u hu)
  have hpow (X : Fin m → E) : (∫⁻ u, F u X ∂μ)^q =
      ∫⁻ v : Fin q → E, ∏ i, F (v i) X ∂Measure.pi (fun _ => μ) :=
    lintegral_pow_pi μ _ (hFX X) q
  calc
    _ ≤ ∫⁻ X : Fin m → E, (∫⁻ u, F u X ∂μ)^q
        ∂Measure.pi (fun _ => stdGaussian E) := by
      apply lintegral_mono
      intro X
      exact pow_le_pow_left' (hfresh X) q
    _ = ∫⁻ v : Fin q → E, ∫⁻ X : Fin m → E, ∏ i, F (v i) X
        ∂Measure.pi (fun _ => stdGaussian E) ∂Measure.pi (fun _ => μ) := by
      simp_rw [hpow]
      rw [lintegral_lintegral_swap (by dsimp [F, rowKernel]; fun_prop)]
    _ ≤ ∫⁻ v : Fin q → E, mixedReplicaWeight m r s v ∂Measure.pi (fun _ => μ) := by
      apply lintegral_mono_ae
      filter_upwards [hBμ.ae_replica_linearIndependent hB.le s hsupp q (by omega)] with v hv
      simp only [F, Finset.prod_mul_distrib]
      rw [lintegral_const_mul _ (by simp only [rowKernel]; fun_prop), mixedReplicaWeight_factor]
      exact mul_le_mul' le_rfl (gaussian_fixed_kernel_bound (fun i => v i-s) hv φ hφ hφ1 m)
    _ ≤ _ := hBμ.mixed_replica_integral hDμ hB hD hn hnd s hsupp q hq

end MixedKernelMoment

end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace





lemma measurable_cubeKernel (δ : ℝ) : Measurable (cubeKernel δ) :=
  measurable_const.indicator measurableSet_Icc

lemma lintegral_cubeKernel {δ : ℝ} (hδ : 0 < δ) : ∫⁻ z, cubeKernel δ z = 1 := by
  rw [cubeKernel, lintegral_indicator measurableSet_Icc, lintegral_const,
    Measure.restrict_apply_univ, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by positivity)]
  have he : δ - -δ = 2*δ := by ring
  rw [he, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

lemma rowKernel_cube {k d : ℕ} (δ : ℝ) (hδ : 0 ≤ δ) (s u : Vector d) (G : Rows k d) :
    rowKernel (cubeKernel δ) s u G =
      Set.indicator {v : Vector d | ∀ i, |label G v i - label G s i| ≤ δ}
        (fun _ => ENNReal.ofReal ((2*δ)⁻¹ ^ k)) u := by
  classical
  have hi (i : Fin k) : ⟪u-s, G i⟫ = label G u i-label G s i := inner_sub_left _ _ _
  have hab (x : ℝ) : x ∈ Set.Icc (-δ) δ ↔ |x| ≤ δ := abs_le.symm
  by_cases h : ∀ i, |label G u i-label G s i| ≤ δ
  · rw [Set.indicator_of_mem (show u ∈ {v : Vector d | ∀ i, |label G v i-label G s i| ≤ δ} from h)]
    unfold rowKernel
    have he (i : Fin k) : cubeKernel δ ⟪u-s, G i⟫ = ENNReal.ofReal ((2*δ)⁻¹) := by
      exact Set.indicator_of_mem ((hab _).2 (by simpa only [hi] using h i)) _
    simp_rw [he]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow (by positivity)]
  · rw [Set.indicator_of_notMem (show u ∉ {v : Vector d | ∀ i, |label G v i-label G s i| ≤ δ} from h)]
    push Not at h
    obtain ⟨i, hi'⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Set.indicator_of_notMem (by simpa only [hi, hab, not_le] using hi') _

lemma cubeAverage_eq_kernel {k d : ℕ} (ρ : Measure (Sphere d)) (δ : ℝ) (hδ : 0 ≤ δ)
    (s : Sphere d) (G : Rows k d) :
    cubeAverage ρ G (label G (s:Vector d)) δ =
      ∫⁻ u, rowKernel (cubeKernel δ) (s:Vector d) u G ∂sphereLift ρ := by
  have hm : Measurable (fun u : Vector d => rowKernel (cubeKernel δ) (s:Vector d) u G) :=
    measurable_rowKernel_left (cubeKernel δ) (measurable_cubeKernel δ) k (s:Vector d) G
  rw [sphereLift, lintegral_map hm continuous_subtype_val.measurable]
  simp_rw [rowKernel_cube δ hδ]
  have hset : MeasurableSet {u : Sphere d | ∀ i, |label G (u:Vector d) i - label G (s:Vector d) i| ≤ δ} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by unfold label; fun_prop) measurable_const
  change _ = ∫⁻ u : Sphere d, Set.indicator
    {u : Sphere d | ∀ i, |label G (u:Vector d) i-label G (s:Vector d) i| ≤ δ}
      (fun (_ : Sphere d) => ENNReal.ofReal ((2*δ)⁻¹ ^ k)) u ∂ρ
  rw [lintegral_indicator hset, lintegral_const, Measure.restrict_apply_univ]
  rfl



theorem mixed_cube_moment {d m r q : ℕ} (hdim : AdmissibleDimensions d m r q)
    (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (B D : ℝ) (hB : 0 < B) (hD : 0 < D)
    (hBρ : LocalGrowth ρ (m+r) B) (hDρ : LocalGrowth ρ (d-1) D)
    (s : Sphere d) (δ : ℝ) (hδ : 0 < δ) :
    (∫⁻ X, (∫⁻ Z, cubeAverage ρ (Fin.append X Z)
      (label (Fin.append X Z) (s:Vector d)) δ ∂gaussianRows r d)^q
      ∂gaussianRows m d) ≤ (momentConstant 9 d B D)^q := by
  rcases hdim with ⟨hm, hr, hq, hn, hmargin⟩
  simp_rw [cubeAverage_eq_kernel ρ δ hδ.le]
  exact hBρ.sphereLift.mixed_kernel_moment hDρ.sphereLift hB hD hr hn (by omega)
    (by omega) (s:Vector d) (sphereLift_ae_norm_sub_le ρ s)
    (cubeKernel δ) (measurable_cubeKernel δ) (lintegral_cubeKernel hδ)



section AppendPi
variable {E : Type*} [MeasurableSpace E]

lemma measurable_append (m r : ℕ) :
    Measurable (fun z : (Fin m → E) × (Fin r → E) => Fin.append z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [Fin.append_left, Function.comp_def] using (measurable_pi_apply i).comp measurable_fst
  | right i => simpa only [Fin.append_right, Function.comp_def] using (measurable_pi_apply i).comp measurable_snd

lemma map_append_pi (μ : Measure E) [SigmaFinite μ] (m r : ℕ) :
    ((Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi (fun _ : Fin r => μ))).map
      (fun z => Fin.append z.1 z.2) = Measure.pi (fun _ : Fin (m+r) => μ) := by
  symm
  apply Measure.pi_eq
  intro t ht
  rw [Measure.map_apply (measurable_append m r) (MeasurableSet.univ_pi ht)]
  have he : (fun z : (Fin m → E) × (Fin r → E) => Fin.append z.1 z.2) ⁻¹' Set.univ.pi t =
      (Set.univ.pi (fun i => t (Fin.castAdd r i))) ×ˢ
        (Set.univ.pi (fun i => t (Fin.natAdd m i))) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro hz
      exact ⟨fun i => by simpa only [Fin.append_left] using hz (Fin.castAdd r i),
        fun i => by simpa only [Fin.append_right] using hz (Fin.natAdd m i)⟩
    · rintro ⟨h₁,h₂⟩ i
      induction i using Fin.addCases with
      | left i => simpa only [Fin.append_left] using h₁ i
      | right i => simpa only [Fin.append_right] using h₂ i
  rw [he, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fin.prod_univ_add]

lemma ae_pi_append (μ : Measure E) [SigmaFinite μ] (m r : ℕ)
    {P : (Fin (m+r) → E) → Prop} (hP : MeasurableSet {x | P x}) :
    (∀ᵐ G ∂Measure.pi (fun _ => μ), P G) ↔
      ∀ᵐ X ∂Measure.pi (fun _ : Fin m => μ), ∀ᵐ Z ∂Measure.pi (fun _ : Fin r => μ),
        P (Fin.append X Z) := by
  rw [← map_append_pi μ m r, ae_map_iff (measurable_append m r).aemeasurable hP]
  exact Measure.ae_prod_iff_ae_ae (hP.preimage (measurable_append m r))

end AppendPi







lemma measurable_cubeAverage {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] (δ : ℝ) :
    Measurable (fun z : Rows k d × (Fin k → ℝ) => cubeAverage ρ z.1 z.2 δ) := by
  have hset : MeasurableSet {z : (Rows k d × (Fin k → ℝ)) × Sphere d |
      ∀ i, |label z.1.1 (z.2:Vector d) i-z.1.2 i| ≤ δ} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by unfold label; fun_prop) measurable_const
  exact measurable_const.mul (measurable_measure_prodMk_left hset)

lemma measurable_extendedCubeDensity {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] :
    Measurable (fun z : Rows k d × (Fin k → ℝ) => extendedCubeDensity ρ z.1 z.2) :=
  Measurable.liminf (fun j => measurable_cubeAverage ρ (1/(j:ℝ)))

lemma cubeAverage_lt_top {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) (y : Fin k → ℝ) (δ : ℝ) : cubeAverage ρ G y δ < ∞ := by
  unfold cubeAverage
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

lemma exactDensity_eq_of_tendsto {k d : ℕ} (ρ : Measure (Sphere d))
    (G : Rows k d) (y : Fin k → ℝ) {L : ℝ≥0∞}
    (hL : Tendsto (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) atTop (𝓝 L))
    (hLt : L ≠ ∞) : exactDensity ρ G y = L := by
  have ht : Tendsto (fun j : ℕ => (cubeAverage ρ G y (1/(j:ℝ))).toReal)
      atTop (𝓝 L.toReal) := (ENNReal.continuousAt_toReal hLt).tendsto.comp hL
  unfold exactDensity
  dsimp only
  split_ifs with h
  · rw [tendsto_nhds_unique h.choose_spec ht, ENNReal.ofReal_toReal hLt]
  · exact False.elim (h ⟨L.toReal, ht⟩)


lemma measurable_exactDensity {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] :
    Measurable (fun z : Rows k d × (Fin k → ℝ) => exactDensity ρ z.1 z.2) := by
  classical
  let f : ℕ → (Rows k d × (Fin k → ℝ)) → ℝ := fun j z =>
    (cubeAverage ρ z.1 z.2 (1/(j:ℝ))).toReal
  have hf (j : ℕ) : Measurable (f j) := (measurable_cubeAverage ρ _).ennreal_toReal
  let T : Set (Rows k d × (Fin k → ℝ)) := {z | ∃ L : ℝ, Tendsto (fun j => f j z) atTop (𝓝 L)}
  have hT : MeasurableSet T := measurableSet_exists_tendsto hf
  let g : (Rows k d × (Fin k → ℝ)) → ℝ := fun z =>
    if h : z ∈ T then h.choose else 0
  have hg : Measurable g := by
    apply measurable_of_tendsto_metrizable (fun j => (hf j).indicator hT)
    apply tendsto_pi_nhds.mpr
    intro z
    by_cases h : z ∈ T
    · simpa only [Set.indicator_of_mem h, g, dite_eq_left h] using h.choose_spec
    · simpa only [Set.indicator_of_notMem h, g, dite_eq_right h] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  convert hg.ennreal_ofReal using 1
  funext z
  unfold exactDensity
  dsimp [g, T, f]
  split_ifs <;> simp only [ENNReal.ofReal_zero]


lemma cubeAverage_eq_ball_ratio {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d)
    (y : Fin k → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    cubeAverage ρ G y δ = labelLaw ρ G (Metric.closedBall y δ) /
      volume (Metric.closedBall y δ) := by
  rw [labelLaw, Measure.map_apply (by unfold label; fun_prop)
    Metric.isClosed_closedBall.measurableSet, Real.volume_pi_closedBall y hδ.le]
  have hset : {s : Sphere d | ∀ i, |label G (s:Vector d) i-y i| ≤ δ} =
      (fun s : Sphere d => label G (s:Vector d)) ⁻¹' Metric.closedBall y δ := by
    ext s
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm,
      pi_norm_le_iff_of_nonneg hδ.le, Pi.sub_apply, Real.norm_eq_abs, Set.mem_ofPred_eq]
  unfold cubeAverage
  rw [hset, Fintype.card_fin, div_eq_mul_inv, mul_comm]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), inv_pow]

lemma tendsto_cube_scale : Tendsto (fun j : ℕ => 1/(j:ℝ)) atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with j hj
  simp only [Set.mem_Ioi]
  positivity



lemma mixed_liminf_moment_le {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    (μ : Measure A) (ν : Measure T) [SFinite ν]
    (f : ℕ → A × T → ℝ≥0∞) (hf : ∀ j, Measurable (f j)) (q : ℕ) :
    ∫⁻ a, (∫⁻ t, liminf (fun j => f j (a,t)) atTop ∂ν)^q ∂μ ≤
      liminf (fun j => ∫⁻ a, (∫⁻ t, f j (a,t) ∂ν)^q ∂μ) atTop := by
  calc
    _ ≤ ∫⁻ a, liminf (fun j => (∫⁻ t, f j (a,t) ∂ν)^q) atTop ∂μ := by
      apply lintegral_mono
      intro a
      have hfa (j : ℕ) : Measurable (fun t => f j (a,t)) :=
        (hf j).comp (measurable_const.prodMk measurable_id)
      calc
        _ ≤ (liminf (fun j => ∫⁻ t, f j (a,t) ∂ν) atTop)^q :=
          pow_le_pow_left' (lintegral_liminf_le hfa) q
        _ = _ := (show Monotone (fun x : ℝ≥0∞ => x^q) from
            fun _ _ h => pow_le_pow_left' h q).map_liminf_of_continuousAt _
              (ENNReal.continuous_pow q).continuousAt
    _ ≤ _ := lintegral_liminf_le (fun j =>
      (show Measurable (Function.uncurry (fun a t => f j (a,t))) from hf j).lintegral_prod_right.pow_const q)

lemma measurable_fixed_label {k d : ℕ} (s : Sphere d) :
    Measurable (fun G : Rows k d => label G (s:Vector d)) := by
  exact measurable_own_label.comp (measurable_id.prodMk measurable_const)

lemma measurable_own_extended {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] :
    Measurable (fun z : Rows k d × Sphere d => extendedCubeDensity ρ z.1 (label z.1 (z.2:Vector d))) := by
  have h : Measurable (fun z : Rows k d × Sphere d => (z.1, label z.1 (z.2:Vector d))) :=
    measurable_fst.prodMk (measurable_own_label (k:=k) (d:=d))
  have h2 := (measurable_extendedCubeDensity (k:=k) ρ).comp h
  exact h2

lemma measurable_fixed_extended {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] (s : Sphere d) :
    Measurable (fun G : Rows k d => extendedCubeDensity ρ G (label G (s:Vector d))) := by
  have h : Measurable (fun G : Rows k d => (G, label G (s:Vector d))) :=
    measurable_id.prodMk (measurable_fixed_label (k:=k) s)
  have h2 := (measurable_extendedCubeDensity (k:=k) ρ).comp h
  exact h2

lemma extended_mixed_moment {d m r q : ℕ} (hdim : AdmissibleDimensions d m r q)
    (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (B D : ℝ) (hB : 0 < B) (hD : 0 < D)
    (hBρ : LocalGrowth ρ (m+r) B) (hDρ : LocalGrowth ρ (d-1) D) (s : Sphere d) :
    (∫⁻ X, (∫⁻ Z, extendedCubeDensity ρ (Fin.append X Z)
      (label (Fin.append X Z) (s:Vector d)) ∂gaussianRows r d)^q
      ∂gaussianRows m d) ≤ (momentConstant 9 d B D)^q := by
  let f : ℕ → Rows m d × Rows r d → ℝ≥0∞ := fun j z =>
    cubeAverage ρ (Fin.append z.1 z.2) (label (Fin.append z.1 z.2) (s:Vector d)) (1/(j:ℝ))
  have hf (j : ℕ) : Measurable (f j) := by
    have hmap : Measurable (fun z : Rows m d × Rows r d =>
        (Fin.append z.1 z.2, label (Fin.append z.1 z.2) (s:Vector d))) :=
      (measurable_append (E:=Vector d) m r).prodMk
        ((measurable_fixed_label (k:=m+r) s).comp (measurable_append (E:=Vector d) m r))
    have hh := (measurable_cubeAverage (k:=m+r) ρ (1/(j:ℝ))).comp hmap
    exact hh
  apply (mixed_liminf_moment_le (gaussianRows m d) (gaussianRows r d) f hf q).trans
  apply liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
  apply Filter.Eventually.frequently
  filter_upwards [eventually_ge_atTop 1] with j hj
  exact mixed_cube_moment hdim ρ B D hB hD hBρ hDρ s _ (by positivity)

lemma extended_ae_finite {d m r q : ℕ} (hdim : AdmissibleDimensions d m r q)
    (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (B D : ℝ) (hB : 0 < B) (hD : 0 < D)
    (hBρ : LocalGrowth ρ (m+r) B) (hDρ : LocalGrowth ρ (d-1) D) (s : Sphere d) :
    ∀ᵐ G ∂gaussianRows (m+r) d, extendedCubeDensity ρ G (label G (s:Vector d)) < ∞ := by
  let f : Rows m d → Rows r d → ℝ≥0∞ := fun X Z => extendedCubeDensity ρ (Fin.append X Z)
    (label (Fin.append X Z) (s:Vector d))
  have hf : Measurable (Function.uncurry f) := by
    have hh := (measurable_fixed_extended (k:=m+r) ρ s).comp (measurable_append (E:=Vector d) m r)
    exact hh
  have hbound : ∫⁻ X, (∫⁻ Z, f X Z ∂gaussianRows r d)^q ∂gaussianRows m d ≠ ∞ := by
    apply ne_of_lt
    exact (extended_mixed_moment hdim ρ B D hB hD hBρ hDρ s).trans_lt (by
      unfold momentConstant
      finiteness)
  rw [gaussianRows, ae_pi_append (stdGaussian (Vector d)) m r
    (measurableSet_lt (measurable_fixed_extended (k:=m+r) ρ s) measurable_const)]
  filter_upwards [ae_lt_top (hf.lintegral_prod_right.pow_const q) hbound] with X hX
  have hXt : ∫⁻ Z, f X Z ∂gaussianRows r d ≠ ∞ := by
    intro he
    rw [he, ENNReal.top_pow (by rcases hdim with ⟨_, _, h, _, _⟩; omega)] at hX
    exact (lt_irrefl _ hX)
  have hfX : Measurable (fun Z : Rows r d => f X Z) := by
    have hh := hf.comp (show Measurable (fun Z : Rows r d => (X,Z)) from
      measurable_const.prodMk measurable_id)
    exact hh
  exact ae_lt_top hfX hXt




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Sphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace

section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma unitBallLaw_closedBall (z : E) {r : ℝ} (hr : 0 < r) :
    unitBallLaw (Metric.closedBall z r) ≤ ENNReal.ofReal (r ^ Module.finrank ℝ E) := by
  have h0 : (volume : Measure E) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
  have ht : (volume : Measure E) (Metric.ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  calc
    _ ≤ ((volume : Measure E) (Metric.ball 0 1))⁻¹ * volume (Metric.closedBall z r) := by
      exact mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)
    _ = _ := by
      rw [Measure.addHaar_closedBall _ _ hr.le, mul_comm _ (_ * _), mul_assoc,
        ENNReal.mul_inv_cancel h0 ht, mul_one]

lemma unitBallLaw_local : HasLocalMassBound (unitBallLaw : Measure E)
    (Module.finrank ℝ E : ℝ) := by
  intro z _ r hr
  simpa only [Real.rpow_natCast] using unitBallLaw_closedBall z hr

lemma unitBallLaw_support : (unitBallLaw : Measure E).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, unitBallLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply Metric.isClosed_closedBall.measurableSet.compl]
  simp

lemma sphereLaw_apply [Nontrivial E] {s : Set (Metric.sphere (0 : E) 1)}
    (hs : MeasurableSet s) :
    sphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  have hd0 : (Module.finrank ℝ E : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hdt : (Module.finrank ℝ E : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hsub : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s) ⊆ Metric.closedBall (0 : E) 1 := by
    rintro _ ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      (mem_sphere_zero_iff_norm.mp x.property), mul_one, Real.norm_eq_abs,
      abs_of_pos hr.1]
    exact hr.2.le
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul, Measure.toSphere_apply_univ,
    Measure.toSphere_apply' _ hs, ENNReal.mul_inv (Or.inl hd0) (Or.inl hdt), unitBallLaw, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet,
    Set.inter_eq_left.mpr hsub]
  calc
    _ = ((volume : Measure E) (Metric.ball 0 1))⁻¹ *
      (((Module.finrank ℝ E : ℝ≥0∞))⁻¹ * (Module.finrank ℝ E)) *
      volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hd0 hdt, mul_one]

lemma sphereLaw_cap_raw [Nontrivial E] (z : E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hd : 1 ≤ Module.finrank ℝ E) :
    sphereLaw {s : Metric.sphere (0 : E) 1 | dist s.val z ≤ r} ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) *
        ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) := by
  classical
  let L := (Submodule.span ℝ ({z} : Set E)).toAffineSubspace
  let : Nonempty L := ⟨⟨0, (Submodule.span ℝ ({z} : Set E)).zero_mem⟩⟩
  have hl : Module.finrank ℝ L.direction ≤ 1 := by
    dsimp only [L]
    rw [Submodule.toAffineSubspace_direction]
    simpa using (finrank_span_le_card (R := ℝ) ({z} : Set E))
  have hm : (Module.finrank ℝ L.direction : ℝ) + (Module.finrank ℝ E - 1 : ℕ) ≤
      (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast (by omega : Module.finrank ℝ L.direction + (Module.finrank ℝ E - 1) ≤ Module.finrank ℝ E)
  have hsub : Set.Ioo (0 : ℝ) 1 •
      (Subtype.val '' {s : Metric.sphere (0 : E) 1 | dist s.val z ≤ r}) ⊆
      {t | Metric.infDist t L ≤ r} := by
    rintro _ ⟨c, hc, _, ⟨s, hs, rfl⟩, rfl⟩
    have hz : c • z ∈ L := Submodule.smul_mem _ c (Submodule.subset_span (by simp))
    exact (Metric.infDist_le_dist_of_mem hz).trans (by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hc.1]
      exact (mul_le_mul_of_nonneg_left hs hc.1.le).trans (mul_le_of_le_one_left hr.le hc.2.le))
  rw [sphereLaw_apply (measurableSet_le (by fun_prop) measurable_const)]
  apply (measure_mono hsub).trans
  apply (unitBallLaw_local.affine_tube_pow unitBallLaw_support L _ hm hr hr1).trans
  simp only [Real.rpow_natCast]
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hl)
    (by positivity)

end SphereBounds



lemma uniformSphere_growth {d a : ℕ} (hd : 1 ≤ d) (ha : a ≤ d-1) :
    LocalGrowth (uniformSphere d) a ((3:ℝ)*4^d) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  intro z t ht
  have hf : Module.finrank ℝ (Vector d) = d := finrank_euclideanSpace_fin
  change sphereLaw {s : Sphere d | dist (s:Vector d) z ≤ t} ≤ _
  by_cases ht1 : t ≤ 1
  · have hh := sphereLaw_cap_raw z ht ht1 (by simpa only [hf] using hd)
    rw [hf] at hh
    apply hh.trans
    calc
      _ ≤ ENNReal.ofReal ((3:ℝ)*4^d) * ENNReal.ofReal (t^a) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one ht.le ht1 ha))
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  · calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by
        apply ENNReal.one_le_ofReal.mpr
        have h4 := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4) (n:=d)
        have ht' := one_le_pow₀ (le_of_not_ge ht1) (n:=a)
        nlinarith

lemma dominatedSphere_growth {d a : ℕ} (ν : Measure (Sphere d)) {H : ℝ}
    (hH : 0 ≤ H) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d)
    (hd : 1 ≤ d) (ha : a ≤ d-1) : LocalGrowth ν a (H * (3*4^d)) := by
  intro z t ht
  calc
    _ ≤ (ENNReal.ofReal H • uniformSphere d) _ := hν _
    _ = ENNReal.ofReal H * uniformSphere d _ := rfl
    _ ≤ ENNReal.ofReal H * ENNReal.ofReal ((3*4^d)*t^a) :=
      mul_le_mul' le_rfl (uniformSphere_growth hd ha z t ht)
    _ = _ := by rw [← ENNReal.ofReal_mul hH]; congr 1; ring

lemma extended_eq_inverse_rnDeriv {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) :
    ∀ᵐ y ∂labelLaw ρ G, extendedCubeDensity ρ G y = (volume.rnDeriv (labelLaw ρ G) y)⁻¹ := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv volume (labelLaw ρ G)] with y hy
  have ht := (hy.comp tendsto_cube_scale).inv
  have he : (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) =ᶠ[atTop]
      (fun j : ℕ => (volume (Metric.closedBall y (1/(j:ℝ))) /
        labelLaw ρ G (Metric.closedBall y (1/(j:ℝ))))⁻¹) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hjp : 0 < 1/(j:ℝ) := by positivity
    rw [cubeAverage_eq_ball_ratio ρ G y hjp,
      ENNReal.inv_div (Or.inl (measure_ne_top _ _))]
    exact Or.inr (by rw [Real.volume_pi_closedBall y hjp.le]; positivity)
  exact (ht.congr' he.symm).liminf_eq

lemma labelLaw_ac_of_finite_extended {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d)
    (hf : ∀ᵐ (s : Sphere d) ∂ρ, extendedCubeDensity ρ G (label G (s:Vector d)) < ∞) :
    labelLaw ρ G ≪ volume := by
  have hm : Measurable (fun y => extendedCubeDensity ρ G y) := by
    have hh := (measurable_extendedCubeDensity (k:=k) ρ).comp
      (show Measurable (fun y : Fin k → ℝ => (G,y)) from measurable_const.prodMk measurable_id)
    exact hh
  have hfy : ∀ᵐ y ∂labelLaw ρ G, extendedCubeDensity ρ G y < ∞ :=
    (ae_map_iff (by unfold label; fun_prop) (measurableSet_lt hm measurable_const)).mpr hf
  apply Measure.ae_le_iff_absolutelyContinuous.mp
  intro p hp
  filter_upwards [extended_eq_inverse_rnDeriv ρ G, hfy,
    Measure.ae_rnDeriv_ne_zero_imp_of_ae (labelLaw ρ G) hp] with y he hy hpy
  apply hpy
  intro hz
  rw [he, hz, ENNReal.inv_zero] at hy
  exact (lt_irrefl _ hy)

lemma measurable_swapped_extended {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] :
    Measurable (fun z : Sphere d × Rows k d =>
      extendedCubeDensity ρ z.2 (label z.2 (z.1:Vector d))) := by
  have hh := (measurable_own_extended (k:=k) ρ).comp
    (show Measurable (Prod.swap : Sphere d × Rows k d → Rows k d × Sphere d) from measurable_swap)
  exact hh

lemma ae_labelLaw_ac_of_growth {d m r q : ℕ} (hdim : AdmissibleDimensions d m r q)
    (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (B D : ℝ) (hB : 0 < B) (hD : 0 < D)
    (hBρ : LocalGrowth ρ (m+r) B) (hDρ : LocalGrowth ρ (d-1) D) :
    ∀ᵐ G ∂gaussianRows (m+r) d, labelLaw ρ G ≪ volume := by
  have hf : ∀ᵐ G ∂gaussianRows (m+r) d, ∀ᵐ (s : Sphere d) ∂ρ,
      extendedCubeDensity ρ G (label G (s:Vector d)) < ∞ := by
    apply (Measure.ae_ae_comm ?_).mp
    · exact Filter.Eventually.of_forall (extended_ae_finite hdim ρ B D hB hD hBρ hDρ)
    · exact measurableSet_lt (measurable_swapped_extended (k:=m+r) ρ) measurable_const
  exact hf.mono (fun G hG => labelLaw_ac_of_finite_extended ρ G hG)



lemma volume_ae_cube_limit {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) :
    ∀ᵐ y ∂(volume : Measure (Fin k → ℝ)),
      Tendsto (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) atTop (𝓝 (exactDensity ρ G y)) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv (labelLaw ρ G) volume,
    Measure.rnDeriv_ne_top (labelLaw ρ G) volume] with y hy hyt
  have ht := hy.comp tendsto_cube_scale
  have he : (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) =ᶠ[atTop]
      (fun j : ℕ => labelLaw ρ G (Metric.closedBall y (1/(j:ℝ))) /
        volume (Metric.closedBall y (1/(j:ℝ)))) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact cubeAverage_eq_ball_ratio ρ G y (by positivity)
  have htc := ht.congr' he.symm
  exact (exactDensity_eq_of_tendsto ρ G y htc hyt).symm ▸ htc



open InformationTheory



lemma entropy_exp_bound {A : Type*} [MeasurableSpace A]
    (P Q : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : klDiv P Q ≠ ∞) (f c : A → ℝ)
    (hf : Measurable f) (hc : Measurable c) (hf0 : ∀ x, 0 ≤ f x)
    (hci : Integrable c P)
    (hExp : ∫⁻ x, ENNReal.ofReal (Real.exp (f x-c x)) ∂Q ≤ 1) :
    Integrable f P ∧ ∫ x, f x ∂P ≤ (klDiv P Q).toReal + ∫ x, c x ∂P := by
  obtain ⟨hPQ, hllr⟩ := klDiv_ne_top_iff.mp hKL
  let v : A → ℝ := fun x => Real.exp (f x-c x-llr P Q x)
  have hvm : Measurable v := (hf.sub hc |>.sub (measurable_llr P Q)).exp
  have hv0 (x : A) : 0 ≤ v x := (Real.exp_pos _).le
  have hvbound : ∫⁻ x, ENNReal.ofReal (v x) ∂P ≤ 1 := by
    rw [← lintegral_rnDeriv_mul hPQ hvm.ennreal_ofReal.aemeasurable]
    apply le_trans (lintegral_mono_ae ?_) hExp
    filter_upwards [Measure.rnDeriv_ne_top P Q] with x hxt
    by_cases hx0 : P.rnDeriv Q x = 0
    · simp [hx0]
    · have hxr : 0 < (P.rnDeriv Q x).toReal := ENNReal.toReal_pos hx0 hxt
      dsimp only [v]
      rw [Real.exp_sub, llr_def, Real.exp_log hxr, ENNReal.ofReal_div_of_pos hxr,
        ENNReal.ofReal_toReal hxt, div_eq_mul_inv, ← mul_assoc,
        mul_comm (P.rnDeriv Q x), mul_assoc, ENNReal.mul_inv_cancel hx0 hxt, mul_one]
  have hvi : Integrable v P :=
    (lintegral_ofReal_ne_top_iff_integrable hvm.aestronglyMeasurable
      (Filter.Eventually.of_forall hv0)).mp (ne_of_lt (hvbound.trans_lt (by simp)))
  have hvint : ∫ x, v x ∂P ≤ 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hvi (Filter.Eventually.of_forall hv0)] at hvbound
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp (by simpa using hvbound)
  have hle : ∀ x, f x ≤ llr P Q x + c x + v x - 1 := by
    intro x
    have he := Real.add_one_le_exp (f x-c x-llr P Q x)
    dsimp only [v]
    linarith
  have hup : Integrable (fun x => llr P Q x + c x + v x - 1) P :=
    ((hllr.add hci).add hvi).sub (integrable_const 1)
  have hfi : Integrable f P := integrable_of_le_of_le hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hle) (integrable_zero _ _ _) hup
  refine ⟨hfi, ?_⟩
  have hb := integral_mono hfi hup hle
  have hi : (∫ x, llr P Q x + c x + v x - 1 ∂P) =
      (∫ x, llr P Q x ∂P) + (∫ x, c x ∂P) + (∫ x, v x ∂P) - 1 := by
    rw [integral_sub (f:=fun x => llr P Q x+c x+v x) (g:=fun _ => 1)
      ((hllr.add hci).add hvi) (integrable_const 1)]
    rw [integral_add (f:=fun x => llr P Q x+c x) (g:=v) (hllr.add hci) hvi]
    rw [integral_add hllr hci, integral_const]
    simp
  rw [hi] at hb
  rw [toReal_klDiv_of_measure_eq hPQ (by simp)]
  linarith


lemma lintegral_one_add_pow_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (F : A → ℝ≥0∞)
    (hF : Measurable F) {q : ℕ} (hq : 1 ≤ q) {C : ℝ≥0∞}
    (hC : ∫⁻ x, (F x)^q ∂μ ≤ C^q) :
    ∫⁻ x, (1+F x)^q ∂μ ≤ (1+C)^q := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hh := ENNReal.lintegral_Lp_add_le (μ:=μ) (f:=fun _ : A => (1:ℝ≥0∞)) (g:=F)
    measurable_const.aemeasurable hF.aemeasurable (show (1:ℝ) ≤ q by exact_mod_cast hq)
  simp only [Pi.add_apply, ENNReal.rpow_natCast, one_pow,
    lintegral_const, measure_univ, mul_one, ENNReal.one_rpow] at hh
  have hFroot : (∫⁻ x, (F x)^q ∂μ) ^ (1/(q:ℝ)) ≤ C := by
    apply (ENNReal.rpow_le_rpow hC (by positivity)).trans_eq
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
  have hroot := hh.trans (add_le_add_right hFroot 1)
  have hpow := ENNReal.rpow_le_rpow hroot hq0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one,
    ENNReal.rpow_natCast] at hpow
  exact hpow




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

open InformationTheory

lemma joint_le_fst_prod_count {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (P : Measure (A × W)) [SFinite P.fst] :
    P ≤ P.fst.prod (Measure.count : Measure W) := by
  apply Measure.le_iff.mpr
  intro t ht
  have hm (w : W) : MeasurableSet {a : A | (a,w) ∈ t} :=
    ht.preimage (measurable_id.prodMk measurable_const)
  calc
    P t ≤ P (⋃ w : W, Prod.fst ⁻¹' {a : A | (a,w) ∈ t}) := by
      apply measure_mono
      intro z hz
      exact Set.mem_iUnion.mpr ⟨z.2, hz⟩
    _ ≤ ∑' w : W, P (Prod.fst ⁻¹' {a : A | (a,w) ∈ t}) := measure_iUnion_le _
    _ = ∑' w : W, P.fst {a : A | (a,w) ∈ t} := by
      congr 1; funext w; exact (Measure.fst_apply (hm w)).symm
    _ = (P.fst.prod Measure.count) t := by
      rw [Measure.prod_apply_symm ht, lintegral_count]
      rfl

lemma joint_ac_fst_prod_count {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (P : Measure (A × W)) [SFinite P.fst] :
    P ≪ P.fst.prod (Measure.count : Measure W) := (joint_le_fst_prod_count P).absolutelyContinuous

lemma ae_positive_atom {W : Type*} [MeasurableSpace W] [Countable W]
    [MeasurableSingletonClass W] (π : Measure W) : ∀ᵐ w ∂π, π {w} ≠ 0 := by
  have : π {w | π {w} = 0} = 0 := by
    rw [show {w | π {w} = 0} = ⋃ w : {w : W // π {w} = 0}, ({w.1} : Set W) by
      ext w; simp]
    exact measure_iUnion_null (fun w => w.2)
  simpa only [ae_iff, not_not] using this

lemma joint_ac_prod_marginals {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (P : Measure (A × W)) [IsFiniteMeasure P] :
    P ≪ P.fst.prod P.snd := by
  apply Measure.AbsolutelyContinuous.mk
  intro t ht hzero
  have hm (w : W) : MeasurableSet {a : A | (a,w) ∈ t} :=
    ht.preimage (measurable_id.prodMk measurable_const)
  have hsec : ∀ᵐ w ∂P.snd, P.fst {a : A | (a,w) ∈ t} = 0 := by
    rw [Measure.prod_apply_symm ht] at hzero
    exact (lintegral_eq_zero_iff (measurable_measure_prodMk_right ht)).mp hzero
  have hslice (w : W) : P (t ∩ Prod.snd ⁻¹' {w}) = 0 := by
    by_cases hw : P.snd {w} = 0
    · exact measure_mono_null Set.inter_subset_right (by rwa [← Measure.snd_apply (measurableSet_singleton w)])
    · have hz : P.fst {a : A | (a,w) ∈ t} = 0 := (ae_iff_of_countable.mp hsec) w hw
      apply measure_mono_null (t:=Prod.fst ⁻¹' {a : A | (a,w) ∈ t})
      · rintro ⟨a,v⟩ ⟨ha,hv⟩
        have hvw : v = w := hv
        simpa only [Set.mem_preimage, Set.mem_ofPred_eq, hvw] using ha
      · rwa [← Measure.fst_apply (hm w)]
  have he : t = ⋃ w : W, t ∩ Prod.snd ⁻¹' {w} := by ext z; simp
  rw [he]
  exact measure_iUnion_null hslice

lemma joint_le_prod_inverse_mass {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (P : Measure (A × W)) [IsFiniteMeasure P] :
    P ≤ (P.fst.prod P.snd).withDensity (fun z => (P.snd {z.2})⁻¹) := by
  have hm : Measurable (fun w : W => (P.snd {w})⁻¹) := measurable_of_countable _
  rw [← prod_withDensity_right hm]
  apply Measure.le_iff.mpr
  intro t ht
  have htm (w : W) : MeasurableSet {a : A | (a,w) ∈ t} :=
    ht.preimage (measurable_id.prodMk measurable_const)
  have he : t = ⋃ w : W, t ∩ Prod.snd ⁻¹' {w} := by ext z; simp
  calc
    P t ≤ ∑' w : W, P (t ∩ Prod.snd ⁻¹' {w}) := by
      calc P t = P (⋃ w : W, t ∩ Prod.snd ⁻¹' {w}) := congrArg P he
           _ ≤ _ := measure_iUnion_le (fun w : W => t ∩ Prod.snd ⁻¹' {w})
    _ ≤ ∑' w : W, P.fst {a : A | (a,w) ∈ t} * ((P.snd {w})⁻¹ * P.snd {w}) := by
      apply ENNReal.tsum_le_tsum
      intro w
      by_cases hw : P.snd {w} = 0
      · simp only [hw, ENNReal.inv_zero, mul_zero]
        exact le_of_eq (measure_mono_null Set.inter_subset_right
          (by rwa [← Measure.snd_apply (measurableSet_singleton w)]))
      · rw [ENNReal.inv_mul_cancel hw (measure_ne_top _ _), mul_one, Measure.fst_apply (htm w)]
        apply measure_mono
        rintro ⟨a,v⟩ ⟨ha,hv⟩
        have hvw : v = w := hv
        simpa only [Set.mem_preimage, Set.mem_ofPred_eq, hvw] using ha
    _ = (P.fst.prod (P.snd.withDensity (fun w => (P.snd {w})⁻¹))) t := by
      rw [Measure.prod_apply_symm ht, lintegral_withDensity_eq_lintegral_mul P.snd hm
        (measurable_measure_prodMk_right ht), lintegral_countable']
      congr 1; funext w
      change P.fst {a : A | (a,w) ∈ t} * ((P.snd {w})⁻¹ * P.snd {w}) =
        ((P.snd {w})⁻¹ * P.fst {a : A | (a,w) ∈ t}) * P.snd {w}
      ac_rfl

lemma rnDeriv_le_of_le_withDensity {A : Type*} [MeasurableSpace A]
    (P Q : Measure A) [IsFiniteMeasure P] [SigmaFinite Q]
    (b : A → ℝ≥0∞) (hPQ : P ≤ Q.withDensity b) :
    P.rnDeriv Q ≤ᵐ[Q] b := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv P Q)
  intro s hs hsf
  calc
    ∫⁻ x in s, P.rnDeriv Q x ∂Q ≤ P s := Measure.setLIntegral_rnDeriv_le s
    _ ≤ (Q.withDensity b) s := hPQ s
    _ = ∫⁻ x in s, b x ∂Q := withDensity_apply _ hs

lemma klDiv_bound_of_llr_le {A : Type*} [MeasurableSpace A]
    (P Q : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (c : A → ℝ) (hci : Integrable c P)
    (hc : ∀ᵐ x ∂P, llr P Q x ≤ c x) :
    klDiv P Q ≠ ∞ ∧ (klDiv P Q).toReal ≤ ∫ x, c x ∂P := by
  have hri : Integrable (fun x => (Q.rnDeriv P x).toReal) P := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ:=Q) (ν:=P) (s:=Set.univ) (measure_ne_top _ _))
  have hlo : ∀ᵐ x ∂P, -(Q.rnDeriv P x).toReal ≤ llr P Q x := by
    filter_upwards [exp_neg_llr hPQ] with x hx
    have h := Real.add_one_le_exp (-llr P Q x)
    rw [hx] at h
    linarith
  have hli : Integrable (llr P Q) P := integrable_of_le_of_le
    (measurable_llr P Q).aestronglyMeasurable hlo hc hri.neg hci
  refine ⟨klDiv_ne_top hPQ hli, ?_⟩
  rw [toReal_klDiv_of_measure_eq hPQ (by simp)]
  exact integral_mono_ae hli hci hc


lemma atom_surprisal_nonneg {W : Type*} [MeasurableSpace W]
    (π : Measure W) [IsProbabilityMeasure π] (w : W) :
    0 ≤ -Real.log (π {w}).toReal := by
  apply neg_nonneg.mpr
  exact Real.log_nonpos ENNReal.toReal_nonneg (by exact_mod_cast ENNReal.toReal_mono (by simp) (prob_le_one))

lemma countable_information_le_entropy {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (P : Measure (A × W)) [IsProbabilityMeasure P]
    (hH : shannonEntropy P.snd ≠ ∞) :
    klDiv P (P.fst.prod P.snd) ≠ ∞ ∧
      (klDiv P (P.fst.prod P.snd)).toReal ≤ (shannonEntropy P.snd).toReal := by
  let c : W → ℝ := fun w => -Real.log (P.snd {w}).toReal
  have hcm : Measurable c := measurable_of_countable _
  have hci : Integrable c P.snd :=
    (lintegral_ofReal_ne_top_iff_integrable hcm.aestronglyMeasurable
      (Filter.Eventually.of_forall (atom_surprisal_nonneg P.snd))).mp hH
  have hcip : Integrable (fun z : A × W => c z.2) P :=
    (integrable_map_measure hcm.aestronglyMeasurable measurable_snd.aemeasurable).mp hci
  have hPQ := joint_ac_prod_marginals P
  have hb := rnDeriv_le_of_le_withDensity P (P.fst.prod P.snd)
    (fun z => (P.snd {z.2})⁻¹)
    (joint_le_prod_inverse_mass P)
  have hpos : ∀ᵐ z : A × W ∂P, P.snd {z.2} ≠ 0 :=
    (ae_map_iff measurable_snd.aemeasurable ((Set.to_countable _).measurableSet)).mp (ae_positive_atom P.snd)
  have hll : ∀ᵐ z ∂P, llr P (P.fst.prod P.snd) z ≤ c z.2 := by
    filter_upwards [hPQ.ae_le hb, hpos, Measure.rnDeriv_pos hPQ,
      hPQ.ae_le (Measure.rnDeriv_ne_top P (P.fst.prod P.snd))] with z hz hzp hzr hzt
    have ht : (P.snd {z.2})⁻¹ ≠ ∞ := by simpa using hzp
    have hreal := ENNReal.toReal_mono ht hz
    have hl := Real.log_le_log (ENNReal.toReal_pos hzr.ne' hzt) hreal
    simpa only [llr, ENNReal.toReal_inv, Real.log_inv, c] using hl
  obtain ⟨hf, hi⟩ := klDiv_bound_of_llr_le P (P.fst.prod P.snd) hPQ
    (fun z => c z.2) hcip hll
  refine ⟨hf, hi.trans_eq ?_⟩
  rw [← integral_map measurable_snd.aemeasurable hcm.aestronglyMeasurable]
  exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
    (atom_surprisal_nonneg P.snd)) hcm.aestronglyMeasurable)



lemma klDiv_map_equiv {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P Q : Measure A) [IsFiniteMeasure P] [IsFiniteMeasure Q] (e : A ≃ᵐ B) :
    klDiv (P.map e) (Q.map e) = klDiv P Q := by
  apply le_antisymm (klDiv_map_le P Q e.measurable)
  have h := klDiv_map_le (P.map e) (Q.map e) e.symm.measurable
  simpa only [e.map_symm_map] using h

lemma map_swapLast_prod {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (τ : Measure C) [SFinite μ] [SFinite ν] [SFinite τ] :
    ((μ.prod ν).prod τ).map swapLast = (μ.prod τ).prod ν := by
  have he : (swapLast : (A×B)×C ≃ᵐ (A×C)×B) =
      (MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl A).prodCongr
        (MeasurableEquiv.prodComm (α:=B) (β:=C)))).trans MeasurableEquiv.prodAssoc.symm := by
    ext p <;> rfl
  rw [he]
  change Measure.map (MeasurableEquiv.prodAssoc.symm ∘
    (Prod.map id Prod.swap) ∘ MeasurableEquiv.prodAssoc) _ = _
  rw [← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (measurable_id.prodMap measurable_swap |>.comp MeasurableEquiv.prodAssoc.measurable)]
  rw [← Measure.map_map (measurable_id.prodMap measurable_swap) MeasurableEquiv.prodAssoc.measurable]
  rw [Measure.prodAssoc_prod, ← Measure.map_prod_map _ _ measurable_id measurable_swap,
    Measure.map_id, Measure.prod_swap]
  simpa only [Measure.prodAssoc_prod] using
    (MeasurableEquiv.prodAssoc.map_symm_map (μ:=((μ.prod τ).prod ν)))


lemma rowInformation_le_entropy {S W X : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((S×W)×X)) [IsProbabilityMeasure P]
    (ν : Measure S) (γ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hInd : (P.map swapLast).fst = ν.prod γ)
    (hH : shannonEntropy (P.map swapLast).snd ≠ ∞) :
    rowInformation P γ ≠ ∞ ∧
      (rowInformation P γ).toReal ≤ (shannonEntropy (P.map swapLast).snd).toReal := by
  let : IsProbabilityMeasure (P.map (swapLast : (S×W)×X ≃ᵐ (S×X)×W)) :=
    Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  let π := (P.map swapLast).snd
  have hRef : (((ν.prod π).prod γ).map swapLast) =
      (P.map swapLast).fst.prod (P.map swapLast).snd := by
    rw [map_swapLast_prod, hInd]
  have hi := countable_information_le_entropy (P.map swapLast) hH
  rw [← hRef, klDiv_map_equiv] at hi
  have hchain := klDiv_compProd_eq_add P.fst (ν.prod π) P.condKernel (Kernel.const _ γ)
  rw [P.disintegrate P.condKernel, Measure.compProd_const, Measure.compProd_const] at hchain
  have hle : rowInformation P γ ≤ klDiv P ((ν.prod π).prod γ) := by
    rw [hchain]
    exact le_add_left le_rfl
  exact ⟨ne_top_of_le_ne_top hi.1 hle, (ENNReal.toReal_mono hi.1 hle).trans hi.2⟩



lemma map_fiber_ac_prod {A S Y : Type*} [MeasurableSpace A] [MeasurableSpace S]
    [MeasurableSpace Y] (μ : Measure A) (ν : Measure S) (L : Measure Y)
    [SFinite μ] [SFinite ν] [SFinite L]
    (f : A×S → Y) (hf : Measurable f)
    (hac : ∀ᵐ a ∂μ, ν.map (fun s => f (a,s)) ≪ L) :
    (μ.prod ν).map (fun z => (z.1,f z)) ≪ μ.prod L := by
  apply Measure.AbsolutelyContinuous.mk
  intro t ht ht0
  rw [Measure.prod_apply ht] at ht0
  have hz : ∀ᵐ a ∂μ, L {y | (a,y) ∈ t} = 0 :=
    (lintegral_eq_zero_iff (measurable_measure_prodMk_left ht)).mp ht0
  rw [Measure.map_apply (measurable_fst.prodMk hf) ht,
    Measure.prod_apply (ht.preimage (measurable_fst.prodMk hf))]
  apply (lintegral_eq_zero_iff
    (measurable_measure_prodMk_left (ht.preimage (measurable_fst.prodMk hf)))).mpr
  filter_upwards [hac, hz] with a ha hza
  have hh := ha hza
  have ham : Measurable (fun s : S => f (a,s)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have has : MeasurableSet {y : Y | (a,y) ∈ t} :=
    ht.preimage (show Measurable (fun y : Y => (a,y)) from measurable_const.prodMk measurable_id)
  rw [Measure.map_apply ham has] at hh
  exact hh

lemma ae_condKernel_ac_of_joint_ac {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] (P : Measure (A×Y)) [IsFiniteMeasure P]
    (R : Measure A) (L : Measure Y) [SFinite R] [SFinite L]
    (hac : P ≪ R.prod L) : ∀ᵐ a ∂P.fst, P.condKernel a ≪ L := by
  obtain ⟨L', hL', hLL', hL'L⟩ := exists_isFiniteMeasure_absolutelyContinuous L
  let := hL'
  have hh : P.fst ⊗ₘ P.condKernel ≪ R ⊗ₘ Kernel.const A L' := by
    rw [P.disintegrate P.condKernel, Measure.compProd_const]
    exact hac.trans ((Measure.AbsolutelyContinuous.refl R).prod hLL')
  filter_upwards [hh.kernel_of_compProd] with a ha
  exact ha.trans hL'L

lemma adjoin_countable_ac {A Y W : Type*} [MeasurableSpace A] [MeasurableSpace Y]
    [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((A×Y)×W)) [IsFiniteMeasure P]
    (R : Measure A) (L : Measure Y) [SFinite R] [SFinite L]
    (hac : P.fst ≪ R.prod L) :
    P.map (swapLast : (A×Y)×W ≃ᵐ (A×W)×Y) ≪ (R.prod Measure.count).prod L := by
  have h := (joint_ac_fst_prod_count P).trans (hac.prod (Measure.AbsolutelyContinuous.refl (Measure.count : Measure W)))
  have hm := h.map (swapLast : (A×Y)×W ≃ᵐ (A×W)×Y).measurable
  rwa [map_swapLast_prod] at hm


lemma countable_null_transfer {A Y W : Type*} [MeasurableSpace A] [MeasurableSpace Y]
    [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
    (N : Measure ((A×W)×Y)) (R : Measure A) (L : Measure Y)
    [SFinite R] [SFinite L]
    (hac : N ≪ (R.prod Measure.count).prod L)
    (p : A → W → Y → Prop)
    (hpm : ∀ w, MeasurableSet {ay : A×Y | p ay.1 w ay.2})
    (hp : ∀ w a, ∀ᵐ y ∂L, p a w y) : ∀ᵐ z ∂N, p z.1.1 z.1.2 z.2 := by
  apply hac.ae_le
  have hm : MeasurableSet {z : (A×W)×Y | p z.1.1 z.1.2 z.2} := by
    have he : {z : (A×W)×Y | p z.1.1 z.1.2 z.2} =
      ⋃ w : W, {z : (A×W)×Y | z.1.2 = w} ∩
        (fun z : (A×W)×Y => (z.1.1,z.2)) ⁻¹' {ay | p ay.1 w ay.2} := by
      ext z; simp
    rw [he]
    exact MeasurableSet.iUnion fun w =>
      (measurableSet_eq_fun measurable_fst.snd measurable_const).inter
        ((hpm w).preimage (measurable_fst.fst.prodMk measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  exact Filter.Eventually.of_forall fun aw => hp aw.2 aw.1


lemma log_one_add_nonneg (x : ℝ≥0∞) : 0 ≤ Real.log (1+x.toReal) :=
  Real.log_nonneg (le_add_of_nonneg_right ENNReal.toReal_nonneg)

lemma log_one_add_le (x : ℝ≥0∞) : Real.log (1+x.toReal) ≤ x.toReal := by
  simpa using Real.log_le_sub_one_of_pos (show 0 < 1+x.toReal by positivity)

lemma measurable_log_one_add {A : Type*} [MeasurableSpace A] {f : A → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fun x => Real.log (1+(f x).toReal)) :=
  (measurable_const.add hf.ennreal_toReal).log

lemma log_one_add_jensen {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (F : A → ℝ≥0∞)
    (hFm : Measurable F) (hFt : ∀ a, F a ≠ ∞)
    (hFin : ∫⁻ a, F a ∂μ ≠ ∞) :
    ∫⁻ a, ENNReal.ofReal (Real.log (1+(F a).toReal)) ∂μ ≤
      ENNReal.ofReal (Real.log (1+(∫⁻ a, F a ∂μ).toReal)) := by
  have hFi : Integrable (fun a => (F a).toReal) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable hFm.ennreal_toReal.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))).mp
    simpa only [ENNReal.ofReal_toReal (hFt _)] using hFin
  have hLi : Integrable (fun a => Real.log (1+(F a).toReal)) μ :=
    hFi.mono' (measurable_log_one_add hFm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs, abs_of_nonneg (log_one_add_nonneg _)]; exact log_one_add_le _)
  let M := 1+(∫⁻ a, F a ∂μ).toReal
  have hM : 0 < M := by dsimp [M]; positivity
  have htangent (a : A) : Real.log (1+(F a).toReal) ≤
      Real.log M + (1+(F a).toReal)/M - 1 := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < (1+(F a).toReal)/M by positivity)
    rw [Real.log_div (by positivity) hM.ne'] at hh
    linarith
  have hupper : Integrable (fun a => Real.log M + (1+(F a).toReal)/M - 1) μ :=
    ((integrable_const _).add (((integrable_const 1).add hFi).div_const M)).sub (integrable_const _)
  have hbound := integral_mono hLi hupper htangent
  have hmean : ∫ a, (1+(F a).toReal)/M ∂μ = 1 := by
    rw [integral_div, integral_add (integrable_const 1) hFi, integral_const,
      integral_toReal hFm.aemeasurable (Filter.Eventually.of_forall fun a => lt_top_iff_ne_top.mpr (hFt a))]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    exact div_self hM.ne'
  rw [integral_sub (f:=fun a => Real.log M+(1+(F a).toReal)/M) (g:=fun _ => 1)
    ((integrable_const _).add (((integrable_const 1).add hFi).div_const M))
    (integrable_const 1), integral_add (f:=fun _ => Real.log M) (g:=fun a => (1+(F a).toReal)/M)
    (integrable_const _) (((integrable_const 1).add hFi).div_const M),
    hmean, integral_const, integral_const] at hbound
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, add_sub_cancel_right] at hbound
  rw [← ofReal_integral_eq_lintegral_ofReal hLi (Filter.Eventually.of_forall fun a => log_one_add_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hbound


lemma exp_log_normalization (v : ℝ≥0∞) (hv : v ≠ ∞) (c : ℝ) (hc : 0 ≤ c) (q : ℕ) :
    ENNReal.ofReal (Real.exp ((q:ℝ)*Real.log (1+v.toReal)-(q:ℝ)*Real.log (1+c))) =
      (1+v)^q / (ENNReal.ofReal (1+c))^q := by
  rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by positivity), Real.exp_log (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
    ENNReal.ofReal_one, ENNReal.ofReal_toReal hv]


lemma mixed_entropy_log_bound {A X Z : Type*} [MeasurableSpace A] [MeasurableSpace X]
    [MeasurableSpace Z] (P : Measure (A×X)) [IsProbabilityMeasure P]
    (γ : Measure X) (η : Measure Z) [IsProbabilityMeasure γ] [IsProbabilityMeasure η]
    (hKL : klDiv P (P.fst.prod γ) ≠ ∞)
    (K : (A×X)×Z → ℝ≥0∞) (hKm : Measurable K) (hKt : ∀ z, K z ≠ ∞)
    (hKint : ∀ ax, ∫⁻ z, K (ax,z) ∂η ≠ ∞)
    (C : A → ℝ) (hCm : Measurable C) (hC0 : ∀ a, 0 ≤ C a)
    (hCI : Integrable (fun a => Real.log (1+C a)) P.fst)
    {q : ℕ} (hq : 1 ≤ q)
    (hMoment : ∀ a, ∫⁻ x, (∫⁻ z, K ((a,x),z) ∂η)^q ∂γ ≤ (ENNReal.ofReal (C a))^q) :
    ∫⁻ axz, ENNReal.ofReal (Real.log (1+(K axz).toReal)) ∂P.prod η ≤
      ENNReal.ofReal ((klDiv P (P.fst.prod γ)).toReal / q +
        ∫ a, Real.log (1+C a) ∂P.fst) := by
  let F : A×X → ℝ≥0∞ := fun ax => ∫⁻ z, K (ax,z) ∂η
  have hFm : Measurable F := Measurable.lintegral_prod_right (f:=fun ax z => K (ax,z)) hKm
  have hf : Measurable (fun ax : A×X => (q:ℝ)*Real.log (1+(F ax).toReal)) :=
    measurable_const.mul (measurable_log_one_add hFm)
  have hc : Measurable (fun ax : A×X => (q:ℝ)*Real.log (1+C ax.1)) :=
    measurable_const.mul ((measurable_const.add (hCm.comp measurable_fst)).log)
  have hCc : Integrable (fun ax : A×X => Real.log (1+C ax.1)) P :=
    (integrable_map_measure (measurable_const.add hCm |>.log.aestronglyMeasurable)
      measurable_fst.aemeasurable).mp hCI
  have hcI := hCc.const_mul (q:ℝ)
  have hExp : ∫⁻ ax : A×X, ENNReal.ofReal (Real.exp
      ((q:ℝ)*Real.log (1+(F ax).toReal)-(q:ℝ)*Real.log (1+C ax.1))) ∂P.fst.prod γ ≤ 1 := by
    rw [lintegral_prod (fun ax : A×X => ENNReal.ofReal (Real.exp
      ((q:ℝ)*Real.log (1+(F ax).toReal)-(q:ℝ)*Real.log (1+C ax.1))))
      (by exact (hf.sub hc).exp.ennreal_ofReal.aemeasurable)]
    calc
      _ ≤ ∫⁻ _a, (1:ℝ≥0∞) ∂P.fst := by
        apply lintegral_mono; intro a
        have heq : (fun x => ENNReal.ofReal (Real.exp
            ((q:ℝ)*Real.log (1+(F (a,x)).toReal)-(q:ℝ)*Real.log (1+C a)))) =
            (fun x => (1+F (a,x))^q / (ENNReal.ofReal (1+C a))^q) := by
          funext x
          exact exp_log_normalization _ (hKint (a,x)) _ (hC0 a) q
        change (∫⁻ x, ENNReal.ofReal (Real.exp
          ((q:ℝ)*Real.log (1+(F (a,x)).toReal)-(q:ℝ)*Real.log (1+C a))) ∂γ) ≤ 1
        rw [heq]
        simp_rw [div_eq_mul_inv]
        have hpow : Measurable (fun x : X => (1+F (a,x))^q) :=
          (measurable_const.add (hFm.comp (measurable_const.prodMk measurable_id))).pow_const q
        rw [lintegral_mul_const _ hpow]
        have hh := lintegral_one_add_pow_le γ (fun x => F (a,x))
          (hFm.comp (measurable_const.prodMk measurable_id)) hq (hMoment a)
        have he : ENNReal.ofReal (1+C a) = 1+ENNReal.ofReal (C a) := by
          rw [ENNReal.ofReal_add (by norm_num) (hC0 a), ENNReal.ofReal_one]
        rw [he]
        apply (mul_le_mul' hh le_rfl).trans_eq
        exact ENNReal.mul_inv_cancel (by positivity) (by finiteness)
      _ = 1 := by simp
  obtain ⟨hfi, hbi⟩ := entropy_exp_bound P (P.fst.prod γ) hKL _ _ hf hc
    (fun ax => mul_nonneg (Nat.cast_nonneg _) (log_one_add_nonneg _)) hcI hExp
  have hqpos : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqne := hqpos.ne'
  have hLi : Integrable (fun ax => Real.log (1+(F ax).toReal)) P := by
    have hh := hfi.div_const (q:ℝ)
    simpa only [mul_div_cancel_left₀ _ hqne] using hh
  have hCeq : ∫ ax : A×X, Real.log (1+C ax.1) ∂P = ∫ a, Real.log (1+C a) ∂P.fst := by
    exact (integral_map measurable_fst.aemeasurable
      (measurable_const.add hCm |>.log.aestronglyMeasurable)).symm
  rw [integral_const_mul, integral_const_mul, hCeq] at hbi
  have hfinal : ∫ ax, Real.log (1+(F ax).toReal) ∂P ≤
      (klDiv P (P.fst.prod γ)).toReal / q + ∫ a, Real.log (1+C a) ∂P.fst := by
    rw [← sub_le_iff_le_add, le_div_iff₀ hqpos]
    nlinarith
  calc
    _ = ∫⁻ ax, ∫⁻ z, ENNReal.ofReal (Real.log (1+(K (ax,z)).toReal)) ∂η ∂P :=
      lintegral_prod _ (measurable_log_one_add hKm |>.ennreal_ofReal.aemeasurable)
    _ ≤ ∫⁻ ax, ENNReal.ofReal (Real.log (1+(F ax).toReal)) ∂P := by
      exact lintegral_mono fun ax => log_one_add_jensen η (fun z => K (ax,z))
        (hKm.comp (measurable_const.prodMk measurable_id)) (fun z => hKt (ax,z)) (hKint ax)
    _ = ENNReal.ofReal (∫ ax, Real.log (1+(F ax).toReal) ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hLi (Filter.Eventually.of_forall fun _ => log_one_add_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfinal



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.ActualRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


lemma measurable_actualRowsSignal {d m r : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (actualRowsSignal : ((Sphere d×W)×Rows m d)×Rows r d → _) :=
  ((measurable_append (E:=Vector d) m r).comp (measurable_fst.snd.prodMk measurable_snd)).prodMk
    measurable_fst.fst.fst

lemma measurable_actualObservation {d m r : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (actualObservation : ((Sphere d×W)×Rows m d)×Rows r d → _) := by
  have hG : Measurable (fun p : ((Sphere d×W)×Rows m d)×Rows r d => Fin.append p.1.2 p.2) := (measurable_append (E:=Vector d) m r).comp (measurable_fst.snd.prodMk measurable_snd)
  have hY : Measurable (fun p : ((Sphere d×W)×Rows m d)×Rows r d => label (Fin.append p.1.2 p.2) (p.1.1.1:Vector d)) := (measurable_own_label (k:=m+r) (d:=d)).comp measurable_actualRowsSignal
  exact (hG.prodMk measurable_fst.fst.snd).prodMk hY

lemma map_actualRowsSignal {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) :
    (actualExperiment (r:=r) P).map actualRowsSignal = (gaussianRows (m+r) d).prod ν := by
  let f : (Sphere d×W)×Rows m d → Sphere d×Rows m d := fun p => (p.1.1,p.2)
  have hf : Measurable f := measurable_fst.fst.prodMk measurable_snd
  have hBase : P.map f = ν.prod (gaussianRows m d) := by
    rw [Measure.fst, Measure.map_map measurable_fst swapLast.measurable] at hInd
    exact hInd
  let T := Prod.map f (id : Rows r d → Rows r d)
  have hT : Measurable T := hf.prodMap measurable_id
  have hpre : (actualExperiment (r:=r) P).map T =
      (ν.prod (gaussianRows m d)).prod (gaussianRows r d) := by
    change (P.prod (gaussianRows r d)).map (Prod.map f id) = _
    rw [← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id, hBase]
  let U : (Sphere d×Rows m d)×Rows r d → (Rows m d×Rows r d)×Sphere d :=
    fun p => ((p.1.2,p.2),p.1.1)
  have hU : Measurable U := (measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst
  have hmid : ((ν.prod (gaussianRows m d)).prod (gaussianRows r d)).map U =
      ((gaussianRows m d).prod (gaussianRows r d)).prod ν := by
    change Measure.map (Prod.swap ∘ MeasurableEquiv.prodAssoc) _ = _
    rw [← Measure.map_map measurable_swap MeasurableEquiv.prodAssoc.measurable,
      Measure.prodAssoc_prod, Measure.prod_swap]
  let V : (Rows m d×Rows r d)×Sphere d → Rows (m+r) d×Sphere d :=
    Prod.map (fun p => Fin.append p.1 p.2) id
  have hV : Measurable V := (measurable_append (E:=Vector d) m r).prodMap measurable_id
  have hlast : (((gaussianRows m d).prod (gaussianRows r d)).prod ν).map V =
      (gaussianRows (m+r) d).prod ν := by
    rw [show V = Prod.map (fun p : Rows m d×Rows r d => Fin.append p.1 p.2) id from rfl,
      ← Measure.map_prod_map _ _ (measurable_append (E:=Vector d) m r) measurable_id,
      Measure.map_id]
    rw [show ((gaussianRows m d).prod (gaussianRows r d)).map (fun p => Fin.append p.1 p.2) =
      gaussianRows (m+r) d from map_append_pi (stdGaussian (Vector d)) m r]
  have hfun : actualRowsSignal = V ∘ U ∘ T := rfl
  rw [hfun, ← Measure.map_map hV (hU.comp hT), ← Measure.map_map hU hT,
    hpre, hmid, hlast]

lemma actualObservation_ac {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d) :
    (actualExperiment (r:=r) P).map actualObservation ≪
      ((gaussianRows (m+r) d).prod (Measure.count : Measure W)).prod
        (volume : Measure (Fin (m+r) → ℝ)) := by
  have hB := dominatedSphere_growth ν hH.le hν (show 1 ≤ d by have := hdim.2.2.2.1; omega)
    (show m+r ≤ d-1 by have := hdim.2.2.2.1; omega)
  have hD := dominatedSphere_growth ν hH.le hν (show 1 ≤ d by have := hdim.2.2.2.1; omega) le_rfl
  have hac := ae_labelLaw_ac_of_growth hdim ν (H*(3*4^d)) (H*(3*4^d))
    (by positivity) (by positivity) hB hD
  have hGY := map_fiber_ac_prod (gaussianRows (m+r) d) ν volume
    (fun gs : Rows (m+r) d×Sphere d => label gs.1 (gs.2:Vector d)) measurable_own_label hac
  let J := (actualExperiment (r:=r) P).map
    (fun p => ((Fin.append p.1.2 p.2,label (Fin.append p.1.2 p.2) (p.1.1.1:Vector d)),p.1.1.2))
  have hJm : Measurable (fun p : ((Sphere d×W)×Rows m d)×Rows r d =>
      ((Fin.append p.1.2 p.2,label (Fin.append p.1.2 p.2) (p.1.1.1:Vector d)),p.1.1.2)) :=
    (measurable_actualRowsSignal.fst.prodMk
      (measurable_own_label.comp measurable_actualRowsSignal)).prodMk measurable_fst.fst.snd
  let : IsProbabilityMeasure (actualExperiment (r:=r) P) := inferInstanceAs (IsProbabilityMeasure (P.prod (gaussianRows r d)))
  let : IsProbabilityMeasure J := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hJfst : J.fst = ((gaussianRows (m+r) d).prod ν).map
      (fun gs : Rows (m+r) d×Sphere d => (gs.1,label gs.1 (gs.2:Vector d))) := by
    rw [← map_actualRowsSignal P ν hInd]
    rw [Measure.map_map (measurable_fst.prodMk measurable_own_label) measurable_actualRowsSignal]
    change ((actualExperiment P).map _).fst = _
    rw [Measure.fst, Measure.map_map measurable_fst hJm]
    rfl
  have hjac : J.fst ≪ (gaussianRows (m+r) d).prod (volume : Measure (Fin (m+r) → ℝ)) := by
    rw [hJfst]; exact hGY
  have hh := adjoin_countable_ac J (gaussianRows (m+r) d) volume hjac
  change (J.map swapLast) ≪ _ at hh
  dsimp only [J] at hh
  rw [Measure.map_map swapLast.measurable hJm] at hh
  exact hh


lemma measurable_countable_selection {A B T W : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace T] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (f : W → A×B → T)
    (hf : ∀ w, Measurable (f w)) :
    Measurable (fun z : (A×W)×B => f z.1.2 (z.1.1,z.2)) := by
  have hh : Measurable (fun z : (A×B)×W => f z.2 z.1) :=
    measurable_from_prod_countable_left hf
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

lemma measurable_selectedCube {k d : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (ρ : W → Measure (Sphere d))
    [∀ w, SFinite (ρ w)] (δ : ℝ) : Measurable (selectedCube (k:=k) ρ δ) :=
  measurable_countable_selection (fun w gy => cubeAverage (ρ w) gy.1 gy.2 δ)
    (fun w => measurable_cubeAverage (ρ w) δ)

lemma measurable_selectedExact {k d : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (ρ : W → Measure (Sphere d))
    [∀ w, SFinite (ρ w)] : Measurable (selectedExact (k:=k) ρ) :=
  measurable_countable_selection (fun w gy => exactDensity (ρ w) gy.1 gy.2)
    (fun w => measurable_exactDensity (ρ w))

lemma exactDensity_ne_top {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d) (y : Fin k → ℝ) :
    exactDensity ρ G y ≠ ∞ := by
  unfold exactDensity
  dsimp only
  split_ifs <;> simp

lemma actual_cube_limit {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d)
    (ρ : W → Measure (Sphere d)) [∀ w, IsFiniteMeasure (ρ w)] :
    ∀ᵐ p ∂actualExperiment (r:=r) P,
      Tendsto (fun j : ℕ => selectedCube ρ (1/(j:ℝ)) (actualObservation p)) atTop
        (𝓝 (selectedExact ρ (actualObservation p))) := by
  have hh := countable_null_transfer ((actualExperiment (r:=r) P).map actualObservation)
    (gaussianRows (m+r) d) (volume : Measure (Fin (m+r) → ℝ))
    (actualObservation_ac hdim P ν hInd H hH hν)
    (fun g w y => Tendsto (fun j : ℕ => cubeAverage (ρ w) g y (1/(j:ℝ))) atTop
      (𝓝 (exactDensity (ρ w) g y)))
    (fun w => measurableSet_tendsto_fun (fun j : ℕ => measurable_cubeAverage (ρ w) (1/(j:ℝ)))
      (measurable_exactDensity (ρ w)))
    (fun w g => volume_ae_cube_limit (ρ w) g)
  exact ae_of_ae_map measurable_actualObservation.aemeasurable hh

lemma actual_conditional_label_ac {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d) :
    ∀ᵐ gw ∂((actualExperiment (r:=r) P).map actualObservation).fst,
      ((actualExperiment (r:=r) P).map actualObservation).condKernel gw ≪ volume := by
  let : IsProbabilityMeasure (actualExperiment (r:=r) P) :=
    inferInstanceAs (IsProbabilityMeasure (P.prod (gaussianRows r d)))
  let : IsProbabilityMeasure ((actualExperiment (r:=r) P).map actualObservation) :=
    inferInstance
  exact ae_condKernel_ac_of_joint_ac _ _ _ (actualObservation_ac hdim P ν hInd H hH hν)


lemma momentBound_nonneg (C : ℝ) (d : ℕ) {B D : ℝ} (hB : 0 ≤ B) :
    0 ≤ momentBound C d B D := by
  unfold momentBound
  positivity

lemma cubeAverage_inner_finite {d m r : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (s : Sphere d) (X : Rows m d) (δ : ℝ) :
    ∫⁻ Z, cubeAverage ρ (Fin.append X Z) (label (Fin.append X Z) (s:Vector d)) δ
      ∂gaussianRows r d ≠ ∞ := by
  apply ne_top_of_le_ne_top (b:=ENNReal.ofReal ((2*δ)⁻¹^(m+r))*ρ univ)
  · finiteness
  · calc
      _ ≤ ∫⁻ _Z : Rows r d, ENNReal.ofReal ((2*δ)⁻¹^(m+r))*ρ univ ∂gaussianRows r d := by
        apply lintegral_mono; intro Z
        exact mul_le_mul' le_rfl (measure_mono (Set.subset_univ _))
      _ = _ := by simp

lemma actual_smoothed_log_bound {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (hKL : rowInformation P (gaussianRows m d) ≠ ∞)
    (ρ : W → Measure (Sphere d)) [∀ w, IsFiniteMeasure (ρ w)]
    (B D : W → ℝ) (hB : ∀ w, 0 < B w) (hD : ∀ w, 0 < D w)
    (hgB : ∀ w, LocalGrowth (ρ w) (m+r) (B w))
    (hgD : ∀ w, LocalGrowth (ρ w) (d-1) (D w))
    (hCI : Integrable (fun sw : Sphere d×W => Real.log (1+momentBound 9 d (B sw.2) (D sw.2))) P.fst)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ p, ENNReal.ofReal (Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal))
      ∂actualExperiment (r:=r) P ≤
        ENNReal.ofReal ((rowInformation P (gaussianRows m d)).toReal/q +
          ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst) := by
  apply mixed_entropy_log_bound P (gaussianRows m d) (gaussianRows r d) hKL
    (fun p => selectedCube ρ δ (actualObservation p))
    ((measurable_selectedCube ρ δ).comp measurable_actualObservation)
    (fun p => (cubeAverage_lt_top _ _ _ _).ne)
    (fun p => cubeAverage_inner_finite (ρ p.1.2) p.1.1 p.2 δ)
    (fun sw : Sphere d×W => momentBound 9 d (B sw.2) (D sw.2))
    ((measurable_of_countable (f:=fun w => momentBound 9 d (B w) (D w))).comp measurable_snd)
    (fun sw => momentBound_nonneg 9 d (hB sw.2).le) hCI hdim.2.2.1
  intro sw
  exact mixed_cube_moment hdim (ρ sw.2) (B sw.2) (D sw.2)
    (hB sw.2) (hD sw.2) (hgB sw.2) (hgD sw.2) sw.1 δ hδ

lemma log_lintegral_bound_of_ae_tendsto {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (f : ℕ → A → ℝ≥0∞) (F : A → ℝ≥0∞)
    (hf : ∀ j, Measurable (f j)) (hFt : ∀ a, F a ≠ ∞)
    (ht : ∀ᵐ a ∂μ, Tendsto (fun j => f j a) atTop (𝓝 (F a)))
    (R : ℝ≥0∞) (hR : ∀ j ≥ 1, ∫⁻ a, ENNReal.ofReal (Real.log (1+(f j a).toReal)) ∂μ ≤ R) :
    ∫⁻ a, ENNReal.ofReal (Real.log (1+(F a).toReal)) ∂μ ≤ R := by
  let g : ℕ → A → ℝ≥0∞ := fun j a => ENNReal.ofReal (Real.log (1+(f j a).toReal))
  have hlim : ∀ᵐ a ∂μ, liminf (fun j => g j a) atTop = ENNReal.ofReal (Real.log (1+(F a).toReal)) := by
    filter_upwards [ht] with a ha
    have htr := (ENNReal.continuousAt_toReal (hFt a)).tendsto.comp ha
    have hlog := (tendsto_const_nhds.add htr).log (show 1+(F a).toReal ≠ 0 by positivity)
    exact (ENNReal.continuous_ofReal.tendsto _ |>.comp hlog).liminf_eq
  calc
    _ = ∫⁻ a, liminf (fun j => g j a) atTop ∂μ := lintegral_congr_ae (hlim.mono fun a ha => ha.symm)
    _ ≤ liminf (fun j => ∫⁻ a, g j a ∂μ) atTop :=
      lintegral_liminf_le (fun j => (measurable_log_one_add (hf j)).ennreal_ofReal)
    _ ≤ R := liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
      ((eventually_ge_atTop 1).mono fun j hj => hR j hj).frequently

lemma logPositive_le_log_one_add (x : ℝ≥0∞) : logPositive x ≤ Real.log (1+x.toReal) := by
  apply max_le _ (log_one_add_nonneg x)
  by_cases h : x.toReal = 0
  · simp only [h, Real.log_zero, add_zero, Real.log_one, le_refl]
  · exact Real.log_le_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h)) (le_add_of_nonneg_left zero_le_one)

lemma log_bound_consequences {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f : A → ℝ≥0∞) (hf : Measurable f) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∫⁻ a, ENNReal.ofReal (Real.log (1+(f a).toReal)) ∂μ ≤ ENNReal.ofReal R) :
    (Integrable (fun a => Real.log (1+(f a).toReal)) μ ∧
      ∫ a, Real.log (1+(f a).toReal) ∂μ ≤ R) ∧
    Integrable (fun a => logPositive (f a)) μ ∧ extendedLogExpectation μ f ≤ (R:EReal) := by
  have hLi : Integrable (fun a => Real.log (1+(f a).toReal)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (measurable_log_one_add hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => log_one_add_nonneg _)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hR)
  have hLf : ∫ a, Real.log (1+(f a).toReal) ∂μ ≤ R := by
    rw [← ofReal_integral_eq_lintegral_ofReal hLi
      (Filter.Eventually.of_forall fun _ => log_one_add_nonneg _)] at hR
    exact (ENNReal.ofReal_le_ofReal_iff hR0).mp hR
  have hPi : Integrable (fun a => logPositive (f a)) μ := by
    apply hLi.mono' ((hf.ennreal_toReal.log.max measurable_const).aestronglyMeasurable)
    apply Filter.Eventually.of_forall; intro a
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact logPositive_le_log_one_add _
  refine ⟨⟨hLi,hLf⟩,hPi,?_⟩
  have hPL : ∫⁻ a, ENNReal.ofReal (logPositive (f a)) ∂μ ≤ ENNReal.ofReal R :=
    (lintegral_mono fun a => ENNReal.ofReal_le_ofReal (logPositive_le_log_one_add _)).trans hR
  apply (EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hPL)
    (EReal.coe_ennreal_nonneg (∫⁻ a, logNegative (f a) ∂μ))).trans
  have he : (ENNReal.ofReal R : EReal) = (R:EReal) :=
    by simpa using (EReal.coe_toENNReal (x := (R:EReal)) (by exact_mod_cast hR0))
  simp only [sub_zero, he, le_refl]



lemma completeFamily_pos {W : Type*} [MeasurableSpace W] (π : Measure W)
    (f : PositiveMessage π → ℝ) (hf : ∀ w, 0 < f w) (w : W) :
    0 < completeFamily π f 1 w := by
  unfold completeFamily
  split_ifs with h
  · exact hf ⟨w,h⟩
  · norm_num

lemma completeFamily_growth {W : Type*} [MeasurableSpace W] {d a : ℕ}
    (π : Measure W) (ρ : PositiveMessage π → Measure (Sphere d))
    (B : PositiveMessage π → ℝ) (hg : ∀ w, LocalGrowth (ρ w) a (B w)) (w : W) :
    LocalGrowth (completeFamily π ρ 0 w) a (completeFamily π B 1 w) := by
  unfold completeFamily
  split_ifs with h
  · exact hg ⟨w,h⟩
  · intro z t ht
    simp


theorem actualRowMain_oai {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d)
    (hEntropy : shannonEntropy (P.map swapLast).snd ≠ ∞)
    (ρ : PositiveMessage (P.map swapLast).snd → Measure (Sphere d))
    [∀ w, IsFiniteMeasure (ρ w)]
    (_hρac : ∀ w, ρ w ≪ uniformSphere d)
    (B D : PositiveMessage (P.map swapLast).snd → ℝ)
    (hB : ∀ w, 0 < B w) (hD : ∀ w, 0 < D w)
    (hgB : ∀ w, LocalGrowth (ρ w) (m+r) (B w))
    (hgD : ∀ w, LocalGrowth (ρ w) (d-1) (D w))
    (hCI : Integrable (fun sw : Sphere d×W => Real.log (1+momentBound 9 d
      (completeFamily (P.map swapLast).snd B 1 sw.2) (completeFamily (P.map swapLast).snd D 1 sw.2))) P.fst) :
    ActualRowConclusion (r:=r) (q:=q) P (completeFamily (P.map swapLast).snd ρ 0)
      (completeFamily (P.map swapLast).snd B 1) (completeFamily (P.map swapLast).snd D 1) := by
  let ρ' := completeFamily (P.map swapLast).snd ρ 0
  let B' := completeFamily (P.map swapLast).snd B 1
  let D' := completeFamily (P.map swapLast).snd D 1
  have hB' := completeFamily_pos (P.map swapLast).snd B hB
  have hD' := completeFamily_pos (P.map swapLast).snd D hD
  have hgB' := completeFamily_growth (P.map swapLast).snd ρ B hgB
  have hgD' := completeFamily_growth (P.map swapLast).snd ρ D hgD
  have hH : 0 < H := by
    by_contra hn
    have hh := hν univ
    simp [ENNReal.ofReal_of_nonpos (le_of_not_gt hn)] at hh
  obtain ⟨hKL,hKE⟩ := rowInformation_le_entropy P ν (gaussianRows m d) hInd hEntropy
  have hlim := actual_cube_limit hdim P ν hInd H hH hν ρ'
  let R := (rowInformation P (gaussianRows m d)).toReal/q +
    ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B' sw.2) (D' sw.2)) ∂P.fst
  have hR0 : 0 ≤ R := add_nonneg (div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))
    (integral_nonneg fun sw => Real.log_nonneg (le_add_of_nonneg_right (momentBound_nonneg 9 d (hB' sw.2).le)))
  have hsmooth (δ : ℝ) (hδ : 0 < δ) :=
    actual_smoothed_log_bound hdim P hKL ρ' B' D' hB' hD' hgB' hgD' hCI hδ
  have hExact : ∫⁻ p, ENNReal.ofReal (Real.log (1+(selectedExact ρ' (actualObservation p)).toReal))
      ∂actualExperiment (r:=r) P ≤ ENNReal.ofReal R := by
    apply log_lintegral_bound_of_ae_tendsto (actualExperiment (r:=r) P)
      (fun j p => selectedCube ρ' (1/(j:ℝ)) (actualObservation p))
      (fun p => selectedExact ρ' (actualObservation p))
      (fun j => (measurable_selectedCube ρ' (1/(j:ℝ))).comp measurable_actualObservation)
      (fun p => exactDensity_ne_top _ _ _) hlim (ENNReal.ofReal R)
    intro j hj
    exact hsmooth _ (by positivity)
  have hc := log_bound_consequences (actualExperiment (r:=r) P)
    (fun p => selectedExact ρ' (actualObservation p))
    ((measurable_selectedExact ρ').comp measurable_actualObservation) R hR0 hExact
  refine ⟨hKL,hKE,actual_conditional_label_ac hdim P ν hInd H hH hν,hlim,?_,hc.1.1,hc.1.2,?_,hc.2.1,hc.2.2⟩
  · intro δ hδ
    exact (log_bound_consequences (actualExperiment (r:=r) P)
      (fun p => selectedCube ρ' δ (actualObservation p))
      ((measurable_selectedCube ρ' δ).comp measurable_actualObservation) R hR0 (hsmooth δ hδ)).1
  · exact add_le_add (div_le_div_of_nonneg_right hKE (Nat.cast_nonneg q)) le_rfl



end CurrentProjection

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CurrentProjection.actualRowMain_oai.{u_1} := @OAI.CurrentProjection.actualRowMain_oai.{u_1}
