-- Prove2me | solution 1 for OAI.CurrentProjection.critical_refined_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:58:51.995286+00:00
-- url     : https://prove2.me/submissions/eb5138d4-8491-4ebf-8f90-a24de265603d

import Mathlib
import Definitions.Def_GaussianReplacement
import Definitions.Def_OAIQWCP000
import Theorems.Thm_OAI_CurrentProjection_actualRowMain

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

lemma messagePosterior_apply {S W : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [StandardBorelSpace S] [Nonempty S] [MeasurableSingletonClass W]
    (P : Measure (S×W)) [IsFiniteMeasure P] {w : W} (hw : P.snd {w} ≠ 0)
    (s : Set S) (hs : MeasurableSet s) :
    messagePosterior P w s = (P.snd {w})⁻¹ * P (s ×ˢ {w}) := by
  have hfst : (P.map Prod.swap).fst = P.snd := by
    rw [Measure.fst,Measure.snd,Measure.map_map measurable_fst measurable_swap]
    rfl
  rw [messagePosterior,Measure.IsCondKernel.apply_of_ne_zero _ _ (by rwa [hfst]),
    hfst,Measure.map_apply measurable_swap (measurableSet_singleton w |>.prod hs)]
  congr 2
  ext x
  simp [and_comm]

lemma messagePosterior_le {S W : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [StandardBorelSpace S] [Nonempty S] [MeasurableSingletonClass W]
    (P : Measure (S×W)) [IsFiniteMeasure P] {w : W} (hw : P.snd {w} ≠ 0) :
    messagePosterior P w ≤ (P.snd {w})⁻¹ • P.fst := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [messagePosterior_apply P hw s hs,Measure.smul_apply,smul_eq_mul]
  apply mul_le_mul_right
  rw [Measure.fst_apply hs]
  exact measure_mono (by rintro ⟨s,w⟩ h; exact h.1)

lemma messagePosterior_disintegrate {S W : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [StandardBorelSpace S] [Nonempty S]
    (P : Measure (S×W)) [IsFiniteMeasure P] :
    (P.snd ⊗ₘ messagePosterior P).map Prod.swap = P := by
  have hfst : (P.map Prod.swap).fst = P.snd := by
    rw [Measure.fst,Measure.snd,Measure.map_map measurable_fst measurable_swap]
    rfl
  rw [← hfst, messagePosterior,Measure.disintegrate,Measure.map_map measurable_swap measurable_swap]
  exact Measure.map_id

lemma refineSignal_apply {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) (e : S×W → E) (he : Measurable e)
    (w : W) (v : E) (s : Set S) (hs : MeasurableSet s) :
    refineSignal P e (s ×ˢ {(w,v)}) = P ((s ∩ {x | e (x,w) = v}) ×ˢ {w}) := by
  rw [refineSignal,Measure.map_apply (measurable_fst.prodMk (measurable_snd.prodMk he))
    (hs.prod (measurableSet_singleton (w,v)))]
  congr 1
  ext ⟨a,b⟩
  simp only [mem_preimage,mem_prod,mem_singleton_iff,Prod.mk.injEq,mem_inter_iff,mem_ofPred_eq]
  constructor
  · rintro ⟨hs,hx,he⟩
    exact ⟨⟨hs,by simpa [hx] using he⟩,hx⟩
  · rintro ⟨⟨hs,he⟩,hx⟩
    exact ⟨hs,hx,by simpa [hx] using he⟩

lemma refineSignal_mass {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) [IsFiniteMeasure P] (e : S×W → E) (he : Measurable e)
    {w : W} (hw : P.snd {w} ≠ 0) (v : E) :
    (refineSignal P e).snd {(w,v)} = P.snd {w} * messagePosterior P w {x | e (x,w) = v} := by
  have hclass : MeasurableSet {x : S | e (x,w) = v} :=
    (measurableSet_singleton v).preimage (he.comp (measurable_id.prodMk measurable_const))
  rw [messagePosterior_apply P hw _ hclass,←mul_assoc,
    ENNReal.mul_inv_cancel hw (measure_ne_top _ _),one_mul,Measure.snd_apply (measurableSet_singleton (w,v))]
  have heq : (Prod.snd ⁻¹' ({(w,v)} : Set (W×E))) = (univ : Set S) ×ˢ {(w,v)} := by ext x; simp
  rw [heq,refineSignal_apply P e he w v univ MeasurableSet.univ,univ_inter]

lemma refineSignal_positive_original {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) (e : S×W → E) (he : Measurable e)
    {w : W} {v : E} (hv : (refineSignal P e).snd {(w,v)} ≠ 0) : P.snd {w} ≠ 0 := by
  contrapose! hv
  rw [Measure.snd_apply (measurableSet_singleton (w,v)),
    show (Prod.snd ⁻¹' ({(w,v)} : Set (W×E))) = (univ : Set S) ×ˢ {(w,v)} from by ext x; simp,
    refineSignal_apply P e he w v univ MeasurableSet.univ,univ_inter]
  apply measure_mono_null (t:=Prod.snd ⁻¹' {w})
  · intro x hx; exact hx.2
  · rwa [←Measure.snd_apply (measurableSet_singleton w)]

lemma messagePosterior_refinement {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) [IsFiniteMeasure P] (e : S×W → E) (he : Measurable e)
    {w : W} {v : E} (hv : (refineSignal P e).snd {(w,v)} ≠ 0) :
    messagePosterior (refineSignal P e) (w,v) =
      (messagePosterior P w {x | e (x,w) = v})⁻¹ •
        (messagePosterior P w).restrict {x | e (x,w) = v} := by
  have hw := refineSignal_positive_original P e he hv
  have hclass : MeasurableSet {x : S | e (x,w) = v} :=
    (measurableSet_singleton v).preimage (he.comp (measurable_id.prodMk measurable_const))
  have hη : messagePosterior P w {x | e (x,w) = v} ≠ 0 := by
    intro hz
    rw [refineSignal_mass P e he hw v,hz,mul_zero] at hv
    exact hv rfl
  ext s hs
  rw [messagePosterior_apply _ hv s hs,refineSignal_apply P e he w v s hs,
    Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hs,
    messagePosterior_apply P hw _ (hs.inter hclass),refineSignal_mass P e he hw v,
    ENNReal.mul_inv (Or.inl hw) (Or.inl (measure_ne_top _ _)), mul_assoc]
  ac_rfl



lemma countable_ac_of_atom {W : Type*} [MeasurableSpace W] [Countable W]
    [MeasurableSingletonClass W] (P Q : Measure W)
    (h : ∀ w, Q {w} = 0 → P {w} = 0) : P ≪ Q := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  rw [show s = ⋃ w : s, ({w.1} : Set W) by ext x; simp]
  apply measure_iUnion_null
  intro w
  exact h w (measure_mono_null (by simp [w.2]) hz)

lemma rnDeriv_atom {W : Type*} [MeasurableSpace W] [MeasurableSingletonClass W]
    (P Q : Measure W) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P ≪ Q) {w : W} (hw : Q {w} ≠ 0) :
    P.rnDeriv Q w = P {w} / Q {w} := by
  have h := congrArg (fun M : Measure W => M {w}) (Measure.withDensity_rnDeriv_eq P Q hPQ)
  rw [withDensity_apply _ (measurableSet_singleton w),Measure.restrict_singleton,
    lintegral_smul_measure,lintegral_dirac] at h
  change Q {w} * P.rnDeriv Q w = P {w} at h
  apply (ENNReal.eq_div_iff hw (measure_ne_top _ _)).mpr
  simpa only [mul_comm] using h

lemma countable_entropy_le_crossEntropy {W : Type*} [MeasurableSpace W] [Countable W]
    [MeasurableSingletonClass W] (P Q : Measure W) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hci : Integrable (fun w => -Real.log (Q {w}).toReal) P) :
    shannonEntropy P ≠ ∞ ∧ (shannonEntropy P).toReal ≤ ∫ w, -Real.log (Q {w}).toReal ∂P := by
  have hpos : ∀ᵐ w ∂P, Q {w} ≠ 0 := hPQ.ae_le (ae_positive_atom Q)
  have he : ∀ᵐ w ∂P, llr P Q w = Real.log (P {w}).toReal - Real.log (Q {w}).toReal := by
    filter_upwards [ae_positive_atom P,hpos] with w hp hq
    rw [llr,rnDeriv_atom P Q hPQ hq,ENNReal.toReal_div,Real.log_div
      (ENNReal.toReal_ne_zero.mpr ⟨hp,measure_ne_top _ _⟩)
      (ENNReal.toReal_ne_zero.mpr ⟨hq,measure_ne_top _ _⟩)]
  have hbound : ∀ᵐ w ∂P, llr P Q w ≤ -Real.log (Q {w}).toReal := by
    filter_upwards [he] with w hw
    rw [hw]
    linarith [atom_surprisal_nonneg P w]
  have hk := klDiv_bound_of_llr_le P Q hPQ _ hci hbound
  have hli := (klDiv_ne_top_iff.mp hk.1).2
  have hpi : Integrable (fun w => -Real.log (P {w}).toReal) P := by
    apply (hci.sub hli).congr
    filter_upwards [he] with w hw
    change -Real.log (Q {w}).toReal - llr P Q w = -Real.log (P {w}).toReal
    rw [hw]
    ring
  have hent : shannonEntropy P = ENNReal.ofReal (∫ w, -Real.log (P {w}).toReal ∂P) := by
    exact (ofReal_integral_eq_lintegral_ofReal hpi (Eventually.of_forall (atom_surprisal_nonneg P))).symm
  refine ⟨by rw [hent]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hent,ENNReal.toReal_ofReal (integral_nonneg (atom_surprisal_nonneg P))]
  have hn : 0 ≤ ∫ w, llr P Q w ∂P := by simpa using integral_llr_add_sub_measure_univ_nonneg hPQ hli
  have hi : (∫ w, llr P Q w ∂P) = (∫ w, -Real.log (Q {w}).toReal ∂P) -
      ∫ w, -Real.log (P {w}).toReal ∂P := by
    rw [←integral_sub hci hpi]
    apply integral_congr_ae
    filter_upwards [he] with w hw
    linarith
  linarith

lemma shannonEntropy_map_le {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]
    [Countable W] [Countable V] [MeasurableSingletonClass W] [MeasurableSingletonClass V]
    (P : Measure W) [IsProbabilityMeasure P] (f : W → V) :
    shannonEntropy (P.map f) ≤ shannonEntropy P := by
  have hfm : Measurable f := measurable_of_countable _
  let : IsProbabilityMeasure (P.map f) := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  unfold shannonEntropy
  rw [lintegral_map (measurable_of_countable _) hfm]
  apply lintegral_mono_ae
  filter_upwards [ae_positive_atom P] with w hw
  apply ENNReal.ofReal_le_ofReal
  apply neg_le_neg
  apply Real.log_le_log (ENNReal.toReal_pos hw (measure_ne_top _ _))
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  rw [Measure.map_apply hfm (measurableSet_singleton (f w))]
  exact measure_mono (by intro x hx; simpa only [mem_preimage,mem_singleton_iff] using congrArg f hx)

lemma shannonEntropy_equiv {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]
    [Countable W] [Countable V] [MeasurableSingletonClass W] [MeasurableSingletonClass V]
    (P : Measure W) [IsProbabilityMeasure P] (e : W ≃ᵐ V) :
    shannonEntropy (P.map e) = shannonEntropy P := by
  let : IsProbabilityMeasure (P.map e) := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  apply le_antisymm (shannonEntropy_map_le P e)
  simpa only [e.map_symm_map] using shannonEntropy_map_le (P.map e) e.symm

lemma geometric_pair_entropy {P : Measure (ℕ×ℕ)} [IsProbabilityMeasure P]
    (M : ℝ) (hM : 1 ≤ M)
    (hi : Integrable (fun x : ℕ×ℕ => (x.1:ℝ)+(x.2:ℝ)) P)
    (hmean : (∫ x : ℕ×ℕ, (x.1:ℝ)+(x.2:ℝ) ∂P) ≤ M) :
    shannonEntropy P ≠ ∞ ∧ (shannonEntropy P).toReal ≤ 1 + 2 * Real.log (M+1) := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hM1 : 0 < M+1 := by linarith
  let p : unitInterval := ⟨(M+1)⁻¹, ⟨(inv_pos.mpr hM1).le, (inv_le_one₀ hM1).mpr (by linarith)⟩⟩
  have hp0 : p ≠ 0 := by
    intro h
    have hh : (M+1)⁻¹ = 0 := congrArg Subtype.val h
    exact (inv_ne_zero hM1.ne') hh
  have hp1 : p ≠ 1 := by
    intro h
    have hh := congrArg Subtype.val h
    have hlt : (M+1)⁻¹ < 1 := (inv_lt_one₀ hM1).mpr (by linarith)
    exact hlt.ne hh
  have hpR : 0 < (p:ℝ) := inv_pos.mpr hM1
  have hqR : 0 < 1-(p:ℝ) := by
    change 0 < 1-(M+1)⁻¹
    linarith [(inv_lt_one₀ hM1).mpr (by linarith : 1 < M+1)]
  let Q := (geometricMeasure p).prod (geometricMeasure p)
  have hatom (x : ℕ×ℕ) : Q {x} = ENNReal.ofReal (((1-p)^x.1*p) * ((1-p)^x.2*p)) := by
    rw [show ({x} : Set (ℕ×ℕ)) = {x.1} ×ˢ {x.2} by ext y; simp [Prod.ext_iff]]
    rw [Measure.prod_prod,geometricMeasure_singleton hp0,geometricMeasure_singleton hp0,
      ENNReal.ofReal_mul (geometricMeasure_nonneg p x.1)]
  have hpos (x : ℕ×ℕ) : Q {x} ≠ 0 := by
    rw [hatom, ne_eq,ENNReal.ofReal_eq_zero]
    exact (mul_pos (geometricMeasure_pos hp0 hp1 x.1) (geometricMeasure_pos hp0 hp1 x.2)).not_ge
  have hc (x : ℕ×ℕ) : -Real.log (Q {x}).toReal =
      ((x.1:ℝ)+(x.2:ℝ)) * (-Real.log (1-(p:ℝ))) - 2*Real.log (p:ℝ) := by
    rw [hatom,ENNReal.toReal_ofReal (mul_nonneg (geometricMeasure_nonneg p x.1)
      (geometricMeasure_nonneg p x.2)),Real.log_mul
      (geometricMeasure_pos hp0 hp1 x.1).ne' (geometricMeasure_pos hp0 hp1 x.2).ne',
      Real.log_mul (pow_pos hqR _).ne' hpR.ne',
      Real.log_mul (pow_pos hqR _).ne' hpR.ne',Real.log_pow,Real.log_pow]
    ring
  have hci : Integrable (fun x : ℕ×ℕ => -Real.log (Q {x}).toReal) P := by
    simp_rw [hc]
    exact (hi.mul_const _).sub (integrable_const _)
  have he := countable_entropy_le_crossEntropy P Q
    (countable_ac_of_atom P Q (fun x hx => False.elim (hpos x hx))) hci
  refine ⟨he.1,he.2.trans ?_⟩
  simp_rw [hc]
  rw [integral_sub (hi.mul_const _) (integrable_const _),integral_mul_const,integral_const,
    probReal_univ,one_smul]
  have hlp : -Real.log (p:ℝ) = Real.log (M+1) := by simp [p,Real.log_inv]
  have htpos : 0 < 1-(p:ℝ) := by
    change 0 < 1-(M+1)⁻¹
    linarith [(inv_lt_one₀ hM1).mpr (by linarith : 1 < M+1)]
  have hlog : -Real.log (1-(p:ℝ)) ≤ M⁻¹ := by
    have hrat : (1-(p:ℝ))⁻¹ = 1+M⁻¹ := by dsimp [p]; field_simp [hM0.ne',hM1.ne']; ring
    calc
      _ = Real.log ((1-(p:ℝ))⁻¹) := (Real.log_inv _).symm
      _ ≤ (1-(p:ℝ))⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr htpos)
      _ = _ := by rw [hrat]; ring
  have hlog0 : 0 ≤ -Real.log (1-(p:ℝ)) := by
    apply neg_nonneg.mpr (Real.log_nonpos htpos.le _)
    have : 0 ≤ (p:ℝ) := p.2.1
    linarith
  have hb := mul_le_mul_of_nonneg_right hmean hlog0
  have hb' := mul_le_mul_of_nonneg_left hlog hM0.le
  rw [mul_inv_cancel₀ hM0.ne'] at hb'
  linarith

lemma entropy_finite_integrable {W : Type*} [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
    (P : Measure W) [IsProbabilityMeasure P] (h : shannonEntropy P ≠ ∞) :
    Integrable (fun w => -Real.log (P {w}).toReal) P :=
  (lintegral_ofReal_ne_top_iff_integrable (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall (atom_surprisal_nonneg P))).mp h

lemma integral_surprisal {W : Type*} [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
    (P : Measure W) [IsProbabilityMeasure P] :
    (∫ w, -Real.log (P {w}).toReal ∂P) = (shannonEntropy P).toReal :=
  integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (atom_surprisal_nonneg P))
    (measurable_of_countable _).aestronglyMeasurable

lemma shannonEntropy_subadd {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    [Countable W] [Countable E] [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (W×E)) [IsProbabilityMeasure P]
    (hW : shannonEntropy P.fst ≠ ∞) (hE : shannonEntropy P.snd ≠ ∞) :
    shannonEntropy P ≠ ∞ ∧ (shannonEntropy P).toReal ≤
      (shannonEntropy P.fst).toReal + (shannonEntropy P.snd).toReal := by
  have hiW : Integrable (fun z : W×E => -Real.log (P.fst {z.1}).toReal) P :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      measurable_fst.aemeasurable).mp (entropy_finite_integrable P.fst hW)
  have hiE : Integrable (fun z : W×E => -Real.log (P.snd {z.2}).toReal) P :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      measurable_snd.aemeasurable).mp (entropy_finite_integrable P.snd hE)
  have he : ∀ᵐ z ∂P, -Real.log ((P.fst.prod P.snd) {z}).toReal =
      -Real.log (P.fst {z.1}).toReal + -Real.log (P.snd {z.2}).toReal := by
    have hf := (ae_map_iff measurable_fst.aemeasurable
      ((Set.to_countable _).measurableSet)).mp (ae_positive_atom P.fst)
    have hs := (ae_map_iff measurable_snd.aemeasurable
      ((Set.to_countable _).measurableSet)).mp (ae_positive_atom P.snd)
    filter_upwards [hf,hs] with z hzf hzs
    rw [show ({z} : Set (W×E)) = {z.1} ×ˢ {z.2} by ext y; simp [Prod.ext_iff],
      Measure.prod_prod,ENNReal.toReal_mul,Real.log_mul
        (ENNReal.toReal_ne_zero.mpr ⟨hzf,measure_ne_top _ _⟩)
        (ENNReal.toReal_ne_zero.mpr ⟨hzs,measure_ne_top _ _⟩)]
    ring
  have hi : Integrable (fun z : W×E => -Real.log ((P.fst.prod P.snd) {z}).toReal) P :=
    (hiW.add hiE).congr (by filter_upwards [he] with z hz; exact hz.symm)
  obtain ⟨hfin,hineq⟩ := countable_entropy_le_crossEntropy P (P.fst.prod P.snd)
    (joint_ac_prod_marginals P) hi
  refine ⟨hfin,hineq.trans_eq ?_⟩
  rw [integral_congr_ae he,integral_add hiW hiE]
  have h1 : (∫ a : W×E, -Real.log (P.fst {a.1}).toReal ∂P) = (shannonEntropy P.fst).toReal := by
    rw [←integral_surprisal]
    exact (integral_map measurable_fst.aemeasurable (measurable_of_countable
      (fun w => -Real.log (P.fst {w}).toReal)).aestronglyMeasurable).symm
  have h2 : (∫ a : W×E, -Real.log (P.snd {a.2}).toReal ∂P) = (shannonEntropy P.snd).toReal := by
    rw [←integral_surprisal]
    exact (integral_map measurable_snd.aemeasurable (measurable_of_countable
      (fun w => -Real.log (P.snd {w}).toReal)).aestronglyMeasurable).symm
  rw [h1,h2]

lemma intCode_le (q : ℤ) : (Equiv.intEquivNat q : ℝ) ≤ 2 * (q.natAbs:ℝ) := by
  cases q with
  | ofNat n => change ((2*n:ℕ):ℝ) ≤ 2*(n:ℝ); norm_cast
  | negSucc n => change ((2*n+1:ℕ):ℝ) ≤ 2*((n+1:ℕ):ℝ); push_cast; linarith

lemma natInt_entropy {P : Measure (ℕ×ℤ)} [IsProbabilityMeasure P]
    (M : ℝ) (hM : 1 ≤ M)
    (hi : Integrable (fun x : ℕ×ℤ => (x.1:ℝ)+2*(x.2.natAbs:ℝ)) P)
    (hmean : (∫ x : ℕ×ℤ, (x.1:ℝ)+2*(x.2.natAbs:ℝ) ∂P) ≤ M) :
    shannonEntropy P ≠ ∞ ∧ (shannonEntropy P).toReal ≤ 1 + 2 * Real.log (M+1) := by
  let e := natIntEquivNatNat
  let Q := P.map e
  let : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hle (x : ℕ×ℤ) : ((e x).1:ℝ)+((e x).2:ℝ) ≤ (x.1:ℝ)+2*(x.2.natAbs:ℝ) :=
    add_le_add le_rfl (intCode_le x.2)
  have hi' : Integrable (fun x : ℕ×ℤ => ((e x).1:ℝ)+((e x).2:ℝ)) P := by
    apply hi.mono' (measurable_of_countable _).aestronglyMeasurable
    exact Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]; exact hle x)
  have hqi : Integrable (fun x : ℕ×ℕ => (x.1:ℝ)+(x.2:ℝ)) Q :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable e.measurable.aemeasurable).mpr hi'
  have hqm : (∫ x : ℕ×ℕ, (x.1:ℝ)+(x.2:ℝ) ∂Q) ≤ M := by
    rw [integral_map e.measurable.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
    exact (integral_mono_ae hi' hi (Eventually.of_forall hle)).trans hmean
  have h := geometric_pair_entropy M hM hqi hqm
  simpa only [Q,shannonEntropy_equiv P e] using h



lemma log_one_add_nonneg (x : ℝ≥0∞) : 0 ≤ Real.log (1+x.toReal) :=
  Real.log_nonneg (le_add_of_nonneg_right ENNReal.toReal_nonneg)

lemma measurable_log_one_add {A : Type*} [MeasurableSpace A] {f : A → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fun x => Real.log (1+(f x).toReal)) :=
  (measurable_const.add hf.ennreal_toReal).log



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

lemma momentBound_nonneg (C : ℝ) (d : ℕ) {B D : ℝ} (hB : 0 ≤ B) :
    0 ≤ momentBound C d B D := by
  unfold momentBound
  positivity

lemma logPositive_le_log_one_add (x : ℝ≥0∞) : logPositive x ≤ Real.log (1+x.toReal) := by
  apply max_le _ (log_one_add_nonneg x)
  by_cases h : x.toReal = 0
  · simp only [h, Real.log_zero, add_zero, Real.log_one, le_refl]
  · exact Real.log_le_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h)) (le_add_of_nonneg_left zero_le_one)



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.ConditionalInfo
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




lemma kernel_prod_eq_compProd {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (κ : Kernel Z A) (η : Kernel Z B) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    κ ×ₖ η = κ ⊗ₖ η.comap Prod.fst measurable_fst := by
  ext z s hs
  rw [Kernel.prod_apply' _ _ _ hs, Kernel.compProd_apply hs]
  rfl

lemma compProd_prod_assoc {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Z) [SFinite μ] (κ : Kernel Z A) (η : Kernel Z B)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (μ ⊗ₘ (κ ×ₖ η)).map MeasurableEquiv.prodAssoc.symm =
      (μ ⊗ₘ κ) ⊗ₘ η.comap Prod.fst measurable_fst := by
  rw [kernel_prod_eq_compProd, Measure.compProd_assoc]

lemma compProd_prod_swapAssoc {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Z) [SFinite μ] (κ : Kernel Z A) (η : Kernel Z B)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (μ ⊗ₘ (κ ×ₖ η)).map swapAssoc = (μ ⊗ₘ η) ⊗ₘ κ.comap Prod.fst measurable_fst := by
  change (μ ⊗ₘ (κ ×ₖ η)).map (MeasurableEquiv.prodAssoc.symm ∘ Prod.map id Prod.swap) = _
  rw [← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (measurable_id.prodMap measurable_swap), ← Measure.compProd_map measurable_swap,
    Kernel.map_prod_swap, compProd_prod_assoc]

lemma fst_map_swapAssoc_compProd {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Z) [SFinite μ] (κ : Kernel Z (A×B)) [IsSFiniteKernel κ] :
    ((μ ⊗ₘ κ).map swapAssoc).fst = μ ⊗ₘ κ.snd := by
  rw [Kernel.snd_eq]
  rw [Measure.compProd_map measurable_snd]
  rw [Measure.fst, Measure.map_map measurable_fst swapAssoc.measurable]
  rfl



lemma conditionalKL_chain {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [StandardBorelSpace A] [Nonempty A]
    (μ : Measure Z) [IsProbabilityMeasure μ] (κ : Kernel Z (A×B)) [IsMarkovKernel κ]
    (π : Measure B) [IsProbabilityMeasure π] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ Kernel.const Z π)) =
      klDiv (μ ⊗ₘ κ.snd) (μ.prod π) +
      klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
  let R := (μ ⊗ₘ κ).map swapAssoc
  have hR : R.fst = μ ⊗ₘ κ.snd := fst_map_swapAssoc_compProd μ κ
  have hchain := klDiv_compProd_eq_add R.fst (μ.prod π) R.condKernel
    (κ.fst.comap Prod.fst measurable_fst)
  rw [R.disintegrate R.condKernel, hR] at hchain
  have hleft := klDiv_map_equiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ Kernel.const Z π)) swapAssoc
  rw [compProd_prod_swapAssoc, Measure.compProd_const] at hleft
  have hright := klDiv_map_equiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) swapAssoc
  rw [compProd_prod_swapAssoc] at hright
  exact hleft.symm.trans (hchain.trans (congrArg (klDiv (μ ⊗ₘ κ.snd) (μ.prod π) + ·) hright))


lemma fst_map_assoc_compProd {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Z) [SFinite μ] (κ : Kernel Z (A×B)) [IsSFiniteKernel κ] :
    ((μ ⊗ₘ κ).map MeasurableEquiv.prodAssoc.symm).fst = μ ⊗ₘ κ.fst := by
  rw [Kernel.fst_eq, Measure.compProd_map measurable_fst, Measure.fst,
    Measure.map_map measurable_fst MeasurableEquiv.prodAssoc.symm.measurable]
  rfl

lemma mutualInformation_chain {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [StandardBorelSpace A] [StandardBorelSpace B] [Nonempty A] [Nonempty B]
    (P : Measure (Z×(A×B))) [IsProbabilityMeasure P] :
    mutualInformation (P.map MeasurableEquiv.prodAssoc.symm) =
      mutualInformation (P.map (Prod.map id Prod.snd)) + conditionalMutualInformation P := by
  let μ := P.fst
  let κ := P.condKernel
  let Q := P.map MeasurableEquiv.prodAssoc.symm
  let R := P.map (Prod.map id Prod.snd)
  let : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  let : IsProbabilityMeasure R := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hP : μ ⊗ₘ κ = P := P.disintegrate P.condKernel
  have hQ : Q.fst = μ ⊗ₘ κ.fst := by
    change (P.map MeasurableEquiv.prodAssoc.symm).fst = _
    rw [← hP]
    exact fst_map_assoc_compProd μ κ
  have hR : R = μ ⊗ₘ κ.snd := by
    rw [Kernel.snd_eq,Measure.compProd_map measurable_snd,hP]
  have hRf : R.fst = μ := by rw [hR,Measure.fst_compProd]
  have hRs : R.snd = Q.snd := by
    dsimp only [R,Q,Measure.snd]
    rw [Measure.map_map measurable_snd (measurable_id.prodMap measurable_snd),
      Measure.map_map measurable_snd MeasurableEquiv.prodAssoc.symm.measurable]
    rfl
  have hleft := klDiv_map_equiv P (μ ⊗ₘ (κ.fst ×ₖ Kernel.const Z Q.snd)) MeasurableEquiv.prodAssoc.symm
  rw [compProd_prod_assoc] at hleft
  have hconst : (Kernel.const Z Q.snd).comap (Prod.fst : Z×A → Z) measurable_fst =
      Kernel.const (Z×A) Q.snd := by ext x t ht; rfl
  rw [hconst,Measure.compProd_const,← hQ] at hleft
  have hc := conditionalKL_chain μ κ Q.snd
  have hSmall : klDiv (μ ⊗ₘ κ.snd) (μ.prod Q.snd) = mutualInformation R := by
    rw [← hR,← hRf,← hRs]
    rfl
  rw [hP,hSmall] at hc
  have hCM : conditionalMutualInformation P = klDiv P (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
    simp only [conditionalMutualInformation,dite_eq_left (inferInstance : Nonempty (A×B))]
    rfl
  rw [hCM]
  exact hleft.trans hc

lemma measurable_alignedMap {d m r : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (fun p : ((Sphere d×W)×Rows m d)×Rows r d => (p.1.1,Fin.append p.1.2 p.2)) :=
  measurable_fst.fst.prodMk ((measurable_append (E:=Vector d) m r).comp (measurable_fst.snd.prodMk measurable_snd))

lemma measurable_exposedJointMap {d k : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (exposedJointMap (d:=d) (k:=k) (W:=W)) := by
  have hY : Measurable (fun p : (Sphere d×W)×Rows k d => label p.2 (p.1.1:Vector d)) :=
    (measurable_own_label (d:=d) (k:=k)).comp (measurable_snd.prodMk measurable_fst.fst)
  exact (measurable_snd.prodMk hY).prodMk measurable_fst





end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.CriticalGeometry
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

lemma criticalRadius_pos (j : ℕ) : 0 < criticalRadius j := by
  unfold criticalRadius
  positivity

lemma criticalRadius_le_two (j : ℕ) : criticalRadius j ≤ 2 := by
  unfold criticalRadius
  nlinarith [pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) (n:=j)]

lemma criticalRadius_tendsto : Tendsto criticalRadius atTop (𝓝 0) := by
  change Tendsto (fun j => 2 * (1/2:ℝ)^j) atTop (𝓝 0)
  simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul 2

lemma sphere_dist_le_two {d : ℕ} (s t : Sphere d) : dist (s:Vector d) (t:Vector d) ≤ 2 := by
  have hs : ‖(s:Vector d)‖ = 1 := by simp
  have ht : ‖(t:Vector d)‖ = 1 := by simp
  calc
    _ ≤ dist (s:Vector d) 0 + dist (0:Vector d) t := dist_triangle _ _ _
    _ = 2 := by simp only [dist_zero_right,dist_zero_left,hs,ht]; norm_num

lemma ballRatio_zero {d : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (ℓ : ℕ) (s : Sphere d) : ballRatio F ℓ s 0 = (2:ℝ)⁻¹ ^ ℓ := by
  have he : {x : Sphere d | dist (x:Vector d) (s:Vector d) ≤ criticalRadius 0} = univ := by
    ext x
    simp [criticalRadius, sphere_dist_le_two x s]
  unfold ballRatio
  rw [he]
  simp [criticalRadius,one_div]

lemma ballRatio_nonneg {d : ℕ} (F : Measure (Sphere d)) (ℓ : ℕ) (s : Sphere d) (j : ℕ) :
    0 ≤ ballRatio F ℓ s j := div_nonneg ENNReal.toReal_nonneg (pow_pos (criticalRadius_pos j) _).le

lemma ballRatio_le_growth {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsFiniteMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ ≤ n)
    (s : Sphere d) (j : ℕ) : ballRatio F ℓ s j ≤ D * criticalRadius j^(n-ℓ) := by
  have hr := criticalRadius_pos j
  have hb : (F {x | dist (x:Vector d) (s:Vector d) ≤ criticalRadius j}).toReal ≤
      D * criticalRadius j^n := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hD (pow_nonneg hr.le _))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hF s (criticalRadius j) hr)
  apply (div_le_iff₀ (pow_pos hr ℓ)).mpr
  calc
    _ ≤ D * criticalRadius j^n := hb
    _ = _ := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hℓ]

lemma ballRatio_tendsto_zero {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsFiniteMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) :
    Tendsto (ballRatio F ℓ s) atTop (𝓝 0) := by
  have ht : Tendsto (fun j => D * criticalRadius j^(n-ℓ)) atTop (𝓝 0) := by
    simpa [Nat.ne_of_gt (Nat.sub_pos_of_lt hℓ)] using (criticalRadius_tendsto.pow (n-ℓ)).const_mul D
  exact squeeze_zero (ballRatio_nonneg F ℓ s) (ballRatio_le_growth F D hD hF hℓ.le s) ht

lemma exists_max_of_tendsto_zero (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0))
    (h0 : 0 < f 0) : ∃ j, ∀ i, f i ≤ f j := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hf.eventually (gt_mem_nhds h0))
  obtain ⟨j,hj,hmax⟩ := (Finset.range (N+1)).exists_max_image f (by simp)
  refine ⟨j,fun i => ?_⟩
  by_cases hi : i < N+1
  · exact hmax _ (Finset.mem_range.mpr hi)
  · exact (hN i (by omega)).le.trans (hmax 0 (by simp))

lemma ballRatio_has_max {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) :
    ∃ j, ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s j := by
  apply exists_max_of_tendsto_zero _ (ballRatio_tendsto_zero F D hD hF hℓ s)
  rw [ballRatio_zero]
  positivity


lemma criticalIndex_max {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) (i : ℕ) :
    ballRatio F ℓ s i ≤ criticalMass F ℓ s := by
  classical
  have hm := ballRatio_has_max F D hD hF hℓ s
  simp only [criticalMass,criticalIndex,dite_eq_left hm]
  exact Nat.find_spec hm i

lemma criticalMass_pos {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) :
    0 < criticalMass F ℓ s := by
  have hm := criticalIndex_max F D hD hF hℓ s 0
  rw [ballRatio_zero] at hm
  exact lt_of_lt_of_le (by positivity) hm

lemma criticalMass_log_bounds {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 < D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) :
    -(ℓ:ℝ)*Real.log 2 ≤ Real.log (criticalMass F ℓ s) ∧
      Real.log (criticalMass F ℓ s) ≤ Real.log D + (n-ℓ:ℕ)*Real.log 2 := by
  have hp := criticalMass_pos F D hD.le hF hℓ s
  constructor
  · have hm := criticalIndex_max F D hD.le hF hℓ s 0
    rw [ballRatio_zero] at hm
    have h := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)⁻¹^ℓ) hm
    simpa only [Real.log_pow,Real.log_inv,mul_neg,neg_mul] using h
  · have hg := ballRatio_le_growth F D hD.le hF hℓ.le s (criticalIndex F ℓ s)
    have hb : criticalMass F ℓ s ≤ D * 2^(n-ℓ) := hg.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (criticalRadius_pos _).le (criticalRadius_le_two _) _) hD.le)
    simpa only [Real.log_mul hD.ne' (by positivity : (2:ℝ)^(n-ℓ) ≠ 0),Real.log_pow] using Real.log_le_log hp hb

lemma criticalLevel_bounds {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 1 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) :
    -(ℓ:ℝ) ≤ (criticalLevel F ℓ s : ℝ) ∧
      (criticalLevel F ℓ s : ℝ) ≤ Real.log D + n + 1 := by
  obtain ⟨hlo,hup⟩ := criticalMass_log_bounds F D (lt_of_lt_of_le zero_lt_one hD) hF hℓ s
  have hc := Int.le_ceil (Real.log (criticalMass F ℓ s))
  have hc' := Int.ceil_lt_add_one (Real.log (criticalMass F ℓ s))
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hn : ((n-ℓ:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n ℓ
  change -(ℓ:ℝ) ≤ (⌈Real.log (criticalMass F ℓ s)⌉:ℝ) ∧ _
  constructor
  · nlinarith [Nat.cast_nonneg (α:=ℝ) ℓ]
  · change (⌈Real.log (criticalMass F ℓ s)⌉:ℝ) ≤ _
    nlinarith [Nat.cast_nonneg (α:=ℝ) (n-ℓ)]

lemma criticalIndex_bound {d n ℓ : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 1 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (s : Sphere d) :
    (criticalIndex F ℓ s : ℝ) ≤ n + 1 + 2 * Real.log D := by
  have hp := criticalMass_pos F D (by linarith) hF hℓ s
  have hlo := (criticalMass_log_bounds F D (by linarith) hF hℓ s).1
  have hg := ballRatio_le_growth F D (by linarith) hF hℓ.le s (criticalIndex F ℓ s)
  have hu := Real.log_le_log hp hg
  have hd0 : D ≠ 0 := by linarith
  have hj := criticalRadius_pos (criticalIndex F ℓ s)
  rw [Real.log_mul hd0 (pow_ne_zero _ hj.ne'),Real.log_pow] at hu
  have hr : Real.log (criticalRadius (criticalIndex F ℓ s)) =
      (1-(criticalIndex F ℓ s:ℝ))*Real.log 2 := by
    rw [criticalRadius,Real.log_mul (by norm_num) (by positivity),Real.log_pow]
    simp only [one_div, Real.log_inv]
    ring
  rw [hr] at hu
  have hj0 : 0 ≤ (criticalIndex F ℓ s:ℝ) := Nat.cast_nonneg _
  have hn1 : (1:ℝ) ≤ (n-ℓ:ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hℓ)
  have hn : ((n-ℓ:ℕ):ℝ) = n - ℓ := by exact_mod_cast (Nat.cast_sub hℓ.le : ((n-ℓ:ℕ):ℝ) = n-ℓ)
  have hl2lo : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2hi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlD := Real.log_nonneg hD
  have hh : (criticalIndex F ℓ s:ℝ) * ((n-ℓ:ℕ):ℝ) * Real.log 2 ≤ Real.log D + n*Real.log 2 := by
    nlinarith
  have ha : (criticalIndex F ℓ s:ℝ) * Real.log 2 ≤
      (criticalIndex F ℓ s:ℝ) * ((n-ℓ:ℕ):ℝ) * Real.log 2 := by
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
  by_cases hjn : (criticalIndex F ℓ s:ℝ) ≤ n
  · linarith
  · have ht := mul_nonneg (show 0 ≤ (criticalIndex F ℓ s:ℝ)-n by linarith)
      (show 0 ≤ Real.log 2-1/2 by linarith)
    nlinarith


lemma measurableSet_criticalClass {d : ℕ} (F : Measure (Sphere d)) [SFinite F]
    (ℓ j : ℕ) (q : ℤ) : MeasurableSet (criticalClass F ℓ j q) :=
  (measurableSet_eq_fun (measurable_criticalIndex F ℓ) measurable_const).inter
    (measurableSet_eq_fun (measurable_criticalLevel F ℓ) measurable_const)

lemma criticalClass_mass_upper {d n ℓ j : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n)
    {q : ℤ} {s : Sphere d} (hs : s ∈ criticalClass F ℓ j q) (i : ℕ) :
    F {x | dist (x:Vector d) (s:Vector d) ≤ criticalRadius i} ≤
      ENNReal.ofReal (Real.exp q * criticalRadius i^ℓ) := by
  have hp := criticalMass_pos F D hD hF hℓ s
  have hq : Real.log (criticalMass F ℓ s) ≤ q := by
    have hh := Int.le_ceil (Real.log (criticalMass F ℓ s))
    change Real.log (criticalMass F ℓ s) ≤ (criticalLevel F ℓ s:ℝ) at hh
    rwa [hs.2] at hh
  have hb := (criticalIndex_max F D hD hF hℓ s i).trans ((Real.log_le_iff_le_exp hp).mp hq)
  have hb' := (div_le_iff₀ (pow_pos (criticalRadius_pos i) ℓ)).mp hb
  rw [← ENNReal.ofReal_toReal (measure_ne_top F _)]
  exact ENNReal.ofReal_le_ofReal hb'

lemma criticalClass_mass_lower {d n ℓ j : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n)
    {q : ℤ} {s : Sphere d} (hs : s ∈ criticalClass F ℓ j q) :
    ENNReal.ofReal (Real.exp ((q:ℝ)-1) * criticalRadius j^ℓ) ≤
      F {x | dist (x:Vector d) (s:Vector d) ≤ criticalRadius j} := by
  have hp := criticalMass_pos F D hD hF hℓ s
  have hq : (q:ℝ)-1 ≤ Real.log (criticalMass F ℓ s) := by
    have hh := Int.ceil_lt_add_one (Real.log (criticalMass F ℓ s))
    change (criticalLevel F ℓ s:ℝ) < _ at hh
    rw [hs.2] at hh
    linarith
  have hb := (Real.le_log_iff_exp_le hp).mp hq
  unfold criticalMass at hb
  rw [hs.1] at hb
  have hb' := (le_div_iff₀ (pow_pos (criticalRadius_pos j) ℓ)).mp hb
  rw [← ENNReal.ofReal_toReal (measure_ne_top F _)]
  exact ENNReal.ofReal_le_ofReal hb'

lemma exists_criticalRadius {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ j, 2*t ≤ criticalRadius j ∧ criticalRadius j ≤ 4*t := by
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one ht ht1
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  refine ⟨j,?_,?_⟩
  · unfold criticalRadius
    linarith
  · rw [pow_succ] at hlo
    unfold criticalRadius
    linarith


lemma criticalClass_restrict_growth {d n ℓ j : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (q : ℤ) :
    LocalGrowth (F.restrict (criticalClass F ℓ j q)) ℓ ((4:ℝ)^ℓ * Real.exp q) := by
  intro z t ht
  let A := criticalClass F ℓ j q
  let b := {x : Sphere d | dist (x:Vector d) z ≤ t}
  have hB : MeasurableSet b := measurableSet_le (by fun_prop) measurable_const
  by_cases hzero : (F.restrict A) b = 0
  · change (F.restrict A) b ≤ _
    simp [hzero]
  have hm : F (b ∩ A) ≠ 0 := by rwa [Measure.restrict_apply hB] at hzero
  obtain ⟨s,hsb,hsA⟩ := nonempty_of_measure_ne_zero hm
  obtain ⟨i,hiB,hiR⟩ : ∃ i, b ⊆ {x | dist (x:Vector d) (s:Vector d) ≤ criticalRadius i} ∧ criticalRadius i ≤ 4*t := by
    by_cases ht1 : t ≤ 1
    · obtain ⟨i,hlo,hhi⟩ := exists_criticalRadius ht ht1
      refine ⟨i,?_,hhi⟩
      intro x hx
      calc
        dist (x:Vector d) s ≤ dist (x:Vector d) z + dist z (s:Vector d) := dist_triangle _ _ _
        _ ≤ t+t := add_le_add hx (by simpa only [b, Set.mem_ofPred_eq, dist_comm] using hsb)
        _ ≤ criticalRadius i := by linarith
    · refine ⟨0,fun x _ => ?_,?_⟩
      · simpa [criticalRadius] using sphere_dist_le_two x s
      · simp only [criticalRadius,pow_zero,mul_one]
        linarith
  calc
    (F.restrict A) b ≤ F b := (Measure.restrict_le_self : F.restrict A ≤ F) b
    _ ≤ F {x | dist (x:Vector d) (s:Vector d) ≤ criticalRadius i} := measure_mono hiB
    _ ≤ ENNReal.ofReal (Real.exp q * criticalRadius i^ℓ) :=
      criticalClass_mass_upper F D hD hF hℓ hsA i
    _ ≤ ENNReal.ofReal (((4:ℝ)^ℓ * Real.exp q) * t^ℓ) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ Real.exp q * (4*t)^ℓ := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (criticalRadius_pos i).le hiR ℓ) (Real.exp_pos _).le
        _ = _ := by rw [mul_pow]; ring


lemma criticalPosterior_growth {d n ℓ j : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (q : ℤ)
    (hη : 0 < F (criticalClass F ℓ j q)) :
    LocalGrowth (criticalPosterior F ℓ j q) ℓ
      ((4:ℝ)^ℓ * Real.exp q / (F (criticalClass F ℓ j q)).toReal) := by
  have hηt := measure_ne_top F (criticalClass F ℓ j q)
  have hηr : 0 < (F (criticalClass F ℓ j q)).toReal := ENNReal.toReal_pos hη.ne' hηt
  intro z t ht
  change (F (criticalClass F ℓ j q))⁻¹ * (F.restrict (criticalClass F ℓ j q)) _ ≤ _
  apply (mul_le_mul' le_rfl (criticalClass_restrict_growth F D hD hF hℓ q z t ht)).trans_eq
  have hei : (F (criticalClass F ℓ j q))⁻¹ =
      ENNReal.ofReal (((F (criticalClass F ℓ j q)).toReal)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hηr, ENNReal.ofReal_toReal hηt]
  rw [hei, ← ENNReal.ofReal_mul (inv_nonneg.mpr hηr.le)]
  congr 1
  ring



lemma criticalClass_packing {d n ℓ j : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (q : ℤ)
    (s : Finset (Sphere d)) (hs : ∀ x ∈ s, x ∈ criticalClass F ℓ j q)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 2 * criticalRadius j < dist x y) :
    (s.card:ℝ) ≤ Real.exp (1-(q:ℝ)) / criticalRadius j^ℓ := by
  let a := Real.exp ((q:ℝ)-1) * criticalRadius j^ℓ
  have ha : 0 < a := mul_pos (Real.exp_pos _) (pow_pos (criticalRadius_pos j) _)
  let b := fun x : Sphere d => {y : Sphere d | dist (y:Vector d) (x:Vector d) ≤ criticalRadius j}
  have hm (x : Sphere d) : MeasurableSet (b x) := measurableSet_le (by fun_prop) measurable_const
  have hd : (s:Set (Sphere d)).PairwiseDisjoint b := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have hz : dist x y ≤ 2*criticalRadius j := by
      change dist (x:Vector d) (y:Vector d) ≤ 2*criticalRadius j
      calc
        _ ≤ dist (x:Vector d) (z:Vector d) + dist (z:Vector d) (y:Vector d) := dist_triangle _ _ _
        _ ≤ criticalRadius j + criticalRadius j := add_le_add
          (by simpa only [b, Set.mem_ofPred_eq, dist_comm] using hzx) hzy
        _ = _ := by ring
    exact (hsep x hx y hy hxy).not_ge hz
  have hb : (s.card:ℝ≥0∞) * ENNReal.ofReal a ≤ 1 := by
    calc
      _ = ∑ x ∈ s, ENNReal.ofReal a := by simp
      _ ≤ ∑ x ∈ s, F (b x) := Finset.sum_le_sum (fun x hx => criticalClass_mass_lower F D hD hF hℓ (hs x hx))
      _ = F (⋃ x ∈ s, b x) := (measure_biUnion_finset hd (fun x _ => hm x)).symm
      _ ≤ F Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hr : (s.card:ℝ)*a ≤ 1 := by
    have hb' : ((s.card:ℝ≥0∞) * ENNReal.ofReal a).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal (by norm_num : (0:ℝ) ≤ 1) (by simpa using hb)
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal ha.le] using hb'
  have he : 1/a = Real.exp (1-(q:ℝ)) / criticalRadius j^ℓ := by
    dsimp only [a]
    rw [show (1-(q:ℝ)) = -((q:ℝ)-1) by ring, Real.exp_neg]
    field_simp [ne_of_gt (Real.exp_pos ((q:ℝ)-1)),ne_of_gt (pow_pos (criticalRadius_pos j) ℓ)]
  exact ((le_div_iff₀ ha).mpr hr).trans_eq he


lemma criticalClass_cover {d n ℓ j : ℕ} (F : Measure (Sphere d)) [IsProbabilityMeasure F]
    (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D) (hℓ : ℓ < n) (q : ℤ) :
    ∃ s : Finset (Sphere d), (∀ x ∈ s, x ∈ criticalClass F ℓ j q) ∧
      (s.card:ℝ) ≤ Real.exp (1-(q:ℝ)) / criticalRadius j^ℓ ∧
      ∀ x ∈ criticalClass F ℓ j q, ∃ y ∈ s, dist x y ≤ 2*criticalRadius j := by
  let N := ⌊Real.exp (1-(q:ℝ)) / criticalRadius j^ℓ⌋₊
  obtain ⟨s,hs,hsep,hcov⟩ := exists_net_of_finite_packing_bound (criticalClass F ℓ j q)
    (mul_nonneg (by norm_num) (criticalRadius_pos j).le) N
    (fun s hs hsep => Nat.le_floor (criticalClass_packing F D hD hF hℓ q s hs hsep))
  exact ⟨s,hs,criticalClass_packing F D hD hF hℓ q s hs hsep,hcov⟩



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.CriticalEntropy
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


lemma posterior_sphere_growth {d : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] [MeasurableSingletonClass W]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hd : 1 ≤ d) {w : W} (hw : P.snd {w} ≠ 0) :
    LocalGrowth (messagePosterior P w) (d-1) ((P.snd {w}).toReal⁻¹*(3*4^d)) := by
  apply dominatedSphere_growth (messagePosterior P w) (by positivity) _ hd le_rfl
  have h := messagePosterior_le P hw
  rw [hσ] at h
  convert h using 1
  rw [← ENNReal.toReal_inv,ENNReal.ofReal_toReal (by simpa using hw)]

lemma criticalRefinement_size {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] [MeasurableSingletonClass W]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) {p : Sphere d×W} (hp : P.snd {p.2} ≠ 0) :
    ((criticalRefinement P ℓ p).1:ℝ) + 2*((criticalRefinement P ℓ p).2.natAbs:ℝ) ≤
      20*((d:ℝ)+1-Real.log (P.snd {p.2}).toReal) := by
  let D := (P.snd {p.2}).toReal⁻¹*(3*4^d)
  have hd : 1 ≤ d := by omega
  have ha : 0 < (P.snd {p.2}).toReal := ENNReal.toReal_pos hp (measure_ne_top _ _)
  have ha1 : (P.snd {p.2}).toReal ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using (prob_le_one : P.snd {p.2} ≤ 1))
  have hinv : 1 ≤ (P.snd {p.2}).toReal⁻¹ := (one_le_inv₀ ha).mpr ha1
  have h4 : (1:ℝ) ≤ 4^d := one_le_pow₀ (by norm_num)
  have hD : 1 ≤ D := by dsimp only [D]; nlinarith
  have hg := posterior_sphere_growth P hσ hd hp
  have hj := criticalIndex_bound (messagePosterior P p.2) D hD hg hℓ p.1
  obtain ⟨hqlo,hqhi⟩ := criticalLevel_bounds (messagePosterior P p.2) D hD hg hℓ p.1
  have hlog : Real.log D ≤ -Real.log (P.snd {p.2}).toReal + 2 + 3*d := by
    dsimp only [D]
    rw [Real.log_mul (inv_ne_zero ha.ne') (by positivity),Real.log_inv,
      Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),Real.log_pow]
    have h3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
    have h4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
    nlinarith [Nat.cast_nonneg (α:=ℝ) d]
  have hn : ((d-1:ℕ):ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  have hl : (ℓ:ℝ) ≤ d := by exact_mod_cast (hℓ.le.trans (Nat.sub_le d 1))
  have hlog0 : 0 ≤ Real.log D := Real.log_nonneg hD
  have hqabs : |(criticalLevel (messagePosterior P p.2) ℓ p.1:ℝ)| ≤
      Real.log D + (d-1:ℕ) + 1 + ℓ := by
    apply abs_le.mpr
    constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) ℓ,Nat.cast_nonneg (α:=ℝ) (d-1)]
  have habs : ((criticalLevel (messagePosterior P p.2) ℓ p.1).natAbs:ℝ) =
      |(criticalLevel (messagePosterior P p.2) ℓ p.1:ℝ)| := by simp
  change (criticalIndex (messagePosterior P p.2) ℓ p.1:ℝ) +
    2*((criticalLevel (messagePosterior P p.2) ℓ p.1).natAbs:ℝ) ≤ _
  rw [habs]
  nlinarith [atom_surprisal_nonneg P.snd p.2,Nat.cast_nonneg (α:=ℝ) d]

lemma criticalRefinement_entropy {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] [Countable W] [MeasurableSingletonClass W]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) (hH : shannonEntropy P.snd ≠ ∞) :
    shannonEntropy (P.map (criticalRefinement P ℓ)) ≠ ∞ ∧
      (shannonEntropy (P.map (criticalRefinement P ℓ))).toReal ≤
        1 + 2*Real.log (20*((d:ℝ)+1+(shannonEntropy P.snd).toReal)+1) := by
  let E := criticalRefinement P ℓ
  have hE : Measurable E := measurable_criticalRefinement P ℓ
  let c : W → ℝ := fun w => -Real.log (P.snd {w}).toReal
  have hc : Integrable c P.snd := entropy_finite_integrable P.snd hH
  have hcp : Integrable (fun p : Sphere d×W => c p.2) P :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable measurable_snd.aemeasurable).mp hc
  let b : Sphere d×W → ℝ := fun p => 20*((d:ℝ)+1+c p.2)
  have hbi : Integrable b P := ((integrable_const _).add hcp).const_mul 20
  have hle : ∀ᵐ p ∂P, ((E p).1:ℝ)+2*((E p).2.natAbs:ℝ) ≤ b p := by
    have hp := (ae_map_iff measurable_snd.aemeasurable
      ((Set.to_countable _).measurableSet)).mp (ae_positive_atom P.snd)
    filter_upwards [hp] with p hp
    exact criticalRefinement_size P hσ hℓ hp
  have hfi : Integrable (fun p => ((E p).1:ℝ)+2*((E p).2.natAbs:ℝ)) P := by
    apply hbi.mono' (((measurable_of_countable (fun x : ℕ×ℤ => (x.1:ℝ)+2*(x.2.natAbs:ℝ))).comp hE).aestronglyMeasurable)
    filter_upwards [hle] with p hp
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ ((E p).1:ℝ)+2*((E p).2.natAbs:ℝ))] using hp
  let : IsProbabilityMeasure (P.map E) := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hi : Integrable (fun x : ℕ×ℤ => (x.1:ℝ)+2*(x.2.natAbs:ℝ)) (P.map E) :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable hE.aemeasurable).mpr hfi
  have hM : 1 ≤ 20*((d:ℝ)+1+(shannonEntropy P.snd).toReal) := by
    nlinarith [ENNReal.toReal_nonneg (a:=shannonEntropy P.snd), Nat.cast_nonneg (α:=ℝ) d]
  apply natInt_entropy _ hM hi
  rw [integral_map hE.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
  calc
    _ ≤ ∫ p, b p ∂P := integral_mono_ae hfi hbi hle
    _ = _ := by
      dsimp only [b]
      rw [integral_const_mul,integral_add (integrable_const _) hcp,integral_const,probReal_univ,one_smul,
        ←integral_map measurable_snd.aemeasurable (measurable_of_countable c).aestronglyMeasurable]
      rw [←Measure.snd]
      dsimp only [c]
      rw [integral_surprisal]



lemma llr_chain_ae {A : Type*} [MeasurableSpace A]
    (P Q R : Measure A) [SigmaFinite P] [SigmaFinite Q] [SigmaFinite R]
    (hPQ : P ≪ Q) (hQR : Q ≪ R) :
    llr P R =ᵐ[P] fun x => llr P Q x + llr Q R x := by
  filter_upwards [hPQ.ae_le (Measure.rnDeriv_mul_rnDeriv' (μ:=P) hQR),
    Measure.rnDeriv_pos hPQ, hPQ.ae_le (Measure.rnDeriv_ne_top P Q),
    hPQ.ae_le (Measure.rnDeriv_pos hQR), (hPQ.trans hQR).ae_le (Measure.rnDeriv_ne_top Q R)]
    with x he hp hpt hq hqt
  simp only [llr_def,←he,Pi.mul_apply,ENNReal.toReal_mul]
  exact Real.log_mul (ENNReal.toReal_pos hp.ne' hpt).ne' (ENNReal.toReal_pos hq.ne' hqt).ne'



lemma density_log_integrable_and_gibbs {A : Type*} [MeasurableSpace A]
    (P Q Λ : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite Λ]
    (hPQ : P ≪ Q) (hQΛ : Q ≪ Λ)
    (hpos : Integrable (fun x => max (llr P Λ x) 0) P)
    (href : Integrable (llr Q Λ) P) :
    Integrable (llr P Λ) P ∧ (∫ x, llr Q Λ x ∂P) ≤ ∫ x, llr P Λ x ∂P := by
  have he := llr_chain_ae P Q Λ hPQ hQΛ
  have hb : ∀ᵐ x ∂P, llr P Q x ≤ max (llr P Λ x) 0 - llr Q Λ x := by
    filter_upwards [he] with x hx
    linarith [le_max_left (llr P Λ x) 0]
  have hk := klDiv_bound_of_llr_le P Q hPQ _ (hpos.sub href) hb
  have hi := (klDiv_ne_top_iff.mp hk.1).2
  have hpi : Integrable (llr P Λ) P := (hi.add href).congr he.symm
  refine ⟨hpi,?_⟩
  have hn : 0 ≤ ∫ x, llr P Q x ∂P := by
    simpa using integral_llr_add_sub_measure_univ_nonneg hPQ hi
  have heint : (∫ x, llr P Λ x ∂P) = (∫ x, llr P Q x ∂P) + ∫ x, llr Q Λ x ∂P := by
    rw [integral_congr_ae he,integral_add hi href]
  linarith

lemma klDiv_chain_finite {A : Type*} [MeasurableSpace A]
    (P Q R : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (hPQ : klDiv P Q ≠ ∞) (hQR : Q ≪ R) (hi : Integrable (llr Q R) P) :
    klDiv P R ≠ ∞ ∧ (klDiv P R).toReal = (klDiv P Q).toReal + ∫ x, llr Q R x ∂P := by
  obtain ⟨hpq,hpi⟩ := klDiv_ne_top_iff.mp hPQ
  have he := llr_chain_ae P Q R hpq hQR
  have hpr : Integrable (llr P R) P := (hpi.add hi).congr he.symm
  refine ⟨klDiv_ne_top (hpq.trans hQR) hpr,?_⟩
  rw [toReal_klDiv_of_measure_eq (hpq.trans hQR) (by simp),
    toReal_klDiv_of_measure_eq hpq (by simp),integral_congr_ae he,integral_add hpi hi]

lemma density_gibbs_integrable {A : Type*} [MeasurableSpace A]
    (P Q Λ : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite Λ]
    (p : A → ℝ≥0∞) (hp : Measurable p) (hP : Λ.withDensity p = P)
    (g : A → ℝ) (hg : Measurable g) (hgpos : ∀ x, 0 < g x)
    (hQ : Λ.withDensity (fun x => ENNReal.ofReal (g x)) = Q)
    (hpos : Integrable (fun x => max (Real.log (p x).toReal) 0) P)
    (hgi : Integrable (fun x => Real.log (g x)) P) :
    Integrable (fun x => Real.log (p x).toReal) P ∧
      (∫ x, Real.log (g x) ∂P) ≤ ∫ x, Real.log (p x).toReal ∂P := by
  have hPΛ : P ≪ Λ := by rw [←hP]; exact withDensity_absolutelyContinuous _ _
  have hQΛ : Q ≪ Λ := by rw [←hQ]; exact withDensity_absolutelyContinuous _ _
  have hΛQ : Λ ≪ Q := by
    rw [←hQ]
    exact withDensity_absolutelyContinuous' hg.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (hgpos x)).ne'))
  have hpd : P.rnDeriv Λ =ᵐ[P] p := by
    apply hPΛ.ae_le
    rw [←hP]
    exact Measure.rnDeriv_withDensity Λ hp
  have hgd : Q.rnDeriv Λ =ᵐ[P] fun x => ENNReal.ofReal (g x) := by
    apply hPΛ.ae_le
    rw [←hQ]
    exact Measure.rnDeriv_withDensity Λ hg.ennreal_ofReal
  have hpll : llr P Λ =ᵐ[P] fun x => Real.log (p x).toReal := by
    exact hpd.mono (fun x hx => by simp only [llr_def,hx])
  have hgll : llr Q Λ =ᵐ[P] fun x => Real.log (g x) := by
    exact hgd.mono (fun x hx => by simp only [llr_def,hx,ENNReal.toReal_ofReal (hgpos x).le])
  obtain ⟨hi,hb⟩ := density_log_integrable_and_gibbs P Q Λ (hPΛ.trans hΛQ) hQΛ
    (hpos.congr (hpll.symm.fun_comp (fun t : ℝ => max t 0))) (hgi.congr hgll.symm)
  exact ⟨hi.congr hpll,by simpa only [integral_congr_ae hpll,integral_congr_ae hgll] using hb⟩



lemma cross_llr_integrable {A : Type*} [MeasurableSpace A]
    (P Q R : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (hPQ : klDiv P Q ≠ ∞) (hQR : Q ≪ R)
    (u : A → ℝ) (hu : Integrable u P) (hle : ∀ᵐ x ∂P, llr Q R x ≤ u x) :
    Integrable (llr Q R) P ∧ klDiv P R ≠ ∞ := by
  obtain ⟨ha,hi⟩ := klDiv_ne_top_iff.mp hPQ
  have he := llr_chain_ae P Q R ha hQR
  have hb : ∀ᵐ x ∂P, llr P R x ≤ llr P Q x + u x := by
    filter_upwards [he,hle] with x hx hy
    rw [hx]
    exact add_le_add_right hy _
  have hk := klDiv_bound_of_llr_le P R (ha.trans hQR) _ (hi.add hu) hb
  have hint := (klDiv_ne_top_iff.mp hk.1).2
  have hsub : (fun x => llr P R x - llr P Q x) =ᵐ[P] llr Q R := by
    filter_upwards [he] with x hx
    rw [hx]
    ring
  exact ⟨(hint.sub hi).congr hsub,hk.1⟩

lemma llr_of_two_densities {A : Type*} [MeasurableSpace A]
    (Q R Λ : Measure A) [IsProbabilityMeasure Q] [IsProbabilityMeasure R] [SigmaFinite Λ]
    (p : A → ℝ≥0∞) (hp : Measurable p) (hQ : Λ.withDensity p = Q)
    (g : A → ℝ) (hg : Measurable g) (hgpos : ∀ x, 0 < g x)
    (hR : Λ.withDensity (fun x => ENNReal.ofReal (g x)) = R) :
    Q ≪ R ∧ llr Q R =ᵐ[Q] fun x => Real.log (p x).toReal - Real.log (g x) := by
  have hQΛ : Q ≪ Λ := by rw [←hQ]; exact withDensity_absolutelyContinuous _ _
  have hRΛ : R ≪ Λ := by rw [←hR]; exact withDensity_absolutelyContinuous _ _
  have hΛR : Λ ≪ R := by
    rw [←hR]
    exact withDensity_absolutelyContinuous' hg.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (hgpos x)).ne'))
  have hQR := hQΛ.trans hΛR
  refine ⟨hQR,?_⟩
  have hpRN : Q.rnDeriv Λ =ᵐ[Q] p := by
    apply hQΛ.ae_le
    rw [←hQ]
    exact Measure.rnDeriv_withDensity Λ hp
  have hgRN : R.rnDeriv Λ =ᵐ[Q] fun x => ENNReal.ofReal (g x) := by
    apply hQΛ.ae_le
    rw [←hR]
    exact Measure.rnDeriv_withDensity Λ hg.ennreal_ofReal
  filter_upwards [llr_chain_ae Q R Λ hQR hRΛ,hpRN,hgRN] with x hx hpq hgq
  simp only [llr_def,hpq,hgq,ENNReal.toReal_ofReal (hgpos x).le] at hx
  simp only [llr_def]
  linarith



lemma volume_ae_exactDensity_rnDeriv {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) :
    (fun y => exactDensity ρ G y) =ᵐ[volume] (labelLaw ρ G).rnDeriv volume := by
  filter_upwards [volume_ae_cube_limit ρ G,
    Besicovitch.ae_tendsto_rnDeriv (labelLaw ρ G) volume] with y he hy
  have ht := hy.comp tendsto_cube_scale
  have hratio : (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) =ᶠ[atTop]
      (fun j : ℕ => labelLaw ρ G (Metric.closedBall y (1/(j:ℝ))) /
        volume (Metric.closedBall y (1/(j:ℝ)))) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact cubeAverage_eq_ball_ratio ρ G y (by positivity)
  exact tendsto_nhds_unique he (ht.congr' hratio.symm)

lemma labelLaw_withDensity_exact {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) (h : labelLaw ρ G ≪ volume) :
    volume.withDensity (fun y => exactDensity ρ G y) = labelLaw ρ G := by
  rw [withDensity_congr_ae (volume_ae_exactDensity_rnDeriv ρ G)]
  exact Measure.withDensity_rnDeriv_eq _ _ h

lemma map_fiber_withDensity {A S Y : Type*} [MeasurableSpace A] [MeasurableSpace S]
    [MeasurableSpace Y] (μ : Measure A) (ν : Measure S) (L : Measure Y)
    [SFinite μ] [SFinite ν] [SFinite L]
    (f : A×S → Y) (hf : Measurable f) (p : A×Y → ℝ≥0∞) (hp : Measurable p)
    (h : ∀ᵐ a ∂μ, L.withDensity (fun y => p (a,y)) = ν.map (fun s => f (a,s))) :
    (μ.prod L).withDensity p = (μ.prod ν).map (fun z => (z.1,f z)) := by
  apply Measure.ext
  intro t ht
  rw [withDensity_apply _ ht,←lintegral_indicator ht,lintegral_prod _ (hp.indicator ht).aemeasurable,
    Measure.map_apply (measurable_fst.prodMk hf) ht,
    Measure.prod_apply (ht.preimage (measurable_fst.prodMk hf))]
  apply lintegral_congr_ae
  filter_upwards [h] with a ha
  have ht' : MeasurableSet {y : Y | (a,y) ∈ t} := ht.preimage (measurable_const.prodMk measurable_id)
  have hf' : Measurable (fun s : S => f (a,s)) := hf.comp (measurable_const.prodMk measurable_id)
  calc
    _ = L.withDensity (fun y => p (a,y)) {y | (a,y) ∈ t} := by
      rw [withDensity_apply _ ht',←lintegral_indicator ht']
      rfl
    _ = _ := by rw [ha,Measure.map_apply hf' ht']; rfl

lemma projectionJoint_withDensity {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (μ : Measure (Rows k d)) [SFinite μ]
    (h : ∀ᵐ G ∂μ, labelLaw ρ G ≪ volume) :
    (μ.prod volume).withDensity (fun gy => exactDensity ρ gy.1 gy.2) = projectionJoint ρ μ := by
  apply map_fiber_withDensity μ ρ volume _ (measurable_own_label (d:=d) (k:=k)) _
    (measurable_exactDensity ρ)
  exact h.mono (fun G hG => labelLaw_withDensity_exact ρ G hG)



lemma gaussian_inner_sq_integrable {d : ℕ} (v : Vector d) :
    Integrable (fun a : Vector d => ⟪v,a⟫^2) (stdGaussian (Vector d)) := by
  exact (IsGaussian.memLp_dual (stdGaussian (Vector d)) (innerSL ℝ v) 2 (by simp)).integrable_sq

lemma gaussian_inner_sq_integral {d : ℕ} (v : Vector d) :
    (∫ a : Vector d, ⟪v,a⟫^2 ∂stdGaussian (Vector d)) = ‖v‖^2 := by
  have h := variance_dual_stdGaussian (innerSL ℝ v)
  rw [variance_eq_integral (by fun_prop),integral_strongDual_stdGaussian] at h
  simpa using h

lemma projectionSquare_nonneg {k d : ℕ} (G : Rows k d) (v : Vector d) :
    0 ≤ projectionSquare G v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma projectionSquare_integrable {k d : ℕ} (v : Vector d) :
    Integrable (fun G : Rows k d => projectionSquare G v) (gaussianRows k d) := by
  apply integrable_finsetSum
  intro i _
  exact integrable_comp_eval (μ:=fun _ : Fin k => stdGaussian (Vector d)) (i:=i) (gaussian_inner_sq_integrable v)

lemma projectionSquare_integral {k d : ℕ} (v : Vector d) :
    (∫ G : Rows k d, projectionSquare G v ∂gaussianRows k d) = (k:ℝ)*‖v‖^2 := by
  unfold projectionSquare
  rw [integral_finsetSum]
  · simp only [label,gaussianRows,integral_comp_eval (μ:=fun _ : Fin k => stdGaussian (Vector d)) (by fun_prop : AEStronglyMeasurable (fun a : Vector d => ⟪v,a⟫^2) (stdGaussian _)),gaussian_inner_sq_integral,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  · intro i _
    exact integrable_comp_eval (μ:=fun _ : Fin k => stdGaussian (Vector d)) (i:=i) (gaussian_inner_sq_integrable v)

lemma radiusVariance_ne_zero {R : ℝ} (hR : 0 < R) : radiusVariance R ≠ 0 := by
  intro h
  have := congrArg (fun v : ℝ≥0 => (v:ℝ)) h
  exact (sq_pos_of_pos hR).ne' this

lemma gaussianProductPDF_pos {k : ℕ} {R : ℝ} (hR : 0 < R) (c y : Fin k→ℝ) :
    0 < gaussianProductPDF R c y := by
  apply Finset.prod_pos
  intro i _
  exact gaussianPDFReal_pos _ _ _ (radiusVariance_ne_zero hR)

lemma integrable_gaussianProductPDF {k : ℕ} (R : ℝ) (c : Fin k→ℝ) :
    Integrable (gaussianProductPDF R c) volume :=
  Integrable.fintype_prod (fun i => integrable_gaussianPDFReal (c i) _)

lemma integral_gaussianProductPDF {k : ℕ} {R : ℝ} (hR : 0<R) (c : Fin k→ℝ) :
    (∫ y, gaussianProductPDF R c y) = 1 := by
  unfold gaussianProductPDF
  change (∫ y, ∏ i, gaussianPDFReal (c i) (radiusVariance R) (y i) ∂Measure.pi (fun _ : Fin k => (volume : Measure ℝ))) = 1
  rw [integral_fintype_prod_eq_prod]
  simp [integral_gaussianPDFReal_eq_one _ (radiusVariance_ne_zero hR)]

lemma normalizer_pos {R : ℝ} (hR : 0 < R) : 0 < normalizer R := by
  unfold normalizer
  positivity

lemma log_gaussianProductPDF {k : ℕ} {R : ℝ} (hR : 0<R) (c y : Fin k→ℝ) :
    Real.log (gaussianProductPDF R c y) = -(k:ℝ)*Real.log (normalizer R) -
      (∑ i, (y i-c i)^2)/(2*R^2) := by
  unfold gaussianProductPDF
  rw [Real.log_prod (fun i _ => (gaussianPDFReal_pos _ _ _ (radiusVariance_ne_zero hR)).ne')]
  simp only [gaussianPDFReal,show (radiusVariance R : ℝ) = R^2 from rfl]
  change (∑ i, Real.log ((normalizer R)⁻¹ * Real.exp (-(y i-c i)^2/(2*R^2)))) = _
  simp_rw [Real.log_mul (inv_ne_zero (normalizer_pos hR).ne') (Real.exp_pos _).ne',Real.log_inv,Real.log_exp]
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [neg_div,Finset.sum_neg_distrib,←Finset.sum_div]
  ring

lemma log_normalizer_le {R : ℝ} (hR : 0<R) :
    Real.log (normalizer R) ≤ Real.log R + 3 := by
  have he : normalizer R = Real.sqrt (2*Real.pi)*R := by
    rw [normalizer,Real.sqrt_mul (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hR]
  rw [he,Real.log_mul (by positivity) hR.ne']
  have hs : Real.sqrt (2*Real.pi) ≤ 4 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · linarith [Real.pi_lt_four]
  have hl := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt (2*Real.pi) by positivity)
  linarith

lemma coverPDF_pos {k d : ℕ} {C : Finset (Sphere d)} (hC : C.Nonempty)
    {R : ℝ} (hR : 0<R) (G : Rows k d) (y : Fin k→ℝ) : 0 < coverPDF C R G y := by
  apply mul_pos (inv_pos.mpr (by exact_mod_cast hC.card_pos))
  exact Finset.sum_pos (fun c _ => gaussianProductPDF_pos hR _ _) hC

lemma measurable_coverPDF {k d : ℕ} (C : Finset (Sphere d)) (R : ℝ) :
    Measurable (fun gy : Rows k d×(Fin k→ℝ) => coverPDF C R gy.1 gy.2) := by
  have hf (c : Sphere d) : Measurable (fun gy : Rows k d×(Fin k→ℝ) =>
      gaussianProductPDF R (label gy.1 (c:Vector d)) gy.2) := by
    unfold gaussianProductPDF
    apply Finset.measurable_prod
    intro i _
    have h1 : Measurable (fun gy : Rows k d×(Fin k→ℝ) => label gy.1 (c:Vector d) i) :=
      (measurable_pi_apply i).comp ((measurable_fixed_label (k:=k) c).comp measurable_fst)
    have h2 : Measurable (fun gy : Rows k d×(Fin k→ℝ) => gy.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    exact measurable_uncurry_gaussianPDFReal.comp (h1.prodMk (measurable_const.prodMk h2))
  have hsum : Measurable (fun gy : Rows k d×(Fin k→ℝ) =>
      ∑ c ∈ C, gaussianProductPDF R (label gy.1 (c:Vector d)) gy.2) :=
    Finset.measurable_sum C (fun c _ => hf c)
  exact hsum.const_mul _

lemma integral_coverPDF {k d : ℕ} {C : Finset (Sphere d)} (hC : C.Nonempty)
    {R : ℝ} (hR : 0<R) (G : Rows k d) : (∫ y, coverPDF C R G y) = 1 := by
  unfold coverPDF
  rw [integral_const_mul,integral_finsetSum]
  · simp only [integral_gaussianProductPDF hR,Finset.sum_const,nsmul_eq_mul,mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast hC.card_pos.ne')
  · intro c _
    exact integrable_gaussianProductPDF R _

lemma integrable_coverPDF {k d : ℕ} (C : Finset (Sphere d)) (R : ℝ) (G : Rows k d) :
    Integrable (coverPDF C R G) volume :=
  (integrable_finsetSum _ (fun _ _ => integrable_gaussianProductPDF R _)).const_mul _

lemma lintegral_coverPDF {k d : ℕ} {C : Finset (Sphere d)} (hC : C.Nonempty)
    {R : ℝ} (hR : 0<R) (G : Rows k d) : (∫⁻ y, ENNReal.ofReal (coverPDF C R G y)) = 1 := by
  rw [←ofReal_integral_eq_lintegral_ofReal (integrable_coverPDF C R G)
    (ae_of_all _ (fun y => (coverPDF_pos hC hR G y).le)),integral_coverPDF hC hR]
  simp

lemma gaussianProductPDF_le_exp {k : ℕ} {R : ℝ} (hR : 0<R) (c y : Fin k→ℝ) :
    gaussianProductPDF R c y ≤ Real.exp (-(k:ℝ)*Real.log (normalizer R)) := by
  rw [←Real.log_le_iff_le_exp (gaussianProductPDF_pos hR c y),log_gaussianProductPDF hR]
  have hn : 0 ≤ (∑ i, (y i-c i)^2)/(2*R^2) := by positivity
  linarith

lemma log_coverPDF_upper {k d : ℕ} {C : Finset (Sphere d)} (hC : C.Nonempty)
    {R : ℝ} (hR : 0<R) (G : Rows k d) (y : Fin k→ℝ) :
    Real.log (coverPDF C R G y) ≤ -(k:ℝ)*Real.log (normalizer R) := by
  rw [Real.log_le_iff_le_exp (coverPDF_pos hC hR G y)]
  calc
    _ ≤ (C.card:ℝ)⁻¹ * ∑ c ∈ C, Real.exp (-(k:ℝ)*Real.log (normalizer R)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun c _ => gaussianProductPDF_le_exp hR _ _)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hC.card_pos.ne'),one_mul]

lemma neg_log_coverPDF_le {k d : ℕ} {C : Finset (Sphere d)} {c : Sphere d}
    (hc : c ∈ C) {R : ℝ} (hR : 0<R) (G : Rows k d) (s : Sphere d) :
    -Real.log (coverPDF C R G (label G (s:Vector d))) ≤
      Real.log (C.card:ℝ) + (k:ℝ)*Real.log (normalizer R) +
        projectionSquare G ((s:Vector d)-(c:Vector d))/(2*R^2) := by
  have hC : C.Nonempty := ⟨c,hc⟩
  have hcard : 0 < (C.card:ℝ) := by exact_mod_cast hC.card_pos
  have hb : (C.card:ℝ)⁻¹ * gaussianProductPDF R (label G (c:Vector d)) (label G (s:Vector d)) ≤
      coverPDF C R G (label G (s:Vector d)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.single_le_sum (f:=fun x : Sphere d => gaussianProductPDF R (label G (x:Vector d)) (label G (s:Vector d))) (fun x _ => (gaussianProductPDF_pos hR _ _).le) hc
  have hl := Real.log_le_log (mul_pos (inv_pos.mpr hcard) (gaussianProductPDF_pos hR _ _)) hb
  rw [Real.log_mul (inv_ne_zero hcard.ne') (gaussianProductPDF_pos hR _ _).ne',
    Real.log_inv,log_gaussianProductPDF hR] at hl
  have he : (∑ i, (label G (s:Vector d) i - label G (c:Vector d) i)^2) =
      projectionSquare G ((s:Vector d)-(c:Vector d)) := by
    simp only [projectionSquare,label,inner_sub_left]
  rw [he] at hl
  linarith

lemma projectionSquare_joint_integrable {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (c : Sphere d) :
    Integrable (fun z : Rows k d×Sphere d => projectionSquare z.1 ((z.2:Vector d)-(c:Vector d)))
      ((gaussianRows k d).prod ρ) := by
  have hm : Measurable (fun z : Rows k d×Sphere d => projectionSquare z.1 ((z.2:Vector d)-(c:Vector d))) := by
    unfold projectionSquare label
    exact Finset.measurable_sum _ (fun i _ => ((measurable_subtype_coe.comp measurable_snd).sub measurable_const |>.inner ((measurable_pi_apply i).comp measurable_fst) |>.pow_const 2))
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun s => projectionSquare_integrable ((s:Vector d)-(c:Vector d)))
  · have he (s : Sphere d) : (∫ G : Rows k d, ‖projectionSquare G ((s:Vector d)-(c:Vector d))‖ ∂gaussianRows k d) =
        (k:ℝ)*‖(s:Vector d)-(c:Vector d)‖^2 := by
      simp_rw [Real.norm_eq_abs,abs_of_nonneg (projectionSquare_nonneg _ _)]
      exact projectionSquare_integral _
    simp_rw [he]
    apply (integrable_const (4*(k:ℝ))).mono' (by fun_prop)
    apply ae_of_all
    intro s
    have hs : ‖(s:Vector d)-(c:Vector d)‖ ≤ 2 := by
      rw [←dist_eq_norm]
      exact sphere_dist_le_two s c
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hsq : ‖(s:Vector d)-(c:Vector d)‖^2 ≤ 4 := by nlinarith [norm_nonneg ((s:Vector d)-(c:Vector d))]
    nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α:=ℝ) k)]

lemma log_coverPDF_integrable_rows {k d : ℕ} {C : Finset (Sphere d)} (hC : C.Nonempty)
    {R : ℝ} (hR : 0<R) (s : Sphere d) :
    Integrable (fun G : Rows k d => Real.log (coverPDF C R G (label G (s:Vector d)))) (gaussianRows k d) := by
  obtain ⟨c,hc⟩ := hC
  have hm := ((measurable_coverPDF (k:=k) C R).comp (measurable_id.prodMk (measurable_fixed_label s))).log
  apply integrable_of_le_of_le hm.aestronglyMeasurable
    (ae_of_all _ (fun G => neg_le.mp (neg_log_coverPDF_le hc hR G s)))
    (ae_of_all _ (fun G => log_coverPDF_upper ⟨c,hc⟩ hR G _))
  · exact ((integrable_const _).add ((projectionSquare_integrable ((s:Vector d)-(c:Vector d))).div_const _)).neg
  · exact integrable_const _

lemma log_coverPDF_joint_integrable {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    {C : Finset (Sphere d)} (hC : C.Nonempty) {R : ℝ} (hR : 0<R) :
    Integrable (fun z : Rows k d×Sphere d => Real.log (coverPDF C R z.1 (label z.1 (z.2:Vector d))))
      ((gaussianRows k d).prod ρ) := by
  obtain ⟨c,hc⟩ := hC
  have hm := ((measurable_coverPDF (k:=k) C R).comp (measurable_fst.prodMk measurable_own_label)).log
  apply integrable_of_le_of_le hm.aestronglyMeasurable
    (ae_of_all _ (fun z => neg_le.mp (neg_log_coverPDF_le hc hR z.1 z.2)))
    (ae_of_all _ (fun z => log_coverPDF_upper ⟨c,hc⟩ hR z.1 _))
  · exact ((integrable_const _).add ((projectionSquare_joint_integrable ρ c).div_const _)).neg
  · exact integrable_const _

lemma integral_neg_log_coverPDF_rows_le {k d : ℕ} {C : Finset (Sphere d)} {c : Sphere d}
    (hc : c∈C) {R : ℝ} (hR : 0<R) (s : Sphere d) (hs : dist s c ≤ 2*R) :
    (∫ G : Rows k d, -Real.log (coverPDF C R G (label G (s:Vector d))) ∂gaussianRows k d) ≤
      Real.log (C.card:ℝ) + (k:ℝ)*Real.log R + 5*k := by
  have hi := (log_coverPDF_integrable_rows (k:=k) ⟨c,hc⟩ hR s).neg
  have hqi := ((projectionSquare_integrable (k:=k) ((s:Vector d)-(c:Vector d))).div_const (2*R^2))
  calc
    _ ≤ ∫ G : Rows k d, Real.log (C.card:ℝ) + (k:ℝ)*Real.log (normalizer R) +
        projectionSquare G ((s:Vector d)-(c:Vector d))/(2*R^2) ∂gaussianRows k d :=
      integral_mono hi ((integrable_const _).add hqi) (fun G => neg_log_coverPDF_le hc hR G s)
    _ = Real.log (C.card:ℝ) + (k:ℝ)*Real.log (normalizer R) + (k:ℝ)*‖(s:Vector d)-(c:Vector d)‖^2/(2*R^2) := by
      rw [integral_add (integrable_const _) hqi,integral_const,probReal_univ,one_smul,integral_div,projectionSquare_integral]
    _ ≤ _ := by
      have hs' : ‖(s:Vector d)-(c:Vector d)‖ ≤ 2*R := hs
      have hb : (k:ℝ)*‖(s:Vector d)-(c:Vector d)‖^2/(2*R^2) ≤ 2*k := by
        apply (div_le_iff₀ (by positivity)).mpr
        have hn : ‖(s:Vector d)-(c:Vector d)‖^2 ≤ (2*R)^2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hs'
        nlinarith [mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (α:=ℝ) k)]
      nlinarith [mul_le_mul_of_nonneg_left (log_normalizer_le hR) (Nat.cast_nonneg (α:=ℝ) k)]

lemma integral_neg_log_coverPDF_le {k d : ℕ} (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ]
    {C : Finset (Sphere d)} (hC : C.Nonempty) {R : ℝ} (hR : 0<R)
    (hcover : ∀ᵐ s ∂ρ, ∃ c∈C, dist s c ≤ 2*R) :
    (∫ z : Rows k d×Sphere d, -Real.log (coverPDF C R z.1 (label z.1 (z.2:Vector d)))
      ∂(gaussianRows k d).prod ρ) ≤ Real.log (C.card:ℝ) + (k:ℝ)*Real.log R + 5*k := by
  have hi := (log_coverPDF_joint_integrable (k:=k) ρ hC hR).neg
  rw [integral_prod_symm (fun z : Rows k d×Sphere d => -Real.log (coverPDF C R z.1 (label z.1 (z.2:Vector d)))) hi]
  calc
    _ ≤ ∫ _s, Real.log (C.card:ℝ) + (k:ℝ)*Real.log R + 5*k ∂ρ := by
      apply integral_mono_ae hi.integral_prod_right (integrable_const _)
      filter_upwards [hcover] with s hs
      obtain ⟨c,hc,hsc⟩ := hs
      exact integral_neg_log_coverPDF_rows_le hc hR s hsc
    _ = _ := by simp



instance projectionJoint_probability {d k : ℕ} (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ]
    (μ : Measure (Rows k d)) [IsProbabilityMeasure μ] : IsProbabilityMeasure (projectionJoint ρ μ) := by
  unfold projectionJoint
  exact Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)



lemma projection_cover_entropy {d k : ℕ} (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ]
    (hAC : ∀ᵐ G ∂gaussianRows k d, labelLaw ρ G ≪ volume)
    (hpos : Integrable (fun z : Rows k d×Sphere d => logPositive (exactDensity ρ z.1 (label z.1 (z.2:Vector d))))
      ((gaussianRows k d).prod ρ))
    {C : Finset (Sphere d)} (hC : C.Nonempty) {R : ℝ} (hR : 0<R)
    (hcover : ∀ᵐ s ∂ρ, ∃ c∈C, dist s c ≤ 2*R) :
    Integrable (fun z : Rows k d×Sphere d => Real.log (exactDensity ρ z.1 (label z.1 (z.2:Vector d))).toReal)
      ((gaussianRows k d).prod ρ) ∧
    -(∫ z : Rows k d×Sphere d, Real.log (exactDensity ρ z.1 (label z.1 (z.2:Vector d))).toReal
      ∂(gaussianRows k d).prod ρ) ≤ Real.log (C.card:ℝ) + (k:ℝ)*Real.log R + 5*k := by
  let Λ : Measure (Rows k d×(Fin k→ℝ)) := (gaussianRows k d).prod volume
  let p : Rows k d×(Fin k→ℝ) → ℝ≥0∞ := fun z => exactDensity ρ z.1 z.2
  let g : Rows k d×(Fin k→ℝ) → ℝ := fun z => coverPDF C R z.1 z.2
  let Q := Λ.withDensity (fun z => ENNReal.ofReal (g z))
  have hp : Measurable p := measurable_exactDensity ρ
  have hg : Measurable g := measurable_coverPDF C R
  have hgpos : ∀ z, 0 < g z := fun z => coverPDF_pos hC hR z.1 z.2
  let : IsProbabilityMeasure Q := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ]
    rw [lintegral_prod _ hg.ennreal_ofReal.aemeasurable]
    simp only [g,lintegral_coverPDF hC hR,lintegral_const,measure_univ,mul_one]
  have hm : Measurable (fun z : Rows k d×Sphere d => (z.1,label z.1 (z.2:Vector d))) :=
    measurable_fst.prodMk measurable_own_label
  have hpi : Integrable (fun z => max (Real.log (p z).toReal) 0) (projectionJoint ρ (gaussianRows k d)) :=
    (integrable_map_measure (hp.ennreal_toReal.log.max measurable_const).aestronglyMeasurable hm.aemeasurable).mpr hpos
  have hgi : Integrable (fun z => Real.log (g z)) (projectionJoint ρ (gaussianRows k d)) :=
    (integrable_map_measure hg.log.aestronglyMeasurable hm.aemeasurable).mpr (log_coverPDF_joint_integrable ρ hC hR)
  obtain ⟨hlog,hbound⟩ := density_gibbs_integrable (projectionJoint ρ (gaussianRows k d)) Q Λ p hp
    (projectionJoint_withDensity ρ (gaussianRows k d) hAC) g hg hgpos rfl hpi hgi
  have hlog' := (integrable_map_measure hp.ennreal_toReal.log.aestronglyMeasurable hm.aemeasurable).mp hlog
  refine ⟨hlog',?_⟩
  have heP : (∫ z, Real.log (p z).toReal ∂projectionJoint ρ (gaussianRows k d)) =
      ∫ z : Rows k d×Sphere d, Real.log (exactDensity ρ z.1 (label z.1 (z.2:Vector d))).toReal ∂(gaussianRows k d).prod ρ :=
    integral_map hm.aemeasurable hp.ennreal_toReal.log.aestronglyMeasurable
  have heQ : (∫ z, Real.log (g z) ∂projectionJoint ρ (gaussianRows k d)) =
      ∫ z : Rows k d×Sphere d, Real.log (coverPDF C R z.1 (label z.1 (z.2:Vector d))) ∂(gaussianRows k d).prod ρ :=
    integral_map hm.aemeasurable hg.log.aestronglyMeasurable
  rw [heP,heQ] at hbound
  have hb := integral_neg_log_coverPDF_le (k:=k) ρ hC hR hcover
  rw [integral_neg] at hb
  linarith



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Information
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


lemma klDiv_prod_chain {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (P : Measure (A×B)) [IsProbabilityMeasure P]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv P (μ.prod ν) = klDiv P.fst μ + klDiv P (P.fst.prod ν) := by
  have h := klDiv_compProd_eq_add P.fst μ P.condKernel (Kernel.const A ν)
  simpa only [P.disintegrate P.condKernel,Measure.compProd_const] using h

lemma mutualInformation_reference {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (P : Measure (A×B)) [IsProbabilityMeasure P]
    (μ : Measure A) [IsProbabilityMeasure μ] :
    klDiv P (μ.prod P.snd) = klDiv P.fst μ + mutualInformation P :=
  klDiv_prod_chain P μ P.snd

lemma klDiv_map_leftInverse {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P Q : Measure A) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (f : A → B) (g : B → A) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    klDiv (P.map f) (Q.map f) = klDiv P Q := by
  apply le_antisymm (klDiv_map_le P Q hf)
  have h := klDiv_map_le (P.map f) (Q.map f) hg
  have he : g ∘ f = id := funext hgf
  simpa only [Measure.map_map hg hf,he,Measure.map_id] using h

lemma mutualInformation_map_left {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (P : Measure (A×B)) [IsProbabilityMeasure P]
    (f : A → C) (g : C → A) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    mutualInformation (P.map (Prod.map f id)) = mutualInformation P := by
  have hT : Measurable (Prod.map f (id : B → B)) := hf.prodMap measurable_id
  have hfst : (P.map (Prod.map f id)).fst = P.fst.map f := by
    simp only [Measure.fst,Measure.map_map measurable_fst hT,Measure.map_map hf measurable_fst]
    rfl
  have hsnd : (P.map (Prod.map f id)).snd = P.snd := by
    simp only [Measure.snd,Measure.map_map measurable_snd hT]
    rfl
  unfold mutualInformation
  have hRef : (P.fst.prod P.snd).map (Prod.map f id) = (P.fst.map f).prod P.snd := by
    rw [←Measure.map_prod_map _ _ hf measurable_id,Measure.map_id]
  rw [hfst,hsnd,←hRef]
  exact klDiv_map_leftInverse P (P.fst.prod P.snd) (Prod.map f id) (Prod.map g id)
    hT (hg.prodMap measurable_id) (fun x => by ext <;> simp [hgf x.1])

lemma mutualInformation_rows_chain {S W X : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure ((S×W)×X)) [IsProbabilityMeasure P]
    (ν : Measure S) (γ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hInd : (P.map swapLast).fst = ν.prod γ) :
    mutualInformation (P.map swapLast) = mutualInformation P.fst + rowInformation P γ := by
  have hSW : P.fst.fst = ν := by
    have h := congrArg Measure.fst hInd
    rw [Measure.fst_prod] at h
    convert h using 1
    simp only [Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
      Measure.map_map measurable_fst measurable_fst,
      Measure.map_map measurable_fst (measurable_fst.comp swapLast.measurable)]
    rfl
  have hW : (P.map swapLast).snd = P.fst.snd := by
    simp only [Measure.snd,Measure.fst,Measure.map_map measurable_snd swapLast.measurable,
      Measure.map_map measurable_snd measurable_fst]; rfl
  have h := klDiv_prod_chain P (ν.prod P.fst.snd) γ
  unfold mutualInformation rowInformation
  rw [hInd,hW,←map_swapLast_prod,klDiv_map_equiv,h,hSW]

lemma mutualInformation_independent_rows {S W X : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] (P : Measure (S×W)) [IsProbabilityMeasure P]
    (γ : Measure X) [IsProbabilityMeasure γ] :
    mutualInformation ((P.prod γ).map swapLast) = mutualInformation P := by
  have hf : ((P.prod γ).map swapLast).fst = P.fst.prod γ := by
    rw [Measure.fst,Measure.map_map measurable_fst swapLast.measurable]
    change (P.prod γ).map (Prod.map Prod.fst id) = _
    rw [←Measure.map_prod_map P γ measurable_fst measurable_id,Measure.map_id]
    rfl
  have hs : ((P.prod γ).map swapLast).snd = P.snd := by
    rw [Measure.snd,Measure.map_map measurable_snd swapLast.measurable]
    change (P.prod γ).map (Prod.snd ∘ Prod.fst) = _
    rw [←Measure.map_map measurable_snd measurable_fst,←Measure.fst,Measure.fst_prod]
    rfl
  unfold mutualInformation
  rw [hf,hs,←map_swapLast_prod,klDiv_map_equiv]
  have h := klDiv_compProd_left P (P.fst.prod P.snd) (Kernel.const (S×W) γ)
  simpa only [Measure.compProd_const] using h

lemma mutualInformation_reference_comparison {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [StandardBorelSpace W] [Nonempty W]
    (P Q : Measure (Z×W)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (hfst : P.fst = Q.fst) (hsnd : P.snd = Q.snd)
    (hPQ : klDiv P Q ≠ ∞) (hQR : klDiv Q (μ.prod Q.snd) ≠ ∞)
    (hi : Integrable (llr Q (μ.prod Q.snd)) P) :
    mutualInformation P ≠ ∞ ∧ mutualInformation Q ≠ ∞ ∧
      (mutualInformation P).toReal = (mutualInformation Q).toReal + (klDiv P Q).toReal +
        (∫ z, llr Q (μ.prod Q.snd) z ∂P) - (∫ z, llr Q (μ.prod Q.snd) z ∂Q) := by
  obtain ⟨hPR,hchain⟩ := klDiv_chain_finite P Q (μ.prod Q.snd) hPQ
    (klDiv_ne_top_iff.mp hQR).1 hi
  have hP := mutualInformation_reference P μ
  have hQ := mutualInformation_reference Q μ
  rw [hsnd,hfst] at hP
  have hbase : klDiv Q.fst μ ≠ ∞ := by
    exact ne_top_of_le_ne_top hQR (hQ ▸ le_add_right le_rfl)
  have hMP : mutualInformation P ≠ ∞ := by
    exact ne_top_of_le_ne_top hPR (hP ▸ le_add_left le_rfl)
  have hMQ : mutualInformation Q ≠ ∞ := by
    exact ne_top_of_le_ne_top hQR (hQ ▸ le_add_left le_rfl)
  refine ⟨hMP,hMQ,?_⟩
  have hP' := congrArg ENNReal.toReal hP
  have hQ' := congrArg ENNReal.toReal hQ
  rw [ENNReal.toReal_add hbase hMP] at hP'
  rw [ENNReal.toReal_add hbase hMQ] at hQ'
  have hQR' : (klDiv Q (μ.prod Q.snd)).toReal = ∫ z, llr Q (μ.prod Q.snd) z ∂Q := by
    exact toReal_klDiv_of_measure_eq (klDiv_ne_top_iff.mp hQR).1 (by simp)
  rw [hQR'] at hQ'
  linarith





lemma density_mutualInformation_comparison {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [StandardBorelSpace W] [Nonempty W]
    (P Q : Measure (Z×W)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Λ : Measure Z) [SigmaFinite Λ] (g : Z → ℝ) (hg : Measurable g) (hgpos : ∀ z, 0<g z)
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (hμ : Λ.withDensity (fun z => ENNReal.ofReal (g z)) = μ)
    (p : Z×W → ℝ≥0∞) (hp : Measurable p)
    (hQ : (Λ.prod Q.snd).withDensity p = Q)
    (hfst : P.fst = Q.fst) (hsnd : P.snd = Q.snd) (hPQ : klDiv P Q ≠ ∞)
    (hpP : Integrable (fun z => logPositive (p z)) P)
    (hpQ : Integrable (fun z => logPositive (p z)) Q)
    (hgQ : Integrable (fun z => Real.log (g z)) Q.fst) :
    Integrable (fun z => Real.log (p z).toReal) P ∧
    Integrable (fun z => Real.log (p z).toReal) Q ∧
    mutualInformation P ≠ ∞ ∧ mutualInformation Q ≠ ∞ ∧
    (mutualInformation P).toReal = (mutualInformation Q).toReal + (klDiv P Q).toReal +
      (∫ z, Real.log (p z).toReal ∂P) - (∫ z, Real.log (p z).toReal ∂Q) := by
  let R := μ.prod Q.snd
  have hR : (Λ.prod Q.snd).withDensity (fun z => ENNReal.ofReal (g z.1)) = R := by
    rw [←prod_withDensity_left hg.ennreal_ofReal,hμ]
  obtain ⟨hQR,he⟩ := llr_of_two_densities Q R (Λ.prod Q.snd) p hp hQ
    (fun z => g z.1) (hg.comp measurable_fst) (fun z => hgpos z.1) hR
  have hPQac := (klDiv_ne_top_iff.mp hPQ).1
  have heP := hPQac.ae_le he
  have hgiQ : Integrable (fun z : Z×W => Real.log (g z.1)) Q :=
    (integrable_map_measure hg.log.aestronglyMeasurable measurable_fst.aemeasurable).mp hgQ
  have hgiP : Integrable (fun z : Z×W => Real.log (g z.1)) P :=
    (integrable_map_measure hg.log.aestronglyMeasurable measurable_fst.aemeasurable).mp (by change Integrable _ P.fst; rw [hfst]; exact hgQ)
  have huP : Integrable (fun z => logPositive (p z) - Real.log (g z.1)) P := hpP.sub hgiP
  have huQ : Integrable (fun z => logPositive (p z) - Real.log (g z.1)) Q := hpQ.sub hgiQ
  have hleP : ∀ᵐ z ∂P, llr Q R z ≤ logPositive (p z) - Real.log (g z.1) := by
    filter_upwards [heP] with z hz
    rw [hz]
    exact sub_le_sub_right (le_max_left _ _) _
  have hleQ : ∀ᵐ z ∂Q, llr Q R z ≤ logPositive (p z) - Real.log (g z.1) := by
    filter_upwards [he] with z hz
    rw [hz]
    exact sub_le_sub_right (le_max_left _ _) _
  obtain ⟨hcP,_⟩ := cross_llr_integrable P Q R hPQ hQR _ huP hleP
  obtain ⟨hcQ,hQRfinite⟩ := cross_llr_integrable Q Q R (by simp) hQR _ huQ hleQ
  have hpPi : Integrable (fun z => Real.log (p z).toReal) P := by
    apply (hcP.add hgiP).congr
    filter_upwards [heP] with z hz
    simp only [Pi.add_apply,hz]
    ring
  have hpQi : Integrable (fun z => Real.log (p z).toReal) Q := by
    apply (hcQ.add hgiQ).congr
    filter_upwards [he] with z hz
    simp only [Pi.add_apply,hz]
    ring
  obtain ⟨hMP,hMQ,hinfo⟩ := mutualInformation_reference_comparison P Q μ hfst hsnd hPQ hQRfinite hcP
  refine ⟨hpPi,hpQi,hMP,hMQ,?_⟩
  have hgint : (∫ z : Z×W, Real.log (g z.1) ∂P) = ∫ z : Z×W, Real.log (g z.1) ∂Q := by
    rw [←integral_map measurable_fst.aemeasurable hg.log.aestronglyMeasurable,
      ←integral_map measurable_fst.aemeasurable hg.log.aestronglyMeasurable]
    change (∫ z, Real.log (g z) ∂P.fst) = ∫ z, Real.log (g z) ∂Q.fst
    rw [hfst]
  change _ = _ + _ + (∫ z, llr Q R z ∂P) - (∫ z, llr Q R z ∂Q) at hinfo
  rw [integral_congr_ae heP,integral_congr_ae he,
    integral_sub hpPi hgiP,integral_sub hpQi hgiQ,hgint] at hinfo
  linarith



lemma measurable_observedMessageMap {d k : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (observedMessageMap (d:=d) (k:=k) (W:=W)) :=
  ((measurable_exposedJointMap (d:=d) (k:=k) (W:=W)).fst).prodMk measurable_fst.snd

instance observedMessage_probability {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (observedMessage P) := by
  unfold observedMessage
  exact Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)

lemma observedMessage_snd {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : (observedMessage P).snd = P.fst.snd := by
  simp only [observedMessage,Measure.snd,Measure.fst,
    Measure.map_map measurable_snd measurable_observedMessageMap,
    Measure.map_map measurable_snd measurable_fst]
  rfl

lemma exposedInformation_chain {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [StandardBorelSpace W] [Nonempty W] [Nonempty (Sphere d)]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    mutualInformation (P.map swapLast) = mutualInformation (observedMessage P) + exposedInformation P := by
  let f : Sphere d×Rows k d → (Rows k d×(Fin k→ℝ))×Sphere d :=
    fun z => ((z.2,label z.2 (z.1:Vector d)),z.1)
  let g : ((Rows k d×(Fin k→ℝ))×Sphere d) → Sphere d×Rows k d := fun z => (z.2,z.1.1)
  have hf : Measurable f := by
    have hy : Measurable (fun z : Sphere d×Rows k d => label z.2 (z.1:Vector d)) :=
      measurable_own_label.comp measurable_swap
    exact (measurable_snd.prodMk hy).prodMk measurable_fst
  have hg : Measurable g := measurable_snd.prodMk measurable_fst.fst
  let R := P.map exposedJointMap
  let : IsProbabilityMeasure R := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  let : IsProbabilityMeasure (P.map (swapLast : (Sphere d×W)×Rows k d ≃ᵐ _)) :=
    Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hleft : R.map MeasurableEquiv.prodAssoc.symm = (P.map swapLast).map (Prod.map f id) := by
    rw [Measure.map_map (hf.prodMap measurable_id) swapLast.measurable]
    dsimp only [R]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable measurable_exposedJointMap]
    rfl
  have hright : R.map (Prod.map id Prod.snd) = observedMessage P := by
    dsimp only [R,observedMessage]
    rw [Measure.map_map (measurable_id.prodMap measurable_snd) measurable_exposedJointMap]
    rfl
  have h := mutualInformation_chain R
  rw [hleft,mutualInformation_map_left _ f g hf hg (fun _ => rfl),hright] at h
  exact h

lemma observedMessage_fst_of_independence {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) (γ : Measure (Rows k d))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hInd : (P.map swapLast).fst = ν.prod γ) :
    (observedMessage P).fst = projectionJoint ν γ := by
  have hbase : P.map (fun p : (Sphere d×W)×Rows k d => (p.2,p.1.1)) = γ.prod ν := by
    have h := congrArg (fun μ : Measure (Sphere d×Rows k d) => μ.map Prod.swap) hInd
    rw [Measure.prod_swap,Measure.fst,Measure.map_map measurable_swap measurable_fst,
      Measure.map_map (measurable_swap.comp measurable_fst) swapLast.measurable] at h
    exact h
  rw [projectionJoint,←hbase,
    Measure.map_map (measurable_fst.prodMk measurable_own_label) (measurable_snd.prodMk measurable_fst.fst)]
  rw [observedMessage,Measure.fst,Measure.map_map measurable_fst measurable_observedMessageMap]
  rfl




lemma prod_posterior_map {S W G Z : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace G] [MeasurableSpace Z] [StandardBorelSpace S] [Nonempty S]
    (P : Measure (S×W)) [IsProbabilityMeasure P] (γ : Measure G) [IsProbabilityMeasure γ]
    (f : S×G → Z) (hf : Measurable f) :
    (P.prod γ).map (fun p => (f (p.1.1,p.2),p.1.2)) =
      (P.snd ⊗ₘ ((messagePosterior P ×ₖ Kernel.const W γ).map f)).map Prod.swap := by
  let κ := messagePosterior P
  have hpost : P.snd ⊗ₘ κ = P.map Prod.swap := by
    have h := congrArg (fun μ : Measure (S×W) => μ.map Prod.swap) (messagePosterior_disintegrate P)
    rw [Measure.map_map measurable_swap measurable_swap] at h
    simpa only [show (Prod.swap ∘ Prod.swap : W×S → W×S) = id from rfl,Measure.map_id] using h
  have hbase : (P.snd ⊗ₘ (κ ×ₖ Kernel.const W γ)).map MeasurableEquiv.prodAssoc.symm =
      (P.map Prod.swap).prod γ := by
    rw [compProd_prod_assoc,hpost]
    have hc : (Kernel.const W γ).comap (Prod.fst : W×S → W) measurable_fst =
        Kernel.const (W×S) γ := by ext x t ht; rfl
    rw [hc,Measure.compProd_const]
  have hbase' : P.snd ⊗ₘ (κ ×ₖ Kernel.const W γ) =
      ((P.map Prod.swap).prod γ).map MeasurableEquiv.prodAssoc := by
    rw [←hbase,MeasurableEquiv.map_map_symm]
  rw [Measure.compProd_map hf]
  change _ = ((P.snd ⊗ₘ (κ ×ₖ Kernel.const W γ)).map (Prod.map id f)).map Prod.swap
  rw [hbase',Measure.map_map (measurable_id.prodMap hf) MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map measurable_swap ((measurable_id.prodMap hf).comp MeasurableEquiv.prodAssoc.measurable)]
  have hp : (P.map Prod.swap).prod γ = (P.prod γ).map (Prod.map Prod.swap id) := by
    rw [←Measure.map_prod_map _ _ measurable_swap measurable_id,Measure.map_id]
  rw [hp,Measure.map_map (measurable_swap.comp ((measurable_id.prodMap hf).comp MeasurableEquiv.prodAssoc.measurable))
    (measurable_swap.prodMap measurable_id)]
  rfl

lemma swapped_compProd_withDensity {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (π : Measure W) (Λ : Measure Z) [SFinite π] [SFinite Λ]
    (κ : Kernel W Z) [IsSFiniteKernel κ] (p : Z×W → ℝ≥0∞) (hp : Measurable p)
    (h : ∀ᵐ w ∂π, Λ.withDensity (fun z => p (z,w)) = κ w) :
    (Λ.prod π).withDensity p = (π ⊗ₘ κ).map Prod.swap := by
  apply Measure.ext
  intro t ht
  rw [withDensity_apply _ ht,←lintegral_indicator ht,
    lintegral_prod_symm _ (hp.indicator ht).aemeasurable,
    Measure.map_apply measurable_swap ht,Measure.compProd_apply (ht.preimage measurable_swap)]
  apply lintegral_congr_ae
  filter_upwards [h] with w hw
  change _ = κ w ((fun z : Z => (z,w)) ⁻¹' t)
  have ht' : MeasurableSet ((fun z : Z => (z,w)) ⁻¹' t) :=
    ht.preimage (measurable_id.prodMk measurable_const)
  rw [←hw,withDensity_apply _ ht',←lintegral_indicator ht']
  rfl

lemma measurable_posteriorProjectionMap {d k : ℕ} :
    Measurable (fun z : Sphere d×Rows k d => (z.2,label z.2 (z.1:Vector d))) :=
  measurable_snd.prodMk (measurable_own_label.comp measurable_swap)

instance posteriorProjectionKernel_markov {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] (P : Measure (Sphere d×W)) [IsFiniteMeasure P]
    (γ : Measure (Rows k d)) [IsProbabilityMeasure γ] : IsMarkovKernel (posteriorProjectionKernel P γ) :=
  Kernel.IsMarkovKernel.map _ measurable_posteriorProjectionMap

lemma posteriorProjectionKernel_apply {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] (P : Measure (Sphere d×W)) [IsFiniteMeasure P]
    (γ : Measure (Rows k d)) [SFinite γ] (w : W) :
    posteriorProjectionKernel P γ w = projectionJoint (messagePosterior P w) γ := by
  rw [posteriorProjectionKernel,Kernel.map_apply _ measurable_posteriorProjectionMap,
    Kernel.prod_apply,Kernel.const_apply,projectionJoint,←Measure.prod_swap]
  rw [Measure.map_map measurable_posteriorProjectionMap measurable_swap]
  rfl

lemma observedMessage_independent_disintegrate {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] (P : Measure (Sphere d×W)) [IsProbabilityMeasure P]
    (γ : Measure (Rows k d)) [IsProbabilityMeasure γ] :
    observedMessage (P.prod γ) = (P.snd ⊗ₘ posteriorProjectionKernel P γ).map Prod.swap :=
  prod_posterior_map P γ _ measurable_posteriorProjectionMap

lemma observedMessage_independent_density {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P]
    (γ : Measure (Rows k d)) [IsProbabilityMeasure γ]
    (hAC : ∀ᵐ w ∂P.snd, ∀ᵐ G ∂γ, labelLaw (messagePosterior P w) G ≪ volume) :
    ((γ.prod (volume : Measure (Fin k→ℝ))).prod P.snd).withDensity
      (fun z => exactDensity (messagePosterior P z.2) z.1.1 z.1.2) =
        observedMessage (P.prod γ) := by
  rw [observedMessage_independent_disintegrate]
  apply swapped_compProd_withDensity
  · exact measurable_from_prod_countable_left (fun w => measurable_exactDensity (messagePosterior P w))
  · filter_upwards [hAC] with w hw
    rw [posteriorProjectionKernel_apply]
    exact projectionJoint_withDensity (messagePosterior P w) γ hw



lemma criticalPosterior_probability {d ℓ j : ℕ} (F : Measure (Sphere d))
    [IsProbabilityMeasure F] (q : ℤ) (hη : 0 < F (criticalClass F ℓ j q)) :
    IsProbabilityMeasure (criticalPosterior F ℓ j q) := by
  constructor
  change (F (criticalClass F ℓ j q))⁻¹ * (F.restrict (criticalClass F ℓ j q)) Set.univ = 1
  simp only [Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hη.ne' (measure_ne_top F _)

lemma criticalPosterior_ae_class {d ℓ j : ℕ} (F : Measure (Sphere d))
    [IsFiniteMeasure F] (q : ℤ) :
    ∀ᵐ s ∂criticalPosterior F ℓ j q, s ∈ criticalClass F ℓ j q := by
  exact (Measure.smul_absolutelyContinuous).ae_le (ae_restrict_mem (measurableSet_criticalClass F ℓ j q))

lemma criticalPosterior_cover_entropy {d n ℓ j : ℕ} (F : Measure (Sphere d))
    [IsProbabilityMeasure F] (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D)
    (hℓ : ℓ < n) (q : ℤ) (hη : 0 < F (criticalClass F ℓ j q))
    (hAC : ∀ᵐ G ∂gaussianRows ℓ d, labelLaw (criticalPosterior F ℓ j q) G ≪ volume)
    (hpos : Integrable (fun z : Rows ℓ d×Sphere d =>
      logPositive (exactDensity (criticalPosterior F ℓ j q) z.1 (label z.1 (z.2:Vector d))))
      ((gaussianRows ℓ d).prod (criticalPosterior F ℓ j q))) :
    Integrable (fun z : Rows ℓ d×Sphere d =>
      Real.log (exactDensity (criticalPosterior F ℓ j q) z.1 (label z.1 (z.2:Vector d))).toReal)
      ((gaussianRows ℓ d).prod (criticalPosterior F ℓ j q)) ∧
    -(∫ z : Rows ℓ d×Sphere d,
      Real.log (exactDensity (criticalPosterior F ℓ j q) z.1 (label z.1 (z.2:Vector d))).toReal
      ∂(gaussianRows ℓ d).prod (criticalPosterior F ℓ j q)) ≤ 1 + 5*(ℓ:ℝ) - q := by
  let := criticalPosterior_probability F q hη
  obtain ⟨C,hsub,hcard,hcover⟩ := criticalClass_cover F D hD hF hℓ q
  have hC : C.Nonempty := by
    obtain ⟨x,hx⟩ := nonempty_of_measure_ne_zero hη.ne'
    obtain ⟨y,hy,_⟩ := hcover x hx
    exact ⟨y,hy⟩
  have hc : ∀ᵐ s ∂criticalPosterior F ℓ j q, ∃ c∈C, dist s c ≤ 2*criticalRadius j :=
    (criticalPosterior_ae_class F q).mono (fun s hs => hcover s hs)
  obtain ⟨hi,hb⟩ := projection_cover_entropy (criticalPosterior F ℓ j q) hAC hpos hC
    (criticalRadius_pos j) hc
  refine ⟨hi,hb.trans ?_⟩
  have hl := Real.log_le_log (show (0:ℝ) < C.card by exact_mod_cast hC.card_pos) hcard
  rw [Real.log_div (Real.exp_pos _).ne' (pow_pos (criticalRadius_pos j) _).ne',
    Real.log_exp,Real.log_pow] at hl
  linarith



lemma projection_positive_reference {d k : ℕ} [Nonempty (Sphere d)]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν] :
    ∃ g : Rows k d×(Fin k→ℝ) → ℝ, Measurable g ∧ (∀ z, 0<g z) ∧
      IsProbabilityMeasure (((gaussianRows k d).prod (volume : Measure (Fin k→ℝ))).withDensity
        (fun z => ENNReal.ofReal (g z))) ∧
      Integrable (fun z => Real.log (g z)) (projectionJoint ν (gaussianRows k d)) := by
  classical
  let c : Sphere d := Classical.choice inferInstance
  let C : Finset (Sphere d) := {c}
  have hC : C.Nonempty := Finset.singleton_nonempty _
  let g : Rows k d×(Fin k→ℝ) → ℝ := fun z => coverPDF C 1 z.1 z.2
  have hg : Measurable g := measurable_coverPDF C 1
  refine ⟨g,hg,fun z => coverPDF_pos hC (by norm_num) z.1 z.2,?_,?_⟩
  · constructor
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      lintegral_prod _ hg.ennreal_ofReal.aemeasurable]
    simp only [g,lintegral_coverPDF hC (by norm_num : (0:ℝ)<1),lintegral_const,measure_univ,mul_one]
  · exact (integrable_map_measure hg.log.aestronglyMeasurable
      (measurable_fst.prodMk measurable_own_label).aemeasurable).mpr
        (log_coverPDF_joint_integrable ν hC (by norm_num))

lemma independent_rows_signal {S W G : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace G] (P : Measure (S×W)) [IsProbabilityMeasure P]
    (γ : Measure G) [IsProbabilityMeasure γ] :
    ((P.prod γ).map swapLast).fst = P.fst.prod γ := by
  rw [Measure.fst,Measure.map_map measurable_fst swapLast.measurable]
  change (P.prod γ).map (Prod.map Prod.fst id) = _
  rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
  rfl

lemma swapLast_snd {S W G : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace G] (P : Measure ((S×W)×G)) : (P.map swapLast).snd = P.fst.snd := by
  rw [Measure.snd,Measure.fst,Measure.snd,Measure.map_map measurable_snd swapLast.measurable,
    Measure.map_map measurable_snd measurable_fst]
  rfl



lemma exposedInformation_density_comparison {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty W] [Nonempty (Sphere d)]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows k d))
    (hH : shannonEntropy P.fst.snd ≠ ∞)
    (hAC : ∀ᵐ w ∂P.fst.snd, ∀ᵐ G ∂gaussianRows k d, labelLaw (messagePosterior P.fst w) G ≪ volume)
    (hpP : Integrable (fun z => logPositive (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2))
      (observedMessage P))
    (hpQ : Integrable (fun z => logPositive (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2))
      (observedMessage (P.fst.prod (gaussianRows k d)))) :
    Integrable (fun z => Real.log (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2).toReal)
      (observedMessage P) ∧
    Integrable (fun z => Real.log (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2).toReal)
      (observedMessage (P.fst.prod (gaussianRows k d))) ∧
    exposedInformation P ≠ ∞ ∧ exposedInformation (P.fst.prod (gaussianRows k d)) ≠ ∞ ∧
    (exposedInformation (P.fst.prod (gaussianRows k d))).toReal ≤ (exposedInformation P).toReal +
      (∫ z, Real.log (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2).toReal ∂observedMessage P) -
      (∫ z, Real.log (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2).toReal
        ∂observedMessage (P.fst.prod (gaussianRows k d))) := by
  let : IsProbabilityMeasure (P.map (swapLast : (Sphere d×W)×Rows k d ≃ᵐ _)) :=
    Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  let γ := gaussianRows k d
  let Q := P.fst.prod γ
  let O := observedMessage P
  let R := observedMessage Q
  have hs : P.fst.fst = ν := by
    have hh := congrArg Measure.fst hInd
    rw [Measure.fst_prod] at hh
    convert hh using 1
    simp only [Measure.fst,Measure.map_map measurable_fst measurable_fst,
      Measure.map_map measurable_fst swapLast.measurable,
      Measure.map_map measurable_fst (measurable_fst.comp swapLast.measurable)]
    rfl
  have hQI : (Q.map swapLast).fst = ν.prod γ := by rw [independent_rows_signal,hs]
  have hOf : O.fst = projectionJoint ν γ := observedMessage_fst_of_independence P ν γ hInd
  have hRf : R.fst = projectionJoint ν γ := observedMessage_fst_of_independence Q ν γ hQI
  have hfs : O.fst = R.fst := hOf.trans hRf.symm
  have hss : O.snd = R.snd := by simp only [O,R,Q,observedMessage_snd,Measure.fst_prod]
  obtain ⟨hk,_⟩ := rowInformation_le_entropy P ν γ hInd (by simpa only [swapLast_snd] using hH)
  have hDPI : klDiv O R ≤ rowInformation P γ := klDiv_map_le P Q measurable_observedMessageMap
  have hOR : klDiv O R ≠ ∞ := ne_top_of_le_ne_top hk hDPI
  let p : (Rows k d×(Fin k→ℝ))×W → ℝ≥0∞ :=
    fun z => exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2
  have hp : Measurable p := measurable_from_prod_countable_left (fun w => measurable_exactDensity (messagePosterior P.fst w))
  have hdens : ((γ.prod (volume : Measure (Fin k→ℝ))).prod R.snd).withDensity p = R := by
    dsimp only [R,Q]
    rw [observedMessage_snd,Measure.fst_prod]
    exact observedMessage_independent_density P.fst γ hAC
  obtain ⟨g,hg,hgp,hprob,hgi⟩ := projection_positive_reference (k:=k) ν
  let μ := (γ.prod (volume : Measure (Fin k→ℝ))).withDensity (fun z => ENNReal.ofReal (g z))
  let : IsProbabilityMeasure μ := hprob
  obtain ⟨hiP,hiQ,hMP,hMQ,heq⟩ := density_mutualInformation_comparison O R
    (γ.prod volume) g hg hgp μ rfl p hp hdens hfs hss hOR hpP hpQ (by rwa [hRf])
  have hinput : mutualInformation (P.map swapLast) ≠ ∞ :=
    (countable_information_le_entropy _ (by simpa only [swapLast_snd] using hH)).1
  have hinputQ : mutualInformation (Q.map swapLast) ≠ ∞ := by
    rw [mutualInformation_independent_rows]
    exact (countable_information_le_entropy _ hH).1
  have hchainP := exposedInformation_chain P
  have hchainQ := exposedInformation_chain Q
  have hJP : exposedInformation P ≠ ∞ := ne_top_of_le_ne_top hinput (hchainP ▸ le_add_left le_rfl)
  have hJQ : exposedInformation Q ≠ ∞ := ne_top_of_le_ne_top hinputQ (hchainQ ▸ le_add_left le_rfl)
  refine ⟨hiP,hiQ,hJP,hJQ,?_⟩
  have hinputEq : mutualInformation (P.map swapLast) = mutualInformation (Q.map swapLast) + rowInformation P γ := by
    rw [mutualInformation_independent_rows]
    exact mutualInformation_rows_chain P ν γ hInd
  have he := congrArg ENNReal.toReal hinputEq
  rw [ENNReal.toReal_add hinputQ hk] at he
  have heP := congrArg ENNReal.toReal hchainP
  have heQ := congrArg ENNReal.toReal hchainQ
  rw [ENNReal.toReal_add hMP hJP] at heP
  rw [ENNReal.toReal_add hMQ hJQ] at heQ
  have hb := ENNReal.toReal_mono hk hDPI
  linarith



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Refinement
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


lemma alignedExperiment_fst {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    (alignedExperiment (r:=r) P).fst = P.fst := by
  rw [alignedExperiment,Measure.fst,Measure.map_map measurable_fst measurable_alignedMap]
  change (actualExperiment (r:=r) P).map (Prod.fst ∘ Prod.fst) = _
  rw [←Measure.map_map measurable_fst measurable_fst,←Measure.fst]
  change (P.prod (gaussianRows r d)).fst.map Prod.fst = _
  rw [Measure.fst_prod]
  rfl

lemma alignedExperiment_independence {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) :
    ((alignedExperiment (r:=r) P).map swapLast).fst = ν.prod (gaussianRows (m+r) d) := by
  have h := congrArg (fun μ : Measure (Rows (m+r) d×Sphere d) => μ.map Prod.swap)
    (map_actualRowsSignal (r:=r) P ν hInd)
  rw [Measure.prod_swap,Measure.map_map measurable_swap measurable_actualRowsSignal] at h
  rw [alignedExperiment,Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map (measurable_fst.comp swapLast.measurable) measurable_alignedMap]
  exact h



lemma critical_moment_log_bound {d ℓ : ℕ} (hd : 1 ≤ d) (hℓ : ℓ ≤ d)
    (q t s : ℝ) (hs : 0 ≤ s) (hb : 0 ≤ q+(ℓ:ℝ)*Real.log 4+t) :
    Real.log (1+momentBound 9 d (Real.exp (q+(ℓ:ℝ)*Real.log 4+t))
      (Real.exp s*(3*4^d))) ≤ (q+t)+18*d+Real.log (1+s) := by
  let b := q+(ℓ:ℝ)*Real.log 4+t
  let B := Real.exp b
  let D := Real.exp s*(3*4^d)
  let M := momentBound 9 d B D
  have hB : 0 < B := Real.exp_pos _
  have hD : 0 < D := by dsimp [D]; positivity
  have hB1 : 1 ≤ B := Real.one_le_exp_iff.mpr hb
  have hlog4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hlog3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlogD : Real.log D ≤ s+2+3*d := by
    dsimp only [D]
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity),Real.log_exp,
      Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),Real.log_pow]
    nlinarith [Nat.cast_nonneg (α:=ℝ) d]
  have hmax : max (Real.log (D/B)) 0 ≤ s+2+3*d := by
    apply max_le _ (by positivity)
    rw [Real.log_div hD.ne' hB.ne',show Real.log B=b from Real.log_exp b]
    linarith
  have hu : 0 < 1+max (Real.log (D/B)) 0 := by positivity
  have hM : 0 < M := by dsimp [M,momentBound]; positivity
  have hM1 : 1 ≤ M := by
    have hExp : 1 ≤ Real.exp (9*(d:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
    have hU : 1 ≤ 1+max (Real.log (D/B)) 0 := le_add_of_nonneg_right (le_max_right _ _)
    dsimp only [M,momentBound]
    calc
      1 = 1*1*1 := by ring
      _ ≤ Real.exp (9*(d:ℝ))*B*(1+max (Real.log (D/B)) 0) :=
        mul_le_mul (mul_le_mul hExp hB1 (by norm_num) (by positivity)) hU (by norm_num) (by positivity)
  have hupp : Real.log (1+max (Real.log (D/B)) 0) ≤ 2+3*d+Real.log (1+s) := by
    have hprod : 1+max (Real.log (D/B)) 0 ≤ (3+3*(d:ℝ))*(1+s) := by
      nlinarith [Nat.cast_nonneg (α:=ℝ) d]
    have hh := Real.log_le_log hu hprod
    rw [Real.log_mul (by positivity) (by positivity)] at hh
    have hc : Real.log (3+3*(d:ℝ)) ≤ 2+3*d := by
      linarith [Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<3+3*(d:ℝ))]
    linarith
  have hh : Real.log (1+M) ≤ Real.log 2+Real.log M := by
    have hh := Real.log_le_log (by positivity : 0<1+M) (show 1+M ≤ 2*M by linarith)
    rwa [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hM.ne'] at hh
  have hmLog : Real.log M = 9*(d:ℝ)+b+Real.log (1+max (Real.log (D/B)) 0) := by
    dsimp only [M,momentBound]
    rw [Real.log_mul (by positivity) hu.ne',Real.log_mul (Real.exp_pos _).ne' hB.ne',
      Real.log_exp,show Real.log B=b from Real.log_exp b]
  rw [hmLog] at hh
  change Real.log (1+M) ≤ _
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hl' : (ℓ:ℝ) ≤ d := by exact_mod_cast hℓ
  dsimp only [b] at hh
  nlinarith [Nat.cast_nonneg (α:=ℝ) ℓ]

lemma integrable_log_one_add_real {A : Type*} [MeasurableSpace A]
    (μ : Measure A) {f : A → ℝ} (hf : Integrable f μ)
    (hm : Measurable f) (h0 : ∀ᵐ x ∂μ, 0 ≤ f x) :
    Integrable (fun x => Real.log (1+f x)) μ := by
  apply hf.mono' (measurable_const.add hm |>.log.aestronglyMeasurable)
  filter_upwards [h0] with x hx
  change ‖Real.log (1+f x)‖ ≤ f x
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith))]
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0<1+f x)]

lemma integral_log_one_add_real_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] {f : A → ℝ} (hf : Integrable f μ)
    (hm : Measurable f) (h0 : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (∫ x, Real.log (1+f x) ∂μ) ≤ Real.log (1+∫ x, f x ∂μ) := by
  have hLi := integrable_log_one_add_real μ hf hm h0
  let M := 1+∫ x, f x ∂μ
  have hM : 0<M := by dsimp only [M]; linarith [integral_nonneg_of_ae h0]
  have hb : ∀ᵐ x ∂μ, Real.log (1+f x) ≤ Real.log M+(1+f x)/M-1 := by
    filter_upwards [h0] with x hx
    have hh := Real.log_le_sub_one_of_pos (show 0<(1+f x)/M by positivity)
    rw [Real.log_div (by positivity) hM.ne'] at hh
    linarith
  have h1f : Integrable (fun x => 1+f x) μ := (integrable_const 1).add hf
  have hdiv : Integrable (fun x => (1+f x)/M) μ := h1f.div_const M
  have hsum : Integrable (fun x => Real.log M+(1+f x)/M) μ := (integrable_const _).add hdiv
  have hi : Integrable (fun x => Real.log M+(1+f x)/M-1) μ := hsum.sub (integrable_const 1)
  have hb' := integral_mono_ae hLi hi hb
  rw [integral_sub hsum (integrable_const 1),integral_add (integrable_const (Real.log M)) hdiv,
    integral_div,integral_add (integrable_const 1) hf] at hb'
  simp only [integral_const,probReal_univ,one_smul] at hb'
  change _ ≤ Real.log M at ⊢
  have he : (1+∫ x, f x ∂μ)/M=1 := div_self hM.ne'
  rw [he] at hb'
  linarith


lemma refineSignal_fst {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] (P : Measure (S×W)) (e : S×W → E) (he : Measurable e) :
    (refineSignal P e).fst = P.fst := by
  rw [refineSignal,Measure.fst,Measure.map_map measurable_fst
    (measurable_fst.prodMk (measurable_snd.prodMk he))]
  rfl

lemma refineSignal_snd_fst {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] (P : Measure (S×W)) (e : S×W → E) (he : Measurable e) :
    (refineSignal P e).snd.fst = P.snd := by
  rw [refineSignal,Measure.fst,Measure.snd,Measure.map_map measurable_fst measurable_snd,
    Measure.map_map (measurable_fst.comp measurable_snd)
      (measurable_fst.prodMk (measurable_snd.prodMk he))]
  rfl

lemma refineSignal_snd_snd {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] (P : Measure (S×W)) (e : S×W → E) (he : Measurable e) :
    (refineSignal P e).snd.snd = P.map e := by
  rw [refineSignal,Measure.snd,Measure.snd,Measure.map_map measurable_snd measurable_snd,
    Measure.map_map (measurable_snd.comp measurable_snd)
      (measurable_fst.prodMk (measurable_snd.prodMk he))]
  rfl

lemma refinementLoss_nonneg {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) [IsProbabilityMeasure P] (e : S×W → E) (he : Measurable e)
    {v : W×E} (hv : (refineSignal P e).snd {v} ≠ 0) : 0 ≤ refinementLoss P e v := by
  have hh : (refineSignal P e).snd {v} ≤ P.snd {v.1} := by
    rw [←refineSignal_snd_fst P e he,Measure.fst_apply (measurableSet_singleton _)]
    exact measure_mono (by intro x hx; have hx' : x=v := hx; simp only [mem_preimage,mem_singleton_iff,hx'])
  have hl := Real.log_le_log (ENNReal.toReal_pos hv (measure_ne_top _ _))
    (ENNReal.toReal_mono (measure_ne_top _ _) hh)
  dsimp only [refinementLoss]
  linarith

lemma refinementLoss_eq {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) [IsProbabilityMeasure P] (e : S×W → E) (he : Measurable e)
    {v : W×E} (hv : (refineSignal P e).snd {v} ≠ 0) :
    refinementLoss P e v = -Real.log (messagePosterior P v.1 {x | e (x,v.1)=v.2}).toReal := by
  have hw := refineSignal_positive_original P e he hv
  have hmass := refineSignal_mass P e he hw v.2
  have hη : messagePosterior P v.1 {x | e (x,v.1)=v.2} ≠ 0 := by
    intro hz
    rw [hmass,hz,mul_zero] at hv
    exact hv rfl
  unfold refinementLoss
  rw [hmass,ENNReal.toReal_mul,Real.log_mul
    (ENNReal.toReal_ne_zero.mpr ⟨hw,measure_ne_top _ _⟩)
    (ENNReal.toReal_ne_zero.mpr ⟨hη,measure_ne_top _ _⟩)]
  ring

lemma refinement_entropy_and_loss {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [Countable W] [Countable E]
    [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) [IsProbabilityMeasure P] (e : S×W → E) (he : Measurable e)
    (hW : shannonEntropy P.snd ≠ ∞) (hE : shannonEntropy (P.map e) ≠ ∞) :
    shannonEntropy (refineSignal P e).snd ≠ ∞ ∧
    (shannonEntropy (refineSignal P e).snd).toReal ≤ (shannonEntropy P.snd).toReal +
      (shannonEntropy (P.map e)).toReal ∧
    Integrable (refinementLoss P e) (refineSignal P e).snd ∧
    (∫ v, refinementLoss P e v ∂(refineSignal P e).snd) ≤ (shannonEntropy (P.map e)).toReal := by
  let := refineSignal_probability P e he
  obtain ⟨hHW,hbound⟩ := shannonEntropy_subadd (refineSignal P e).snd
    (by rwa [refineSignal_snd_fst P e he]) (by rwa [refineSignal_snd_snd P e he])
  rw [refineSignal_snd_fst P e he,refineSignal_snd_snd P e he] at hbound
  have hpi := entropy_finite_integrable (refineSignal P e).snd hHW
  have hwi : Integrable (fun v : W×E => -Real.log (P.snd {v.1}).toReal) (refineSignal P e).snd := by
    apply (integrable_map_measure (measurable_of_countable
      (fun w : W => -Real.log (P.snd {w}).toReal)).aestronglyMeasurable measurable_fst.aemeasurable).mp
    change Integrable _ (refineSignal P e).snd.fst
    rw [refineSignal_snd_fst P e he]
    exact entropy_finite_integrable P.snd hW
  have hloss : Integrable (refinementLoss P e) (refineSignal P e).snd := by
    convert hpi.sub hwi using 1
    ext v
    simp [refinementLoss]
  refine ⟨hHW,hbound,hloss,?_⟩
  have heq : (∫ v, refinementLoss P e v ∂(refineSignal P e).snd) =
      (shannonEntropy (refineSignal P e).snd).toReal - (shannonEntropy P.snd).toReal := by
    have hfun : refinementLoss P e = (fun v => -Real.log ((refineSignal P e).snd {v}).toReal -
        -Real.log (P.snd {v.1}).toReal) := by funext v; simp [refinementLoss]
    rw [hfun,integral_sub hpi hwi,integral_surprisal]
    have hh : (∫ v : W×E, -Real.log (P.snd {v.1}).toReal ∂(refineSignal P e).snd) =
        (shannonEntropy P.snd).toReal := by
      rw [←integral_map measurable_fst.aemeasurable (measurable_of_countable
        (fun w => -Real.log (P.snd {w}).toReal)).aestronglyMeasurable]
      change (∫ w, -Real.log (P.snd {w}).toReal ∂(refineSignal P e).snd.fst) = _
      rw [refineSignal_snd_fst P e he,integral_surprisal]
    rw [hh]
  linarith

lemma refineSignal_snd {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] (P : Measure (S×W)) (e : S×W → E) (he : Measurable e) :
    (refineSignal P e).snd = P.map (fun p => (p.2,e p)) := by
  rw [refineSignal,Measure.snd,Measure.map_map measurable_snd
    (measurable_fst.prodMk (measurable_snd.prodMk he))]
  rfl



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Posterior
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


lemma criticalSignal_fst {d : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (ℓ : ℕ) :
    (criticalSignal P ℓ).fst = P.fst :=
  refineSignal_fst P _ (measurable_criticalRefinement P ℓ)

lemma criticalSignal_posterior {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P]
    {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0) :
    messagePosterior (criticalSignal P ℓ) v = criticalPosterior (messagePosterior P v.1) ℓ v.2.1 v.2.2 ∧
    0 < messagePosterior P v.1 (criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2) ∧
    P.snd {v.1} ≠ 0 := by
  have he := measurable_criticalRefinement P ℓ
  have hw := refineSignal_positive_original P _ he hv
  have hc : {s : Sphere d | criticalRefinement P ℓ (s,v.1) = v.2} =
      criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2 := by
    ext s
    simp only [criticalRefinement,criticalClass,mem_ofPred_eq,Prod.ext_iff]
  have hmass := refineSignal_mass P _ he hw v.2
  rw [hc] at hmass
  change (criticalSignal P ℓ).snd {v} = _ at hmass
  have hη : messagePosterior P v.1 (criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2) ≠ 0 := by
    intro hz
    rw [hmass,hz,mul_zero] at hv
    exact hv rfl
  refine ⟨?_,hη.bot_lt,hw⟩
  have hp := messagePosterior_refinement P _ he hv
  rw [hc] at hp
  exact hp

lemma criticalB_eq {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P]
    {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0) :
    criticalB P ℓ v = (4:ℝ)^ℓ * Real.exp (v.2.2:ℝ) /
      (messagePosterior P v.1 (criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2)).toReal := by
  have he := measurable_criticalRefinement P ℓ
  have hc : {s : Sphere d | criticalRefinement P ℓ (s,v.1) = v.2} =
      criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2 := by
    ext s
    simp only [criticalRefinement,criticalClass,mem_ofPred_eq,Prod.ext_iff]
  have hδ := refinementLoss_eq P _ he hv
  rw [hc] at hδ
  have hη := (criticalSignal_posterior P hv).2.1
  have hηr := ENNReal.toReal_pos hη.ne' (measure_ne_top _ _)
  unfold criticalB
  rw [hδ,Real.exp_add,Real.exp_add,Real.exp_neg,Real.exp_log hηr,
    ←Real.log_pow,Real.exp_log (by positivity : (0:ℝ)<4^ℓ)]
  ring

lemma criticalD_eq {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P]
    {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0) :
    criticalD P ℓ v = ((criticalSignal P ℓ).snd {v}).toReal⁻¹*(3*4^d) := by
  rw [criticalD,Real.exp_neg,Real.exp_log (ENNReal.toReal_pos hv (measure_ne_top _ _))]

lemma criticalFamily_growth {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0) :
    LocalGrowth (messagePosterior (criticalSignal P ℓ) v) ℓ (criticalB P ℓ v) ∧
    LocalGrowth (messagePosterior (criticalSignal P ℓ) v) (d-1) (criticalD P ℓ v) ∧
    0 ≤ (v.2.2:ℝ)+(ℓ:ℝ)*Real.log 4+refinementLoss P (criticalRefinement P ℓ) v ∧
    messagePosterior (criticalSignal P ℓ) v ≪ uniformSphere d := by
  obtain ⟨hpost,hη,hw⟩ := criticalSignal_posterior P hv
  have hd : 1 ≤ d := by omega
  have hg := posterior_sphere_growth P hσ hd hw
  let D := (P.snd {v.1}).toReal⁻¹*(3*4^d)
  have hD : 1 ≤ D := by
    have ha := ENNReal.toReal_pos hw (measure_ne_top _ _)
    have ha1 : (P.snd {v.1}).toReal ≤ 1 := by
      exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using (prob_le_one : P.snd {v.1} ≤ 1))
    have hinv : 1 ≤ (P.snd {v.1}).toReal⁻¹ := (one_le_inv₀ ha).mpr ha1
    have hp : (1:ℝ) ≤ 4^d := one_le_pow₀ (by norm_num)
    dsimp only [D]
    nlinarith
  have hsigma : (criticalSignal P ℓ).fst = uniformSphere d := (criticalSignal_fst P ℓ).trans hσ
  refine ⟨?_,?_,?_,?_⟩
  · rw [hpost,criticalB_eq P hv]
    exact criticalPosterior_growth (messagePosterior P v.1) D (by linarith) hg hℓ v.2.2 hη
  · rw [criticalD_eq P hv]
    exact posterior_sphere_growth (criticalSignal P ℓ) hsigma hd hv
  · obtain ⟨s,hs⟩ := nonempty_of_measure_ne_zero hη.ne'
    have hq := (criticalLevel_bounds (messagePosterior P v.1) D hD hg hℓ s).1
    rw [hs.2] at hq
    have hl4 : 1 ≤ Real.log 4 := by
      have hh : Real.log 4 = 2*Real.log 2 := by
        have hh := (Real.log_pow (2:ℝ) 2)
        norm_num at hh ⊢
        exact hh
      linarith [Real.log_two_gt_d9]
    have ht := refinementLoss_nonneg P _ (measurable_criticalRefinement P ℓ) hv
    nlinarith [Nat.cast_nonneg (α:=ℝ) ℓ]
  · have hh := messagePosterior_le (criticalSignal P ℓ) hv
    rw [hsigma] at hh
    exact hh.absolutelyContinuous.trans Measure.smul_absolutelyContinuous

lemma criticalSignal_entropy {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) (hH : shannonEntropy P.snd ≠ ∞) :
    shannonEntropy (P.map (criticalRefinement P ℓ)) ≠ ∞ ∧
    (shannonEntropy (P.map (criticalRefinement P ℓ))).toReal ≤
      1+2*Real.log (20*((d:ℝ)+1+(shannonEntropy P.snd).toReal)+1) ∧
    shannonEntropy (criticalSignal P ℓ).snd ≠ ∞ ∧
    (shannonEntropy (criticalSignal P ℓ).snd).toReal ≤ (shannonEntropy P.snd).toReal+
      (shannonEntropy (P.map (criticalRefinement P ℓ))).toReal := by
  obtain ⟨he,hb⟩ := criticalRefinement_entropy P hσ hℓ hH
  obtain ⟨hp,hpb,_,_⟩ := refinement_entropy_and_loss P _ (measurable_criticalRefinement P ℓ) hH he
  exact ⟨he,hb,hp,hpb⟩

lemma criticalLevel_integrable {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) (hH : shannonEntropy P.snd ≠ ∞) :
    Integrable (fun v : W×(ℕ×ℤ) => (v.2.2:ℝ)) (criticalSignal P ℓ).snd := by
  let e := criticalRefinement P ℓ
  have he := measurable_criticalRefinement P ℓ
  have hw : Integrable (fun p : Sphere d×W => -Real.log (P.snd {p.2}).toReal) P :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable measurable_snd.aemeasurable).mp
      (entropy_finite_integrable P.snd hH)
  have hbi : Integrable (fun p : Sphere d×W => 20*((d:ℝ)+1-Real.log (P.snd {p.2}).toReal)) P := by
    convert ((integrable_const ((d:ℝ)+1)).add hw).const_mul 20 using 1 <;>
      first | rfl | (funext p; simp only [Pi.add_apply]; ring)
  have hqi : Integrable (fun p => ((e p).2:ℝ)) P := by
    apply hbi.mono' ((measurable_of_countable (fun x : ℕ×ℤ => (x.2:ℝ))).comp he).aestronglyMeasurable
    have hp := (ae_map_iff measurable_snd.aemeasurable ((Set.to_countable _).measurableSet)).mp
      (ae_positive_atom P.snd)
    filter_upwards [hp] with p hp
    have hb := criticalRefinement_size P hσ hℓ hp
    change ‖((e p).2:ℝ)‖ ≤ _
    rw [Real.norm_eq_abs]
    have habs : |((e p).2:ℝ)| = ((e p).2.natAbs:ℝ) := by simp
    rw [habs]
    change ((e p).1:ℝ)+2*((e p).2.natAbs:ℝ) ≤ _ at hb
    nlinarith [Nat.cast_nonneg (α:=ℝ) (e p).1,Nat.cast_nonneg (α:=ℝ) (e p).2.natAbs]
  change Integrable _ (refineSignal P e).snd
  rw [refineSignal_snd P e he]
  exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_snd.prodMk he).aemeasurable).mpr hqi

lemma criticalFamily_moment_mean {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) (hH : shannonEntropy P.snd ≠ ∞) :
    Integrable (fun v => Real.log (1+momentBound 9 d (criticalB P ℓ v) (criticalD P ℓ v)))
      (criticalSignal P ℓ).snd ∧
    (∫ v, Real.log (1+momentBound 9 d (criticalB P ℓ v) (criticalD P ℓ v)) ∂(criticalSignal P ℓ).snd) ≤
      (∫ v : W×(ℕ×ℤ), (v.2.2:ℝ) ∂(criticalSignal P ℓ).snd) +
      (shannonEntropy (P.map (criticalRefinement P ℓ))).toReal + 18*d +
      Real.log (1+(shannonEntropy (criticalSignal P ℓ).snd).toReal) := by
  let π := (criticalSignal P ℓ).snd
  let e := criticalRefinement P ℓ
  let s : W×(ℕ×ℤ) → ℝ := fun v => -Real.log (π {v}).toReal
  have hs : Integrable s π := entropy_finite_integrable π (criticalSignal_entropy P hσ hℓ hH).2.2.1
  have hsm : Measurable s := measurable_of_countable _
  have hs0 : ∀ v, 0 ≤ s v := atom_surprisal_nonneg π
  have hlog := integrable_log_one_add_real π hs hsm (Eventually.of_forall hs0)
  have hlogmean := integral_log_one_add_real_le π hs hsm (Eventually.of_forall hs0)
  have hsmean : (∫ v, s v ∂π) = (shannonEntropy π).toReal := integral_surprisal π
  rw [hsmean] at hlogmean
  obtain ⟨_,_,hδ,hδmean⟩ := refinement_entropy_and_loss P e (measurable_criticalRefinement P ℓ) hH
    (criticalSignal_entropy P hσ hℓ hH).1
  have hqi := criticalLevel_integrable P hσ hℓ hH
  have hupper : Integrable (fun v : W×(ℕ×ℤ) => ((v.2.2:ℝ)+refinementLoss P e v)+18*d+Real.log (1+s v)) π :=
    ((hqi.add hδ).add (integrable_const _)).add hlog
  have hle : ∀ᵐ v ∂π,
      Real.log (1+momentBound 9 d (criticalB P ℓ v) (criticalD P ℓ v)) ≤
        ((v.2.2:ℝ)+refinementLoss P e v)+18*d+Real.log (1+s v) := by
    filter_upwards [ae_positive_atom π] with v hv
    have hb := (criticalFamily_growth P hσ hℓ hv).2.2.1
    exact critical_moment_log_bound (by omega) (by omega) _ _ _
      (hs0 v) hb
  have hL : Integrable (fun v => Real.log (1+momentBound 9 d (criticalB P ℓ v) (criticalD P ℓ v))) π := by
    apply hupper.mono' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [hle] with v hv
    have hB : 0 ≤ criticalB P ℓ v := (Real.exp_pos _).le
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg
      (le_add_of_nonneg_right (momentBound_nonneg 9 d hB)))]
    exact hv
  refine ⟨hL,?_⟩
  have hh := integral_mono_ae hL hupper hle
  have hqδ : Integrable (fun v : W×(ℕ×ℤ) => (v.2.2:ℝ)+refinementLoss P e v) π := hqi.add hδ
  have hu : Integrable (fun v : W×(ℕ×ℤ) => (v.2.2:ℝ)+refinementLoss P e v+18*(d:ℝ)) π :=
    hqδ.add (integrable_const _)
  rw [integral_add hu hlog,integral_add hqδ (integrable_const (18*(d:ℝ))),integral_add hqi hδ,
    integral_const,probReal_univ,one_smul] at hh
  exact hh.trans (add_le_add (add_le_add (add_le_add le_rfl hδmean) le_rfl) hlogmean)


lemma completeFamily_restrict_apply {W T : Type*} [MeasurableSpace W]
    (π : Measure W) (f : W → T) (t₀ : T) {w : W} (hw : π {w} ≠ 0) :
    completeFamily π (fun v => f v.1) t₀ w = f w := by
  have hp : 0 < π {w} := pos_iff_ne_zero.mpr hw
  rw [completeFamily, dite_eq_left hp]

lemma actual_posterior_completed {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d)
    (hH : shannonEntropy P.fst.snd ≠ ∞)
    (B D : W → ℝ)
    (hB : ∀ w, P.fst.snd {w} ≠ 0 → 0 < B w)
    (hD : ∀ w, P.fst.snd {w} ≠ 0 → 0 < D w)
    (hAC : ∀ w, P.fst.snd {w} ≠ 0 → messagePosterior P.fst w ≪ uniformSphere d)
    (hgB : ∀ w, P.fst.snd {w} ≠ 0 → LocalGrowth (messagePosterior P.fst w) (m+r) (B w))
    (hgD : ∀ w, P.fst.snd {w} ≠ 0 → LocalGrowth (messagePosterior P.fst w) (d-1) (D w))
    (hCI : Integrable (fun w => Real.log (1+momentBound 9 d (B w) (D w))) P.fst.snd) :
    ActualRowConclusion (r:=r) (q:=q) P
      (completeFamily (P.map swapLast).snd (fun w => messagePosterior P.fst w.1) 0)
      (completeFamily (P.map swapLast).snd (fun w => B w.1) 1)
      (completeFamily (P.map swapLast).snd (fun w => D w.1) 1) := by
  let π := (P.map swapLast).snd
  have hπ : π = P.fst.snd := swapLast_snd P
  let ρ : PositiveMessage π → Measure (Sphere d) := fun w => messagePosterior P.fst w.1
  let b : PositiveMessage π → ℝ := fun w => B w.1
  let c : PositiveMessage π → ℝ := fun w => D w.1
  have hw (w : PositiveMessage π) : P.fst.snd {w.1} ≠ 0 := by rw [←hπ]; exact w.2.ne'
  let f : W → ℝ := fun w => Real.log (1+momentBound 9 d (B w) (D w))
  let f' : W → ℝ := fun w => Real.log (1+momentBound 9 d
    (completeFamily π b 1 w) (completeFamily π c 1 w))
  have hf : f' =ᵐ[π] f := by
    filter_upwards [ae_positive_atom π] with w hw
    dsimp only [f',f,b,c]
    rw [completeFamily_restrict_apply π B 1 hw,completeFamily_restrict_apply π D 1 hw]
  have hfbase : (fun sw : Sphere d×W => f' sw.2) =ᵐ[P.fst] (fun sw => f sw.2) := by
    apply (ae_map_iff measurable_snd.aemeasurable (measurableSet_eq_fun
      (measurable_of_countable f') (measurable_of_countable f))).mp
    change f' =ᵐ[P.fst.snd] f
    rw [←hπ]
    exact hf
  have hCI' : Integrable (fun sw : Sphere d×W => f' sw.2) P.fst := by
    apply Integrable.congr _ hfbase.symm
    exact (integrable_map_measure (measurable_of_countable f).aestronglyMeasurable
      measurable_snd.aemeasurable).mp hCI
  exact actualRowMain hdim P ν hInd H hν (by rwa [swapLast_snd]) ρ
    (fun w => hAC w.1 (hw w)) b c (fun w => hB w.1 (hw w)) (fun w => hD w.1 (hw w))
    (fun w => hgB w.1 (hw w)) (fun w => hgD w.1 (hw w)) hCI'

lemma actualRowConclusion_observed {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ρ : W → Measure (Sphere d)) [∀ w, IsFiniteMeasure (ρ w)] (B D : W → ℝ)
    (hmain : ActualRowConclusion (r:=r) (q:=q) P ρ B D) :
    Integrable (fun z => Real.log (1+(exactDensity (ρ z.2) z.1.1 z.1.2).toReal))
      (observedMessage (alignedExperiment (r:=r) P)) ∧
    Integrable (fun z => logPositive (exactDensity (ρ z.2) z.1.1 z.1.2))
      (observedMessage (alignedExperiment (r:=r) P)) ∧
    (∫ z, Real.log (1+(exactDensity (ρ z.2) z.1.1 z.1.2).toReal)
      ∂observedMessage (alignedExperiment (r:=r) P)) ≤
        (rowInformation P (gaussianRows m d)).toReal/q +
          ∫ w, Real.log (1+momentBound 9 d (B w) (D w)) ∂P.fst.snd := by
  let O := observedMessage (alignedExperiment (r:=r) P)
  let p : (Rows (m+r) d×(Fin (m+r)→ℝ))×W → ℝ≥0∞ :=
    fun z => exactDensity (ρ z.2) z.1.1 z.1.2
  have hp : Measurable p := measurable_from_prod_countable_left fun w => measurable_exactDensity (k:=m+r) (ρ w)
  let T : ((Sphere d×W)×Rows m d)×Rows r d → (Rows (m+r) d×(Fin (m+r)→ℝ))×W :=
    observedMessageMap ∘ (fun p => (p.1.1,Fin.append p.1.2 p.2))
  have hT : Measurable T := measurable_observedMessageMap.comp measurable_alignedMap
  have hO : O = (actualExperiment (r:=r) P).map T := by
    dsimp only [O]
    rw [observedMessage,alignedExperiment,Measure.map_map measurable_observedMessageMap measurable_alignedMap]
  have hLi : Integrable (fun z => Real.log (1+(p z).toReal)) O := by
    rw [hO]
    apply (integrable_map_measure (measurable_log_one_add hp).aestronglyMeasurable
      hT.aemeasurable).mpr
    exact hmain.exact_integrable
  have hPi : Integrable (fun z => logPositive (p z)) O := by
    rw [hO]
    apply (integrable_map_measure ((hp.ennreal_toReal.log.max measurable_const).aestronglyMeasurable) hT.aemeasurable).mpr
    exact hmain.positive_log_integrable
  refine ⟨hLi,hPi,?_⟩
  change (∫ z, Real.log (1+(p z).toReal) ∂O) ≤ _
  rw [hO,integral_map hT.aemeasurable (measurable_log_one_add hp).aestronglyMeasurable]
  have hb := hmain.exact_bound
  rw [←integral_map measurable_snd.aemeasurable (measurable_of_countable
    (fun w => Real.log (1+momentBound 9 d (B w) (D w)))).aestronglyMeasurable] at hb
  exact hb

lemma observedMessage_aligned_positive {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    ∀ᵐ z ∂observedMessage (alignedExperiment (r:=r) P), (P.map swapLast).snd {z.2} ≠ 0 := by
  have hpos : ∀ᵐ w ∂(observedMessage (alignedExperiment (r:=r) P)).snd, (P.map swapLast).snd {w} ≠ 0 := by
    rw [observedMessage_snd,alignedExperiment_fst,swapLast_snd]
    exact ae_positive_atom P.fst.snd
  exact (ae_map_iff measurable_snd.aemeasurable
    (Set.to_countable {w : W | (P.map swapLast).snd {w} ≠ 0}).measurableSet).mp hpos



lemma actual_posterior_log_bound {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d)
    (hH : shannonEntropy P.fst.snd ≠ ∞)
    (B D : W → ℝ)
    (hB : ∀ w, P.fst.snd {w} ≠ 0 → 0 < B w)
    (hD : ∀ w, P.fst.snd {w} ≠ 0 → 0 < D w)
    (hAC : ∀ w, P.fst.snd {w} ≠ 0 → messagePosterior P.fst w ≪ uniformSphere d)
    (hgB : ∀ w, P.fst.snd {w} ≠ 0 → LocalGrowth (messagePosterior P.fst w) (m+r) (B w))
    (hgD : ∀ w, P.fst.snd {w} ≠ 0 → LocalGrowth (messagePosterior P.fst w) (d-1) (D w))
    (hCI : Integrable (fun w => Real.log (1+momentBound 9 d (B w) (D w))) P.fst.snd) :
    Integrable (fun z => Real.log (1+(exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2).toReal))
      (observedMessage (alignedExperiment (r:=r) P)) ∧
    Integrable (fun z => logPositive (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2))
      (observedMessage (alignedExperiment (r:=r) P)) ∧
    (∫ z, Real.log (1+(exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2).toReal)
      ∂observedMessage (alignedExperiment (r:=r) P)) ≤
        (rowInformation P (gaussianRows m d)).toReal/q +
          ∫ w, Real.log (1+momentBound 9 d (B w) (D w)) ∂P.fst.snd := by
  let π := (P.map swapLast).snd
  let ρ' := completeFamily π (fun w => messagePosterior P.fst w.1) 0
  let B' := completeFamily π (fun w => B w.1) 1
  let D' := completeFamily π (fun w => D w.1) 1
  have hmain := actual_posterior_completed hdim P ν hInd H hν hH B D hB hD hAC hgB hgD hCI
  obtain ⟨hLi,hPi,hBound⟩ := actualRowConclusion_observed P ρ' B' D' hmain
  have heqp : (fun z => exactDensity (ρ' z.2) z.1.1 z.1.2) =ᵐ[observedMessage (alignedExperiment (r:=r) P)]
      (fun z => exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2) := by
    filter_upwards [observedMessage_aligned_positive (r:=r) P] with z hz
    dsimp only [ρ']
    rw [completeFamily_restrict_apply π (messagePosterior P.fst) 0 hz]
  have heqlog := heqp.mono (fun z hz => congrArg (fun t : ℝ≥0∞ => Real.log (1+t.toReal)) hz)
  have heqpos := heqp.mono (fun z hz => congrArg logPositive hz)
  refine ⟨hLi.congr heqlog,hPi.congr heqpos,?_⟩
  have hf : (fun w => Real.log (1+momentBound 9 d (B' w) (D' w))) =ᵐ[P.fst.snd]
      (fun w => Real.log (1+momentBound 9 d (B w) (D w))) := by
    rw [←swapLast_snd P]
    filter_upwards [ae_positive_atom π] with w hw
    dsimp only [B',D']
    rw [completeFamily_restrict_apply π B 1 hw,completeFamily_restrict_apply π D 1 hw]
  rw [integral_congr_ae heqlog,integral_congr_ae hf] at hBound
  exact hBound


lemma criticalFamily_cover_fibre {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0)
    (hac : ∀ᵐ G ∂gaussianRows ℓ d, labelLaw (messagePosterior (criticalSignal P ℓ) v) G ≪ volume)
    (hpi : Integrable (fun z : Rows ℓ d×(Fin ℓ→ℝ) => logPositive
      (exactDensity (messagePosterior (criticalSignal P ℓ) v) z.1 z.2))
      (projectionJoint (messagePosterior (criticalSignal P ℓ) v) (gaussianRows ℓ d))) :
    -(∫ z, Real.log (exactDensity (messagePosterior (criticalSignal P ℓ) v) z.1 z.2).toReal
      ∂projectionJoint (messagePosterior (criticalSignal P ℓ) v) (gaussianRows ℓ d)) ≤
      1+5*(ℓ:ℝ)-(v.2.2:ℝ) := by
  let R := criticalSignal P ℓ
  obtain ⟨hpost,hη,hw⟩ := criticalSignal_posterior P hv
  have hpi' : Integrable (fun z : Rows ℓ d×Sphere d => logPositive
      (exactDensity (messagePosterior R v) z.1 (label z.1 (z.2:Vector d))))
      ((gaussianRows ℓ d).prod (messagePosterior R v)) := by
    rw [projectionJoint] at hpi
    exact (integrable_map_measure ((measurable_exactDensity _).ennreal_toReal.log.max
      measurable_const).aestronglyMeasurable (measurable_fst.prodMk measurable_own_label).aemeasurable).mp hpi
  change ∀ᵐ G ∂gaussianRows ℓ d, labelLaw (messagePosterior R v) G ≪ volume at hac
  rw [show messagePosterior R v = criticalPosterior (messagePosterior P v.1) ℓ v.2.1 v.2.2 from hpost] at hpi' hac
  have hbound := (criticalPosterior_cover_entropy (messagePosterior P v.1)
    ((P.snd {v.1}).toReal⁻¹*(3*4^d)) (by positivity)
    (posterior_sphere_growth P hσ (by omega) hw) hℓ v.2.2 hη hac hpi').2
  rw [projectionJoint,integral_map (measurable_fst.prodMk measurable_own_label).aemeasurable
    (measurable_exactDensity _).ennreal_toReal.log.aestronglyMeasurable]
  simpa only [hpost] using hbound


lemma criticalFamily_cover_mean {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) (hH : shannonEntropy P.snd ≠ ∞)
    (hAC : ∀ᵐ v ∂(criticalSignal P ℓ).snd, ∀ᵐ G ∂gaussianRows ℓ d,
      labelLaw (messagePosterior (criticalSignal P ℓ) v) G ≪ volume)
    (hpos : Integrable (fun z => logPositive (exactDensity
      (messagePosterior (criticalSignal P ℓ) z.2) z.1.1 z.1.2))
      (observedMessage ((criticalSignal P ℓ).prod (gaussianRows ℓ d))))
    (hlog : Integrable (fun z => Real.log (exactDensity
      (messagePosterior (criticalSignal P ℓ) z.2) z.1.1 z.1.2).toReal)
      (observedMessage ((criticalSignal P ℓ).prod (gaussianRows ℓ d)))) :
    -(∫ z, Real.log (exactDensity (messagePosterior (criticalSignal P ℓ) z.2) z.1.1 z.1.2).toReal
      ∂observedMessage ((criticalSignal P ℓ).prod (gaussianRows ℓ d))) ≤
      1+5*(ℓ:ℝ)-(∫ v : W×(ℕ×ℤ), (v.2.2:ℝ) ∂(criticalSignal P ℓ).snd) := by
  let R := criticalSignal P ℓ
  let π := R.snd
  let κ := posteriorProjectionKernel R (gaussianRows ℓ d)
  let f : (W×(ℕ×ℤ))×(Rows ℓ d×(Fin ℓ→ℝ)) → ℝ :=
    fun z => Real.log (exactDensity (messagePosterior R z.1) z.2.1 z.2.2).toReal
  let fp : (W×(ℕ×ℤ))×(Rows ℓ d×(Fin ℓ→ℝ)) → ℝ :=
    fun z => logPositive (exactDensity (messagePosterior R z.1) z.2.1 z.2.2)
  have hm : Measurable (fun z : (Rows ℓ d×(Fin ℓ→ℝ))×(W×(ℕ×ℤ)) =>
      exactDensity (messagePosterior R z.2) z.1.1 z.1.2) :=
    measurable_from_prod_countable_left fun v => measurable_exactDensity (k:=ℓ) (messagePosterior R v)
  have hfi : Integrable f (π ⊗ₘ κ) := by
    rw [observedMessage_independent_disintegrate] at hlog
    exact (integrable_map_measure hm.ennreal_toReal.log.aestronglyMeasurable
      measurable_swap.aemeasurable).mp hlog
  have hfpi : Integrable fp (π ⊗ₘ κ) := by
    rw [observedMessage_independent_disintegrate] at hpos
    exact (integrable_map_measure (hm.ennreal_toReal.log.max measurable_const).aestronglyMeasurable
      measurable_swap.aemeasurable).mp hpos
  have hji : Integrable (fun v => ∫ z, f (v,z) ∂κ v) π := by
    simpa only [Kernel.prodMkLeft_apply,Kernel.const_apply] using hfi.integral_compProd
  have hposae : ∀ᵐ v ∂π, Integrable (fun z => fp (v,z)) (κ v) :=
    (Measure.integrable_compProd_iff hfpi.aestronglyMeasurable).mp hfpi |>.1
  have hb : ∀ᵐ v ∂π, -(∫ z, f (v,z) ∂κ v) ≤ 1+5*(ℓ:ℝ)-(v.2.2:ℝ) := by
    filter_upwards [ae_positive_atom π,hposae,hAC] with v hv hpi hac
    have hk : κ v = projectionJoint (messagePosterior R v) (gaussianRows ℓ d) :=
      posteriorProjectionKernel_apply R _ _
    dsimp only [fp] at hpi
    rw [hk] at hpi
    dsimp only [f]
    rw [hk]
    exact criticalFamily_cover_fibre P hσ hℓ hv hac hpi
  have hqi := criticalLevel_integrable P hσ hℓ hH
  have hupper : Integrable (fun v : W×(ℕ×ℤ) => 1+5*(ℓ:ℝ)-(v.2.2:ℝ)) π :=
    (integrable_const _).sub hqi
  have he := integral_mono_ae hji.neg hupper hb
  simp only [Pi.neg_apply] at he
  rw [integral_neg,integral_sub (integrable_const (1+5*(ℓ:ℝ))) hqi,
    integral_const,probReal_univ,one_smul] at he
  rw [observedMessage_independent_disintegrate,
    integral_map measurable_swap.aemeasurable hm.ennreal_toReal.log.aestronglyMeasurable]
  change -(∫ z, f z ∂π ⊗ₘ κ) ≤ _
  rw [Measure.integral_compProd hfi]
  exact he



lemma alignedExperiment_independent {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] :
    alignedExperiment (r:=r) (P.prod (gaussianRows m d)) = P.prod (gaussianRows (m+r) d) := by
  change (((P.prod (gaussianRows m d)).prod (gaussianRows r d)).map
    ((Prod.map id (fun p : Rows m d×Rows r d => Fin.append p.1 p.2)) ∘ MeasurableEquiv.prodAssoc)) = _
  rw [←Measure.map_map (measurable_id.prodMap (measurable_append (E:=Vector d) m r))
    MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod,
    ←Measure.map_prod_map _ _ measurable_id (measurable_append (E:=Vector d) m r),Measure.map_id]
  rw [show ((gaussianRows m d).prod (gaussianRows r d)).map (fun p => Fin.append p.1 p.2) =
    gaussianRows (m+r) d from map_append_pi (stdGaussian (Vector d)) m r]



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Comparison
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


lemma criticalFamily_projection_ac {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d) :
    ∀ᵐ v ∂(criticalSignal P (m+r)).snd, ∀ᵐ G ∂gaussianRows (m+r) d,
      labelLaw (messagePosterior (criticalSignal P (m+r)) v) G ≪ volume := by
  filter_upwards [ae_positive_atom (criticalSignal P (m+r)).snd] with v hv
  obtain ⟨hB,hD,_,_⟩ := criticalFamily_growth P hσ hdim.2.2.2.1 hv
  apply ae_labelLaw_ac_of_growth hdim _ (criticalB P (m+r) v) (criticalD P (m+r) v)
    (Real.exp_pos _) _ hB hD
  dsimp only [criticalD]
  positivity

lemma criticalFamily_actual_log_bound {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    [IsProbabilityMeasure (uniformSphere d)] (hdim : AdmissibleDimensions d m r q)
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hH : shannonEntropy P.snd ≠ ∞)
    (R : Measure ((Sphere d×(W×(ℕ×ℤ)))×Rows m d)) [IsProbabilityMeasure R]
    (hRF : R.fst = criticalSignal P (m+r))
    (hInd : (R.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d)) :
    Integrable (fun z => Real.log (1+(exactDensity
      (messagePosterior (criticalSignal P (m+r)) z.2) z.1.1 z.1.2).toReal))
      (observedMessage (alignedExperiment (r:=r) R)) ∧
    Integrable (fun z => logPositive (exactDensity
      (messagePosterior (criticalSignal P (m+r)) z.2) z.1.1 z.1.2))
      (observedMessage (alignedExperiment (r:=r) R)) ∧
    (∫ z, Real.log (1+(exactDensity (messagePosterior (criticalSignal P (m+r)) z.2) z.1.1 z.1.2).toReal)
      ∂observedMessage (alignedExperiment (r:=r) R)) ≤
      (rowInformation R (gaussianRows m d)).toReal/q +
      (∫ v : W×(ℕ×ℤ), (v.2.2:ℝ) ∂(criticalSignal P (m+r)).snd) +
      (shannonEntropy (P.map (criticalRefinement P (m+r)))).toReal + 18*d +
      Real.log (1+(shannonEntropy (criticalSignal P (m+r)).snd).toReal) := by
  have hℓ := hdim.2.2.2.1
  have hEnt := criticalSignal_entropy P hσ hℓ hH
  obtain ⟨hCI,hmean⟩ := criticalFamily_moment_mean P hσ hℓ hH
  have hmain := actual_posterior_log_bound hdim R (uniformSphere d) hInd 1
    (by simp) (by simpa only [hRF] using hEnt.2.2.1)
    (criticalB P (m+r)) (criticalD P (m+r))
    (fun v _ => Real.exp_pos _)
    (fun v _ => by dsimp only [criticalD]; positivity)
    (by intro v hv; simp only [hRF] at hv ⊢; exact (criticalFamily_growth P hσ hℓ hv).2.2.2)
    (by intro v hv; simp only [hRF] at hv ⊢; exact (criticalFamily_growth P hσ hℓ hv).1)
    (by intro v hv; simp only [hRF] at hv ⊢; exact (criticalFamily_growth P hσ hℓ hv).2.1)
    (by simpa only [hRF] using hCI)
  simp only [hRF] at hmain
  refine ⟨hmain.1,hmain.2.1,?_⟩
  linarith [hmain.2.2]

lemma critical_refined_comparison_oai {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty W] [Nonempty (Sphere d)]
    [IsProbabilityMeasure (uniformSphere d)] (hdim : AdmissibleDimensions d m r q)
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hH : shannonEntropy P.snd ≠ ∞)
    (R : Measure ((Sphere d×(W×(ℕ×ℤ)))×Rows m d)) [IsProbabilityMeasure R]
    (hRF : R.fst = criticalSignal P (m+r))
    (hInd : (R.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d)) :
    exposedInformation ((criticalSignal P (m+r)).prod (gaussianRows (m+r) d)) ≠ ∞ ∧
    exposedInformation (alignedExperiment (r:=r) R) ≠ ∞ ∧
    (exposedInformation ((criticalSignal P (m+r)).prod (gaussianRows (m+r) d))).toReal ≤
      (exposedInformation (alignedExperiment (r:=r) R)).toReal +
      (rowInformation R (gaussianRows m d)).toReal/q +
      (shannonEntropy (P.map (criticalRefinement P (m+r)))).toReal +
      (1+18*(d:ℝ)+5*(m+r)) + Real.log (1+(shannonEntropy (criticalSignal P (m+r)).snd).toReal) := by
  let F := criticalSignal P (m+r)
  let A := alignedExperiment (r:=r) R
  let Q := F.prod (gaussianRows m d)
  have hAF : A.fst = F := (alignedExperiment_fst R).trans hRF
  have hA := criticalFamily_actual_log_bound hdim P hσ hH R hRF hInd
  have hQInd : (Q.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d) := by
    rw [independent_rows_signal,criticalSignal_fst,hσ]
  have hQ := criticalFamily_actual_log_bound hdim P hσ hH Q Measure.fst_prod hQInd
  rw [alignedExperiment_independent] at hQ
  have hEnt := (criticalSignal_entropy P hσ hdim.2.2.2.1 hH).2.2.1
  have hAc := criticalFamily_projection_ac hdim P hσ
  have hsignal := alignedExperiment_independence (r:=r) R (uniformSphere d) hInd
  obtain ⟨hlogA,hlogQ,hJA,hJQ,hcompare⟩ := exposedInformation_density_comparison A
    (uniformSphere d) hsignal (by simpa only [hAF] using hEnt) (by simpa only [hAF] using hAc)
    (by simpa only [hAF] using hA.2.1) (by simpa only [hAF] using hQ.2.1)
  simp only [hAF] at hlogA hlogQ hJQ hcompare
  have hCover := criticalFamily_cover_mean P hσ hdim.2.2.2.1 hH hAc hQ.2.1 hlogQ
  have hLogLe : (∫ z, Real.log (exactDensity (messagePosterior F z.2) z.1.1 z.1.2).toReal
      ∂observedMessage A) ≤
      ∫ z, Real.log (1+(exactDensity (messagePosterior F z.2) z.1.1 z.1.2).toReal)
      ∂observedMessage A := by
    apply integral_mono_ae hlogA hA.1
    filter_upwards [] with z
    exact (le_max_left _ _).trans (logPositive_le_log_one_add _)
  refine ⟨hJQ,hJA,?_⟩
  simp only [Nat.cast_add] at hCover
  dsimp only [A,F] at hLogLe hcompare
  linarith [hA.2.2]




end CurrentProjection

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CurrentProjection.critical_refined_comparison_oai.{u_1} := @OAI.CurrentProjection.critical_refined_comparison_oai.{u_1}
