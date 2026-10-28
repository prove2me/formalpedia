-- Prove2me | solution 1 for OAI.CurrentProjection.fiberTwoPointMain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T23:55:36.35853+00:00
-- url     : https://prove2.me/submissions/734a18eb-7497-4197-8c08-1777195a17cc

import Mathlib
import Definitions.Def_GaussianReplacement
import Definitions.Def_OAIQWCP001

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
attribute [-instance] _root_.OAI.CurrentProjection.actualExperiment_isProbabilityMeasure _root_.OAI.CurrentProjection.actualObservation_isProbabilityMeasure _root_.OAI.CurrentProjection.alignedExperiment_probability _root_.OAI.CurrentProjection.blockLaw_probability _root_.OAI.CurrentProjection.completeFamily_finite _root_.OAI.CurrentProjection.criticalSignal_probability _root_.OAI.CurrentProjection.endingRowLaw_probability _root_.OAI.CurrentProjection.endingSignalLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.fixedTargetPosterior_markov _root_.OAI.CurrentProjection.gaussianObservation_probability _root_.OAI.CurrentProjection.gaussianObservations_probability _root_.OAI.CurrentProjection.gaussianRows_isProbabilityMeasure _root_.OAI.CurrentProjection.labelLaw_isFiniteMeasure _root_.OAI.CurrentProjection.prefixLaw_probability _root_.OAI.CurrentProjection.residualLaw_probability _root_.OAI.CurrentProjection.sphereLift_isFiniteMeasure _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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

end GramFactorization

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



end MixedNondegenerate

section MixedReplica
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]


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

end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Density
attribute [-instance] _root_.OAI.CurrentProjection.actualExperiment_isProbabilityMeasure _root_.OAI.CurrentProjection.actualObservation_isProbabilityMeasure _root_.OAI.CurrentProjection.alignedExperiment_probability _root_.OAI.CurrentProjection.blockLaw_probability _root_.OAI.CurrentProjection.completeFamily_finite _root_.OAI.CurrentProjection.criticalSignal_probability _root_.OAI.CurrentProjection.endingRowLaw_probability _root_.OAI.CurrentProjection.endingSignalLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.fixedTargetPosterior_markov _root_.OAI.CurrentProjection.gaussianObservation_probability _root_.OAI.CurrentProjection.gaussianObservations_probability _root_.OAI.CurrentProjection.prefixLaw_probability _root_.OAI.CurrentProjection.residualLaw_probability _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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



lemma measurable_own_cube {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] (δ : ℝ) :
    Measurable (fun z : Rows k d × Sphere d => cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) δ) := by
  have h : Measurable (fun z : Rows k d × Sphere d => (z.1, label z.1 (z.2:Vector d))) :=
    measurable_fst.prodMk (measurable_own_label (k:=k) (d:=d))
  have h2 := (measurable_cubeAverage (k:=k) ρ δ).comp h
  exact h2

lemma measurable_own_extended {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] :
    Measurable (fun z : Rows k d × Sphere d => extendedCubeDensity ρ z.1 (label z.1 (z.2:Vector d))) := by
  have h : Measurable (fun z : Rows k d × Sphere d => (z.1, label z.1 (z.2:Vector d))) :=
    measurable_fst.prodMk (measurable_own_label (k:=k) (d:=d))
  have h2 := (measurable_extendedCubeDensity (k:=k) ρ).comp h
  exact h2

lemma measurable_own_exact {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] :
    Measurable (fun z : Rows k d × Sphere d => exactDensity ρ z.1 (label z.1 (z.2:Vector d))) := by
  have h : Measurable (fun z : Rows k d × Sphere d => (z.1, label z.1 (z.2:Vector d))) :=
    measurable_fst.prodMk (measurable_own_label (k:=k) (d:=d))
  have h2 := (measurable_exactDensity (k:=k) ρ).comp h
  exact h2




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Sphere
attribute [-instance] _root_.OAI.CurrentProjection.actualExperiment_isProbabilityMeasure _root_.OAI.CurrentProjection.actualObservation_isProbabilityMeasure _root_.OAI.CurrentProjection.alignedExperiment_probability _root_.OAI.CurrentProjection.blockLaw_probability _root_.OAI.CurrentProjection.completeFamily_finite _root_.OAI.CurrentProjection.criticalSignal_probability _root_.OAI.CurrentProjection.endingRowLaw_probability _root_.OAI.CurrentProjection.endingSignalLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.fixedTargetPosterior_markov _root_.OAI.CurrentProjection.gaussianObservation_probability _root_.OAI.CurrentProjection.gaussianObservations_probability _root_.OAI.CurrentProjection.prefixLaw_probability _root_.OAI.CurrentProjection.residualLaw_probability _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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
-- module Solutions.OAIQW_CurrentProjection.CriticalEntropy
attribute [-instance] _root_.OAI.CurrentProjection.blockLaw_probability _root_.OAI.CurrentProjection.criticalSignal_probability _root_.OAI.CurrentProjection.endingRowLaw_probability _root_.OAI.CurrentProjection.endingSignalLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.fixedTargetPosterior_markov _root_.OAI.CurrentProjection.gaussianObservation_probability _root_.OAI.CurrentProjection.gaussianObservations_probability _root_.OAI.CurrentProjection.prefixLaw_probability _root_.OAI.CurrentProjection.residualLaw_probability _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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



lemma radiusVariance_ne_zero {R : ℝ} (hR : 0 < R) : radiusVariance R ≠ 0 := by
  intro h
  have := congrArg (fun v : ℝ≥0 => (v:ℝ)) h
  exact (sq_pos_of_pos hR).ne' this



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Reference
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




lemma gaussianLabels_density (k : ℕ) :
    (volume : Measure (Fin k → ℝ)).withDensity
      (fun y => ENNReal.ofReal (gaussianProductPDF 1 0 y)) = gaussianLabels k := by
  symm
  apply Measure.pi_eq
  intro t ht
  rw [withDensity_apply _ (MeasurableSet.univ_pi ht)]
  simp only [gaussianProductPDF,radiusVariance,one_pow,Pi.zero_apply]
  change (∫⁻ y in Set.univ.pi t, ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) = _
  rw [←ofReal_integral_eq_lintegral_ofReal]
  · change ENNReal.ofReal (∫ y, ∏ i, gaussianPDFReal 0 1 (y i)
        ∂(Measure.pi (fun _ : Fin k => (volume : Measure ℝ))).restrict (Set.univ.pi t)) = _
    rw [Measure.restrict_pi_pi,integral_fintype_prod_eq_prod,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => (gaussianPDFReal_pos 0 1 _ (by norm_num)).le))]
    congr 1
    funext i
    rw [gaussianReal_apply 0 (by norm_num : (1:ℝ≥0) ≠ 0)]
    exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).integrableOn
      (ae_of_all _ (fun x => (gaussianPDFReal_pos 0 1 x (by norm_num)).le))
  · exact (Integrable.fintype_prod (fun _ : Fin k => integrable_gaussianPDFReal 0 1)).integrableOn
  · exact ae_of_all _ (fun y => Finset.prod_nonneg (fun i _ => (gaussianPDFReal_pos 0 1 (y i) (by norm_num)).le))



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.ConditionalLaw
attribute [-instance] _root_.OAI.CurrentProjection.endingRowLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.gaussianObservation_probability _root_.OAI.CurrentProjection.gaussianObservations_probability _root_.OAI.CurrentProjection.prefixLaw_probability _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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


lemma dependentMapKernel_markov {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (κ : Kernel A B) [IsMarkovKernel κ] (f : A×B → D)
    (hf : Measurable f) : IsMarkovKernel (dependentMapKernel κ f) :=
  Kernel.IsMarkovKernel.map _ hf

lemma dependentMapKernel_apply {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (κ : Kernel A B) [IsSFiniteKernel κ] (f : A×B → D)
    (hf : Measurable f) (a : A) : dependentMapKernel κ f a = (κ a).map (fun b => f (a,b)) := by
  rw [dependentMapKernel,Kernel.map_apply _ hf,Kernel.prod_apply,Kernel.id_apply,
    Measure.dirac_prod,Measure.map_map hf (measurable_prodMk_left (x:=a))]
  rfl

instance scalarProjectionKernel_markov {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] : IsMarkovKernel (scalarProjectionKernel κ) :=
  dependentMapKernel_markov _ _ (by fun_prop)



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.FiberModel
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





lemma measurable_fiberObservationMap {d k : ℕ} :
    Measurable (fun z : Rows k d×Sphere d => ((z.1,label z.1 (z.2:Vector d)),z.2)) :=
  (measurable_fst.prodMk measurable_own_label).prodMk measurable_snd



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.FiberGeometry
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



section GaussianDirection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

omit finiteDimensionalRealE measurableSpaceE borelSpaceE in
lemma directionComplement_apply (u g : E) : directionComplement u g = g - ⟪u,g⟫ • u := rfl

omit finiteDimensionalRealE measurableSpaceE borelSpaceE in
lemma directionComplement_inner (u g y : E) :
    ⟪y,directionComplement u g⟫ = ⟪y-⟪u,y⟫ • u,g⟫ := by
  simp only [directionComplement_apply,inner_sub_right,inner_smul_right,inner_sub_left,
    inner_smul_left,conj_trivial,real_inner_comm u y]
  ring

lemma gaussian_direction_indep {u : E} (hu : ‖u‖ = 1) :
    IndepFun (fun g : E => ⟪u,g⟫) (directionComplement u) (stdGaussian E) := by
  have hG := (IsGaussian.hasGaussianLaw_id (μ:=stdGaussian E)).map_fun
    ((innerSL ℝ u).prod (directionComplement u))
  change HasGaussianLaw (fun g : E => (⟪u,g⟫,directionComplement u g)) (stdGaussian E) at hG
  apply hG.indepFun_of_covariance_inner
  intro x y
  have he : (fun g : E => ⟪x,⟪u,g⟫⟫) = fun g => ⟪x • u,g⟫ := by
    funext g
    simp only [Real.inner_apply,inner_smul_left,conj_trivial]
  simp_rw [he,directionComplement_inner]
  rw [←covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,covarianceBilin_stdGaussian]
  change ⟪x • u,y-⟪u,y⟫ • u⟫ = 0
  simp only [inner_smul_left,conj_trivial,inner_sub_right,inner_smul_right,
    real_inner_self_eq_norm_sq,hu,one_pow,mul_one]
  ring

lemma gaussian_direction_real {u : E} (hu : ‖u‖ = 1) :
    (stdGaussian E).map (fun g => ⟪u,g⟫) = gaussianReal 0 1 := by
  have hG := (IsGaussian.hasGaussianLaw_id (μ:=stdGaussian E)).map_fun (innerSL ℝ u)
  change HasGaussianLaw (fun g : E => ⟪u,g⟫) (stdGaussian E) at hG
  rw [hG.map_eq_gaussianReal]
  have hi : (∫ g : E, ⟪u,g⟫ ∂stdGaussian E) = 0 := integral_strongDual_stdGaussian (innerSL ℝ u)
  have hv : Var[fun g : E => ⟪u,g⟫; stdGaussian E] = 1 := by
    rw [←covariance_self (by fun_prop),←covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian,innerSL_apply_apply,real_inner_self_eq_norm_sq,hu,one_pow]
  simp only [hi,hv,Real.toNNReal_one]

lemma gaussian_direction_split {u : E} (hu : ‖u‖ = 1) :
    (stdGaussian E).map (fun g => (⟪u,g⟫,directionComplement u g)) =
      (gaussianReal 0 1).prod ((stdGaussian E).map (directionComplement u)) := by
  rw [(gaussian_direction_indep hu).map_prod_eq_prod_map_map (by fun_prop) (by fun_prop),
    gaussian_direction_real hu]

end GaussianDirection

section GaussianDirectionRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_direction_rows_split {u : E} (hu : ‖u‖ = 1) (k : ℕ) :
    (Measure.pi (fun _ : Fin k => stdGaussian E)).map
      (fun G => ((fun i => ⟪u,G i⟫),(fun i => directionComplement u (G i)))) =
      (Measure.pi (fun _ : Fin k => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin k => (stdGaussian E).map (directionComplement u))) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ E (Fin k)
  have he : (fun G : Fin k→E => ((fun i => ⟪u,G i⟫),(fun i => directionComplement u (G i)))) =
      e ∘ (fun G => fun i => (⟪u,G i⟫,directionComplement u (G i))) := rfl
  rw [he,←Measure.map_map e.measurable (by fun_prop),
    Measure.pi_map_pi (f := fun (_ : Fin k) => fun g : E => (⟪u,g⟫,directionComplement u g))
      (μ := fun _ => stdGaussian E) (fun i => by fun_prop)]
  simp_rw [gaussian_direction_split hu]
  exact (measurePreserving_arrowProdEquivProdArrow ℝ E (Fin k)
    (fun _ => gaussianReal 0 1) (fun _ => (stdGaussian E).map (directionComplement u))).map_eq

lemma gaussian_direction_rows_recover {u : E} (hu : ‖u‖ = 1) (k : ℕ) :
    ((Measure.pi (fun _ : Fin k => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin k => (stdGaussian E).map (directionComplement u)))).map
      (fun z => fun i => z.1 i • u+z.2 i) = Measure.pi (fun _ : Fin k => stdGaussian E) := by
  rw [←gaussian_direction_rows_split hu k,Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun z : (Fin k→ℝ)×(Fin k→E) => fun i => z.1 i • u+z.2 i) ∘
      (fun G : Fin k→E => ((fun i => ⟪u,G i⟫),(fun i => directionComplement u (G i)))) = id := by
    funext G i
    simp [directionComplement_apply]
  rw [he,Measure.map_id]
end GaussianDirectionRows




section FiberAverage
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X)

lemma tendsto_normalized_closedBall {f : X → ℝ≥0∞} {x : X}
    (hf : ContinuousAt f x)
    (hvol : ∀ r : ℝ, 0 < r → μ (Metric.closedBall x r) ≠ 0 ∧
      μ (Metric.closedBall x r) ≠ ∞) :
    Tendsto (fun r : ℝ => (μ (Metric.closedBall x r))⁻¹ *
      ∫⁻ y in Metric.closedBall x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨b,hab,hb⟩ := exists_between ha
    have hnb : {y | b < f y} ∈ 𝓝 x := hf (Ioi_mem_nhds hb)
    have he : ∀ᶠ r in 𝓝[>] (0:ℝ), Metric.closedBall x r ⊆ _ :=
      (eventually_closedBall_subset hnb).filter_mono inf_le_left
    filter_upwards [he, self_mem_nhdsWithin] with r hr hr0
    have hv := hvol r hr0
    apply hab.trans_le
    calc
      b = (μ (Metric.closedBall x r))⁻¹ * (b * μ (Metric.closedBall x r)) := by
        rw [mul_left_comm, ENNReal.inv_mul_cancel hv.1 hv.2, mul_one]
      _ ≤ _ := mul_le_mul_right (by
        rw [←setLIntegral_const]
        apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
        intro y hy
        exact (hr hy).le) _
  · intro a ha
    obtain ⟨b,hb,hba⟩ := exists_between ha
    have hnb : {y | f y < b} ∈ 𝓝 x := hf (Iio_mem_nhds hb)
    have he : ∀ᶠ r in 𝓝[>] (0:ℝ), Metric.closedBall x r ⊆ _ :=
      (eventually_closedBall_subset hnb).filter_mono inf_le_left
    filter_upwards [he, self_mem_nhdsWithin] with r hr hr0
    have hv := hvol r hr0
    apply lt_of_le_of_lt _ hba
    calc
      _ ≤ (μ (Metric.closedBall x r))⁻¹ * (b * μ (Metric.closedBall x r)) := by
        apply mul_le_mul_right
        rw [←setLIntegral_const]
        apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
        intro y hy
        exact (hr hy).le
      _ = b := by rw [mul_left_comm, ENNReal.inv_mul_cancel hv.1 hv.2,mul_one]
end FiberAverage

lemma ennreal_double_mul_le_sq_add (a b : ℝ≥0∞) : 2*(a*b) ≤ a^2+b^2 := by
  have h := ENNReal.young_inequality a b Real.HolderConjugate.two_two
  norm_num only [ENNReal.rpow_two,ENNReal.ofReal_ofNat] at h
  calc
    _ ≤ 2*(a^2/2+b^2/2) := mul_le_mul_right h 2
    _ = _ := by
      rw [mul_add,div_eq_mul_inv,div_eq_mul_inv]
      rw [mul_left_comm 2, mul_left_comm 2]
      rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      simp

lemma cube_energy_contraction {k : ℕ} (p K : (Fin k → ℝ) → ℝ≥0∞)
    (hp : Measurable p) (hK : Measurable K) (hKn : ∫⁻ z, K z = 1) :
    (∫⁻ x, ∫⁻ y, p x*p y*K (y-x)) ≤ ∫⁻ x, p x^2 := by
  have hA : (∫⁻ x, ∫⁻ y, p x^2*K (y-x)) = ∫⁻ x, p x^2 := by
    congr 1
    funext x
    rw [lintegral_const_mul _ (show Measurable (fun y => K (y-x)) by fun_prop),
      lintegral_sub_right_eq_self,hKn,mul_one]
  have hB : (∫⁻ x, ∫⁻ y, p y^2*K (y-x)) = ∫⁻ y, p y^2 := by
    rw [lintegral_lintegral_swap (by fun_prop)]
    congr 1
    funext y
    rw [lintegral_const_mul _ (show Measurable (fun x => K (y-x)) by fun_prop),
      lintegral_sub_left_eq_self,hKn,mul_one]
  have he : 2*(∫⁻ x, ∫⁻ y, p x*p y*K (y-x)) ≤ 2*(∫⁻ x, p x^2) := by
    calc
      _ = ∫⁻ x, ∫⁻ y, 2*(p x*p y)*K (y-x) := by
        simp_rw [mul_assoc,lintegral_const_mul' (2:ℝ≥0∞) _ (by norm_num)]
      _ ≤ ∫⁻ x, ∫⁻ y, (p x^2+p y^2)*K (y-x) := by
        apply lintegral_mono
        intro x
        apply lintegral_mono
        intro y
        exact mul_le_mul_left (ennreal_double_mul_le_sq_add _ _) _
      _ = (∫⁻ x, ∫⁻ y, p x^2*K (y-x)) + (∫⁻ x, ∫⁻ y, p y^2*K (y-x)) := by
        simp_rw [add_mul]
        rw [show (fun x => ∫⁻ y, p x^2*K (y-x)+p y^2*K (y-x)) =
          (fun x => (∫⁻ y, p x^2*K (y-x))+(∫⁻ y, p y^2*K (y-x))) by
            funext x; exact lintegral_add_left (by fun_prop) _]
        exact lintegral_add_left (by fun_prop) _
      _ = _ := by rw [hA,hB,two_mul]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num)).mp he



lemma continuous_lintegral_bounded {A X : Type*} [TopologicalSpace A] [FirstCountableTopology A]
    [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (f : A → X → ℝ≥0∞) (hf : ∀ x, Continuous (fun a => f a x))
    (hm : ∀ a, Measurable (f a)) (M : ℝ≥0∞) (hM : M ≠ ∞)
    (hb : ∀ a x, f a x ≤ M) : Continuous (fun a => ∫⁻ x, f a x ∂μ) := by
  apply continuous_iff_continuousAt.2
  intro a
  exact tendsto_lintegral_filter_of_dominated_convergence (fun _ => M)
    (Eventually.of_forall hm) (Eventually.of_forall (fun a => ae_of_all _ (hb a)))
    (by simp only [lintegral_const]; exact ENNReal.mul_ne_top hM (measure_ne_top _ _))
    (ae_of_all _ (fun x => (hf x).continuousAt))

lemma tendsto_scaled_cube_average {k : ℕ} (F : (Fin k→ℝ) → ℝ≥0∞)
    (hF : ContinuousAt F 0) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun δ : ℝ => ENNReal.ofReal ((2*δ)⁻¹ ^ k) *
      ∫⁻ z in Metric.closedBall (0 : Fin k→ℝ) (δ/r), F z)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (r⁻¹ ^ k) * F 0)) := by
  have hv : ∀ a : ℝ, 0 < a →
      (volume : Measure (Fin k→ℝ)) (Metric.closedBall 0 a) ≠ 0 ∧
      (volume : Measure (Fin k→ℝ)) (Metric.closedBall 0 a) ≠ ∞ := by
    intro a ha
    rw [Real.volume_pi_closedBall 0 ha.le]
    constructor
    · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    · exact ENNReal.ofReal_ne_top
  have hz : Tendsto (fun δ : ℝ => δ/r) (𝓝[>] (0:ℝ)) (𝓝 (0/r)) :=
    ((tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 (0:ℝ)) (𝓝 (0:ℝ))).mono_left
      (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from inf_le_left)).div_const r
  rw [zero_div] at hz
  have ht := (tendsto_normalized_closedBall volume hF hv).comp
    (show Tendsto (fun δ : ℝ => δ/r) (𝓝[>] 0) (𝓝[>] 0) from
      tendsto_nhdsWithin_iff.2 ⟨hz,
        by filter_upwards [self_mem_nhdsWithin] with δ hδ; exact div_pos hδ hr⟩)
  have ht' := ENNReal.Tendsto.const_mul ht (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (r⁻¹ ^ k) ≠ ∞))
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  dsimp only [Function.comp_def]
  rw [Real.volume_pi_closedBall 0 (div_nonneg hδ.le hr.le)]
  simp only [Fintype.card_fin]
  rw [←mul_assoc]
  congr 1
  rw [←ENNReal.ofReal_inv_of_pos (by positivity : (0:ℝ) < (2*(δ/r))^k),
    ←ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [inv_pow]
  rw [←mul_inv_rev,←mul_pow]
  congr 2
  field_simp

section GaussianSlab
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

lemma gaussian_reconstruct_law {u : E} (hu : ‖u‖ = 1) (k : ℕ) :
    ((Measure.pi (fun _ : Fin k => gaussianReal 0 1)).prod
      (Measure.pi (fun _ : Fin k => stdGaussian E))).map (gaussianReconstruct u) =
      Measure.pi (fun _ : Fin k => stdGaussian E) := by
  have hm : Measurable (fun G : Fin k→E => fun i => directionComplement u (G i)) := by fun_prop
  have he := Measure.pi_map_pi (μ := fun _ : Fin k => stdGaussian E)
    (f := fun _ => directionComplement u) (fun _ => (directionComplement u).measurable.aemeasurable)
  calc
    _ = (((Measure.pi (fun _ : Fin k => gaussianReal 0 1)).prod
      ((Measure.pi (fun _ : Fin k => stdGaussian E)).map
        (fun G => fun i => directionComplement u (G i)))).map
        (fun z => fun i => z.1 i • u+z.2 i)) := by
      rw [show Measure.pi (fun _ : Fin k => gaussianReal 0 1) =
        (Measure.pi (fun _ : Fin k => gaussianReal 0 1)).map id by rw [Measure.map_id],
        Measure.map_prod_map _ _ measurable_id hm,
        Measure.map_map (by fun_prop) (by fun_prop)]
      rw [Measure.map_id]
      rfl
    _ = _ := by rw [he]; exact gaussian_direction_rows_recover hu k

omit finiteDimensionalRealE measurableSpaceE borelSpaceE in
lemma gaussian_reconstruct_pairing {u : E} (hu : ‖u‖ = 1) {k : ℕ}
    (zG : (Fin k→ℝ)×(Fin k→E)) (i : Fin k) :
    ⟪u,gaussianReconstruct u zG i⟫ = zG.1 i := by
  simp [gaussianReconstruct,directionComplement_apply,inner_add_right,
    inner_sub_right,inner_smul_right,hu]

lemma continuous_gaussian_slice {u : E} {k : ℕ} (H : BoundedContinuousFunction (Fin k→E) ℝ≥0) :
    Continuous (fun z : Fin k→ℝ => ∫⁻ G : Fin k→E,
      (H (gaussianReconstruct u (z,G)) : ℝ≥0∞) ∂Measure.pi (fun _ => stdGaussian E)) := by
  apply continuous_lintegral_bounded _ (fun G => by
    apply ENNReal.continuous_coe.comp
    exact H.continuous.comp (by unfold gaussianReconstruct; fun_prop))
    (fun z => by apply ENNReal.continuous_coe.measurable.comp
                 exact H.continuous.measurable.comp (by unfold gaussianReconstruct; fun_prop))
    ((nndist H 0 : ℝ≥0) : ℝ≥0∞) ENNReal.coe_ne_top
  intro z G
  apply ENNReal.coe_le_coe.mpr
  simpa using (BoundedContinuousFunction.nndist_coe_le_nndist (f:=H) (g:=0) (gaussianReconstruct u (z,G)))
end GaussianSlab




lemma fiberEnergyBound_ne_top (d : ℕ) : fiberEnergyBound d ≠ ∞ := ENNReal.ofReal_ne_top

lemma uniformSphere_ae_ne {d : ℕ} (hd : 2 ≤ d) (s : Sphere d) :
    ∀ᵐ t ∂uniformSphere d, t ≠ s := by
  have hz := (uniformSphere_growth (by omega : 1 ≤ d) (le_refl (d-1))).sphereLift.affine_span_null
    (by positivity) (⊥ : Submodule ℝ (Vector d)) (s:Vector d) (by simp; omega)
    (sphereLift_ae_norm_sub_le (uniformSphere d) s)
  simp only [Submodule.mem_bot,sub_eq_zero] at hz
  rw [sphereLift,Measure.map_apply continuous_subtype_val.measurable (show MeasurableSet {u : Vector d | u = (s:Vector d)} from isClosed_eq continuous_id continuous_const |>.measurableSet)] at hz
  simpa only [ae_iff,not_not,Set.preimage_ofPred_eq,Subtype.val_inj] using hz

lemma spherical_inverse_bound {d k : ℕ} (hk : 1 ≤ k) (hkd : k < d-1)
    (s : Sphere d) :
    (∫⁻ t : Sphere d, ENNReal.ofReal (‖(t:Vector d)-(s:Vector d)‖⁻¹ ^ k)
      ∂uniformSphere d) ≤ fiberEnergyBound d := by
  have hB : AmbientGrowth (sphereLift (uniformSphere d)) (0+k) (3*4^d) := by
    simpa only [zero_add] using (uniformSphere_growth (by omega : 1 ≤ d) hkd.le).sphereLift
  have hh := hB.mixed_inverse_uniform
    ((uniformSphere_growth (by omega : 1 ≤ d) (le_refl (d-1))).sphereLift)
    (by positivity) (by positivity) (m:=0) (by simpa using hkd) (Nat.sub_le d 1)
    (⊥ : Submodule ℝ (Vector d)) (s:Vector d) (by simpa using hk)
    (sphereLift_ae_norm_sub_le (uniformSphere d) s)
  rw [sphereLift,lintegral_map (measurable_mixedInverse _ _ _ _) continuous_subtype_val.measurable] at hh
  simpa only [mixedInverse,pow_zero,mul_one,fiberEnergyBound] using hh

lemma spherical_cube_expectation {d k : ℕ} (hk : 1 ≤ k) (hkd : k < d-1)
    (s : Sphere d) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ C, cubeAverage (uniformSphere d) C (label C (s:Vector d)) δ
      ∂gaussianRows k d) ≤ fiberEnergyBound d := by
  have he : ∀ C : Rows k d, cubeAverage (uniformSphere d) C (label C (s:Vector d)) δ =
      ∫⁻ t : Sphere d, rowKernel (cubeKernel δ) (s:Vector d) (t:Vector d) C ∂uniformSphere d := by
    intro C
    rw [cubeAverage_eq_kernel _ _ hδ.le,sphereLift,
      lintegral_map (measurable_rowKernel_left _ (measurable_cubeKernel δ) _ _ C)
        continuous_subtype_val.measurable]
  simp_rw [he]
  have hK := measurable_cubeKernel δ
  rw [lintegral_lintegral_swap (by dsimp [rowKernel]; fun_prop)]
  apply le_trans _ (spherical_inverse_bound hk hkd s)
  apply lintegral_mono_ae
  filter_upwards [uniformSphere_ae_ne (by omega) s] with t ht
  exact gaussian_fresh_kernel_bound (cubeKernel δ) (measurable_cubeKernel δ)
    (lintegral_cubeKernel hδ) k (s:Vector d) (t:Vector d) (Subtype.coe_injective.ne ht)

lemma spherical_extended_energy {d k : ℕ} (hk : 1 ≤ k) (hkd : k < d-1) :
    (∫⁻ z : Rows k d×Sphere d,
      extendedCubeDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d))
      ∂(gaussianRows k d).prod (uniformSphere d)) ≤ fiberEnergyBound d := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  change (∫⁻ z, liminf (fun j : ℕ => cubeAverage (uniformSphere d) z.1
    (label z.1 (z.2:Vector d)) (1/(j:ℝ))) atTop
    ∂(gaussianRows k d).prod (uniformSphere d)) ≤ _
  apply (lintegral_liminf_le (fun j => measurable_own_cube (uniformSphere d) _)).trans
  apply liminf_le_of_frequently_le'
  apply Eventually.frequently
  filter_upwards [eventually_ge_atTop 1] with j hj
  rw [lintegral_prod _ (measurable_own_cube (k:=k) (uniformSphere d) _).aemeasurable,
    lintegral_lintegral_swap (measurable_own_cube (k:=k) (uniformSphere d) _).aemeasurable]
  calc
    _ ≤ ∫⁻ s : Sphere d, fiberEnergyBound d ∂uniformSphere d := by
      apply lintegral_mono
      intro s
      exact spherical_cube_expectation hk hkd s (by positivity)
    _ = _ := by simp

lemma spherical_projection_ac {d k : ℕ} (hk : 1 ≤ k) (hkd : k < d-1) :
    ∀ᵐ C ∂gaussianRows k d, labelLaw (uniformSphere d) C ≪ volume := by
  have hf := ae_lt_top (measurable_own_extended (k:=k) (uniformSphere d))
    (ne_of_lt (lt_of_le_of_lt (spherical_extended_energy hk hkd) (lt_top_iff_ne_top.mpr (fiberEnergyBound_ne_top d))))
  have hff := Measure.ae_ae_of_ae_prod hf
  filter_upwards [hff] with C hC
  exact labelLaw_ac_of_finite_extended (uniformSphere d) C hC




lemma projection_convolution_contraction {k : ℕ} (μ : Measure (Fin k→ℝ))
    (p K : (Fin k→ℝ) → ℝ≥0∞) (hp : Measurable p) (hK : Measurable K)
    (hμ : volume.withDensity p = μ) (hKn : ∫⁻ z, K z = 1) :
    (∫⁻ x, ∫⁻ y, K (y-x) ∂μ ∂μ) ≤ ∫⁻ x, p x ∂μ := by
  rw [←hμ]
  have hi (x : Fin k→ℝ) : (∫⁻ y, K (y-x) ∂volume.withDensity p) =
      ∫⁻ y, p y*K (y-x) := by
    exact lintegral_withDensity_eq_lintegral_mul _ hp (by fun_prop)
  simp_rw [hi]
  rw [lintegral_withDensity_eq_lintegral_mul _ hp (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hp hp]
  simp only [Pi.mul_apply]
  have he : (∫⁻ x, p x*(∫⁻ y, p y*K (y-x))) =
      ∫⁻ x, ∫⁻ y, p x*p y*K (y-x) := by
    congr 1
    funext x
    rw [←lintegral_const_mul _ (show Measurable (fun y => p y*K (y-x)) by fun_prop)]
    simp only [mul_assoc]
  rw [he]
  simpa only [pow_two] using cube_energy_contraction p K hp hK hKn

lemma cubeVectorKernel_normalized {k : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ z : Fin k→ℝ, ∏ i, cubeKernel δ (z i)) = 1 := by
  rw [volume_pi,lintegral_fin_prod (volume : Measure ℝ) k (fun _ => cubeKernel δ) (fun _ => (measurable_cubeKernel δ))]
  simp [lintegral_cubeKernel hδ]

lemma cubeAverage_labelKernel {d k : ℕ} (ρ : Measure (Sphere d)) (C : Rows k d)
    {δ : ℝ} (hδ : 0 < δ) (s : Sphere d) :
    cubeAverage ρ C (label C (s:Vector d)) δ =
      ∫⁻ y, ∏ i, cubeKernel δ (y i-label C (s:Vector d) i) ∂labelLaw ρ C := by
  rw [cubeAverage_eq_kernel _ _ hδ.le,sphereLift,labelLaw,
    lintegral_map (measurable_rowKernel_left _ (measurable_cubeKernel δ) _ _ C) continuous_subtype_val.measurable,
    lintegral_map (by have := measurable_cubeKernel δ; fun_prop) (by unfold label; fun_prop)]
  congr 1
  funext t
  simp only [rowKernel,label,inner_sub_left]

lemma spherical_cube_energy_eq {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (C : Rows k d) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ s : Sphere d, cubeAverage ρ C (label C (s:Vector d)) δ ∂ρ) =
      ∫⁻ x, ∫⁻ y, (∏ i, cubeKernel δ ((y-x) i)) ∂labelLaw ρ C ∂labelLaw ρ C := by
  have hK : Measurable (fun z : Fin k→ℝ => ∏ i, cubeKernel δ (z i)) := by
    have := measurable_cubeKernel δ
    fun_prop
  have hf : Measurable (fun s : Sphere d => label C (s:Vector d)) := by unfold label; fun_prop
  have hm : Measurable (fun x : Fin k→ℝ => ∫⁻ y,
      (∏ i, cubeKernel δ ((y-x) i)) ∂labelLaw ρ C) :=
    Measurable.lintegral_prod_right (hK.comp (measurable_snd.sub measurable_fst))
  calc
    _ = ∫⁻ s : Sphere d, ∫⁻ y, (∏ i, cubeKernel δ ((y-label C (s:Vector d)) i)) ∂labelLaw ρ C ∂ρ := by
      apply lintegral_congr
      intro s
      exact cubeAverage_labelKernel ρ C hδ s
    _ = _ := (lintegral_map hm hf).symm

lemma lintegral_labelLaw {d k : ℕ} (ρ : Measure (Sphere d)) (C : Rows k d)
    (f : (Fin k→ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, f y ∂labelLaw ρ C) = ∫⁻ s : Sphere d, f (label C (s:Vector d)) ∂ρ :=
  lintegral_map hf (by unfold label; fun_prop)

lemma spherical_cube_energy_le {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (C : Rows k d) (hC : labelLaw ρ C ≪ volume) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ s : Sphere d, cubeAverage ρ C (label C (s:Vector d)) δ ∂ρ) ≤
      ∫⁻ s : Sphere d, exactDensity ρ C (label C (s:Vector d)) ∂ρ := by
  have hpair : Measurable (fun y : Fin k→ℝ => (C,y)) := measurable_const.prodMk measurable_id
  have hp := (measurable_exactDensity (k:=k) ρ).comp hpair
  change Measurable (fun y : Fin k→ℝ => exactDensity ρ C y) at hp
  have hK : Measurable (fun z : Fin k→ℝ => ∏ i, cubeKernel δ (z i)) := by
    have := measurable_cubeKernel δ
    fun_prop
  rw [spherical_cube_energy_eq ρ C hδ]
  calc
    _ ≤ ∫⁻ y, exactDensity ρ C y ∂labelLaw ρ C :=
      projection_convolution_contraction (labelLaw ρ C) (fun y => exactDensity ρ C y)
        (fun z => ∏ i, cubeKernel δ (z i)) hp hK
        (labelLaw_withDensity_exact ρ C hC) (cubeVectorKernel_normalized (k:=k) hδ)
    _ = _ := lintegral_labelLaw ρ C _ hp

lemma spherical_quadratic_limit {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (hAC : ∀ᵐ C ∂gaussianRows k d, labelLaw ρ C ≪ volume) :
    Tendsto (fun j : ℕ => ∫⁻ z : Rows k d×Sphere d,
      (H z.1 : ℝ≥0∞)*cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) (1/(j:ℝ))
      ∂(gaussianRows k d).prod ρ) atTop
      (𝓝 (∫⁻ z : Rows k d×Sphere d, (H z.1 : ℝ≥0∞)*exactDensity ρ z.1 (label z.1 (z.2:Vector d))
        ∂(gaussianRows k d).prod ρ)) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  have hm (j : ℕ) : Measurable (fun z : Rows k d×Sphere d =>
      (H z.1 : ℝ≥0∞)*cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) (1/(j:ℝ))) :=
    (hH.comp measurable_fst).mul (measurable_own_cube ρ _)
  have hlim : ∀ᵐ z : Rows k d×Sphere d ∂(gaussianRows k d).prod ρ,
      Tendsto (fun j : ℕ => cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) (1/(j:ℝ)))
        atTop (𝓝 (exactDensity ρ z.1 (label z.1 (z.2:Vector d)))) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun
      (fun j : ℕ => measurable_own_cube (k:=k) ρ (1/(j:ℝ))) (measurable_own_exact ρ))).mpr
    filter_upwards [hAC] with C hC
    exact ae_of_ae_map (by unfold label; fun_prop) (hC.ae_le (volume_ae_cube_limit ρ C))
  have hlow : (∫⁻ z : Rows k d×Sphere d, (H z.1 : ℝ≥0∞)*exactDensity ρ z.1 (label z.1 (z.2:Vector d))
        ∂(gaussianRows k d).prod ρ) ≤
      liminf (fun j : ℕ => ∫⁻ z : Rows k d×Sphere d,
      (H z.1 : ℝ≥0∞)*cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) (1/(j:ℝ))
      ∂(gaussianRows k d).prod ρ) atTop := by
    calc
      _ = ∫⁻ z : Rows k d×Sphere d, liminf (fun j : ℕ =>
          (H z.1 : ℝ≥0∞)*cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) (1/(j:ℝ))) atTop
          ∂(gaussianRows k d).prod ρ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with z hz
        exact (ENNReal.Tendsto.const_mul hz (Or.inr ENNReal.coe_ne_top)).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le hm
  apply tendsto_of_le_liminf_of_limsup_le hlow
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hmExact : Measurable (fun z : Rows k d×Sphere d =>
      (H z.1 : ℝ≥0∞)*exactDensity ρ z.1 (label z.1 (z.2:Vector d))) :=
    (hH.comp measurable_fst).mul (measurable_own_exact ρ)
  rw [lintegral_prod _ (hm j).aemeasurable,lintegral_prod _ hmExact.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [hAC] with C hC
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  exact mul_le_mul_right (spherical_cube_energy_le ρ C hC (by positivity)) _



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Slab
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


lemma prod_cubeKernel_scaled {k : ℕ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (z : Fin k→ℝ) :
    (∏ i, cubeKernel δ (r*z i)) =
      (Metric.closedBall (0:Fin k→ℝ) (δ/r)).indicator
        (fun _ => ENNReal.ofReal ((2*δ)⁻¹ ^ k)) z := by
  classical
  have hz : z ∈ Metric.closedBall (0:Fin k→ℝ) (δ/r) ↔ ∀ i, r*z i ∈ Icc (-δ) δ := by
    rw [Metric.mem_closedBall,dist_pi_le_iff (div_nonneg hδ.le hr.le)]
    simp only [Pi.zero_apply,dist_zero_right,Real.norm_eq_abs,mem_Icc,←abs_le]
    exact forall_congr' (fun i => by rw [abs_mul,abs_of_pos hr,le_div_iff₀ hr,mul_comm])
  by_cases h : z ∈ Metric.closedBall (0:Fin k→ℝ) (δ/r)
  · rw [indicator_of_mem h]
    simp only [cubeKernel,indicator_of_mem (hz.mp h _),Finset.prod_const,
      Finset.card_univ,Fintype.card_fin,ENNReal.ofReal_pow (by positivity : (0:ℝ)≤(2*δ)⁻¹)]
  · rw [indicator_of_notMem h]
    have hh := mt hz.mpr h
    push Not at hh
    obtain ⟨i,hi⟩ := hh
    exact Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)

section SlabLimit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

omit finiteDimensionalRealE measurableSpaceE borelSpaceE in
lemma normalized_direction {v : E} (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ = 1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

lemma gaussian_slab_formula {k : ℕ} {v : E} (hv : v ≠ 0)
    (H : BoundedContinuousFunction (Fin k→E) ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ C : Fin k→E, (H C : ℝ≥0∞)*(∏ i, cubeKernel δ ⟪v,C i⟫)
      ∂Measure.pi (fun _ => stdGaussian E)) =
    ENNReal.ofReal ((2*δ)⁻¹ ^ k) *
      ∫⁻ z in Metric.closedBall (0:Fin k→ℝ) (δ/‖v‖),
        ENNReal.ofReal (gaussianProductPDF 1 0 z) *
          ∫⁻ G : Fin k→E, (H (gaussianReconstruct (‖v‖⁻¹ • v) (z,G)) : ℝ≥0∞)
            ∂Measure.pi (fun _ => stdGaussian E) := by
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := normalized_direction hv
  have hvu : v = ‖v‖ • u := by
    dsimp [u]
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul]
  have hpair (zG : (Fin k→ℝ)×(Fin k→E)) (i : Fin k) :
      ⟪v,gaussianReconstruct u zG i⟫ = ‖v‖*zG.1 i := by
    conv_lhs => rw [hvu]
    rw [inner_smul_left,conj_trivial,gaussian_reconstruct_pairing hu]
  have hK := measurable_cubeKernel δ
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  calc
    _ = ∫⁻ zG : (Fin k→ℝ)×(Fin k→E),
        (H (gaussianReconstruct u zG) : ℝ≥0∞) *
          ∏ i, cubeKernel δ (‖v‖*zG.1 i)
        ∂(gaussianLabels k).prod (Measure.pi (fun _ => stdGaussian E)) := by
      conv_lhs => rw [←gaussian_reconstruct_law hu k]
      rw [lintegral_map (by fun_prop) (by unfold gaussianReconstruct; fun_prop)]
      simp_rw [hpair]
      rfl
    _ = ∫⁻ z : Fin k→ℝ, (∏ i, cubeKernel δ (‖v‖*z i)) *
        ∫⁻ G : Fin k→E, (H (gaussianReconstruct u (z,G)) : ℝ≥0∞)
          ∂Measure.pi (fun _ => stdGaussian E) ∂gaussianLabels k := by
      rw [lintegral_prod _ (by unfold gaussianReconstruct; fun_prop)]
      congr 1
      funext z
      simp only
      have hHz : Measurable (fun G : Fin k→E => (H (gaussianReconstruct u (z,G)) : ℝ≥0∞)) :=
        hH.comp (by unfold gaussianReconstruct; fun_prop)
      rw [lintegral_mul_const _ hHz,mul_comm]
    _ = _ := by
      have hp : Measurable (fun z : Fin k→ℝ => ENNReal.ofReal (gaussianProductPDF 1 0 z)) := by
        unfold gaussianProductPDF
        fun_prop
      have hs : Measurable (fun z : Fin k→ℝ => ∫⁻ G : Fin k→E,
          (H (gaussianReconstruct u (z,G)) : ℝ≥0∞) ∂Measure.pi (fun _ => stdGaussian E)) :=
        (continuous_gaussian_slice H).measurable
      rw [←gaussianLabels_density,lintegral_withDensity_eq_lintegral_mul₀ hp.aemeasurable
        (show Measurable (fun z : Fin k→ℝ => (∏ i, cubeKernel δ (‖v‖*z i)) *
          ∫⁻ G : Fin k→E, (H (gaussianReconstruct u (z,G)) : ℝ≥0∞)
            ∂Measure.pi (fun _ => stdGaussian E)) from
          (by exact (by fun_prop : Measurable (fun z : Fin k→ℝ => ∏ i, cubeKernel δ (‖v‖*z i))).mul hs)).aemeasurable]
      simp only [Pi.mul_apply]
      simp_rw [prod_cubeKernel_scaled (norm_pos_iff.mpr hv) hδ]
      rw [show (fun z : Fin k→ℝ => ENNReal.ofReal (gaussianProductPDF 1 0 z) *
          ((Metric.closedBall (0:Fin k→ℝ) (δ/‖v‖)).indicator (fun _ => ENNReal.ofReal ((2*δ)⁻¹^k)) z *
          ∫⁻ G : Fin k→E, (H (gaussianReconstruct u (z,G)) : ℝ≥0∞) ∂Measure.pi (fun _ => stdGaussian E))) =
        (Metric.closedBall (0:Fin k→ℝ) (δ/‖v‖)).indicator
          (fun z => ENNReal.ofReal ((2*δ)⁻¹^k) *
            (ENNReal.ofReal (gaussianProductPDF 1 0 z) *
            ∫⁻ G : Fin k→E, (H (gaussianReconstruct u (z,G)) : ℝ≥0∞) ∂Measure.pi (fun _ => stdGaussian E))) by
        funext z
        by_cases hz : z ∈ Metric.closedBall (0:Fin k→ℝ) (δ/‖v‖) <;> simp [hz,mul_left_comm]]
      rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma gaussian_slab_limit {k : ℕ} {v : E} (hv : v ≠ 0)
    (H : BoundedContinuousFunction (Fin k→E) ℝ≥0) :
    Tendsto (fun δ : ℝ => ∫⁻ C : Fin k→E, (H C : ℝ≥0∞)*(∏ i, cubeKernel δ ⟪v,C i⟫)
      ∂Measure.pi (fun _ => stdGaussian E)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (‖v‖⁻¹ ^ k) *
        (ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹ ^ k) *
        ∫⁻ G : Fin k→E, (H (fun i => directionComplement (‖v‖⁻¹ • v) (G i)) : ℝ≥0∞)
          ∂Measure.pi (fun _ => stdGaussian E)))) := by
  have hF : Continuous (fun z : Fin k→ℝ => ENNReal.ofReal (gaussianProductPDF 1 0 z) *
      ∫⁻ G : Fin k→E, (H (gaussianReconstruct (‖v‖⁻¹ • v) (z,G)) : ℝ≥0∞)
        ∂Measure.pi (fun _ => stdGaussian E)) := by
    apply Continuous.ennreal_mul
    · apply ENNReal.continuous_ofReal.comp
      unfold gaussianProductPDF gaussianPDFReal
      fun_prop
    · exact continuous_gaussian_slice H
    · intro z
      left
      exact ENNReal.ofReal_pos.mpr (by
        unfold gaussianProductPDF
        apply Finset.prod_pos
        intro i _
        apply gaussianPDFReal_pos
        exact radiusVariance_ne_zero (by norm_num)) |>.ne'
    · intro z
      exact Or.inr ENNReal.ofReal_ne_top
  have ht := tendsto_scaled_cube_average _ hF.continuousAt (norm_pos_iff.mpr hv)
  have hzero : gaussianProductPDF (k:=k) 1 0 0 = (Real.sqrt (2*Real.pi))⁻¹ ^ k := by
    simp only [gaussianProductPDF,gaussianPDFReal,radiusVariance,Pi.zero_apply,
      one_pow,sub_zero,zero_pow (by norm_num : 2 ≠ 0),neg_zero,
      zero_div,Real.exp_zero,mul_one,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    change (Real.sqrt (2*Real.pi*1))⁻¹ ^ k = _
    rw [mul_one]
  rw [hzero] at ht
  have hz (G : Fin k→E) : gaussianReconstruct (‖v‖⁻¹ • v) ((0:Fin k→ℝ), G) =
      (fun i => directionComplement (‖v‖⁻¹ • v) (G i)) := by
    funext i
    simp [gaussianReconstruct]
  simp_rw [hz] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (gaussian_slab_formula hv H hδ).symm
end SlabLimit



lemma measurable_fiberPairInverse {d k : ℕ} : Measurable (fiberPairInverse (d:=d) k) := by
  unfold fiberPairInverse
  fun_prop

lemma measurable_fiberSlab {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0) (δ : ℝ) :
    Measurable (fiberSlab H δ) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  have hK := measurable_cubeKernel δ
  apply Measurable.lintegral_prod_right
  unfold rowKernel
  fun_prop

lemma measurable_fiberPerpendicularTest {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0) :
    Measurable (fiberPerpendicularTest H) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  apply Measurable.lintegral_prod_right
  apply hH.comp
  unfold perpendicularRow
  fun_prop

lemma normalized_complement_perpendicular {d : ℕ} (v g : Vector d) :
    directionComplement (‖v‖⁻¹ • v) g = perpendicularRow v g := by
  simp only [directionComplement_apply,inner_smul_left,conj_trivial,smul_smul,perpendicularRow]
  congr 2
  rw [div_eq_mul_inv,←inv_pow]
  ring

lemma fiberSlab_limit {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    {z : Sphere d×Sphere d} (hz : z.1 ≠ z.2) :
    Tendsto (fun δ : ℝ => fiberSlab H δ z) (𝓝[>] 0)
      (𝓝 (fiberPairInverse k z * (fiberTwoPointConstant k * fiberPerpendicularTest H z))) := by
  have hv : (z.2:Vector d)-(z.1:Vector d) ≠ 0 := sub_ne_zero.mpr (Subtype.coe_injective.ne hz.symm)
  have ht := gaussian_slab_limit hv H
  simpa only [fiberSlab,fiberPairInverse,fiberTwoPointConstant,fiberPerpendicularTest,
    rowKernel,normalized_complement_perpendicular,gaussianRows] using ht

lemma fiberSlab_le {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    {δ : ℝ} (hδ : 0 < δ) {z : Sphere d×Sphere d} (hz : z.1 ≠ z.2) :
    fiberSlab H δ z ≤ (nndist H 0 : ℝ≥0∞)*fiberPairInverse k z := by
  calc
    _ ≤ ∫⁻ C, (nndist H 0 : ℝ≥0∞)*rowKernel (cubeKernel δ) (z.1:Vector d) (z.2:Vector d) C
        ∂gaussianRows k d := by
      apply lintegral_mono
      intro C
      exact mul_le_mul_left (by
        exact ENNReal.coe_le_coe.mpr (show H C ≤ nndist H 0 by
          simpa using (BoundedContinuousFunction.nndist_coe_le_nndist (f:=H) (g:=0) C))) _
    _ = (nndist H 0 : ℝ≥0∞)*(∫⁻ C, rowKernel (cubeKernel δ) (z.1:Vector d) (z.2:Vector d) C
        ∂gaussianRows k d) := lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ _ := mul_le_mul_right (gaussian_fresh_kernel_bound (cubeKernel δ) (measurable_cubeKernel δ)
      (lintegral_cubeKernel hδ) k (z.1:Vector d) (z.2:Vector d) (Subtype.coe_injective.ne hz.symm)) _

lemma fiberSlab_integrated_limit {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (hne : ∀ᵐ z ∂ρ.prod ρ, z.1 ≠ z.2)
    (hfin : (∫⁻ z, fiberPairInverse k z ∂ρ.prod ρ) ≠ ∞) :
    Tendsto (fun δ : ℝ => ∫⁻ z, fiberSlab H δ z ∂ρ.prod ρ) (𝓝[>] 0)
      (𝓝 (∫⁻ z, fiberPairInverse k z*(fiberTwoPointConstant k*fiberPerpendicularTest H z) ∂ρ.prod ρ)) := by
  apply tendsto_lintegral_filter_of_dominated_convergence
    (fun z => (nndist H 0 : ℝ≥0∞)*fiberPairInverse k z)
  · exact Eventually.of_forall (measurable_fiberSlab H)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hne.mono (fun z hz => fiberSlab_le H hδ hz)
  · rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  · exact hne.mono (fun z hz => fiberSlab_limit H hz)

lemma cubeAverage_sphereKernel {d k : ℕ} (ρ : Measure (Sphere d)) (C : Rows k d)
    {δ : ℝ} (hδ : 0 < δ) (s : Sphere d) :
    cubeAverage ρ C (label C (s:Vector d)) δ =
      ∫⁻ t : Sphere d, rowKernel (cubeKernel δ) (s:Vector d) (t:Vector d) C ∂ρ := by
  rw [cubeAverage_eq_kernel _ _ hδ.le,sphereLift,
    lintegral_map (measurable_rowKernel_left _ (measurable_cubeKernel δ) _ _ C) continuous_subtype_val.measurable]

lemma fiberSlab_tonelli {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ z : Rows k d×Sphere d, (H z.1 : ℝ≥0∞)*cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) δ
      ∂(gaussianRows k d).prod ρ) = ∫⁻ z, fiberSlab H δ z ∂ρ.prod ρ := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  have hK := measurable_cubeKernel δ
  have hm : Measurable (fun z : Rows k d×Sphere d =>
      (H z.1 : ℝ≥0∞)*cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) δ) :=
    (hH.comp measurable_fst).mul (measurable_own_cube ρ δ)
  have hm' : Measurable (fun z : Rows k d×(Sphere d×Sphere d) =>
      (H z.1 : ℝ≥0∞)*rowKernel (cubeKernel δ) (z.2.1:Vector d) (z.2.2:Vector d) z.1) := by
    unfold rowKernel
    fun_prop
  rw [lintegral_prod _ hm.aemeasurable]
  simp_rw [cubeAverage_sphereKernel ρ _ hδ]
  have he (C : Rows k d) :
      (∫⁻ s : Sphere d, (H C : ℝ≥0∞)*(∫⁻ t : Sphere d,
        rowKernel (cubeKernel δ) (s:Vector d) (t:Vector d) C ∂ρ) ∂ρ) =
      ∫⁻ z : Sphere d×Sphere d, (H C : ℝ≥0∞)*rowKernel (cubeKernel δ) (z.1:Vector d) (z.2:Vector d) C ∂ρ.prod ρ := by
    have hC : Measurable (fun z : Sphere d×Sphere d =>
        (H C : ℝ≥0∞)*rowKernel (cubeKernel δ) (z.1:Vector d) (z.2:Vector d) C) :=
      hm'.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ hC.aemeasurable]
    apply lintegral_congr
    intro s
    exact (lintegral_const_mul' _ _ ENNReal.coe_ne_top).symm
  simp_rw [he]
  exact lintegral_lintegral_swap hm'.aemeasurable

lemma spherical_energy_identity {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (hAC : ∀ᵐ C ∂gaussianRows k d, labelLaw ρ C ≪ volume)
    (hne : ∀ᵐ z ∂ρ.prod ρ, z.1 ≠ z.2)
    (hfin : (∫⁻ z, fiberPairInverse k z ∂ρ.prod ρ) ≠ ∞) :
    (∫⁻ z : Rows k d×Sphere d, (H z.1 : ℝ≥0∞)*exactDensity ρ z.1 (label z.1 (z.2:Vector d))
      ∂(gaussianRows k d).prod ρ) =
      ∫⁻ z, fiberPairInverse k z*(fiberTwoPointConstant k*fiberPerpendicularTest H z) ∂ρ.prod ρ := by
  have ht := (fiberSlab_integrated_limit ρ H hne hfin).comp tendsto_cube_scale
  apply tendsto_nhds_unique (spherical_quadratic_limit ρ H hAC)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with j hj
  exact (fiberSlab_tonelli ρ H (by positivity)).symm




lemma finite_bounded_withDensity {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    (b : A→ℝ≥0∞) (M : ℝ≥0∞) (hM : M ≠ ∞) (hbM : ∀ x, b x ≤ M) :
    IsFiniteMeasure (μ.withDensity b) := by
  apply isFiniteMeasure_withDensity
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hM (measure_ne_top μ Set.univ))
  calc
    _ ≤ ∫⁻ x, M ∂μ := lintegral_mono hbM
    _ = _ := lintegral_const M

lemma weightedSphere_pair_ne {d : ℕ} (hd : 2 ≤ d) (b : Sphere d→ℝ≥0∞) :
    ∀ᵐ z ∂((uniformSphere d).withDensity b).prod ((uniformSphere d).withDensity b), z.1 ≠ z.2 := by
  have ha : ∀ᵐ z ∂(uniformSphere d).prod (uniformSphere d), z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet {z : Sphere d×Sphere d | z.1 ≠ z.2} from (isClosed_eq continuous_fst continuous_snd).measurableSet.compl)).mpr
    exact ae_of_all _ (fun s => (uniformSphere_ae_ne hd s).mono (fun t ht => ht.symm))
  exact ((withDensity_absolutelyContinuous _ b).prod (withDensity_absolutelyContinuous _ b)).ae_le ha

lemma spherical_pair_inverse_finite {d k : ℕ} (hk : 1≤k) (hkd : k<d-1) :
    (∫⁻ z, fiberPairInverse k z ∂(uniformSphere d).prod (uniformSphere d)) ≠ ∞ := by
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (fiberEnergyBound_ne_top d) (measure_ne_top (uniformSphere d) Set.univ))
  calc
    _ = ∫⁻ s : Sphere d, ∫⁻ t : Sphere d, ENNReal.ofReal (‖(t:Vector d)-(s:Vector d)‖⁻¹ ^ k)
        ∂uniformSphere d ∂uniformSphere d := lintegral_prod _ measurable_fiberPairInverse.aemeasurable
    _ ≤ ∫⁻ s : Sphere d, fiberEnergyBound d ∂uniformSphere d :=
      lintegral_mono (spherical_inverse_bound hk hkd)
    _ = _ := lintegral_const _

lemma weightedSphere_pair_inverse_finite {d k : ℕ} (hk : 1≤k) (hkd : k<d-1)
    (b : Sphere d→ℝ≥0∞) (hb : Measurable b) (M : ℝ≥0∞) (hM : M ≠ ∞) (hbM : ∀ s, b s ≤ M) :
    (∫⁻ z, fiberPairInverse k z ∂((uniformSphere d).withDensity b).prod ((uniformSphere d).withDensity b)) ≠ ∞ := by
  rw [prod_withDensity hb hb,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : Sphere d×Sphere d => b z.1*b z.2) from
        (hb.comp measurable_fst).mul (hb.comp measurable_snd)) measurable_fiberPairInverse]
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hM hM) (spherical_pair_inverse_finite hk hkd))
  calc
    _ ≤ ∫⁻ z : Sphere d×Sphere d, (M*M)*fiberPairInverse k z ∂(uniformSphere d).prod (uniformSphere d) := by
      apply lintegral_mono
      intro z
      exact mul_le_mul_left (mul_le_mul (hbM z.1) (hbM z.2) bot_le bot_le) _
    _ = _ := lintegral_const_mul' _ _ (ENNReal.mul_ne_top hM hM)

lemma weightedSphere_projection_ac {d k : ℕ} (hk : 1≤k) (hkd : k<d-1)
    (b : Sphere d→ℝ≥0∞) :
    ∀ᵐ C ∂gaussianRows k d, labelLaw ((uniformSphere d).withDensity b) C ≪ volume := by
  filter_upwards [spherical_projection_ac hk hkd] with C hC
  exact (Measure.AbsolutelyContinuous.map (withDensity_absolutelyContinuous _ b)
      (by unfold label; fun_prop)).trans hC



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.FiberConditional
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


section PosteriorWeight
variable {O S : Type*} [MeasurableSpace O] [MeasurableSpace S]
  [StandardBorelSpace S] [Nonempty S]

lemma posterior_weight_integral (P : Measure (O×S)) [IsFiniteMeasure P]
    (b : S→ℝ≥0∞) (hb : Measurable b) (f : O→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z.1*b z.2 ∂P) =
      ∫⁻ o, f o*(∫⁻ s, b s ∂P.condKernel o) ∂P.fst := by
  have hm : Measurable (fun z : O×S => f z.1*b z.2) :=
    (hf.comp measurable_fst).mul (hb.comp measurable_snd)
  rw [←Measure.lintegral_condKernel hm]
  congr 1
  funext o
  simpa only [Prod.fst,Prod.snd] using (lintegral_const_mul (μ:=P.condKernel o) (f o) hb)

lemma posterior_weighted_fst (P : Measure (O×S)) [IsFiniteMeasure P]
    (b : S→ℝ≥0∞) (hb : Measurable b) :
    (P.withDensity (fun z : O×S => b z.2)).fst =
      P.fst.withDensity (fun o => ∫⁻ s, b s ∂P.condKernel o) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.fst,lintegral_map hf measurable_fst,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : O×S => b z.2) from hb.comp measurable_snd)
      (show Measurable (fun z : O×S => f z.1) from hf.comp measurable_fst),
    lintegral_withDensity_eq_lintegral_mul _ (hb.lintegral_kernel (κ:=P.condKernel)) hf]
  simp only [Pi.mul_apply]
  simp_rw [mul_comm (b _) (f _),mul_comm (∫⁻ s, b s ∂P.condKernel _) (f _)]
  exact posterior_weight_integral P b hb f hf
end PosteriorWeight

lemma measurable_sphericalPosteriorWeight {d k : ℕ} [Nonempty (Sphere d)]
    {b : Sphere d→ℝ≥0∞} (hb : Measurable b) : Measurable (sphericalPosteriorWeight d k b) :=
  hb.lintegral_kernel

lemma fiberObservationLaw_fst (d k : ℕ) :
    (fiberObservationLaw d k).fst = projectionJoint (uniformSphere d) (gaussianRows k d) := by
  rw [fiberObservationLaw,
    Measure.fst_map_prodMk measurable_snd]
  rfl

lemma fiberObservationLaw_weighted_fst {d k : ℕ} (b : Sphere d→ℝ≥0∞) (hb : Measurable b) :
    ((fiberObservationLaw d k).withDensity (fun z => b z.2)).fst =
      projectionJoint ((uniformSphere d).withDensity b) (gaussianRows k d) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.fst,lintegral_map hf measurable_fst,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : (Rows k d×(Fin k→ℝ))×Sphere d => b z.2) from hb.comp measurable_snd)
      (show Measurable (fun z : (Rows k d×(Fin k→ℝ))×Sphere d => f z.1) from hf.comp measurable_fst)]
  simp only [Pi.mul_apply]
  rw [fiberObservationLaw,lintegral_map
    (show Measurable (fun z : (Rows k d×(Fin k→ℝ))×Sphere d => b z.2*f z.1) from
      (hb.comp measurable_snd).mul (hf.comp measurable_fst)) measurable_fiberObservationMap]
  rw [projectionJoint,lintegral_map hf (measurable_fst.prodMk measurable_own_label),
    prod_withDensity_right hb,lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : Rows k d×Sphere d => b z.2) from hb.comp measurable_snd)
      (show Measurable (fun z : Rows k d×Sphere d => f (z.1,label z.1 (z.2:Vector d))) from
        hf.comp (measurable_fst.prodMk measurable_own_label))]
  rfl

lemma sphericalPosterior_density {d k : ℕ} [Nonempty (Sphere d)]
    (b : Sphere d→ℝ≥0∞) (hb : Measurable b)
    [IsFiniteMeasure ((uniformSphere d).withDensity b)]
    (hAC : ∀ᵐ C ∂gaussianRows k d, labelLaw (uniformSphere d) C ≪ volume) :
    (fun o : Rows k d×(Fin k→ℝ) => exactDensity ((uniformSphere d).withDensity b) o.1 o.2) =ᵐ[
      (gaussianRows k d).prod (volume : Measure (Fin k→ℝ))]
      (fun o => exactDensity (uniformSphere d) o.1 o.2 * sphericalPosteriorWeight d k b o) := by
  have hρ : ∀ᵐ C ∂gaussianRows k d, labelLaw ((uniformSphere d).withDensity b) C ≪ volume := by
    filter_upwards [hAC] with C hC
    exact (Measure.AbsolutelyContinuous.map (withDensity_absolutelyContinuous _ b)
      (by unfold label; fun_prop)).trans hC
  apply (withDensity_eq_iff_of_sigmaFinite (measurable_exactDensity _).aemeasurable
    ((measurable_exactDensity _).mul (measurable_sphericalPosteriorWeight hb)).aemeasurable).mp
  rw [projectionJoint_withDensity _ _ hρ,
    withDensity_mul _ (measurable_exactDensity _) (measurable_sphericalPosteriorWeight hb),
    projectionJoint_withDensity _ _ hAC]
  rw [←fiberObservationLaw_fst]
  change _ = (fiberObservationLaw d k).fst.withDensity
    (fun o => ∫⁻ s, b s ∂(fiberObservationLaw d k).condKernel o)
  rw [←posterior_weighted_fst _ b hb,fiberObservationLaw_weighted_fst b hb]



lemma measurable_fiberBilinearTest {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    {b a : Sphere d→ℝ≥0∞} (hb : Measurable b) (ha : Measurable a) :
    Measurable (fiberBilinearTest H b a) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  exact ((hH.comp measurable_fst).mul (hb.comp measurable_snd.fst)).mul (ha.comp measurable_snd.snd)

lemma fiberLeft_bilinear {d k : ℕ} [Nonempty (Sphere d)]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) (hb : Measurable b) (ha : Measurable a) :
    (∫⁻ z, fiberBilinearTest H b a z ∂fiberTwoPointLeft d k) =
      ∫⁻ o : Rows k d×(Fin k→ℝ), (H o.1 : ℝ≥0∞)*exactDensity (uniformSphere d) o.1 o.2 *
        sphericalPosteriorWeight d k b o * sphericalPosteriorWeight d k a o
        ∂projectionJoint (uniformSphere d) (gaussianRows k d) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  have hp := measurable_exactDensity (k:=k) (uniformSphere d)
  have hap := measurable_sphericalPosteriorWeight (d:=d) (k:=k) ha
  have hbp := measurable_sphericalPosteriorWeight (d:=d) (k:=k) hb
  have hf : Measurable (fun o : Rows k d×(Fin k→ℝ) =>
      (H o.1 : ℝ≥0∞)*exactDensity (uniformSphere d) o.1 o.2*sphericalPosteriorWeight d k a o) :=
    ((hH.comp measurable_fst).mul hp).mul hap
  have hObs : Measurable (fun z : Rows k d×Sphere d => (z.1,label z.1 (z.2:Vector d))) :=
    measurable_fst.prodMk measurable_own_label
  have hinner (z : Rows k d×Sphere d) :
      (∫⁻ t : Sphere d, (H z.1 : ℝ≥0∞)*b z.2*a t ∂sphericalFiberKernel d k (z.1,label z.1 (z.2:Vector d))) =
      (H z.1 : ℝ≥0∞)*b z.2*sphericalPosteriorWeight d k a (z.1,label z.1 (z.2:Vector d)) :=
    lintegral_const_mul _ ha
  calc
    _ = ∫⁻ z : Rows k d×Sphere d,
        exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d)) *
        ((H z.1 : ℝ≥0∞)*b z.2*sphericalPosteriorWeight d k a (z.1,label z.1 (z.2:Vector d)))
        ∂(gaussianRows k d).prod (uniformSphere d) := by
      rw [fiberTwoPointLeft,lintegral_map (measurable_fiberBilinearTest H hb ha) (by fun_prop)]
      rw [Measure.lintegral_compProd (by
        change Measurable (fun z : (Rows k d×Sphere d)×Sphere d =>
          (H z.1.1 : ℝ≥0∞)*b z.1.2*a z.2)
        fun_prop)]
      simp only [fiberBilinearTest,Kernel.comap_apply]
      simp_rw [hinner]
      exact lintegral_withDensity_eq_lintegral_mul _ (measurable_own_exact (uniformSphere d))
        (show Measurable (fun z : Rows k d×Sphere d => (H z.1 : ℝ≥0∞)*b z.2 *
          sphericalPosteriorWeight d k a (z.1,label z.1 (z.2:Vector d))) from
          ((hH.comp measurable_fst).mul (hb.comp measurable_snd)).mul (hap.comp hObs))
    _ = ∫⁻ z, ((H z.1.1 : ℝ≥0∞)*exactDensity (uniformSphere d) z.1.1 z.1.2*
        sphericalPosteriorWeight d k a z.1)*b z.2 ∂fiberObservationLaw d k := by
      rw [fiberObservationLaw,lintegral_map
        (show Measurable (fun z : (Rows k d×(Fin k→ℝ))×Sphere d =>
          ((H z.1.1 : ℝ≥0∞)*exactDensity (uniformSphere d) z.1.1 z.1.2*
          sphericalPosteriorWeight d k a z.1)*b z.2) from
          (hf.comp measurable_fst).mul (hb.comp measurable_snd)) measurable_fiberObservationMap]
      apply lintegral_congr
      intro z
      dsimp only
      ac_rfl
    _ = _ := by
      rw [posterior_weight_integral _ b hb _ hf,fiberObservationLaw_fst]
      apply lintegral_congr
      intro o
      change (H o.1 : ℝ≥0∞)*exactDensity (uniformSphere d) o.1 o.2*
        sphericalPosteriorWeight d k a o*sphericalPosteriorWeight d k b o = _
      ac_rfl

lemma fiberLeft_bilinear_comm {d k : ℕ} [Nonempty (Sphere d)]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) (hb : Measurable b) (ha : Measurable a) :
    (∫⁻ z, fiberBilinearTest H b a z ∂fiberTwoPointLeft d k) =
      ∫⁻ z, fiberBilinearTest H a b z ∂fiberTwoPointLeft d k := by
  rw [fiberLeft_bilinear H b a hb ha,fiberLeft_bilinear H a b ha hb]
  apply lintegral_congr
  intro o
  ac_rfl

lemma fiberLeft_quadratic {d k : ℕ} [Nonempty (Sphere d)]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b : Sphere d→ℝ≥0∞) (hb : Measurable b)
    [IsFiniteMeasure ((uniformSphere d).withDensity b)]
    (hAC : ∀ᵐ C ∂gaussianRows k d, labelLaw (uniformSphere d) C ≪ volume) :
    (∫⁻ z, fiberBilinearTest H b b z ∂fiberTwoPointLeft d k) =
      ∫⁻ z : Rows k d×Sphere d, (H z.1 : ℝ≥0∞)*exactDensity ((uniformSphere d).withDensity b)
        z.1 (label z.1 (z.2:Vector d)) ∂(gaussianRows k d).prod ((uniformSphere d).withDensity b) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  have hp := measurable_exactDensity (k:=k) ((uniformSphere d).withDensity b)
  have hpb := measurable_sphericalPosteriorWeight (d:=d) (k:=k) hb
  have he := sphericalPosterior_density b hb hAC
  have hE : (fun o : Rows k d×(Fin k→ℝ) => exactDensity ((uniformSphere d).withDensity b) o.1 o.2) =ᵐ[
      projectionJoint (uniformSphere d) (gaussianRows k d)]
      (fun o => exactDensity (uniformSphere d) o.1 o.2*sphericalPosteriorWeight d k b o) := by
    rw [←projectionJoint_withDensity _ _ hAC]
    exact (withDensity_absolutelyContinuous _ _).ae_le he
  rw [fiberLeft_bilinear H b b hb hb]
  calc
    _ = ∫⁻ o : Rows k d×(Fin k→ℝ), sphericalPosteriorWeight d k b o *
        ((H o.1 : ℝ≥0∞)*exactDensity ((uniformSphere d).withDensity b) o.1 o.2)
        ∂projectionJoint (uniformSphere d) (gaussianRows k d) := by
      apply lintegral_congr_ae
      filter_upwards [hE] with o ho
      rw [ho]
      ac_rfl
    _ = ∫⁻ o : Rows k d×(Fin k→ℝ), (H o.1 : ℝ≥0∞)*exactDensity ((uniformSphere d).withDensity b) o.1 o.2
        ∂projectionJoint ((uniformSphere d).withDensity b) (gaussianRows k d) := by
      rw [←fiberObservationLaw_weighted_fst b hb,posterior_weighted_fst _ b hb,
        fiberObservationLaw_fst]
      symm
      exact lintegral_withDensity_eq_lintegral_mul _ hpb
        (show Measurable (fun o : Rows k d×(Fin k→ℝ) =>
          (H o.1 : ℝ≥0∞)*exactDensity ((uniformSphere d).withDensity b) o.1 o.2) from
          (hH.comp measurable_fst).mul hp)
    _ = _ := lintegral_map
      (show Measurable (fun o : Rows k d×(Fin k→ℝ) =>
        (H o.1 : ℝ≥0∞)*exactDensity ((uniformSphere d).withDensity b) o.1 o.2) from
        (hH.comp measurable_fst).mul hp) (measurable_fst.prodMk measurable_own_label)



lemma measurable_perpendicularRowsMap (d k : ℕ) :
    Measurable (fun z : (Sphere d×Sphere d)×Rows k d =>
      fun i => perpendicularRow ((z.1.1:Vector d)-(z.1.2:Vector d)) (z.2 i)) := by
  unfold perpendicularRow
  fun_prop

instance perpendicularRowsKernel_markov (d k : ℕ) : IsMarkovKernel (perpendicularRowsKernel d k) :=
  dependentMapKernel_markov _ _ (measurable_perpendicularRowsMap d k)

lemma perpendicularRow_neg {d : ℕ} (v g : Vector d) : perpendicularRow (-v) g = perpendicularRow v g := by
  simp [perpendicularRow,neg_div,neg_smul,sub_eq_add_neg]

lemma fiberPerpendicularTest_swap {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (z : Sphere d×Sphere d) : fiberPerpendicularTest H z.swap = fiberPerpendicularTest H z := by
  unfold fiberPerpendicularTest
  change (∫⁻ C, (H (fun i => perpendicularRow ((z.1:Vector d)-(z.2:Vector d)) (C i)) : ℝ≥0∞) ∂gaussianRows k d) = _
  rw [show (z.1:Vector d)-(z.2:Vector d) = -((z.2:Vector d)-(z.1:Vector d)) by abel]
  simp only [perpendicularRow_neg]

lemma fiberPairInverse_swap {d k : ℕ} (z : Sphere d×Sphere d) :
    fiberPairInverse k z.swap = fiberPairInverse k z := by
  simp only [fiberPairInverse,Prod.swap,norm_sub_rev]

lemma measurable_fiberDistanceWeight {d k : ℕ} : Measurable (fiberDistanceWeight (d:=d) k) := by
  unfold fiberDistanceWeight
  fun_prop

lemma fiberDistanceWeight_eq {d k : ℕ} {z : Sphere d×Sphere d} (hz : z.1 ≠ z.2) :
    fiberDistanceWeight k z = fiberPairInverse k z := by
  have hv : 0 < ‖(z.2:Vector d)-(z.1:Vector d)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Subtype.coe_injective.ne hz.symm))
  rw [fiberDistanceWeight,fiberPairInverse,ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_inv_of_pos hv,norm_sub_rev (z.1:Vector d) (z.2:Vector d)]

lemma fiberDistanceWeight_ae {d k : ℕ} (hd : 2≤d) :
    fiberDistanceWeight (d:=d) k =ᵐ[(uniformSphere d).prod (uniformSphere d)] fiberPairInverse k := by
  have hne := weightedSphere_pair_ne hd (fun _ => 1)
  have hne' : ∀ᵐ z ∂(uniformSphere d).prod (uniformSphere d), z.1 ≠ z.2 := by
    simpa only [withDensity_const,one_smul] using hne
  exact hne'.mono (fun z hz => fiberDistanceWeight_eq hz)

lemma perpendicularRowsKernel_lintegral {d k : ℕ}
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0) (z : Sphere d×Sphere d) :
    (∫⁻ C, (H C : ℝ≥0∞) ∂perpendicularRowsKernel d k z) = fiberPerpendicularTest H z := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  rw [perpendicularRowsKernel,dependentMapKernel_apply _ _ (measurable_perpendicularRowsMap d k),
    Kernel.const_apply]
  rw [lintegral_map hH (show Measurable (fun C : Rows k d => fun i =>
    perpendicularRow ((z.1:Vector d)-(z.2:Vector d)) (C i)) from
    (measurable_perpendicularRowsMap d k).comp (measurable_const.prodMk measurable_id))]
  change (∫⁻ C, (H (fun i => perpendicularRow ((z.1:Vector d)-(z.2:Vector d)) (C i)) : ℝ≥0∞)
    ∂gaussianRows k d) = _
  rw [show (z.1:Vector d)-(z.2:Vector d) = -((z.2:Vector d)-(z.1:Vector d)) by abel]
  simp only [perpendicularRow_neg,fiberPerpendicularTest]

lemma fiberRight_bilinear {d k : ℕ} (hd : 2≤d)
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) (hb : Measurable b) (ha : Measurable a) :
    (∫⁻ z, fiberBilinearTest H b a z ∂fiberTwoPointRight d k) =
      ∫⁻ z : Sphere d×Sphere d, b z.1*a z.2 *
        (fiberPairInverse k z*(fiberTwoPointConstant k*fiberPerpendicularTest H z))
        ∂(uniformSphere d).prod (uniformSphere d) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  have hF := measurable_fiberBilinearTest H hb ha
  have hinner (z : Sphere d×Sphere d) :
      (∫⁻ C, fiberBilinearTest H b a (C,z) ∂perpendicularRowsKernel d k z) =
      b z.1*a z.2*fiberPerpendicularTest H z := by
    simp only [fiberBilinearTest]
    rw [show (fun C : Rows k d => (H C : ℝ≥0∞)*b z.1*a z.2) =
        (fun C => (b z.1*a z.2)*(H C : ℝ≥0∞)) by funext C; ac_rfl,
      lintegral_const_mul _ hH,perpendicularRowsKernel_lintegral]
  rw [fiberTwoPointRight,lintegral_smul_measure,smul_eq_mul,
    lintegral_map hF measurable_swap]
  have hi := Measure.lintegral_compProd
    (μ:=((uniformSphere d).prod (uniformSphere d)).withDensity (fiberDistanceWeight k))
    (κ:=perpendicularRowsKernel d k)
    (f:=fun z : (Sphere d×Sphere d)×Rows k d => fiberBilinearTest H b a z.swap)
    (hF.comp measurable_swap)
  rw [hi]
  simp only [Prod.swap]
  simp_rw [hinner]
  rw [lintegral_withDensity_eq_lintegral_mul _ measurable_fiberDistanceWeight
    (show Measurable (fun z : Sphere d×Sphere d => b z.1*a z.2*fiberPerpendicularTest H z) from
      ((hb.comp measurable_fst).mul (ha.comp measurable_snd)).mul (measurable_fiberPerpendicularTest H)),
    ←lintegral_const_mul' _ _ (show fiberTwoPointConstant k ≠ ∞ from ENNReal.ofReal_ne_top)]
  apply lintegral_congr_ae
  filter_upwards [fiberDistanceWeight_ae (k:=k) hd] with z hz
  simp only [Pi.mul_apply]
  rw [hz]
  ac_rfl

lemma fiberRight_bilinear_comm {d k : ℕ} (hd : 2≤d)
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) (hb : Measurable b) (ha : Measurable a) :
    (∫⁻ z, fiberBilinearTest H b a z ∂fiberTwoPointRight d k) =
      ∫⁻ z, fiberBilinearTest H a b z ∂fiberTwoPointRight d k := by
  rw [fiberRight_bilinear hd H b a hb ha,fiberRight_bilinear hd H a b ha hb]
  calc
    _ = ∫⁻ z : Sphere d×Sphere d, a z.swap.1*b z.swap.2*
        (fiberPairInverse k z.swap*(fiberTwoPointConstant k*fiberPerpendicularTest H z.swap))
        ∂(uniformSphere d).prod (uniformSphere d) := by
      apply lintegral_congr
      intro z
      rw [fiberPairInverse_swap, fiberPerpendicularTest_swap]
      dsimp only [Prod.swap]
      rw [mul_comm (b z.1) (a z.2)]
    _ = _ := lintegral_prod_swap (fun z : Sphere d×Sphere d => a z.1*b z.2*
      (fiberPairInverse k z*(fiberTwoPointConstant k*fiberPerpendicularTest H z)))

lemma fiberRight_quadratic {d k : ℕ} (hd : 2≤d)
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b : Sphere d→ℝ≥0∞) (hb : Measurable b) :
    (∫⁻ z, fiberBilinearTest H b b z ∂fiberTwoPointRight d k) =
      ∫⁻ z, fiberPairInverse k z*(fiberTwoPointConstant k*fiberPerpendicularTest H z)
        ∂((uniformSphere d).withDensity b).prod ((uniformSphere d).withDensity b) := by
  rw [fiberRight_bilinear hd H b b hb hb,prod_withDensity hb hb]
  symm
  exact lintegral_withDensity_eq_lintegral_mul _
    (show Measurable (fun z : Sphere d×Sphere d => b z.1*b z.2) from
      (hb.comp measurable_fst).mul (hb.comp measurable_snd))
    (show Measurable (fun z : Sphere d×Sphere d =>
      fiberPairInverse k z*(fiberTwoPointConstant k*fiberPerpendicularTest H z)) from
      measurable_fiberPairInverse.mul (measurable_const.mul (measurable_fiberPerpendicularTest H)))

lemma fiberRight_finite {d k : ℕ} (hk : 1≤k) (hkd : k<d-1) :
    IsFiniteMeasure (fiberTwoPointRight d k) := by
  have : IsFiniteMeasure (((uniformSphere d).prod (uniformSphere d)).withDensity (fiberDistanceWeight k)) := by
    apply isFiniteMeasure_withDensity
    rw [lintegral_congr_ae (fiberDistanceWeight_ae (k:=k) (by omega))]
    exact spherical_pair_inverse_finite hk hkd
  unfold fiberTwoPointRight
  exact Measure.smul_finite _ (show fiberTwoPointConstant k ≠ ∞ from ENNReal.ofReal_ne_top)

lemma fiber_quadratic_eq {d k : ℕ} [Nonempty (Sphere d)] (hk : 1≤k) (hkd : k<d-1)
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b : Sphere d→ℝ≥0∞) (hb : Measurable b) (M : ℝ≥0∞) (hM : M ≠ ∞) (hbM : ∀ s, b s≤M) :
    (∫⁻ z, fiberBilinearTest H b b z ∂fiberTwoPointLeft d k) =
      ∫⁻ z, fiberBilinearTest H b b z ∂fiberTwoPointRight d k := by
  have := finite_bounded_withDensity (uniformSphere d) b M hM hbM
  rw [fiberLeft_quadratic H b hb (spherical_projection_ac hk hkd),fiberRight_quadratic (by omega) H b hb]
  exact spherical_energy_identity _ H (weightedSphere_projection_ac hk hkd b)
    (weightedSphere_pair_ne (by omega) b) (weightedSphere_pair_inverse_finite hk hkd b hb M hM hbM)



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.FiberEquality
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


lemma fiberLeft_finite {d k : ℕ} [Nonempty (Sphere d)] (hk : 1≤k) (hkd : k<d-1) :
    IsFiniteMeasure (fiberTwoPointLeft d k) := by
  have := fiberRight_finite hk hkd
  have h := fiber_quadratic_eq hk hkd 1 (fun _ => 1) measurable_const 1 (by norm_num) (fun _ => le_rfl)
  simp only [fiberBilinearTest,BoundedContinuousFunction.coe_one,Pi.one_apply,
    ENNReal.coe_one,mul_one,lintegral_one] at h
  constructor
  rw [h]
  exact measure_lt_top _ _

lemma fiberBilinear_integral_ne_top {d k : ℕ} (μ : Measure (Rows k d×(Sphere d×Sphere d)))
    [IsFiniteMeasure μ] (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) {M N : ℝ≥0∞} (hM : M≠∞) (hN : N≠∞)
    (hbM : ∀ s, b s≤M) (haN : ∀ s, a s≤N) :
    (∫⁻ z, fiberBilinearTest H b a z ∂μ) ≠ ∞ := by
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hM) hN)
      (measure_ne_top μ Set.univ))
  calc
    _ ≤ ∫⁻ z, (nndist H 0 : ℝ≥0∞)*M*N ∂μ := by
      apply lintegral_mono
      intro z
      exact mul_le_mul (mul_le_mul (ENNReal.coe_le_coe.mpr (show H z.1≤nndist H 0 by
        simpa using (BoundedContinuousFunction.nndist_coe_le_nndist (f:=H) (g:=0) z.1)))
        (hbM z.2.1) bot_le bot_le) (haN z.2.2) bot_le bot_le
    _ = _ := lintegral_const _

lemma fiberBilinear_add_left {d k : ℕ} (μ : Measure (Rows k d×(Sphere d×Sphere d)))
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0) (b a c : Sphere d→ℝ≥0∞)
    (hb : Measurable b) (hc : Measurable c) :
    (∫⁻ z, fiberBilinearTest H (b+a) c z ∂μ) =
      (∫⁻ z, fiberBilinearTest H b c z ∂μ)+(∫⁻ z, fiberBilinearTest H a c z ∂μ) := by
  rw [show fiberBilinearTest H (b+a) c = (fun z => fiberBilinearTest H b c z+fiberBilinearTest H a c z) by
    funext z; simp only [fiberBilinearTest,Pi.add_apply,mul_add,add_mul]]
  exact lintegral_add_left (measurable_fiberBilinearTest H hb hc) _

lemma fiberBilinear_add_right {d k : ℕ} (μ : Measure (Rows k d×(Sphere d×Sphere d)))
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0) (b a c : Sphere d→ℝ≥0∞)
    (hb : Measurable b) (ha : Measurable a) :
    (∫⁻ z, fiberBilinearTest H b (a+c) z ∂μ) =
      (∫⁻ z, fiberBilinearTest H b a z ∂μ)+(∫⁻ z, fiberBilinearTest H b c z ∂μ) := by
  rw [show fiberBilinearTest H b (a+c) = (fun z => fiberBilinearTest H b a z+fiberBilinearTest H b c z) by
    funext z; simp only [fiberBilinearTest,Pi.add_apply,mul_add]]
  exact lintegral_add_left (measurable_fiberBilinearTest H hb ha) _

lemma fiber_bilinear_eq {d k : ℕ} [Nonempty (Sphere d)] (hk : 1≤k) (hkd : k<d-1)
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) (hb : Measurable b) (ha : Measurable a)
    {M N : ℝ≥0∞} (hM : M≠∞) (hN : N≠∞) (hbM : ∀ s, b s≤M) (haN : ∀ s, a s≤N) :
    (∫⁻ z, fiberBilinearTest H b a z ∂fiberTwoPointLeft d k) =
      ∫⁻ z, fiberBilinearTest H b a z ∂fiberTwoPointRight d k := by
  have := fiberRight_finite hk hkd
  have hbb := fiber_quadratic_eq hk hkd H b hb M hM hbM
  have haa := fiber_quadratic_eq hk hkd H a ha N hN haN
  have hsum := fiber_quadratic_eq hk hkd H (b+a) (hb.add ha) (M+N)
    (ENNReal.add_ne_top.mpr ⟨hM,hN⟩) (fun s => add_le_add (hbM s) (haN s))
  rw [fiberBilinear_add_left _ H b a (b+a) hb (hb.add ha),
    fiberBilinear_add_right _ H b b a hb hb,
    fiberBilinear_add_right _ H a b a ha hb,
    fiberBilinear_add_left _ H b a (b+a) hb (hb.add ha),
    fiberBilinear_add_right _ H b b a hb hb,
    fiberBilinear_add_right _ H a b a ha hb,
    fiberLeft_bilinear_comm H a b ha hb,fiberRight_bilinear_comm (by omega) H a b ha hb,
    hbb,haa] at hsum
  have hbbfin := fiberBilinear_integral_ne_top (fiberTwoPointRight d k) H b b hM hM hbM hbM
  have haafin := fiberBilinear_integral_ne_top (fiberTwoPointRight d k) H a a hN hN haN haN
  simp only [add_assoc] at hsum
  have h := (ENNReal.add_right_inj hbbfin).mp hsum
  rw [←add_assoc,←add_assoc] at h
  have h' := (ENNReal.add_left_inj haafin).mp h
  rw [←mul_two,←mul_two] at h'
  exact (ENNReal.mul_left_inj (by norm_num : (2:ℝ≥0∞)≠0) (by norm_num : (2:ℝ≥0∞)≠∞)).mp h'




lemma fiber_indicator_lintegral {d k : ℕ}
    (μ : Measure (Rows k d×(Sphere d×Sphere d)))
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    {B D : Set (Sphere d)} (hB : MeasurableSet B) (hD : MeasurableSet D) :
    (∫⁻ C, (H C : ℝ≥0∞) ∂(μ.restrict (Set.univ ×ˢ (B ×ˢ D))).map Prod.fst) =
      ∫⁻ z, fiberBilinearTest H (B.indicator (fun _ => 1)) (D.indicator (fun _ => 1)) z ∂μ := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  rw [lintegral_map hH measurable_fst,←lintegral_indicator (MeasurableSet.univ.prod (hB.prod hD))]
  apply lintegral_congr
  intro z
  by_cases hb : z.2.1∈B <;> by_cases hd : z.2.2∈D <;>
    simp [fiberBilinearTest,Set.indicator,hb,hd]

lemma fst_restrict_sphere_rectangle {d k : ℕ}
    (μ : Measure (Rows k d×(Sphere d×Sphere d)))
    {A : Set (Rows k d)} {B D : Set (Sphere d)} (hA : MeasurableSet A) :
    ((μ.restrict (Set.univ ×ˢ (B ×ˢ D))).map Prod.fst) A = μ (A ×ˢ (B ×ˢ D)) := by
  rw [Measure.map_apply measurable_fst hA,Measure.restrict_apply (measurable_fst hA)]
  congr 1
  ext z
  simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_prod,Set.mem_univ,true_and]

lemma snd_restrict_sphere_rectangle {d k : ℕ}
    (μ : Measure (Rows k d×(Sphere d×Sphere d)))
    {A : Set (Rows k d)} {E : Set (Sphere d×Sphere d)} (hE : MeasurableSet E) :
    ((μ.restrict (A ×ˢ Set.univ)).map Prod.snd) E = μ (A ×ˢ E) := by
  rw [Measure.map_apply measurable_snd hE,Measure.restrict_apply (measurable_snd hE)]
  congr 1
  ext z
  simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_prod,Set.mem_univ,and_true]
  exact and_comm

lemma fiber_three_rectangle_eq {d k : ℕ} [Nonempty (Sphere d)] (hk : 1≤k) (hkd : k<d-1)
    {A : Set (Rows k d)} {B D : Set (Sphere d)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hD : MeasurableSet D) :
    fiberTwoPointLeft d k (A ×ˢ (B ×ˢ D)) = fiberTwoPointRight d k (A ×ˢ (B ×ˢ D)) := by
  have := fiberLeft_finite hk hkd
  have heq : ((fiberTwoPointLeft d k).restrict (Set.univ ×ˢ (B ×ˢ D))).map Prod.fst =
      ((fiberTwoPointRight d k).restrict (Set.univ ×ˢ (B ×ˢ D))).map Prod.fst := by
    apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
    intro H
    rw [fiber_indicator_lintegral _ H hB hD,fiber_indicator_lintegral _ H hB hD]
    apply fiber_bilinear_eq hk hkd H _ _ (measurable_const.indicator hB) (measurable_const.indicator hD)
      (M:=1) (N:=1) (by norm_num) (by norm_num)
    · intro s
      by_cases hs : s∈B <;> simp [hs]
    · intro s
      by_cases hs : s∈D <;> simp [hs]
  have h := congrArg (fun μ : Measure (Rows k d) => μ A) heq
  simpa only [fst_restrict_sphere_rectangle _ hA] using h


theorem fiberTwoPointMain_oai : FiberTwoPointMain := by
  intro d k hk hkd
  let : IsProbabilityMeasure (uniformSphere d) :=
    uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  have := fiberLeft_finite hk hkd
  have := fiberRight_finite hk hkd
  refine ⟨inferInstance,inferInstance,?_⟩
  apply Measure.ext_prod
  intro A E hA hE
  have heq : ((fiberTwoPointLeft d k).restrict (A ×ˢ Set.univ)).map Prod.snd =
      ((fiberTwoPointRight d k).restrict (A ×ˢ Set.univ)).map Prod.snd := by
    apply Measure.ext_prod
    intro B D hB hD
    rw [snd_restrict_sphere_rectangle _ (hB.prod hD),snd_restrict_sphere_rectangle _ (hB.prod hD)]
    exact fiber_three_rectangle_eq hk hkd hA hB hD
  have h := congrArg (fun μ : Measure (Sphere d×Sphere d) => μ E) heq
  simpa only [snd_restrict_sphere_rectangle _ hE] using h





end CurrentProjection

end

end OAI
end

theorem solution : type_of% @OAI.CurrentProjection.fiberTwoPointMain_oai := @OAI.CurrentProjection.fiberTwoPointMain_oai
