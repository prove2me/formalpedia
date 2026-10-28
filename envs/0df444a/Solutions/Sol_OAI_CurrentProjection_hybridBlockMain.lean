-- Prove2me | solution 1 for OAI.CurrentProjection.hybridBlockMain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T23:58:56.382729+00:00
-- url     : https://prove2.me/submissions/dd7bc168-fbb6-4648-b1a9-a0404f367f44

import Mathlib
import Definitions.Def_GaussianReplacement
import Definitions.Def_OAIQWCP001
import Theorems.Thm_OAI_CurrentProjection_actual_fresh_row_bound

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

lemma lintegral_pi_append (μ : Measure E) [SigmaFinite μ] (m r : ℕ)
    (f : (Fin (m+r) → E) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ G, f G ∂Measure.pi (fun _ => μ) =
      ∫⁻ X, ∫⁻ Z, f (Fin.append X Z) ∂Measure.pi (fun _ : Fin r => μ)
        ∂Measure.pi (fun _ : Fin m => μ) := by
  rw [← map_append_pi μ m r, lintegral_map hf (measurable_append m r)]
  exact lintegral_prod _ (hf.comp (measurable_append m r)).aemeasurable

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



lemma ae_cube_tendsto_positive {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) :
    ∀ᵐ (s : Sphere d) ∂ρ,
      Tendsto (fun j : ℕ => cubeAverage ρ G (label G (s:Vector d)) (1/(j:ℝ)))
        atTop (𝓝 (extendedCubeDensity ρ G (label G (s:Vector d)))) ∧
      0 < extendedCubeDensity ρ G (label G (s:Vector d)) := by
  have hlabel : ∀ᵐ y ∂labelLaw ρ G,
      Tendsto (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ)))
        atTop (𝓝 (extendedCubeDensity ρ G y)) ∧ 0 < extendedCubeDensity ρ G y := by
    filter_upwards [Besicovitch.ae_tendsto_rnDeriv volume (labelLaw ρ G),
      Measure.rnDeriv_ne_top volume (labelLaw ρ G)] with y hy hyt
    have ht := (hy.comp tendsto_cube_scale).inv
    have he : (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) =ᶠ[atTop]
        (fun j : ℕ => (volume (Metric.closedBall y (1/(j:ℝ))) /
          labelLaw ρ G (Metric.closedBall y (1/(j:ℝ))))⁻¹) := by
      filter_upwards [eventually_ge_atTop 1] with j hj
      have hjp : 0 < 1/(j:ℝ) := by positivity
      rw [cubeAverage_eq_ball_ratio ρ G y hjp,
        ENNReal.inv_div (Or.inl (measure_ne_top _ _))]
      exact Or.inr (by rw [Real.volume_pi_closedBall y hjp.le]; positivity)
    have htc := ht.congr' he.symm
    have heq : extendedCubeDensity ρ G y = (volume.rnDeriv (labelLaw ρ G) y)⁻¹ := htc.liminf_eq
    exact ⟨heq.symm ▸ htc, heq.symm ▸ ENNReal.inv_pos.mpr hyt⟩
  exact ae_of_ae_map (by unfold label; fun_prop) hlabel

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

lemma measurable_fixed_extended {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] (s : Sphere d) :
    Measurable (fun G : Rows k d => extendedCubeDensity ρ G (label G (s:Vector d))) := by
  have h : Measurable (fun G : Rows k d => (G, label G (s:Vector d))) :=
    measurable_id.prodMk (measurable_fixed_label (k:=k) s)
  have h2 := (measurable_extendedCubeDensity (k:=k) ρ).comp h
  exact h2

lemma measurable_fixed_exact {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] (s : Sphere d) :
    Measurable (fun G : Rows k d => exactDensity ρ G (label G (s:Vector d))) := by
  have h : Measurable (fun G : Rows k d => (G, label G (s:Vector d))) :=
    measurable_id.prodMk (measurable_fixed_label (k:=k) s)
  have h2 := (measurable_exactDensity (k:=k) ρ).comp h
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

lemma ae_target_cube_limit {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ] :
    ∀ᵐ (s : Sphere d) ∂ρ, ∀ᵐ G ∂gaussianRows k d,
      Tendsto (fun j : ℕ => cubeAverage ρ G (label G (s:Vector d)) (1/(j:ℝ)))
        atTop (𝓝 (extendedCubeDensity ρ G (label G (s:Vector d)))) ∧
      0 < extendedCubeDensity ρ G (label G (s:Vector d)) := by
  apply (Measure.ae_ae_comm ?_).mp
  · exact Filter.Eventually.of_forall (ae_cube_tendsto_positive ρ)
  · exact (measurableSet_tendsto_fun (fun j : ℕ => measurable_own_cube (k:=k) ρ (1/(j:ℝ)))
      (measurable_own_extended (k:=k) ρ)).inter
      (measurableSet_lt measurable_const (measurable_own_extended (k:=k) ρ))

lemma exact_mixed_moment_of_ae {d m r q : ℕ} (hdim : AdmissibleDimensions d m r q)
    (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (B D : ℝ) (hB : 0 < B) (hD : 0 < D)
    (hBρ : LocalGrowth ρ (m+r) B) (hDρ : LocalGrowth ρ (d-1) D) (s : Sphere d)
    (he : ∀ᵐ G ∂gaussianRows (m+r) d,
      exactDensity ρ G (label G (s:Vector d)) = extendedCubeDensity ρ G (label G (s:Vector d))) :
    (∫⁻ X, (∫⁻ Z, exactDensity ρ (Fin.append X Z)
      (label (Fin.append X Z) (s:Vector d)) ∂gaussianRows r d)^q
      ∂gaussianRows m d) ≤ (momentConstant 9 d B D)^q := by
  have hea := (ae_pi_append (stdGaussian (Vector d)) m r
    (measurableSet_eq_fun (measurable_fixed_exact (k:=m+r) ρ s)
      (measurable_fixed_extended (k:=m+r) ρ s))).mp he
  calc
    _ = (∫⁻ X, (∫⁻ Z, extendedCubeDensity ρ (Fin.append X Z)
        (label (Fin.append X Z) (s:Vector d)) ∂gaussianRows r d)^q
        ∂gaussianRows m d) := by
      apply lintegral_congr_ae
      filter_upwards [hea] with X hX
      exact congrArg (fun x : ℝ≥0∞ => x^q) (lintegral_congr_ae hX)
    _ ≤ _ := extended_mixed_moment hdim ρ B D hB hD hBρ hDρ s




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



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.ActualRow
attribute [-instance] _root_.OAI.CurrentProjection.alignedExperiment_probability _root_.OAI.CurrentProjection.blockLaw_probability _root_.OAI.CurrentProjection.criticalSignal_probability _root_.OAI.CurrentProjection.endingRowLaw_probability _root_.OAI.CurrentProjection.endingSignalLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.fixedTargetPosterior_markov _root_.OAI.CurrentProjection.gaussianObservation_probability _root_.OAI.CurrentProjection.gaussianObservations_probability _root_.OAI.CurrentProjection.prefixLaw_probability _root_.OAI.CurrentProjection.residualLaw_probability _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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

lemma exactDensity_ne_top {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d) (y : Fin k → ℝ) :
    exactDensity ρ G y ≠ ∞ := by
  unfold exactDensity
  dsimp only
  split_ifs <;> simp

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



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.ConditionalInfo
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

lemma conditionalMutualInformation_compProd {Z A B : Type*} [MeasurableSpace Z]
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace A] [StandardBorelSpace B]
    [Nonempty A] [Nonempty B] (μ : Measure Z) [IsFiniteMeasure μ]
    (κ : Kernel Z (A×B)) [IsMarkovKernel κ] :
    conditionalMutualInformation (μ ⊗ₘ κ) = klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
  simp only [conditionalMutualInformation,dite_eq_left (inferInstance : Nonempty (A×B)),Measure.fst_compProd]
  congr 1
  apply Measure.compProd_congr
  filter_upwards [condKernel_compProd μ κ] with z hz
  simp only [Kernel.prod_apply,Kernel.fst_apply,Kernel.snd_apply,hz]

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

lemma sphere_dist_le_two {d : ℕ} (s t : Sphere d) : dist (s:Vector d) (t:Vector d) ≤ 2 := by
  have hs : ‖(s:Vector d)‖ = 1 := by simp
  have ht : ‖(t:Vector d)‖ = 1 := by simp
  calc
    _ ≤ dist (s:Vector d) 0 + dist (0:Vector d) t := dist_triangle _ _ _
    _ = 2 := by simp only [dist_zero_right,dist_zero_left,hs,ht]; norm_num



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




lemma swapLast_snd {S W G : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace G] (P : Measure ((S×W)×G)) : (P.map swapLast).snd = P.fst.snd := by
  rw [Measure.snd,Measure.fst,Measure.snd,Measure.map_map measurable_snd swapLast.measurable,
    Measure.map_map measurable_snd measurable_fst]
  rfl



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Refinement
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

lemma rowInformation_alignedExperiment {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    rowInformation (alignedExperiment (r:=r) P) (gaussianRows (m+r) d) =
      rowInformation P (gaussianRows m d) := by
  let f : ((Sphere d×W)×Rows m d)×Rows r d → (Sphere d×W)×Rows (m+r) d :=
    fun p => (p.1.1,Fin.append p.1.2 p.2)
  let g : (Sphere d×W)×Rows (m+r) d → ((Sphere d×W)×Rows m d)×Rows r d :=
    fun p => ((p.1,fun i => p.2 (Fin.castAdd r i)),fun i => p.2 (Fin.natAdd m i))
  have hf : Measurable f := measurable_alignedMap
  have hg : Measurable g :=
    (measurable_fst.prodMk (Measurable.of_eval (fun i => (measurable_pi_apply _).comp measurable_snd))).prodMk
      (Measurable.of_eval (fun i => (measurable_pi_apply _).comp measurable_snd))
  have hgf : Function.LeftInverse g f := by
    intro p
    ext <;> simp [f,g]
  have hRef : ((P.fst.prod (gaussianRows m d)).prod (gaussianRows r d)).map f =
      P.fst.prod (gaussianRows (m+r) d) := by
    change Measure.map ((Prod.map id (fun p : Rows m d×Rows r d => Fin.append p.1 p.2)) ∘
      MeasurableEquiv.prodAssoc) _ = _
    rw [←Measure.map_map (measurable_id.prodMap (measurable_append (E:=Vector d) m r))
      MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod,
      ←Measure.map_prod_map _ _ measurable_id (measurable_append (E:=Vector d) m r),Measure.map_id]
    rw [show ((gaussianRows m d).prod (gaussianRows r d)).map (fun p => Fin.append p.1 p.2) =
      gaussianRows (m+r) d from map_append_pi (stdGaussian (Vector d)) m r]
  unfold rowInformation
  rw [alignedExperiment_fst]
  change klDiv ((P.prod (gaussianRows r d)).map f) (P.fst.prod (gaussianRows (m+r) d)) = _
  rw [←hRef,klDiv_map_leftInverse _ _ f g hf hg hgf]
  simpa only [Measure.compProd_const] using
    klDiv_compProd_left P (P.fst.prod (gaussianRows m d)) (Kernel.const _ (gaussianRows r d))



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Tilt
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




section CauchyVector
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_inner_map_scaled (v : E) :
    (stdGaussian E).map (fun x => ⟪v,x⟫) =
      (gaussianReal 0 1).map (fun x => ‖v‖*x) := by
  have hi := IsGaussian.map_eq_gaussianReal (μ:=stdGaussian E) (innerSL ℝ v)
  rw [integral_strongDual_stdGaussian,variance_dual_stdGaussian] at hi
  have he : (fun x : ℝ => ‖v‖*x) = fun x => x*‖v‖ := by funext x; ring
  rw [he,gaussianReal_map_mul_const]
  have hv : (‖v‖^2).toNNReal = (⟨‖v‖^2,sq_nonneg _⟩ : ℝ≥0) := by
    exact Real.toNNReal_of_nonneg (sq_nonneg _)
  rw [innerSL_apply_norm] at hi
  change (stdGaussian E).map (fun x => ⟪v,x⟫) = gaussianReal 0 (‖v‖^2).toNNReal at hi
  rw [hi]
  congr 1 <;> simp only [mul_zero,mul_one,hv]
  ext
  rfl


end CauchyVector



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Reference
attribute [-instance] _root_.OAI.CurrentProjection.endingRowLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.fixedTargetPosterior_markov _root_.OAI.CurrentProjection.gaussianObservation_probability _root_.OAI.CurrentProjection.gaussianObservations_probability _root_.OAI.CurrentProjection.prefixLaw_probability _root_.OAI.CurrentProjection.residualLaw_probability _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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




lemma sphere_own_density_moment {d m r : ℕ}
    (hdim : AdmissibleDimensions d m r 1) (hd : 2 ≤ d) :
    ∫⁻ z : Rows (m+r) d × Sphere d,
      exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d))
      ∂(gaussianRows (m+r) d).prod (uniformSphere d) ≤
        momentConstant 9 d (3*4^d) (3*4^d) := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  have hB : (0:ℝ) < 3*4^d := by positivity
  have hG := uniformSphere_growth (show 1 ≤ d by omega) (show m+r ≤ d-1 by have := hdim.2.2.2.1; omega)
  have hD := uniformSphere_growth (show 1 ≤ d by omega) (le_refl (d-1))
  have ha : ∀ᵐ (s : Sphere d) ∂uniformSphere d,
      (∫⁻ G, exactDensity (uniformSphere d) G (label G (s:Vector d))
        ∂gaussianRows (m+r) d) ≤ momentConstant 9 d (3*4^d) (3*4^d) := by
    filter_upwards [ae_target_cube_limit (k:=m+r) (uniformSphere d)] with s hs
    have hfin := extended_ae_finite hdim (uniformSphere d) _ _ hB hB hG hD s
    have he : ∀ᵐ G ∂gaussianRows (m+r) d,
        exactDensity (uniformSphere d) G (label G (s:Vector d)) =
          extendedCubeDensity (uniformSphere d) G (label G (s:Vector d)) := by
      filter_upwards [hs,hfin] with G hG hf
      exact exactDensity_eq_of_tendsto _ _ _ hG.1 hf.ne
    have hm := exact_mixed_moment_of_ae hdim (uniformSphere d) _ _ hB hB hG hD s he
    simpa only [pow_one, gaussianRows, ←lintegral_pi_append (stdGaussian (Vector d)) m r
      _ (measurable_fixed_exact (uniformSphere d) s)] using hm
  rw [lintegral_prod_symm _ (measurable_own_exact (uniformSphere d)).aemeasurable]
  exact (lintegral_mono_ae ha).trans_eq (by simp)

lemma sphere_moment_log_bound {d : ℕ} (hd : 1 ≤ d) :
    Real.log (1+(momentConstant 9 d (3*4^d) (3*4^d)).toReal) ≤ 20*d := by
  have hB : (0:ℝ) < 3*4^d := by positivity
  have he : (momentConstant 9 d (3*4^d) (3*4^d)).toReal =
      Real.exp (9*d)*(3*4^d) := by
    simp [momentConstant,ENNReal.toReal_ofReal (by positivity :
      0 ≤ Real.exp (9*d)*(3*4^d))]
  rw [he]
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hpow : (1:ℝ) ≤ 4^d := one_le_pow₀ (by norm_num)
  have hexp : (1:ℝ) ≤ Real.exp (9*d) := Real.one_le_exp_iff.mpr (by positivity)
  have ht : 1 ≤ Real.exp (9*d)*(3*4^d) := by nlinarith
  have hl := Real.log_le_log (by positivity : 0<1+Real.exp (9*d)*(3*4^d))
    (show 1+Real.exp (9*d)*(3*4^d) ≤ 2*(Real.exp (9*d)*(3*4^d)) by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity),
    Real.log_mul (Real.exp_ne_zero _) hB.ne',Real.log_exp,
    Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),Real.log_pow] at hl
  have h2 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 2)
  have h3 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 3)
  have h4 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 4)
  nlinarith

lemma sphere_label_entropy_finite {d m r : ℕ}
    (hdim : AdmissibleDimensions d m r 1) (hd : 2 ≤ d) :
    Integrable (fun z : Rows (m+r) d × Sphere d =>
      Real.log (exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d))).toReal)
      ((gaussianRows (m+r) d).prod (uniformSphere d)) ∧
    (∫ z : Rows (m+r) d × Sphere d,
      Real.log (exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d))).toReal
      ∂(gaussianRows (m+r) d).prod (uniformSphere d)) ≤ 20*d := by
  classical
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  let μ := (gaussianRows (m+r) d).prod (uniformSphere d)
  let f : Rows (m+r) d × Sphere d → ℝ≥0∞ :=
    fun z => exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d))
  have hf : Measurable f := measurable_own_exact _
  have hmoment := sphere_own_density_moment hdim hd
  have ht : ∫⁻ z, f z ∂μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmoment
  have hJ := log_one_add_jensen μ f hf (fun z => exactDensity_ne_top _ _ _) ht
  have hM := ENNReal.toReal_mono (show momentConstant 9 d (3*4^d) (3*4^d) ≠ ∞ from ENNReal.ofReal_ne_top) hmoment
  have hMlog := Real.log_le_log (by positivity : 0<1+(∫⁻ z, f z ∂μ).toReal)
    (show 1+(∫⁻ z, f z ∂μ).toReal ≤ 1+(momentConstant 9 d (3*4^d) (3*4^d)).toReal from by dsimp [f,μ]; linarith)
  have hb := sphere_moment_log_bound (show 1 ≤ d by omega)
  have hJ' : ∫⁻ z, ENNReal.ofReal (Real.log (1+(f z).toReal)) ∂μ ≤ ENNReal.ofReal (20*d) :=
    hJ.trans (ENNReal.ofReal_le_ofReal (hMlog.trans hb))
  obtain ⟨⟨hiL,hbL⟩,hiP,_⟩ := log_bound_consequences μ f hf (20*d) (by positivity) hJ'
  have hB : (0:ℝ) < 3*4^d := by positivity
  have hAC := ae_labelLaw_ac_of_growth hdim (uniformSphere d) _ _ hB hB
    (uniformSphere_growth (show 1 ≤ d by omega) (show m+r ≤ d-1 by have := hdim.2.2.2.1; omega))
    (uniformSphere_growth (show 1 ≤ d by omega) (le_refl (d-1)))
  let c : Sphere d := Classical.choice inferInstance
  obtain ⟨hi,_⟩ := projection_cover_entropy (uniformSphere d) hAC hiP
    (Finset.singleton_nonempty c) (show (0:ℝ)<1 by norm_num)
    (ae_of_all _ (fun s => ⟨c,Finset.mem_singleton_self c,by
      have hdist := (norm_sub_le (s:Vector d) (c:Vector d))
      simpa only [Subtype.dist_eq,dist_eq_norm,norm_eq_of_mem_sphere s,norm_eq_of_mem_sphere c,one_add_one_eq_two,mul_one] using hdist⟩))
  refine ⟨hi,?_⟩
  apply (integral_mono hi hiL (fun z => ?_)).trans hbL
  exact (le_max_left _ _).trans (logPositive_le_log_one_add (f z))




lemma conditionalReferenceKL_chain {C A B : Type*} [MeasurableSpace C]
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (P : Measure (C×(A×B))) [IsProbabilityMeasure P]
    (ν : Measure A) (π : Measure B) [IsProbabilityMeasure ν] [IsProbabilityMeasure π] :
    conditionalReferenceKL P (ν.prod π) =
      conditionalReferenceKL (P.map (Prod.map id Prod.fst)) ν +
      conditionalReferenceKL (P.map MeasurableEquiv.prodAssoc.symm) π := by
  let R := P.map MeasurableEquiv.prodAssoc.symm
  let : IsProbabilityMeasure R := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hRf : R.fst = P.map (Prod.map id Prod.fst) := by
    rw [Measure.fst,Measure.map_map measurable_fst MeasurableEquiv.prodAssoc.symm.measurable]
    rfl
  have hff : R.fst.fst = P.fst := by
    rw [hRf,Measure.fst,Measure.map_map measurable_fst (measurable_id.prodMap measurable_fst)]
    rfl
  have hr : (P.fst.prod (ν.prod π)).map MeasurableEquiv.prodAssoc.symm =
      (P.fst.prod ν).prod π := by rw [←Measure.prodAssoc_prod,MeasurableEquiv.map_symm_map]
  unfold conditionalReferenceKL
  rw [←klDiv_map_equiv P (P.fst.prod (ν.prod π)) MeasurableEquiv.prodAssoc.symm,hr,
    klDiv_prod_chain R (P.fst.prod ν) π]
  rw [←hff,hRf]

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

lemma log_gaussianLabelsPDF {k : ℕ} (y : Fin k → ℝ) :
    Real.log (gaussianProductPDF 1 0 y) = -(k:ℝ)*Real.log (normalizer 1) -
      (∑ i, (y i)^2)/2 := by
  simpa using log_gaussianProductPDF (k:=k) (show (0:ℝ)<1 by norm_num) (0:Fin k→ℝ) y

lemma projectionSquare_sphere_joint_integrable {d k : ℕ}
    (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ] :
    Integrable (fun z : Rows k d × Sphere d => projectionSquare z.1 (z.2:Vector d))
      ((gaussianRows k d).prod ρ) := by
  have hm : Measurable (fun z : Rows k d × Sphere d => projectionSquare z.1 (z.2:Vector d)) := by
    unfold projectionSquare label
    fun_prop
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun s => projectionSquare_integrable (s:Vector d)),?_⟩
  have he : (fun s : Sphere d => ∫ G, ‖projectionSquare G (s:Vector d)‖ ∂gaussianRows k d) =
      fun _ => (k:ℝ) := by
    funext s
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (projectionSquare_nonneg _ _)]
    rw [projectionSquare_integral,norm_eq_of_mem_sphere s]
    simp
  rw [he]
  exact integrable_const _

lemma projectionSquare_sphere_joint_integral {d k : ℕ}
    (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ] :
    (∫ z : Rows k d × Sphere d, projectionSquare z.1 (z.2:Vector d)
      ∂(gaussianRows k d).prod ρ) = k := by
  rw [integral_prod_symm _ (projectionSquare_sphere_joint_integrable ρ)]
  simp only [projectionSquare_integral,norm_eq_of_mem_sphere,
    one_pow,mul_one,integral_const,probReal_univ,one_smul]

lemma gaussian_log_reference_projection {d k : ℕ}
    (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ] :
    Integrable (fun z : Rows k d×(Fin k→ℝ) =>
      Real.log (gaussianProductPDF 1 0 z.2)) (projectionJoint ρ (gaussianRows k d)) ∧
    (∫ z : Rows k d×(Fin k→ℝ), Real.log (gaussianProductPDF 1 0 z.2)
      ∂projectionJoint ρ (gaussianRows k d)) =
      -(k:ℝ)*(Real.log (normalizer 1)+1/2) := by
  have hf : Measurable (fun z : Rows k d×(Fin k→ℝ) => Real.log (gaussianProductPDF 1 0 z.2)) := by
    unfold gaussianProductPDF
    fun_prop
  have hm : Measurable (fun z : Rows k d×Sphere d => (z.1,label z.1 (z.2:Vector d))) :=
    measurable_fst.prodMk measurable_own_label
  have hi : Integrable (fun z : Rows k d×Sphere d =>
      Real.log (gaussianProductPDF 1 0 (label z.1 (z.2:Vector d))))
      ((gaussianRows k d).prod ρ) := by
    simp_rw [log_gaussianLabelsPDF]
    exact (integrable_const _).sub ((projectionSquare_sphere_joint_integrable ρ).div_const 2)
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mpr hi,?_⟩
  rw [projectionJoint,integral_map hm.aemeasurable hf.aestronglyMeasurable]
  simp_rw [log_gaussianLabelsPDF]
  change (∫ z : Rows k d×Sphere d, -(k:ℝ)*Real.log (normalizer 1) - projectionSquare z.1 (z.2:Vector d)/2 ∂(gaussianRows k d).prod ρ) = _
  rw [integral_sub (integrable_const _) ((projectionSquare_sphere_joint_integrable ρ).div_const 2),
    integral_const,integral_div,projectionSquare_sphere_joint_integral]
  simp only [probReal_univ,one_smul]
  ring

lemma sphere_projection_reference_finite {d m r : ℕ}
    (hdim : AdmissibleDimensions d m r 1) (hd : 2 ≤ d) :
    klDiv (projectionJoint (uniformSphere d) (gaussianRows (m+r) d))
      ((gaussianRows (m+r) d).prod (gaussianLabels (m+r))) ≠ ∞ ∧
    (klDiv (projectionJoint (uniformSphere d) (gaussianRows (m+r) d))
      ((gaussianRows (m+r) d).prod (gaussianLabels (m+r)))).toReal ≤
      20*d + (m+r:ℕ)*(Real.log (normalizer 1)+1/2) := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let P := projectionJoint (uniformSphere d) (gaussianRows (m+r) d)
  let Q := (gaussianRows (m+r) d).prod (gaussianLabels (m+r))
  let Λ := (gaussianRows (m+r) d).prod (volume : Measure (Fin (m+r)→ℝ))
  let p : Rows (m+r) d×(Fin (m+r)→ℝ) → ℝ≥0∞ := fun z => exactDensity (uniformSphere d) z.1 z.2
  let g : Rows (m+r) d×(Fin (m+r)→ℝ) → ℝ := fun z => gaussianProductPDF 1 0 z.2
  have hp : Measurable p := measurable_exactDensity _
  have hg : Measurable g := by unfold g gaussianProductPDF; fun_prop
  have hQ : Λ.withDensity (fun z => ENNReal.ofReal (g z)) = Q := by
    have hs : Measurable (fun y : Fin (m+r)→ℝ => ENNReal.ofReal (gaussianProductPDF 1 0 y)) := by unfold gaussianProductPDF; fun_prop
    dsimp [Λ,g,Q]
    rw [←prod_withDensity_right hs,gaussianLabels_density]
  have hB : (0:ℝ) < 3*4^d := by positivity
  have hAC := ae_labelLaw_ac_of_growth hdim (uniformSphere d) _ _ hB hB
    (uniformSphere_growth (show 1 ≤ d by omega) (show m+r ≤ d-1 by have := hdim.2.2.2.1; omega))
    (uniformSphere_growth (show 1 ≤ d by omega) (le_refl (d-1)))
  obtain ⟨hPQ,he⟩ := llr_of_two_densities P Q Λ p hp
    (projectionJoint_withDensity _ _ hAC) g hg (fun z => gaussianProductPDF_pos (by norm_num) _ _) hQ
  obtain ⟨hpi,hpb⟩ := sphere_label_entropy_finite hdim hd
  have hpm : Measurable (fun z : Rows (m+r) d×Sphere d => (z.1,label z.1 (z.2:Vector d))) :=
    measurable_fst.prodMk measurable_own_label
  have hpi' : Integrable (fun z => Real.log (p z).toReal) P :=
    (integrable_map_measure hp.ennreal_toReal.log.aestronglyMeasurable hpm.aemeasurable).mpr hpi
  obtain ⟨hgi,hge⟩ := gaussian_log_reference_projection (k:=m+r) (uniformSphere d)
  have hll : Integrable (llr P Q) P := (hpi'.sub hgi).congr he.symm
  refine ⟨klDiv_ne_top hPQ hll,?_⟩
  rw [toReal_klDiv_of_measure_eq hPQ (by simp),integral_congr_ae he,integral_sub hpi' hgi,hge]
  have hpint : (∫ z, Real.log (p z).toReal ∂P) =
      ∫ z : Rows (m+r) d×Sphere d, Real.log (exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d))).toReal
      ∂(gaussianRows (m+r) d).prod (uniformSphere d) :=
    integral_map hpm.aemeasurable hp.ennreal_toReal.log.aestronglyMeasurable
  rw [hpint]
  linarith




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.FreshRows
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


lemma gaussian_inner_map_sphere {d : ℕ} (s : Sphere d) :
    (stdGaussian (Vector d)).map (fun x => ⟪(s:Vector d),x⟫) = gaussianReal 0 1 := by
  rw [gaussian_inner_map_scaled,show ‖(s:Vector d)‖ = 1 from mem_sphere_zero_iff_norm.mp s.property]
  simp only [one_mul,Measure.map_id']



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


lemma measurable_scalarObservation {d : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (scalarObservation (d:=d) (C:=C)) := by unfold scalarObservation; fun_prop

instance scalarObservationLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] : IsProbabilityMeasure (scalarObservationLaw Γ) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_scalarObservation.aemeasurable).mpr inferInstance

lemma measurable_residualLabelObservation {d r : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (residualLabelObservation (d:=d) (r:=r) (C:=C)) := by
  unfold residualLabelObservation label
  fun_prop

instance residualLabelLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    IsProbabilityMeasure (residualLabelLaw P r) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_residualLabelObservation.aemeasurable).mpr inferInstance



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Observation
attribute [-instance] _root_.OAI.CurrentProjection.endingRowLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.prefixLaw_probability _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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


lemma appendEquiv_map {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] (m r : ℕ) :
    ((Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi (fun _ : Fin r => μ))).map
      (appendEquiv E m r) = Measure.pi (fun _ : Fin (m+r) => μ) := map_append_pi μ m r

lemma gaussianObservations_eq (k d : ℕ) :
    ((gaussianRows k d).prod (gaussianLabels k)).map (observationEquiv k d) =
      gaussianObservations k d := by
  exact (measurePreserving_arrowProdEquivProdArrow (Vector d) ℝ (Fin k)
    (fun _ => stdGaussian (Vector d)) (fun _ => gaussianReal 0 1)).symm.map_eq

lemma ownObservations_append {i r d : ℕ} (X : Rows i d) (A : Rows r d) (s : Sphere d) :
    ownObservations (Fin.append X A) s = Fin.append (ownObservations X s) (ownObservations A s) := by
  funext j
  induction j using Fin.addCases <;> simp [ownObservations,pairObservation,label]

lemma gaussianObservations_append (i r d : ℕ) :
    ((gaussianObservations i d).prod (gaussianObservations r d)).map
      (appendEquiv (Vector d×ℝ) i r) = gaussianObservations (i+r) d :=
  appendEquiv_map (gaussianObservation d) i r

lemma conditionalReferenceKL_map_context {C D A : Type*} [MeasurableSpace C]
    [MeasurableSpace D] [MeasurableSpace A]
    (P : Measure (C×A)) [IsProbabilityMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    (f : C → D) (g : D → C) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    conditionalReferenceKL (P.map (Prod.map f id)) ν = conditionalReferenceKL P ν := by
  have hfst : (P.map (Prod.map f id)).fst = P.fst.map f := by
    rw [Measure.fst,Measure.map_map measurable_fst (hf.prodMap measurable_id),Measure.fst,
      Measure.map_map hf measurable_fst]
    rfl
  unfold conditionalReferenceKL
  rw [hfst,show (P.fst.map f).prod ν = (P.fst.prod ν).map (Prod.map f id) by
    rw [←Measure.map_prod_map _ _ hf measurable_id,Measure.map_id]]
  exact klDiv_map_leftInverse _ _ _ (Prod.map g id) (hf.prodMap measurable_id)
    (hg.prodMap measurable_id) (fun z => Prod.ext (hgf z.1) rfl)

lemma conditionalReferenceKL_context_equiv {C D A : Type*} [MeasurableSpace C]
    [MeasurableSpace D] [MeasurableSpace A]
    (P : Measure (C×A)) [IsProbabilityMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    (e : C ≃ᵐ D) :
    conditionalReferenceKL (P.map (Prod.map e id)) ν = conditionalReferenceKL P ν :=
  conditionalReferenceKL_map_context P ν e e.symm e.measurable e.symm.measurable e.left_inv


lemma observationReferenceKL_decomposition {d k : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows k d)) :
    observationReferenceKL P =
      klDiv (projectionJoint ν (gaussianRows k d)) ((gaussianRows k d).prod (gaussianLabels k)) +
      mutualInformation (observedMessage P) := by
  unfold observationReferenceKL
  rw [←observedMessage_snd P,mutualInformation_reference,
    observedMessage_fst_of_independence P ν (gaussianRows k d) hInd]

lemma observationReferenceKL_chain_exposed {d k : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W] [Nonempty (Sphere d)]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows k d)) :
    observationReferenceKL P + exposedInformation P =
      klDiv (projectionJoint ν (gaussianRows k d)) ((gaussianRows k d).prod (gaussianLabels k)) +
      mutualInformation P.fst + rowInformation P (gaussianRows k d) := by
  rw [observationReferenceKL_decomposition P ν hInd,add_assoc,
    ←exposedInformation_chain,mutualInformation_rows_chain P ν (gaussianRows k d) hInd,add_assoc]



lemma snocEquiv_apply {E : Type*} [MeasurableSpace E] {r : ℕ} (z : (Fin r→E)×E) :
    snocEquiv E r z = Fin.snoc z.1 z.2 := by
  ext j
  induction j using Fin.lastCases <;> simp [snocEquiv,Fin.snoc,MeasurableEquiv.prodComm]

lemma snocEquiv_map {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] (r : ℕ) :
    ((Measure.pi (fun _ : Fin r => μ)).prod μ).map (snocEquiv E r) =
      Measure.pi (fun _ : Fin (r+1) => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (r+1) => μ) (Fin.last r)).symm.map_eq
  change Measure.map ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r+1) => E) (Fin.last r)).symm ∘ Prod.swap) _ = _
  rw [←Measure.map_map (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (r+1) => E) (Fin.last r)).symm.measurable measurable_swap,Measure.prod_swap]
  exact h

lemma conditionalReferenceKL_outcome_equiv {C A B : Type*} [MeasurableSpace C]
    [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure (C×A)) [IsProbabilityMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    (e : A ≃ᵐ B) :
    conditionalReferenceKL (P.map (Prod.map id e)) (ν.map e) = conditionalReferenceKL P ν := by
  have hf : (P.map (Prod.map id e)).fst = P.fst := by
    rw [Measure.fst,Measure.map_map measurable_fst (measurable_id.prodMap e.measurable)]
    rfl
  unfold conditionalReferenceKL
  rw [hf,show P.fst.prod (ν.map e) = (P.fst.prod ν).map (Prod.map id e) by
    rw [←Measure.map_prod_map _ _ measurable_id e.measurable,Measure.map_id]]
  exact klDiv_map_leftInverse _ _ _ (Prod.map id e.symm) (measurable_id.prodMap e.measurable)
    (measurable_id.prodMap e.symm.measurable) (fun z => Prod.ext rfl (e.left_inv z.2))

lemma measurable_arrayResidualObservation {d r : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (arrayResidualObservation (d:=d) (r:=r) (C:=C)) := by
  unfold arrayResidualObservation
  exact (measurable_fst.fst.prodMk (measurable_ownObservations.comp
    (measurable_snd.prodMk measurable_fst.snd))).prodMk measurable_fst.snd

instance arrayResidualLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    IsProbabilityMeasure (arrayResidualLaw Γ r) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_arrayResidualObservation.aemeasurable).mpr inferInstance

instance freshArrayLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    IsProbabilityMeasure (freshArrayLaw Γ r) := by unfold freshArrayLaw; infer_instance

lemma freshArrayLaw_eq {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) :
    freshArrayLaw Γ r = (Γ.prod (gaussianRows r d)).map
      (fun z => (z.1.1,ownObservations z.2 z.1.2)) := by
  rw [freshArrayLaw,arrayResidualLaw,Measure.fst,Measure.map_map measurable_fst measurable_arrayResidualObservation]
  rfl

lemma freshArrayLaw_fst {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    (freshArrayLaw Γ r).fst = Γ.fst := by
  have hm : Measurable (fun z : (C×Sphere d)×Rows r d => (z.1.1,ownObservations z.2 z.1.2)) :=
    measurable_fst.fst.prodMk (measurable_ownObservations.comp (measurable_snd.prodMk measurable_fst.snd))
  rw [freshArrayLaw_eq,Measure.fst,Measure.map_map measurable_fst hm]
  change (Γ.prod (gaussianRows r d)).map (Prod.fst ∘ Prod.fst) = _
  rw [←Measure.map_map measurable_fst measurable_fst]
  change (Γ.prod (gaussianRows r d)).fst.fst = Γ.fst
  rw [Measure.fst_prod]

lemma scalarObservationLaw_context {d : ℕ} {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (Γ : Measure (C×Sphere d)) [SFinite Γ] (f : C → D) (hf : Measurable f) :
    scalarObservationLaw (Γ.map (Prod.map f id)) = (scalarObservationLaw Γ).map
      (Prod.map (Prod.map f id) id) := by
  rw [scalarObservationLaw,show (Γ.map (Prod.map f id)).prod (stdGaussian (Vector d)) =
      (Γ.prod (stdGaussian (Vector d))).map (Prod.map (Prod.map f id) id) by
    rw [←Measure.map_prod_map _ _ (hf.prodMap measurable_id) measurable_id,Measure.map_id],
    Measure.map_map measurable_scalarObservation ((hf.prodMap measurable_id).prodMap measurable_id),
    scalarObservationLaw,Measure.map_map ((hf.prodMap measurable_id).prodMap measurable_id)
      measurable_scalarObservation]
  rfl

lemma prod_append_gaussian_map {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [SigmaFinite μ] (d r s : ℕ) :
    (((μ.prod (gaussianRows r d)).prod (gaussianRows s d)).map
      (fun z => (z.1.1,Fin.append z.1.2 z.2))) = μ.prod (gaussianRows (r+s) d) := by
  have h := map_append_pi (stdGaussian (Vector d)) r s
  change ((gaussianRows r d).prod (gaussianRows s d)).map (fun z => Fin.append z.1 z.2) = gaussianRows (r+s) d at h
  have hp := Measure.map_prod_map μ ((gaussianRows r d).prod (gaussianRows s d)) measurable_id (measurable_append r s)
  simp only [Measure.map_id] at hp
  rw [←h,hp,
    ←Measure.prodAssoc_prod,Measure.map_map (measurable_id.prodMap (measurable_append r s))
      MeasurableEquiv.prodAssoc.measurable]
  rfl

lemma arrayResidualLaw_append {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r s : ℕ) :
    arrayResidualLaw Γ (r+s) = (arrayResidualLaw (arrayResidualLaw Γ r) s).map
      (fun z => ((z.1.1.1,Fin.append z.1.1.2 z.1.2),z.2)) := by
  have hm : Measurable (fun z : ((C×Observations r d)×Observations s d)×Sphere d =>
      ((z.1.1.1,Fin.append z.1.1.2 z.1.2),z.2)) :=
    (measurable_fst.fst.fst.prodMk ((measurable_append r s).comp
      (measurable_fst.fst.snd.prodMk measurable_fst.snd))).prodMk measurable_snd
  have hm0 : Measurable (fun z : ((C×Sphere d)×Rows r d)×Rows s d => (z.1.1,Fin.append z.1.2 z.2)) :=
    measurable_fst.fst.prodMk ((measurable_append r s).comp (measurable_fst.snd.prodMk measurable_snd))
  rw [arrayResidualLaw,←prod_append_gaussian_map Γ d r s,
    Measure.map_map measurable_arrayResidualObservation hm0]
  rw [arrayResidualLaw,Measure.map_map hm measurable_arrayResidualObservation,arrayResidualLaw,
    show ((Γ.prod (gaussianRows r d)).map arrayResidualObservation).prod (gaussianRows s d) =
      (((Γ.prod (gaussianRows r d)).prod (gaussianRows s d))).map
        (Prod.map arrayResidualObservation id) by
      rw [←Measure.map_prod_map _ _ measurable_arrayResidualObservation measurable_id,Measure.map_id],
    Measure.map_map (hm.comp measurable_arrayResidualObservation)
      (measurable_arrayResidualObservation.prodMap measurable_id)]
  congr 1
  funext z
  simp only [Function.comp_apply,Prod.map,arrayResidualObservation,ownObservations_append,id_eq]

lemma freshArrayLaw_append {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r s : ℕ) :
    freshArrayLaw Γ (r+s) = (freshArrayLaw (arrayResidualLaw Γ r) s).map
      (fun z => (z.1.1,Fin.append z.1.2 z.2)) := by
  have hm : Measurable (fun z : ((C×Observations r d)×Observations s d)×Sphere d =>
      ((z.1.1.1,Fin.append z.1.1.2 z.1.2),z.2)) :=
    (measurable_fst.fst.fst.prodMk ((measurable_append r s).comp
      (measurable_fst.fst.snd.prodMk measurable_fst.snd))).prodMk measurable_snd
  have hm' : Measurable (fun z : (C×Observations r d)×Observations s d =>
      (z.1.1,Fin.append z.1.2 z.2)) :=
    measurable_fst.fst.prodMk ((measurable_append r s).comp (measurable_fst.snd.prodMk measurable_snd))
  rw [freshArrayLaw,arrayResidualLaw_append,Measure.fst,Measure.map_map measurable_fst hm,
    freshArrayLaw,Measure.fst,Measure.map_map hm' measurable_fst]
  rfl

lemma freshReference_append {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r s : ℕ) :
    freshReference Γ (r+s) = freshReference Γ r + freshReference (arrayResidualLaw Γ r) s := by
  let P := freshArrayLaw (arrayResidualLaw Γ r) s
  let Q := P.map MeasurableEquiv.prodAssoc
  let : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hQ : Q.map (Prod.map id (appendEquiv (Vector d×ℝ) r s)) = freshArrayLaw Γ (r+s) := by
    dsimp only [Q]
    rw [Measure.map_map (measurable_id.prodMap (appendEquiv _ _ _).measurable)
      MeasurableEquiv.prodAssoc.measurable,freshArrayLaw_append]
    rfl
  have hQf : Q.map (Prod.map id Prod.fst) = freshArrayLaw Γ r := by
    dsimp only [Q]
    rw [Measure.map_map (measurable_id.prodMap measurable_fst) MeasurableEquiv.prodAssoc.measurable]
    change P.fst = freshArrayLaw Γ r
    exact freshArrayLaw_fst _ _
  have hQa : Q.map MeasurableEquiv.prodAssoc.symm = P := MeasurableEquiv.map_symm_map _
  have h := conditionalReferenceKL_outcome_equiv Q
    ((gaussianObservations r d).prod (gaussianObservations s d)) (appendEquiv (Vector d×ℝ) r s)
  rw [hQ,gaussianObservations_append,conditionalReferenceKL_chain Q,hQf,hQa] at h
  exact h



lemma measurable_singleResidualObservation {d : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (singleResidualObservation (d:=d) (C:=C)) := by
  unfold singleResidualObservation; fun_prop

instance singleSignalLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (singleSignalLaw P) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_singleResidualObservation.aemeasurable).mpr inferInstance

instance singleObservationLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (singleObservationLaw P) := by unfold singleObservationLaw; infer_instance

lemma singleObservationLaw_eq {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) :
    singleObservationLaw P = P.map (fun z => (z.1.1,(z.2,⟪(z.1.2:Vector d),z.2⟫))) := by
  rw [singleObservationLaw,singleSignalLaw,Measure.fst,Measure.map_map measurable_fst measurable_singleResidualObservation]
  rfl

lemma singleObservationLaw_fst {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) : (singleObservationLaw P).fst = P.fst.fst := by
  have hm : Measurable (fun z : (C×Sphere d)×Vector d => (z.1.1,(z.2,⟪(z.1.2:Vector d),z.2⟫))) := by fun_prop
  rw [singleObservationLaw_eq,Measure.fst,Measure.map_map measurable_fst hm,
    Measure.fst,Measure.fst,Measure.map_map measurable_fst measurable_fst]
  rfl

lemma singleObservationLaw_scalar {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) :
    singleObservationLaw (Γ.prod (stdGaussian (Vector d))) =
      (scalarObservationLaw Γ).map MeasurableEquiv.prodAssoc := by
  rw [singleObservationLaw_eq,scalarObservationLaw,
    Measure.map_map MeasurableEquiv.prodAssoc.measurable measurable_scalarObservation]
  rfl

lemma singleReference_fresh {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    singleReference (Γ.prod (stdGaussian (Vector d))) =
      conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) := by
  let P := singleObservationLaw (Γ.prod (stdGaussian (Vector d)))
  have hfst : P.map (Prod.map id Prod.fst) = Γ.fst.prod (stdGaussian (Vector d)) := by
    dsimp only [P]
    rw [singleObservationLaw_eq,Measure.map_map (measurable_id.prodMap measurable_fst) (by fun_prop)]
    change (Γ.prod (stdGaussian (Vector d))).map (Prod.map Prod.fst id) = _
    rw [←Measure.map_prod_map Γ _ measurable_fst measurable_id,Measure.map_id]
    rfl
  have ha : P.map MeasurableEquiv.prodAssoc.symm = scalarObservationLaw Γ := by
    dsimp only [P]
    rw [singleObservationLaw_scalar,MeasurableEquiv.map_symm_map]
  change conditionalReferenceKL P ((stdGaussian (Vector d)).prod (gaussianReal 0 1)) = _
  rw [conditionalReferenceKL_chain,hfst,ha,conditionalReferenceKL,Measure.fst_prod,klDiv_self,zero_add]

lemma gaussianRows_one (d : ℕ) :
    (gaussianRows 1 d).map (MeasurableEquiv.funUnique (Fin 1) (Vector d)) = stdGaussian (Vector d) :=
  (measurePreserving_funUnique (stdGaussian (Vector d)) (Fin 1)).map_eq

lemma gaussianObservations_one (d : ℕ) :
    (gaussianObservations 1 d).map (MeasurableEquiv.funUnique (Fin 1) (Vector d×ℝ)) = gaussianObservation d :=
  (measurePreserving_funUnique (gaussianObservation d) (Fin 1)).map_eq

lemma singleSignalLaw_fresh {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    singleSignalLaw (Γ.prod (stdGaussian (Vector d))) = (arrayResidualLaw Γ 1).map
      (Prod.map (Prod.map id (MeasurableEquiv.funUnique (Fin 1) (Vector d×ℝ))) id) := by
  have hprod : Γ.prod (stdGaussian (Vector d)) = (Γ.prod (gaussianRows 1 d)).map
      (Prod.map id (MeasurableEquiv.funUnique (Fin 1) (Vector d))) := by
    rw [←Measure.map_prod_map Γ _ measurable_id (MeasurableEquiv.funUnique _ _).measurable,
      Measure.map_id,gaussianRows_one]
  rw [singleSignalLaw,hprod,Measure.map_map measurable_singleResidualObservation
    (measurable_id.prodMap (MeasurableEquiv.funUnique _ _).measurable),arrayResidualLaw,
    Measure.map_map ((measurable_id.prodMap (MeasurableEquiv.funUnique _ _).measurable).prodMap measurable_id)
      measurable_arrayResidualObservation]
  rfl

lemma freshReference_one {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    freshReference Γ 1 = conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) := by
  have he : singleObservationLaw (Γ.prod (stdGaussian (Vector d))) = (freshArrayLaw Γ 1).map
      (Prod.map id (MeasurableEquiv.funUnique (Fin 1) (Vector d×ℝ))) := by
    rw [singleObservationLaw,singleSignalLaw_fresh,Measure.fst,
      Measure.map_map measurable_fst ((measurable_id.prodMap (MeasurableEquiv.funUnique _ _).measurable).prodMap measurable_id),
      freshArrayLaw,Measure.fst,Measure.map_map (measurable_id.prodMap (MeasurableEquiv.funUnique _ _).measurable) measurable_fst]
    rfl
  have h := conditionalReferenceKL_outcome_equiv (freshArrayLaw Γ 1) (gaussianObservations 1 d)
    (MeasurableEquiv.funUnique (Fin 1) (Vector d×ℝ))
  rw [←he,gaussianObservations_one] at h
  exact h.symm.trans (singleReference_fresh Γ)

lemma freshReference_succ {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    freshReference Γ (r+1) = freshReference Γ r + freshSlope Γ r := by
  rw [freshReference_append,freshReference_one]
  rfl

lemma arrayResidualLaw_context {d : ℕ} {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (Γ : Measure (C×Sphere d)) [SFinite Γ] (r : ℕ) (f : C → D) (hf : Measurable f) :
    arrayResidualLaw (Γ.map (Prod.map f id)) r = (arrayResidualLaw Γ r).map
      (Prod.map (Prod.map f id) id) := by
  rw [arrayResidualLaw,show (Γ.map (Prod.map f id)).prod (gaussianRows r d) =
      (Γ.prod (gaussianRows r d)).map (Prod.map (Prod.map f id) id) by
    rw [←Measure.map_prod_map _ _ (hf.prodMap measurable_id) measurable_id,Measure.map_id],
    Measure.map_map measurable_arrayResidualObservation ((hf.prodMap measurable_id).prodMap measurable_id),
    arrayResidualLaw,Measure.map_map ((hf.prodMap measurable_id).prodMap measurable_id)
      measurable_arrayResidualObservation]
  rfl

lemma freshReference_context {d : ℕ} {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) (e : C ≃ᵐ D) :
    freshReference (Γ.map (Prod.map e id)) r = freshReference Γ r := by
  have hf : freshArrayLaw (Γ.map (Prod.map e id)) r =
      (freshArrayLaw Γ r).map (Prod.map e id) := by
    rw [freshArrayLaw,arrayResidualLaw_context _ _ _ e.measurable,Measure.fst,
      Measure.map_map measurable_fst ((e.measurable.prodMap measurable_id).prodMap measurable_id),
      freshArrayLaw,Measure.fst,Measure.map_map (e.measurable.prodMap measurable_id) measurable_fst]
    rfl
  rw [freshReference,hf]
  exact conditionalReferenceKL_context_equiv _ _ e

lemma arrayResidualLaw_keep {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    (arrayResidualLaw Γ r).map (fun z => (z.1.1,z.2)) = Γ := by
  rw [arrayResidualLaw,Measure.map_map (measurable_fst.fst.prodMk measurable_snd)
    measurable_arrayResidualObservation]
  change (Γ.prod (gaussianRows r d)).fst = Γ
  exact Measure.fst_prod

lemma arrayResidualLaw_drop_last {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    (arrayResidualLaw Γ (r+1)).map
      (Prod.map (fun z => (z.1,fun j : Fin r => z.2 (Fin.castAdd 1 j))) id) = arrayResidualLaw Γ r := by
  have hm : Measurable (fun z : ((C×Observations r d)×Observations 1 d)×Sphere d =>
      ((z.1.1.1,Fin.append z.1.1.2 z.1.2),z.2)) := by
    apply Measurable.prodMk _ measurable_snd
    exact measurable_fst.fst.fst.prodMk ((measurable_append r 1).comp
      (measurable_fst.fst.snd.prodMk measurable_fst.snd))
  have hf : Measurable (fun z : C×Observations (r+1) d =>
      (z.1,fun j : Fin r => z.2 (Fin.castAdd 1 j))) := by fun_prop
  rw [arrayResidualLaw_append,Measure.map_map (hf.prodMap measurable_id) hm]
  have he : (Prod.map (fun z : C×Observations (r+1) d =>
      (z.1,fun j : Fin r => z.2 (Fin.castAdd 1 j))) id) ∘
      (fun z : ((C×Observations r d)×Observations 1 d)×Sphere d =>
        ((z.1.1.1,Fin.append z.1.1.2 z.1.2),z.2)) = (fun z => (z.1.1,z.2)) := by
    funext z
    simp [Prod.map]
  rw [he,arrayResidualLaw_keep]

lemma conditionalReferenceKL_map_context_le {C D A : Type*} [MeasurableSpace C]
    [MeasurableSpace D] [MeasurableSpace A]
    (P : Measure (C×A)) [IsProbabilityMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    (f : C → D) (hf : Measurable f) :
    conditionalReferenceKL (P.map (Prod.map f id)) ν ≤ conditionalReferenceKL P ν := by
  have hfst : (P.map (Prod.map f id)).fst = P.fst.map f := by
    rw [Measure.fst,Measure.map_map measurable_fst (hf.prodMap measurable_id),Measure.fst,
      Measure.map_map hf measurable_fst]
    rfl
  unfold conditionalReferenceKL
  rw [hfst,show (P.fst.map f).prod ν = (P.fst.prod ν).map (Prod.map f id) by
    rw [←Measure.map_prod_map _ _ hf measurable_id,Measure.map_id]]
  exact klDiv_map_le _ _ (hf.prodMap measurable_id)

lemma freshSlope_monotone {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] : Monotone (freshSlope Γ) := by
  apply monotone_nat_of_le_succ
  intro r
  let f : C×Observations (r+1) d → C×Observations r d :=
    fun z => (z.1,fun j : Fin r => z.2 (Fin.castAdd 1 j))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he : arrayResidualLaw Γ r = (arrayResidualLaw Γ (r+1)).map (Prod.map f id) :=
    (arrayResidualLaw_drop_last Γ r).symm
  rw [freshSlope,he,scalarObservationLaw_context _ _ hf]
  exact conditionalReferenceKL_map_context_le _ _ (Prod.map f id) (hf.prodMap measurable_id)

lemma freshReference_monotone {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] : Monotone (freshReference Γ) := by
  apply monotone_nat_of_le_succ
  intro r
  rw [freshReference_succ]
  exact le_add_right le_rfl

lemma freshSlope_mul_le {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r h : ℕ) :
    (h:ℝ≥0∞)*freshSlope Γ r ≤ freshReference Γ (r+h) := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,Nat.add_succ,freshReference_succ]
      exact add_le_add ih (freshSlope_monotone Γ (by omega))

lemma freshSlope_average {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r h : ℕ) (hh : 1 ≤ h)
    (hfin : freshReference Γ (r+h) ≠ ∞) :
    freshSlope Γ r ≠ ∞ ∧ (freshSlope Γ r).toReal ≤ (freshReference Γ (r+h)).toReal / h := by
  have hle : freshSlope Γ r ≤ freshReference Γ (r+h) := by
    apply le_trans _ (freshReference_monotone Γ (show r+1 ≤ r+h by omega))
    rw [freshReference_succ]
    exact le_add_left le_rfl
  have hTf := ne_top_of_le_ne_top hfin hle
  refine ⟨hTf,?_⟩
  have hb := ENNReal.toReal_mono hfin (freshSlope_mul_le Γ r h)
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hb
  apply (le_div_iff₀ (show (0:ℝ)<h by exact_mod_cast (show 0<h by omega))).mpr
  nlinarith



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.RowOrder
attribute [-instance] _root_.OAI.CurrentProjection.endingRowLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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


lemma measurable_liftActualObservation {d r : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (liftActualObservation (d:=d) (r:=r) (C:=C)) := by
  unfold liftActualObservation
  exact ((measurable_fst.fst.fst.prodMk (measurable_ownObservations.comp
    (measurable_snd.prodMk measurable_fst.fst.snd))).prodMk measurable_fst.fst.snd).prodMk measurable_fst.snd

instance liftActualLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    IsProbabilityMeasure (liftActualLaw P r) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_liftActualObservation.aemeasurable).mpr inferInstance

lemma measurable_actualFreshArray {d r : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (fun w : ((C×Sphere d)×Vector d)×Rows r d =>
      (w.1.1.1,((w.1.2,⟪(w.1.1.2:Vector d),w.1.2⟫),ownObservations w.2 w.1.1.2))) := by
  apply Measurable.prodMk measurable_fst.fst.fst
  exact (measurable_fst.snd.prodMk (by fun_prop)).prodMk
    (measurable_ownObservations.comp (measurable_snd.prodMk measurable_fst.fst.snd))

instance actualFreshArrayLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    IsProbabilityMeasure (actualFreshArrayLaw P r) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_actualFreshArray.aemeasurable).mpr inferInstance

lemma actualFreshArrayLaw_first {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    (actualFreshArrayLaw P r).map (Prod.map id Prod.fst) = singleObservationLaw P := by
  rw [actualFreshArrayLaw,Measure.map_map (measurable_id.prodMap measurable_fst) measurable_actualFreshArray]
  have h : (Prod.map id Prod.fst) ∘ (fun w : ((C×Sphere d)×Vector d)×Rows r d =>
      (w.1.1.1,((w.1.2,⟪(w.1.1.2:Vector d),w.1.2⟫),ownObservations w.2 w.1.1.2))) =
      (fun z : (C×Sphere d)×Vector d => (z.1.1,(z.2,⟪(z.1.2:Vector d),z.2⟫))) ∘ Prod.fst := rfl
  rw [h,←Measure.map_map (by fun_prop) measurable_fst]
  change (P.prod (gaussianRows r d)).fst.map _ = _
  rw [Measure.fst_prod,singleObservationLaw_eq]

attribute [fun_prop] measurable_ownObservations

lemma actualFreshArrayLaw_second {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    (actualFreshArrayLaw P r).map MeasurableEquiv.prodAssoc.symm = freshArrayLaw (singleSignalLaw P) r := by
  rw [actualFreshArrayLaw,Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable measurable_actualFreshArray,
    freshArrayLaw_eq,singleSignalLaw,show (P.map singleResidualObservation).prod (gaussianRows r d) =
      (P.prod (gaussianRows r d)).map (Prod.map singleResidualObservation id) by
        rw [←Measure.map_prod_map _ _ measurable_singleResidualObservation measurable_id,Measure.map_id],
    Measure.map_map (by fun_prop)
      (measurable_singleResidualObservation.prodMap measurable_id)]
  rfl

lemma actualFreshArrayLaw_swapped_first {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    ((actualFreshArrayLaw P r).map (Prod.map id Prod.swap)).map (Prod.map id Prod.fst) =
      freshArrayLaw P.fst r := by
  rw [actualFreshArrayLaw,Measure.map_map (measurable_id.prodMap measurable_swap) measurable_actualFreshArray,
    Measure.map_map (measurable_id.prodMap measurable_fst)
      ((measurable_id.prodMap measurable_swap).comp measurable_actualFreshArray),
    freshArrayLaw_eq,show P.fst.prod (gaussianRows r d) =
      (P.prod (gaussianRows r d)).map (Prod.map Prod.fst id) by
        rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]; rfl,
    Measure.map_map (by fun_prop)
      (measurable_fst.prodMap measurable_id)]
  rfl

lemma actualFreshArrayLaw_swapped_second {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    ((actualFreshArrayLaw P r).map (Prod.map id Prod.swap)).map MeasurableEquiv.prodAssoc.symm =
      singleObservationLaw (liftActualLaw P r) := by
  rw [actualFreshArrayLaw,Measure.map_map (measurable_id.prodMap measurable_swap) measurable_actualFreshArray,
    Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      ((measurable_id.prodMap measurable_swap).comp measurable_actualFreshArray),
    singleObservationLaw_eq,liftActualLaw,
    Measure.map_map (by fun_prop) measurable_liftActualObservation]
  rfl

lemma actual_fresh_diamond {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    singleReference P + freshReference (singleSignalLaw P) r =
      freshReference P.fst r + singleReference (liftActualLaw P r) := by
  let : IsProbabilityMeasure ((actualFreshArrayLaw P r).map (Prod.map id Prod.swap)) :=
    Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have he := conditionalReferenceKL_outcome_equiv (actualFreshArrayLaw P r)
    ((gaussianObservation d).prod (gaussianObservations r d)) MeasurableEquiv.prodComm
  change conditionalReferenceKL ((actualFreshArrayLaw P r).map (Prod.map id Prod.swap))
    (((gaussianObservation d).prod (gaussianObservations r d)).map Prod.swap) = _ at he
  rw [Measure.prod_swap] at he
  rw [conditionalReferenceKL_chain,actualFreshArrayLaw_swapped_first,actualFreshArrayLaw_swapped_second,
    conditionalReferenceKL_chain,actualFreshArrayLaw_first,actualFreshArrayLaw_second] at he
  exact he.symm


lemma initialArray_pi {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {i m : ℕ} (hi : i ≤ m) :
    (Measure.pi (fun _ : Fin m => μ)).map (initialArray hi) = Measure.pi (fun _ : Fin i => μ) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [←map_append_pi μ i r,Measure.map_map (measurable_initialArray hi) (measurable_append i r)]
  have he : (initialArray hi) ∘ (fun z : (Fin i→E)×(Fin r→E) => Fin.append z.1 z.2) = Prod.fst := by
    funext z j
    change Fin.append z.1 z.2 (Fin.castLE hi j) = z.1 j
    have hj : Fin.castLE hi j = Fin.castAdd r j := rfl
    rw [hj,Fin.append_left]
  rw [he]
  exact Measure.fst_prod

lemma prefixLaw_fst {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i ≤ m) : (prefixLaw P i hi).fst = P.fst := by
  rw [prefixLaw,Measure.fst,Measure.map_map measurable_fst (measurable_id.prodMap (measurable_initialArray hi))]
  rfl

lemma prefixLaw_self {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) : prefixLaw P m le_rfl = P := by
  change P.map id = P
  rw [Measure.map_id]

lemma prefixLaw_independence {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) (i : ℕ) (hi : i ≤ m) :
    ((prefixLaw P i hi).map swapLast).fst = ν.prod (gaussianRows i d) := by
  have he := congrArg (fun μ : Measure (Sphere d×Rows m d) => μ.map (Prod.map id (initialArray hi))) hInd
  rw [←Measure.map_prod_map _ _ measurable_id (measurable_initialArray hi),Measure.map_id] at he
  change _ = ν.prod ((Measure.pi (fun _ : Fin m => stdGaussian (Vector d))).map (initialArray hi)) at he
  rw [initialArray_pi] at he
  rw [prefixLaw,Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map (measurable_fst.comp swapLast.measurable) (measurable_id.prodMap (measurable_initialArray hi))]
  rw [Measure.fst,Measure.map_map (measurable_id.prodMap (measurable_initialArray hi)) measurable_fst,
    Measure.map_map ((measurable_id.prodMap (measurable_initialArray hi)).comp measurable_fst) swapLast.measurable] at he
  exact he

lemma measurable_observationSignalMap {d k : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (observationSignalMap (d:=d) (k:=k) (W:=W)) := by
  unfold observationSignalMap
  exact (measurable_fst.snd.prodMk (measurable_ownObservations.comp
    (measurable_snd.prodMk measurable_fst.fst))).prodMk measurable_fst.fst

instance observationSignalLaw_probability {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (observationSignalLaw P) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_observationSignalMap.aemeasurable).mpr inferInstance

lemma observationSignalLaw_context {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : (observationSignalLaw P).fst.fst = P.fst.snd := by
  simp only [observationSignalLaw,Measure.fst,Measure.snd]
  rw [Measure.map_map measurable_fst measurable_observationSignalMap,
    Measure.map_map measurable_fst (measurable_fst.comp measurable_observationSignalMap),
    Measure.map_map measurable_snd measurable_fst]
  rfl

lemma measurable_nextActualRow {d m i : ℕ} {W : Type*} [MeasurableSpace W] (hi : i < m) :
    Measurable (fun z : (Sphere d×W)×Rows m d =>
      (((z.1.2,ownObservations (initialArray (Nat.le_of_lt hi) z.2) z.1.1),z.1.1),z.2 ⟨i,hi⟩)) := by
  exact ((measurable_fst.snd.prodMk (measurable_ownObservations.comp
    (((measurable_initialArray _).comp measurable_snd).prodMk measurable_fst.fst))).prodMk
      measurable_fst.fst).prodMk ((measurable_pi_apply _).comp measurable_snd)

instance nextActualRowLaw_probability {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i < m) :
    IsProbabilityMeasure (nextActualRowLaw P i hi) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_nextActualRow hi).aemeasurable).mpr inferInstance

lemma nextActualRowLaw_fst {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i < m) :
    (nextActualRowLaw P i hi).fst = observationSignalLaw (prefixLaw P i (Nat.le_of_lt hi)) := by
  rw [nextActualRowLaw,Measure.fst,Measure.map_map measurable_fst (measurable_nextActualRow hi),
    observationSignalLaw,prefixLaw,Measure.map_map measurable_observationSignalMap
      (measurable_id.prodMap (measurable_initialArray _))]
  rfl

lemma initialArray_snoc {E : Type*} {i m : ℕ} (hi : i < m) (X : Fin m → E) :
    initialArray (Nat.succ_le_of_lt hi) X = Fin.snoc (initialArray (Nat.le_of_lt hi) X) (X ⟨i,hi⟩) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; rfl
  | cast j => simp only [Fin.snoc_castSucc]; rfl

lemma snoc_ownObservations {d i : ℕ} (X : Rows i d) (x : Vector d) (s : Sphere d) :
    ownObservations (Fin.snoc X x) s = Fin.snoc (ownObservations X s) (x,⟪(s:Vector d),x⟫) := by
  funext j
  induction j using Fin.lastCases <;> simp [ownObservations,pairObservation,label]

lemma nextActualRowLaw_single {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i < m) :
    (singleSignalLaw (nextActualRowLaw P i hi)).map
      (Prod.map (MeasurableEquiv.prodAssoc.trans
        ((MeasurableEquiv.refl W).prodCongr (snocEquiv (Vector d×ℝ) i))) id) =
      observationSignalLaw (prefixLaw P (i+1) (Nat.succ_le_of_lt hi)) := by
  rw [singleSignalLaw,nextActualRowLaw,
    Measure.map_map measurable_singleResidualObservation (measurable_nextActualRow hi),
    Measure.map_map ((MeasurableEquiv.measurable _).prodMap measurable_id)
      (measurable_singleResidualObservation.comp (measurable_nextActualRow hi)),
    observationSignalLaw,prefixLaw,Measure.map_map measurable_observationSignalMap
      (measurable_id.prodMap (measurable_initialArray _))]
  congr 1
  funext z
  change ((z.1.2,snocEquiv (Vector d×ℝ) i
    (ownObservations (initialArray (Nat.le_of_lt hi) z.2) z.1.1,
      (z.2 ⟨i,hi⟩,⟪(z.1.1:Vector d),z.2 ⟨i,hi⟩⟫))),z.1.1) =
    ((z.1.2,ownObservations (initialArray (Nat.succ_le_of_lt hi) z.2) z.1.1),z.1.1)
  rw [snocEquiv_apply,initialArray_snoc,snoc_ownObservations]



lemma measurable_rawNextRow {d m i : ℕ} {W : Type*} [MeasurableSpace W] (hi : i < m) :
    Measurable (fun z : (Sphere d×W)×Rows m d => ((z.1,initialArray (Nat.le_of_lt hi) z.2),z.2 ⟨i,hi⟩)) := by
  exact (measurable_fst.prodMk ((measurable_initialArray _).comp measurable_snd)).prodMk
    ((measurable_pi_apply _).comp measurable_snd)

instance rawNextRowLaw_probability {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i < m) :
    IsProbabilityMeasure (rawNextRowLaw P i hi) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_rawNextRow hi).aemeasurable).mpr inferInstance

lemma rawNextRowLaw_fst {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i < m) :
    (rawNextRowLaw P i hi).fst = prefixLaw P i (Nat.le_of_lt hi) := by
  rw [rawNextRowLaw,Measure.fst,Measure.map_map measurable_fst (measurable_rawNextRow hi)]
  rfl

lemma nextActualRowLaw_raw {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i < m) :
    nextActualRowLaw P i hi = (rawNextRowLaw P i hi).map (Prod.map observationSignalMap id) := by
  rw [rawNextRowLaw,Measure.map_map (measurable_observationSignalMap.prodMap measurable_id) (measurable_rawNextRow hi)]
  rfl

lemma rowCharge_eq_raw {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i < m) :
    klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d))) =
      conditionalReferenceKL (rawNextRowLaw P i hi) (stdGaussian (Vector d)) := by
  change conditionalReferenceKL (nextActualRowLaw P i hi) _ = _
  rw [nextActualRowLaw_raw]
  apply conditionalReferenceKL_map_context _ _ _
    (fun z : (W×Observations i d)×Sphere d => ((z.2,z.1.1),fun j => (z.1.2 j).1))
      measurable_observationSignalMap (by fun_prop)
  intro z
  rfl

lemma prefix_rowInformation_step {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i < m) :
    rowInformation (prefixLaw P (i+1) (Nat.succ_le_of_lt hi)) (gaussianRows (i+1) d) =
      rowInformation (prefixLaw P i (Nat.le_of_lt hi)) (gaussianRows i d) +
      klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d))) := by
  let Q := (rawNextRowLaw P i hi).map MeasurableEquiv.prodAssoc
  let : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hfirst : Q.map (Prod.map id Prod.fst) = prefixLaw P i (Nat.le_of_lt hi) := by
    dsimp only [Q]
    rw [Measure.map_map (measurable_id.prodMap measurable_fst) MeasurableEquiv.prodAssoc.measurable]
    exact rawNextRowLaw_fst P i hi
  have htotal : Q.map (Prod.map id (snocEquiv (Vector d) i)) = prefixLaw P (i+1) (Nat.succ_le_of_lt hi) := by
    dsimp only [Q]
    rw [rawNextRowLaw,Measure.map_map MeasurableEquiv.prodAssoc.measurable (measurable_rawNextRow hi),
      Measure.map_map (measurable_id.prodMap (snocEquiv (Vector d) i).measurable)
        (MeasurableEquiv.prodAssoc.measurable.comp (measurable_rawNextRow hi)),prefixLaw]
    congr 1
    funext z
    change (z.1,snocEquiv (Vector d) i (initialArray (Nat.le_of_lt hi) z.2,z.2 ⟨i,hi⟩)) =
      (z.1,initialArray (Nat.succ_le_of_lt hi) z.2)
    rw [snocEquiv_apply,initialArray_snoc]
  have he := conditionalReferenceKL_outcome_equiv Q
    ((gaussianRows i d).prod (stdGaussian (Vector d))) (snocEquiv (Vector d) i)
  rw [show (((gaussianRows i d).prod (stdGaussian (Vector d))).map (snocEquiv (Vector d) i)) =
      gaussianRows (i+1) d from snocEquiv_map (stdGaussian (Vector d)) i,htotal,
    conditionalReferenceKL_chain,hfirst] at he
  dsimp only [Q] at he
  rw [MeasurableEquiv.map_symm_map,←rowCharge_eq_raw P i hi] at he
  exact he



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.ArrayBounds
attribute [-instance] _root_.OAI.CurrentProjection.endingRowLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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


lemma observationSignalLaw_fst_as_observed {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) :
    (observationSignalLaw P).fst = (observedMessage P).map
      (MeasurableEquiv.prodComm.trans ((MeasurableEquiv.refl W).prodCongr (observationEquiv k d))) := by
  rw [observationSignalLaw,Measure.fst,Measure.map_map measurable_fst measurable_observationSignalMap,
    observedMessage,Measure.map_map (MeasurableEquiv.measurable _) measurable_observedMessageMap]
  rfl

lemma arrayReference_eq {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    arrayReference P = observationReferenceKL P := by
  let e := MeasurableEquiv.prodComm.trans ((MeasurableEquiv.refl W).prodCongr (observationEquiv k d))
  have href : (((gaussianRows k d).prod (gaussianLabels k)).prod P.fst.snd).map e =
      P.fst.snd.prod (gaussianObservations k d) := by
    change ((((gaussianRows k d).prod (gaussianLabels k)).prod P.fst.snd)).map
      ((Prod.map id (observationEquiv k d)) ∘ Prod.swap) = _
    rw [←Measure.map_map (measurable_id.prodMap (observationEquiv k d).measurable) measurable_swap,
      Measure.prod_swap,←Measure.map_prod_map _ _ measurable_id (observationEquiv k d).measurable,
      Measure.map_id,←gaussianObservations_eq]
  rw [arrayReference,conditionalReferenceKL,observationSignalLaw_context,
    observationSignalLaw_fst_as_observed,←href]
  exact klDiv_map_equiv _ _ e

lemma freshArrayLaw_assoc_first {d k r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    ((freshArrayLaw (observationSignalLaw P) r).map MeasurableEquiv.prodAssoc).map
      (Prod.map id Prod.fst) = (observationSignalLaw P).fst := by
  rw [Measure.map_map (measurable_id.prodMap measurable_fst) MeasurableEquiv.prodAssoc.measurable]
  change (freshArrayLaw (observationSignalLaw P) r).fst = _
  rw [freshArrayLaw_fst]

lemma freshArrayLaw_aligned {d k r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    ((freshArrayLaw (observationSignalLaw P) r).map MeasurableEquiv.prodAssoc).map
      (Prod.map id (appendEquiv (Vector d×ℝ) k r)) =
      (observationSignalLaw (alignedExperiment (r:=r) P)).fst := by
  rw [freshArrayLaw_eq,observationSignalLaw,
    show (P.map observationSignalMap).prod (gaussianRows r d) =
      (P.prod (gaussianRows r d)).map (Prod.map observationSignalMap id) by
        rw [←Measure.map_prod_map _ _ measurable_observationSignalMap measurable_id,Measure.map_id],
    Measure.map_map (by fun_prop) (measurable_observationSignalMap.prodMap measurable_id),
    Measure.map_map MeasurableEquiv.prodAssoc.measurable (by fun_prop),
    Measure.map_map (measurable_id.prodMap (appendEquiv _ _ _).measurable) (by fun_prop),
    observationSignalLaw,alignedExperiment,Measure.fst,
    Measure.map_map measurable_fst measurable_observationSignalMap,
    Measure.map_map (measurable_fst.comp measurable_observationSignalMap) measurable_alignedMap]
  congr 1
  funext z
  dsimp [actualExperiment,observationSignalMap]
  rw [ownObservations_append]
  rfl

lemma arrayReference_aligned {d k r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    arrayReference (alignedExperiment (r:=r) P) =
      arrayReference P + freshReference (observationSignalLaw P) r := by
  let Q := (freshArrayLaw (observationSignalLaw P) r).map MeasurableEquiv.prodAssoc
  let : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have he := conditionalReferenceKL_outcome_equiv Q
    ((gaussianObservations k d).prod (gaussianObservations r d)) (appendEquiv (Vector d×ℝ) k r)
  rw [gaussianObservations_append] at he
  dsimp only [Q] at he
  rw [freshArrayLaw_aligned,conditionalReferenceKL_chain,freshArrayLaw_assoc_first,
    MeasurableEquiv.map_symm_map] at he
  exact he

lemma arrayReference_prefix_step {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i < m) :
    arrayReference (prefixLaw P (i+1) (Nat.succ_le_of_lt hi)) =
      arrayReference (prefixLaw P i (Nat.le_of_lt hi)) + singleReference (nextActualRowLaw P i hi) := by
  let Q := (singleObservationLaw (nextActualRowLaw P i hi)).map MeasurableEquiv.prodAssoc
  let : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hfirst : Q.map (Prod.map id Prod.fst) = (observationSignalLaw (prefixLaw P i (Nat.le_of_lt hi))).fst := by
    rw [Measure.map_map (measurable_id.prodMap measurable_fst) MeasurableEquiv.prodAssoc.measurable]
    change (singleObservationLaw (nextActualRowLaw P i hi)).fst = _
    rw [singleObservationLaw_fst,nextActualRowLaw_fst]
  have htotal : Q.map (Prod.map id (snocEquiv (Vector d×ℝ) i)) =
      (observationSignalLaw (prefixLaw P (i+1) (Nat.succ_le_of_lt hi))).fst := by
    have he := congrArg (fun μ : Measure ((W×Observations (i+1) d)×Sphere d) => μ.fst)
      (nextActualRowLaw_single P i hi)
    rw [Measure.fst,Measure.map_map measurable_fst ((MeasurableEquiv.measurable _).prodMap measurable_id)] at he
    dsimp only [Q,singleObservationLaw]
    rw [Measure.map_map (measurable_id.prodMap (snocEquiv _ _).measurable) MeasurableEquiv.prodAssoc.measurable,
      Measure.fst,Measure.map_map (by fun_prop) measurable_fst]
    exact he
  have he := conditionalReferenceKL_outcome_equiv Q
    ((gaussianObservations i d).prod (gaussianObservation d)) (snocEquiv (Vector d×ℝ) i)
  rw [show (((gaussianObservations i d).prod (gaussianObservation d)).map (snocEquiv (Vector d×ℝ) i)) =
      gaussianObservations (i+1) d from snocEquiv_map (gaussianObservation d) i,htotal,
    conditionalReferenceKL_chain,hfirst] at he
  dsimp only [Q] at he
  rw [MeasurableEquiv.map_symm_map] at he
  exact he



lemma hybridBaselineConstant_pos : 0 < hybridBaselineConstant := by
  unfold hybridBaselineConstant
  positivity

lemma baselineCost_finite {d k : ℕ} (hk : 2 ≤ k) (hkd : k < d-1) :
    baselineCost d k ≠ ∞ ∧ (baselineCost d k).toReal ≤ hybridBaselineConstant*d := by
  have hd : 2 ≤ d := by omega
  have hdim : AdmissibleDimensions d 1 (k-1) 1 := by
    unfold AdmissibleDimensions
    omega
  have he : 1+(k-1) = k := by omega
  have h := sphere_projection_reference_finite hdim hd
  rw [he] at h
  refine ⟨h.1,h.2.trans ?_⟩
  have hcast : (k:ℝ) ≤ d := by exact_mod_cast (show k ≤ d by omega)
  have hg := le_abs_self (Real.log (normalizer 1)+1/2)
  have hg0 := abs_nonneg (Real.log (normalizer 1)+1/2)
  dsimp [hybridBaselineConstant]
  nlinarith

lemma arrayReference_finite_bound {d k : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (hd : 1 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows k d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B)
    (hk : 2 ≤ k) (hkd : k < d-1) :
    arrayReference P ≠ ∞ ∧ (arrayReference P).toReal ≤ hybridBaselineConstant*d+B := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos hd
  have hHf : shannonEntropy (observedMessage P).snd ≠ ∞ := by
    rw [observedMessage_snd]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH
  have hI := countable_information_le_entropy (observedMessage P) hHf
  have hbase := baselineCost_finite hk hkd
  rw [arrayReference_eq,observationReferenceKL_decomposition P (uniformSphere d) hInd]
  change baselineCost d k + mutualInformation (observedMessage P) ≠ ∞ ∧
    (baselineCost d k + mutualInformation (observedMessage P)).toReal ≤ hybridBaselineConstant*d+B
  have hIf : mutualInformation (observedMessage P) ≠ ∞ := hI.1
  refine ⟨ENNReal.add_ne_top.mpr ⟨hbase.1,hI.1⟩,?_⟩
  rw [ENNReal.toReal_add hbase.1 hIf]
  have hHb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hH
  rw [ENNReal.toReal_ofReal hB] at hHb
  apply add_le_add hbase.2
  apply hI.2.trans
  simpa only [observedMessage_snd] using hHb

lemma arrayReference_exposed_chain {d k : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W] [Nonempty (Sphere d)]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (hd : 1 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows k d)) :
    arrayReference P + exposedInformation P =
      baselineCost d k + mutualInformation P.fst + rowInformation P (gaussianRows k d) := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos hd
  rw [arrayReference_eq]
  exact observationReferenceKL_chain_exposed P (uniformSphere d) hInd

lemma exposedInformation_finite {d k : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W] [Nonempty (Sphere d)]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (hH : shannonEntropy P.fst.snd ≠ ∞) : exposedInformation P ≠ ∞ := by
  have he := exposedInformation_chain P
  let : IsProbabilityMeasure (P.map swapLast) := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hi := countable_information_le_entropy (P.map swapLast) (by rwa [swapLast_snd])
  exact ne_top_of_le_ne_top hi.1 (by change exposedInformation P ≤ mutualInformation (P.map swapLast); rw [he]; exact le_add_left le_rfl)

lemma rowInformation_finite_bound {d k : ℕ} {W : Type*}
    [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (hd : 1 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows k d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B) :
    rowInformation P (gaussianRows k d) ≠ ∞ ∧ (rowInformation P (gaussianRows k d)).toReal ≤ B := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos hd
  have h := rowInformation_le_entropy P (uniformSphere d) (gaussianRows k d) hInd
    (by rw [swapLast_snd]; exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH)
  rw [swapLast_snd] at h
  have hHb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hH
  rw [ENNReal.toReal_ofReal hB] at hHb
  exact ⟨h.1,h.2.trans hHb⟩

lemma freshReference_from_array_bound {d i r : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows i d)) [IsProbabilityMeasure P]
    (hd : 1 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows i d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B)
    (hk : 2 ≤ i+r) (hkd : i+r < d-1) :
    freshReference (observationSignalLaw P) r ≠ ∞ ∧
      (freshReference (observationSignalLaw P) r).toReal ≤ hybridBaselineConstant*d+B := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos hd
  have h := arrayReference_finite_bound (alignedExperiment (r:=r) P) hd
    (alignedExperiment_independence P (uniformSphere d) hInd) hB
    (by rwa [alignedExperiment_fst]) hk hkd
  have hl : freshReference (observationSignalLaw P) r ≤ arrayReference (alignedExperiment (r:=r) P) := by
    rw [arrayReference_aligned]
    exact le_add_left le_rfl
  exact ⟨ne_top_of_le_ne_top h.1 hl,(ENNReal.toReal_mono h.1 hl).trans h.2⟩

lemma freshSlope_from_array_bound {d i r : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows i d)) [IsProbabilityMeasure P]
    (hd : 16 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows i d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B)
    (hk : 2 ≤ i+r+d/8) (hkd : i+r+d/8 < d-1) :
    freshSlope (observationSignalLaw P) r ≠ ∞ ∧
      (freshSlope (observationSignalLaw P) r).toReal ≤ 16*hybridBaselineConstant+B/(d/8:ℕ) := by
  have h := freshReference_from_array_bound (r:=r+d/8) P (by omega) hInd hB hH (by omega) (by omega)
  have ha := freshSlope_average (observationSignalLaw P) r (d/8) (by omega) h.1
  refine ⟨ha.1,ha.2.trans ?_⟩
  have hp : (0:ℝ)<(d/8:ℕ) := by exact_mod_cast (show 0<d/8 by omega)
  have hratio : (d:ℝ) ≤ 16*(d/8:ℕ) := by exact_mod_cast (show d ≤ 16*(d/8) by omega)
  have hbpos := hybridBaselineConstant_pos
  apply (div_le_iff₀ hp).mpr
  calc
    (freshReference (observationSignalLaw P) (r+d/8)).toReal ≤ hybridBaselineConstant*d+B := h.2
    _ ≤ (16*hybridBaselineConstant+B/(d/8:ℕ))*(d/8:ℕ) := by
      rw [add_mul,div_mul_cancel₀ _ hp.ne']
      nlinarith


lemma arrayReference_actual_step {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i < m) (r : ℕ) :
    arrayReference (alignedExperiment (r:=r) (prefixLaw P (i+1) (Nat.succ_le_of_lt hi))) =
      arrayReference (alignedExperiment (r:=r) (prefixLaw P i (Nat.le_of_lt hi))) +
      singleReference (liftActualLaw (nextActualRowLaw P i hi) r) := by
  have hc : freshReference (observationSignalLaw (prefixLaw P (i+1) (Nat.succ_le_of_lt hi))) r =
      freshReference (singleSignalLaw (nextActualRowLaw P i hi)) r := by
    rw [←nextActualRowLaw_single P i hi]
    exact freshReference_context _ _ _
  rw [arrayReference_aligned,arrayReference_aligned,arrayReference_prefix_step,hc,add_assoc,
    actual_fresh_diamond,nextActualRowLaw_fst,←add_assoc]

lemma nextActualRowLaw_signal_row {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) (i : ℕ) (hi : i < m) :
    (nextActualRowLaw P i hi).map (fun z => (z.1.2,z.2)) = ν.prod (stdGaussian (Vector d)) := by
  have he := congrArg (fun μ : Measure (Sphere d×Rows m d) => μ.map (Prod.map id (fun X => X ⟨i,hi⟩))) hInd
  rw [←Measure.map_prod_map _ _ measurable_id (measurable_pi_apply _),Measure.map_id] at he
  have hev : (gaussianRows m d).map (fun X => X ⟨i,hi⟩) = stdGaussian (Vector d) :=
    (measurePreserving_eval (fun _ : Fin m => stdGaussian (Vector d)) ⟨i,hi⟩).map_eq
  rw [hev] at he
  rw [nextActualRowLaw,Measure.map_map (measurable_fst.snd.prodMk measurable_snd) (measurable_nextActualRow hi)]
  rw [Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map (measurable_id.prodMap (measurable_pi_apply _)) (measurable_fst.comp swapLast.measurable)] at he
  exact he

lemma gaussian_sphere_inner_mixture {d : ℕ} (ν : Measure (Sphere d)) [IsProbabilityMeasure ν] :
    (ν.prod (stdGaussian (Vector d))).map (fun z => ⟪(z.1:Vector d),z.2⟫) = gaussianReal 0 1 := by
  ext t ht
  rw [Measure.map_apply (by fun_prop) ht,Measure.prod_apply (ht.preimage (by fun_prop))]
  have he (s : Sphere d) : stdGaussian (Vector d) {x | ⟪(s:Vector d),x⟫ ∈ t} = gaussianReal 0 1 t := by
    have h := congrArg (fun μ : Measure ℝ => μ t) (gaussian_inner_map_sphere s)
    rwa [Measure.map_apply (by fun_prop) ht] at h
  change (∫⁻ s : Sphere d, stdGaussian (Vector d) {x | ⟪(s:Vector d),x⟫ ∈ t} ∂ν) = _
  simp_rw [he]
  simp

lemma nextActualRowLaw_label {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) (i : ℕ) (hi : i < m) (r : ℕ) :
    (residualLabelLaw (nextActualRowLaw P i hi) r).snd = gaussianReal 0 1 := by
  rw [residualLabelLaw,Measure.snd,Measure.map_map measurable_snd measurable_residualLabelObservation]
  have hel : Measurable (fun z : ((W×Observations i d)×Sphere d)×Vector d => ⟪(z.1.2:Vector d),z.2⟫) := by fun_prop
  change ((nextActualRowLaw P i hi).prod (gaussianRows r d)).map ((fun z => ⟪(z.1.2:Vector d),z.2⟫) ∘ Prod.fst) = _
  rw [←Measure.map_map hel measurable_fst,←Measure.fst,Measure.fst_prod]
  have he := congrArg (fun μ : Measure (Sphere d×Vector d) => μ.map (fun z => ⟪(z.1:Vector d),z.2⟫))
    (nextActualRowLaw_signal_row P ν hInd i hi)
  rw [Measure.map_map (by fun_prop) (measurable_fst.snd.prodMk measurable_snd),gaussian_sphere_inner_mixture] at he
  exact he

lemma hybrid_one_step {d m i r q : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (hd : 16 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B)
    (hi : i < m) (hr : r ≤ d) (hd8 : d ≤ 8*r) (hq : 1 ≤ q)
    (hqr : 2*q ≤ r) (hmargin : 2 ≤ r-q) (htotal : i+r+2 < d-1) :
    (exposedInformation (alignedExperiment (r:=r+1) (prefixLaw P i (Nat.le_of_lt hi)))).toReal -
      (exposedInformation (alignedExperiment (r:=r) (prefixLaw P (i+1) (Nat.succ_le_of_lt hi)))).toReal ≤
        hybridRowConstant +
        (klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d)))).toReal/q +
        (freshSlope (observationSignalLaw (prefixLaw P i (Nat.le_of_lt hi))) (r+1)).toReal -
        (freshSlope (observationSignalLaw (prefixLaw P i (Nat.le_of_lt hi))) r).toReal := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  let P0 := prefixLaw P i (Nat.le_of_lt hi)
  let P1 := prefixLaw P (i+1) (Nat.succ_le_of_lt hi)
  have hI0 : (P0.map swapLast).fst = (uniformSphere d).prod (gaussianRows i d) :=
    prefixLaw_independence P (uniformSphere d) hInd _ _
  have hI1 : (P1.map swapLast).fst = (uniformSphere d).prod (gaussianRows (i+1) d) :=
    prefixLaw_independence P (uniformSphere d) hInd _ _
  have hH0 : shannonEntropy P0.fst.snd ≤ ENNReal.ofReal B := by rwa [prefixLaw_fst]
  have hH1 : shannonEntropy P1.fst.snd ≤ ENNReal.ofReal B := by rwa [prefixLaw_fst]
  have hR0 := rowInformation_finite_bound P0 (by omega) hI0 hB hH0
  have hR1 := rowInformation_finite_bound P1 (by omega) hI1 hB hH1
  have hKchain := prefix_rowInformation_step P i hi
  change rowInformation P1 _ = rowInformation P0 _ + _ at hKchain
  have hK : klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d))) ≠ ∞ :=
    ne_top_of_le_ne_top hR1.1 (by rw [hKchain]; exact le_add_left le_rfl)
  have hF0 := freshReference_from_array_bound (r:=r+1) P0 (by omega) hI0 hB hH0 (by omega) (by omega)
  have hF1 := freshReference_from_array_bound (r:=r+1+1) P0 (by omega) hI0 hB hH0 (by omega) (by omega)
  have hT0 := (freshSlope_average (observationSignalLaw P0) r 1 (by omega) hF0.1).1
  have hT1 := (freshSlope_average (observationSignalLaw P0) (r+1) 1 (by omega) hF1.1).1
  have hcross := actual_fresh_row_bound (nextActualRowLaw P i hi) hK hr hd8 hq hqr hmargin
    (by rwa [nextActualRowLaw_fst]) (by rwa [nextActualRowLaw_fst])
    (nextActualRowLaw_label P (uniformSphere d) hInd i hi r)
  rw [nextActualRowLaw_fst] at hcross
  have hA0 := arrayReference_finite_bound (alignedExperiment (r:=r) P0) (by omega)
    (alignedExperiment_independence P0 (uniformSphere d) hI0) hB (by rwa [alignedExperiment_fst]) (by omega) (by omega)
  have hAl := arrayReference_finite_bound (alignedExperiment (r:=r+1) P0) (by omega)
    (alignedExperiment_independence P0 (uniformSphere d) hI0) hB (by rwa [alignedExperiment_fst]) (by omega) (by omega)
  have hAr := arrayReference_finite_bound (alignedExperiment (r:=r) P1) (by omega)
    (alignedExperiment_independence P1 (uniformSphere d) hI1) hB (by rwa [alignedExperiment_fst]) (by omega) (by omega)
  have hJ0 := exposedInformation_finite (alignedExperiment (r:=r+1) P0)
    (by rw [alignedExperiment_fst]; exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH0)
  have hJ1 := exposedInformation_finite (alignedExperiment (r:=r) P1)
    (by rw [alignedExperiment_fst]; exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH1)
  have hMI : mutualInformation P.fst ≠ ∞ := (countable_information_le_entropy P.fst (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH)).1
  have hbase := (baselineCost_finite (d:=d) (k:=i+(r+1)) (by omega) (by omega)).1
  have hc0 := arrayReference_exposed_chain (alignedExperiment (r:=r+1) P0) (by omega)
    (alignedExperiment_independence P0 (uniformSphere d) hI0)
  have hc1 := arrayReference_exposed_chain (alignedExperiment (r:=r) P1) (by omega)
    (alignedExperiment_independence P1 (uniformSphere d) hI1)
  rw [alignedExperiment_fst,rowInformation_alignedExperiment] at hc0 hc1
  change _ = baselineCost d (i+(r+1)) + mutualInformation P0.fst + _ at hc0
  change _ = baselineCost d (i+1+r) + mutualInformation P1.fst + _ at hc1
  have hPf0 : P0.fst = P.fst := prefixLaw_fst _ _ _
  have hPf1 : P1.fst = P.fst := prefixLaw_fst _ _ _
  rw [hPf0] at hc0
  have hbe : baselineCost d (i+1+r) = baselineCost d (i+(r+1)) := congrArg (baselineCost d) (by omega)
  rw [hPf1,hbe] at hc1
  have hc0r := congrArg ENNReal.toReal hc0
  have hc1r := congrArg ENNReal.toReal hc1
  rw [ENNReal.toReal_add hAl.1 hJ0,ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hbase,hMI⟩) hR0.1,
    ENNReal.toReal_add hbase hMI] at hc0r
  rw [ENNReal.toReal_add hAr.1 hJ1,ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hbase,hMI⟩) hR1.1,
    ENNReal.toReal_add hbase hMI] at hc1r
  have hKreal := congrArg ENNReal.toReal hKchain
  rw [ENNReal.toReal_add hR0.1 hK] at hKreal
  have har := arrayReference_actual_step P i hi r
  have harr := congrArg ENNReal.toReal har
  rw [ENNReal.toReal_add hA0.1 hcross.1] at harr
  have hal : arrayReference (alignedExperiment (r:=r+1) P0) =
      arrayReference (alignedExperiment (r:=r) P0) + freshSlope (observationSignalLaw P0) r := by
    rw [arrayReference_aligned,arrayReference_aligned,freshReference_succ,add_assoc]
  have halr := congrArg ENNReal.toReal hal
  rw [ENNReal.toReal_add hA0.1 hT0] at halr
  change _ ≤ hybridRowConstant + _ + (freshSlope (observationSignalLaw P0) (r+1)).toReal -
    (freshSlope (observationSignalLaw P0) r).toReal
  rw [nextActualRowLaw_fst] at hKreal ⊢
  linarith [hcross.2]



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Telescopes
attribute [-instance] _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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


lemma averaged_telescope_block {m a b : ℕ} (hab : a ≤ b)
    (J T : ℕ → ℕ → ℝ) (K : ℕ → ℝ) (C S B q : ℝ) (hq : 0 < q)
    (hstep : ∀ i < m, ∀ k ∈ Finset.Icc a b,
      J i k-J (i+1) k ≤ C+K i/q+T i (k+1)-T i k)
    (hfirst : ∀ i < m, 0 ≤ T i a)
    (hlast : ∀ i < m, T i (b+1) ≤ S)
    (hK : ∑ i ∈ Finset.range m, K i ≤ B) :
    (∑ k ∈ Finset.Icc a b, J 0 k)/(b-a+1:ℕ) -
      (∑ k ∈ Finset.Icc a b, J m k)/(b-a+1:ℕ) ≤
        C*m+(m:ℝ)/(b-a+1:ℕ)*S+B/q := by
  let N : ℝ := (b-a+1:ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hcard : ((Finset.Icc a b).card:ℝ) = N := by
    dsimp [N]
    simp only [Nat.card_Icc]
    congr 1
    omega
  have he : Finset.Icc a b = Finset.Ico a (b+1) := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  have hs (i : ℕ) : ∑ k ∈ Finset.Icc a b, (T i (k+1)-T i k) = T i (b+1)-T i a := by
    rw [he]
    exact Finset.sum_Ico_sub _ (by omega)
  let F : ℕ → ℝ := fun i => (∑ k ∈ Finset.Icc a b, J i k)/N
  have hrow (i : ℕ) (hi : i < m) : F i-F (i+1) ≤ C+S/N+K i/q := by
    have h := Finset.sum_le_sum (fun k hk => hstep i hi k hk)
    have hrepr : ∑ k ∈ Finset.Icc a b, (C+K i/q+T i (k+1)-T i k) =
        N*(C+K i/q)+T i (b+1)-T i a := by
      simp_rw [show ∀ k, C+K i/q+T i (k+1)-T i k = (C+K i/q)+(T i (k+1)-T i k) by intro k; ring]
      rw [Finset.sum_add_distrib,hs,Finset.sum_const,nsmul_eq_mul,hcard]
      ring
    rw [hrepr,Finset.sum_sub_distrib] at h
    dsimp only [F]
    rw [←sub_div]
    apply (div_le_iff₀ hN).mpr
    have hfirst' := hfirst i hi
    have hlast' := hlast i hi
    calc
      _ ≤ N*(C+K i/q)+S := by linarith
      _ = (C+S/N+K i/q)*N := by field_simp; ring
  have hsum := Finset.sum_le_sum (fun i hi => hrow i (Finset.mem_range.mp hi))
  rw [Finset.sum_range_sub'] at hsum
  have hsumr : ∑ i ∈ Finset.range m, (C+S/N+K i/q) =
      (m:ℝ)*(C+S/N)+(∑ i ∈ Finset.range m, K i)/q := by
    rw [Finset.sum_add_distrib,Finset.sum_div,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [hsumr] at hsum
  have hKq := div_le_div_of_nonneg_right hK hq.le
  change F 0-F m ≤ C*m+(m:ℝ)/N*S+B/q
  calc
    _ ≤ (m:ℝ)*(C+S/N)+(∑ i ∈ Finset.range m, K i)/q := hsum
    _ ≤ (m:ℝ)*(C+S/N)+B/q := add_le_add_right hKq _
    _ = _ := by ring



lemma prefix_charge_sum {d m : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (hd : 1 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B) :
    (∑ i ∈ Finset.range m, (if hi : i < m then
      (klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d)))).toReal else 0)) ≤ B := by
  classical
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos hd
  let R : ℕ → ℝ := fun i => if hi : i ≤ m then
    (rowInformation (prefixLaw P i hi) (gaussianRows i d)).toReal else 0
  have hR (i : ℕ) (hi : i ≤ m) := rowInformation_finite_bound (prefixLaw P i hi) hd
    (prefixLaw_independence P (uniformSphere d) hInd i hi) hB (by rwa [prefixLaw_fst])
  have hstep (i : ℕ) (hi : i < m) :
      (klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d)))).toReal = R (i+1)-R i := by
    have he := prefix_rowInformation_step P i hi
    have hK : klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d))) ≠ ∞ :=
      ne_top_of_le_ne_top (hR (i+1) (by omega)).1 (by rw [he]; exact le_add_left le_rfl)
    have her := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_add (hR i (by omega)).1 hK] at her
    simp only [R,dite_eq_left (Nat.le_of_lt hi),dite_eq_left (Nat.succ_le_of_lt hi)]
    linarith
  have he : (∑ i ∈ Finset.range m, (if hi : i < m then
      (klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d)))).toReal else 0)) = R m-R 0 := by
    calc
      _ = ∑ i ∈ Finset.range m, (R (i+1)-R i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [dite_eq_left (Finset.mem_range.mp hi),hstep i (Finset.mem_range.mp hi)]
      _ = _ := Finset.sum_range_sub R m
  rw [he]
  have h0 : 0 ≤ R 0 := by simp only [R,dite_eq_left (Nat.zero_le m)]; exact ENNReal.toReal_nonneg
  have hm : R m ≤ B := by simp only [R,dite_eq_left le_rfl]; exact (hR m le_rfl).2
  linarith

lemma hybrid_average_ending {d m : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (hd : 256 ≤ d) (hm : m ≤ d/8)
    (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B) :
    (∑ k ∈ Finset.Icc (hybridFirst d) (hybridLast d),
      (exposedInformation (alignedExperiment (r:=k) (prefixLaw P 0 (Nat.zero_le m)))).toReal)/hybridCount d -
    (∑ k ∈ Finset.Icc (hybridFirst d) (hybridLast d),
      (exposedInformation (alignedExperiment (r:=k-m) P)).toReal)/hybridCount d ≤
      hybridRowConstant*m + (m:ℝ)/hybridCount d*(16*hybridBaselineConstant+B/(d/8:ℕ))+B/(d/32:ℕ) := by
  classical
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let J : ℕ → ℕ → ℝ := fun i k => if hi : i ≤ m then
    (exposedInformation (alignedExperiment (r:=k-i) (prefixLaw P i hi))).toReal else 0
  let T : ℕ → ℕ → ℝ := fun i k => if hi : i ≤ m then
    (freshSlope (observationSignalLaw (prefixLaw P i hi)) (k-i-1)).toReal else 0
  let K : ℕ → ℝ := fun i => if hi : i < m then
    (klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d)))).toReal else 0
  have hab : hybridFirst d ≤ hybridLast d := by unfold hybridFirst hybridLast; omega
  have hstep (i : ℕ) (hi : i < m) (k : ℕ) (hk : k ∈ Finset.Icc (hybridFirst d) (hybridLast d)) :
      J i k-J (i+1) k ≤ hybridRowConstant+K i/(d/32:ℕ)+T i (k+1)-T i k := by
    obtain ⟨hka,hkb⟩ := Finset.mem_Icc.mp hk
    dsimp [hybridFirst,hybridLast] at hka hkb
    have h := hybrid_one_step (r:=k-(i+1)) (q:=d/32) P (by omega) hInd hB hH hi
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [J,T,K,dite_eq_left (Nat.le_of_lt hi),dite_eq_left (Nat.succ_le_of_lt hi),dite_eq_left hi]
    have hsub0 : k-i = k-(i+1)+1 := by omega
    have hsub1 : k+1-i-1 = k-(i+1)+1 := by omega
    have hsub2 : k-i-1 = k-(i+1) := by omega
    rw [hsub1,hsub2,hsub0]
    exact h
  have hfirst (i : ℕ) (hi : i < m) : 0 ≤ T i (hybridFirst d) := by
    simp only [T,dite_eq_left (Nat.le_of_lt hi)]
    exact ENNReal.toReal_nonneg
  have hlast (i : ℕ) (hi : i < m) : T i (hybridLast d+1) ≤ 16*hybridBaselineConstant+B/(d/8:ℕ) := by
    simp only [T,dite_eq_left (Nat.le_of_lt hi)]
    apply (freshSlope_from_array_bound (prefixLaw P i (Nat.le_of_lt hi)) (by omega)
      (prefixLaw_independence P (uniformSphere d) hInd i _) hB (by rwa [prefixLaw_fst]) ?_ ?_).2
    · unfold hybridLast; omega
    · unfold hybridLast; omega
  have hsum := averaged_telescope_block hab J T K hybridRowConstant
    (16*hybridBaselineConstant+B/(d/8:ℕ)) B (d/32:ℕ) (by exact_mod_cast (show 0 < d/32 by omega))
      hstep hfirst hlast (prefix_charge_sum P (by omega) hInd hB hH)
  simpa only [J,dite_eq_left (Nat.zero_le m),dite_eq_left le_rfl,Nat.sub_zero,prefixLaw_self,hybridCount] using hsum



lemma processedKernel_apply_prod {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] (z : Z)
    {s : Set A} {t : Set C} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    processedKernel α η z (s×ˢt) = ∫⁻ p in s×ˢSet.univ, η (z,p.2) t ∂α z := by
  rw [processedKernel,Kernel.map_apply _ (measurable_fst.fst.prodMk measurable_snd),Measure.map_apply (measurable_fst.fst.prodMk measurable_snd) (hs.prod ht)]
  rw [show (fun p : (A×B)×C => (p.1.1,p.2)) ⁻¹' (s×ˢt) = (s×ˢSet.univ)×ˢt by ext p; simp]
  rw [Kernel.compProd_apply_prod (hs.prod MeasurableSet.univ) ht]
  rfl

lemma processedKernel_fst {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] : (processedKernel α η).fst = α.fst := by
  rw [processedKernel,Kernel.fst_eq,←Kernel.map_comp_right _ (measurable_fst.fst.prodMk measurable_snd) measurable_fst]
  change (α ⊗ₖ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).map (Prod.fst ∘ Prod.fst) = _
  rw [Kernel.map_comp_right _ measurable_fst measurable_fst]
  rw [←Kernel.fst_eq,←Kernel.fst_eq,Kernel.fst_compProd]

lemma processedKernel_snd_apply {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] (z : Z) {t : Set C} (ht : MeasurableSet t) :
    (processedKernel α η).snd z t = ∫⁻ b, η (z,b) t ∂α.snd z := by
  rw [Kernel.snd_apply' _ _ ht]
  rw [show (Prod.snd : A×C → C) ⁻¹' t = Set.univ×ˢt by ext p; simp]
  rw [processedKernel_apply_prod α η z MeasurableSet.univ ht]
  simp only [Set.univ_prod_univ,Measure.restrict_univ]
  rw [Kernel.snd_eq,Kernel.map_apply _ measurable_snd]
  rw [lintegral_map (by exact (η.measurable_coe ht).comp (measurable_const.prodMk measurable_id)) measurable_snd]

lemma processedKernel_reference {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] :
    processedKernel (α.fst ×ₖ α.snd) η = (processedKernel α η).fst ×ₖ (processedKernel α η).snd := by
  rw [processedKernel_fst]
  ext z : 1
  apply Measure.ext_prod
  intro s t hs ht
  rw [processedKernel_apply_prod _ _ _ hs ht,Kernel.prod_apply_prod,processedKernel_snd_apply _ _ _ ht,
    Kernel.prod_apply,←Measure.prod_restrict (s:=s) (t:=Set.univ),Measure.restrict_univ]
  rw [lintegral_prod _ (by exact ((η.measurable_coe ht).comp (measurable_const.prodMk measurable_snd)).aemeasurable)]
  simp only [lintegral_const,Measure.restrict_apply_univ]
  rw [mul_comm]

lemma compProd_processedKernel {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (μ : Measure Z) [IsFiniteMeasure μ]
    (α : Kernel Z (A×B)) [IsMarkovKernel α] (η : Kernel (Z×B) C) [IsMarkovKernel η] :
    μ ⊗ₘ processedKernel α η =
      ((μ ⊗ₘ α) ⊗ₘ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).map
        (fun z => (z.1.1,(z.1.2.1,z.2))) := by
  rw [processedKernel,Measure.compProd_map (measurable_fst.fst.prodMk measurable_snd),
    ←Measure.compProd_assoc,Measure.map_map
      (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd))
      MeasurableEquiv.prodAssoc.symm.measurable]
  rfl

lemma conditionalMutualInformation_processedKernel_le {Z A B C : Type*}
    [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [StandardBorelSpace A] [StandardBorelSpace B] [StandardBorelSpace C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (α : Kernel Z (A×B)) [IsMarkovKernel α] (η : Kernel (Z×B) C) [IsMarkovKernel η] :
    conditionalMutualInformation (μ ⊗ₘ processedKernel α η) ≤ conditionalMutualInformation (μ ⊗ₘ α) := by
  rw [conditionalMutualInformation_compProd,conditionalMutualInformation_compProd,
    ←processedKernel_reference,compProd_processedKernel,compProd_processedKernel]
  calc
    _ ≤ klDiv ((μ ⊗ₘ α) ⊗ₘ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd))
      ((μ ⊗ₘ (α.fst ×ₖ α.snd)) ⊗ₘ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)) :=
      klDiv_map_le _ _ (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd))
    _ = _ := klDiv_compProd_left _ _ _

lemma conditionalMutualInformation_processed_le {Z A B C : Type*}
    [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [StandardBorelSpace A] [StandardBorelSpace B] [StandardBorelSpace C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (P : Measure (Z×(A×B))) [IsProbabilityMeasure P] (η : Kernel (Z×B) C) [IsMarkovKernel η] :
    conditionalMutualInformation (processedLaw P η) ≤ conditionalMutualInformation P := by
  have h := conditionalMutualInformation_processedKernel_le P.fst P.condKernel η
  simpa only [compProd_processedKernel,P.disintegrate P.condKernel,processedLaw] using h



lemma compProd_map_base {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) [IsProbabilityMeasure μ]
    (κ : Kernel B C) [IsMarkovKernel κ] (f : A → B) (hf : Measurable f) :
    μ.map f ⊗ₘ κ = (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.compProd_apply_prod hs ht,Measure.map_apply (hf.prodMap measurable_id) (hs.prod ht)]
  change _ = (μ ⊗ₘ κ.comap f hf) ((f ⁻¹' s)×ˢt)
  rw [Measure.compProd_apply_prod (hs.preimage hf) ht,setLIntegral_map hs (κ.measurable_coe ht) hf]
  rfl

lemma compProd_independent_swap {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) [IsProbabilityMeasure μ]
    (κ : Kernel A B) [IsMarkovKernel κ] (γ : Measure C) [IsProbabilityMeasure γ] :
    ((μ ⊗ₘ κ).prod γ).map (fun z => ((z.1.1,z.2),z.1.2)) =
      (μ.prod γ) ⊗ₘ κ.comap Prod.fst measurable_fst := by
  apply Measure.ext_prod₃'
  intro s t u hs ht hu
  rw [Measure.map_apply ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd) ((hs.prod ht).prod hu)]
  have he : (fun z : (A×B)×C => ((z.1.1,z.2),z.1.2)) ⁻¹' ((s×ˢt)×ˢu) = (s×ˢu)×ˢt := by
    ext z; simp only [Set.mem_preimage,Set.mem_prod]; tauto
  rw [he,Measure.prod_prod,Measure.compProd_apply_prod hs hu,Measure.compProd_apply_prod (hs.prod ht) hu,
    ←Measure.prod_restrict,lintegral_prod _ (by exact ((κ.measurable_coe hu).comp measurable_fst).aemeasurable)]
  simp only [Kernel.comap_apply,lintegral_const,Measure.restrict_apply_univ]
  rw [lintegral_mul_const _ (κ.measurable_coe hu)]

lemma probability_prod_subsingleton {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Subsingleton B] (μ : Measure (A×B)) [IsProbabilityMeasure μ]
    (γ : Measure B) [IsProbabilityMeasure γ] : μ = μ.fst.prod γ := by
  apply Measure.ext_prod
  intro s t hs ht
  by_cases ht0 : t = ∅
  · simp [ht0]
  · have ht1 : t = Set.univ := (Set.nonempty_iff_ne_empty.mpr ht0).eq_univ
    rw [ht1,Measure.prod_prod,measure_univ,mul_one]
    rw [Measure.fst_apply hs]
    congr 1
    ext z; simp

lemma alignedExperiment_fresh {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] :
    alignedExperiment (r:=r) (P.prod (gaussianRows m d)) = P.prod (gaussianRows (m+r) d) := by
  change Measure.map ((Prod.map id (fun p : Rows m d×Rows r d => Fin.append p.1 p.2)) ∘
    MeasurableEquiv.prodAssoc) ((P.prod (gaussianRows m d)).prod (gaussianRows r d)) = _
  rw [←Measure.map_map (measurable_id.prodMap (measurable_append (E:=Vector d) m r))
    MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod,
    ←Measure.map_prod_map _ _ measurable_id (measurable_append (E:=Vector d) m r),Measure.map_id]
  rw [show ((gaussianRows m d).prod (gaussianRows r d)).map (fun p => Fin.append p.1 p.2) =
    gaussianRows (m+r) d from map_append_pi (stdGaussian (Vector d)) m r]

lemma exposedInformation_prefix_zero {d m k : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    exposedInformation (alignedExperiment (r:=k) (prefixLaw P 0 (Nat.zero_le m))) = freshInformation P.fst k := by
  have he := probability_prod_subsingleton (prefixLaw P 0 (Nat.zero_le m)) (gaussianRows 0 d)
  rw [prefixLaw_fst] at he
  simp only [he,alignedExperiment_fresh]
  change freshInformation P.fst (0+k) = freshInformation P.fst k
  rw [Nat.zero_add]




lemma endingRowLaw_fst {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d×U))
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) :
    (endingRowLaw P κ).fst = endingSignalLaw P κ := by
  rw [endingRowLaw,Measure.fst,Measure.map_map measurable_fst measurable_endingRowMap]
  rfl

lemma endingRowLaw_independence {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d×U)) [IsProbabilityMeasure P]
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) [IsMarkovKernel κ] :
    ((endingRowLaw P κ).map swapLast).fst = P.fst.prod (gaussianRows m d) := by
  rw [endingRowLaw,Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map (measurable_fst.comp swapLast.measurable) measurable_endingRowMap]
  change (blockLaw P κ).map ((Prod.map Prod.fst id) ∘ Prod.fst) = _
  rw [←Measure.map_map (measurable_fst.prodMap measurable_id) measurable_fst,←Measure.fst]
  change (((P.prod (gaussianRows m d)) ⊗ₘ κ.comap blockInput measurable_blockInput).fst).map _ = _
  rw [Measure.fst_compProd,←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
  rfl

lemma measurable_blockExposedBaseMap {d m r : ℕ} {U : Type*} [MeasurableSpace U] :
    Measurable (blockExposedBaseMap (d:=d) (m:=m) (r:=r) (U:=U)) :=
  measurable_exposedJointMap.comp measurable_alignedMap

lemma blockObservedInput_exposed {d m r : ℕ} {U : Type*}
    (z : ((Sphere d×U)×Rows m d)×Rows r d) :
    blockObservedInput ((blockExposedBaseMap z).1,(blockExposedBaseMap z).2.2) = blockInput z.1 := by
  unfold blockObservedInput blockExposedBaseMap exposedJointMap blockInput
  congr 2
  · funext j; simp
  · funext j; simp [label]

lemma block_exposed_processed {d m r : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d×U)) [IsProbabilityMeasure P]
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) [IsMarkovKernel κ] :
    processedLaw ((P.prod (gaussianRows (m+r) d)).map exposedJointMap)
      (κ.comap (blockObservedInput (r:=r)) measurable_blockObservedInput) =
      (alignedExperiment (r:=r) (endingRowLaw P κ)).map exposedJointMap := by
  let μ := P.prod (gaussianRows m d)
  let γ := gaussianRows r d
  let K := κ.comap blockInput measurable_blockInput
  let H := blockExposedBaseMap (d:=d) (m:=m) (r:=r) (U:=U)
  have hH : Measurable H := measurable_blockExposedBaseMap
  have hInput : (μ.prod γ).map H = (P.prod (gaussianRows (m+r) d)).map exposedJointMap := by
    rw [←alignedExperiment_fresh (r:=r) (m:=m) P,alignedExperiment,
      Measure.map_map measurable_exposedJointMap measurable_alignedMap]
    rfl
  have hK : ((κ.comap (blockObservedInput (r:=r)) measurable_blockObservedInput).comap
      (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).comap H hH =
      K.comap Prod.fst measurable_fst := by
    ext z t ht
    change κ (blockObservedInput ((H z).1,(H z).2.2)) t = κ (blockInput z.1) t
    rw [show blockObservedInput ((H z).1,(H z).2.2) = blockInput z.1 from blockObservedInput_exposed z]
  rw [processedLaw,←hInput,compProd_map_base _ _ H hH,hK,
    Measure.map_map (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd))
      (hH.prodMap measurable_id),←compProd_independent_swap μ K γ,
    Measure.map_map ((measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd)).comp
      (hH.prodMap measurable_id)) ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)]
  rw [alignedExperiment,Measure.map_map measurable_exposedJointMap measurable_alignedMap,actualExperiment,endingRowLaw]
  have he : ((blockLaw P κ).map (fun z => ((z.1.1.1,z.2),z.1.2))).prod (gaussianRows r d) =
      ((blockLaw P κ).prod (gaussianRows r d)).map (Prod.map (fun z => ((z.1.1.1,z.2),z.1.2)) id) := by
    rw [←Measure.map_prod_map _ _ measurable_endingRowMap measurable_id,Measure.map_id]
  rw [he,Measure.map_map (measurable_exposedJointMap.comp measurable_alignedMap)
    (measurable_endingRowMap.prodMap measurable_id)]
  rfl

lemma block_exposed_le_fresh {d m r : ℕ} {U V : Type*}
    [MeasurableSpace U] [MeasurableSpace V] [StandardBorelSpace U] [StandardBorelSpace V]
    [Nonempty U] [Nonempty V] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×U)) [IsProbabilityMeasure P]
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) [IsMarkovKernel κ] :
    exposedInformation (alignedExperiment (r:=r) (endingRowLaw P κ)) ≤ freshInformation P (m+r) := by
  let : IsProbabilityMeasure ((P.prod (gaussianRows (m+r) d)).map exposedJointMap) :=
    Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have h := conditionalMutualInformation_processed_le ((P.prod (gaussianRows (m+r) d)).map exposedJointMap)
    (κ.comap (blockObservedInput (r:=r)) measurable_blockObservedInput)
  simpa only [block_exposed_processed,exposedInformation,freshInformation] using h



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Hybrid
attribute [-instance] _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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


lemma shannonEntropy_finite {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (π : Measure W) [IsProbabilityMeasure π] :
    shannonEntropy π ≠ ∞ := by
  rw [shannonEntropy,lintegral_fintype]
  apply ENNReal.sum_ne_top.mpr
  intro w hw
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top π _)

lemma freshInformation_finite {d k : ℕ} {W : Type*}
    [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
    [Nonempty W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] : freshInformation P k ≠ ∞ := by
  apply exposedInformation_finite
  rw [Measure.fst_prod]
  exact shannonEntropy_finite P.snd

lemma hybrid_block_bound {d m : ℕ} (hd : 256 ≤ d) (hm : m ≤ d/8)
    {U V : Type*} [Fintype U] [Fintype V]
    [MeasurableSpace U] [MeasurableSpace V]
    [MeasurableSingletonClass U] [MeasurableSingletonClass V]
    (P : Measure (Sphere d×U)) [IsProbabilityMeasure P]
    (hS : P.fst = uniformSphere d)
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) [IsMarkovKernel κ]
    {B : ℝ} (hB : 0 ≤ B)
    (hH : shannonEntropy (endingSignalLaw P κ).snd ≤ ENNReal.ofReal B) :
    averagedFreshInformation (endingSignalLaw P κ)-averagedFreshInformation P ≤
      hybridRowConstant*m+(m:ℝ)/hybridCount d*(16*hybridBaselineConstant+B/(d/8:ℕ))+B/(d/32:ℕ) := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  let : Nonempty U := nonempty_of_isProbabilityMeasure P.snd
  let : Nonempty V := nonempty_of_isProbabilityMeasure (endingSignalLaw P κ).snd
  have hi : ((endingRowLaw P κ).map swapLast).fst = (uniformSphere d).prod (gaussianRows m d) := by
    rw [endingRowLaw_independence,hS]
  have hh : shannonEntropy (endingRowLaw P κ).fst.snd ≤ ENNReal.ofReal B := by
    rwa [endingRowLaw_fst]
  have h := hybrid_average_ending (endingRowLaw P κ) hd hm hi hB hh
  simp_rw [exposedInformation_prefix_zero,endingRowLaw_fst] at h
  have hle : (∑ k ∈ Finset.Icc (hybridFirst d) (hybridLast d),
      (exposedInformation (alignedExperiment (r:=k-m) (endingRowLaw P κ))).toReal) / hybridCount d ≤
      averagedFreshInformation P := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro k hk
    have hkm : m ≤ k := by
      obtain ⟨hk,_⟩ := Finset.mem_Icc.mp hk
      unfold hybridFirst at hk
      omega
    have hl := block_exposed_le_fresh (r:=k-m) P κ
    have hfresh : freshInformation P (m+(k-m)) = freshInformation P k :=
      congrArg (freshInformation P) (Nat.add_sub_of_le hkm)
    rw [hfresh] at hl
    exact ENNReal.toReal_mono (freshInformation_finite P) hl
  change averagedFreshInformation (endingSignalLaw P κ) - _ ≤ _ at h
  linarith

lemma hybrid_block_numeric {d m : ℕ} {B C : ℝ}
    (hd : 256 ≤ d) (hm : m ≤ d/8) (hB : 0 ≤ B) (hBd : B ≤ (d:ℝ)^2)
    (hC : 0 ≤ C) :
    C*m+(m:ℝ)/hybridCount d*(C+B/(d/8:ℕ))+B/(d/32:ℕ) ≤ (100*C+100)*d := by
  have hh0 : (0:ℝ)<(d/8:ℕ) := by exact_mod_cast (show 0<d/8 by omega)
  have hq0 : (0:ℝ)<(d/32:ℕ) := by exact_mod_cast (show 0<d/32 by omega)
  have hN0 : (0:ℝ)<hybridCount d := by unfold hybridCount; positivity
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hmd : (m:ℝ) ≤ d := by exact_mod_cast (show m≤d by omega)
  have hdh : (d:ℝ) ≤ 16*(d/8:ℕ) := by exact_mod_cast (show d≤16*(d/8) by omega)
  have hdq : (d:ℝ) ≤ 64*(d/32:ℕ) := by exact_mod_cast (show d≤64*(d/32) by omega)
  have hmN : (m:ℝ) ≤ hybridCount d := by
    exact_mod_cast (show m≤hybridCount d by unfold hybridCount hybridFirst hybridLast; omega)
  have hmN' : (m:ℝ)/hybridCount d ≤ 1 := (div_le_one hN0).mpr hmN
  have hBh : B/(d/8:ℕ) ≤ 16*d := by
    apply (div_le_iff₀ hh0).mpr
    nlinarith
  have hBq : B/(d/32:ℕ) ≤ 64*d := by
    apply (div_le_iff₀ hq0).mpr
    nlinarith
  have hmul : (m:ℝ)/hybridCount d*(C+B/(d/8:ℕ)) ≤ C+16*d := by
    calc
      _ ≤ 1*(C+B/(d/8:ℕ)) := mul_le_mul_of_nonneg_right hmN' (add_nonneg hC (div_nonneg hB hh0.le))
      _ ≤ C+16*d := by linarith
  have hCm := mul_le_mul_of_nonneg_left hmd hC
  have hd1 : (1:ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
  nlinarith

theorem hybridBlockMain_oai : HybridBlockMain := by
  let C := 1+|hybridRowConstant|+16*hybridBaselineConstant
  have hbase := hybridBaselineConstant_pos
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,100*C+100,256,hC,by positivity,?_⟩
  intro d hd m hm1 hm U V _ _ _ _ _ _ P _ hS κ _ B hB hH
  have h := hybrid_block_bound hd hm P hS κ hB hH
  have hrow : hybridRowConstant ≤ C := by
    have h := le_abs_self hybridRowConstant
    dsimp [C]
    linarith
  have hbaseline : 16*hybridBaselineConstant ≤ C := by
    dsimp [C]
    linarith [abs_nonneg hybridRowConstant]
  have hbound : averagedFreshInformation (endingSignalLaw P κ)-averagedFreshInformation P ≤
    C*m+(m:ℝ)/hybridCount d*(C+B/(d/8:ℕ))+B/(d/32:ℕ) := by
    apply h.trans
    apply add_le_add _ le_rfl
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hrow (Nat.cast_nonneg _)
    · exact mul_le_mul_of_nonneg_left (add_le_add hbaseline le_rfl) (by positivity)
  refine ⟨hbound,fun hBd => hbound.trans (hybrid_block_numeric hd hm hB hBd hC.le)⟩



end CurrentProjection

end

end OAI
end

theorem solution : type_of% @OAI.CurrentProjection.hybridBlockMain_oai := @OAI.CurrentProjection.hybridBlockMain_oai
