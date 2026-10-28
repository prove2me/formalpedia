-- Prove2me | solution 1 for OAI.CurrentProjection.actual_fresh_row_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T23:58:54.927987+00:00
-- url     : https://prove2.me/submissions/47b0e5df-357e-4448-bcf5-99fda5c06cfb

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
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
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


end MixedGeometry




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

end AppendPi



lemma tendsto_cube_scale : Tendsto (fun j : ℕ => 1/(j:ℝ)) atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with j hj
  simp only [Set.mem_Ioi]
  positivity




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

end SphereBounds



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



lemma klDiv_map_equiv {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P Q : Measure A) [IsFiniteMeasure P] [IsFiniteMeasure Q] (e : A ≃ᵐ B) :
    klDiv (P.map e) (Q.map e) = klDiv P Q := by
  apply le_antisymm (klDiv_map_le P Q e.measurable)
  have h := klDiv_map_le (P.map e) (Q.map e) e.symm.measurable
  simpa only [e.map_symm_map] using h


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



instance projectionJoint_probability {d k : ℕ} (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ]
    (μ : Measure (Rows k d)) [IsProbabilityMeasure μ] : IsProbabilityMeasure (projectionJoint ρ μ) := by
  unfold projectionJoint
  exact Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)



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


lemma klDiv_map_leftInverse {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P Q : Measure A) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (f : A → B) (g : B → A) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    klDiv (P.map f) (Q.map f) = klDiv P Q := by
  apply le_antisymm (klDiv_map_le P Q hf)
  have h := klDiv_map_le (P.map f) (Q.map f) hg
  have he : g ∘ f = id := funext hgf
  simpa only [Measure.map_map hg hf,he,Measure.map_id] using h

lemma measurable_observedMessageMap {d k : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (observedMessageMap (d:=d) (k:=k) (W:=W)) :=
  ((measurable_exposedJointMap (d:=d) (k:=k) (W:=W)).fst).prodMk measurable_fst.snd

instance observedMessage_probability {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (observedMessage P) := by
  unfold observedMessage
  exact Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.KernelGeometry
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



section KernelGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

omit measurableSpaceE borelSpaceE in
lemma rowProjectionL_eq {r : ℕ} (A : Fin r → E) :
    rowProjectionL A = (rowSpan A).starProjection := by
  ext v
  have hgs := gramSchmidt_eq_sub_starProjection (Fin.snoc A v) (Fin.last r)
  rw [image_Iio_last] at hgs
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at hgs
  have he := gramSchmidt_def ℝ (Fin.snoc A v) (Fin.last r)
  rw [Fin.Iio_last_eq_map, Finset.sum_map] at he
  simp only [Fin.castSuccEmb_apply, Fin.snoc_last, gramSchmidt_castSucc,
    Fin.snoc_castSucc, Submodule.starProjection_singleton] at he
  have hz : (rowSpan A).starProjection v =
      ∑ i, (⟪gramSchmidt ℝ A i, v⟫ / ‖gramSchmidt ℝ A i‖ ^ 2) • gramSchmidt ℝ A i := by
    dsimp only [rowSpan]
    have := hgs.symm.trans he
    exact (sub_right_inj).mp this
  rw [hz]
  simp only [rowProjectionL, sum_apply, smul_apply,
    InnerProductSpace.rankOne_apply, smul_smul, div_eq_mul_inv, mul_comm]

lemma measurable_rowProjectionL (r : ℕ) :
    Measurable (rowProjectionL (E:=E) (r:=r)) := by
  apply Finset.measurable_sum
  intro i _
  have hg := measurable_gramSchmidt (E:=E) i
  have hr : Measurable (fun A : Fin r → E =>
      InnerProductSpace.rankOne ℝ (gramSchmidt ℝ A i) (gramSchmidt ℝ A i)) := by
    exact (show Continuous (fun x : E => InnerProductSpace.rankOne ℝ x x) from
      (ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp₂ (innerSL ℝ).continuous continuous_id).measurable.comp hg
  exact (hg.norm.pow_const 2 |>.inv).smul hr

omit finiteDimensionalRealE measurableSpaceE borelSpaceE in
lemma rowSpan_isometry {r : ℕ} (A : Fin r → E) (f : E ≃ₗᵢ[ℝ] E) :
    rowSpan (fun i => f (A i)) = (rowSpan A).map f.toLinearEquiv.toLinearMap := by
  rw [rowSpan, rowSpan, Submodule.map_span, ← Set.range_comp]
  rfl

omit measurableSpaceE borelSpaceE in
lemma rowProjectionL_isometry {r : ℕ} (A : Fin r → E) (f : E ≃ₗᵢ[ℝ] E) (v : E) :
    rowProjectionL (fun i => f (A i)) (f v) = f (rowProjectionL A v) := by
  rw [rowProjectionL_eq, rowProjectionL_eq, rowSpan_isometry]
  exact (f.toLinearIsometry.map_starProjection' (rowSpan A) v).symm

omit measurableSpaceE borelSpaceE in
lemma rowProjectionL_contraction {r : ℕ} (A : Fin r → E) (v : E) :
    ‖rowProjectionL A v‖ ≤ ‖v‖ := by
  rw [rowProjectionL_eq]
  exact (rowSpan A).norm_starProjection_apply_le v

omit measurableSpaceE borelSpaceE in
lemma rowProjectionL_infDist {r : ℕ} (A : Fin r → E) (v : E) :
    ‖rowProjectionL A v‖ = Metric.infDist v ((rowSpan A)ᗮ : Set E) := by
  rw [rowProjectionL_eq]
  have he : v - (rowSpan A)ᗮ.starProjection v = (rowSpan A).starProjection v := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  rw [← he, Submodule.starProjection_minimal, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl

lemma gaussianRowIsometry_preserving (r : ℕ) (f : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (fun A : Fin r → E => fun i => f (A i))
      (Measure.pi fun _ => stdGaussian E) (Measure.pi fun _ => stdGaussian E) :=
  measurePreserving_pi _ _ (fun _ => ⟨f.continuous.measurable, stdGaussian_map f⟩)


lemma rowProjection_smallBall_eq {r : ℕ} (v w : E) (h : ‖v‖ = ‖w‖) (t : ℝ) :
    (Measure.pi fun _ : Fin r => stdGaussian E) {A | ‖rowProjectionL A v‖ ≤ t} =
    (Measure.pi fun _ : Fin r => stdGaussian E) {A | ‖rowProjectionL A w‖ ≤ t} := by
  let f := Submodule.reflection (ℝ ∙ (v-w))ᗮ
  have hf : f v = w := Submodule.reflection_sub h
  have hm : MeasurableSet {A : Fin r → E | ‖rowProjectionL A w‖ ≤ t} :=
    measurableSet_le ((measurable_rowProjectionL r).apply_continuousLinearMap w).norm measurable_const
  rw [← (gaussianRowIsometry_preserving r f).measure_preimage hm.nullMeasurableSet]
  congr 1
  ext A
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, ← hf, rowProjectionL_isometry, f.norm_map]

end KernelGeometry



section GaussianRank
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_submodule_null (V : Submodule ℝ E)
    (hV : Module.finrank ℝ V < Module.finrank ℝ E) : stdGaussian E (V:Set E) = 0 := by
  have hne : Vᗮ ≠ ⊥ := by
    intro h
    have hn := V.finrank_add_finrank_orthogonal
    rw [h, finrank_bot, add_zero] at hn
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let f : StrongDual ℝ E := innerSL ℝ w
  have hf : ‖f‖ ≠ 0 := by simpa [f] using norm_ne_zero_iff.mpr hw0
  have hp : (‖f‖^2).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_ne_zero hf))
  have hmap : (stdGaussian E).map f = gaussianReal 0 (‖f‖^2).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian]
  have hn : stdGaussian E {x | f x = 0} = 0 := by
    have hs : (gaussianReal 0 (‖f‖^2).toNNReal) {0} = 0 := by
      let := nullSingletonClass_gaussianReal (μ:=0) hp
      exact measure_singleton 0
    rw [← hmap, Measure.map_apply f.measurable (measurableSet_singleton 0)] at hs
    exact hs
  apply le_antisymm _ bot_le
  calc
    stdGaussian E (V:Set E) ≤ stdGaussian E {x | f x = 0} := by
      apply measure_mono
      intro x hx
      change ⟪w,x⟫ = 0
      simpa only [real_inner_comm] using hw x hx
    _ = 0 := hn

lemma gaussianRows_ae_gramSchmidt_ne_zero (k : ℕ) (hk : k ≤ Module.finrank ℝ E) :
    ∀ᵐ v : Fin k → E ∂Measure.pi (fun _ => stdGaussian E),
      ∀ i, gramSchmidt ℝ v i ≠ 0 := by
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ k ih =>
    have hm : MeasurableSet {v : Fin (k+1) → E | ∀ i, gramSchmidt ℝ v i ≠ 0} := by
      simpa only [Set.compl_ofPred, Set.iInter_ofPred] using (MeasurableSet.iInter fun i : Fin (k+1) =>
        (measurableSet_eq_fun (measurable_gramSchmidt (E:=E) i)
          (measurable_const (a:=(0:E)))).compl)
    rw [ae_pi_snoc (stdGaussian E) hm]
    filter_upwards [ih (by omega)] with v hv
    let V := rowSpan v
    have hd : Module.finrank ℝ V ≤ k := by
      change Module.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ k
      exact (finrank_range_le_card (R:=ℝ) v).trans_eq (Fintype.card_fin k)
    have hn : stdGaussian E (V:Set E) = 0 := stdGaussian_submodule_null V (by omega)
    have ha : ∀ᵐ x ∂stdGaussian E, x ∉ V := by
      rw [ae_iff]
      simp only [not_not]
      change stdGaussian E (V:Set E) = 0
      exact hn
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

lemma gaussianRows_ae_rowSpan_finrank (k : ℕ) (hk : k ≤ Module.finrank ℝ E) :
    ∀ᵐ A : Fin k → E ∂Measure.pi (fun _ => stdGaussian E),
      Module.finrank ℝ (rowSpan A) = k := by
  filter_upwards [gaussianRows_ae_gramSchmidt_ne_zero k hk] with A hA
  have hi : LinearIndependent ℝ A := by
    apply Matrix.linearIndependent_of_det_gram_ne_zero
    rw [det_gram_eq_prod_gramSchmidt]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hA i))
  change Module.finrank ℝ (Submodule.span ℝ (Set.range A)) = k
  exact (finrank_span_eq_card hi).trans (Fintype.card_fin k)

end GaussianRank



section SphereTubes
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma sphereLaw_submodule_tube (V : Submodule ℝ E) (k : ℕ)
    (hk : Module.finrank ℝ V + k ≤ Module.finrank ℝ E)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    sphereLaw {v : Metric.sphere (0:E) 1 | Metric.infDist (v:E) (V:Set E) ≤ t} ≤
      ENNReal.ofReal ((12:ℝ)^Module.finrank ℝ E * t^k) := by
  let L := V.toAffineSubspace
  let : Nonempty L := ⟨⟨0,V.zero_mem⟩⟩
  have hd : (Module.finrank ℝ L.direction : ℝ) + k ≤ Module.finrank ℝ E := by
    dsimp only [L]
    rw [Submodule.toAffineSubspace_direction]
    exact_mod_cast hk
  have hsub : Set.Ioo (0:ℝ) 1 • (Subtype.val ''
      {v : Metric.sphere (0:E) 1 | Metric.infDist (v:E) (V:Set E) ≤ t}) ⊆
      {v:E | Metric.infDist v L ≤ t} := by
    rintro _ ⟨c,hc,_,⟨v,hv,rfl⟩,rfl⟩
    change Metric.infDist (c • (v:E)) (V:Set E) ≤ t
    rw [infDist_submodule_smul, abs_of_pos hc.1]
    exact (mul_le_mul_of_nonneg_left hv hc.1.le).trans
      (mul_le_of_le_one_left ht.le hc.2.le)
  rw [sphereLaw_apply (measurableSet_le (by fun_prop) measurable_const)]
  apply (measure_mono hsub).trans
  apply (unitBallLaw_local.affine_tube_pow unitBallLaw_support L k hd ht ht1).trans
  simp only [Real.rpow_natCast]
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht.le _)
  calc
    (3:ℝ)^Module.finrank ℝ L.direction * 4^Module.finrank ℝ E ≤
        3^Module.finrank ℝ E * 4^Module.finrank ℝ E := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by exact_mod_cast (show (Module.finrank ℝ L.direction:ℝ) ≤ Module.finrank ℝ E by linarith))) (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num

lemma sphereLaw_rowProjection {r : ℕ} (A : Fin r → E)
    (hr : Module.finrank ℝ (rowSpan A) = r)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    sphereLaw {v : Metric.sphere (0:E) 1 | ‖rowProjectionL A (v:E)‖ ≤ t} ≤
      ENNReal.ofReal ((12:ℝ)^Module.finrank ℝ E * t^r) := by
  simp only [rowProjectionL_infDist]
  apply sphereLaw_submodule_tube (rowSpan A)ᗮ r _ ht ht1
  have h := (rowSpan A).finrank_add_finrank_orthogonal
  omega

end SphereTubes



section KernelSmallBall
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [nontrivialE : Nontrivial E]

omit nontrivialE in
lemma measurable_rowProjection_pair (r : ℕ) :
    Measurable (fun z : (Fin r → E) × E => rowProjectionL z.1 z.2) := by
  have he : Continuous (fun z : (E →L[ℝ] E) × E => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  exact he.measurable.comp ((measurable_rowProjectionL r).comp measurable_fst |>.prodMk measurable_snd)


lemma gaussian_rowProjection_smallBall {r : ℕ} (hr : r ≤ Module.finrank ℝ E)
    (v : E) (hv : ‖v‖ = 1) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (Measure.pi fun _ : Fin r => stdGaussian E) {A | ‖rowProjectionL A v‖ ≤ t} ≤
      ENNReal.ofReal ((12:ℝ)^Module.finrank ℝ E * t^r) := by
  let G : Measure (Fin r → E) := Measure.pi fun _ => stdGaussian E
  let T : Set ((Fin r → E) × Metric.sphere (0:E) 1) :=
    {z | ‖rowProjectionL z.1 (z.2:E)‖ ≤ t}
  have hT : MeasurableSet T := measurableSet_le
    ((measurable_rowProjection_pair r).comp (measurable_fst.prodMk
      (measurable_subtype_coe.comp measurable_snd))).norm measurable_const
  have hconst : ∀ w : Metric.sphere (0:E) 1,
      G ((fun A => (A,w)) ⁻¹' T) = G {A | ‖rowProjectionL A v‖ ≤ t} := by
    intro w
    exact rowProjection_smallBall_eq (w:E) v ((mem_sphere_zero_iff_norm.mp w.property).trans hv.symm) t
  have heq : G.prod sphereLaw T = G {A | ‖rowProjectionL A v‖ ≤ t} := by
    rw [Measure.prod_apply_symm hT]
    simp only [hconst, lintegral_const, measure_univ, mul_one]
  rw [← heq, Measure.prod_apply hT]
  calc
    _ ≤ ∫⁻ _ : Fin r → E, ENNReal.ofReal ((12:ℝ)^Module.finrank ℝ E * t^r) ∂G := by
      apply lintegral_mono_ae
      filter_upwards [gaussianRows_ae_rowSpan_finrank r hr] with A hA
      exact sphereLaw_rowProjection A hA ht ht1
    _ = _ := by simp

end KernelSmallBall



section ProjectionWitness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma exists_unit_sphere_net {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ s : Finset E, (∀ v ∈ s, ‖v‖ = 1) ∧
      (s.card:ℝ) ≤ (3/t)^Module.finrank ℝ E ∧
      ∀ v:E, ‖v‖=1 → ∃ w ∈ s, dist v w ≤ t := by
  classical
  have hbound : ∀ s : Finset E, (∀ v ∈ s, ‖v‖ = 1) →
      (∀ v ∈ s, ∀ w ∈ s, v ≠ w → t < dist v w) →
      (s.card:ℝ) ≤ (3/t)^Module.finrank ℝ E := by
    intro s hs hsep
    refine (card_le_volume_ratio s ht zero_le_one (fun v hv => (hs v hv).le)
      (fun v hv w hw hne => (hsep v hv w hw hne).le)).trans ?_
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_div_iff₀ (by positivity : 0 < t/2) ht).mpr
    nlinarith
  obtain ⟨s,hs,hsep,hnet⟩ := exists_net_of_finite_packing_bound
    {v:E | ‖v‖=1} ht.le ⌈(3/t)^Module.finrank ℝ E⌉₊ (by
      intro s hs hsep
      exact_mod_cast (hbound s hs hsep).trans (Nat.le_ceil _))
  exact ⟨s,hs,hbound s hs hsep,hnet⟩


omit [MeasurableSpace E] [BorelSpace E] in
lemma exists_unit_projection_le_distance (P R : Submodule ℝ E) (hP : P ≠ ⊥)
    (u:E) (hu : ‖u‖=1) (huR : u ∈ Rᗮ) :
    ∃ v : P, ‖v‖=1 ∧ ‖R.starProjection (v:E)‖ ≤ Metric.infDist u (P:Set E) := by
  by_cases hp : P.starProjection u = 0
  · obtain ⟨w,hw,hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    let v : P := ⟨‖w‖⁻¹ • w,P.smul_mem _ hw⟩
    have hv : ‖v‖=1 := by
      change ‖‖w‖⁻¹ • w‖=1
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
    refine ⟨v,hv,?_⟩
    rw [infDist_eq_norm_sub_projection, hp, sub_zero, hu]
    exact (R.norm_starProjection_apply_le (v:E)).trans_eq hv
  · let p := P.starProjection u
    let v : P := ⟨‖p‖⁻¹ • p,P.smul_mem _ (P.starProjection_apply_mem u)⟩
    have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
    have hv : ‖v‖=1 := by
      change ‖‖p‖⁻¹ • p‖=1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp0), inv_mul_cancel₀ hp0.ne']
    have hip : ⟪u,p⟫ = ‖p‖^2 := by
      rw [← real_inner_self_eq_norm_sq]
      exact (P.inner_starProjection_left_eq_right u p).trans (by
        rw [P.starProjection_eq_self_iff.mpr (P.starProjection_apply_mem u)]) |>.symm
    have hiv : ⟪u,(v:E)⟫ = ‖p‖ := by
      change ⟪u, ‖p‖⁻¹ • p⟫ = ‖p‖
      rw [real_inner_smul_right, hip]
      field_simp
    have hic : ⟪u,Rᗮ.starProjection (v:E)⟫ = ‖p‖ := by
      rw [← Rᗮ.inner_starProjection_left_eq_right, (Rᗮ.starProjection_eq_self_iff.mpr huR)]
      exact hiv
    have hcs : ‖p‖ ≤ ‖Rᗮ.starProjection (v:E)‖ := by
      have h := real_inner_le_norm u (Rᗮ.starProjection (v:E))
      rwa [hic,hu,one_mul] at h
    have ht := Submodule.norm_sq_eq_add_norm_sq_starProjection (v:E) R
    have hpyt := Submodule.norm_sq_eq_add_norm_sq_starProjection u P
    have hdist : Metric.infDist u (P:Set E) = ‖Pᗮ.starProjection u‖ := by
      rw [infDist_eq_norm_sub_projection, Submodule.starProjection_orthogonal_val]
    refine ⟨v,hv,?_⟩
    rw [hdist]
    change ‖(v:E)‖=1 at hv
    rw [hv] at ht
    rw [hu] at hpyt
    have hs := sq_le_sq₀ (norm_nonneg p) (norm_nonneg (Rᗮ.starProjection (v:E))) |>.mpr hcs
    dsimp only [p] at hs
    nlinarith [norm_nonneg (Pᗮ.starProjection u), norm_nonneg (R.starProjection (v:E))]

end ProjectionWitness



section KernelSelectedSmallBall
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma kernel_selected_smallBall_raw {r : ℕ} (hr : r ≤ Module.finrank ℝ E)
    (P : Submodule ℝ E) (hP : P ≠ ⊥)
    (Q : Measure ((Fin r → E) × E))
    (hQ : Q.fst = Measure.pi (fun _ => stdGaussian E))
    (hsupport : ∀ᵐ z ∂Q, ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1/2) :
    Q {z | Metric.infDist z.2 (P:Set E) ≤ t} ≤
      ENNReal.ofReal ((3/t)^Module.finrank ℝ P *
        ((12:ℝ)^Module.finrank ℝ E * (2*t)^r)) := by
  classical
  obtain ⟨s,hs,hcard,hnet⟩ := exists_unit_sphere_net (E:=P) ht (by linarith)
  let T : P → Set (Fin r → E) := fun w => {A | ‖rowProjectionL A (w:E)‖ ≤ 2*t}
  have hTm : ∀ w, MeasurableSet (T w) := fun w =>
    measurableSet_le ((measurable_rowProjectionL r).apply_continuousLinearMap (w:E)).norm measurable_const
  have hUnion : MeasurableSet (⋃ w ∈ s, T w) :=
    s.finite_toSet.measurableSet_biUnion (fun w _ => hTm w)
  have hsub : {z | Metric.infDist z.2 (P:Set E) ≤ t} ≤ᵐ[Q]
      Prod.fst ⁻¹' (⋃ w ∈ s, T w) := by
    filter_upwards [hsupport] with z hz
    intro hzt
    obtain ⟨v,hv,hvp⟩ := exists_unit_projection_le_distance P (rowSpan z.1) hP z.2 hz.1 hz.2
    obtain ⟨w,hw,hvw⟩ := hnet v hv
    refine Set.mem_preimage.mpr (Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨hw,?_⟩⟩)
    change ‖rowProjectionL z.1 (w:E)‖ ≤ 2*t
    have hdist : ‖(w:E)-(v:E)‖ ≤ t := by
      rw [dist_eq_norm] at hvw
      change ‖(w-v:P)‖ ≤ t
      simpa only [norm_sub_rev] using hvw
    have hproj : ‖rowProjectionL z.1 (v:E)‖ ≤ t := by
      rw [rowProjectionL_eq]
      exact hvp.trans hzt
    calc
      ‖rowProjectionL z.1 (w:E)‖ ≤ ‖rowProjectionL z.1 (v:E)‖ +
          ‖rowProjectionL z.1 ((w:E)-(v:E))‖ := by
        rw [map_sub]
        exact norm_le_insert' _ _
      _ ≤ t+t := add_le_add hproj ((rowProjectionL_contraction z.1 _).trans hdist)
      _ = 2*t := by ring
  calc
    Q {z | Metric.infDist z.2 (P:Set E) ≤ t} ≤ Q (Prod.fst ⁻¹' (⋃ w ∈ s, T w)) :=
      measure_mono_ae hsub
    _ = (Measure.pi fun _:Fin r => stdGaussian E) (⋃ w ∈ s, T w) := by
      rw [←Measure.fst_apply hUnion,hQ]
    _ ≤ ∑ w ∈ s, (Measure.pi fun _:Fin r => stdGaussian E) (T w) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ s, ENNReal.ofReal ((12:ℝ)^Module.finrank ℝ E * (2*t)^r) := by
      exact Finset.sum_le_sum fun w hw => gaussian_rowProjection_smallBall hr (w:E)
        (hs w hw) (by positivity) (by linarith)
    _ = ENNReal.ofReal ((s.card:ℝ)*((12:ℝ)^Module.finrank ℝ E*(2*t)^r)) := by
      simp [ENNReal.ofReal_mul, nsmul_eq_mul]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (by positivity))

end KernelSelectedSmallBall



lemma kernelSmallBallConstant_ge_two : 2 ≤ kernelSmallBallConstant := by
  norm_num [kernelSmallBallConstant]

lemma kernelSmallBall_coefficient {d r p : ℕ} (hd : d ≤ 8*r) (hp : 2*p ≤ r)
    {t : ℝ} (ht : 0 < t) :
    (3/t)^p * ((12:ℝ)^d * (2*t)^r) ≤
      (kernelSmallBallConstant*t)^(r-p) := by
  have hpr : p ≤ r := by omega
  have hr : r ≤ 2*(r-p) := by omega
  have hpp : p ≤ r-p := by omega
  have hdd : d ≤ 16*(r-p) := by omega
  have hcoef : (3:ℝ)^p * 12^d * 2^r ≤ kernelSmallBallConstant^(r-p) := by
    calc
      (3:ℝ)^p*12^d*2^r ≤ 3^(r-p)*12^(16*(r-p))*2^(2*(r-p)) := by
        apply mul_le_mul (mul_le_mul (pow_le_pow_right₀ (by norm_num) hpp)
          (pow_le_pow_right₀ (by norm_num) hdd) (by positivity) (by positivity))
          (pow_le_pow_right₀ (by norm_num) hr) (by positivity) (by positivity)
      _ = _ := by
        rw [pow_mul, pow_mul, ←mul_pow, ←mul_pow]
        congr 1
        norm_num [kernelSmallBallConstant]
  have htPow : t^r = t^(r-p)*t^p := by
    rw [←pow_add, Nat.sub_add_cancel hpr]
  calc
    (3/t)^p * ((12:ℝ)^d*(2*t)^r) = (3^p*12^d*2^r)*t^(r-p) := by
      rw [div_pow, mul_pow, htPow]
      field_simp
    _ ≤ kernelSmallBallConstant^(r-p)*t^(r-p) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := (mul_pow _ _ _).symm



section KernelInverseOneStep
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma kernel_selected_scaled_smallBall {r : ℕ} (hr : r ≤ Module.finrank ℝ E)
    (hd : Module.finrank ℝ E ≤ 8*r) (P : Submodule ℝ E)
    (hp : 2*Module.finrank ℝ P ≤ r) (hmargin : 2 ≤ r-Module.finrank ℝ P)
    (Q : Measure ((Fin r → E) × E))
    (hQ : Q.fst = Measure.pi (fun _ => stdGaussian E))
    (hsupport : ∀ᵐ z ∂Q, ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ)
    {s:ℝ} (hs : 0<s) (hs1 : s≤1) :
    Q {z | kernelSmallBallConstant * Metric.infDist z.2 (P:Set E) ≤ s} ≤
      ENNReal.ofReal (s^2) := by
  have hC := kernelSmallBallConstant_ge_two
  have hC0 : 0 < kernelSmallBallConstant := by linarith
  by_cases hP : P=⊥
  · have hz : Q {z | kernelSmallBallConstant * Metric.infDist z.2 (P:Set E) ≤ s} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hsupport] with z hz
      rw [hP, infDist_eq_norm_sub_projection]
      simpa only [Submodule.starProjection_bot, zero_apply, sub_zero, hz.1,
        mul_one] using (show ¬kernelSmallBallConstant ≤ s by linarith)
    rw [hz]
    exact bot_le
  · have ht0 : 0 < s/kernelSmallBallConstant := div_pos hs hC0
    have ht1 : s/kernelSmallBallConstant ≤ 1/2 := by
      apply (div_le_iff₀ hC0).mpr
      linarith
    have heq : {z : (Fin r → E) × E |
        kernelSmallBallConstant * Metric.infDist z.2 (P:Set E) ≤ s} =
        {z | Metric.infDist z.2 (P:Set E) ≤ s/kernelSmallBallConstant} := by
      ext z
      change kernelSmallBallConstant * Metric.infDist z.2 (P:Set E) ≤ s ↔
        Metric.infDist z.2 (P:Set E) ≤ s/kernelSmallBallConstant
      rw [le_div_iff₀ hC0, mul_comm]
    rw [heq]
    apply (kernel_selected_smallBall_raw hr P hP Q hQ hsupport ht0 ht1).trans
    apply (ENNReal.ofReal_le_ofReal (kernelSmallBall_coefficient hd hp ht0)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [mul_div_cancel₀ _ hC0.ne']
    exact pow_le_pow_of_le_one hs.le hs1 hmargin

end KernelInverseOneStep

section GenericInverseStep
variable {X : Type*} [MeasurableSpace X]

lemma inverse_moment_of_scaled_smallBall (Q : Measure X) [IsProbabilityMeasure Q]
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {C : ℝ} (hC : 0<C)
    (htube : ∀ s:ℝ, 0<s → s≤1 → Q {x | C*f x ≤ s} ≤ ENNReal.ofReal (s^2)) :
    (∫⁻ x, ENNReal.ofReal ((f x)⁻¹) ∂Q) ≤ ENNReal.ofReal (5*C) ∧
      ∀ᵐ x ∂Q, 0 < f x := by
  have hm : (∫⁻ x, ENNReal.ofReal ((C*f x)⁻¹) ∂Q) ≤ 5 := by
    have h := inverse_moment_of_tube_bound Q (fun x => C*f x) 1
      (measurable_const.mul hf) (fun x => mul_nonneg hC.le (hf0 x)) 1 (by
        intro s hs hs1
        simpa only [one_mul] using htube s hs hs1)
    norm_num at h ⊢
    exact h
  have heq (x:X) : (f x)⁻¹ = C*(C*f x)⁻¹ := by
    rw [mul_inv, ←mul_assoc, mul_inv_cancel₀ hC.ne',one_mul]
  constructor
  · calc
      (∫⁻ x, ENNReal.ofReal ((f x)⁻¹) ∂Q) =
          ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal ((C*f x)⁻¹) ∂Q := by
        simp_rw [heq, ENNReal.ofReal_mul hC.le]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * 5 := mul_le_mul' le_rfl hm
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5)]; norm_num; ring
  · have hn : Q {x | f x = 0} = 0 := by
      have hb (n:ℕ) : Q {x | f x=0} ≤ ENNReal.ofReal (((1/2:ℝ)^n)^2) := by
        calc
          Q {x | f x=0} ≤ Q {x | C*f x ≤ (1/2:ℝ)^n} := by
            apply measure_mono
            intro x hx
            simp only [Set.mem_ofPred_eq] at hx ⊢
            rw [hx,mul_zero]
            positivity
          _ ≤ _ := htube _ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
      have hl : Tendsto (fun n:ℕ => ENNReal.ofReal (((1/2:ℝ)^n)^2)) atTop (𝓝 0) := by
        convert ENNReal.tendsto_ofReal ((tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).pow 2) using 1
        simp
      exact le_antisymm (ge_of_tendsto' hl hb) bot_le
    have ha : ∀ᵐ x ∂Q, f x ≠ 0 := by
      rw [ae_iff]
      simpa only [not_not] using hn
    filter_upwards [ha] with x hx
    exact lt_of_le_of_ne (hf0 x) hx.symm

end GenericInverseStep

section KernelInverseStepFinal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]


lemma kernel_selected_inverse_step {r : ℕ} (hr : r ≤ Module.finrank ℝ E)
    (hd : Module.finrank ℝ E ≤ 8*r) (P : Submodule ℝ E)
    (hp : 2*Module.finrank ℝ P ≤ r) (hmargin : 2 ≤ r-Module.finrank ℝ P)
    (Q : Measure ((Fin r → E) × E)) [IsProbabilityMeasure Q]
    (hQ : Q.fst = Measure.pi (fun _ => stdGaussian E))
    (hsupport : ∀ᵐ z ∂Q, ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ) :
    (∫⁻ z, ENNReal.ofReal ((Metric.infDist z.2 (P:Set E))⁻¹) ∂Q) ≤
        ENNReal.ofReal (5*kernelSmallBallConstant) ∧
      ∀ᵐ z ∂Q, 0 < Metric.infDist z.2 (P:Set E) := by
  apply inverse_moment_of_scaled_smallBall Q (fun z => Metric.infDist z.2 (P:Set E))
    ((Metric.continuous_infDist_pt _).measurable.comp measurable_snd)
    (fun _ => Metric.infDist_nonneg) (by have := kernelSmallBallConstant_ge_two; linarith)
  exact fun s hs hs1 => kernel_selected_scaled_smallBall hr hd P hp hmargin Q hQ hsupport hs hs1

end KernelInverseStepFinal




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.KernelVolume
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

section KernelVolume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E] [nontrivialE : Nontrivial E]

omit nontrivialE in
lemma measurable_kernelInverseVolume (r n : ℕ) :
    Measurable (kernelInverseVolume (E:=E) (r:=r) (n:=n)) := by
  apply Finset.measurable_prod
  intro i _
  exact (((measurable_gramSchmidt (E:=E) i).comp
    (Measurable.of_eval fun j => (measurable_pi_apply j).snd)).norm.inv).ennreal_ofReal

omit measurableSpaceE borelSpaceE nontrivialE in
lemma kernelInverseVolume_snoc {r n : ℕ} (h : KernelHistory r n E)
    (z : (Fin r → E) × E) :
    kernelInverseVolume (Fin.snoc h z) = kernelInverseVolume h *
      ENNReal.ofReal ((Metric.infDist z.2 (rowSpan (fun j => (h j).2) : Set E))⁻¹) := by
  unfold kernelInverseVolume
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    congr 3
    rw [gramSchmidt_castSucc]
    simp only [Fin.snoc_castSucc]
  · congr 2
    rw [norm_gramSchmidt_eq_infDist, image_Iio_last]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, rowSpan]

omit nontrivialE in
lemma measurableSet_kernel_nondegenerate (r n : ℕ) :
    MeasurableSet {h : KernelHistory r n E |
      ∀ i, gramSchmidt ℝ (fun j => (h j).2) i ≠ 0} := by
  simp_rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_eq_fun ((measurable_gramSchmidt (E:=E) i).comp
    (Measurable.of_eval fun j => (measurable_pi_apply j).snd)) measurable_const).compl

omit measurableSpaceE borelSpaceE nontrivialE in
lemma kernel_nondegenerate_snoc {r n : ℕ} (h : KernelHistory r n E)
    (z : (Fin r → E) × E)
    (hh : ∀ i, gramSchmidt ℝ (fun j => (h j).2) i ≠ 0)
    (hz : 0 < Metric.infDist z.2 (rowSpan (fun j => (h j).2) : Set E)) :
    ∀ i, gramSchmidt ℝ (fun j => (Fin.snoc (α:=fun _ => (Fin r → E) × E) h z j).2) i ≠ 0 := by
  intro i
  induction i using Fin.lastCases with
  | last =>
    apply norm_ne_zero_iff.mp
    rw [norm_gramSchmidt_eq_infDist, image_Iio_last]
    simpa only [Fin.snoc_castSucc, Fin.snoc_last, rowSpan] using hz.ne'
  | cast j =>
    simpa only [gramSchmidt_castSucc, Fin.snoc_castSucc] using hh j




end KernelVolume



section KernelPiVolume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E] [nontrivialE : Nontrivial E]

lemma independent_kernel_inverse_volume_pi {r q : ℕ}
    (hr : r ≤ Module.finrank ℝ E) (hd : Module.finrank ℝ E ≤ 8*r)
    (hq : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (Q : Measure ((Fin r → E) × E)) [IsProbabilityMeasure Q]
    (hrows : Q.fst = Measure.pi (fun _ => stdGaussian E))
    (hsupport : ∀ᵐ z ∂Q, ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ) :
    (∫⁻ h : KernelHistory r q E, kernelInverseVolume h ∂Measure.pi (fun _ => Q)) ≤
      ENNReal.ofReal (5*kernelSmallBallConstant)^q ∧
    ∀ᵐ h : KernelHistory r q E ∂Measure.pi (fun _ => Q),
      ∀ i, gramSchmidt ℝ (fun j => (h j).2) i ≠ 0 := by
  induction q with
  | zero =>
    constructor
    · simp [kernelInverseVolume]
    · exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ q ih =>
    have hi := ih (by omega) (by omega)
    have hp (h : KernelHistory r q E) : Module.finrank ℝ (rowSpan (fun j => (h j).2)) ≤ q :=
      (finrank_range_le_card (R:=ℝ) (fun j => (h j).2)).trans_eq (Fintype.card_fin q)
    have hstep (h : KernelHistory r q E) :=
      kernel_selected_inverse_step hr hd (rowSpan (fun j => (h j).2))
        (by have := hp h; omega) (by have := hp h; omega) Q hrows hsupport
    constructor
    · rw [lintegral_pi_snoc Q _ (measurable_kernelInverseVolume r (q+1))]
      calc
        _ ≤ ∫⁻ h : KernelHistory r q E, kernelInverseVolume h *
            ENNReal.ofReal (5*kernelSmallBallConstant) ∂Measure.pi (fun _ => Q) := by
          apply lintegral_mono
          intro h
          simp_rw [kernelInverseVolume_snoc]
          rw [lintegral_const_mul' _ _ (by
            apply ENNReal.prod_ne_top
            intro i _
            exact ENNReal.ofReal_ne_top)]
          exact mul_le_mul' le_rfl (hstep h).1
        _ = (∫⁻ h : KernelHistory r q E, kernelInverseVolume h ∂Measure.pi (fun _ => Q)) *
            ENNReal.ofReal (5*kernelSmallBallConstant) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (5*kernelSmallBallConstant)^q *
            ENNReal.ofReal (5*kernelSmallBallConstant) := mul_le_mul' hi.1 le_rfl
        _ = _ := (pow_succ _ _).symm
    · rw [ae_pi_snoc Q (measurableSet_kernel_nondegenerate r (q+1))]
      filter_upwards [hi.2] with h hh
      filter_upwards [(hstep h).2] with z hz
      exact kernel_nondegenerate_snoc h z hh hz

omit finiteDimensionalRealE measurableSpaceE borelSpaceE nontrivialE in
lemma span_image_diagonal_smul {ι : Type*} (v : ι → E) (c : ι → ℝ)
    (hc : ∀ i, c i ≠ 0) (I : Set ι) :
    Submodule.span ℝ ((fun i => c i • v i) '' I) = Submodule.span ℝ (v '' I) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have h := Submodule.smul_mem (Submodule.span ℝ ((fun i => c i • v i) '' I))
      (c i)⁻¹ (Submodule.subset_span ⟨i, hi, rfl⟩)
    rw [inv_smul_smul₀ (hc i)] at h
    exact h

omit measurableSpaceE borelSpaceE nontrivialE in
lemma gramSchmidt_diagonal_smul {n : ℕ} (v : Fin n → E) (c : Fin n → ℝ)
    (hc : ∀ i, c i ≠ 0) (j : Fin n) :
    gramSchmidt ℝ (fun i => c i • v i) j = c j • gramSchmidt ℝ v j := by
  rw [gramSchmidt_eq_sub_starProjection, gramSchmidt_eq_sub_starProjection,
    span_image_diagonal_smul v c hc, map_smul, smul_sub]

omit measurableSpaceE borelSpaceE nontrivialE in
lemma kernelInverseVolume_normalization {r n : ℕ}
    (h : KernelHistory r n E) (hn : ∀ i, (h i).2 ≠ 0) :
    kernelInverseVolume h =
      (∏ i, ENNReal.ofReal (‖(h i).2‖⁻¹)) *
        kernelInverseVolume (fun i => ((h i).1, ‖(h i).2‖⁻¹ • (h i).2)) := by
  unfold kernelInverseVolume
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [gramSchmidt_diagonal_smul _ _ (fun j => inv_ne_zero (norm_ne_zero_iff.mpr (hn j))),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_inv,
    inv_inv, ←mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hn i)), one_mul]

end KernelPiVolume



section KernelNormalizedMoment
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E] [nontrivialE : Nontrivial E]

omit nontrivialE in
lemma measurable_normalizeKernelVector (r : ℕ) :
    Measurable (normalizeKernelVector (E:=E) (r:=r)) := by
  unfold normalizeKernelVector
  fun_prop

omit finiteDimensionalRealE measurableSpaceE borelSpaceE nontrivialE in
lemma normalizeKernelVector_support {r : ℕ} (z : (Fin r → E) × E)
    (hz : z.2 ≠ 0 ∧ z.2 ∈ (rowSpan z.1)ᗮ) :
    ‖(normalizeKernelVector z).2‖ = 1 ∧
      (normalizeKernelVector z).2 ∈ (rowSpan (normalizeKernelVector z).1)ᗮ := by
  constructor
  · simp [normalizeKernelVector, norm_smul,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz.1)]
  · exact Submodule.smul_mem _ _ hz.2

omit nontrivialE in
lemma gaussian_single_kernel_bound {q : ℕ} (v : Fin q → E)
    (hv : LinearIndependent ℝ v) (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ t, φ t = 1) :
    ∫⁻ x, ∏ i, φ ⟪v i,x⟫ ∂stdGaussian E ≤
      ∏ i, ENNReal.ofReal (‖gramSchmidt ℝ v i‖⁻¹) := by
  rw [← lintegral_map (show Measurable (fun z : Fin q → ℝ => ∏ i, φ (z i)) by fun_prop)
    (show Measurable (fun x : E => fun i => ⟪v i,x⟫) by fun_prop)]
  calc
    _ ≤ ∫⁻ z : Fin q → ℝ, ∏ i, φ (z i)
        ∂(ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹) • volume) :=
      lintegral_mono' (gaussian_pairings_le v hv) (fun _ => le_rfl)
    _ = _ := by
      rw [lintegral_smul_measure, volume_pi, lintegral_fin_prod volume q
        (fun _ => φ) (fun _ => hφ)]
      simp only [hφ1, Finset.prod_const_one, smul_eq_mul, mul_one]
      rw [←Finset.prod_inv_distrib]
      exact ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)




lemma kernel_normalized_projection_moment {r q : ℕ}
    (hr : r ≤ Module.finrank ℝ E) (hd : Module.finrank ℝ E ≤ 8*r)
    (hq : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (Q : Measure ((Fin r → E) × E)) [IsProbabilityMeasure Q]
    (hrows : Q.fst = Measure.pi (fun _ => stdGaussian E))
    (hsupport : ∀ᵐ z ∂Q, z.2 ≠ 0 ∧ z.2 ∈ (rowSpan z.1)ᗮ)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ t, φ t = 1) :
    ∫⁻ x, (∫⁻ z, ENNReal.ofReal ‖z.2‖ * φ ⟪z.2,x⟫ ∂Q)^q
      ∂stdGaussian E ≤ ENNReal.ofReal (5*kernelSmallBallConstant)^q := by
  let T := normalizeKernelVector (E:=E) (r:=r)
  have hT : Measurable T := measurable_normalizeKernelVector r
  let Q' := Q.map T
  have : IsProbabilityMeasure Q' := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hrows' : Q'.fst = Measure.pi (fun _ => stdGaussian E) := by
    change (Q.map T).map Prod.fst = _
    rw [Measure.map_map measurable_fst hT]
    exact hrows
  have hs' : ∀ᵐ z ∂Q', ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ := by
    change ∀ᵐ z ∂Q.map T, ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ
    have hm : MeasurableSet {z : (Fin r → E) × E | z.2 ∈ (rowSpan z.1)ᗮ} := by
      have he : {z : (Fin r → E) × E | z.2 ∈ (rowSpan z.1)ᗮ} =
          {z | rowProjectionL z.1 z.2 = 0} := by
        ext z
        simp only [Set.mem_ofPred_eq, rowProjectionL_eq, Submodule.starProjection_apply_eq_zero_iff]
      rw [he]
      exact measurableSet_eq_fun (measurable_rowProjection_pair r) measurable_const
    apply (ae_map_iff hT.aemeasurable (show MeasurableSet
      {z : (Fin r → E) × E | ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ} from
      (measurableSet_eq_fun measurable_snd.norm (measurable_const (a:= (1:ℝ)))).inter hm)).mpr
    exact hsupport.mono fun z hz => normalizeKernelVector_support z hz
  have hvol := independent_kernel_inverse_volume_pi hr hd hq hmargin Q' hrows' hs'
  have hmap : (Measure.pi (fun _ : Fin q => Q)).map (fun h i => T (h i)) =
      Measure.pi (fun _ : Fin q => Q') := Measure.pi_map_pi (fun _ => hT.aemeasurable)
  have hprodT : Measurable (fun h : KernelHistory r q E => fun i => T (h i)) := by fun_prop
  have hnondeg : ∀ᵐ h : KernelHistory r q E ∂Measure.pi (fun _ => Q),
      ∀ i, gramSchmidt ℝ (fun j => (T (h j)).2) i ≠ 0 := by
    have ht := hvol.2
    rw [← hmap, ae_map_iff hprodT.aemeasurable (measurableSet_kernel_nondegenerate r q)] at ht
    exact ht
  have hnonzero : ∀ᵐ h : KernelHistory r q E ∂Measure.pi (fun _ => Q),
      ∀ i, (h i).2 ≠ 0 := by
    refine ae_all_iff.mpr fun i => ?_
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin q => Q) i).ae
      (hsupport.mono fun _ hz => hz.1)
  have hf : Measurable (fun z : ((Fin r → E) × E) × E =>
      ENNReal.ofReal ‖z.1.2‖ * φ ⟪z.1.2,z.2⟫) := by fun_prop
  have hpow (x : E) := lintegral_pow_pi Q
    (fun z => ENNReal.ofReal ‖z.2‖ * φ ⟪z.2,x⟫)
    (hf.comp (measurable_id.prodMk measurable_const)) q
  calc
    _ = ∫⁻ h : KernelHistory r q E, ∫⁻ x, ∏ i,
        (ENNReal.ofReal ‖(h i).2‖ * φ ⟪(h i).2,x⟫)
        ∂stdGaussian E ∂Measure.pi (fun _ => Q) := by
      simp_rw [hpow]
      rw [lintegral_lintegral_swap (by fun_prop)]
    _ ≤ ∫⁻ h : KernelHistory r q E, kernelInverseVolume (fun i => T (h i))
        ∂Measure.pi (fun _ => Q) := by
      apply lintegral_mono_ae
      filter_upwards [hnondeg, hnonzero] with h hn hz
      have hgs (i : Fin q) : gramSchmidt ℝ (fun j => (h j).2) i ≠ 0 := by
        have hi := hn i
        change gramSchmidt ℝ (fun j => ‖(h j).2‖⁻¹ • (h j).2) i ≠ 0 at hi
        rw [gramSchmidt_diagonal_smul _ _ (fun j => inv_ne_zero (norm_ne_zero_iff.mpr (hz j)))] at hi
        exact fun hh => hi (by rw [hh, smul_zero])
      have hli : LinearIndependent ℝ (fun i => (h i).2) := by
        apply Matrix.linearIndependent_of_det_gram_ne_zero
        rw [det_gram_eq_prod_gramSchmidt]
        exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hgs i))
      simp_rw [Finset.prod_mul_distrib]
      rw [lintegral_const_mul _ (by fun_prop)]
      calc
        _ ≤ (∏ i, ENNReal.ofReal ‖(h i).2‖) * kernelInverseVolume h :=
          mul_le_mul' le_rfl (gaussian_single_kernel_bound _ hli φ hφ hφ1)
        _ = kernelInverseVolume (fun i => T (h i)) := by
          rw [kernelInverseVolume_normalization h hz, ←mul_assoc, ←Finset.prod_mul_distrib]
          have hc (i : Fin q) : ENNReal.ofReal ‖(h i).2‖ * ENNReal.ofReal ‖(h i).2‖⁻¹ = 1 := by
            rw [←ENNReal.ofReal_mul (norm_nonneg _), mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hz i))]
            exact ENNReal.ofReal_one
          simp only [hc, Finset.prod_const_one, one_mul]
          rfl
    _ = ∫⁻ h : KernelHistory r q E, kernelInverseVolume h ∂Measure.pi (fun _ => Q') := by
      rw [←hmap, lintegral_map (measurable_kernelInverseVolume r q) hprodT]
    _ ≤ _ := hvol.1

end KernelNormalizedMoment



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



lemma compProd_withDensity_fst {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [IsProbabilityMeasure μ] (κ : Kernel A B) [IsMarkovKernel κ]
    (w : A×B → ℝ≥0∞) (hw : Measurable w)
    (h1 : ∀ᵐ a ∂μ, ∫⁻ b, w (a,b) ∂κ a = 1) :
    ((μ ⊗ₘ κ).withDensity w).fst = μ := by
  ext s hs
  rw [Measure.fst_apply hs, withDensity_apply _ (hs.preimage measurable_fst),
    ←lintegral_indicator (hs.preimage measurable_fst),
    Measure.lintegral_compProd (hw.indicator (hs.preimage measurable_fst))]
  calc
    _ = ∫⁻ a, s.indicator (fun _ => (1:ℝ≥0∞)) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [h1] with a ha
      by_cases has : a ∈ s
      · simpa only [Set.indicator_of_mem has, Set.mem_preimage, has,
          Set.indicator_of_mem] using ha
      · simp [Set.indicator_of_notMem, has]
    _ = μ s := by simp [lintegral_indicator hs]

section KernelTilt
variable {E : Type*} [NormedAddCommGroup E] [innerProductSpaceRealE : InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [nontrivialE : Nontrivial E]



omit innerProductSpaceRealE finiteDimensionalRealE nontrivialE in
lemma measurable_reciprocalKernelScale {r : ℕ} (κ : Kernel (Fin r → E) E)
    [IsMarkovKernel κ] (s : E) : Measurable (reciprocalKernelScale κ s) := by
  exact (show Measurable (fun t : E => ENNReal.ofReal (‖t-s‖⁻¹)) by fun_prop).lintegral_kernel

lemma reciprocal_kernel_projection_moment {r q : ℕ}
    (hr : r ≤ Module.finrank ℝ E) (hd : Module.finrank ℝ E ≤ 8*r)
    (hq : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (κ : Kernel (Fin r → E) E) [IsMarkovKernel κ] (s : E)
    (hscale : ∀ᵐ A ∂Measure.pi (fun _ : Fin r => stdGaussian E),
      reciprocalKernelScale κ s A ≠ 0 ∧ reciprocalKernelScale κ s A ≠ ∞)
    (hsupport : ∀ᵐ z ∂(Measure.pi (fun _ : Fin r => stdGaussian E)) ⊗ₘ κ,
      z.2-s ≠ 0 ∧ z.2-s ∈ (rowSpan z.1)ᗮ)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ t, φ t = 1) :
    ∫⁻ x, (∫⁻ A, (∫⁻ t, φ ⟪t-s,x⟫ ∂κ A) / reciprocalKernelScale κ s A
      ∂Measure.pi (fun _ : Fin r => stdGaussian E))^q ∂stdGaussian E ≤
      ENNReal.ofReal (5*kernelSmallBallConstant)^q := by
  let γ := Measure.pi (fun _ : Fin r => stdGaussian E)
  let P := γ ⊗ₘ κ
  let a := reciprocalKernelScale κ s
  let w : (Fin r → E)×E → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z.2-s‖⁻¹) / a z.1
  have ha : Measurable a := measurable_reciprocalKernelScale κ s
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hmass : ∀ᵐ A ∂γ, ∫⁻ t, w (A,t) ∂κ A = 1 := by
    filter_upwards [hscale] with A hA
    dsimp [w]
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const _ (by fun_prop)]
    exact ENNReal.div_self hA.1 hA.2
  let P' := P.withDensity w
  have hfst : P'.fst = γ := compProd_withDensity_fst γ κ w hw hmass
  have : IsProbabilityMeasure P' := by
    have hp : IsProbabilityMeasure P'.fst := hfst ▸ inferInstance
    have : IsProbabilityMeasure (P'.map Prod.fst) := hp
    exact Measure.isProbabilityMeasure_of_map (μ:=P') Prod.fst
  let D : (Fin r → E)×E → (Fin r → E)×E := fun z => (z.1,z.2-s)
  have hD : Measurable D := by dsimp [D]; fun_prop
  let Q := P'.map D
  have : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hQfst : Q.fst = γ := by
    change (P'.map D).map Prod.fst = _
    rw [Measure.map_map measurable_fst hD]
    exact hfst
  have hQsup : ∀ᵐ z ∂Q, z.2 ≠ 0 ∧ z.2 ∈ (rowSpan z.1)ᗮ := by
    have hm : MeasurableSet {z : (Fin r → E)×E |
        z.2 ≠ 0 ∧ z.2 ∈ (rowSpan z.1)ᗮ} := by
      have he : {z : (Fin r → E)×E | z.2 ∈ (rowSpan z.1)ᗮ} =
          {z | rowProjectionL z.1 z.2 = 0} := by
        ext z
        simp only [Set.mem_ofPred_eq, rowProjectionL_eq, Submodule.starProjection_apply_eq_zero_iff]
      exact (measurableSet_eq_fun measurable_snd measurable_const).compl.inter
        (by
          change MeasurableSet {z : (Fin r → E)×E | z.2 ∈ (rowSpan z.1)ᗮ}
          rw [he]
          exact measurableSet_eq_fun (measurable_rowProjection_pair r) measurable_const)
    apply (ae_map_iff hD.aemeasurable hm).mpr
    exact (withDensity_absolutelyContinuous P w).ae_le hsupport
  have hmoment := kernel_normalized_projection_moment hr hd hq hmargin Q hQfst hQsup φ hφ hφ1
  have heq (x : E) : (∫⁻ z, ENNReal.ofReal ‖z.2‖ * φ ⟪z.2,x⟫ ∂Q) =
      ∫⁻ A, (∫⁻ t, φ ⟪t-s,x⟫ ∂κ A) / a A ∂γ := by
    rw [lintegral_map (by fun_prop) hD]
    rw [lintegral_withDensity_eq_lintegral_mul P hw (by dsimp [D]; fun_prop)]
    calc
      _ = ∫⁻ z, φ ⟪z.2-s,x⟫ / a z.1 ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hsupport] with z hz
        change w z * (ENNReal.ofReal ‖z.2-s‖ * φ ⟪z.2-s,x⟫) = _
        dsimp [w]
        have hn : 0 < ‖z.2-s‖ := norm_pos_iff.mpr hz.1
        rw [ENNReal.ofReal_inv_of_pos hn]
        have hc := ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hn).ne' ENNReal.ofReal_ne_top
        rw [div_eq_mul_inv, div_eq_mul_inv]
        calc
          _ = ((ENNReal.ofReal ‖z.2-s‖)⁻¹ * ENNReal.ofReal ‖z.2-s‖) *
              (φ ⟪z.2-s,x⟫ * (a z.1)⁻¹) := by simp only [mul_assoc, mul_comm, mul_left_comm]
          _ = _ := by rw [hc, one_mul]
      _ = _ := by
        rw [Measure.lintegral_compProd (by fun_prop)]
        apply lintegral_congr
        intro A
        simp_rw [div_eq_mul_inv]
        rw [lintegral_mul_const _ (by fun_prop)]
  simpa only [heq] using hmoment

end KernelTilt





lemma negativeLogAbs_nonneg (x : ℝ) : 0 ≤ negativeLogAbs x := le_max_right _ _

lemma integrable_negativeLogAbs_gaussian :
    Integrable negativeLogAbs (gaussianReal 0 1) := by
  have hl : IntegrableOn Real.log (Set.Icc (-1) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1:ℝ) ≤ 1)).mp
      intervalIntegral.intervalIntegrable_log'
  have hm : IntegrableOn negativeLogAbs (Set.Icc (-1) 1) volume := by
    have h := (show Integrable (-Real.log) (volume.restrict (Set.Icc (-1) 1)) from hl.neg).sup (integrable_const 0)
    have he : negativeLogAbs = (-Real.log ⊔ fun _ => 0) := by
      ext x
      simp [negativeLogAbs, Real.log_abs]
    rw [IntegrableOn, he]
    exact h
  have hi : Integrable ((Set.Icc (-1:ℝ) 1).indicator negativeLogAbs) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hm
  have he : (Set.Icc (-1:ℝ) 1).indicator negativeLogAbs = negativeLogAbs := by
    funext x
    by_cases hx : x ∈ Set.Icc (-1:ℝ) 1
    · simp [hx]
    · have ha : 1 ≤ |x| := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]
          linarith
        · exact (le_abs_self x).trans' hx.le
      have hlog := Real.log_nonneg ha
      rw [Set.indicator_of_notMem hx, negativeLogAbs, max_eq_right (neg_nonpos.mpr hlog)]
  rw [he] at hi
  exact hi.mono_measure gaussianReal_le_volume

lemma regularizedCauchyCross_upper {r e : ℝ} (hr : 0 ≤ r) (he : 0 < e)
    (x y : ℝ) (hx : x ≠ 0) :
    regularizedCauchyCross r e x y ≤
      Real.log (max r e) + Real.log Real.pi + x^2+y^2+negativeLogAbs x := by
  have ht : 0 < (r*x)^2+(r*y)^2+e^2 := by positivity
  have hD : 0 < (r*x)^2+e^2 := by positivity
  have hxy : 0 < 1+x^2+y^2 := by positivity
  have hlxy : Real.log (1+x^2+y^2) ≤ x^2+y^2 := by
    have h := Real.log_le_sub_one_of_pos hxy
    linarith
  have hex : 0 < |x| := abs_pos.mpr hx
  have hlogx : -Real.log |x| ≤ negativeLogAbs x := le_max_left _ _
  rcases le_total r e with hre | her
  · have hs : r^2 ≤ e^2 := (sq_le_sq₀ hr he.le).mpr hre
    have hu : (r*x)^2+(r*y)^2+e^2 ≤ e^2*(1+x^2+y^2) := by
      have h1 := mul_le_mul_of_nonneg_right hs (sq_nonneg x)
      have h2 := mul_le_mul_of_nonneg_right hs (sq_nonneg y)
      nlinarith
    have hlogT := Real.log_le_log ht hu
    rw [Real.log_mul (sq_pos_of_pos he).ne' hxy.ne', Real.log_pow] at hlogT
    have hlogD := Real.log_le_log (sq_pos_of_pos he)
      (show e^2 ≤ (r*x)^2+e^2 by nlinarith [sq_nonneg (r*x)])
    rw [Real.log_pow] at hlogD
    rw [max_eq_right hre]
    unfold regularizedCauchyCross
    norm_num only [Nat.cast_ofNat] at hlogT hlogD
    linarith [negativeLogAbs_nonneg x]
  · have hrp : 0 < r := he.trans_le her
    have hs : e^2 ≤ r^2 := (sq_le_sq₀ he.le hr).mpr her
    have hu : (r*x)^2+(r*y)^2+e^2 ≤ r^2*(1+x^2+y^2) := by nlinarith
    have hlogT := Real.log_le_log ht hu
    rw [Real.log_mul (sq_pos_of_pos hrp).ne' hxy.ne', Real.log_pow] at hlogT
    have hlogD := Real.log_le_log (mul_pos (sq_pos_of_pos hrp) (sq_pos_of_ne_zero hx))
      (show r^2*x^2 ≤ (r*x)^2+e^2 by nlinarith [sq_nonneg e])
    rw [Real.log_mul (sq_pos_of_pos hrp).ne' (sq_pos_of_ne_zero hx).ne',
      Real.log_pow, Real.log_pow, ←Real.log_abs x] at hlogD
    rw [max_eq_left her]
    unfold regularizedCauchyCross
    norm_num only [Nat.cast_ofNat] at hlogT hlogD
    linarith

lemma regularizedCauchyCross_lower {r e : ℝ} (he : 0 < e) (x y : ℝ) :
    Real.log Real.pi + Real.log e ≤ regularizedCauchyCross r e x y := by
  have hD : 0 < (r*x)^2+e^2 := by positivity
  have hDT := Real.log_le_log hD
    (show (r*x)^2+e^2 ≤ (r*x)^2+(r*y)^2+e^2 by nlinarith [sq_nonneg (r*y)])
  have heD := Real.log_le_log (sq_pos_of_pos he)
    (show e^2 ≤ (r*x)^2+e^2 by nlinarith [sq_nonneg (r*x)])
  rw [Real.log_pow] at heD
  unfold regularizedCauchyCross
  norm_num only [Nat.cast_ofNat] at heD
  linarith

lemma integrable_standardNormal_square : Integrable (fun x : ℝ => x^2) (gaussianReal 0 1) := by
  exact (memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq

lemma integral_standardNormal_square : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ:=0) (v:=1)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa using h

lemma integrable_regularizedCauchyCross {r e : ℝ} (hr : 0 ≤ r) (he : 0 < e) :
    Integrable (fun z : ℝ×ℝ => regularizedCauchyCross r e z.1 z.2) standardNormalPair := by
  have hsq1 := integrable_standardNormal_square.comp_fst (ν:=gaussianReal 0 1)
  have hsq2 := integrable_standardNormal_square.comp_snd (μ:=gaussianReal 0 1)
  have hn := integrable_negativeLogAbs_gaussian.comp_fst (ν:=gaussianReal 0 1)
  have hup : Integrable (fun z : ℝ×ℝ => Real.log (max r e)+Real.log Real.pi+
      z.1^2+z.2^2+negativeLogAbs z.1) standardNormalPair :=
    (((integrable_const _).add hsq1).add hsq2).add hn
  have hx : ∀ᵐ z : ℝ×ℝ ∂standardNormalPair, z.1 ≠ 0 := by
    have hx0 : ∀ᵐ x : ℝ ∂gaussianReal 0 1, x ≠ 0 := by
      apply ae_iff.mpr
      apply (gaussianReal_absolutelyContinuous 0 (by norm_num : (1:ℝ≥0) ≠ 0))
      simp
    exact Measure.quasiMeasurePreserving_fst.ae hx0
  exact integrable_of_le_of_le (by unfold regularizedCauchyCross; fun_prop)
    (ae_of_all _ fun z => regularizedCauchyCross_lower he z.1 z.2)
    (hx.mono fun z hz => regularizedCauchyCross_upper hr he z.1 z.2 hz)
    (integrable_const _) hup

lemma integral_regularizedCauchyCross {r e : ℝ} (hr : 0 ≤ r) (he : 0 < e) :
    (∫ z : ℝ×ℝ, regularizedCauchyCross r e z.1 z.2 ∂standardNormalPair) ≤
      Real.log (max r e) + cauchyTiltConstant := by
  have hsq1 := integrable_standardNormal_square.comp_fst (ν:=gaussianReal 0 1)
  have hsq2 := integrable_standardNormal_square.comp_snd (μ:=gaussianReal 0 1)
  have hn := integrable_negativeLogAbs_gaussian.comp_fst (ν:=gaussianReal 0 1)
  have hup : Integrable (fun z : ℝ×ℝ => Real.log (max r e)+Real.log Real.pi+
      z.1^2+z.2^2+negativeLogAbs z.1) standardNormalPair :=
    (((integrable_const _).add hsq1).add hsq2).add hn
  have hx : ∀ᵐ z : ℝ×ℝ ∂standardNormalPair, z.1 ≠ 0 := by
    have hx0 : ∀ᵐ x : ℝ ∂gaussianReal 0 1, x ≠ 0 := by
      apply ae_iff.mpr
      apply (gaussianReal_absolutelyContinuous 0 (by norm_num : (1:ℝ≥0) ≠ 0))
      simp
    exact Measure.quasiMeasurePreserving_fst.ae hx0
  have h := integral_mono_ae (integrable_regularizedCauchyCross hr he) hup
    (hx.mono fun z hz => regularizedCauchyCross_upper hr he z.1 z.2 hz)
  have heq : (∫ z : ℝ×ℝ, Real.log (max r e)+Real.log Real.pi+
      z.1^2+z.2^2+negativeLogAbs z.1 ∂standardNormalPair) =
      Real.log (max r e)+cauchyTiltConstant := by
    have hc : Integrable (fun _ : ℝ×ℝ => Real.log (max r e)+Real.log Real.pi)
        standardNormalPair := integrable_const _
    have h1 := integral_add ((hc.add hsq1).add hsq2) hn
    have h2 := integral_add (hc.add hsq1) hsq2
    have h3 := integral_add hc hsq1
    simp only [Pi.add_apply] at h1 h2 h3
    rw [h1, h2, h3]
    rw [integral_fun_fst (fun x : ℝ => x^2), integral_fun_snd (fun x : ℝ => x^2),
      integral_fun_fst negativeLogAbs, integral_const]
    simp only [probReal_univ, one_smul, integral_standardNormal_square]
    unfold cauchyTiltConstant
    ring
  exact h.trans_eq heq




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


lemma gaussian_pair_inner_map_scaled (v : E) :
    ((stdGaussian E).prod (stdGaussian E)).map
      (fun z : E×E => (⟪v,z.1⟫,⟪v,z.2⟫)) =
      standardNormalPair.map (fun z : ℝ×ℝ => (‖v‖*z.1,‖v‖*z.2)) := by
  change ((stdGaussian E).prod (stdGaussian E)).map (Prod.map (fun x => ⟪v,x⟫) (fun x => ⟪v,x⟫)) =
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (Prod.map (fun x => ‖v‖*x) (fun x => ‖v‖*x))
  rw [←Measure.map_prod_map (stdGaussian E) (stdGaussian E) (by fun_prop) (by fun_prop),
    gaussian_inner_map_scaled,Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]

lemma gaussian_regularizedCross_integrable (v : E) {e : ℝ} (he : 0 < e) :
    Integrable (fun z : E×E => regularizedCauchyCross 1 e ⟪v,z.1⟫ ⟪v,z.2⟫)
      ((stdGaussian E).prod (stdGaussian E)) := by
  have hm : Measurable (fun z : ℝ×ℝ => regularizedCauchyCross 1 e z.1 z.2) := by
    unfold regularizedCauchyCross; fun_prop
  have hms : Measurable (fun z : ℝ×ℝ => (‖v‖*z.1,‖v‖*z.2)) := by fun_prop
  have hmv : Measurable (fun z : E×E => (⟪v,z.1⟫,⟪v,z.2⟫)) := by fun_prop
  have hi := integrable_regularizedCauchyCross (norm_nonneg v) he
  have hi' : Integrable (fun z : ℝ×ℝ => regularizedCauchyCross 1 e (‖v‖*z.1) (‖v‖*z.2))
      standardNormalPair := by simpa only [regularizedCauchyCross,one_mul] using hi
  have hmap : Integrable (fun z : ℝ×ℝ => regularizedCauchyCross 1 e z.1 z.2)
      (standardNormalPair.map (fun z : ℝ×ℝ => (‖v‖*z.1,‖v‖*z.2))) :=
    (integrable_map_measure hm.aestronglyMeasurable hms.aemeasurable).mpr hi'
  rw [←gaussian_pair_inner_map_scaled v] at hmap
  exact (integrable_map_measure hm.aestronglyMeasurable hmv.aemeasurable).mp hmap

lemma gaussian_regularizedCross_integral (v : E) {e : ℝ} (he : 0 < e) :
    (∫ z : E×E, regularizedCauchyCross 1 e ⟪v,z.1⟫ ⟪v,z.2⟫
      ∂(stdGaussian E).prod (stdGaussian E)) ≤
      Real.log (max ‖v‖ e) + cauchyTiltConstant := by
  have hm : Measurable (fun z : ℝ×ℝ => regularizedCauchyCross 1 e z.1 z.2) := by
    unfold regularizedCauchyCross; fun_prop
  rw [←integral_map (by fun_prop : AEMeasurable (fun z : E×E => (⟪v,z.1⟫,⟪v,z.2⟫)) _)
    hm.aestronglyMeasurable,gaussian_pair_inner_map_scaled,
    integral_map (by fun_prop) hm.aestronglyMeasurable]
  simpa only [regularizedCauchyCross,one_mul] using integral_regularizedCauchyCross (norm_nonneg v) he

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




lemma weighted_log_integral {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (w g : T → ℝ)
    (hw : ∀ t, 0 < w t) (hg : ∀ t, 0 < g t)
    (hwi : Integrable w μ) (hgi : Integrable g μ)
    (hli : Integrable (fun t => w t * (Real.log (g t) - Real.log (w t))) μ)
    (hA : 0 < ∫ t, w t ∂μ) (hM : 0 < ∫ t, g t ∂μ) :
    (∫ t, w t * (Real.log (g t) - Real.log (w t)) ∂μ) ≤
      (∫ t, w t ∂μ) * (Real.log (∫ t, g t ∂μ) - Real.log (∫ t, w t ∂μ)) := by
  let A := ∫ t, w t ∂μ
  let M := ∫ t, g t ∂μ
  change 0 < A at hA
  change 0 < M at hM
  have hp (t : T) : w t * (Real.log (g t) - Real.log (w t)) ≤
      w t * (Real.log M - Real.log A) + (A/M)*g t - w t := by
    have hh := Real.log_le_sub_one_of_pos (div_pos (div_pos (hg t) (hw t)) (div_pos hM hA))
    rw [Real.log_div (div_ne_zero (hg t).ne' (hw t).ne') (div_ne_zero hM.ne' hA.ne'),
      Real.log_div (hg t).ne' (hw t).ne',Real.log_div hM.ne' hA.ne'] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (hw t).le
    have he : w t * ((g t / w t) / (M / A) - 1) = (A/M)*g t - w t := by
      field_simp [hA.ne',hM.ne',(hw t).ne']
    rw [he] at hh'
    nlinarith
  have hi : Integrable (fun t => w t*(Real.log M-Real.log A)+(A/M)*g t-w t) μ :=
    ((hwi.mul_const _).add (hgi.const_mul (A/M))).sub hwi
  have hb := integral_mono hli hi hp
  have hv : (∫ t, w t * (Real.log M-Real.log A) + (A/M)*g t - w t ∂μ) =
      A * (Real.log M-Real.log A) + (A/M)*M - A := by
    calc
      _ = (∫ t, w t * (Real.log M-Real.log A) + (A/M)*g t ∂μ) - A :=
        integral_sub ((hwi.mul_const _).add (hgi.const_mul _)) hwi
      _ = A * (Real.log M-Real.log A) + (A/M)*M - A := by
        rw [integral_add (hwi.mul_const (Real.log M-Real.log A)) (hgi.const_mul (A/M))]
        simp only [integral_mul_const, integral_const_mul, A, M]
  rw [hv,div_mul_cancel₀ _ hM.ne'] at hb
  linarith

lemma sphere_subtype_dist_le_two {d : ℕ} (s t : Sphere d) : dist s t ≤ 2 := by
  simpa only [Subtype.dist_eq,dist_eq_norm,norm_eq_of_mem_sphere s,
    norm_eq_of_mem_sphere t,one_add_one_eq_two] using norm_sub_le (s:Vector d) (t:Vector d)

lemma regularizedReciprocal_pos {d : ℕ} {e : ℝ} (he : 0 < e) (s t : Sphere d) :
    0 < regularizedReciprocal e s t := inv_pos.mpr (he.trans_le (le_max_right _ _))

lemma regularizedReciprocal_bounds {d : ℕ} {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (s t : Sphere d) : 1/2 ≤ regularizedReciprocal e s t ∧ regularizedReciprocal e s t ≤ e⁻¹ := by
  have hmax : 0 < max (dist s t) e := he.trans_le (le_max_right _ _)
  constructor
  · simp only [one_div,regularizedReciprocal]
    change (2:ℝ)⁻¹ ≤ (max (dist s t) e)⁻¹
    exact (inv_le_inv₀ (by norm_num) hmax).mpr (max_le (sphere_subtype_dist_le_two s t) (by linarith))
  · exact (inv_le_inv₀ hmax he).mpr (le_max_right _ _)

lemma integrable_regularizedReciprocal {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (s : Sphere d) : Integrable (regularizedReciprocal e s) μ := by
  apply (integrable_const (e⁻¹)).mono' (by unfold regularizedReciprocal; fun_prop)
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs,abs_of_pos (regularizedReciprocal_pos he s t)]
  exact (inv_le_inv₀ (he.trans_le (le_max_right _ _)) he).mpr (le_max_right _ _)

lemma regularizedScale_bounds {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    1/2 ≤ regularizedScale μ e s ∧ regularizedScale μ e s ≤ e⁻¹ := by
  have hi := integrable_regularizedReciprocal μ he s
  constructor
  · simpa [regularizedScale] using integral_mono (integrable_const (1/2:ℝ)) hi
      (fun t => (regularizedReciprocal_bounds he he1 s t).1)
  · simpa [regularizedScale] using integral_mono hi (integrable_const (e⁻¹))
      (fun t => (regularizedReciprocal_bounds he he1 s t).2)

lemma log_regularizedReciprocal {d : ℕ} (e : ℝ) (s t : Sphere d) :
    Real.log (regularizedReciprocal e s t) = -Real.log (max (dist s t) e) := Real.log_inv _



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Mixture
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


lemma continuous_sphereCauchyCross {d : ℕ} {e : ℝ} (he : 0 < e) (s : Sphere d) :
    Continuous (fun z : Sphere d×(Vector d×Vector d) => sphereCauchyCross e s z.1 z.2) := by
  unfold sphereCauchyCross regularizedCauchyCross
  fun_prop (disch := intro z; positivity)

lemma continuous_regularizedReciprocal {d : ℕ} {e : ℝ} (he : 0 < e) (s : Sphere d) :
    Continuous (regularizedReciprocal e s) := by
  unfold regularizedReciprocal
  exact (continuous_const.dist continuous_id |>.max continuous_const).inv₀
    (fun t => (he.trans_le (le_max_right (dist s t) e)).ne')

lemma sphereCauchyCross_lower {d : ℕ} {e : ℝ} (he : 0 < e) (s t : Sphere d)
    (x : Vector d×Vector d) : Real.log Real.pi + Real.log e ≤ sphereCauchyCross e s t x :=
  regularizedCauchyCross_lower he _ _

lemma sphereCauchyCross_norm_integral {d : ℕ} {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (s t : Sphere d) :
    (∫ x, ‖sphereCauchyCross e s t x‖ ∂gaussianVectorPair d) ≤
      Real.log 2 + cauchyTiltConstant + 2*|Real.log Real.pi+Real.log e| := by
  have hi : Integrable (sphereCauchyCross e s t) (gaussianVectorPair d) :=
    gaussian_regularizedCross_integrable ((s:Vector d)-(t:Vector d)) he
  have hb := gaussian_regularizedCross_integral ((s:Vector d)-(t:Vector d)) he
  have hdist : ‖(s:Vector d)-(t:Vector d)‖ ≤ 2 := by
    simpa only [dist_eq_norm,Subtype.dist_eq] using sphere_subtype_dist_le_two s t
  have hl := Real.log_le_log (he.trans_le (le_max_right ‖(s:Vector d)-(t:Vector d)‖ e))
    (max_le hdist (by linarith : e ≤ 2))
  have hp (x : Vector d×Vector d) : ‖sphereCauchyCross e s t x‖ ≤
      sphereCauchyCross e s t x + 2*|Real.log Real.pi+Real.log e| := by
    rw [Real.norm_eq_abs,abs_le]
    have hh := sphereCauchyCross_lower he s t x
    constructor <;> linarith [le_abs_self (Real.log Real.pi+Real.log e),neg_abs_le (Real.log Real.pi+Real.log e)]
  have h := integral_mono hi.norm (hi.add (integrable_const _)) hp
  have hv : (∫ x, sphereCauchyCross e s t x + 2*|Real.log Real.pi+Real.log e|
      ∂gaussianVectorPair d) = (∫ x, sphereCauchyCross e s t x ∂gaussianVectorPair d) +
      2*|Real.log Real.pi+Real.log e| := by
    calc
      _ = (∫ x, sphereCauchyCross e s t x ∂gaussianVectorPair d) +
        ∫ (_ : Vector d×Vector d), 2*|Real.log Real.pi+Real.log e| ∂gaussianVectorPair d :=
          integral_add hi (integrable_const _)
      _ = _ := by simp
  change _ ≤ ∫ x, sphereCauchyCross e s t x + 2*|Real.log Real.pi+Real.log e| ∂gaussianVectorPair d at h
  rw [hv] at h
  exact h.trans (by dsimp [sphereCauchyCross] at *; linarith)

lemma sphereCauchyCross_joint_integrable {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    Integrable (fun z : Sphere d×(Vector d×Vector d) => sphereCauchyCross e s z.1 z.2)
      (μ.prod (gaussianVectorPair d)) := by
  have hm := (continuous_sphereCauchyCross he s).measurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun t => gaussian_regularizedCross_integrable ((s:Vector d)-(t:Vector d)) he),?_⟩
  apply (integrable_const (Real.log 2+cauchyTiltConstant+2*|Real.log Real.pi+Real.log e|)).mono'
    hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact sphereCauchyCross_norm_integral he he1 s t

lemma continuous_sphereCauchyCross_slice {d : ℕ} {e : ℝ} (he : 0 < e)
    (s : Sphere d) (x : Vector d×Vector d) : Continuous (fun t => sphereCauchyCross e s t x) := by
  change Continuous ((fun z : Sphere d×(Vector d×Vector d) => sphereCauchyCross e s z.1 z.2) ∘
    (fun t : Sphere d => (t,x)))
  exact (continuous_sphereCauchyCross he s).comp
    (continuous_id.prodMk (continuous_const (y:=x)))

lemma integrable_ownCauchyPDF {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (s : Sphere d) (x : Vector d×Vector d) :
    Integrable (fun t => Real.exp (-sphereCauchyCross e s t x)) μ := by
  have hm : Continuous (fun t => sphereCauchyCross e s t x) :=
    continuous_sphereCauchyCross_slice he s x
  have hme : AEStronglyMeasurable (fun t => Real.exp (-sphereCauchyCross e s t x)) μ :=
    (Real.continuous_exp.comp hm.neg).aestronglyMeasurable
  apply (integrable_const (Real.exp (-(Real.log Real.pi+Real.log e)))).mono' hme
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (neg_le_neg (sphereCauchyCross_lower he s t x)))

lemma ownCauchyMixture_pos {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (s : Sphere d) (x : Vector d×Vector d) :
    0 < ownCauchyMixture μ e s x := by
  apply (integral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun t => (Real.exp_pos _).le))
    (integrable_ownCauchyPDF μ he s x)).mpr
  simp [Function.support,Real.exp_ne_zero]

lemma ownCauchyMixture_cross_lower {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (s : Sphere d) (x : Vector d×Vector d) :
    Real.log Real.pi+Real.log e ≤ -Real.log (ownCauchyMixture μ e s x) := by
  have hb : ownCauchyMixture μ e s x ≤ Real.exp (-(Real.log Real.pi+Real.log e)) := by
    have h := integral_mono (integrable_ownCauchyPDF μ he s x)
      (integrable_const (Real.exp (-(Real.log Real.pi+Real.log e))))
      (fun t => Real.exp_le_exp.mpr (neg_le_neg (sphereCauchyCross_lower he s t x)))
    simpa [ownCauchyMixture] using h
  have hl := Real.log_le_log (ownCauchyMixture_pos μ he s x) hb
  rw [Real.log_exp] at hl
  linarith

lemma integrable_weighted_sphereCauchy {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    Integrable (fun z : Sphere d×(Vector d×Vector d) => regularizedReciprocal e s z.1 *
      (sphereCauchyCross e s z.1 z.2 + Real.log (regularizedReciprocal e s z.1)))
      (μ.prod (gaussianVectorPair d)) := by
  have hw := continuous_regularizedReciprocal he s
  have hl : Continuous (fun t => Real.log (regularizedReciprocal e s t)) :=
    hw.log (fun t => (regularizedReciprocal_pos he s t).ne')
  have hli : Integrable (fun t => Real.log (regularizedReciprocal e s t)) μ :=
    hl.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hli' := hli.comp_fst (ν:=gaussianVectorPair d)
  exact ((sphereCauchyCross_joint_integrable μ he he1 s).add hli').bdd_mul
    (hw.comp continuous_fst).aestronglyMeasurable
    (ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_pos (regularizedReciprocal_pos he s z.1)]
      exact (regularizedReciprocal_bounds he he1 s z.1).2))

lemma ownCauchyMixture_cross_upper {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) (x : Vector d×Vector d) :
    -Real.log (ownCauchyMixture μ e s x) ≤ -Real.log (regularizedScale μ e s) +
      (∫ t, regularizedReciprocal e s t *
        (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ) / regularizedScale μ e s := by
  have hA : 0 < regularizedScale μ e s := lt_of_lt_of_le (by norm_num) (regularizedScale_bounds μ he he1 s).1
  have hc : Continuous (fun t => sphereCauchyCross e s t x) :=
    continuous_sphereCauchyCross_slice he s x
  have hw := continuous_regularizedReciprocal he s
  have hcw : Continuous (fun t => regularizedReciprocal e s t *
      (-sphereCauchyCross e s t x - Real.log (regularizedReciprocal e s t))) :=
    hw.mul (hc.neg.sub (hw.log (fun t => (regularizedReciprocal_pos he s t).ne')))
  have hi := hcw.integrable_of_hasCompactSupport (μ:=μ) (HasCompactSupport.of_compactSpace _)
  have h := weighted_log_integral μ (regularizedReciprocal e s)
    (fun t => Real.exp (-sphereCauchyCross e s t x)) (regularizedReciprocal_pos he s)
    (fun t => Real.exp_pos _) (integrable_regularizedReciprocal μ he s)
    (integrable_ownCauchyPDF μ he s x) (by simpa only [Real.log_exp] using hi) hA (ownCauchyMixture_pos μ he s x)
  simp only [Real.log_exp] at h
  have heq : (fun t => regularizedReciprocal e s t * (-sphereCauchyCross e s t x - Real.log (regularizedReciprocal e s t))) =
      fun t => -(regularizedReciprocal e s t * (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t))) := by
    funext t
    ring
  rw [heq,integral_neg] at h
  change -_ ≤ regularizedScale μ e s * (Real.log (ownCauchyMixture μ e s x) - Real.log (regularizedScale μ e s)) at h
  have hh : -Real.log (ownCauchyMixture μ e s x)+Real.log (regularizedScale μ e s) ≤
      (∫ t, regularizedReciprocal e s t * (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ) / regularizedScale μ e s := by
    apply (le_div_iff₀ hA).mpr
    nlinarith
  linarith

lemma ownCauchyMixture_measurable {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (s : Sphere d) : Measurable (ownCauchyMixture μ e s) := by
  have hm : StronglyMeasurable (fun z : Sphere d×(Vector d×Vector d) =>
      Real.exp (-sphereCauchyCross e s z.1 z.2)) :=
    (Real.continuous_exp.comp (continuous_sphereCauchyCross he s).neg).stronglyMeasurable
  exact hm.integral_prod_left'.measurable

lemma ownCauchyMixture_cross_integrable {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    Integrable (fun x => -Real.log (ownCauchyMixture μ e s x)) (gaussianVectorPair d) := by
  have hi := integrable_weighted_sphereCauchy μ he he1 s
  have hu : Integrable (fun x : Vector d×Vector d => -Real.log (regularizedScale μ e s) +
      (∫ t, regularizedReciprocal e s t *
        (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ) / regularizedScale μ e s)
      (gaussianVectorPair d) := (integrable_const _).add (hi.integral_prod_right.div_const _)
  exact integrable_of_le_of_le (ownCauchyMixture_measurable μ he s).log.neg.aestronglyMeasurable
    (ae_of_all _ (fun x => ownCauchyMixture_cross_lower μ he s x))
    (ae_of_all _ (fun x => ownCauchyMixture_cross_upper μ he he1 s x))
    (integrable_const _) hu

lemma weightedCauchyCross_integral_bound {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    (∫ x, ∫ t, regularizedReciprocal e s t *
      (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ
      ∂gaussianVectorPair d) ≤ regularizedScale μ e s * cauchyTiltConstant := by
  have hi := integrable_weighted_sphereCauchy μ he he1 s
  rw [←integral_integral_swap hi]
  have hup : Integrable (fun t => regularizedReciprocal e s t * cauchyTiltConstant) μ :=
    (integrable_regularizedReciprocal μ he s).mul_const _
  calc
    _ ≤ ∫ t, regularizedReciprocal e s t * cauchyTiltConstant ∂μ := by
      apply integral_mono hi.integral_prod_left hup
      intro t
      have ht : Integrable (sphereCauchyCross e s t) (gaussianVectorPair d) :=
        gaussian_regularizedCross_integrable ((s:Vector d)-(t:Vector d)) he
      dsimp only
      rw [integral_const_mul]
      have hv : (∫ x, sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)
          ∂gaussianVectorPair d) = (∫ x, sphereCauchyCross e s t x ∂gaussianVectorPair d) +
          Real.log (regularizedReciprocal e s t) := by
        calc
          _ = (∫ x, sphereCauchyCross e s t x ∂gaussianVectorPair d) +
              ∫ (_ : Vector d×Vector d), Real.log (regularizedReciprocal e s t) ∂gaussianVectorPair d :=
            integral_add ht (integrable_const _)
          _ = _ := by simp
      rw [hv]
      apply mul_le_mul_of_nonneg_left _ (regularizedReciprocal_pos he s t).le
      have hb := gaussian_regularizedCross_integral ((s:Vector d)-(t:Vector d)) he
      change (∫ x, sphereCauchyCross e s t x ∂gaussianVectorPair d) ≤ _ at hb
      rw [←dist_eq_norm,←Subtype.dist_eq] at hb
      rw [log_regularizedReciprocal]
      linarith
    _ = _ := integral_mul_const _ _

lemma ownCauchyMixture_cross_integral {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    (∫ x, -Real.log (ownCauchyMixture μ e s x) ∂gaussianVectorPair d) ≤
      cauchyTiltConstant - Real.log (regularizedScale μ e s) := by
  have hi := integrable_weighted_sphereCauchy μ he he1 s
  have hA : 0 < regularizedScale μ e s := lt_of_lt_of_le (by norm_num) (regularizedScale_bounds μ he he1 s).1
  have hu : Integrable (fun x : Vector d×Vector d => -Real.log (regularizedScale μ e s) +
      (∫ t, regularizedReciprocal e s t *
        (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ) / regularizedScale μ e s)
      (gaussianVectorPair d) := (integrable_const _).add (hi.integral_prod_right.div_const _)
  have hb := integral_mono (ownCauchyMixture_cross_integrable μ he he1 s) hu
    (ownCauchyMixture_cross_upper μ he he1 s)
  have hv : (∫ x, -Real.log (regularizedScale μ e s) +
      (∫ t, regularizedReciprocal e s t *
        (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ) / regularizedScale μ e s
      ∂gaussianVectorPair d) = -Real.log (regularizedScale μ e s) +
      (∫ x, ∫ t, regularizedReciprocal e s t *
        (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ
        ∂gaussianVectorPair d) / regularizedScale μ e s := by
    rw [integral_add (integrable_const _) (hi.integral_prod_right.div_const _)]
    simp only [integral_const,probReal_univ,one_smul,integral_div]
  rw [hv] at hb
  have hn := (div_le_iff₀ hA).mpr (by simpa only [mul_comm] using weightedCauchyCross_integral_bound μ he he1 s)
  linarith



lemma regularizedCauchyPDF_eq {e : ℝ} (he : 0 < e) (a b : ℝ) :
    regularizedCauchyPDF e a b = cauchyPDFReal 0
      ⟨Real.sqrt (a^2+e^2), Real.sqrt_nonneg _⟩ b := by
  have hD : 0 < a^2+e^2 := by positivity
  have hT : 0 < b^2+(Real.sqrt (a^2+e^2))^2 := by positivity
  have hs : (⟨Real.sqrt (a^2+e^2),Real.sqrt_nonneg _⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : ℝ≥0 => (x:ℝ)) h
    exact (Real.sqrt_pos.mpr hD).ne' h'
  have hp := cauchyPDF_pos 0 hs b
  have hl : -regularizedCauchyCross 1 e a b = Real.log (cauchyPDFReal 0
      (⟨Real.sqrt (a^2+e^2),Real.sqrt_nonneg _⟩ : ℝ≥0) b) := by
    change -regularizedCauchyCross 1 e a b = Real.log
      (Real.pi⁻¹ * Real.sqrt (a^2+e^2) * ((b-0)^2+(Real.sqrt (a^2+e^2))^2)⁻¹)
    rw [sub_zero,Real.log_mul (mul_ne_zero (inv_ne_zero Real.pi_ne_zero)
      (Real.sqrt_pos.mpr hD).ne') (inv_ne_zero hT.ne'),
      Real.log_mul (inv_ne_zero Real.pi_ne_zero) (Real.sqrt_pos.mpr hD).ne',Real.log_inv,Real.log_inv,
      Real.log_sqrt hD.le,Real.sq_sqrt hD.le]
    unfold regularizedCauchyCross
    simp only [one_mul]
    rw [show b^2+(a^2+e^2)=a^2+b^2+e^2 by ring]
    ring
  exact (congrArg Real.exp hl).trans (Real.exp_log hp)

lemma integrable_regularizedCauchyPDF {e : ℝ} (he : 0 < e) (a : ℝ) :
    Integrable (regularizedCauchyPDF e a) volume := by
  have hf : regularizedCauchyPDF e a = cauchyPDFReal 0
      ⟨Real.sqrt (a^2+e^2), Real.sqrt_nonneg _⟩ := funext (regularizedCauchyPDF_eq he a)
  rw [hf]
  exact integrable_cauchyPDFReal _

lemma integral_regularizedCauchyPDF {e : ℝ} (he : 0 < e) (a : ℝ) :
    (∫ b, regularizedCauchyPDF e a b) = 1 := by
  simp_rw [regularizedCauchyPDF_eq he]
  apply integral_cauchyPDFReal_eq_one
  intro h
  have h' := congrArg (fun x : ℝ≥0 => (x:ℝ)) h
  exact (Real.sqrt_pos.mpr (by positivity : 0 < a^2+e^2)).ne' h'

lemma lintegral_regularizedCauchyPDF {e : ℝ} (he : 0 < e) (a : ℝ) :
    (∫⁻ b, ENNReal.ofReal (regularizedCauchyPDF e a b)) = 1 := by
  rw [←ofReal_integral_eq_lintegral_ofReal (integrable_regularizedCauchyPDF he a)
    (ae_of_all _ (fun b => (Real.exp_pos _).le)),integral_regularizedCauchyPDF he]
  simp

lemma cauchyMixture_at_own {d : ℕ} (μ : Measure (Sphere d)) (e : ℝ)
    (s : Sphere d) (x : Vector d×Vector d) :
    cauchyMixture μ e x (⟪(s:Vector d),x.1⟫,⟪(s:Vector d),x.2⟫) = ownCauchyMixture μ e s x := by
  unfold cauchyMixture ownCauchyMixture regularizedCauchyPDF sphereCauchyCross
  simp only [inner_sub_left]

lemma cauchyMixture_integrand_integrable {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (x : Vector d×Vector d) (b : ℝ×ℝ) :
    Integrable (fun t : Sphere d => regularizedCauchyPDF e
      (b.1-⟪(t:Vector d),x.1⟫) (b.2-⟪(t:Vector d),x.2⟫)) μ := by
  have hm : Measurable (fun t : Sphere d => regularizedCauchyPDF e
      (b.1-⟪(t:Vector d),x.1⟫) (b.2-⟪(t:Vector d),x.2⟫)) := by
    unfold regularizedCauchyPDF regularizedCauchyCross
    fun_prop
  apply (integrable_const (Real.exp (-(Real.log Real.pi+Real.log e)))).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs]
  unfold regularizedCauchyPDF
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (neg_le_neg (regularizedCauchyCross_lower he _ _))

lemma cauchyMixture_pos {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (x : Vector d×Vector d) (b : ℝ×ℝ) : 0 < cauchyMixture μ e x b := by
  apply (integral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun t => (Real.exp_pos _).le))
    (cauchyMixture_integrand_integrable μ he x b)).mpr
  simp [Function.support,Real.exp_ne_zero]

lemma cauchyMixture_kernel_measurable {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] (e : ℝ) :
    Measurable (fun z : (C×(Vector d×Vector d))×(ℝ×ℝ) => cauchyMixture (κ z.1.1) e z.1.2 z.2) := by
  have hm : StronglyMeasurable (fun z : ((C×(Vector d×Vector d))×(ℝ×ℝ)) × Sphere d =>
      regularizedCauchyPDF e (z.1.2.1-⟪(z.2:Vector d),z.1.1.2.1⟫)
        (z.1.2.2-⟪(z.2:Vector d),z.1.1.2.2⟫)) := by
    apply Measurable.stronglyMeasurable
    unfold regularizedCauchyPDF regularizedCauchyCross
    fun_prop
  exact (hm.integral_kernel_prod_right' (κ:=κ.comap (fun z => z.1.1) (by fun_prop))).measurable

lemma cauchyMixture_normalization {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (x : Vector d×Vector d) (b₁ : ℝ) :
    (∫⁻ b₂, ENNReal.ofReal (cauchyMixture μ e x (b₁,b₂))) = 1 := by
  have hid (b₂ : ℝ) : ENNReal.ofReal (cauchyMixture μ e x (b₁,b₂)) =
      ∫⁻ t : Sphere d, ENNReal.ofReal (regularizedCauchyPDF e
        (b₁-⟪(t:Vector d),x.1⟫) (b₂-⟪(t:Vector d),x.2⟫)) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal (cauchyMixture_integrand_integrable μ he x (b₁,b₂))
      (ae_of_all _ (fun t => (Real.exp_pos _).le))
  simp_rw [hid]
  rw [lintegral_lintegral_swap (by unfold regularizedCauchyPDF regularizedCauchyCross; fun_prop)]
  have ht (t : Sphere d) : (∫⁻ b₂, ENNReal.ofReal (regularizedCauchyPDF e
      (b₁-⟪(t:Vector d),x.1⟫) (b₂-⟪(t:Vector d),x.2⟫))) = 1 := by
    rw [lintegral_sub_right_eq_self (f:=fun b : ℝ => ENNReal.ofReal
      (regularizedCauchyPDF e (b₁-⟪(t:Vector d),x.1⟫) b))]
    exact lintegral_regularizedCauchyPDF he _
  simp_rw [ht]
  simp



lemma ownCauchyMixture_cross_norm_integral {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    (∫ x, ‖-Real.log (ownCauchyMixture μ e s x)‖ ∂gaussianVectorPair d) ≤
      cauchyTiltConstant - Real.log (1/2:ℝ) + 2*|Real.log Real.pi+Real.log e| := by
  have hi := ownCauchyMixture_cross_integrable μ he he1 s
  have hlo := (regularizedScale_bounds μ he he1 s).1
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<1/2) hlo
  have hup := ownCauchyMixture_cross_integral μ he he1 s
  have hb : (∫ x, ‖-Real.log (ownCauchyMixture μ e s x)‖ ∂gaussianVectorPair d) ≤
      (∫ x, -Real.log (ownCauchyMixture μ e s x) ∂gaussianVectorPair d) +
        2*|Real.log Real.pi+Real.log e| := by
    calc
      _ ≤ ∫ x, -Real.log (ownCauchyMixture μ e s x) +
          2*|Real.log Real.pi+Real.log e| ∂gaussianVectorPair d := by
        apply integral_mono hi.norm (hi.add (integrable_const _))
        intro x
        have hx := ownCauchyMixture_cross_lower μ he s x
        dsimp only [Pi.add_apply]
        rw [Real.norm_eq_abs]
        apply abs_le.mpr
        constructor <;> linarith [abs_nonneg (Real.log Real.pi+Real.log e),
          neg_abs_le (Real.log Real.pi+Real.log e)]
      _ = _ := by rw [integral_add hi (integrable_const _)]; simp
  linarith

lemma regularizedScale_kernel_measurable {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] (e : ℝ) :
    Measurable (fun z : C×Sphere d => regularizedScale (κ z.1) e z.2) := by
  have hm : StronglyMeasurable (fun z : (C×Sphere d)×Sphere d => regularizedReciprocal e z.1.2 z.2) := by
    apply Measurable.stronglyMeasurable
    unfold regularizedReciprocal
    fun_prop
  exact (hm.integral_kernel_prod_right' (κ:=κ.comap Prod.fst measurable_fst)).measurable

lemma ownCauchyMixture_kernel_measurable {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] (e : ℝ) :
    Measurable (fun z : (C×Sphere d)×(Vector d×Vector d) => ownCauchyMixture (κ z.1.1) e z.1.2 z.2) := by
  have he : (fun z : (C×Sphere d)×(Vector d×Vector d) => ownCauchyMixture (κ z.1.1) e z.1.2 z.2) =
      (fun z => cauchyMixture (κ z.1.1) e z.1.2 z.2) ∘
        (fun z : (C×Sphere d)×(Vector d×Vector d) => ((z.1.1,z.2),
          (⟪(z.1.2:Vector d),z.2.1⟫,⟪(z.1.2:Vector d),z.2.2⟫))) := by
    funext z
    simp only [Function.comp_apply,cauchyMixture_at_own]
  rw [he]
  exact (cauchyMixture_kernel_measurable κ e).comp (by fun_prop)

lemma ownCauchyMixture_context_integrable {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    Integrable (fun z : (C×Sphere d)×(Vector d×Vector d) =>
      -Real.log (ownCauchyMixture (κ z.1.1) e z.1.2 z.2)) (Γ.prod (gaussianVectorPair d)) := by
  have hm := (ownCauchyMixture_kernel_measurable κ e).log.neg
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun z => ownCauchyMixture_cross_integrable (κ z.1) he he1 z.2),?_⟩
  apply (integrable_const (cauchyTiltConstant-Real.log (1/2:ℝ)+2*|Real.log Real.pi+Real.log e|)).mono'
    (hm.stronglyMeasurable.norm.integral_prod_right.aestronglyMeasurable)
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact ownCauchyMixture_cross_norm_integral (κ z.1) he he1 z.2

lemma regularizedScale_context_log_integrable {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    Integrable (fun z : C×Sphere d => Real.log (regularizedScale (κ z.1) e z.2)) Γ := by
  apply integrable_of_le_of_le (regularizedScale_kernel_measurable κ e).log.aestronglyMeasurable
    (g₁:=fun _ => Real.log (1/2:ℝ)) (g₂:=fun _ => Real.log e⁻¹)
  · exact ae_of_all _ (fun z => Real.log_le_log (by norm_num) (regularizedScale_bounds (κ z.1) he he1 z.2).1)
  · exact ae_of_all _ (fun z => Real.log_le_log (lt_of_lt_of_le (by norm_num)
      (regularizedScale_bounds (κ z.1) he he1 z.2).1) (regularizedScale_bounds (κ z.1) he he1 z.2).2)
  · exact integrable_const _
  · exact integrable_const _

lemma ownCauchyMixture_context_bound {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    (∫ z : (C×Sphere d)×(Vector d×Vector d), -Real.log (ownCauchyMixture (κ z.1.1) e z.1.2 z.2)
      ∂Γ.prod (gaussianVectorPair d)) ≤
      cauchyTiltConstant - ∫ z : C×Sphere d, Real.log (regularizedScale (κ z.1) e z.2) ∂Γ := by
  have hi := ownCauchyMixture_context_integrable Γ κ he he1
  have hA := regularizedScale_context_log_integrable Γ κ he he1
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ z : C×Sphere d, cauchyTiltConstant - Real.log (regularizedScale (κ z.1) e z.2) ∂Γ :=
      integral_mono hi.integral_prod_left ((integrable_const _).sub hA)
        (fun z => ownCauchyMixture_cross_integral (κ z.1) he he1 z.2)
    _ = _ := by rw [integral_sub (integrable_const _) hA]; simp



lemma reference_gibbs {A : Type*} [MeasurableSpace A]
    (P R Λ : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure R] [SigmaFinite Λ]
    (r q : A → ℝ) (hr : Measurable r) (hq : Measurable q)
    (hrpos : ∀ z, 0 < r z) (hqpos : ∀ z, 0 < q z)
    (hR : Λ.withDensity (fun z => ENNReal.ofReal (r z)) = R)
    (hnorm : (∫⁻ z, ENNReal.ofReal (q z) ∂Λ) = 1)
    (hPR : klDiv P R ≠ ∞) (hri : Integrable (fun z => Real.log (r z)) P)
    (hqi : Integrable (fun z => Real.log (q z)) P) :
    (∫ z, -Real.log (r z) ∂P) - (klDiv P R).toReal ≤ ∫ z, -Real.log (q z) ∂P := by
  let Q := Λ.withDensity (fun z => ENNReal.ofReal (q z))
  let : IsProbabilityMeasure Q := ⟨by simpa only [Q,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using hnorm⟩
  have hd := llr_of_two_densities R Q Λ (fun z => ENNReal.ofReal (r z)) hr.ennreal_ofReal hR
    q hq hqpos rfl
  have hPRac := (klDiv_ne_top_iff.mp hPR).1
  have he : llr R Q =ᵐ[P] fun z => Real.log (r z) - Real.log (q z) := by
    filter_upwards [hPRac.ae_le hd.2] with z hz
    simpa only [ENNReal.toReal_ofReal (hrpos z).le] using hz
  have hi := (hri.sub hqi).congr he.symm
  have hk := klDiv_chain_finite P R Q hPR hd.1 hi
  have hnonneg := ENNReal.toReal_nonneg (a:=klDiv P Q)
  rw [hk.2,integral_congr_ae he,integral_sub hri hqi] at hnonneg
  simp only [integral_neg]
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


lemma measurable_cauchyObservation {d : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (cauchyObservation (d:=d) (C:=C)) := by
  unfold cauchyObservation
  fun_prop

instance cauchyObservationLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] : IsProbabilityMeasure (cauchyObservationLaw Γ) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_cauchyObservation.aemeasurable).mpr inferInstance

lemma gaussian_inner_map_sphere {d : ℕ} (s : Sphere d) :
    (stdGaussian (Vector d)).map (fun x => ⟪(s:Vector d),x⟫) = gaussianReal 0 1 := by
  rw [gaussian_inner_map_scaled,show ‖(s:Vector d)‖ = 1 from mem_sphere_zero_iff_norm.mp s.property]
  simp only [one_mul,Measure.map_id']

lemma cauchyObservationLaw_snd {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    (cauchyObservationLaw Γ).snd = gaussianReal 0 1 := by
  rw [Measure.snd,cauchyObservationLaw,Measure.map_map measurable_snd measurable_cauchyObservation]
  ext t ht
  rw [Measure.map_apply (by unfold cauchyObservation; fun_prop) ht,
    Measure.prod_apply (ht.preimage (by unfold cauchyObservation; fun_prop))]
  have ho (z : C×Sphere d) : gaussianVectorPair d {x | ⟪(z.2:Vector d),x.2⟫ ∈ t} = gaussianReal 0 1 t := by
    have hm : Measurable (fun x : Vector d => ⟪(z.2:Vector d),x⟫) := by fun_prop
    have he := congrArg (fun μ : Measure ℝ => μ t) (gaussian_inner_map_sphere z.2)
    rw [Measure.map_apply hm ht] at he
    change gaussianVectorPair d (Prod.snd ⁻¹' ((fun x : Vector d => ⟪(z.2:Vector d),x⟫) ⁻¹' t)) = _
    rw [←Measure.snd_apply (ht.preimage hm),Measure.snd_prod]
    exact he
  change (∫⁻ z : C×Sphere d, gaussianVectorPair d {x | ⟪(z.2:Vector d),x.2⟫ ∈ t} ∂Γ) = _
  simp_rw [ho]
  simp

lemma log_standardGaussianPDF (x : ℝ) :
    Real.log (gaussianPDFReal 0 1 x) = -Real.log (Real.sqrt (2*Real.pi))-x^2/2 := by
  change Real.log ((Real.sqrt (2*Real.pi*1))⁻¹ * Real.exp (-(x-0)^2/(2*1))) = _
  simp only [mul_one,sub_zero]
  rw [Real.log_mul (inv_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne') (Real.exp_pos _).ne',
    Real.log_inv,Real.log_exp]
  ring

lemma standardGaussian_cross_entropy {T : Type*} [MeasurableSpace T]
    (P : Measure (T×ℝ)) [IsProbabilityMeasure P] (hm : P.snd = gaussianReal 0 1) :
    Integrable (fun z : T×ℝ => Real.log (gaussianPDFReal 0 1 z.2)) P ∧
      (∫ z : T×ℝ, -Real.log (gaussianPDFReal 0 1 z.2) ∂P) = standardGaussianEntropy := by
  have hf : Measurable (fun x : ℝ => Real.log (gaussianPDFReal 0 1 x)) := by fun_prop
  have hsq := integrable_standardNormal_square
  have hi : Integrable (fun x : ℝ => Real.log (gaussianPDFReal 0 1 x)) (gaussianReal 0 1) := by
    simp_rw [log_standardGaussianPDF]
    exact (integrable_const _).sub (hsq.div_const 2)
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable measurable_snd.aemeasurable).mp (by change Integrable _ P.snd; rw [hm]; exact hi),?_⟩
  have he := integral_map (μ:=P) (φ:=Prod.snd) measurable_snd.aemeasurable hf.neg.aestronglyMeasurable
  change (∫ z, (-fun x => Real.log (gaussianPDFReal 0 1 x)) z.2 ∂P) = _
  rw [←he]
  change (∫ x, -Real.log (gaussianPDFReal 0 1 x) ∂P.snd) = _
  rw [hm]
  simp_rw [log_standardGaussianPDF,neg_sub]
  rw [integral_sub (hsq.div_const 2) (integrable_const _),integral_div,integral_standardNormal_square]
  simp [standardGaussianEntropy,add_comm]

lemma cauchyMixture_experiment_bound {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ]
    (hfin : conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1) ≠ ∞)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    standardGaussianEntropy - (conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1)).toReal ≤
      cauchyTiltConstant - ∫ z : C×Sphere d, Real.log (regularizedScale (κ z.1) e z.2) ∂Γ := by
  let P := cauchyObservationLaw Γ
  let Λ := P.fst.prod (volume : Measure ℝ)
  let r : (((C×(Vector d×Vector d))×ℝ)×ℝ) → ℝ := fun z => gaussianPDFReal 0 1 z.2
  let q : (((C×(Vector d×Vector d))×ℝ)×ℝ) → ℝ :=
    fun z => cauchyMixture (κ z.1.1.1) e z.1.1.2 (z.1.2,z.2)
  have hr : Measurable r := by dsimp [r]; fun_prop
  have hq : Measurable q := (cauchyMixture_kernel_measurable κ e).comp (show Measurable (fun z : (((C×(Vector d×Vector d))×ℝ)×ℝ) => ((z.1.1.1,z.1.1.2),(z.1.2,z.2))) by fun_prop)
  have hrpos : ∀ z, 0 < r z := fun z => gaussianPDFReal_pos _ _ _ (by norm_num)
  have hqpos : ∀ z, 0 < q z := fun z => cauchyMixture_pos _ he _ _
  have hR : Λ.withDensity (fun z => ENNReal.ofReal (r z)) = P.fst.prod (gaussianReal 0 1) := by
    rw [show (fun z => ENNReal.ofReal (r z)) = (fun z => gaussianPDF 0 1 z.2) from rfl,
      ←prod_withDensity_right (measurable_gaussianPDF 0 1),gaussianReal_of_var_ne_zero 0 (by norm_num)]
  have hnorm : (∫⁻ z, ENNReal.ofReal (q z) ∂Λ) = 1 := by
    rw [lintegral_prod _ hq.ennreal_ofReal.aemeasurable]
    simp_rw [show ∀ z : (C×(Vector d×Vector d))×ℝ,
      (∫⁻ y, ENNReal.ofReal (q (z,y))) = 1 from fun z => cauchyMixture_normalization (κ z.1.1) he z.1.2 z.2]
    simp
  have hc := standardGaussian_cross_entropy P (cauchyObservationLaw_snd Γ)
  have hqi : Integrable (fun z => Real.log (q z)) P := by
    apply (integrable_map_measure hq.log.aestronglyMeasurable measurable_cauchyObservation.aemeasurable).mpr
    have hi := (ownCauchyMixture_context_integrable Γ κ he he1).neg
    convert hi using 1
    ext z
    simp [q,cauchyObservation,cauchyMixture_at_own]
  have hg := reference_gibbs P (P.fst.prod (gaussianReal 0 1)) Λ r q hr hq hrpos hqpos hR hnorm hfin hc.1 hqi
  rw [hc.2] at hg
  have heq : (∫ z, -Real.log (q z) ∂P) = ∫ z, -Real.log (ownCauchyMixture (κ z.1.1) e z.1.2 z.2)
      ∂Γ.prod (gaussianVectorPair d) := by
    rw [show P = (Γ.prod (gaussianVectorPair d)).map cauchyObservation from rfl,
      integral_map (f:=fun z => -Real.log (q z)) measurable_cauchyObservation.aemeasurable hq.log.neg.aestronglyMeasurable]
    simp only [q,cauchyObservation,cauchyMixture_at_own]
  rw [heq] at hg
  exact hg.trans (ownCauchyMixture_context_bound Γ κ he he1)



lemma reciprocalCutoff_pos (n : ℕ) : 0 < reciprocalCutoff n := by unfold reciprocalCutoff; positivity
lemma reciprocalCutoff_le_one (n : ℕ) : reciprocalCutoff n ≤ 1 := by
  unfold reciprocalCutoff
  apply (div_le_iff₀ (by positivity)).mpr
  simp
lemma reciprocalCutoff_antitone : Antitone reciprocalCutoff := by
  intro n m h
  unfold reciprocalCutoff
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right h 1
lemma reciprocalCutoff_limit : Tendsto reciprocalCutoff atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma regularizedReciprocal_monotone {d : ℕ} (s t : Sphere d) :
    Monotone (fun n => regularizedReciprocal (reciprocalCutoff n) s t) := by
  intro n m h
  unfold regularizedReciprocal
  apply inv_anti₀ (lt_of_lt_of_le (reciprocalCutoff_pos m) (le_max_right _ _))
  exact max_le_max_left _ (reciprocalCutoff_antitone h)

lemma regularizedReciprocal_limit {d : ℕ} (s t : Sphere d) :
    Tendsto (fun n => ENNReal.ofReal (regularizedReciprocal (reciprocalCutoff n) s t)) atTop
      (𝓝 (ENNReal.ofReal (dist s t))⁻¹) := by
  have hm : Tendsto (fun n => ENNReal.ofReal (max (dist s t) (reciprocalCutoff n))) atTop
      (𝓝 (ENNReal.ofReal (dist s t))) := by
    simpa only [Function.comp_def,max_eq_left dist_nonneg] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((tendsto_const_nhds (x:=dist s t)).max reciprocalCutoff_limit)
  have he : (fun n => ENNReal.ofReal (regularizedReciprocal (reciprocalCutoff n) s t)) =
      fun n => (ENNReal.ofReal (max (dist s t) (reciprocalCutoff n)))⁻¹ := by
    funext n
    exact ENNReal.ofReal_inv_of_pos (lt_of_lt_of_le (reciprocalCutoff_pos n) (le_max_right _ _))
  rw [he]
  exact tendsto_inv_iff.mpr hm

lemma regularizedScale_ofReal {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (s : Sphere d) :
    ENNReal.ofReal (regularizedScale μ e s) = ∫⁻ t, ENNReal.ofReal (regularizedReciprocal e s t) ∂μ :=
  ofReal_integral_eq_lintegral_ofReal (integrable_regularizedReciprocal μ he s)
    (ae_of_all _ (fun t => (regularizedReciprocal_pos he s t).le))

lemma regularizedScale_limit {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ] (s : Sphere d) :
    Tendsto (fun n => ENNReal.ofReal (regularizedScale μ (reciprocalCutoff n) s)) atTop
      (𝓝 (reciprocalScale μ s)) := by
  simp_rw [regularizedScale_ofReal μ (reciprocalCutoff_pos _)]
  exact lintegral_tendsto_of_tendsto_of_monotone
    (fun _ => (by unfold regularizedReciprocal; fun_prop))
    (ae_of_all _ (fun t => fun n m h => ENNReal.ofReal_le_ofReal (regularizedReciprocal_monotone s t h)))
    (ae_of_all _ (fun t => regularizedReciprocal_limit s t))

lemma regularizedScale_monotone {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ] (s : Sphere d) :
    Monotone (fun n => regularizedScale μ (reciprocalCutoff n) s) := by
  intro n m h
  exact integral_mono (integrable_regularizedReciprocal μ (reciprocalCutoff_pos n) s)
    (integrable_regularizedReciprocal μ (reciprocalCutoff_pos m) s)
    (fun t => regularizedReciprocal_monotone s t h)

lemma reciprocalScale_kernel_measurable {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] :
    Measurable (fun z : C×Sphere d => reciprocalScale (κ z.1) z.2) := by
  exact (show Measurable (fun z : (C×Sphere d)×Sphere d => (ENNReal.ofReal (dist z.1.2 z.2))⁻¹) by
    fun_prop).lintegral_kernel_prod_right (κ:=κ.comap Prod.fst measurable_fst)

lemma regularizedScale_le_reciprocalScale {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    (s : Sphere d) (n : ℕ) :
    ENNReal.ofReal (regularizedScale μ (reciprocalCutoff n) s) ≤ reciprocalScale μ s := by
  exact ge_of_tendsto (regularizedScale_limit μ s) (eventually_atTop.mpr ⟨n,fun m hm =>
    ENNReal.ofReal_le_ofReal (regularizedScale_monotone μ s hm)⟩)

lemma reciprocalScale_lower {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ] (s : Sphere d) :
    ENNReal.ofReal (1/2:ℝ) ≤ reciprocalScale μ s :=
  (ENNReal.ofReal_le_ofReal (regularizedScale_bounds μ (reciprocalCutoff_pos 0)
    (reciprocalCutoff_le_one 0) s).1).trans (regularizedScale_le_reciprocalScale μ s 0)

lemma continuous_logScaleExtended : Continuous logScaleExtended :=
  EReal.continuous_toENNReal.comp (ENNReal.continuous_log.comp (ENNReal.continuous_const_mul (a:=2) (by norm_num)))

lemma logScaleExtended_monotone : Monotone logScaleExtended := by
  intro a b h
  apply EReal.toENNReal_le_toENNReal
  exact ENNReal.log_le_log (mul_le_mul_right h 2)

lemma logScaleExtended_ofReal {a : ℝ} (ha : 0 < a) :
    logScaleExtended (ENNReal.ofReal a) = ENNReal.ofReal (Real.log a+Real.log 2) := by
  unfold logScaleExtended
  rw [show (2:ℝ≥0∞)=ENNReal.ofReal (2:ℝ) by norm_num]
  rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.log_ofReal_of_pos (by positivity),
    EReal.real_coe_toENNReal,Real.log_mul (by norm_num) ha.ne']
  congr 1
  ring

lemma logScaleExtended_top_iff (a : ℝ≥0∞) : logScaleExtended a = ∞ ↔ a = ∞ := by
  simp [logScaleExtended,ENNReal.mul_eq_top]

lemma log_add_log_two_nonneg {a : ℝ} (ha : 1/2 ≤ a) : 0 ≤ Real.log a+Real.log 2 := by
  have hp : 0 < a := lt_of_lt_of_le (by norm_num) ha
  rw [←Real.log_mul hp.ne' (by norm_num)]
  apply Real.log_nonneg
  linarith

lemma reciprocalScale_log_bound {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] {M : ℝ}
    (hb : ∀ n, (∫ z : C×Sphere d, Real.log (regularizedScale (κ z.1) (reciprocalCutoff n) z.2) ∂Γ) ≤ M) :
    (∀ᵐ z : C×Sphere d ∂Γ, reciprocalScale (κ z.1) z.2 ≠ ∞) ∧
    Integrable (fun z : C×Sphere d => Real.log (reciprocalScale (κ z.1) z.2).toReal) Γ ∧
    (∫ z : C×Sphere d, Real.log (reciprocalScale (κ z.1) z.2).toReal ∂Γ) ≤ M := by
  let f (n : ℕ) (z : C×Sphere d) := logScaleExtended (ENNReal.ofReal
    (regularizedScale (κ z.1) (reciprocalCutoff n) z.2))
  let F (z : C×Sphere d) := logScaleExtended (reciprocalScale (κ z.1) z.2)
  have hm n : Measurable (f n) := continuous_logScaleExtended.measurable.comp
    (regularizedScale_kernel_measurable κ _).ennreal_ofReal
  have hM : Measurable F := continuous_logScaleExtended.measurable.comp (reciprocalScale_kernel_measurable κ)
  have hl (n : ℕ) (z : C×Sphere d) : 1/2 ≤ regularizedScale (κ z.1) (reciprocalCutoff n) z.2 :=
    (regularizedScale_bounds _ (reciprocalCutoff_pos n) (reciprocalCutoff_le_one n) _).1
  have he n : (∫⁻ z, f n z ∂Γ) = ENNReal.ofReal ((∫ z : C×Sphere d,
      Real.log (regularizedScale (κ z.1) (reciprocalCutoff n) z.2) ∂Γ)+Real.log 2) := by
    simp_rw [f,logScaleExtended_ofReal (lt_of_lt_of_le (by norm_num) (hl n _))]
    rw [←ofReal_integral_eq_lintegral_ofReal (f:=fun z : C×Sphere d => Real.log (regularizedScale (κ z.1) (reciprocalCutoff n) z.2)+Real.log 2)
      ((regularizedScale_context_log_integrable Γ κ (reciprocalCutoff_pos n) (reciprocalCutoff_le_one n)).add (integrable_const _))
      (ae_of_all _ (fun z => log_add_log_two_nonneg (hl n z))),
      integral_add (regularizedScale_context_log_integrable Γ κ (reciprocalCutoff_pos n)
        (reciprocalCutoff_le_one n)) (integrable_const _)]
    simp
  have hn : 0 ≤ M+Real.log 2 := by
    have h := integral_nonneg (μ:=Γ) (f:=fun z : C×Sphere d => Real.log (regularizedScale (κ z.1) (reciprocalCutoff 0) z.2)+Real.log 2) (fun z => log_add_log_two_nonneg (hl 0 z))
    rw [integral_add (regularizedScale_context_log_integrable Γ κ (reciprocalCutoff_pos 0)
      (reciprocalCutoff_le_one 0)) (integrable_const _)] at h
    simp only [integral_const,probReal_univ,one_smul] at h
    linarith [hb 0]
  have ht : Tendsto (fun n => ∫⁻ z, f n z ∂Γ) atTop (𝓝 (∫⁻ z, F z ∂Γ)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone (fun n => (hm n).aemeasurable)
    · exact ae_of_all _ (fun z n m h => logScaleExtended_monotone
        (ENNReal.ofReal_le_ofReal (regularizedScale_monotone (κ z.1) z.2 h)))
    · exact ae_of_all _ (fun z => continuous_logScaleExtended.continuousAt.tendsto.comp
        (regularizedScale_limit (κ z.1) z.2))
  have hbF : (∫⁻ z, F z ∂Γ) ≤ ENNReal.ofReal (M+Real.log 2) := by
    apply le_of_tendsto' ht
    intro n
    rw [he]
    exact ENNReal.ofReal_le_ofReal (by linarith [hb n])
  have hfin : (∫⁻ z, F z ∂Γ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbF
  have haeF : ∀ᵐ z ∂Γ, F z ≠ ∞ := (ae_lt_top hM hfin).mono (fun _ h => h.ne)
  have hae : ∀ᵐ z : C×Sphere d ∂Γ, reciprocalScale (κ z.1) z.2 ≠ ∞ := by
    filter_upwards [haeF] with z hz
    exact mt (logScaleExtended_top_iff _).mpr hz
  have heF : (fun z => (F z).toReal) =ᵐ[Γ]
      fun z : C×Sphere d => Real.log (reciprocalScale (κ z.1) z.2).toReal+Real.log 2 := by
    filter_upwards [hae] with z hz
    have hlz : 1/2 ≤ (reciprocalScale (κ z.1) z.2).toReal := by
      exact (ENNReal.ofReal_le_iff_le_toReal hz).mp (reciprocalScale_lower _ _)
    have hez := logScaleExtended_ofReal (lt_of_lt_of_le (by norm_num) hlz)
    rw [ENNReal.ofReal_toReal hz] at hez
    change (logScaleExtended _).toReal = _
    rw [hez,ENNReal.toReal_ofReal (log_add_log_two_nonneg hlz)]
  have hi := integrable_toReal_of_lintegral_ne_top hM.aemeasurable hfin
  have hi' : Integrable (fun z : C×Sphere d => Real.log (reciprocalScale (κ z.1) z.2).toReal) Γ := by
    have := (hi.congr heF).sub (integrable_const (Real.log 2))
    convert this using 1
    ext z
    simp
  refine ⟨hae,hi',?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbF
  rw [ENNReal.toReal_ofReal hn,←integral_toReal hM.aemeasurable (haeF.mono (fun _ h => h.lt_top)),
    integral_congr_ae heF,integral_add hi' (integrable_const _)] at hreal
  simp only [integral_const,probReal_univ,one_smul] at hreal
  linarith

lemma reciprocalScale_experiment_bound {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ]
    (hfin : conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1) ≠ ∞) :
    (∀ᵐ z : C×Sphere d ∂Γ, reciprocalScale (κ z.1) z.2 ≠ ∞) ∧
    Integrable (fun z : C×Sphere d => Real.log (reciprocalScale (κ z.1) z.2).toReal) Γ ∧
    (∫ z : C×Sphere d, Real.log (reciprocalScale (κ z.1) z.2).toReal ∂Γ) ≤
      cauchyTiltConstant-standardGaussianEntropy+
        (conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1)).toReal := by
  apply reciprocalScale_log_bound Γ κ
  intro n
  have h := cauchyMixture_experiment_bound Γ κ hfin (reciprocalCutoff_pos n) (reciprocalCutoff_le_one n)
  linarith



lemma residualLaw_support {d r : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    ∀ᵐ z ∂residualLaw Γ r, label z.1.2.1 (z.2:Vector d) = z.1.2.2 := by
  apply (ae_map_iff measurable_residualObservation.aemeasurable
    (measurableSet_eq_fun (by unfold label; fun_prop) (by fun_prop))).mpr
  exact ae_of_all _ (fun _ => rfl)

lemma residualPosterior_support {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    ∀ᵐ c ∂(residualLaw Γ r).fst, ∀ᵐ t : Sphere d ∂(residualLaw Γ r).condKernel c,
      label c.2.1 (t:Vector d) = c.2.2 := by
  apply Measure.ae_ae_of_ae_compProd (p:=fun z : (C×(Rows r d×(Fin r→ℝ)))×Sphere d => label z.1.2.1 (z.2:Vector d) = z.1.2.2)
  rw [(residualLaw Γ r).disintegrate (residualLaw Γ r).condKernel]
  exact residualLaw_support Γ

lemma reciprocalScale_finite_nonatomicAt {d : ℕ} (μ : Measure (Sphere d)) (s : Sphere d)
    (h : reciprocalScale μ s ≠ ∞) : ∀ᵐ t ∂μ, t ≠ s := by
  have ha := ae_lt_top (show Measurable (fun t : Sphere d => (ENNReal.ofReal (dist s t))⁻¹) by fun_prop) h
  filter_upwards [ha] with t ht
  rintro rfl
  simp at ht

lemma reciprocalScale_finite_eq_real {d : ℕ} (μ : Measure (Sphere d)) (s : Sphere d)
    (h : reciprocalScale μ s ≠ ∞) :
    reciprocalScale μ s = ∫⁻ t, ENNReal.ofReal (‖(t:Vector d)-(s:Vector d)‖⁻¹) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [reciprocalScale_finite_nonatomicAt μ s h] with t ht
  have hn : 0 < ‖(t:Vector d)-(s:Vector d)‖ := norm_pos_iff.mpr
    (sub_ne_zero.mpr (fun he => ht (Subtype.ext he)))
  rw [ENNReal.ofReal_inv_of_pos hn]
  congr 2
  change dist (s:Vector d) (t:Vector d) = _
  rw [dist_comm,dist_eq_norm]

lemma label_eq_difference_orthogonal {d r : ℕ} (A : Rows r d) (s t : Vector d)
    (h : label A t = label A s) : t-s ∈ (rowSpan A)ᗮ := by
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro u hu
  induction hu using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨i,rfl⟩ := hv
      rw [inner_sub_left,sub_eq_zero]
      exact congrFun h i
  | zero => simp
  | add x y hx hy hx' hy' => simp [inner_add_right,hx',hy']
  | smul a x hx hx' => simp [inner_smul_right,hx']



lemma fixedTargetPosterior_support {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (hfin : ∀ᵐ z ∂residualLaw Γ r, reciprocalScale ((residualLaw Γ r).condKernel z.1) z.2 ≠ ∞) :
    ∀ᵐ z : C×Sphere d ∂Γ, ∀ᵐ w ∂(gaussianRows r d) ⊗ₘ fixedTargetPosterior Γ z.1 z.2,
      w.2-(z.2:Vector d) ≠ 0 ∧ w.2-(z.2:Vector d) ∈ (rowSpan w.1)ᗮ := by
  have hs := ae_of_ae_map measurable_residualObservation.aemeasurable
    (ae_of_ae_map measurable_fst.aemeasurable (residualPosterior_support Γ (r:=r)))
  have hf := ae_of_ae_map measurable_residualObservation.aemeasurable hfin
  filter_upwards [Measure.ae_ae_of_ae_prod hs,Measure.ae_ae_of_ae_prod hf] with z hzs hzf
  apply Measure.ae_compProd_of_ae_ae
  · have hm : Measurable (fun w : Rows r d×Vector d => label w.1 (w.2-(z.2:Vector d))) := by
      unfold label
      fun_prop
    have he : {w : Rows r d×Vector d | w.2-(z.2:Vector d) ≠ 0 ∧
        w.2-(z.2:Vector d) ∈ (rowSpan w.1)ᗮ} =
        {w | w.2-(z.2:Vector d) ≠ 0 ∧ label w.1 (w.2-(z.2:Vector d)) = 0} := by
      ext w
      simp only [Set.mem_ofPred_eq,and_congr_right_iff]
      intro _
      constructor
      · intro h
        funext i
        exact Submodule.inner_left_of_mem_orthogonal
          (show w.1 i ∈ rowSpan w.1 from Submodule.subset_span ⟨i,rfl⟩) h
      · intro h
        have he : label w.1 w.2 = label w.1 (z.2:Vector d) := by
          funext i
          have hi := congrFun h i
          simp only [label,inner_sub_left,Pi.zero_apply] at hi
          exact sub_eq_zero.mp hi
        exact label_eq_difference_orthogonal _ _ _ he
    rw [he]
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl.inter
      (measurableSet_eq_fun hm measurable_const)
  · filter_upwards [hzs,hzf] with A hAs hAf
    unfold fixedTargetPosterior
    rw [Kernel.map_apply _ measurable_subtype_coe]
    change ∀ᵐ t ∂(((residualLaw Γ r).condKernel (z.1,(A,label A (z.2:Vector d)))).map Subtype.val),
      t-(z.2:Vector d) ≠ 0 ∧ t-(z.2:Vector d) ∈ (rowSpan A)ᗮ
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      ((measurableSet_eq_fun (by fun_prop) measurable_const).compl.inter
        ((Submodule.isClosed_orthogonal (rowSpan A)).measurableSet.preimage (by fun_prop)))).mpr
    filter_upwards [hAs,reciprocalScale_finite_nonatomicAt _ _ hAf] with t ht hne
    exact ⟨sub_ne_zero.mpr (fun h => hne (Subtype.ext h)),label_eq_difference_orthogonal A _ _ ht⟩



lemma mixed_entropy_log_bound_ae {A X Z : Type*} [MeasurableSpace A] [MeasurableSpace X]
    [MeasurableSpace Z] (P : Measure (A×X)) [IsProbabilityMeasure P]
    (γ : Measure X) (η : Measure Z) [IsProbabilityMeasure γ] [IsProbabilityMeasure η]
    (hKL : klDiv P (P.fst.prod γ) ≠ ∞)
    (K : (A×X)×Z → ℝ≥0∞) (hKm : Measurable K) (hKt : ∀ z, K z ≠ ∞)
    (hKint : ∀ ax, ∫⁻ z, K (ax,z) ∂η ≠ ∞)
    (C : A → ℝ) (hCm : Measurable C) (hC0 : ∀ a, 0 ≤ C a)
    (hCI : Integrable (fun a => Real.log (1+C a)) P.fst)
    {q : ℕ} (hq : 1 ≤ q)
    (hMoment : ∀ᵐ a ∂P.fst, ∫⁻ x, (∫⁻ z, K ((a,x),z) ∂η)^q ∂γ ≤ (ENNReal.ofReal (C a))^q) :
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
        apply lintegral_mono_ae
        filter_upwards [hMoment] with a hMa
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
          (hFm.comp (measurable_const.prodMk measurable_id)) hq hMa
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



lemma measurable_residualScale {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    Measurable (fun z : (C×Sphere d)×Rows r d => residualScale Γ z.1 z.2) := by
  exact (reciprocalScale_kernel_measurable (residualLaw Γ r).condKernel).comp
    measurable_residualObservation

lemma residualScale_lower {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (z : C×Sphere d) (A : Rows r d) :
    ENNReal.ofReal (1/2:ℝ) ≤ residualScale Γ z A := reciprocalScale_lower _ _

lemma fixedTargetPosterior_scale {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (z : C×Sphere d) (A : Rows r d)
    (hf : residualScale Γ z A ≠ ∞) :
    reciprocalKernelScale (fixedTargetPosterior Γ z.1 z.2) (z.2:Vector d) A = residualScale Γ z A := by
  unfold reciprocalKernelScale fixedTargetPosterior
  rw [Kernel.map_apply _ measurable_subtype_coe]
  rw [lintegral_map (by fun_prop) measurable_subtype_coe]
  exact (reciprocalScale_finite_eq_real _ _ hf).symm

lemma measurable_residualCube {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (δ : ℝ) :
    Measurable (residualCube (r:=r) Γ δ) := by
  let f : ((C×Sphere d)×Vector d)×Rows r d → C×(Rows r d×(Fin r→ℝ)) :=
    fun w => (w.1.1.1,(w.2,label w.2 (w.1.1.2:Vector d)))
  have hf : Measurable f := by unfold f label; fun_prop
  have hn : Measurable (fun w : ((C×Sphere d)×Vector d)×Rows r d =>
      ∫⁻ t : Sphere d, cubeKernel δ ⟪(t:Vector d)-(w.1.1.2:Vector d),w.1.2⟫
      ∂(residualLaw Γ r).condKernel (f w)) :=
    (show Measurable (fun z : (((C×Sphere d)×Vector d)×Rows r d)×Sphere d =>
      cubeKernel δ ⟪(z.2:Vector d)-(z.1.1.1.2:Vector d),z.1.1.2⟫) from
      (measurable_cubeKernel δ).comp (by fun_prop)).lintegral_kernel_prod_right
      (f:=fun w t => cubeKernel δ ⟪(t:Vector d)-(w.1.1.2:Vector d),w.1.2⟫)
      (κ:=(residualLaw Γ r).condKernel.comap f hf)
  exact hn.div ((measurable_residualScale Γ).comp
    (measurable_fst.fst.prodMk measurable_snd))

lemma residualCube_bound {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (δ : ℝ)
    (w : ((C×Sphere d)×Vector d)×Rows r d) :
    residualCube Γ δ w ≤ ENNReal.ofReal ((2*δ)⁻¹) * 2 := by
  have hn : (∫⁻ t : Sphere d, cubeKernel δ ⟪(t:Vector d)-(w.1.1.2:Vector d),w.1.2⟫
      ∂(residualLaw Γ r).condKernel (w.1.1.1,(w.2,label w.2 (w.1.1.2:Vector d)))) ≤
      ENNReal.ofReal ((2*δ)⁻¹) := by
    calc
      _ ≤ ∫⁻ _t : Sphere d, ENNReal.ofReal ((2*δ)⁻¹)
          ∂(residualLaw Γ r).condKernel (w.1.1.1,(w.2,label w.2 (w.1.1.2:Vector d))) :=
        lintegral_mono (fun t => by
          unfold cubeKernel
          exact Set.indicator_le_self _ _ _)
      _ = _ := by simp
  have ha : (residualScale Γ w.1.1 w.2)⁻¹ ≤ (2:ℝ≥0∞) := by
    have h := ENNReal.inv_le_inv.mpr (residualScale_lower Γ w.1.1 w.2)
    have he : (ENNReal.ofReal (1/2:ℝ))⁻¹ = (2:ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_one,ENNReal.ofReal_ofNat]
      simp
    rwa [he] at h
  exact mul_le_mul' hn ha

lemma residualCube_finite {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (δ : ℝ)
    (w : ((C×Sphere d)×Vector d)×Rows r d) : residualCube Γ δ w ≠ ∞ :=
  ne_top_of_le_ne_top (by finiteness) (residualCube_bound Γ δ w)

lemma residualCube_integral_finite {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (δ : ℝ)
    (w : (C×Sphere d)×Vector d) :
    (∫⁻ A, residualCube Γ δ (w,A) ∂gaussianRows r d) ≠ ∞ := by
  apply ne_top_of_le_ne_top (b:=ENNReal.ofReal ((2*δ)⁻¹)*2) (by finiteness)
  exact (lintegral_mono (fun A => residualCube_bound Γ δ (w,A))).trans_eq (by simp)

lemma residualCube_moment {d r q : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (hr : r ≤ d) (hd : d ≤ 8*r) (hq : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (hfin : ∀ᵐ z ∂residualLaw Γ r, reciprocalScale ((residualLaw Γ r).condKernel z.1) z.2 ≠ ∞)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ z : C×Sphere d ∂Γ, ∫⁻ x, (∫⁻ A, residualCube Γ δ ((z,x),A)
      ∂gaussianRows r d)^q ∂stdGaussian (Vector d) ≤ ENNReal.ofReal (5*kernelSmallBallConstant)^q := by
  have hdpos : 0 < d := by omega
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hdpos
  have hf := Measure.ae_ae_of_ae_prod (ae_of_ae_map measurable_residualObservation.aemeasurable hfin)
  filter_upwards [fixedTargetPosterior_support Γ hfin,hf] with z hzs hzf
  have heq : ∀ᵐ A ∂gaussianRows r d,
      reciprocalKernelScale (fixedTargetPosterior Γ z.1 z.2) (z.2:Vector d) A = residualScale Γ z A := by
    filter_upwards [hzf] with A hA
    exact fixedTargetPosterior_scale Γ z A hA
  have hscale : ∀ᵐ A ∂gaussianRows r d,
      reciprocalKernelScale (fixedTargetPosterior Γ z.1 z.2) (z.2:Vector d) A ≠ 0 ∧
      reciprocalKernelScale (fixedTargetPosterior Γ z.1 z.2) (z.2:Vector d) A ≠ ∞ := by
    filter_upwards [heq,hzf] with A he hf
    rw [he]
    exact ⟨ne_of_gt (lt_of_lt_of_le (by norm_num) (residualScale_lower Γ z A)),hf⟩
  have h := reciprocal_kernel_projection_moment (E:=Vector d)
    (by simpa) (by simpa) hq hmargin (fixedTargetPosterior Γ z.1 z.2) (z.2:Vector d)
    hscale hzs (cubeKernel δ) (measurable_cubeKernel δ) (lintegral_cubeKernel hδ)
  apply le_trans (le_of_eq ?_) h
  apply lintegral_congr
  intro x
  congr 1
  apply lintegral_congr_ae
  filter_upwards [heq] with A he
  rw [he]
  unfold residualCube fixedTargetPosterior
  rw [Kernel.map_apply _ measurable_subtype_coe,lintegral_map
    (f:=fun t : Vector d => cubeKernel δ ⟪t-(z.2:Vector d),x⟫)
    ((measurable_cubeKernel δ).comp (by fun_prop)) measurable_subtype_coe]
  rfl




lemma scalarCube_ball (μ : Measure ℝ) (y : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    scalarCube μ y δ = μ (Metric.closedBall y δ) / volume (Metric.closedBall y δ) := by
  have he : (fun t : ℝ => cubeKernel δ (t-y)) =
      Set.indicator (Metric.closedBall y δ) (fun _ => ENNReal.ofReal ((2*δ)⁻¹)) := by
    ext t
    simp only [cubeKernel,Set.indicator_apply]
    congr 1
    simp only [Set.mem_Icc,Metric.mem_closedBall,Real.dist_eq,abs_le]
  unfold scalarCube
  rw [he,lintegral_indicator Metric.isClosed_closedBall.measurableSet,
    lintegral_const,Measure.restrict_apply_univ,Real.volume_closedBall,
    ENNReal.ofReal_inv_of_pos (by positivity),div_eq_mul_inv,mul_comm]

lemma measurable_scalarCube {A : Type*} [MeasurableSpace A]
    (κ : Kernel A ℝ) [IsSFiniteKernel κ] (δ : ℝ) :
    Measurable (fun z : A×ℝ => scalarCube (κ z.1) z.2 δ) := by
  exact ((measurable_cubeKernel δ).comp (show Measurable (fun z : (A×ℝ)×ℝ => z.2-z.1.2) by fun_prop)).lintegral_kernel_prod_right
    (f:=fun z t => cubeKernel δ (t-z.2)) (κ:=κ.comap Prod.fst measurable_fst)

lemma measurable_scalarExtended {A : Type*} [MeasurableSpace A]
    (κ : Kernel A ℝ) [IsSFiniteKernel κ] :
    Measurable (fun z : A×ℝ => scalarExtended (κ z.1) z.2) :=
  Measurable.liminf (fun n => measurable_scalarCube κ (1/(n:ℝ)))

lemma measurable_scalarDensity {A : Type*} [MeasurableSpace A]
    (κ : Kernel A ℝ) [IsSFiniteKernel κ] :
    Measurable (fun z : A×ℝ => scalarDensity (κ z.1) z.2) := by
  exact Measurable.ite (measurableSet_eq_fun (measurable_scalarExtended κ) measurable_const)
    measurable_const (measurable_scalarExtended κ)

lemma scalarDensity_finite (μ : Measure ℝ) (y : ℝ) : scalarDensity μ y ≠ ∞ := by
  unfold scalarDensity
  split_ifs with h <;> simp_all

lemma scalarDensity_ae_rnDeriv (μ : Measure ℝ) [IsFiniteMeasure μ] :
    scalarDensity μ =ᵐ[volume] μ.rnDeriv volume := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ volume,Measure.rnDeriv_ne_top μ volume] with y hy hyt
  have ht := hy.comp tendsto_cube_scale
  have he : (fun n : ℕ => scalarCube μ y (1/(n:ℝ))) =ᶠ[atTop]
      fun n : ℕ => μ (Metric.closedBall y (1/(n:ℝ))) / volume (Metric.closedBall y (1/(n:ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact scalarCube_ball μ y (by positivity)
  have hl : scalarExtended μ y = μ.rnDeriv volume y := (ht.congr' he.symm).liminf_eq
  simp only [scalarDensity,hl,ite_eq_right hyt]

lemma scalarDensity_ae_limit (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ y ∂(volume : Measure ℝ), Tendsto (fun n : ℕ => scalarCube μ y (1/(n:ℝ)))
      atTop (𝓝 (scalarDensity μ y)) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ volume,scalarDensity_ae_rnDeriv μ] with y hy heq
  have he : (fun n : ℕ => scalarCube μ y (1/(n:ℝ))) =ᶠ[atTop]
      fun n : ℕ => μ (Metric.closedBall y (1/(n:ℝ))) / volume (Metric.closedBall y (1/(n:ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact scalarCube_ball μ y (by positivity)
  rw [heq]
  exact (hy.comp tendsto_cube_scale).congr' he.symm

lemma scalarDensity_withDensity (μ : Measure ℝ) [IsFiniteMeasure μ] (h : μ ≪ volume) :
    volume.withDensity (scalarDensity μ) = μ := by
  rw [withDensity_congr_ae (scalarDensity_ae_rnDeriv μ)]
  exact Measure.withDensity_rnDeriv_eq _ _ h

lemma kernel_scalarDensity_withDensity {A : Type*} [MeasurableSpace A]
    (π : Measure A) [SFinite π] (κ : Kernel A ℝ) [IsFiniteKernel κ]
    (h : ∀ᵐ a ∂π, κ a ≪ volume) :
    (π.prod volume).withDensity (fun z : A×ℝ => scalarDensity (κ z.1) z.2) = π ⊗ₘ κ := by
  apply Measure.ext
  intro t ht
  rw [withDensity_apply _ ht,←lintegral_indicator ht,
    lintegral_prod _ ((measurable_scalarDensity κ).indicator ht).aemeasurable,
    Measure.compProd_apply ht]
  apply lintegral_congr_ae
  filter_upwards [h] with a ha
  have ht' : MeasurableSet (Prod.mk a ⁻¹' t) := ht.preimage (measurable_const.prodMk measurable_id)
  rw [←scalarDensity_withDensity (κ a) ha,withDensity_apply _ ht',←lintegral_indicator ht']
  rfl

lemma kernel_scalarDensity_ae_limit {A : Type*} [MeasurableSpace A]
    (π : Measure A) [SFinite π] (κ : Kernel A ℝ) [IsFiniteKernel κ] :
    ∀ᵐ z : A×ℝ ∂π.prod volume, Tendsto
      (fun n : ℕ => scalarCube (κ z.1) z.2 (1/(n:ℝ))) atTop (𝓝 (scalarDensity (κ z.1) z.2)) := by
  have hm : MeasurableSet {z : A×ℝ | Tendsto
      (fun n : ℕ => scalarCube (κ z.1) z.2 (1/(n:ℝ))) atTop (𝓝 (scalarDensity (κ z.1) z.2))} :=
    measurableSet_tendsto_fun (fun n : ℕ => measurable_scalarCube κ (1/(n:ℝ))) (measurable_scalarDensity κ)
  exact (Measure.ae_prod_iff_ae_ae hm).mpr (ae_of_all _ (fun a => scalarDensity_ae_limit (κ a)))



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

lemma compProd_dependentMapKernel {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (μ : Measure A) [SFinite μ]
    (κ : Kernel A B) [IsSFiniteKernel κ] (f : A×B → D) (hf : Measurable f) :
    μ ⊗ₘ dependentMapKernel κ f = (μ ⊗ₘ κ).map (fun z => (z.1,f z)) := by
  have : IsSFiniteKernel (dependentMapKernel κ f) := by unfold dependentMapKernel; infer_instance
  ext t ht
  rw [Measure.compProd_apply ht,Measure.map_apply (measurable_fst.prodMk hf) ht,
    Measure.compProd_apply (ht.preimage (measurable_fst.prodMk hf))]
  apply lintegral_congr
  intro a
  rw [dependentMapKernel_apply κ f hf a,
    Measure.map_apply (show Measurable (fun b => f (a,b)) from hf.comp measurable_prodMk_left)
      (ht.preimage (measurable_prodMk_left (x:=a)))]
  rfl

lemma compProd_conditional_prod_swap {C S X : Type*} [MeasurableSpace C]
    [MeasurableSpace S] [MeasurableSpace X] (μ : Measure C) [SFinite μ]
    (κ : Kernel C S) [IsSFiniteKernel κ] (γ : Measure X) [SFinite γ] :
    ((μ.prod γ) ⊗ₘ κ.comap Prod.fst measurable_fst).map
      (fun z : (C×X)×S => ((z.1.1,z.2),z.1.2)) = (μ ⊗ₘ κ).prod γ := by
  have h1 := compProd_prod_assoc μ (Kernel.const C γ) κ
  rw [Measure.compProd_const] at h1
  rw [←h1,Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.symm.measurable]
  have h2 := compProd_prod_assoc μ κ (Kernel.const C γ)
  have hconst : (Kernel.const C γ).comap (Prod.fst : C×S → C) measurable_fst = Kernel.const _ γ := rfl
  rw [hconst,Measure.compProd_const] at h2
  rw [←h2,←Kernel.map_prod_swap (Kernel.const C γ) κ,Measure.compProd_map measurable_swap,
    Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable (measurable_id.prodMap measurable_swap)]
  rfl

instance scalarProjectionKernel_markov {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] : IsMarkovKernel (scalarProjectionKernel κ) :=
  dependentMapKernel_markov _ _ (by fun_prop)

lemma scalarProjectionKernel_apply {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsSFiniteKernel κ] (z : C×Vector d) :
    scalarProjectionKernel κ z = (κ z.1).map (fun s : Sphere d => ⟪(s:Vector d),z.2⟫) :=
  dependentMapKernel_apply _ _ (by fun_prop) _

lemma measurable_scalarObservation {d : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (scalarObservation (d:=d) (C:=C)) := by unfold scalarObservation; fun_prop

instance scalarObservationLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] : IsProbabilityMeasure (scalarObservationLaw Γ) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_scalarObservation.aemeasurable).mpr inferInstance

lemma scalarObservationLaw_disintegrate {d : ℕ} [Nonempty (Sphere d)]
    {C : Type*} [MeasurableSpace C] (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    (Γ.fst.prod (stdGaussian (Vector d))) ⊗ₘ scalarProjectionKernel Γ.condKernel = scalarObservationLaw Γ := by
  rw [scalarProjectionKernel,compProd_dependentMapKernel _ _ _ (by fun_prop),scalarObservationLaw]
  have he := compProd_conditional_prod_swap Γ.fst Γ.condKernel (stdGaussian (Vector d))
  rw [Γ.disintegrate Γ.condKernel] at he
  rw [←he,Measure.map_map measurable_scalarObservation (by fun_prop)]
  rfl

lemma scalarObservationLaw_fst {d : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    (scalarObservationLaw Γ).fst = Γ.fst.prod (stdGaussian (Vector d)) := by
  rw [←scalarObservationLaw_disintegrate Γ,Measure.fst_compProd]

lemma scalarCube_projection {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsSFiniteKernel κ] (z : C×Vector d) (s : Sphere d) (δ : ℝ) :
    scalarCube (scalarProjectionKernel κ z) ⟪(s:Vector d),z.2⟫ δ =
      ∫⁻ t : Sphere d, cubeKernel δ ⟪(t:Vector d)-(s:Vector d),z.2⟫ ∂κ z.1 := by
  rw [scalarCube,scalarProjectionKernel_apply,lintegral_map
    (f:=fun t : ℝ => cubeKernel δ (t-⟪(s:Vector d),z.2⟫))
    ((measurable_cubeKernel δ).comp (by fun_prop)) (by fun_prop)]
  simp only [inner_sub_left]

lemma scalarObservationLaw_kernel_ac {d : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (h : conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) ≠ ∞) :
    ∀ᵐ a ∂Γ.fst.prod (stdGaussian (Vector d)), scalarProjectionKernel Γ.condKernel a ≪ volume := by
  have hac := (klDiv_ne_top_iff.mp h).1
  have hgv : gaussianReal 0 1 ≪ (volume : Measure ℝ) := by
    rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
    exact withDensity_absolutelyContinuous _ _
  change scalarObservationLaw Γ ≪ (scalarObservationLaw Γ).fst.prod (gaussianReal 0 1) at hac
  have hh : (Γ.fst.prod (stdGaussian (Vector d))) ⊗ₘ scalarProjectionKernel Γ.condKernel ≪
      (Γ.fst.prod (stdGaussian (Vector d))) ⊗ₘ Kernel.const _ (gaussianReal 0 1) := by
    rw [Measure.compProd_const,scalarObservationLaw_disintegrate Γ,←scalarObservationLaw_fst Γ]
    exact hac
  exact hh.kernel_of_compProd.mono (fun a ha => ha.trans hgv)

lemma scalarObservationLaw_density {d : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (h : conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) ≠ ∞) :
    ((scalarObservationLaw Γ).fst.prod volume).withDensity
      (fun z => scalarDensity (scalarProjectionKernel Γ.condKernel z.1) z.2) = scalarObservationLaw Γ := by
  rw [scalarObservationLaw_fst,←scalarObservationLaw_disintegrate Γ]
  exact kernel_scalarDensity_withDensity _ _ (scalarObservationLaw_kernel_ac Γ h)

lemma scalarObservationLaw_ae_limit {d : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (h : conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) ≠ ∞) :
    ∀ᵐ z ∂scalarObservationLaw Γ, Tendsto
      (fun n : ℕ => scalarCube (scalarProjectionKernel Γ.condKernel z.1) z.2 (1/(n:ℝ)))
      atTop (𝓝 (scalarDensity (scalarProjectionKernel Γ.condKernel z.1) z.2)) := by
  have ha : scalarObservationLaw Γ ≪ (scalarObservationLaw Γ).fst.prod volume := by
    have hh := withDensity_absolutelyContinuous
      ((scalarObservationLaw Γ).fst.prod volume)
      (fun z => scalarDensity (scalarProjectionKernel Γ.condKernel z.1) z.2)
    rwa [scalarObservationLaw_density Γ h] at hh
  exact ha.ae_le (kernel_scalarDensity_ae_limit (scalarObservationLaw Γ).fst
    (scalarProjectionKernel Γ.condKernel))

lemma prod_map_swap23 {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (μ : Measure A) (ν : Measure B) (π : Measure D)
    [SFinite μ] [SFinite ν] [SFinite π] :
    ((μ.prod ν).prod π).map (fun z : (A×B)×D => ((z.1.1,z.2),z.1.2)) = (μ.prod π).prod ν := by
  have h : ((μ.prod ν).prod π).map (fun z : (A×B)×D => ((z.1.1,z.2),z.1.2)) =
      (((μ.prod ν).prod π).map MeasurableEquiv.prodAssoc).map
        ((MeasurableEquiv.prodAssoc : (A×D)×B ≃ᵐ A×(D×B)).symm ∘ Prod.map id Prod.swap) := by
    rw [Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable]
    rfl
  rw [h,Measure.prodAssoc_prod,←Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (measurable_id.prodMap measurable_swap),←Measure.map_prod_map _ _ measurable_id measurable_swap,
    Measure.map_id,Measure.prod_swap,←Measure.prodAssoc_prod,MeasurableEquiv.map_symm_map]



lemma measurable_residualLabelObservation {d r : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (residualLabelObservation (d:=d) (r:=r) (C:=C)) := by
  unfold residualLabelObservation label
  fun_prop

instance residualLabelLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    IsProbabilityMeasure (residualLabelLaw P r) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_residualLabelObservation.aemeasurable).mpr inferInstance

lemma residualLabelLaw_fresh {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    residualLabelLaw (Γ.prod (stdGaussian (Vector d))) r =
      scalarObservationLaw (residualLaw Γ r) := by
  unfold scalarObservationLaw residualLaw
  have he : ((Γ.prod (gaussianRows r d)).map residualObservation).prod (stdGaussian (Vector d)) =
      ((Γ.prod (gaussianRows r d)).prod (stdGaussian (Vector d))).map
        (Prod.map residualObservation id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map
      (Γ.prod (gaussianRows r d)) (stdGaussian (Vector d)) measurable_residualObservation measurable_id
  rw [he,←prod_map_swap23 Γ (stdGaussian (Vector d)) (gaussianRows r d),
    Measure.map_map (measurable_residualObservation.prodMap measurable_id) (by fun_prop),
    Measure.map_map measurable_scalarObservation
      ((measurable_residualObservation.prodMap measurable_id).comp (by fun_prop))]
  rfl

lemma klDiv_prod_same {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure B) [IsProbabilityMeasure π] : klDiv (μ.prod π) (ν.prod π) = klDiv μ ν := by
  rw [←Measure.compProd_const,←Measure.compProd_const]
  exact klDiv_compProd_left _ _ _

lemma residualLabelLaw_kl_le {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    klDiv (residualLabelLaw P r) (scalarObservationLaw (residualLaw P.fst r)) ≤
      klDiv P (P.fst.prod (stdGaussian (Vector d))) := by
  rw [←residualLabelLaw_fresh P.fst r]
  exact (klDiv_map_le _ _ measurable_residualLabelObservation).trans_eq
    (klDiv_prod_same _ _ _)

lemma measurable_residualExact {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    Measurable (residualExact (r:=r) Γ) := by
  exact ((measurable_scalarDensity (scalarProjectionKernel (residualLaw Γ r).condKernel)).comp
    measurable_residualLabelObservation).div ((measurable_residualScale Γ).comp
      (measurable_fst.fst.prodMk measurable_snd))

lemma residualExact_finite {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (w : ((C×Sphere d)×Vector d)×Rows r d) : residualExact Γ w ≠ ∞ := by
  exact ENNReal.div_ne_top (scalarDensity_finite _ _)
    (ne_of_gt (lt_of_lt_of_le (by norm_num) (residualScale_lower Γ w.1.1 w.2)))

lemma residualCube_ae_limit_actual {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P]
    (hKL : klDiv P (P.fst.prod (stdGaussian (Vector d))) ≠ ∞)
    (href : conditionalReferenceKL (scalarObservationLaw (residualLaw P.fst r)) (gaussianReal 0 1) ≠ ∞) :
    ∀ᵐ w ∂P.prod (gaussianRows r d), Tendsto
      (fun n : ℕ => residualCube P.fst (1/(n:ℝ)) w) atTop (𝓝 (residualExact P.fst w)) := by
  have hk := ne_top_of_le_ne_top hKL (residualLabelLaw_kl_le P r)
  have ha := (klDiv_ne_top_iff.mp hk).1
  have ht := ha.ae_le (scalarObservationLaw_ae_limit (residualLaw P.fst r) href)
  have hh := ae_of_ae_map measurable_residualLabelObservation.aemeasurable ht
  filter_upwards [hh] with w hw
  have hd := ENNReal.Tendsto.div_const hw (Or.inr
    (ne_of_gt (lt_of_lt_of_le (by norm_num) (residualScale_lower P.fst w.1.1 w.2))))
  convert hd using 1
  · funext n
    dsimp only [residualLabelObservation,Prod.fst,Prod.snd]
    rw [scalarCube_projection]
    rfl
  · rfl

lemma residualCube_log_bound {d r q : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P]
    (hKL : klDiv P (P.fst.prod (stdGaussian (Vector d))) ≠ ∞)
    (hr : r ≤ d) (hd : d ≤ 8*r) (hq : 1 ≤ q) (hqr : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (hfin : ∀ᵐ z ∂residualLaw P.fst r, reciprocalScale ((residualLaw P.fst r).condKernel z.1) z.2 ≠ ∞)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ w, ENNReal.ofReal (Real.log (1+(residualCube P.fst δ w).toReal)) ∂P.prod (gaussianRows r d) ≤
      ENNReal.ofReal ((klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal / q +
        Real.log (1+5*kernelSmallBallConstant)) := by
  have hc : 0 ≤ 5*kernelSmallBallConstant := by
    have := kernelSmallBallConstant_ge_two
    linarith
  simpa only [integral_const,probReal_univ,one_smul] using mixed_entropy_log_bound_ae P
    (stdGaussian (Vector d)) (gaussianRows r d) hKL (residualCube P.fst δ)
    (measurable_residualCube P.fst δ) (residualCube_finite P.fst δ) (residualCube_integral_finite P.fst δ)
    (fun _ => 5*kernelSmallBallConstant) measurable_const (fun _=>hc) (integrable_const _) hq
    (residualCube_moment P.fst hr hd hqr hmargin hfin hδ)

lemma residualExact_log_bound {d r q : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P]
    (hKL : klDiv P (P.fst.prod (stdGaussian (Vector d))) ≠ ∞)
    (hr : r ≤ d) (hd : d ≤ 8*r) (hq : 1 ≤ q) (hqr : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (hfin : ∀ᵐ z ∂residualLaw P.fst r, reciprocalScale ((residualLaw P.fst r).condKernel z.1) z.2 ≠ ∞)
    (href : conditionalReferenceKL (scalarObservationLaw (residualLaw P.fst r)) (gaussianReal 0 1) ≠ ∞) :
    Integrable (fun w => Real.log (1+(residualExact P.fst w).toReal)) (P.prod (gaussianRows r d)) ∧
    (∫ w, Real.log (1+(residualExact P.fst w).toReal) ∂P.prod (gaussianRows r d)) ≤
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal / q +
        Real.log (1+5*kernelSmallBallConstant) := by
  have hR : 0 ≤ (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal / q +
      Real.log (1+5*kernelSmallBallConstant) := by
    apply add_nonneg (by positivity)
    apply Real.log_nonneg
    have := kernelSmallBallConstant_ge_two
    linarith
  apply (log_bound_consequences _ _ (measurable_residualExact P.fst) _ hR ?_).1
  apply log_lintegral_bound_of_ae_tendsto _ (fun n => residualCube P.fst (1/(n:ℝ)))
    (residualExact P.fst) (fun n => measurable_residualCube P.fst _) (residualExact_finite P.fst)
    (residualCube_ae_limit_actual P hKL href)
  intro n hn
  exact residualCube_log_bound P hKL hr hd hq hqr hmargin hfin (by positivity)




lemma klDiv_map_bound_of_llr_le {A D : Type*} [MeasurableSpace A] [MeasurableSpace D]
    (P : Measure A) [IsProbabilityMeasure P] (R : Measure D) [IsProbabilityMeasure R]
    (f : A → D) (hf : Measurable f) (ha : P.map f ≪ R)
    (u : A → ℝ) (hu : Integrable u P)
    (hb : ∀ᵐ w ∂P, llr (P.map f) R (f w) ≤ u w) :
    klDiv (P.map f) R ≠ ∞ ∧ (klDiv (P.map f) R).toReal ≤ ∫ w, u w ∂P := by
  let : IsProbabilityMeasure (P.map f) := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hri : Integrable (fun x => (R.rnDeriv (P.map f) x).toReal) (P.map f) := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ:=R) (ν:=P.map f) (s:=Set.univ) (measure_ne_top _ _))
  have hri' : Integrable (fun w => (R.rnDeriv (P.map f) (f w)).toReal) P :=
    (integrable_map_measure (Measurable.ennreal_toReal (Measure.measurable_rnDeriv _ _)).aestronglyMeasurable
      hf.aemeasurable).mp hri
  have hlo : ∀ᵐ w ∂P, -(R.rnDeriv (P.map f) (f w)).toReal ≤ llr (P.map f) R (f w) := by
    filter_upwards [ae_of_ae_map hf.aemeasurable (exp_neg_llr ha)] with w hw
    have ht := Real.add_one_le_exp (-llr (P.map f) R (f w))
    rw [hw] at ht
    linarith
  have hi : Integrable (fun w => llr (P.map f) R (f w)) P := integrable_of_le_of_le
    ((measurable_llr _ _).comp hf).aestronglyMeasurable hlo hb hri'.neg hu
  have hi' : Integrable (llr (P.map f) R) (P.map f) :=
    (integrable_map_measure (measurable_llr _ _).aestronglyMeasurable hf.aemeasurable).mpr hi
  refine ⟨klDiv_ne_top ha hi',?_⟩
  rw [toReal_klDiv_of_measure_eq ha (by simp),integral_map hf.aemeasurable
    (measurable_llr _ _).aestronglyMeasurable]
  exact integral_mono_ae hi hu hb

lemma klDiv_map_cross_bound {A D : Type*} [MeasurableSpace A] [MeasurableSpace D]
    (P : Measure A) [IsProbabilityMeasure P] (Q R : Measure D)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (f : A → D) (hf : Measurable f) (hPQ : klDiv (P.map f) Q ≠ ∞) (hQR : Q ≪ R)
    (u : A → ℝ) (hu : Integrable u P)
    (hb : ∀ᵐ w ∂P, llr Q R (f w) ≤ u w) :
    klDiv (P.map f) R ≠ ∞ ∧ (klDiv (P.map f) R).toReal ≤
      (klDiv (P.map f) Q).toReal + ∫ w, u w ∂P := by
  let : IsProbabilityMeasure (P.map f) := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  obtain ⟨ha,hi⟩ := klDiv_ne_top_iff.mp hPQ
  have hi' : Integrable (fun w => llr (P.map f) Q (f w)) P :=
    (integrable_map_measure (measurable_llr _ _).aestronglyMeasurable hf.aemeasurable).mp hi
  have he := ae_of_ae_map hf.aemeasurable (llr_chain_ae (P.map f) Q R ha hQR)
  have hb' : ∀ᵐ w ∂P, llr (P.map f) R (f w) ≤ llr (P.map f) Q (f w)+u w := by
    filter_upwards [he,hb] with w hw hb
    rw [hw]
    linarith
  obtain ⟨hfin,hbound⟩ := klDiv_map_bound_of_llr_le P R f hf (ha.trans hQR) _ (hi'.add hu) hb'
  refine ⟨hfin,?_⟩
  simp only [Pi.add_apply] at hbound
  rw [integral_add hi' hu,←integral_map hf.aemeasurable (measurable_llr _ _).aestronglyMeasurable,
    ←toReal_klDiv_of_measure_eq ha (by simp)] at hbound
  exact hbound



lemma residualSignalLaw {d r : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] :
    (P.prod (gaussianRows r d)).map
      (fun w => residualObservation (w.1.1,w.2)) = residualLaw P.fst r := by
  unfold residualLaw
  have he : (P.fst.prod (gaussianRows r d)) =
      (P.prod (gaussianRows r d)).map (Prod.map Prod.fst id) := by
    simpa only [Measure.map_id,Measure.fst] using Measure.map_prod_map P (gaussianRows r d) measurable_fst measurable_id
  rw [he,Measure.map_map measurable_residualObservation (measurable_fst.prodMap measurable_id)]
  rfl

lemma density_positive_ae {A : Type*} [MeasurableSpace A]
    (Q Λ : Measure A) [IsProbabilityMeasure Q] [SigmaFinite Λ]
    (p : A → ℝ≥0∞) (hp : Measurable p) (he : Λ.withDensity p = Q) :
    ∀ᵐ a ∂Q, 0 < p a := by
  have ha : Q ≪ Λ := by rw [←he]; exact withDensity_absolutelyContinuous _ _
  have hr : Q.rnDeriv Λ =ᵐ[Λ] p := by rw [←he]; exact Measure.rnDeriv_withDensity _ hp
  filter_upwards [ha.ae_le hr,Measure.rnDeriv_pos ha] with a h1 h2
  rwa [←h1]

lemma log_le_log_scale_add {p A : ℝ≥0∞} (hp : 0 < p) (hpt : p ≠ ∞)
    (hA : 0 < A) (hAt : A ≠ ∞) :
    Real.log p.toReal ≤ Real.log A.toReal+Real.log (1+(p/A).toReal) := by
  have hp' := ENNReal.toReal_pos hp.ne' hpt
  have hA' := ENNReal.toReal_pos hA.ne' hAt
  rw [ENNReal.toReal_div]
  have hl := Real.log_le_log (div_pos hp' hA') (le_add_of_nonneg_left (show (0:ℝ)≤1 by norm_num) : p.toReal/A.toReal ≤ 1+p.toReal/A.toReal)
  rw [Real.log_div hp'.ne' hA'.ne'] at hl
  linarith

lemma residual_reference_bound {d r q : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P]
    (hKL : klDiv P (P.fst.prod (stdGaussian (Vector d))) ≠ ∞)
    (hr : r ≤ d) (hd : d ≤ 8*r) (hq : 1 ≤ q) (hqr : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (hfresh : conditionalReferenceKL (scalarObservationLaw (residualLaw P.fst r)) (gaussianReal 0 1) ≠ ∞)
    (hnext : conditionalReferenceKL (cauchyObservationLaw (residualLaw P.fst r)) (gaussianReal 0 1) ≠ ∞)
    (hlabel : (residualLabelLaw P r).snd = gaussianReal 0 1) :
    klDiv (residualLabelLaw P r)
      ((scalarObservationLaw (residualLaw P.fst r)).fst.prod (gaussianReal 0 1)) ≠ ∞ ∧
    (klDiv (residualLabelLaw P r)
      ((scalarObservationLaw (residualLaw P.fst r)).fst.prod (gaussianReal 0 1))).toReal ≤
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal +
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal / q + hybridRowConstant +
      (conditionalReferenceKL (cauchyObservationLaw (residualLaw P.fst r)) (gaussianReal 0 1)).toReal := by
  let Γ := residualLaw P.fst r
  let M := P.prod (gaussianRows r d)
  let Q := scalarObservationLaw Γ
  let R := Q.fst.prod (gaussianReal 0 1)
  let Λ := Q.fst.prod (volume : Measure ℝ)
  let p : ((C×(Rows r d×(Fin r→ℝ)))×Vector d)×ℝ → ℝ≥0∞ :=
    fun z => scalarDensity (scalarProjectionKernel Γ.condKernel z.1) z.2
  have hp : Measurable p := measurable_scalarDensity _
  have hpQ : Λ.withDensity p = Q := scalarObservationLaw_density Γ hfresh
  have hgR : Λ.withDensity (fun z => ENNReal.ofReal (gaussianPDFReal 0 1 z.2)) = R := by
    rw [show (fun z : ((C×(Rows r d×(Fin r→ℝ)))×Vector d)×ℝ =>
      ENNReal.ofReal (gaussianPDFReal 0 1 z.2)) = (fun z => gaussianPDF 0 1 z.2) from rfl,
      ←prod_withDensity_right (measurable_gaussianPDF 0 1)]
    change Q.fst.prod _ = Q.fst.prod (gaussianReal 0 1)
    rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1:ℝ≥0) ≠ 0)]
  have hdens := llr_of_two_densities Q R Λ p hp hpQ
    (fun z => gaussianPDFReal 0 1 z.2) (by fun_prop)
    (fun z => gaussianPDFReal_pos _ _ _ (by norm_num)) hgR
  have hobsKL := ne_top_of_le_ne_top hKL (residualLabelLaw_kl_le P r)
  have hobsAC := (klDiv_ne_top_iff.mp hobsKL).1
  have hpos := ae_of_ae_map measurable_residualLabelObservation.aemeasurable
    (hobsAC.ae_le (density_positive_ae Q Λ p hp hpQ))
  have hllr := ae_of_ae_map measurable_residualLabelObservation.aemeasurable (hobsAC.ae_le hdens.2)
  obtain ⟨hAfinite,hAi,hAb⟩ := reciprocalScale_experiment_bound Γ Γ.condKernel hnext
  have hmap : M.map (fun w => residualObservation (w.1.1,w.2)) = Γ := residualSignalLaw P
  have hmapm : Measurable (fun w : ((C×Sphere d)×Vector d)×Rows r d => residualObservation (w.1.1,w.2)) :=
    measurable_residualObservation.comp (measurable_fst.fst.prodMk measurable_snd)
  have hAm : Measurable (fun z : (C×(Rows r d×(Fin r→ℝ)))×Sphere d =>
      Real.log (reciprocalScale (Γ.condKernel z.1) z.2).toReal) :=
    (reciprocalScale_kernel_measurable Γ.condKernel).ennreal_toReal.log
  have hAi' : Integrable (fun w => Real.log (residualScale P.fst w.1.1 w.2).toReal) M := by
    exact (integrable_map_measure hAm.aestronglyMeasurable hmapm.aemeasurable).mp (hmap.symm ▸ hAi)
  have hAb' : (∫ w, Real.log (residualScale P.fst w.1.1 w.2).toReal ∂M) ≤
      cauchyTiltConstant-standardGaussianEntropy+
        (conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1)).toReal := by
    have he := integral_map (μ:=M) hmapm.aemeasurable hAm.aestronglyMeasurable
    rw [hmap] at he
    exact he ▸ hAb
  have hAf : ∀ᵐ w ∂M, residualScale P.fst w.1.1 w.2 ≠ ∞ := by
    have ht : ∀ᵐ z ∂M.map (fun w => residualObservation (w.1.1,w.2)),
        reciprocalScale (Γ.condKernel z.1) z.2 ≠ ∞ := by rwa [hmap]
    exact ae_of_ae_map hmapm.aemeasurable ht
  obtain ⟨hNi,hNb⟩ := residualExact_log_bound P hKL hr hd hq hqr hmargin hAfinite hfresh
  obtain ⟨hgi,hgb⟩ := standardGaussian_cross_entropy (residualLabelLaw P r) hlabel
  have hgm : Measurable (fun z : ((C×(Rows r d×(Fin r→ℝ)))×Vector d)×ℝ =>
      Real.log (gaussianPDFReal 0 1 z.2)) := by fun_prop
  have hgi' : Integrable (fun w => Real.log (gaussianPDFReal 0 1 (residualLabelObservation w).2)) M :=
    (integrable_map_measure hgm.aestronglyMeasurable measurable_residualLabelObservation.aemeasurable).mp hgi
  let u : ((C×Sphere d)×Vector d)×Rows r d → ℝ := fun w =>
    Real.log (residualScale P.fst w.1.1 w.2).toReal + Real.log (1+(residualExact P.fst w).toReal) -
      Real.log (gaussianPDFReal 0 1 (residualLabelObservation w).2)
  have hui : Integrable u M := (hAi'.add hNi).sub hgi'
  have hu : ∀ᵐ w ∂M, llr Q R (residualLabelObservation w) ≤ u w := by
    filter_upwards [hllr,hpos,hAf] with w hl hp0 hAt
    rw [hl]
    have ht := log_le_log_scale_add hp0 (scalarDensity_finite _ _)
      (lt_of_lt_of_le (by norm_num) (residualScale_lower P.fst w.1.1 w.2)) hAt
    exact sub_le_sub_right ht _
  obtain ⟨hfin,hbound⟩ := klDiv_map_cross_bound M Q R residualLabelObservation
    measurable_residualLabelObservation hobsKL hdens.1 u hui hu
  refine ⟨hfin,?_⟩
  have hK : (klDiv (residualLabelLaw P r) Q).toReal ≤
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal :=
    ENNReal.toReal_mono hKL (residualLabelLaw_kl_le P r)
  have hgb' : -(∫ w, Real.log (gaussianPDFReal 0 1 (residualLabelObservation w).2) ∂M) = standardGaussianEntropy := by
    rw [←integral_map measurable_residualLabelObservation.aemeasurable hgm.aestronglyMeasurable]
    simpa only [integral_neg,residualLabelLaw,M] using hgb
  dsimp only [u] at hbound
  have hsum : Integrable (fun w => Real.log (residualScale P.fst w.1.1 w.2).toReal +
      Real.log (1+(residualExact P.fst w).toReal)) M := hAi'.add hNi
  rw [integral_sub hsum hgi',integral_add hAi' hNi] at hbound
  change _ ≤ _ + _ + (cauchyTiltConstant+Real.log (1+5*kernelSmallBallConstant)) + _
  dsimp only [M,Q,R,Γ,residualLabelLaw] at hbound hK hAb' hNb hgb' ⊢
  linarith



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


lemma ownObservations_append {i r d : ℕ} (X : Rows i d) (A : Rows r d) (s : Sphere d) :
    ownObservations (Fin.append X A) s = Fin.append (ownObservations X s) (ownObservations A s) := by
  funext j
  induction j using Fin.addCases <;> simp [ownObservations,pairObservation,label]

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

lemma arrayResidualLaw_eq {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) :
    arrayResidualLaw Γ r = (residualLaw Γ r).map
      (Prod.map (Prod.map id (observationEquiv r d)) id) := by
  rw [residualLaw,Measure.map_map
    ((measurable_id.prodMap (observationEquiv r d).measurable).prodMap measurable_id)
    measurable_residualObservation]
  rfl

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

lemma freshSlope_eq {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    freshSlope Γ r = conditionalReferenceKL (scalarObservationLaw (residualLaw Γ r)) (gaussianReal 0 1) := by
  rw [freshSlope,arrayResidualLaw_eq,scalarObservationLaw_context _ _
    (measurable_id.prodMap (observationEquiv r d).measurable)]
  exact conditionalReferenceKL_context_equiv _ _
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl C) (observationEquiv r d)).prodCongr
      (MeasurableEquiv.refl (Vector d)))

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

lemma gaussianRows_one (d : ℕ) :
    (gaussianRows 1 d).map (MeasurableEquiv.funUnique (Fin 1) (Vector d)) = stdGaussian (Vector d) :=
  (measurePreserving_funUnique (stdGaussian (Vector d)) (Fin 1)).map_eq

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

lemma scalarReference_context {d : ℕ} {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (e : C ≃ᵐ D) :
    conditionalReferenceKL (scalarObservationLaw (Γ.map (Prod.map e id))) (gaussianReal 0 1) =
      conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) := by
  rw [scalarObservationLaw_context _ _ e.measurable]
  exact conditionalReferenceKL_context_equiv _ _ (e.prodCongr (MeasurableEquiv.refl (Vector d)))

lemma freshSlope_succ {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    freshSlope Γ (r+1) = conditionalReferenceKL
      (scalarObservationLaw (singleSignalLaw ((arrayResidualLaw Γ r).prod (stdGaussian (Vector d)))))
      (gaussianReal 0 1) := by
  let e : ((C×Observations r d)×Observations 1 d) ≃ᵐ C×Observations (r+1) d :=
    MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.refl C).prodCongr (appendEquiv (Vector d×ℝ) r 1))
  have he : arrayResidualLaw Γ (r+1) = (arrayResidualLaw (arrayResidualLaw Γ r) 1).map (Prod.map e id) :=
    arrayResidualLaw_append Γ r 1
  rw [freshSlope,he,scalarReference_context,singleSignalLaw_fresh]
  exact (scalarReference_context _ ((MeasurableEquiv.refl (C×Observations r d)).prodCongr
    (MeasurableEquiv.funUnique (Fin 1) (Vector d×ℝ)))).symm



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


lemma cauchyObservationLaw_single {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    cauchyObservationLaw Γ =
      (scalarObservationLaw (singleSignalLaw (Γ.prod (stdGaussian (Vector d))))).map
        (Prod.map (exchangeMiddle C (Vector d) ℝ (Vector d)) id) := by
  rw [scalarObservationLaw,singleSignalLaw,
    show ((Γ.prod (stdGaussian (Vector d))).map singleResidualObservation).prod
        (stdGaussian (Vector d)) =
        ((Γ.prod (stdGaussian (Vector d))).prod (stdGaussian (Vector d))).map
          (Prod.map singleResidualObservation id) by
      rw [←Measure.map_prod_map _ _ measurable_singleResidualObservation measurable_id,Measure.map_id],
    Measure.map_map measurable_scalarObservation (measurable_singleResidualObservation.prodMap measurable_id),
    Measure.map_map ((exchangeMiddle C (Vector d) ℝ (Vector d)).measurable.prodMap measurable_id)
      (measurable_scalarObservation.comp (measurable_singleResidualObservation.prodMap measurable_id))]
  rw [cauchyObservationLaw,show gaussianVectorPair d = (stdGaussian (Vector d)).prod (stdGaussian (Vector d)) from rfl,
    ←Measure.prodAssoc_prod,Measure.map_map measurable_cauchyObservation MeasurableEquiv.prodAssoc.measurable]
  rfl

lemma cauchyReference_single {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1) =
      conditionalReferenceKL
        (scalarObservationLaw (singleSignalLaw (Γ.prod (stdGaussian (Vector d))))) (gaussianReal 0 1) := by
  rw [cauchyObservationLaw_single,conditionalReferenceKL_context_equiv]

lemma cauchyReference_context {d : ℕ} {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (e : C ≃ᵐ D) :
    conditionalReferenceKL (cauchyObservationLaw (Γ.map (Prod.map e id))) (gaussianReal 0 1) =
      conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1) := by
  have he : cauchyObservationLaw (Γ.map (Prod.map e id)) =
      (cauchyObservationLaw Γ).map (Prod.map
        ((e.prodCongr (MeasurableEquiv.refl (Vector d×Vector d))).prodCongr (MeasurableEquiv.refl ℝ)) id) := by
    rw [cauchyObservationLaw,show (Γ.map (Prod.map e id)).prod (gaussianVectorPair d) =
      (Γ.prod (gaussianVectorPair d)).map (Prod.map (Prod.map e id) id) by
        rw [←Measure.map_prod_map _ _ (e.measurable.prodMap measurable_id) measurable_id,Measure.map_id],
      Measure.map_map measurable_cauchyObservation ((e.measurable.prodMap measurable_id).prodMap measurable_id),
      cauchyObservationLaw,Measure.map_map (by fun_prop) measurable_cauchyObservation]
    rfl
  rw [he,conditionalReferenceKL_context_equiv]

lemma freshSlope_next_residual {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    freshSlope Γ (r+1) =
      conditionalReferenceKL (cauchyObservationLaw (residualLaw Γ r)) (gaussianReal 0 1) := by
  rw [freshSlope_succ,←cauchyReference_single,arrayResidualLaw_eq]
  exact cauchyReference_context _ ((MeasurableEquiv.refl C).prodCongr (observationEquiv r d))

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

lemma liftActualLaw_fst {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    (liftActualLaw P r).fst = arrayResidualLaw P.fst r := by
  rw [liftActualLaw,Measure.fst,Measure.map_map measurable_fst measurable_liftActualObservation,
    arrayResidualLaw,show P.fst.prod (gaussianRows r d) =
      (P.prod (gaussianRows r d)).map (Prod.map Prod.fst id) by
        rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]; rfl,
    Measure.map_map measurable_arrayResidualObservation (measurable_fst.prodMap measurable_id)]
  rfl

attribute [fun_prop] measurable_ownObservations


lemma residualLabelLaw_to_single {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) (r : ℕ) :
    (residualLabelLaw P r).map
      (MeasurableEquiv.prodAssoc.trans
        (((MeasurableEquiv.refl C).prodCongr (observationEquiv r d)).prodCongr
          (MeasurableEquiv.refl (Vector d×ℝ)))) =
      singleObservationLaw (liftActualLaw P r) := by
  rw [residualLabelLaw,Measure.map_map (MeasurableEquiv.measurable _) measurable_residualLabelObservation,
    singleObservationLaw_eq,liftActualLaw,Measure.map_map (by fun_prop) measurable_liftActualObservation]
  rfl

lemma scalarObservationLaw_fst_direct {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [SFinite Γ] :
    (scalarObservationLaw Γ).fst = Γ.fst.prod (stdGaussian (Vector d)) := by
  rw [scalarObservationLaw,Measure.fst,Measure.map_map measurable_fst measurable_scalarObservation]
  change (Γ.prod (stdGaussian (Vector d))).map (Prod.map Prod.fst id) = _
  rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
  rfl

lemma singleReference_lift_eq {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    singleReference (liftActualLaw P r) = klDiv (residualLabelLaw P r)
      ((scalarObservationLaw (residualLaw P.fst r)).fst.prod (gaussianReal 0 1)) := by
  let e := (MeasurableEquiv.refl C).prodCongr (observationEquiv r d)
  let e' := MeasurableEquiv.prodAssoc.trans (e.prodCongr (MeasurableEquiv.refl (Vector d×ℝ)))
  have hbase : ((residualLaw P.fst r).fst).map e = freshArrayLaw P.fst r := by
    rw [freshArrayLaw,arrayResidualLaw_eq]
    simp only [Measure.fst]
    rw [Measure.map_map e.measurable measurable_fst,
      Measure.map_map measurable_fst ((measurable_id.prodMap (observationEquiv r d).measurable).prodMap measurable_id)]
    rfl
  have hfst : (singleObservationLaw (liftActualLaw P r)).fst = freshArrayLaw P.fst r := by
    rw [singleObservationLaw_fst,liftActualLaw_fst]; rfl
  have href : ((scalarObservationLaw (residualLaw P.fst r)).fst.prod (gaussianReal 0 1)).map e' =
      (freshArrayLaw P.fst r).prod (gaussianObservation d) := by
    rw [scalarObservationLaw_fst_direct]
    change (((residualLaw P.fst r).fst.prod (stdGaussian (Vector d))).prod (gaussianReal 0 1)).map
      (e.prodCongr (MeasurableEquiv.refl (Vector d×ℝ)) ∘ MeasurableEquiv.prodAssoc) = _
    rw [←Measure.map_map (e.prodCongr (MeasurableEquiv.refl (Vector d×ℝ))).measurable
      MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod]
    change (((residualLaw P.fst r).fst).prod (gaussianObservation d)).map (Prod.map e id) = _
    rw [←Measure.map_prod_map _ _ e.measurable measurable_id,Measure.map_id,hbase]
  rw [singleReference,conditionalReferenceKL,hfst,
    ←residualLabelLaw_to_single P r,←href]
  exact klDiv_map_equiv _ _ e'

lemma actual_fresh_row_bound_oai {d r q : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P]
    (hKL : klDiv P (P.fst.prod (stdGaussian (Vector d))) ≠ ∞)
    (hr : r ≤ d) (hd : d ≤ 8*r) (hq : 1 ≤ q) (hqr : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (hfresh : freshSlope P.fst r ≠ ∞) (hnext : freshSlope P.fst (r+1) ≠ ∞)
    (hlabel : (residualLabelLaw P r).snd = gaussianReal 0 1) :
    singleReference (liftActualLaw P r) ≠ ∞ ∧
    (singleReference (liftActualLaw P r)).toReal ≤
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal +
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal / q + hybridRowConstant +
      (freshSlope P.fst (r+1)).toReal := by
  rw [singleReference_lift_eq,freshSlope_next_residual] at ⊢
  rw [freshSlope_eq] at hfresh
  rw [freshSlope_next_residual] at hnext
  exact residual_reference_bound P hKL hr hd hq hqr hmargin hfresh hnext hlabel




end CurrentProjection

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CurrentProjection.actual_fresh_row_bound_oai.{u_1} := @OAI.CurrentProjection.actual_fresh_row_bound_oai.{u_1}
