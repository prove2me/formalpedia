-- Prove2me | solution 1 for OAI.CurrentProjection.mixedMomentMain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T23:55:38.073995+00:00
-- url     : https://prove2.me/submissions/9d8bf706-0e29-446f-b925-46b0e4c1020b

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

end AppendPi



lemma cubeAverage_scale_lower {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d)
    (y : Fin k → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ENNReal.ofReal ((a/b)^k) * cubeAverage ρ G y a ≤ cubeAverage ρ G y b := by
  have hb : 0 < b := ha.trans_le hab
  unfold cubeAverage
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  have he : a / b * (2*a)⁻¹ = (2*b)⁻¹ := by field_simp
  rw [he]
  exact mul_le_mul' le_rfl (measure_mono (fun u hu i => (hu i).trans hab))

lemma cubeAverage_scale_upper {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d)
    (y : Fin k → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    cubeAverage ρ G y a ≤ ENNReal.ofReal ((b/a)^k) * cubeAverage ρ G y b := by
  have hb : 0 < b := ha.trans_le hab
  unfold cubeAverage
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  have he : b / a * (2*b)⁻¹ = (2*a)⁻¹ := by field_simp
  rw [he]
  exact mul_le_mul' le_rfl (measure_mono (fun u hu i => (hu i).trans hab))

lemma tendsto_cube_of_recip_nat {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d)
    (y : Fin k → ℝ) {L : ℝ≥0∞}
    (h : Tendsto (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) atTop (𝓝 L)) :
    Tendsto (fun δ : ℝ => cubeAverage ρ G y δ) (𝓝[>] 0) (𝓝 L) := by
  have hj : Tendsto (fun t : ℝ => Nat.floor t) atTop atTop := tendsto_nat_floor_atTop
  have hj1 : Tendsto (fun t : ℝ => Nat.floor t + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hj
  have hratio : Tendsto (fun t : ℝ => (Nat.floor t:ℝ)/t) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop
  have hratio1 : Tendsto (fun t : ℝ => ((Nat.floor t:ℝ)+1)/t) atTop (𝓝 1) := by
    have hz : Tendsto (fun t : ℝ => (1:ℝ)/t) atTop (𝓝 (0:ℝ)) := by
      simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 (0:ℝ)))
    have hh := hratio.add hz
    simpa only [add_zero, ← add_div] using hh
  have hlo : Tendsto (fun t : ℝ => ENNReal.ofReal ((t/((Nat.floor t:ℝ)+1))^k) *
      cubeAverage ρ G y (1/(Nat.floor t+1:ℕ))) atTop (𝓝 L) := by
    have hh := (hratio1.inv₀ (by norm_num)).pow k
    simp only [inv_div, inv_one, one_pow] at hh
    simpa only [ENNReal.ofReal_one, one_mul, Nat.cast_add, Nat.cast_one, Function.comp_def] using
      ENNReal.Tendsto.mul ((ENNReal.continuous_ofReal.tendsto 1).comp hh)
        (Or.inl (by simp)) (h.comp hj1) (Or.inr (by simp))
  have hhi : Tendsto (fun t : ℝ => ENNReal.ofReal ((t/(Nat.floor t:ℝ))^k) *
      cubeAverage ρ G y (1/(Nat.floor t:ℝ))) atTop (𝓝 L) := by
    have hh := (hratio.inv₀ (by norm_num)).pow k
    simp only [inv_div, inv_one, one_pow] at hh
    simpa only [ENNReal.ofReal_one, one_mul, Function.comp_def] using
      ENNReal.Tendsto.mul ((ENNReal.continuous_ofReal.tendsto 1).comp hh)
        (Or.inl (by simp)) (h.comp hj) (Or.inr (by simp))
  have ht : Tendsto (fun t : ℝ => cubeAverage ρ G y (1/t)) atTop (𝓝 L) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      have ht0 : 0 < t := by linarith
      have hn : 0 < (Nat.floor t:ℝ) := by exact_mod_cast (Nat.floor_pos.mpr ht)
      have hn1 : 0 < (Nat.floor t:ℝ)+1 := by positivity
      have hlt : t < (Nat.floor t:ℝ)+1 := Nat.lt_floor_add_one t
      have hlow := cubeAverage_scale_lower ρ G y (one_div_pos.mpr hn1)
        ((one_div_le_one_div hn1 ht0).mpr hlt.le)
      simpa only [Nat.cast_add, Nat.cast_one, one_div, inv_div_inv] using hlow
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      have ht0 : 0 < t := by linarith
      have hn : 0 < (Nat.floor t:ℝ) := by exact_mod_cast (Nat.floor_pos.mpr ht)
      have hle : (Nat.floor t:ℝ) ≤ t := Nat.floor_le ht0.le
      have hupp := cubeAverage_scale_upper ρ G y (one_div_pos.mpr ht0)
        ((one_div_le_one_div ht0 hn).mpr hle)
      simpa only [one_div, inv_div_inv] using hupp
  simpa only [Function.comp_def, one_div, inv_inv] using ht.comp tendsto_inv_nhdsGT_zero







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


theorem mixedMomentMain_oai : MixedMomentMain := by
  refine ⟨9, by norm_num, ?_⟩
  intro d m r q hdim ρ hρ B D hB hD hBρ hDρ
  let := hρ
  refine ⟨fun s δ hδ => mixed_cube_moment hdim ρ B D hB hD hBρ hDρ s δ hδ, ?_⟩
  intro _hρσ
  have ha : ∀ᵐ (s : Sphere d) ∂ρ,
      (∀ᵐ G ∂gaussianRows (m+r) d,
        Tendsto (fun j : ℕ => cubeAverage ρ G (label G (s:Vector d)) (1/(j:ℝ)))
          atTop (𝓝 (exactDensity ρ G (label G (s:Vector d))))) ∧
      (∀ᵐ G ∂gaussianRows (m+r) d,
        0 < exactDensity ρ G (label G (s:Vector d)) ∧
        exactDensity ρ G (label G (s:Vector d)) < ∞) ∧
      (∀ᵐ G ∂gaussianRows (m+r) d,
        exactDensity ρ G (label G (s:Vector d)) =
          extendedCubeDensity ρ G (label G (s:Vector d))) := by
    filter_upwards [ae_target_cube_limit (k:=m+r) ρ] with s hs
    have hfin := extended_ae_finite hdim ρ B D hB hD hBρ hDρ s
    have hall : ∀ᵐ G ∂gaussianRows (m+r) d,
        Tendsto (fun j : ℕ => cubeAverage ρ G (label G (s:Vector d)) (1/(j:ℝ)))
          atTop (𝓝 (exactDensity ρ G (label G (s:Vector d)))) ∧
        (0 < exactDensity ρ G (label G (s:Vector d)) ∧
          exactDensity ρ G (label G (s:Vector d)) < ∞) ∧
        exactDensity ρ G (label G (s:Vector d)) =
          extendedCubeDensity ρ G (label G (s:Vector d)) := by
      filter_upwards [hs, hfin] with G hG hGt
      have he := exactDensity_eq_of_tendsto ρ G _ hG.1 hGt.ne
      exact ⟨he.symm ▸ hG.1, he.symm ▸ ⟨hG.2, hGt⟩, he⟩
    exact ⟨hall.mono fun _ h => h.1, hall.mono fun _ h => h.2.1,
      hall.mono fun _ h => h.2.2⟩
  obtain ⟨E, hsub, hE, hEρ⟩ := exists_measurable_superset_of_null (ae_iff.mp ha)
  refine ⟨E, hE, hEρ, ?_⟩
  intro s hs
  have hsa := not_not.mp fun h => hs (hsub h)
  exact ⟨hsa.1.mono (fun G h => tendsto_cube_of_recip_nat ρ G _ h), exact_mixed_moment_of_ae hdim ρ B D hB hD hBρ hDρ s hsa.2.2,
    fun _ => hsa.2.1⟩




end CurrentProjection

end

end OAI
end

theorem solution : type_of% @OAI.CurrentProjection.mixedMomentMain_oai := @OAI.CurrentProjection.mixedMomentMain_oai
