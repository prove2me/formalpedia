-- Prove2me | solution 1 for OAI.CurrentProjection.fiberBlockMain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T23:54:43.21535+00:00
-- url     : https://prove2.me/submissions/a3900988-b158-41fc-a42c-470ebcd44e8d

import Mathlib
import Definitions.Def_GaussianReplacement
import Definitions.Def_OAIQWCP001
import Theorems.Thm_OAI_CurrentProjection_critical_refined_comparison

section
-- module Solutions.OAIQW_CurrentProjection.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
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

lemma rowInformation_refinement {S W X E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] [MeasurableSpace E]
    (P : Measure ((S×W)×X)) [IsProbabilityMeasure P]
    (γ : Measure X) [IsProbabilityMeasure γ] (e : S×W → E) (he : Measurable e) :
    rowInformation (P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))) γ =
      rowInformation P γ := by
  let f : S×W → S×(W×E) := fun sw => (sw.1,(sw.2,e sw))
  let g : S×(W×E) → S×W := fun sw => (sw.1,sw.2.1)
  have hf : Measurable f := measurable_fst.prodMk (measurable_snd.prodMk he)
  have hg : Measurable g := measurable_fst.prodMk measurable_snd.fst
  let T := Prod.map f (id : X → X)
  let U := Prod.map g (id : X → X)
  have hT : Measurable T := hf.prodMap measurable_id
  have hU : Measurable U := hg.prodMap measurable_id
  have hfst : (P.map T).fst = P.fst.map f := by
    simp only [Measure.fst, Measure.map_map measurable_fst hT,
      Measure.map_map hf measurable_fst]
    rfl
  have hRef : (P.map T).fst.prod γ = (P.fst.prod γ).map T := by
    rw [hfst]
    change _ = (P.fst.prod γ).map (Prod.map f id)
    rw [← Measure.map_prod_map P.fst γ hf measurable_id, Measure.map_id]
  change klDiv (P.map T) ((P.map T).fst.prod γ) = klDiv P (P.fst.prod γ)
  rw [hRef]
  apply le_antisymm (klDiv_map_le _ _ hT)
  have hd := klDiv_map_le (P.map T) ((P.fst.prod γ).map T) hU
  have heq : U ∘ T = id := rfl
  simpa only [Measure.map_map hU hT, heq, Measure.map_id] using hd



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

lemma conditionalMutualInformation_le_entropy {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [StandardBorelSpace A] [Nonempty A] [Nonempty B]
    [Countable B] [MeasurableSingletonClass B]
    (P : Measure (Z×(A×B))) [IsProbabilityMeasure P]
    (hH : shannonEntropy (P.map MeasurableEquiv.prodAssoc.symm).snd ≠ ∞) :
    conditionalMutualInformation P ≠ ∞ ∧
      (conditionalMutualInformation P).toReal ≤
        (shannonEntropy (P.map MeasurableEquiv.prodAssoc.symm).snd).toReal := by
  let : IsProbabilityMeasure (P.map MeasurableEquiv.prodAssoc.symm) :=
    Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have h := countable_information_le_entropy (P.map MeasurableEquiv.prodAssoc.symm) hH
  have hle : conditionalMutualInformation P ≤ mutualInformation (P.map MeasurableEquiv.prodAssoc.symm) := by
    rw [mutualInformation_chain P]
    exact le_add_left le_rfl
  exact ⟨ne_top_of_le_ne_top h.1 hle,(ENNReal.toReal_mono h.1 hle).trans h.2⟩

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

lemma conditionalMutualInformation_map_right_le {Z A B C : Type*} [MeasurableSpace Z]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [StandardBorelSpace A] [StandardBorelSpace B] [StandardBorelSpace C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (P : Measure (Z×(A×B))) [IsProbabilityMeasure P] (f : B → C) (hf : Measurable f) :
    conditionalMutualInformation (P.map (Prod.map id (Prod.map id f))) ≤
      conditionalMutualInformation P := by
  let μ := P.fst
  let κ := P.condKernel
  let g : A×B → A×C := Prod.map id f
  have hg : Measurable g := measurable_id.prodMap hf
  let : IsMarkovKernel (κ.map g) := Kernel.IsMarkovKernel.map κ hg
  have hT : Measurable (Prod.map (id : Z → Z) g) := measurable_id.prodMap hg
  have hP : μ ⊗ₘ κ = P := P.disintegrate P.condKernel
  have hmap : P.map (Prod.map id g) = μ ⊗ₘ κ.map g := by
    rw [Measure.compProd_map hg,hP]
  have hfst : (κ.map g).fst = κ.fst := by
    rw [Kernel.fst_eq,←Kernel.map_comp_right _ hg measurable_fst,Kernel.fst_eq]
    rfl
  have hsnd : (κ.map g).snd = κ.snd.map f := by
    rw [Kernel.snd_eq,Kernel.snd_eq,←Kernel.map_comp_right _ hg measurable_snd,
      ←Kernel.map_comp_right _ measurable_snd hf]
    rfl
  have hRef : μ ⊗ₘ ((κ.map g).fst ×ₖ (κ.map g).snd) =
      (μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map (Prod.map id g) := by
    have hk : κ.fst ×ₖ κ.snd.map f = (κ.fst ×ₖ κ.snd).map g := by
      simpa only [Kernel.map_id] using Kernel.map_prod_map κ.fst κ.snd measurable_id hf
    rw [hfst,hsnd,hk,Measure.compProd_map hg]
  change conditionalMutualInformation (P.map (Prod.map id g)) ≤ _
  have hCM := conditionalMutualInformation_compProd μ (κ.map g)
  have hCM' : conditionalMutualInformation (P.map (Prod.map id g)) =
      klDiv (P.map (Prod.map id g)) ((μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map (Prod.map id g)) := by
    simpa only [←hmap,hRef] using hCM
  rw [hCM']
  have h := klDiv_map_le P (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) hT
  have hCM0 : conditionalMutualInformation P = klDiv P (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
    simpa only [hP] using conditionalMutualInformation_compProd μ κ
  rwa [hCM0]




lemma conditionalMutualInformation_swap {S A B : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace A] [StandardBorelSpace B] [Nonempty A] [Nonempty B]
    (P : Measure (S×(A×B))) [IsProbabilityMeasure P] :
    conditionalMutualInformation (P.map (Prod.map id Prod.swap)) =
      conditionalMutualInformation P := by
  let μ := P.fst
  let κ := P.condKernel
  let e : S×(A×B) ≃ᵐ S×(B×A) :=
    (MeasurableEquiv.refl S).prodCongr MeasurableEquiv.prodComm
  have hP : μ ⊗ₘ κ = P := P.disintegrate P.condKernel
  let : IsMarkovKernel (κ.map Prod.swap) := Kernel.IsMarkovKernel.map κ measurable_swap
  have hf : (κ.map Prod.swap).fst = κ.snd := by
    rw [Kernel.fst_eq, ← Kernel.map_comp_right _ measurable_swap measurable_fst, Kernel.snd_eq]
    rfl
  have hs : (κ.map Prod.swap).snd = κ.fst := by
    rw [Kernel.snd_eq, ← Kernel.map_comp_right _ measurable_swap measurable_snd, Kernel.fst_eq]
    rfl
  have href : μ ⊗ₘ ((κ.map Prod.swap).fst ×ₖ (κ.map Prod.swap).snd) =
      (μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map e := by
    rw [hf,hs, ← Kernel.map_prod_swap, Measure.compProd_map measurable_swap]
    rfl
  have hQ : μ ⊗ₘ κ.map Prod.swap = P.map (Prod.map id Prod.swap) := by
    rw [Measure.compProd_map measurable_swap,hP]
  have hcm : conditionalMutualInformation (P.map (Prod.map id Prod.swap)) =
      klDiv (P.map (Prod.map id Prod.swap)) ((μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map e) := by
    simpa only [hQ,href] using conditionalMutualInformation_compProd μ (κ.map Prod.swap)
  have hcm0 : conditionalMutualInformation P = klDiv P (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
    simpa only [hP] using conditionalMutualInformation_compProd μ κ
  rw [hcm,hcm0]
  exact klDiv_map_equiv P (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) e


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

lemma mutualInformation_swap {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure (A×B)) [IsProbabilityMeasure P] :
    mutualInformation (P.map Prod.swap) = mutualInformation P := by
  have hf : (P.map Prod.swap).fst = P.snd := by
    simp only [Measure.fst,Measure.snd,Measure.map_map measurable_fst measurable_swap]; rfl
  have hs : (P.map Prod.swap).snd = P.fst := by
    simp only [Measure.fst,Measure.snd,Measure.map_map measurable_snd measurable_swap]; rfl
  unfold mutualInformation
  rw [hf,hs,←Measure.prod_swap]
  exact klDiv_map_equiv P (P.fst.prod P.snd) MeasurableEquiv.prodComm

lemma measurable_observedMessageMap {d k : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (observedMessageMap (d:=d) (k:=k) (W:=W)) :=
  ((measurable_exposedJointMap (d:=d) (k:=k) (W:=W)).fst).prodMk measurable_fst.snd

instance observedMessage_probability {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (observedMessage P) := by
  unfold observedMessage
  exact Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)

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



lemma mutualInformation_pair_right_le {A W E : Type*} [MeasurableSpace A]
    [MeasurableSpace W] [MeasurableSpace E] [StandardBorelSpace A] [StandardBorelSpace W]
    [Countable E] [MeasurableSingletonClass E] [Nonempty A] [Nonempty W] [Nonempty E]
    (P : Measure (A×(W×E))) [IsProbabilityMeasure P]
    (hH : shannonEntropy P.snd.snd ≠ ∞) :
    mutualInformation P ≤ mutualInformation (P.map (Prod.map id Prod.fst)) + shannonEntropy P.snd.snd := by
  let T : A×(W×E) → W×(E×A) := fun p => (p.2.1,(p.2.2,p.1))
  have hT : Measurable T := measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst)
  let R := P.map T
  let : IsProbabilityMeasure R := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  let : IsProbabilityMeasure (P.map (Prod.map (id : A → A) (Prod.fst : W×E → W))) :=
    Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  let U := R.map (Prod.map id Prod.swap)
  let : IsProbabilityMeasure U := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hHs : (U.map MeasurableEquiv.prodAssoc.symm).snd = P.snd.snd := by
    simp only [U,R,Measure.snd,Measure.map_map measurable_snd MeasurableEquiv.prodAssoc.symm.measurable,
      Measure.map_map (measurable_snd.comp MeasurableEquiv.prodAssoc.symm.measurable)
        (measurable_id.prodMap measurable_swap),
      Measure.map_map ((measurable_snd.comp MeasurableEquiv.prodAssoc.symm.measurable).comp
        (measurable_id.prodMap measurable_swap)) hT,
      Measure.map_map measurable_snd measurable_snd]
    rfl
  obtain ⟨hcfin,hcb⟩ := conditionalMutualInformation_le_entropy U (by rwa [hHs])
  rw [hHs] at hcb
  have hc : conditionalMutualInformation R ≤ shannonEntropy P.snd.snd := by
    have hh : conditionalMutualInformation U ≤ shannonEntropy P.snd.snd :=
      (ENNReal.toReal_le_toReal hcfin hH).mp hcb
    simpa only [U,conditionalMutualInformation_swap] using hh
  have hleft : R.map MeasurableEquiv.prodAssoc.symm = P.map Prod.swap := by
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable hT]
    rfl
  have hright : R.map (Prod.map id Prod.snd) = (P.map (Prod.map id Prod.fst)).map Prod.swap := by
    rw [Measure.map_map measurable_swap (measurable_id.prodMap measurable_fst)]
    change (P.map T).map (Prod.map id Prod.snd) = _
    rw [Measure.map_map (measurable_id.prodMap measurable_snd) hT]
    rfl
  have hchain := mutualInformation_chain R
  rw [hleft,hright,mutualInformation_swap,mutualInformation_swap] at hchain
  rw [hchain]
  exact add_le_add le_rfl hc

lemma mutualInformation_map_right_le {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (P : Measure (A×B)) [IsProbabilityMeasure P]
    (f : B → C) (hf : Measurable f) :
    mutualInformation (P.map (Prod.map id f)) ≤ mutualInformation P := by
  have hT : Measurable (Prod.map (id : A→A) f) := measurable_id.prodMap hf
  have hfst : (P.map (Prod.map id f)).fst = P.fst := by
    rw [Measure.fst,Measure.map_map measurable_fst hT]; rfl
  have hsnd : (P.map (Prod.map id f)).snd = P.snd.map f := by
    rw [Measure.snd,Measure.snd,Measure.map_map measurable_snd hT,Measure.map_map hf measurable_snd]; rfl
  have hRef : (P.fst.prod P.snd).map (Prod.map id f) = P.fst.prod (P.snd.map f) := by
    rw [←Measure.map_prod_map _ _ measurable_id hf,Measure.map_id]
  unfold mutualInformation
  rw [hfst,hsnd,←hRef]
  exact klDiv_map_le _ _ hT

lemma exposedInformation_le_entropy {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty W] [Nonempty (Sphere d)]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (hH : shannonEntropy P.fst.snd ≠ ∞) :
    exposedInformation P ≠ ∞ ∧ mutualInformation (observedMessage P) ≠ ∞ := by
  let : IsProbabilityMeasure (P.map (swapLast : (Sphere d×W)×Rows k d ≃ᵐ _)) :=
    Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hi := (countable_information_le_entropy (P.map swapLast) (by rwa [swapLast_snd])).1
  change mutualInformation (P.map swapLast) ≠ ∞ at hi
  rw [exposedInformation_chain] at hi
  exact ⟨(ENNReal.add_ne_top.mp hi).2,(ENNReal.add_ne_top.mp hi).1⟩

lemma exposedInformation_dropMessage {d k : ℕ} {W E : Type*}
    [MeasurableSpace W] [MeasurableSpace E] [StandardBorelSpace W] [StandardBorelSpace E]
    [Nonempty W] [Nonempty E] [Nonempty (Sphere d)]
    (P : Measure ((Sphere d×(W×E))×Rows k d)) [IsProbabilityMeasure P] :
    exposedInformation (P.map (fun p => ((p.1.1,p.1.2.1),p.2))) ≤ exposedInformation P := by
  let : IsProbabilityMeasure (P.map (exposedJointMap (d:=d) (k:=k) (W:=W×E))) :=
    Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have h := conditionalMutualInformation_map_right_le (P.map exposedJointMap)
    (Prod.fst : W×E → W) measurable_fst
  have hmap : (P.map (fun p => ((p.1.1,p.1.2.1),p.2))).map exposedJointMap =
      (P.map exposedJointMap).map (Prod.map id (Prod.map id (Prod.fst : W×E → W))) := by
    rw [Measure.map_map measurable_exposedJointMap
        ((measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd),
      Measure.map_map (measurable_id.prodMap (measurable_id.prodMap measurable_fst))
        measurable_exposedJointMap]
    rfl
  simpa only [exposedInformation,hmap] using h

lemma exposedInformation_refinement_cost {d k : ℕ} {W E : Type*}
    [MeasurableSpace W] [MeasurableSpace E] [Countable W] [Countable E]
    [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    [Nonempty W] [Nonempty E] [Nonempty (Sphere d)]
    (P : Measure ((Sphere d×(W×E))×Rows k d)) [IsProbabilityMeasure P]
    (hH : shannonEntropy P.fst.snd ≠ ∞)
    (hE : shannonEntropy P.fst.snd.snd ≠ ∞) :
    exposedInformation P ≤ exposedInformation (P.map (fun p => ((p.1.1,p.1.2.1),p.2))) +
      shannonEntropy P.fst.snd.snd := by
  let T : (Sphere d×(W×E))×Rows k d → (Sphere d×W)×Rows k d :=
    fun p => ((p.1.1,p.1.2.1),p.2)
  have hT : Measurable T := (measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd
  let Q := P.map T
  let : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  let : IsProbabilityMeasure (P.map (swapLast : (Sphere d×(W×E))×Rows k d ≃ᵐ _)) :=
    Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  let : IsProbabilityMeasure (Q.map (swapLast : (Sphere d×W)×Rows k d ≃ᵐ _)) :=
    Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hs : Q.fst.snd = P.fst.snd.fst := by
    simp only [Q,Measure.fst,Measure.snd,Measure.map_map measurable_snd measurable_fst,
      Measure.map_map (measurable_snd.comp measurable_fst) hT,
      Measure.map_map measurable_fst (measurable_snd.comp measurable_fst)]
    rfl
  have hHQ : shannonEntropy Q.fst.snd ≠ ∞ := by
    rw [hs]
    exact ne_top_of_le_ne_top hH (shannonEntropy_map_le P.fst.snd Prod.fst)
  have hqi : (P.map swapLast).map (Prod.map id Prod.fst) = Q.map swapLast := by
    rw [Measure.map_map (measurable_id.prodMap measurable_fst) swapLast.measurable]
    dsimp only [Q]
    rw [Measure.map_map swapLast.measurable hT]
    rfl
  have ho : (observedMessage P).map (Prod.map id Prod.fst) = observedMessage Q := by
    rw [observedMessage,Measure.map_map (measurable_id.prodMap measurable_fst) measurable_observedMessageMap]
    dsimp only [Q,observedMessage]
    rw [Measure.map_map measurable_observedMessageMap hT]
    rfl
  have hip := mutualInformation_pair_right_le (P.map swapLast) (by rwa [swapLast_snd])
  rw [swapLast_snd,hqi,exposedInformation_chain P,exposedInformation_chain Q] at hip
  have hop := mutualInformation_map_right_le (observedMessage P) (Prod.fst : W×E → W) measurable_fst
  rw [ho] at hop
  obtain ⟨hJP,hOP⟩ := exposedInformation_le_entropy P hH
  obtain ⟨hJQ,hOQ⟩ := exposedInformation_le_entropy Q hHQ
  have hib := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hOQ,hJQ⟩,hE⟩) hip
  rw [ENNReal.toReal_add hOP hJP,ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hOQ,hJQ⟩) hE,
    ENNReal.toReal_add hOQ hJQ] at hib
  have hob := ENNReal.toReal_mono hOP hop
  apply (ENNReal.toReal_le_toReal hJP (ENNReal.add_ne_top.mpr ⟨hJQ,hE⟩)).mp
  rw [ENNReal.toReal_add hJQ hE]
  linarith



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



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Posterior
attribute [-instance] _root_.OAI.CurrentProjection.blockLaw_probability _root_.OAI.CurrentProjection.endingRowLaw_probability _root_.OAI.CurrentProjection.endingSignalLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.fixedTargetPosterior_markov _root_.OAI.CurrentProjection.gaussianObservation_probability _root_.OAI.CurrentProjection.gaussianObservations_probability _root_.OAI.CurrentProjection.prefixLaw_probability _root_.OAI.CurrentProjection.residualLaw_probability _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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

lemma measurable_refineRowsMap {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (e : Sphere d×W → E) (he : Measurable e) :
    Measurable (fun p : (Sphere d×W)×Rows m d => ((p.1.1,(p.1.2,e p.1)),p.2)) :=
  (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk (he.comp measurable_fst))).prodMk measurable_snd

lemma refineRows_probability {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (e : Sphere d×W → E) (he : Measurable e) : IsProbabilityMeasure (refineRows P e) := by
  unfold refineRows
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_refineRowsMap e he).aemeasurable).mpr inferInstance

lemma refineRows_fst {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) (e : Sphere d×W → E) (he : Measurable e) :
    (refineRows P e).fst = refineSignal P.fst e := by
  rw [refineRows,Measure.fst,refineSignal,Measure.fst,
    Measure.map_map measurable_fst (measurable_refineRowsMap e he),
    Measure.map_map (measurable_fst.prodMk (measurable_snd.prodMk he)) measurable_fst]
  rfl

lemma refineRows_signal_rows {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) (e : Sphere d×W → E) (he : Measurable e) :
    ((refineRows P e).map swapLast).fst = (P.map swapLast).fst := by
  rw [Measure.fst,Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map measurable_fst swapLast.measurable,refineRows,
    Measure.map_map (measurable_fst.comp swapLast.measurable) (measurable_refineRowsMap e he)]
  rfl

lemma refineRows_drop {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) (e : Sphere d×W → E) (he : Measurable e) :
    (refineRows P e).map (fun p => ((p.1.1,p.1.2.1),p.2)) = P := by
  rw [refineRows,Measure.map_map
    ((measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd)
    (measurable_refineRowsMap e he)]
  exact Measure.map_id

lemma alignedExperiment_drop {d m r : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×(W×E))×Rows m d)) [IsProbabilityMeasure P] :
    (alignedExperiment (r:=r) P).map (fun p => ((p.1.1,p.1.2.1),p.2)) =
      alignedExperiment (r:=r) (P.map (fun p => ((p.1.1,p.1.2.1),p.2))) := by
  let T : (Sphere d×(W×E))×Rows m d → (Sphere d×W)×Rows m d :=
    fun p => ((p.1.1,p.1.2.1),p.2)
  have hT : Measurable T := (measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd
  have hprod : (P.map T).prod (gaussianRows r d) =
      (P.prod (gaussianRows r d)).map (Prod.map T id) := by
    simpa only [Measure.map_id] using (Measure.map_prod_map P (gaussianRows r d) hT measurable_id)
  rw [alignedExperiment,Measure.map_map
    ((measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd) measurable_alignedMap]
  change _ = ((P.map T).prod (gaussianRows r d)).map _
  rw [hprod,Measure.map_map measurable_alignedMap (hT.prodMap measurable_id)]
  rfl

lemma independent_refineSignal_drop {d k : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (e : Sphere d×W → E) (he : Measurable e) :
    ((refineSignal P e).prod (gaussianRows k d)).map (fun p => ((p.1.1,p.1.2.1),p.2)) =
      P.prod (gaussianRows k d) := by
  let : IsFiniteMeasure (refineSignal P e) := Measure.isFiniteMeasure_map _ _
  have hb : (refineSignal P e).map (fun p => (p.1,p.2.1)) = P := by
    rw [refineSignal,Measure.map_map (measurable_fst.prodMk measurable_snd.fst)
      (measurable_fst.prodMk (measurable_snd.prodMk he))]
    exact Measure.map_id
  have hh := Measure.map_prod_map (refineSignal P e) (gaussianRows k d)
    (measurable_fst.prodMk measurable_snd.fst) measurable_id
  rw [Measure.map_id,hb] at hh
  exact hh.symm

lemma signal_marginal_of_independence {S W G : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace G] (P : Measure ((S×W)×G)) (ν : Measure S)
    (γ : Measure G) [IsProbabilityMeasure γ] [SFinite ν]
    (hInd : (P.map swapLast).fst = ν.prod γ) : P.fst.fst = ν := by
  have hh := congrArg Measure.fst hInd
  rw [Measure.fst_prod] at hh
  convert hh using 1
  simp only [Measure.fst,Measure.map_map measurable_fst measurable_fst,
    Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map measurable_fst (measurable_fst.comp swapLast.measurable)]
  rfl



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Comparison
attribute [-instance] _root_.OAI.CurrentProjection.blockLaw_probability _root_.OAI.CurrentProjection.endingRowLaw_probability _root_.OAI.CurrentProjection.endingSignalLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.fixedTargetPosterior_markov _root_.OAI.CurrentProjection.gaussianObservation_probability _root_.OAI.CurrentProjection.gaussianObservations_probability _root_.OAI.CurrentProjection.prefixLaw_probability _root_.OAI.CurrentProjection.residualLaw_probability _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
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


lemma critical_unrefined_comparison {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty W] [Nonempty (Sphere d)]
    [IsProbabilityMeasure (uniformSphere d)] (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d))
    (hH : shannonEntropy P.fst.snd ≠ ∞) :
    exposedInformation (P.fst.prod (gaussianRows (m+r) d)) ≠ ∞ ∧
    exposedInformation (alignedExperiment (r:=r) P) ≠ ∞ ∧
    (exposedInformation (P.fst.prod (gaussianRows (m+r) d))).toReal ≤
      (exposedInformation (alignedExperiment (r:=r) P)).toReal +
      (rowInformation P (gaussianRows m d)).toReal/q +
      2*(shannonEntropy (P.fst.map (criticalRefinement P.fst (m+r)))).toReal +
      (1+18*(d:ℝ)+5*(m+r)) + Real.log (1+(shannonEntropy (criticalSignal P.fst (m+r)).snd).toReal) := by
  let e := criticalRefinement P.fst (m+r)
  have he := measurable_criticalRefinement P.fst (m+r)
  let R := refineRows P e
  let : IsProbabilityMeasure R := refineRows_probability P e he
  have hRF : R.fst = criticalSignal P.fst (m+r) := refineRows_fst P e he
  have hRI : (R.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d) :=
    (refineRows_signal_rows P e he).trans hInd
  have hσ := signal_marginal_of_independence P (uniformSphere d) (gaussianRows m d) hInd
  obtain ⟨hE,hEb,hF,hFb⟩ := criticalSignal_entropy P.fst hσ hdim.2.2.2.1 hH
  have hRIeq : rowInformation R (gaussianRows m d) = rowInformation P (gaussianRows m d) :=
    rowInformation_refinement P (gaussianRows m d) e he
  obtain ⟨hJ0R,hJ1R,hcmp⟩ := critical_refined_comparison hdim P.fst hσ hH R hRF hRI
  rw [hRIeq] at hcmp
  have hJ0 : exposedInformation (P.fst.prod (gaussianRows (m+r) d)) ≠ ∞ :=
    (exposedInformation_le_entropy _ (by simpa only [Measure.fst_prod] using hH)).1
  have hJ1 : exposedInformation (alignedExperiment (r:=r) P) ≠ ∞ :=
    (exposedInformation_le_entropy _ (by simpa only [alignedExperiment_fst] using hH)).1
  have hDrop := exposedInformation_dropMessage ((criticalSignal P.fst (m+r)).prod (gaussianRows (m+r) d))
  change exposedInformation (((refineSignal P.fst e).prod (gaussianRows (m+r) d)).map
    (fun p => ((p.1.1,p.1.2.1),p.2))) ≤ _ at hDrop
  simp only [independent_refineSignal_drop P.fst e he] at hDrop
  have hAF : (alignedExperiment (r:=r) R).fst = criticalSignal P.fst (m+r) :=
    (alignedExperiment_fst R).trans hRF
  have hAE : (alignedExperiment (r:=r) R).fst.snd.snd = P.fst.map e := by
    rw [hAF]
    exact refineSignal_snd_snd P.fst e he
  have hCost := exposedInformation_refinement_cost (alignedExperiment (r:=r) R)
    (by rwa [hAF]) (by rwa [hAE])
  simp only [hAE,alignedExperiment_drop,R,refineRows_drop P e he] at hCost
  have hh0 := ENNReal.toReal_mono hJ0R hDrop
  have hh1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hJ1,hE⟩) hCost
  rw [ENNReal.toReal_add hJ1 hE] at hh1
  refine ⟨hJ0,hJ1,?_⟩
  linarith



lemma critical_entropy_scalars {d : ℕ} (hd : 1 ≤ d) {H E F : ℝ}
    (hH0 : 0 ≤ H) (hH : H ≤ (d:ℝ)^2)
    (hE : E ≤ 1+2*Real.log (20*((d:ℝ)+1+H)+1)) (hF0 : 0 ≤ F) (hF : F ≤ H+E) :
    E ≤ 127*(d:ℝ) ∧ Real.log (1+F) ≤ 131*(d:ℝ) := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0:ℝ) < d := by linarith
  have hd2 : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hd21 : (1:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have harg : 20*((d:ℝ)+1+H)+1 ≤ 61*(d:ℝ)^2 := by nlinarith
  have hlog := Real.log_le_log (by positivity : 0<20*((d:ℝ)+1+H)+1) harg
  rw [Real.log_mul (by norm_num : (61:ℝ) ≠ 0) (by positivity),Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hl61 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 61)
  have hld := Real.log_le_self hd0.le
  have hEb : E ≤ 127*(d:ℝ) := by nlinarith
  refine ⟨hEb,?_⟩
  have harg2 : 1+F ≤ 129*(d:ℝ)^2 := by nlinarith
  have hlog2 := Real.log_le_log (by positivity : 0<1+F) harg2
  rw [Real.log_mul (by norm_num : (129:ℝ) ≠ 0) (by positivity),Real.log_pow] at hlog2
  norm_num only [Nat.cast_ofNat] at hlog2
  have hl129 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 129)
  nlinarith




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



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.FiberBlock
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



lemma shannonEntropy_le_log_card {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (π : Measure W) [IsProbabilityMeasure π] :
    (shannonEntropy π).toReal ≤ Real.log (Fintype.card W) := by
  let : Nonempty W := nonempty_of_isProbabilityMeasure π
  let Q := (PMF.uniformOfFintype W).toMeasure
  have hQ : ∀ w, Q {w} = (Fintype.card W:ℝ≥0∞)⁻¹ := by
    intro w
    change (PMF.uniformOfFintype W).toMeasure {w} = _
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton w),PMF.uniformOfFintype_apply]
  have hq0 : (Fintype.card W:ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hPQ : π ≪ Q := countable_ac_of_atom π Q (by intro w hw; exact (hq0 ((hQ w).symm.trans hw)).elim)
  obtain ⟨_,hb⟩ := countable_entropy_le_crossEntropy π Q hPQ (Integrable.of_finite)
  have he : (fun w => -Real.log (Q {w}).toReal) = fun _ : W => Real.log (Fintype.card W) := by
    funext w
    rw [hQ w,ENNReal.toReal_inv,ENNReal.toReal_natCast,Real.log_inv,neg_neg]
  simpa [he] using hb

lemma fiber_comparison {d : ℕ} (hd : 100 ≤ d) {W : Type*} [Fintype W]
    [MeasurableSpace W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows (d/10) d)) [IsProbabilityMeasure P]
    (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows (d/10) d))
    (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal ((d:ℝ)^2)) :
    freshInformation P.fst (d/3) ≤ exposedInformation (alignedExperiment (r:=d/3-d/10) P) +
      ENNReal.ofReal (1000*d) := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  let : Nonempty W := nonempty_of_isProbabilityMeasure P.fst.snd
  have hHfin : shannonEntropy P.fst.snd ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH
  have hHr : (shannonEntropy P.fst.snd).toReal ≤ (d:ℝ)^2 :=
    ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hH
  have hdim : AdmissibleDimensions d (d/10) (d/3-d/10) (d/10) := by
    unfold AdmissibleDimensions
    omega
  obtain ⟨hJ0,hJ1,hcomp⟩ := critical_unrefined_comparison hdim P hInd hHfin
  have hσ := signal_marginal_of_independence P (uniformSphere d) (gaussianRows (d/10) d) hInd
  obtain ⟨hE,hEb,hF,hFb⟩ := criticalSignal_entropy P.fst hσ hdim.2.2.2.1 hHfin
  obtain ⟨he,hl⟩ := critical_entropy_scalars (show 1 ≤ d by omega) ENNReal.toReal_nonneg hHr
    hEb ENNReal.toReal_nonneg hFb
  obtain ⟨hRow,hRowB⟩ := rowInformation_le_entropy P (uniformSphere d) (gaussianRows (d/10) d)
    hInd (by rwa [swapLast_snd])
  rw [swapLast_snd] at hRowB
  have hqr : (0:ℝ) < (d/10:ℕ) := by exact_mod_cast (show 0<d/10 by omega)
  have hqrB : (d:ℝ) ≤ 20*(d/10:ℕ) := by exact_mod_cast (show d≤20*(d/10) by omega)
  have hℓr : ((d/10+(d/3-d/10):ℕ):ℝ) ≤ d := by exact_mod_cast (show d/10+(d/3-d/10)≤d by omega)
  simp only [Nat.cast_add] at hℓr
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (show 1≤d by omega)
  have hRowr : (rowInformation P (gaussianRows (d/10) d)).toReal/(d/10:ℕ) ≤ 20*(d:ℝ) := by
    apply (div_le_iff₀ hqr).mpr
    nlinarith [hRowB.trans hHr]
  have hbound : exposedInformation (P.fst.prod (gaussianRows (d/10+(d/3-d/10)) d)) ≤
      exposedInformation (alignedExperiment (r:=d/3-d/10) P) + ENNReal.ofReal (1000*d) := by
    apply (ENNReal.toReal_le_toReal hJ0 (ENNReal.add_ne_top.mpr ⟨hJ1,ENNReal.ofReal_ne_top⟩)).mp
    rw [ENNReal.toReal_add hJ1 ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal (by positivity)]
    nlinarith
  have hdimEq : d/10+(d/3-d/10) = d/3 := by omega
  change freshInformation P.fst (d/10+(d/3-d/10)) ≤ _ at hbound
  have hfresh : freshInformation P.fst (d/10+(d/3-d/10)) = freshInformation P.fst (d/3) :=
    congrArg (freshInformation P.fst) hdimEq
  rwa [hfresh] at hbound

theorem fiberBlockMain_oai : FiberBlockMain := by
  refine ⟨1000,100,by norm_num,?_⟩
  intro d hd U V _ _ _ _ _ _ P _ hS κ _ N hN hcard hNlog
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  let : Nonempty U := nonempty_of_isProbabilityMeasure P.snd
  let : Nonempty V := nonempty_of_isProbabilityMeasure (endingSignalLaw P κ).snd
  have hEnt : shannonEntropy (endingSignalLaw P κ).snd ≤ ENNReal.ofReal ((d:ℝ)^2) := by
    apply (ENNReal.toReal_le_toReal (shannonEntropy_finite _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
    apply (shannonEntropy_le_log_card _).trans
    exact (Real.log_le_log (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast hcard)).trans hNlog
  have hInd : ((endingRowLaw P κ).map swapLast).fst = (uniformSphere d).prod (gaussianRows (d/10) d) := by
    rw [endingRowLaw_independence,hS]
  have h := fiber_comparison hd (endingRowLaw P κ) hInd (by rwa [endingRowLaw_fst])
  simp only [endingRowLaw_fst] at h
  have hproc := block_exposed_le_fresh (r:=d/3-d/10) P κ
  have he : freshInformation P (d/10+(d/3-d/10)) = freshInformation P (d/3) :=
    congrArg (freshInformation P) (by omega)
  rw [he] at hproc
  exact h.trans (add_le_add hproc le_rfl)



end CurrentProjection

end

end OAI
end

theorem solution : type_of% @OAI.CurrentProjection.fiberBlockMain_oai := @OAI.CurrentProjection.fiberBlockMain_oai
