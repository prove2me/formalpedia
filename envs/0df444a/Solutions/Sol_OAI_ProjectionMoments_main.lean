-- Prove2me | solution 1 for OAI.ProjectionMoments.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T17:47:15.828013+00:00
-- url     : https://prove2.me/submissions/9d49505c-5a50-4918-b5dd-c935f4a9dbe5

import Mathlib
import Definitions.Def_ProjectionMoments

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
alias Finset.prod_le_one₀ := Finset.prod_le_one
alias Finset.one_le_prod₀ := Finset.one_le_prod
alias List.Nodup.getElem?_inj := List.getElem?_inj
end OAICompat434

universe u

section
section
namespace OAI

noncomputable section

section InlineMainProof

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace


namespace NoiselessRegression

namespace Learner

end Learner

open scoped Topology

open InnerProductSpace

section SphereBounds

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SphereBounds

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end NoiselessRegression

end InlineMainProof

open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section GaussianGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianGraph

section

section BallDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end BallDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

section Rotations

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

variable {E}

variable [MeasurableSpace E] [BorelSpace E]

end Rotations

section Triangular

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end Triangular

section CoordinateDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end CoordinateDensity

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

section


variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

namespace Learner

section


variable {d M T : ℕ} {Ω : Type u}

end


variable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]

end Learner

namespace FiniteKernelLearner

variable {d M T : ℕ}

end FiniteKernelLearner

section

variable {J O : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace O]

end

namespace FiniteKernelLearner

section

open Learner

variable {d M T : ℕ}

end

open Learner

variable {d M T : ℕ}

end FiniteKernelLearner

section


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

namespace Learner

variable {d M T : ℕ} {Ω : Type u}

end Learner

end

namespace FiniteKernelLearner

section


variable {d M T : ℕ}

end


variable {d M T : ℕ} {Ξ : Type u} [MeasurableSpace Ξ]

end FiniteKernelLearner

end NoiselessRegression

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace

open NoiselessRegression NoiselessRegression.FiniteKernelLearner

open scoped ENNReal NNReal RealInnerProductSpace Topology


namespace ProjectionMoments

end ProjectionMoments

end

end OAI
end
end

section
section
namespace OAI

/-!
Finite-state Gaussian regression with noiseless labels and angular accuracy.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section


namespace NoiselessRegression

namespace Learner

def success {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (s : UnitSphere d) : ℝ≥0∞ :=
  (ρ.prod (sampleLaw d T))
    {z | angularError s (L.estimate s z.1 z.2) ≤ ε}

end Learner

def SubquadraticMemory : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ) ^ 2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d (M d) T Ω, L.Admissible ρ →
    (((2 : ℕ) / (3 : ℕ) : ℝ≥0∞) ≤ L.uniformSuccess ρ ε ∨
      ∀ s, ((2 : ℕ) / (3 : ℕ) : ℝ≥0∞) ≤ L.success ρ ε s) →
    c * (d : ℝ) * Real.log (1 / ε) ≤ (T : ℝ)

def FixedQuadraticMemory : Prop :=
  ∀ A₀ : ℝ, 0 < A₀ → ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
    ∀ d : ℕ, d₀ ≤ d → ∀ M T : ℕ, (M : ℝ) ≤ A₀ * (d : ℝ) ^ 2 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d M T Ω, L.Admissible ρ →
    ((2 : ℕ) / (3 : ℕ) : ℝ≥0∞) ≤ L.uniformSuccess ρ ε →
    c * (d : ℝ) * Real.log (1 / ε) ≤ (T : ℝ)

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Local mass bounds and quantitative finite Euclidean nets.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section


namespace NoiselessRegression

section FrostmanGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def HasLocalMassBound (ν : Measure E) (a : ℝ) : Prop :=
  ∀ t ∈ ν.support, ∀ r : ℝ, 0 < r →
    ν (Metric.closedBall t r) ≤ ENNReal.ofReal (r ^ a)

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

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Inverse moments from polynomial tube bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section


namespace NoiselessRegression

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

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Affine tube covers and inverse-distance bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section


namespace NoiselessRegression

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

theorem HasLocalMassBound.affine_inverse_moment {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] (m : ℕ)
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + (m + 1 : ℕ) ≤ a) :
    ∫⁻ t, ENNReal.ofReal ((Metric.infDist t L)⁻¹ ^ m) ∂ν ≤
      ν Set.univ +
        ENNReal.ofReal ((3 : ℝ) ^ Module.finrank ℝ L.direction * (4 : ℝ) ^ a) *
          (2 : ℝ≥0∞) ^ (m + 1) := by
  apply inverse_moment_of_tube_bound ν _ m (Metric.continuous_infDist_pt _).measurable
    (fun _ => Metric.infDist_nonneg)
  intro r hr hr1
  exact hν.affine_tube_pow hsupport L (m + 1) hmargin hr hr1

theorem HasLocalMassBound.affine_null {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L]
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + 1 ≤ a) : ν L = 0 := by
  let C : ℝ := (3 : ℝ) ^ Module.finrank ℝ L.direction * (4 : ℝ) ^ a
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (n : ℕ) : ν L ≤ ENNReal.ofReal (C * (1 / 2 : ℝ) ^ n) := by
    have hn : 0 < (1 / 2 : ℝ) ^ n := by positivity
    have hn1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc
      ν L ≤ ν {t | Metric.infDist t L ≤ (1 / 2 : ℝ) ^ n} := by
        apply measure_mono
        intro t ht
        simp only [mem_ofPred_eq, Metric.infDist_zero_of_mem ht]
        exact hn.le
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ 1) :=
        hν.affine_tube_pow hsupport L 1 (by simpa using hmargin) hn hn1
      _ = _ := by rw [pow_one, ENNReal.ofReal_mul hC]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C * (1 / 2 : ℝ) ^ n))
      atTop (𝓝 0) := by
    convert ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := C)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))) using 1
    simp
  exact le_antisymm (ge_of_tendsto' hlim hb) (by positivity)

end AffineTubes

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Gram determinants, orthogonal distances, and product integration.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section


namespace NoiselessRegression

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
def gsUpper (v : Fin n → E) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (if i = j then 1 else 0) +
    if i < j then ⟪gramSchmidt ℝ v i, v j⟫ / ‖gramSchmidt ℝ v i‖ ^ 2 else 0

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
lemma infDist_affine_mk' (p x : E) (K : Submodule ℝ E) :
    Metric.infDist x (AffineSubspace.mk' p K : Set E) =
      Metric.infDist (x - p) (K : Set E) := by
  rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist,
    EuclideanGeometry.orthogonalProjection_apply_mem _ (AffineSubspace.self_mem_mk' p K),
    dist_eq_norm, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  change ‖x - _‖ = ⨅ y : K, ‖(x - p) - y‖
  rw [← Submodule.starProjection_minimal]
  simp only [AffineSubspace.direction_mk', vsub_eq_sub, vadd_eq_add,
    Submodule.coe_orthogonalProjectionOnto_apply]
  congr 1
  abel

lemma norm_gramSchmidt_sub_eq_affine_infDist (p : E) (t : Fin n → E) (j : Fin n) :
    ‖gramSchmidt ℝ (fun i => t i - p) j‖ =
      Metric.infDist (t j) (AffineSubspace.mk' p
        (Submodule.span ℝ ((fun i => t i - p) '' Set.Iio j)) : Set E) := by
  rw [infDist_affine_mk', norm_gramSchmidt_eq_infDist]

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

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Inverse Gram moments and almost-everywhere replica independence.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section


namespace NoiselessRegression

section ReplicaMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def replicaWeight (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal ((‖gramSchmidt ℝ (fun j => v j - p) i‖)⁻¹ ^ m)

lemma measurable_replicaWeight (m : ℕ) (p : E) (n : ℕ) :
    Measurable (replicaWeight m p (n := n)) := by
  have hs : Measurable (fun v : Fin n → E => fun j => v j - p) := by fun_prop
  exact Finset.measurable_prod _ fun i _ =>
    (((measurable_gramSchmidt i).comp hs).norm.inv.pow_const m).ennreal_ofReal

omit [MeasurableSpace E] [BorelSpace E] in
lemma replicaWeight_snoc (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) (x : E) :
    replicaWeight m p (Fin.snoc v x) = replicaWeight m p v *
      ENNReal.ofReal ((Metric.infDist x (AffineSubspace.mk' p
        (Submodule.span ℝ (Set.range (fun i => v i - p))) : Set E))⁻¹ ^ m) := by
  unfold replicaWeight
  rw [Fin.prod_univ_castSucc]
  simp only [gramSchmidt_castSucc, Fin.snoc_castSucc]
  rw [norm_gramSchmidt_sub_eq_affine_infDist, image_Iio_last]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]

def replicaConstant (ν : Measure E) (a : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ν Set.univ + ENNReal.ofReal ((3 : ℝ) ^ Module.finrank ℝ E * (4 : ℝ) ^ a) *
    (2 : ℝ≥0∞) ^ (m+1)

lemma affine_inverse_moment_le_replicaConstant {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] (m : ℕ)
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + (m + 1 : ℕ) ≤ a) :
    ∫⁻ x, ENNReal.ofReal ((Metric.infDist x L)⁻¹ ^ m) ∂ν ≤ replicaConstant ν a m := by
  apply (hν.affine_inverse_moment hsupport L m hmargin).trans
  dsimp [replicaConstant]
  gcongr
  · norm_num
  · exact Submodule.finrank_le L.direction

theorem replica_integral_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (m : ℕ) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => ν) ≤
      (replicaConstant ν a m) ^ n := by
  induction n with
  | zero => simp [replicaWeight]
  | succ n ih =>
    have hmargin' : (n : ℝ) + m ≤ a := by exact le_trans (by push_cast; linarith) hmargin
    have hinner (v : Fin n → E) :
        ∫⁻ x, replicaWeight m p (Fin.snoc v x) ∂ν ≤
          replicaWeight m p v * replicaConstant ν a m := by
      simp_rw [replicaWeight_snoc]
      rw [lintegral_const_mul _ (by fun_prop)]
      gcongr
      apply affine_inverse_moment_le_replicaConstant hν hsupport
      have hdim := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simp only [Fintype.card_fin] at hdim
      have hdim' : (Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i => v i - p))) : ℝ) ≤ n :=
        by exact_mod_cast hdim
      rw [AffineSubspace.direction_mk']
      push_cast at hmargin ⊢
      linarith
    calc
      _ = ∫⁻ v : Fin n → E, ∫⁻ x, replicaWeight m p (Fin.snoc v x) ∂ν
          ∂Measure.pi (fun _ => ν) := lintegral_pi_snoc ν _ (measurable_replicaWeight m p (n+1))
      _ ≤ ∫⁻ v : Fin n → E, replicaWeight m p v * replicaConstant ν a m
          ∂Measure.pi (fun _ => ν) := lintegral_mono hinner
      _ = (∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => ν)) *
          replicaConstant ν a m := lintegral_mul_const _ (measurable_replicaWeight m p n)
      _ ≤ (replicaConstant ν a m)^n * replicaConstant ν a m :=
          mul_le_mul' (ih hmargin') le_rfl
      _ = _ := (pow_succ _ _).symm
end ReplicaMoments
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

theorem ae_gramSchmidt_ne_zero {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) ≤ a) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν),
      ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0 := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ n ih =>
    rw [ae_pi_snoc ν (measurableSet_gramSchmidt_ne_zero p (n+1))]
    have hn : (n : ℝ) ≤ a := by push_cast at hmargin; linarith
    filter_upwards [ih hn] with v hv
    let L := AffineSubspace.mk' p (Submodule.span ℝ (Set.range (fun i : Fin n => v i - p)))
    have hdim : (Module.finrank ℝ L.direction : ℝ) ≤ n := by
      dsimp [L]
      rw [AffineSubspace.direction_mk']
      have hh := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simp only [Fintype.card_fin, Set.finrank] at hh
      exact_mod_cast hh
    have hnull : ν L = 0 := hν.affine_null hsupport L (by push_cast at hmargin; linarith)
    have ha : ∀ᵐ x ∂ν, x ∉ L := by
      rw [ae_iff]
      convert hnull using 2
      ext x
      simp
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [norm_gramSchmidt_sub_eq_affine_infDist, image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact ne_of_gt ((L.closed_of_finiteDimensional.notMem_iff_infDist_pos
        ⟨p, AffineSubspace.self_mem_mk' _ _⟩).mp hx)
    | cast j => simpa only [gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

theorem ae_replica_linearIndependent {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) ≤ a) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν),
      LinearIndependent ℝ (fun j => v j - p) := by
  filter_upwards [ae_gramSchmidt_ne_zero hν hsupport p n hmargin] with v hv
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [det_gram_eq_prod_gramSchmidt]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hv i))

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma sqrt_det_gram (n : ℕ) (v : Fin n → E) :
    Real.sqrt (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
  rw [det_gram_eq_prod_gramSchmidt, Real.sqrt_prod _ (fun _ _ => sq_nonneg _)]
  simp only [Real.sqrt_sq (norm_nonneg _)]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma replicaWeight_eq_det (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) :
    replicaWeight m p v = ENNReal.ofReal
      ((Real.sqrt (Matrix.gram ℝ (fun j => v j - p)).det)⁻¹ ^ m) := by
  rw [sqrt_det_gram, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)).symm

theorem gram_integral_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (m : ℕ) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ v : Fin n → E, ENNReal.ofReal
      ((Real.sqrt (Matrix.gram ℝ (fun j => v j - p)).det)⁻¹ ^ m)
      ∂Measure.pi (fun _ => ν) ≤ (replicaConstant ν a m)^n := by
  simpa only [← replicaWeight_eq_det] using replica_integral_bound hν hsupport m p n hmargin

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Gaussian coordinate domination and replica kernel bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section


namespace NoiselessRegression

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

lemma lintegral_product_differences (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ x, φ x = 1) (m n : ℕ) (y : Fin m → ℝ) :
    ∫⁻ z : Fin m → Fin n → ℝ,
      ∏ j, φ (y j) * ∏ i, φ (y j - z j i) = ∏ j, φ (y j) := by
  rw [volume_pi, lintegral_fin_prod (volume : Measure (Fin n → ℝ)) m
    (fun j z => φ (y j) * ∏ i, φ (y j - z i)) (by intro i; fun_prop)]
  apply Finset.prod_congr rfl
  intro j _
  rw [lintegral_const_mul _ (by fun_prop), volume_pi,
    lintegral_fin_prod (volume : Measure ℝ) n
      (fun _ z => φ (y j - z)) (by intro i; fun_prop)]
  simp_rw [lintegral_sub_left_eq_self φ (y j), hφ1]
  simp

end ReplicaKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_rows_kernel_bound {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1)
    (m : ℕ) (y : Fin m → ℝ) :
    ∫⁻ A : Fin m → E, (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) * ∏ j, φ (y j) := by
  let H : (Fin m → Fin n → ℝ) → ℝ≥0∞ :=
    fun z => ∏ j, φ (y j) * ∏ i, φ (y j - z j i)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have heq (A : Fin m → E) :
      (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫) =
      H (fun j i => ⟪v i, A j⟫) := by
    dsimp [H]
    rw [Finset.prod_mul_distrib, Finset.prod_comm]
  simp_rw [heq]
  rw [← lintegral_map hH (by fun_prop)]
  calc
    _ ≤ ∫⁻ z, H z ∂(ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) •
        (volume : Measure (Fin m → Fin n → ℝ))) :=
      lintegral_mono' (gaussian_rows_pairings_le v hv m) (fun _ => le_rfl)
    _ = _ := by
      rw [lintegral_smul_measure]
      change _ * (∫⁻ z : Fin m → Fin n → ℝ, ∏ j, φ (y j) * ∏ i, φ (y j - z j i)) = _
      rw [lintegral_product_differences φ hφ hφ1]

lemma gaussian_replica_kernel_bound {n : ℕ} (p : E) (v : Fin n → E)
    (hv : LinearIndependent ℝ (fun i => v i - p))
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1) (m : ℕ) :
    ∫⁻ A : Fin m → E, ∫⁻ y : Fin m → ℝ,
      (∏ j, φ (y j - ⟪p, A j⟫)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)
      ∂volume ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i - p) i‖)⁻¹ ^ m) := by
  have ht (A : Fin m → E) :
      (∫⁻ y : Fin m → ℝ, (∏ j, φ (y j - ⟪p, A j⟫)) *
        ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)) =
      ∫⁻ y : Fin m → ℝ, (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i - p, A j⟫) := by
    have he (y : Fin m → ℝ) (i : Fin n) (j : Fin m) :
        y j - ⟪p, A j⟫ - ⟪v i - p, A j⟫ = y j - ⟪v i, A j⟫ := by
      rw [inner_sub_left]
      ring
    simpa only [Pi.sub_apply, he] using
      lintegral_sub_right_eq_self
        (fun y : Fin m → ℝ => (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i - p, A j⟫))
        (fun j => ⟪p, A j⟫)
  simp_rw [ht]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ ≤ ∫⁻ y : Fin m → ℝ,
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i - p) i‖)⁻¹ ^ m) *
        ∏ j, φ (y j) := lintegral_mono fun y =>
          gaussian_rows_kernel_bound (fun i => v i - p) hv φ hφ hφ1 m y
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop), volume_pi,
        lintegral_fin_prod volume m (fun _ => φ) (fun _ => hφ)]
      simp [hφ1]

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Projection smoothing, Gaussian noise, and bounds under weak limits.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section


namespace NoiselessRegression

section SmoothingMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def projectionSmoothing (ν : Measure E) (φ : ℝ → ℝ≥0∞) (m : ℕ)
    (z : (Fin m → E) × (Fin m → ℝ)) : ℝ≥0∞ :=
  ∫⁻ t, ∏ j, φ (z.2 j - ⟪t, z.1 j⟫) ∂ν

lemma measurable_projectionSmoothing (ν : Measure E) [SFinite ν]
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m : ℕ) :
    Measurable (projectionSmoothing ν φ m) := by
  apply Measurable.lintegral_prod_right
  fun_prop

lemma projectionSmoothing_pow (ν : Measure E) [SigmaFinite ν]
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m n : ℕ)
    (z : (Fin m → E) × (Fin m → ℝ)) :
    (projectionSmoothing ν φ m z)^(n+1) =
      ∫⁻ w : E × (Fin n → E),
        (∏ j, φ (z.2 j - ⟪w.1, z.1 j⟫)) *
          ∏ i, ∏ j, φ (z.2 j - ⟪w.2 i, z.1 j⟫)
        ∂ν.prod (Measure.pi (fun _ => ν)) := by
  rw [lintegral_prod _ (by fun_prop)]
  have hG : Measurable (fun v : Fin n → E =>
      ∏ i, ∏ j, φ (z.2 j - ⟪v i, z.1 j⟫)) := by fun_prop
  simp_rw [lintegral_const_mul _ hG]
  rw [lintegral_mul_const _ (by fun_prop), ← lintegral_pow_pi ν
    (fun t : E => ∏ j, φ (z.2 j - ⟪t, z.1 j⟫)) (by fun_prop) n]
  exact pow_succ' _ _

theorem projectionSmoothing_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1)
    (m n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ z : (Fin m → E) × (Fin m → ℝ),
      (projectionSmoothing ν φ m z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
       ν Set.univ * (replicaConstant ν a m)^n := by
  simp_rw [projectionSmoothing_pow ν φ hφ m n]
  rw [lintegral_lintegral_swap (by fun_prop), lintegral_prod _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ p, ∫⁻ v : Fin n → E, replicaWeight m p v
        ∂Measure.pi (fun _ => ν) ∂ν := by
      apply lintegral_mono
      intro p
      apply lintegral_mono_ae
      filter_upwards [ae_replica_linearIndependent hν hsupport p n
        (le_trans (le_add_of_nonneg_right (Nat.cast_nonneg m)) hmargin)] with v hv
      rw [lintegral_prod _ (by fun_prop), replicaWeight_eq_det, sqrt_det_gram]
      exact gaussian_replica_kernel_bound p v hv φ hφ hφ1 m
    _ ≤ ∫⁻ _p, (replicaConstant ν a m)^n ∂ν :=
      lintegral_mono fun p => replica_integral_bound hν hsupport m p n hmargin
    _ = _ := by rw [lintegral_const, mul_comm]
end SmoothingMoments

section ProductDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

lemma measure_pi_withDensity (n : ℕ) (f : Fin n → X → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite (μ.withDensity (f i))] :
    Measure.pi (fun i => μ.withDensity (f i)) =
      (Measure.pi (fun _ : Fin n => μ)).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have he (x : Fin n → X) :
      (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x =
        ∏ i, (s i).indicator (f i) (x i) := by
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      have : ∃ i, x i ∉ s i := by simpa only [Set.mem_univ_pi, not_forall] using hx
      obtain ⟨i, hi⟩ := this
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  simp_rw [he]
  rw [lintegral_fin_prod μ n _ (fun i => (hf i).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]
end ProductDensity

lemma pi_gaussian_map_scale (m : ℕ) (δ : ℝ) :
    (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
      (fun u => fun j => δ * u j) =
      Measure.pi (fun _ : Fin m => gaussianReal 0 (NNReal.mk (δ^2) (sq_nonneg δ))) := by
  rw [Measure.pi_map_pi (f := fun _ : Fin m => fun x : ℝ => δ * x)
    (fun _ => (by fun_prop : Measurable (fun x : ℝ => δ * x)).aemeasurable)]
  simp_rw [gaussianReal_map_const_mul, mul_zero, mul_one]

lemma pi_gaussian_withDensity (m : ℕ) (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : Fin m => gaussianReal 0 v) =
      (volume : Measure (Fin m → ℝ)).withDensity (fun y => ∏ j, gaussianPDF 0 v (y j)) := by
  simp_rw [gaussianReal_of_var_ne_zero _ hv]
  have : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]
    infer_instance
  rw [measure_pi_withDensity (volume : Measure ℝ) m
    (fun _ => gaussianPDF 0 v) (fun _ => measurable_gaussianPDF 0 v)]
  rfl
lemma lintegral_gaussian_shift_scale (m : ℕ) (δ : ℝ) (hδ : δ ≠ 0)
    (a : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ u : Fin m → ℝ, f (fun j => a j + δ * u j)
      ∂Measure.pi (fun _ => gaussianReal 0 1) =
    ∫⁻ y : Fin m → ℝ, (∏ j, gaussianPDF 0 (NNReal.mk (δ^2) (sq_nonneg δ)) (y j - a j)) * f y := by
  let v : ℝ≥0 := NNReal.mk (δ^2) (sq_nonneg δ)
  have hv : v ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    exact pow_ne_zero 2 hδ
  have he :
      (∫⁻ u : Fin m → ℝ, f (fun j => a j + δ * u j)
        ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫⁻ y : Fin m → ℝ, f (a + y) ∂Measure.pi (fun _ => gaussianReal 0 v) := by
    rw [← pi_gaussian_map_scale m δ, lintegral_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he, pi_gaussian_withDensity m v hv,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have hh (y : Fin m → ℝ) :
      (∏ j, gaussianPDF 0 v (y j)) * f (a + y) =
      (fun z : Fin m → ℝ => (∏ j, gaussianPDF 0 v (z j - a j)) * f z) (a + y) := by
    simp only [Pi.add_apply, add_sub_cancel_left]
  exact (lintegral_congr (μ := volume) hh).trans (lintegral_add_left_eq_self
    (μ := volume) (fun z : Fin m → ℝ => (∏ j, gaussianPDF 0 v (z j - a j)) * f z) a)

section HolderSet
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
lemma withDensity_apply_le_moment (f : X → ℝ≥0∞) (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hC : ∫⁻ x, f x ^ p ∂μ ≤ C) (S : Set X) (hS : MeasurableSet S) :
    μ.withDensity f S ≤ C^(1/p) * (μ S)^(1 - 1/p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict S) hpq
    hf.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have he : 1 / (Real.conjExponent p) = 1 - 1/p := by
    have hh := hpq.inv_add_inv_eq_one
    simpa only [one_div] using (eq_sub_of_add_eq' hh)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul, he] at h
  rw [withDensity_apply _ hS]
  exact h.trans (mul_le_mul' (ENNReal.rpow_le_rpow
    ((lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans hC) (by positivity)) le_rfl)
end HolderSet

section LimitSet
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [BorelSpace Y]
  (ρ : Measure X) (τ : Measure Y)

lemma map_apply_open_le_of_tendsto (F : X → Y) (Fₖ : ℕ → X → Y)
    (hF : Measurable F) (hFₖ : ∀ k, Measurable (Fₖ k))
    (ht : ∀ x, Tendsto (fun k => Fₖ k x) atTop (𝓝 (F x)))
    (C : ℝ≥0∞) (α : ℝ)
    (hbound : ∀ k U, IsOpen U → (ρ.map (Fₖ k)) U ≤ C * (τ U)^α)
    (U : Set Y) (hU : IsOpen U) :
    (ρ.map F) U ≤ C * (τ U)^α := by
  let f : ℕ → X → ℝ≥0∞ := fun k => (Fₖ k ⁻¹' U).indicator (fun _ => 1)
  have hf : ∀ k, Measurable (f k) := fun k =>
    measurable_const.indicator (hU.measurableSet.preimage (hFₖ k))
  have hind : ∀ x, (F ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
      atTop.liminf (fun k => f k x) := by
    intro x
    by_cases hx : F x ∈ U
    · rw [Set.indicator_of_mem (show x ∈ F ⁻¹' U from hx)]
      apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [(ht x).eventually (hU.mem_nhds hx)] with k hk
      change 1 ≤ (Fₖ k ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x
      rw [Set.indicator_of_mem (show x ∈ Fₖ k ⁻¹' U from hk)]
    · rw [Set.indicator_of_notMem (show x ∉ F ⁻¹' U from hx)]
      exact zero_le
  calc
    (ρ.map F) U = ∫⁻ x, (F ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ρ := by
      rw [Measure.map_apply hF hU.measurableSet,
        lintegral_indicator (hU.measurableSet.preimage hF)]
      simp
    _ ≤ ∫⁻ x, atTop.liminf (fun k => f k x) ∂ρ := lintegral_mono hind
    _ ≤ atTop.liminf (fun k => ∫⁻ x, f k x ∂ρ) := lintegral_liminf_le hf
    _ ≤ _ := by
      apply liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
      apply Filter.Eventually.frequently
      filter_upwards [] with k
      have hk := hbound k U hU
      simpa [f, lintegral_indicator (hU.measurableSet.preimage (hFₖ k)),
        Measure.map_apply (hFₖ k) hU.measurableSet] using hk
end LimitSet

variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]

lemma ennreal_rpow_iInf {ι : Sort*} (f : ι → ℝ≥0∞) {α : ℝ} (hα : 0 < α) :
    (⨅ i, f i)^α = ⨅ i, (f i)^α :=
  (ENNReal.orderIsoRpow α hα).map_iInf f

lemma measure_apply_le_of_isOpen (μ τ : Measure Y) [τ.OuterRegular]
    {C : ℝ≥0∞} (hC : C ≠ ∞) {α : ℝ} (hα : 0 < α)
    (hbound : ∀ U, IsOpen U → μ U ≤ C * (τ U)^α) (S : Set Y) :
    μ S ≤ C * (τ S)^α := by
  by_cases hC0 : C = 0
  · simp only [hC0, zero_mul] at hbound ⊢
    exact (measure_mono (Set.subset_univ S)).trans (hbound Set.univ isOpen_univ)
  rw [S.measure_eq_iInf_isOpen τ]
  simp_rw [ennreal_rpow_iInf _ hα, ENNReal.mul_iInf_of_ne hC0 hC]
  exact le_iInf fun U => le_iInf fun hSU => le_iInf fun hU =>
    (measure_mono hSU).trans (hbound U hU)

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Exact noiseless projection laws and completed-event bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section


namespace NoiselessRegression

section ProjectionCoupling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def matrixLabelReference (m : ℕ) : Measure ((Fin m → E) × (Fin m → ℝ)) :=
  (Measure.pi (fun _ => stdGaussian E)).prod volume

def projectionLaw (ν : Measure E) (m : ℕ) : Measure ((Fin m → E) × (Fin m → ℝ)) :=
  ((Measure.pi (fun _ => stdGaussian E)).prod ν).map
    (fun z => (z.1, fun j => ⟪z.2, z.1 j⟫))

def gaussianCoupling (ν : Measure E) (m : ℕ) :
    Measure ((Fin m → E) × (E × (Fin m → ℝ))) :=
  (Measure.pi (fun _ => stdGaussian E)).prod
    (ν.prod (Measure.pi (fun _ => gaussianReal 0 1)))

def noisyObservation (m : ℕ) (δ : ℝ)
    (z : (Fin m → E) × (E × (Fin m → ℝ))) : (Fin m → E) × (Fin m → ℝ) :=
  (z.1, fun j => ⟪z.2.1, z.1 j⟫ + δ * z.2.2 j)

lemma measurable_noisyObservation (m : ℕ) (δ : ℝ) :
    Measurable (noisyObservation (E := E) m δ) := by
  unfold noisyObservation
  fun_prop

lemma gaussianCoupling_map_noisyObservation_zero (ν : Measure E) [SigmaFinite ν] (m : ℕ) :
    (gaussianCoupling ν m).map (noisyObservation m 0) = projectionLaw ν m := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_noisyObservation m 0),
    projectionLaw, lintegral_map hf (by fun_prop)]
  dsimp [gaussianCoupling, noisyObservation]
  simp only [zero_mul, add_zero]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro A
  rw [lintegral_prod _ (by fun_prop)]
  simp

lemma gaussianCoupling_map_noisyObservation (ν : Measure E) [SigmaFinite ν]
    (m : ℕ) (δ : ℝ) (hδ : δ ≠ 0) :
    (gaussianCoupling ν m).map (noisyObservation m δ) =
      (matrixLabelReference (E := E) m).withDensity
        (projectionSmoothing ν (gaussianPDF 0 (NNReal.mk (δ^2) (sq_nonneg δ))) m) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_noisyObservation m δ),
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _) hf]
  dsimp [gaussianCoupling, matrixLabelReference, noisyObservation]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by
    exact ((measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _).mul hf).aemeasurable)]
  apply lintegral_congr
  intro A
  rw [lintegral_prod _ (by fun_prop)]
  have he (p : E) := lintegral_gaussian_shift_scale m δ hδ
    (fun j => ⟪p, A j⟫) (fun y => f (A, y)) (hf.comp (measurable_const.prodMk measurable_id))
  simp_rw [he]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro y
  rw [lintegral_mul_const _ (by fun_prop)]
  rfl
lemma matrixLabelReference_outerRegular (m : ℕ) :
    (matrixLabelReference (E := E) m).OuterRegular := by
  unfold matrixLabelReference
  exact (Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _).toOuterRegular

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tendsto_noisyObservation (m : ℕ)
    (z : (Fin m → E) × (E × (Fin m → ℝ))) :
    Tendsto (fun k : ℕ => noisyObservation m (1 / ((k : ℝ) + 1)) z)
      atTop (𝓝 (noisyObservation m 0 z)) := by
  apply Filter.Tendsto.prodMk_nhds tendsto_const_nhds
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_const_nhds.add
    (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _)

theorem projectionLaw_set_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hn : 1 ≤ n) (hmargin : (n : ℝ) + m ≤ a)
    (S : Set ((Fin m → E) × (Fin m → ℝ))) :
    projectionLaw ν m S ≤
      (ν Set.univ * (replicaConstant ν a m)^n)^(1 / ((n : ℝ) + 1)) *
      (matrixLabelReference (E := E) m S)^(1 - 1 / ((n : ℝ) + 1)) := by
  have hp : 1 < (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 < n + 1)
  have hα : 0 < 1 - 1 / ((n : ℝ) + 1) := by
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hp)
  have hC : ν Set.univ * (replicaConstant ν a m)^n ≠ ∞ := by
    unfold replicaConstant
    finiteness
  have := matrixLabelReference_outerRegular (E := E) m
  apply measure_apply_le_of_isOpen _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hC) hα
  intro U hU
  rw [← gaussianCoupling_map_noisyObservation_zero ν m]
  apply map_apply_open_le_of_tendsto (gaussianCoupling ν m)
    (matrixLabelReference (E := E) m) (noisyObservation m 0)
    (fun k => noisyObservation m (1 / ((k : ℝ) + 1)))
    (measurable_noisyObservation m 0) (fun k => measurable_noisyObservation m _)
    (tendsto_noisyObservation m) _ _ (U := U) (hU := hU)
  intro k V hV
  have hδ : (1 / ((k : ℝ) + 1)) ≠ 0 := by positivity
  rw [gaussianCoupling_map_noisyObservation ν m _ hδ]
  apply withDensity_apply_le_moment _ _
    (measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _) hp _ _ hV.measurableSet
  have hv : (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
      (sq_nonneg (1 / ((k : ℝ) + 1)))) ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    exact pow_ne_zero 2 hδ
  simpa only [← ENNReal.rpow_natCast, Nat.cast_add, Nat.cast_one, matrixLabelReference]
    using projectionSmoothing_moment hν hsupport
      (gaussianPDF 0 (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
        (sq_nonneg (1 / ((k : ℝ) + 1))))) (measurable_gaussianPDF _ _)
      (lintegral_gaussianPDF_eq_one _ hv) m n hmargin

end ProjectionCoupling

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Finite-volume enclosures for Gaussian matrix observations.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section


namespace NoiselessRegression

open scoped Pointwise

def coordinateNorm {m : ℕ} (y : Fin m → ℝ) : ℝ := ‖WithLp.toLp 2 y‖

@[fun_prop] lemma continuous_coordinateNorm {m : ℕ} :
    Continuous (coordinateNorm (m := m)) := by
  unfold coordinateNorm
  fun_prop

lemma coordinateNorm_sq {m : ℕ} (y : Fin m → ℝ) :
    coordinateNorm y ^ 2 = ∑ j, (y j)^2 := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y)

lemma coordinateNorm_smul {m : ℕ} (c : ℝ) (y : Fin m → ℝ) :
    coordinateNorm (c • y) = |c| * coordinateNorm y := by
  simp [coordinateNorm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

def coordinateBall (m : ℕ) (r : ℝ) : Set (Fin m → ℝ) :=
  {y | coordinateNorm y ≤ r}

lemma measurableSet_coordinateBall (m : ℕ) (r : ℝ) :
    MeasurableSet (coordinateBall m r) :=
  measurableSet_le continuous_coordinateNorm.measurable measurable_const

lemma coordinateBall_smul (m : ℕ) (c r : ℝ) (hc : 0 < c) :
    coordinateBall m (c * r) = c • coordinateBall m r := by
  ext y
  constructor
  · intro hy
    refine ⟨c⁻¹ • y, ?_, by simp [hc.ne']⟩
    change coordinateNorm (c⁻¹ • y) ≤ r
    rw [coordinateNorm_smul, abs_of_pos (inv_pos.mpr hc)]
    exact (inv_mul_le_iff₀ hc).mpr hy
  · rintro ⟨y, hy, rfl⟩
    change coordinateNorm (c • y) ≤ c * r
    rw [coordinateNorm_smul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hy hc.le

lemma volume_coordinateBall_smul (m : ℕ) (c r : ℝ) (hc : 0 < c) :
    volume (coordinateBall m (c * r)) =
      ENNReal.ofReal (c^m) * volume (coordinateBall m r) := by
  rw [coordinateBall_smul m c r hc, Measure.addHaar_smul_of_nonneg volume hc.le]
  simp

lemma gaussianPDF_le_exp (x : ℝ) :
    gaussianPDF 0 1 x ≤ ENNReal.ofReal (Real.exp (-(x^2)/2)) := by
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  apply mul_le_of_le_one_left (Real.exp_nonneg _)
  apply inv_le_one_of_one_le₀
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  nlinarith [Real.pi_gt_three]

lemma lintegral_quarterGaussian_le :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(x^2)/4))) ≤ 4 := by
  have he : (fun x : ℝ => Real.exp (-(x^2)/4)) =
      (fun x : ℝ => Real.exp (-(1/4 : ℝ) * x^2)) := by
    ext x
    congr 1
    ring
  simp_rw [show ∀ x : ℝ, Real.exp (-(x^2)/4) = Real.exp (-(1/4 : ℝ) * x^2) from congrFun he]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_neg_mul_sq (by norm_num)) (by filter_upwards [] with x; positivity),
    integral_gaussian]
  have hs : Real.sqrt (Real.pi / (1/4 : ℝ)) ≤ 4 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [Real.pi_lt_four]
  exact (ENNReal.ofReal_le_ofReal hs).trans_eq (by norm_num)

lemma gaussian_density_pair_bound {m : ℕ} (x y : Fin m → ℝ)
    (h : coordinateNorm y ≤ coordinateNorm x) :
    (∏ j, gaussianPDF 0 1 (x j)) ≤
      (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4))) *
      ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4)) := by
  calc
    _ ≤ ∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/2)) :=
      Finset.prod_le_prod' fun j _ => gaussianPDF_le_exp (x j)
    _ = ENNReal.ofReal (Real.exp (- (∑ j, (x j)^2) / 2)) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _), ← Real.exp_sum]
      congr 2
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
    _ ≤ ENNReal.ofReal (Real.exp (- (∑ j, (x j)^2)/4 - (∑ j, (y j)^2)/4)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hn : 0 ≤ coordinateNorm y := norm_nonneg _
      have hs := pow_le_pow_left₀ hn h 2
      rw [coordinateNorm_sq, coordinateNorm_sq] at hs
      linarith
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _),
        ← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _),
        ← Real.exp_sum, ← Real.exp_sum, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← Real.exp_add]
      congr 2
      simp only [← Finset.sum_div, Finset.sum_neg_distrib]
      ring

lemma measurable_coordinateVolume (m : ℕ) : Measurable (fun x : Fin m → ℝ => volume (coordinateBall m (coordinateNorm x))) := by
  have : Measurable (fun z : (Fin m → ℝ) × (Fin m → ℝ) =>
      ({z | coordinateNorm z.2 ≤ coordinateNorm z.1} : Set _).indicator
        (fun _ => (1 : ℝ≥0∞)) z) :=
    measurable_const.indicator (measurableSet_le (by fun_prop) (by fun_prop))
  change Measurable (Function.uncurry (fun x y : Fin m → ℝ =>
    (coordinateBall m (coordinateNorm x)).indicator (fun _ => (1 : ℝ≥0∞)) y)) at this
  convert this.lintegral_prod_right (ν := (volume : Measure (Fin m → ℝ))) using 1
  ext x
  rw [lintegral_indicator (measurableSet_coordinateBall m _)]
  simp

lemma gaussian_expected_coordinate_volume (m : ℕ) :
    (∫⁻ x : Fin m → ℝ, volume (coordinateBall m (coordinateNorm x))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤ (16 : ℝ≥0∞)^m := by
  have hB := measurable_coordinateVolume m
  rw [pi_gaussian_withDensity m 1 (by norm_num),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hB]
  have hi (x : Fin m → ℝ) :
      (∏ j, gaussianPDF 0 1 (x j)) * volume (coordinateBall m (coordinateNorm x)) =
      ∫⁻ y : Fin m → ℝ, (coordinateBall m (coordinateNorm x)).indicator
        (fun _ => ∏ j, gaussianPDF 0 1 (x j)) y := by
    rw [lintegral_indicator (measurableSet_coordinateBall m _)]
    simp
  simp only [Pi.mul_apply]
  simp_rw [hi]
  calc
    _ ≤ ∫⁻ x : Fin m → ℝ, ∫⁻ y : Fin m → ℝ,
      (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4))) *
        ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4)) := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ coordinateBall m (coordinateNorm x)
      · rw [Set.indicator_of_mem hy]
        exact gaussian_density_pair_bound x y hy
      · rw [Set.indicator_of_notMem hy]
        exact zero_le
    _ = ((∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z^2)/4)))^m)^2 := by
      have hJ : (∫⁻ y : Fin m → ℝ, ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4))) =
          (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z^2)/4)))^m := by
        rw [volume_pi, lintegral_fin_prod volume m
          (fun _ => fun z : ℝ => ENNReal.ofReal (Real.exp (-(z^2)/4))) (fun _ => by fun_prop)]
        simp
      have hj (x : Fin m → ℝ) := lintegral_const_mul (μ := volume)
        (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4)))
        (by fun_prop : Measurable (fun y : Fin m → ℝ =>
          ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4))))
      simp_rw [hj, hJ]
      rw [lintegral_mul_const _ (by fun_prop), hJ, pow_two]
    _ ≤ ((4 : ℝ≥0∞)^m)^2 := pow_le_pow_left₀ (by positivity)
      (pow_le_pow_left₀ (by positivity) lintegral_quarterGaussian_le m) 2
    _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num

section Rows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_inner_map (u : E) :
    (stdGaussian E).map (fun x => ⟪u, x⟫) =
      gaussianReal 0 (NNReal.mk (‖u‖^2) (sq_nonneg ‖u‖)) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ u)
  have he : (⇑(innerSL ℝ u)) = (fun x => ⟪u, x⟫) := by
    ext x
    exact innerSL_apply_apply ℝ u x
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at h
  rw [he] at h
  have hh : (‖u‖^2).toNNReal = NNReal.mk (‖u‖^2) (sq_nonneg ‖u‖) := by
    ext
    simp
  simpa only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, hh] using h

lemma rows_inner_map (u : E) (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map
      (fun A => fun j => ⟪u, A j⟫) =
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
        (fun x => ‖u‖ • x) := by
  rw [Measure.pi_map_pi (f := fun _ : Fin m => fun x : E => ⟪u, x⟫)
    (fun _ => (by fun_prop : Measurable (fun x : E => ⟪u, x⟫)).aemeasurable)]
  simp_rw [stdGaussian_inner_map]
  exact (pi_gaussian_map_scale m ‖u‖).symm

lemma rows_expected_coordinate_volume (u : E) (hu : ‖u‖ ≤ 1) (m : ℕ) :
    (∫⁻ A : Fin m → E, volume (coordinateBall m (coordinateNorm (fun j => ⟪u, A j⟫)))
      ∂Measure.pi (fun _ => stdGaussian E)) ≤ (16 : ℝ≥0∞)^m := by
  have h := congrArg (fun μ : Measure (Fin m → ℝ) =>
    ∫⁻ y, volume (coordinateBall m (coordinateNorm y)) ∂μ) (rows_inner_map u m)
  rw [lintegral_map (measurable_coordinateVolume m) (by fun_prop),
    lintegral_map (measurable_coordinateVolume m) (by fun_prop)] at h
  rw [h]
  apply le_trans _ (gaussian_expected_coordinate_volume m)
  apply lintegral_mono
  intro x
  apply measure_mono
  intro y hy
  change coordinateNorm y ≤ coordinateNorm x
  apply le_trans hy
  rw [coordinateNorm_smul, abs_of_nonneg (norm_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) hu

def rowOperator {m : ℕ} (A : Fin m → E) : E →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => innerSL ℝ (A j)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowOperator_apply {m : ℕ} (A : Fin m → E) (t : E) :
    rowOperator A t = WithLp.toLp 2 (fun j => ⟪t, A j⟫) := by
  ext j
  exact real_inner_comm _ _

def netProjectionSupport (s : Finset E) (m : ℕ) :
    Set ((Fin m → E) × (Fin m → ℝ)) :=
  ⋃ u ∈ s, {z | coordinateNorm z.2 ≤ 2 * coordinateNorm (fun j => ⟪u, z.1 j⟫)}

lemma measurableSet_netProjectionSupport (s : Finset E) (m : ℕ) :
    MeasurableSet (netProjectionSupport s m) := by
  apply MeasurableSet.biUnion s.countable_toSet
  intro u _
  exact measurableSet_le (by fun_prop) (by fun_prop)

lemma netProjectionSupport_volume (s : Finset E) (hs : ∀ u ∈ s, ‖u‖ ≤ 1) (m : ℕ) :
    matrixLabelReference (E := E) m (netProjectionSupport s m) ≤
      (s.card : ℝ≥0∞) * (32 : ℝ≥0∞)^m := by
  classical
  apply (measure_biUnion_finset_le s _).trans
  calc
    _ ≤ ∑ _u ∈ s, (32 : ℝ≥0∞)^m := by
      apply Finset.sum_le_sum
      intro u hu
      rw [matrixLabelReference, Measure.prod_apply (measurableSet_le (by fun_prop) (by fun_prop))]
      change (∫⁻ A : Fin m → E,
        volume (coordinateBall m (2 * coordinateNorm (fun j => ⟪u, A j⟫)))
        ∂Measure.pi (fun _ => stdGaussian E)) ≤ _
      simp_rw [volume_coordinateBall_smul m 2 _ (by norm_num)]
      have hme : Measurable (fun A : Fin m → E =>
          volume (coordinateBall m (coordinateNorm (fun j => ⟪u, A j⟫)))) :=
        (measurable_coordinateVolume m).comp (by fun_prop)
      rw [lintegral_const_mul _ hme]
      calc
        _ ≤ ENNReal.ofReal ((2 : ℝ)^m) * (16 : ℝ≥0∞)^m :=
          mul_le_mul' le_rfl (rows_expected_coordinate_volume u (hs u hu) m)
        _ = _ := by rw [ENNReal.ofReal_pow (by norm_num)]; norm_num [← mul_pow]
    _ = _ := by simp
end Rows

section NetNorm
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma opNorm_le_twice_net (f : E →L[ℝ] F) (s : Finset E)
    (hnet : ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ 1/2) :
    ‖f‖ ≤ 2 * (s.sup (fun u => ‖f u‖₊) : ℝ≥0) := by
  classical
  let K : ℝ := (s.sup (fun u => ‖f u‖₊) : ℝ≥0)
  have hK : 0 ≤ K := NNReal.coe_nonneg _
  have hbound : ‖f‖ ≤ K + ‖f‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx.le
    have hfy : ‖f y‖ ≤ K := by
      exact_mod_cast (Finset.le_sup (f := fun u => ‖f u‖₊) hy)
    calc
      ‖f x‖ = ‖f y + f (x-y)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖f y‖ + ‖f (x-y)‖ := norm_add_le _ _
      _ ≤ K + ‖f‖ * (1/2) := add_le_add hfy
        ((f.le_opNorm (x-y)).trans (mul_le_mul_of_nonneg_left
          (by simpa [dist_eq_norm] using hxy) (norm_nonneg _)))
      _ = _ := by ring
  dsimp [K] at hbound
  linarith
end NetNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_projection_support (m : ℕ) (hm : m ≤ Module.finrank ℝ E) :
    ∃ D : Set ((Fin m → E) × (Fin m → ℝ)), MeasurableSet D ∧
      (∀ A t, ‖t‖ ≤ 1 → (A, fun j => ⟪t, A j⟫) ∈ D) ∧
      matrixLabelReference (E := E) m D ≤ (192 : ℝ≥0∞)^(Module.finrank ℝ E) := by
  classical
  obtain ⟨s, hs, hc, hnet⟩ := exists_unit_ball_net (E := E)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  have hsne : s.Nonempty := by
    obtain ⟨u, hu, _⟩ := hnet 0 (by simp)
    exact ⟨u, hu⟩
  refine ⟨netProjectionSupport s m, measurableSet_netProjectionSupport s m, ?_, ?_⟩
  · intro A t ht
    obtain ⟨u, hu, he⟩ := s.exists_mem_eq_sup hsne (fun u => ‖rowOperator A u‖₊)
    refine Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, ?_⟩⟩
    change coordinateNorm (fun j => ⟪t, A j⟫) ≤
      2 * coordinateNorm (fun j => ⟪u, A j⟫)
    change ‖WithLp.toLp 2 (fun j => ⟪t, A j⟫)‖ ≤
      2 * ‖WithLp.toLp 2 (fun j => ⟪u, A j⟫)‖
    rw [← rowOperator_apply, ← rowOperator_apply]
    calc
      _ ≤ ‖rowOperator A‖ * ‖t‖ := (rowOperator A).le_opNorm t
      _ ≤ ‖rowOperator A‖ := mul_le_of_le_one_right (norm_nonneg _) ht
      _ ≤ _ := by simpa [he] using opNorm_le_twice_net (rowOperator A) s hnet
  · apply (netProjectionSupport_volume s hs m).trans
    have hcard : (s.card : ℝ≥0∞) ≤ (6 : ℝ≥0∞)^(Module.finrank ℝ E) := by
      have h : (s.card : ℝ) ≤ (6 : ℝ)^(Module.finrank ℝ E) := by norm_num at hc ⊢; exact hc
      simpa using ENNReal.ofReal_le_ofReal h
    calc
      _ ≤ (6 : ℝ≥0∞)^Module.finrank ℝ E * (32 : ℝ≥0∞)^Module.finrank ℝ E :=
        mul_le_mul' hcard (pow_le_pow_right₀ (by norm_num) hm)
      _ = _ := by rw [← mul_pow]; norm_num

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Localization, finite selection, and block mass propagation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section


namespace NoiselessRegression

section Block
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def PolynomialMass (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ z : E, ∀ r : ℝ, 0 < r → ν (Metric.closedBall z r) ≤ C * ENNReal.ofReal (r^a)

def localNormalize (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) (z : E) (r : ℝ) : Measure E :=
  (C * ENNReal.ofReal (r^a))⁻¹ • (ν.restrict (Metric.closedBall z r)).map (fun x => r⁻¹ • (x-z))

omit [FiniteDimensional ℝ E] in
lemma localNormalize_univ {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    localNormalize ν a C z r univ ≤ 1 := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  simp only [localNormalize, Measure.smul_apply, smul_eq_mul, Measure.map_apply (by fun_prop : Measurable (fun x : E => r⁻¹ • (x-z))) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact (mul_le_mul' le_rfl (hν z r hr)).trans_eq (ENNReal.inv_mul_cancel hc0 hct)

omit [FiniteDimensional ℝ E] in
lemma localNormalize_finite {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    IsFiniteMeasure (localNormalize ν a C z r) :=
  ⟨(localNormalize_univ hν hC hCt z hr).trans_lt (by simp)⟩

omit [FiniteDimensional ℝ E] in
lemma localNormalize_support (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) (z : E) {r : ℝ} (hr : 0 < r) :
    (localNormalize ν a C z r).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, localNormalize, Measure.smul_apply, Measure.map_apply (by fun_prop)
    Metric.isClosed_closedBall.measurableSet.compl,
    Measure.restrict_apply ((by fun_prop : Measurable (fun x : E => r⁻¹ • (x-z)))
      Metric.isClosed_closedBall.measurableSet.compl)]
  have he : (fun x : E => r⁻¹ • (x-z)) ⁻¹' (Metric.closedBall 0 1)ᶜ ∩ Metric.closedBall z r = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x ⟨hx,hb⟩
    apply hx
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_iff₀ hr).2 (by simpa [dist_eq_norm] using hb)
  rw [he, measure_empty, smul_zero]

omit [FiniteDimensional ℝ E] in
lemma localNormalize_local {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    HasLocalMassBound (localNormalize ν a C z r) (a : ℝ) := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  intro t _ ρ hρ
  rw [localNormalize, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
  have hsub : (fun x : E => r⁻¹ • (x-z)) ⁻¹' Metric.closedBall t ρ ⊆
      Metric.closedBall (z + r • t) (r*ρ) := by
    intro x hx
    have he : x - (z+r • t) = r • (r⁻¹ • (x-z) - t) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    rw [Metric.mem_closedBall, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (by simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm] using hx) hr.le
  calc
    _ ≤ (C * ENNReal.ofReal (r^a))⁻¹ * ν (Metric.closedBall (z+r • t) (r*ρ)) :=
      mul_le_mul' le_rfl ((Measure.restrict_le_self _).trans (measure_mono hsub))
    _ ≤ (C * ENNReal.ofReal (r^a))⁻¹ * (C * ENNReal.ofReal ((r*ρ)^a)) :=
      mul_le_mul' le_rfl (hν _ _ (mul_pos hr hρ))
    _ = ENNReal.ofReal (ρ^(a : ℝ)) := by
      rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hr.le a), ← mul_assoc C,
        ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul, Real.rpow_natCast]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma replicaConstant_le {ν : Measure E} (hν : ν univ ≤ 1) {a m : ℕ}
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E) :
    replicaConstant ν (a : ℝ) m ≤ (128 : ℝ≥0∞) ^ Module.finrank ℝ E := by
  let d := Module.finrank ℝ E
  have h2 : (2 : ℝ≥0∞) ≤ 2^d := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) hd
  have hp : (2 : ℝ≥0∞)^(m+1) ≤ 4^d := by
    rw [pow_succ]
    calc
      _ ≤ (2 : ℝ≥0∞)^d * 2^d := mul_le_mul' (pow_le_pow_right₀ (by norm_num) hm) h2
      _ = _ := by rw [← mul_pow]; norm_num
  calc
    replicaConstant ν (a : ℝ) m ≤ 1 + (4 : ℝ≥0∞)^d * 4^d * 4^d := by
      unfold replicaConstant
      rw [Real.rpow_natCast, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_pow (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat]
      gcongr <;> norm_num
    _ = 1 + (64 : ℝ≥0∞)^d := by rw [mul_assoc, ← mul_pow, ← mul_pow]; norm_num
    _ ≤ (2 : ℝ≥0∞) * 64^d := by
      rw [two_mul]
      exact add_le_add (one_le_pow₀ (by norm_num)) le_rfl
    _ ≤ (2 : ℝ≥0∞)^d * 64^d := mul_le_mul' h2 le_rfl
    _ = _ := by rw [← mul_pow]; norm_num; rfl

lemma projectionLaw_uniform_set_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a m n : ℕ} (hν : HasLocalMassBound ν (a : ℝ)) (hν1 : ν univ ≤ 1)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E)
    (hn : 1 ≤ n) (hmargin : n+m ≤ a) (S : Set ((Fin m → E) × (Fin m → ℝ))) :
    projectionLaw ν m S ≤ (128 : ℝ≥0∞) ^ Module.finrank ℝ E *
      (matrixLabelReference (E := E) m S)^(1 - 1 / ((n : ℝ)+1)) := by
  apply (projectionLaw_set_bound hν hsupport m n hn (by exact_mod_cast hmargin) S).trans
  apply mul_le_mul' _ le_rfl
  have hn0 : (0 : ℝ) < n+1 := by positivity
  calc
    _ ≤ (((128 : ℝ≥0∞)^Module.finrank ℝ E) ^ n)^(1 / ((n : ℝ)+1)) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      simpa only [one_mul] using mul_le_mul' hν1 (pow_le_pow_left' (replicaConstant_le hν1 hd ha hm) n)
    _ = ((128 : ℝ≥0∞)^Module.finrank ℝ E)^((n : ℝ)/(n+1)) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      congr 1
      rw [mul_one_div]
    _ ≤ ((128 : ℝ≥0∞)^Module.finrank ℝ E)^(1 : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
        ((div_le_one hn0).2 (by linarith))
    _ = _ := ENNReal.rpow_one _

lemma finite_rpow_holder {J : Type*} [Fintype J] (a : J → ℝ≥0∞) {q : ℝ} (hq : 1 < q) :
    (∑ j, a j ^ (1 - 1/q)) ≤
      (Fintype.card J : ℝ≥0∞)^(1/q) * (∑ j, a j)^(1-1/q) := by
  have hh := Real.HolderConjugate.conjExponent hq
  have hq' : q.conjExponent ≠ 0 := ne_of_gt hh.symm.pos
  have hex : 1 - 1/q = q.conjExponent⁻¹ := by simpa only [one_div] using hh.one_sub_inv
  rw [hex]
  simpa only [one_mul, one_div, ENNReal.one_rpow, ENNReal.rpow_inv_rpow hq',
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    ENNReal.inner_le_Lp_mul_Lq Finset.univ (fun _ : J => (1 : ℝ≥0∞))
      (fun j => a j ^ q.conjExponent⁻¹) hh

lemma normalized_routing_bound {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (ν : J → Measure E) [∀ j, IsFiniteMeasure (ν j)]
    {a m n : ℕ} (hν : ∀ j, HasLocalMassBound (ν j) (a : ℝ))
    (hν1 : ∀ j, ν j univ ≤ 1) (hsupport : ∀ j, (ν j).support ⊆ Metric.closedBall 0 1)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (hφ : Measurable φ) :
    (∑ j, projectionLaw (ν j) m {x | φ x = j}) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) := by
  classical
  obtain ⟨D, hD, hDs, hDV⟩ := exists_projection_support (E := E) m hm
  let S : J → Set ((Fin m → E) × (Fin m → ℝ)) := fun j => D ∩ {x | φ x = j}
  have hS (j : J) : MeasurableSet (S j) := hD.inter (hφ (measurableSet_singleton j))
  have hSD (j : J) : projectionLaw (ν j) m (S j) = projectionLaw (ν j) m {x | φ x = j} := by
    apply Measure.measure_inter_eq_of_ae
    unfold projectionLaw
    apply (ae_map_iff (by fun_prop) hD).2
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ν j).support_mem_ae] with x hx
    exact hDs x.1 x.2 (by simpa using hsupport j hx)
  have hdis : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hUnion : (⋃ j, S j) = D := by
    ext x
    simp only [S, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_,h,_⟩ => h, fun h => ⟨φ x,h,rfl⟩⟩
  have hsum : ∑ j, matrixLabelReference (E := E) m (S j) = matrixLabelReference (E := E) m D := by
    simpa only [hUnion, tsum_fintype] using (measure_iUnion (μ := matrixLabelReference (E := E) m) hdis hS).symm
  have hα : 0 ≤ 1 - 1/((n : ℝ)+1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ n+1)]
  have hV : (matrixLabelReference (E := E) m D)^(1-1/((n : ℝ)+1)) ≤
      (256 : ℝ≥0∞)^Module.finrank ℝ E := by
    calc
      _ ≤ ((256 : ℝ≥0∞)^Module.finrank ℝ E)^(1-1/((n : ℝ)+1)) :=
        ENNReal.rpow_le_rpow (hDV.trans (pow_le_pow_left' (by norm_num) _)) hα
      _ ≤ ((256 : ℝ≥0∞)^Module.finrank ℝ E)^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (sub_le_self _ (by positivity))
      _ = _ := ENNReal.rpow_one _
  calc
    _ = ∑ j, projectionLaw (ν j) m (S j) := by simp_rw [hSD]
    _ ≤ ∑ j, (128 : ℝ≥0∞)^Module.finrank ℝ E *
        (matrixLabelReference (E := E) m (S j))^(1-1/((n : ℝ)+1)) :=
      Finset.sum_le_sum fun j _ => projectionLaw_uniform_set_bound
        (hν j) (hν1 j) (hsupport j) hd ha hm hn hmargin (S j)
    _ = (128 : ℝ≥0∞)^Module.finrank ℝ E *
        ∑ j, (matrixLabelReference (E := E) m (S j))^(1-1/((n : ℝ)+1)) := by rw [Finset.mul_sum]
    _ ≤ (128 : ℝ≥0∞)^Module.finrank ℝ E *
        ((Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) *
         (∑ j, matrixLabelReference (E := E) m (S j))^(1-1/((n : ℝ)+1))) :=
      mul_le_mul' le_rfl (finite_rpow_holder _ (by exact_mod_cast Nat.lt_add_one_of_le hn))
    _ ≤ (128 : ℝ≥0∞)^Module.finrank ℝ E *
        ((Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) * (256 : ℝ≥0∞)^Module.finrank ℝ E) := by
      rw [hsum]
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hV)
    _ = _ := by rw [mul_left_comm, ← mul_pow]; norm_num; rw [mul_comm]

omit [FiniteDimensional ℝ E] in
lemma localNormalize_reconstruct (ν : Measure E) (a : ℕ) {C : ℝ≥0∞}
    (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    (C * ENNReal.ofReal (r^a)) • (localNormalize ν a C z r).map (fun t => z+r • t) =
      ν.restrict (Metric.closedBall z r) := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  rw [localNormalize, Measure.map_smul, smul_smul, ENNReal.mul_inv_cancel hc0 hct,
    one_smul, Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun t : E => z+r • t) ∘ (fun x => r⁻¹ • (x-z)) = id := by
    ext x
    simp [smul_smul, hr.ne']
  rw [he, Measure.map_id]

lemma projectionLaw_smul (ν : Measure E) [SFinite ν] (m : ℕ) (c : ℝ≥0∞) :
    projectionLaw (c • ν) m = c • projectionLaw ν m := by
  rw [projectionLaw, Measure.prod_smul_right, Measure.map_smul]
  rfl

lemma projectionLaw_affine (ν : Measure E) [SFinite ν] (m : ℕ) (z : E) (r : ℝ) :
    projectionLaw (ν.map (fun t => z + r • t)) m =
      (projectionLaw ν m).map (fun x => (x.1, fun j => ⟪z,x.1 j⟫ + r * x.2 j)) := by
  unfold projectionLaw
  rw [← Measure.map_id (μ := Measure.pi (fun _ : Fin m => stdGaussian E)),
    Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_id, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x <;> simp [inner_add_left, real_inner_smul_left]

lemma localized_routing_bound {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (ν : J → Measure E) [∀ j, IsFiniteMeasure (ν j)]
    {a m n : ℕ} {C : ℝ≥0∞} (hν : ∀ j, PolynomialMass (ν j) a C)
    (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (hφ : Measurable φ)
    (z : E) {r : ℝ} (hr : 0 < r) :
    (∑ j, projectionLaw ((ν j).restrict (Metric.closedBall z r)) m {x | φ x = j}) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) *
        C * ENNReal.ofReal (r^a) := by
  let τ (j : J) := localNormalize (ν j) a C z r
  let F : ((Fin m → E) × (Fin m → ℝ)) → ((Fin m → E) × (Fin m → ℝ)) :=
    fun x => (x.1, fun i => ⟪z,x.1 i⟫ + r * x.2 i)
  have hF : Measurable F := by fun_prop
  let (j : J) : IsFiniteMeasure (τ j) := localNormalize_finite (hν j) hC hCt z hr
  have hb := normalized_routing_bound τ
    (fun j => localNormalize_local (hν j) hC hCt z hr)
    (fun j => localNormalize_univ (hν j) hC hCt z hr)
    (fun j => localNormalize_support (ν j) a C z hr) hd ha hm hn hmargin (φ ∘ F) (hφ.comp hF)
  have he (j : J) : projectionLaw ((ν j).restrict (Metric.closedBall z r)) m {x | φ x = j} =
      (C * ENNReal.ofReal (r^a)) * projectionLaw (τ j) m {x | φ (F x) = j} := by
    rw [← localNormalize_reconstruct (ν j) a hC hCt z hr, projectionLaw_smul,
      projectionLaw_affine, Measure.smul_apply, smul_eq_mul, Measure.map_apply hF
      (measurableSet_eq_fun hφ measurable_const)]
    rfl
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact (mul_le_mul' le_rfl hb).trans_eq (by ring)

lemma projectionLaw_withDensity_apply (μ : Measure E) [SFinite μ] {h : E → ℝ≥0∞}
    (hh : Measurable h) [SFinite (μ.withDensity h)] (m : ℕ)
    {S : Set ((Fin m → E) × (Fin m → ℝ))} (hS : MeasurableSet S) :
    projectionLaw (μ.withDensity h) m S =
      ∫⁻ s, h s * (∫⁻ A, S.indicator (fun _ => (1 : ℝ≥0∞)) (A, fun j => ⟪s,A j⟫)
        ∂Measure.pi (fun _ : Fin m => stdGaussian E)) ∂μ := by
  have hobs : Measurable (fun x : (Fin m → E) × E => (x.1, fun j => ⟪x.2,x.1 j⟫)) := by fun_prop
  have hi : Measurable (fun x : (Fin m → E) × E => S.indicator (fun _ => (1 : ℝ≥0∞))
      (x.1, fun j => ⟪x.2,x.1 j⟫)) :=
    ((measurable_const : Measurable (fun _ => (1 : ℝ≥0∞))).indicator hS).comp hobs
  rw [projectionLaw, Measure.map_apply hobs hS]
  rw [← one_mul (((Measure.pi (fun _ : Fin m => stdGaussian E)).prod (μ.withDensity h)) _),
    ← lintegral_indicator_const (hobs hS) 1]
  change (∫⁻ x : (Fin m → E) × E, S.indicator (fun _ => (1 : ℝ≥0∞))
    (x.1, fun j => ⟪x.2,x.1 j⟫) ∂(Measure.pi (fun _ : Fin m => stdGaussian E)).prod (μ.withDensity h)) = _
  rw [lintegral_prod_symm _ hi.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul μ hh hi.lintegral_prod_left]
  rfl

def blockValue {J : Type*} [Fintype J] {m : ℕ} (h : J → E → ℝ≥0∞)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (s : E) : ℝ≥0∞ :=
  ∫⁻ A, h (φ (A, fun j => ⟪s,A j⟫)) s ∂Measure.pi (fun _ : Fin m => stdGaussian E)

lemma measurable_finite_select {X J : Type*} [MeasurableSpace X] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    {h : J → X → ℝ≥0∞} (hh : ∀ j, Measurable (h j)) {φ : X → J} (hφ : Measurable φ) :
    Measurable (fun x => h (φ x) x) := by
  classical
  have he (x : X) : h (φ x) x = ∑ j : J, if φ x = j then h j x else 0 := by simp
  simp_rw [he]
  exact Finset.measurable_sum _ fun j _ => Measurable.ite
    (measurableSet_eq_fun hφ measurable_const) (hh j) measurable_const

lemma measurable_blockValue {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] {m : ℕ} {h : J → E → ℝ≥0∞}
    (hh : ∀ j, Measurable (h j)) {φ : ((Fin m → E) × (Fin m → ℝ)) → J}
    (hφ : Measurable φ) : Measurable (blockValue h φ) := by
  apply Measurable.lintegral_prod_left
  exact measurable_finite_select (fun j => (hh j).comp measurable_snd)
    (hφ.comp (by fun_prop))

lemma blockValue_le_one {J : Type*} [Fintype J] {m : ℕ} {h : J → E → ℝ≥0∞}
    (hh : ∀ j s, h j s ≤ 1) (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (s : E) :
    blockValue h φ s ≤ 1 := by
  refine (lintegral_mono (fun A => hh _ s)).trans_eq ?_
  simp only [lintegral_const, one_mul, Measure.pi_univ]
  apply Finset.prod_eq_one
  intro index _
  rw [stdGaussian, Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ]
  exact measure_univ

lemma blockValue_mass_identity (μ : Measure E) [IsFiniteMeasure μ]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {m : ℕ} {h : J → E → ℝ≥0∞} (hh : ∀ j, Measurable (h j))
    (hh1 : ∀ j s, h j s ≤ 1)
    {φ : ((Fin m → E) × (Fin m → ℝ)) → J} (hφ : Measurable φ)
    {S : Set E} (hS : MeasurableSet S) :
    (μ.withDensity (blockValue h φ)) S =
      ∑ j, projectionLaw ((μ.withDensity (h j)).restrict S) m {x | φ x = j} := by
  classical
  let g (j : J) (s : E) (A : Fin m → E) : ℝ≥0∞ :=
    if φ (A, fun k => ⟪s,A k⟫) = j then h j s else 0
  have hg (j : J) : Measurable (Function.uncurry (g j)) := by
    exact Measurable.ite (measurableSet_eq_fun (hφ.comp (by fun_prop)) measurable_const)
      ((hh j).comp measurable_fst) measurable_const
  have hselect (s : E) (A : Fin m → E) : h (φ (A, fun k => ⟪s,A k⟫)) s = ∑ j, g j s A := by
    simp [g]
  have he (j : J) : projectionLaw ((μ.withDensity (h j)).restrict S) m {x | φ x = j} =
      ∫⁻ s in S, ∫⁻ A, g j s A ∂Measure.pi (fun _ : Fin m => stdGaussian E) ∂μ := by
    rw [restrict_withDensity hS]
    let : IsFiniteMeasure ((μ.restrict S).withDensity (h j)) :=
      isFiniteMeasure_withDensity (ne_of_lt ((lintegral_mono (hh1 j)).trans_lt (by simp)))
    rw [projectionLaw_withDensity_apply _ (hh j) _ (measurableSet_eq_fun hφ measurable_const)]
    apply lintegral_congr
    intro s
    rw [← lintegral_const_mul' _ _ (ne_of_lt ((hh1 j s).trans_lt (by simp)))]
    apply lintegral_congr
    intro A
    by_cases hx : φ (A, fun k => ⟪s,A k⟫) = j <;> simp [g, hx]
  rw [withDensity_apply _ hS]
  calc
    _ = ∫⁻ s in S, ∑ j, ∫⁻ A, g j s A ∂Measure.pi (fun _ : Fin m => stdGaussian E) ∂μ := by
      apply lintegral_congr
      intro s
      unfold blockValue
      simp_rw [hselect]
      exact lintegral_finsetSum _ (fun j _ => (hg j).comp (measurable_const.prodMk measurable_id))
    _ = _ := by
      rw [lintegral_finsetSum _ (fun j _ => (hg j).lintegral_prod_right)]
      simp_rw [he]

lemma blockValue_mass_bound (μ : Measure E) [IsFiniteMeasure μ]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {a m n : ℕ} {C : ℝ≥0∞} {h : J → E → ℝ≥0∞}
    (hh : ∀ j, Measurable (h j)) (hh1 : ∀ j s, h j s ≤ 1)
    (hlocal : ∀ j, PolynomialMass (μ.withDensity (h j)) a C)
    (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    {φ : ((Fin m → E) × (Fin m → ℝ)) → J} (hφ : Measurable φ) :
    PolynomialMass (μ.withDensity (blockValue h φ)) a
      ((32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) * C) := by
  let (j : J) : IsFiniteMeasure (μ.withDensity (h j)) :=
    isFiniteMeasure_withDensity (ne_of_lt ((lintegral_mono (hh1 j)).trans_lt (by simp)))
  intro z r hr
  rw [blockValue_mass_identity μ hh hh1 hφ Metric.isClosed_closedBall.measurableSet]
  exact localized_routing_bound (fun j => μ.withDensity (h j)) hlocal hC hCt hd ha hm hn hmargin φ hφ z hr

end Block

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Normalized spherical surface measure, cap bounds, and rotational symmetry.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section


namespace NoiselessRegression

section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def unitBallLaw : Measure E :=
  ((volume : Measure E) (Metric.ball 0 1))⁻¹ • volume.restrict (Metric.closedBall 0 1)

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

instance unitBallLaw_probability : IsProbabilityMeasure (unitBallLaw : Measure E) := by
  constructor
  rw [unitBallLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Measure.addHaar_closedBall _ _ (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [one_pow, ENNReal.ofReal_one, one_mul]
  exact ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
    measure_ball_lt_top.ne

instance sphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (sphereLaw (E := E)) := by
  constructor
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel _ (measure_ne_top _ _)
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero (by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne')
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'

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

open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance ambientSphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (ambientSphereLaw (E := E)) :=
  (Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable :
    IsProbabilityMeasure ((sphereLaw (E := E)).map Subtype.val))

lemma ambientSphereLaw_support : (ambientSphereLaw (E := E)).support ⊆ Metric.sphere 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_sphere
  rw [mem_ae_iff, ambientSphereLaw, Measure.map_apply (by fun_prop)
    Metric.isClosed_sphere.measurableSet.compl]
  have h : (Subtype.val : Metric.sphere (0 : E) 1 → E) ⁻¹' (Metric.sphere 0 1)ᶜ = ∅ := by
    ext x
    simp
  rw [h, measure_empty]

lemma ambientSphereLaw_closedBall [Nontrivial E] (z : E) {r : ℝ} (hr : 0 < r)
    (k : ℕ) (hk : k ≤ Module.finrank ℝ E - 1) :
    ambientSphereLaw (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) * ENNReal.ofReal (r^k) := by
  by_cases hr1 : r ≤ 1
  · rw [ambientSphereLaw, Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
    apply (sphereLaw_cap_raw z hr hr1 (Module.finrank_pos (R := ℝ) (M := E))).trans
    apply mul_le_mul' le_rfl
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hr.le hr1 hk)
  · have hr1 : 1 ≤ r := (le_of_not_ge hr1)
    calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by
        apply one_le_mul
        · rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          have : (1 : ℝ) ≤ 4 ^ Module.finrank ℝ E := one_le_pow₀ (by norm_num)
          linarith
        · rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hr1)

lemma terminal_cap_mass [Nontrivial E] (y z : E) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (a : ℕ) (ha : 2*a ≤ Module.finrank ℝ E - 1) :
    ((ambientSphereLaw (E := E)).restrict (Metric.closedBall y ε)) (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) *
        ENNReal.ofReal (ε^a) * ENNReal.ofReal (r^a) := by
  rw [Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]
  by_cases h : r ≤ ε
  · apply (measure_mono Set.inter_subset_left).trans
    apply (ambientSphereLaw_closedBall z hr (2*a) ha).trans
    rw [mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hε.le a)]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    rw [mul_comm 2 a, pow_mul, pow_two]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le h a) (by positivity)
  · apply (measure_mono Set.inter_subset_right).trans
    apply (ambientSphereLaw_closedBall y hε (2*a) ha).trans
    rw [mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hε.le a)]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    rw [mul_comm 2 a, pow_mul, pow_two]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le (le_of_not_ge h) a) (by positivity)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma chord_le_arccos (s t : Metric.sphere (0 : E) 1) :
    dist s.val t.val ≤ Real.arccos ⟪s.val,t.val⟫ := by
  have hs : ‖s.val‖ = 1 := mem_sphere_zero_iff_norm.mp s.property
  have ht : ‖t.val‖ = 1 := mem_sphere_zero_iff_norm.mp t.property
  have habs : |⟪s.val,t.val⟫| ≤ 1 := by
    simpa [hs, ht] using abs_real_inner_le_norm s.val t.val
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.arccos ⟪s.val,t.val⟫)
  rw [Real.cos_arccos (abs_le.mp habs).1 (abs_le.mp habs).2] at hcos
  have hd : (dist s.val t.val)^2 = 2 - 2*⟪s.val,t.val⟫ := by
    rw [dist_eq_norm, norm_sub_sq_real, hs, ht]
    ring
  nlinarith [dist_nonneg (x := s.val) (y := t.val), Real.arccos_nonneg ⟪s.val,t.val⟫]

lemma unitBallLaw_isometry_apply (e : E ≃ₗᵢ[ℝ] E) (s : Set E) :
    unitBallLaw (e ⁻¹' s) = unitBallLaw s := by
  have hb : e ⁻¹' Metric.closedBall (0 : E) 1 = Metric.closedBall 0 1 := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  have hset : e ⁻¹' s ∩ Metric.closedBall (0 : E) 1 =
      e ⁻¹' (s ∩ Metric.closedBall 0 1) := by rw [Set.preimage_inter, hb]
  rw [unitBallLaw, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet, hset]
  congr 1
  calc
    _ = (Measure.map e volume) (s ∩ Metric.closedBall 0 1) :=
      (e.toMeasurableEquiv.measurableEmbedding.map_apply _ _).symm
    _ = _ := by rw [e.measurePreserving.map_eq]

lemma ambientSphereLaw_apply [Nontrivial E] {s : Set E} (hs : MeasurableSet s) :
    ambientSphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ s)) := by
  rw [ambientSphereLaw, Measure.map_apply (by fun_prop) hs,
    sphereLaw_apply (measurable_subtype_coe hs)]
  congr 2
  ext x
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hs⟩
    exact ⟨⟨x,hx⟩,hs,rfl⟩

lemma ambientSphereLaw_isometry [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving e (ambientSphereLaw (E := E)) (ambientSphereLaw (E := E)) := by
  refine ⟨e.continuous.measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply e.continuous.measurable hs,
    ambientSphereLaw_apply (e.continuous.measurable hs), ambientSphereLaw_apply hs]
  have hset : Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ e ⁻¹' s) =
      e ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨hy, hys⟩, he⟩
      refine ⟨r,hr,e y,⟨?_,hys⟩,?_⟩
      · simpa only [mem_sphere_zero_iff_norm, e.norm_map] using hy
      · simpa only [map_smul] using congrArg e he
    · rintro ⟨r,hr,y,⟨hy,hys⟩,he⟩
      refine ⟨r,hr,e.symm y,⟨?_,?_⟩,?_⟩
      · simpa only [mem_sphere_zero_iff_norm, e.symm.norm_map] using hy
      · simpa using hys
      · simpa only [map_smul, e.symm_apply_apply] using congrArg e.symm he
  rw [hset, unitBallLaw_isometry_apply]

lemma ambientSphereLaw_ae_norm [Nontrivial E] :
    ∀ᵐ x : E ∂ambientSphereLaw, ‖x‖ = 1 := by
  filter_upwards [Measure.support_mem_ae (μ := ambientSphereLaw (E := E))] with x hx
  exact mem_sphere_zero_iff_norm.mp (ambientSphereLaw_support hx)

lemma sphere_inner_sq_integrable [Nontrivial E] (v : E) :
    Integrable (fun x => ⟪v,x⟫^2) (ambientSphereLaw (E := E)) := by
  apply (integrable_const (‖v‖^2)).mono' (by fun_prop)
  filter_upwards [ambientSphereLaw_ae_norm (E := E)] with x hx
  have h := abs_real_inner_le_norm v x
  rw [hx, mul_one] at h
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _) |>.2 h)

lemma sphere_inner_sq_eq [Nontrivial E] {v w : E} (h : ‖v‖ = ‖w‖) :
    (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = ∫ x, ⟪w,x⟫^2 ∂ambientSphereLaw := by
  let e := (ℝ ∙ (v-w))ᗮ.reflection
  have he : e v = w := Submodule.reflection_sub h
  have hi := (ambientSphereLaw_isometry e).integral_comp
    e.toMeasurableEquiv.measurableEmbedding (fun x => ⟪w,x⟫^2)
  rw [← he] at hi
  simp only [e.inner_map_map] at hi
  simpa only [he] using hi

lemma sphere_inner_sq_unit [Nontrivial E] {v : E} (hv : ‖v‖ = 1) :
    (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = 1 / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  have hsum : ∀ x : E, (∑ i, ⟪b i,x⟫^2) = ‖x‖^2 := by
    intro x
    simpa only [real_inner_comm x, pow_two, real_inner_self_eq_norm_sq] using
      b.sum_inner_mul_inner x x
  have h : (Module.finrank ℝ E : ℝ) * (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = 1 := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ E), ∫ x, ⟪b i,x⟫^2 ∂ambientSphereLaw := by
        have heq : ∀ i, (∫ x, ⟪b i,x⟫^2 ∂ambientSphereLaw) =
            ∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw := fun i =>
          sphere_inner_sq_eq (by rw [b.norm_eq_one, hv])
        simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∫ x, ∑ i, ⟪b i,x⟫^2 ∂ambientSphereLaw :=
        (integral_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i))).symm
      _ = ∫ _ : E, (1 : ℝ) ∂ambientSphereLaw := by
        apply integral_congr_ae
        filter_upwards [ambientSphereLaw_ae_norm (E := E)] with x hx
        rw [hsum, hx, one_pow]
      _ = 1 := by simp
  have hd : (Module.finrank ℝ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne'
  exact (eq_div_iff hd).2 (by simpa only [mul_comm] using h)

lemma sphere_projection_sq_integrable [Nontrivial E] (U : Submodule ℝ E) :
    Integrable (fun x => ‖U.orthogonalProjectionOnto x‖^2) (ambientSphereLaw (E := E)) := by
  let b := stdOrthonormalBasis ℝ U
  have hsum : ∀ x : E, (∑ i, ⟪(b i : E),x⟫^2) = ‖U.orthogonalProjectionOnto x‖^2 := by
    intro x
    have h := b.sum_inner_mul_inner (U.orthogonalProjectionOnto x) (U.orthogonalProjectionOnto x)
    rw [real_inner_self_eq_norm_sq] at h
    have hi : ∀ i, ⟪U.orthogonalProjectionOnto x, b i⟫ = ⟪b i, U.orthogonalProjectionOnto x⟫ :=
      fun i => real_inner_comm _ _
    simpa only [hi, U.inner_orthogonalProjectionOnto_eq_of_mem_left, pow_two] using h
  simp_rw [← hsum]
  exact integrable_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i : E))

lemma sphere_projection_sq_integral [Nontrivial E] (U : Submodule ℝ E) :
    (∫ x, ‖U.orthogonalProjectionOnto x‖^2 ∂ambientSphereLaw) =
      (Module.finrank ℝ U : ℝ) / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ U
  have hsum : ∀ x : E, (∑ i, ⟪(b i : E),x⟫^2) = ‖U.orthogonalProjectionOnto x‖^2 := by
    intro x
    have h := b.sum_inner_mul_inner (U.orthogonalProjectionOnto x) (U.orthogonalProjectionOnto x)
    rw [real_inner_self_eq_norm_sq] at h
    have hi : ∀ i, ⟪U.orthogonalProjectionOnto x, b i⟫ = ⟪b i, U.orthogonalProjectionOnto x⟫ :=
      fun i => real_inner_comm _ _
    simpa only [hi, U.inner_orthogonalProjectionOnto_eq_of_mem_left, pow_two] using h
  simp_rw [← hsum]
  rw [integral_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i : E))]
  have hi : ∀ i, (∫ x, ⟪(b i : E), x⟫^2 ∂ambientSphereLaw) =
      1 / (Module.finrank ℝ E : ℝ) := fun i =>
    sphere_inner_sq_unit (by exact b.norm_eq_one i)
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]

def sphereIsometry (e : E ≃ₗᵢ[ℝ] E) : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1 :=
  e.toHomeomorph.subtype (fun x => by
    simp only [mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖e x‖ = 1
    rw [e.norm_map])

lemma sphereIsometry_preserving [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereIsometry e) (sphereLaw (E := E)) (sphereLaw (E := E)) := by
  refine ⟨(sphereIsometry e).continuous.measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).map_injective
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  change (sphereLaw (E := E)).map (e ∘ Subtype.val) = ambientSphereLaw
  rw [← Measure.map_map e.continuous.measurable (by fun_prop)]
  exact (ambientSphereLaw_isometry e).map_eq

omit [MeasurableSpace E] [BorelSpace E] in
lemma reflection_dist (U : Submodule ℝ E) (x : E) :
    dist x (U.reflection x) = 2 * ‖Uᗮ.starProjection x‖ := by
  rw [dist_eq_norm, Submodule.reflection_apply]
  have heq : x - (2 • U.starProjection x - x) = (2 : ℝ) • Uᗮ.starProjection x := by
    rw [Submodule.starProjection_orthogonal]
    simp only [sub_apply, ContinuousLinearMap.id_apply, two_smul ℝ]
    abel
  rw [heq, norm_smul]
  norm_num

lemma sphere_projection_large [Nontrivial E] (U : Submodule ℝ E)
    (hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ E) :
    sphereLaw {x : Metric.sphere (0 : E) 1 | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x.val‖^2} ≤
      ENNReal.ofReal (5/16 : ℝ) := by
  have hi := ofReal_integral_eq_lintegral_ofReal (sphere_projection_sq_integrable U)
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖U.orthogonalProjectionOnto x‖)
  rw [sphere_projection_sq_integral] at hi
  have hmark := meas_ge_le_lintegral_div
    (μ := ambientSphereLaw (E := E)) (f := fun x => ENNReal.ofReal (‖U.orthogonalProjectionOnto x‖^2))
    (by fun_prop) (by norm_num : ENNReal.ofReal (4/5 : ℝ) ≠ 0) (ENNReal.ofReal_ne_top : ENNReal.ofReal (4/5 : ℝ) ≠ ∞)
  rw [← hi] at hmark
  have hset : {x : E | ENNReal.ofReal (4/5 : ℝ) ≤ ENNReal.ofReal (‖U.orthogonalProjectionOnto x‖^2)} =
      {x : E | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x‖^2} := by
    ext x
    change ENNReal.ofReal (4/5 : ℝ) ≤ _ ↔ _
    exact ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)
  rw [hset, ambientSphereLaw,
    (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).map_apply] at hmark
  apply hmark.trans
  have hd : (0 : ℝ) < Module.finrank ℝ E := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hdiv : (Module.finrank ℝ U : ℝ) / (Module.finrank ℝ E : ℝ) ≤ 1/4 := by
    rw [div_le_iff₀ hd]
    have : (4 : ℝ) * Module.finrank ℝ U ≤ Module.finrank ℝ E := by exact_mod_cast hU
    linarith
  calc
    _ ≤ ENNReal.ofReal (1/4 : ℝ) / ENNReal.ofReal (4/5 : ℝ) := by gcongr
    _ = ENNReal.ofReal (5/16 : ℝ) := by
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4/5)]
      norm_num

lemma sphere_reflection_success_bound [Nontrivial E] (U : Submodule ℝ E)
    (hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ E)
    (S : Set (Metric.sphere (0 : E) 1)) (hS : NullMeasurableSet S sphereLaw)
    (hsep : ∀ s ∈ S, sphereIsometry U.reflection s ∈ S →
      dist s.val (U.reflection s.val) ≤ 1/5) :
    sphereLaw S ≤ ENNReal.ofReal (21/32 : ℝ) := by
  let f := sphereIsometry U.reflection
  have hp := sphereIsometry_preserving U.reflection
  have hi : S ∩ f ⁻¹' S ⊆
      {x : Metric.sphere (0 : E) 1 | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x.val‖^2} := by
    intro s hs
    have hd := hsep s hs.1 hs.2
    rw [reflection_dist] at hd
    have hn := U.norm_sq_eq_add_norm_sq_starProjection s.val
    rw [mem_sphere_zero_iff_norm.mp s.property] at hn
    change (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto s.val‖^2
    have he : ‖U.starProjection s.val‖ = ‖U.orthogonalProjectionOnto s.val‖ := rfl
    rw [he] at hn
    nlinarith [norm_nonneg (Uᗮ.starProjection s.val)]
  have hinter := (measure_mono hi).trans (sphere_projection_large U hU)
  have heq := measure_union_add_inter₀ S (hS.preimage hp.quasiMeasurePreserving)
  rw [hp.measure_preimage hS] at heq
  calc
    sphereLaw S = ENNReal.ofReal (1/2 : ℝ) * (sphereLaw S + sphereLaw S) := by
      rw [← two_mul, ← mul_assoc]
      have hc : ENNReal.ofReal (1/2 : ℝ) * 2 = 1 := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
        norm_num
      rw [hc, one_mul]
    _ = ENNReal.ofReal (1/2 : ℝ) *
        (sphereLaw (S ∪ f ⁻¹' S) + sphereLaw (S ∩ f ⁻¹' S)) := by rw [heq]
    _ ≤ ENNReal.ofReal (1/2 : ℝ) * (1 + ENNReal.ofReal (5/16 : ℝ)) := by
      exact mul_le_mul' le_rfl (add_le_add prob_le_one hinter)
    _ = ENNReal.ofReal (21/32 : ℝ) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (0 : ℝ) ≤ 5/16),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
      norm_num

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Absolute continuity of noiseless spherical observation laws.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section


namespace NoiselessRegression

section ObservationAC
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma projectionLaw_absolutelyContinuous {ν : Measure E} [IsFiniteMeasure ν]
    {a m n : ℕ} {C : ℝ≥0∞} (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (hn : 1 ≤ n) (hmargin : n+m ≤ a) :
    projectionLaw ν m ≪ matrixLabelReference (E := E) m := by
  let ν' := C⁻¹ • ν
  have hCi : C⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hC
  let : IsFiniteMeasure ν' := ⟨by simp only [ν', Measure.smul_apply, smul_eq_mul]; finiteness⟩
  have hlocal : HasLocalMassBound ν' (a : ℝ) := by
    intro z _ r hr
    have hh := mul_le_mul' (le_rfl : C⁻¹ ≤ C⁻¹) (hν z r hr)
    simpa only [ν', Measure.smul_apply, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hC hCt, one_mul, Real.rpow_natCast] using hh
  have hs : ν'.support ⊆ Metric.closedBall 0 1 :=
    (Measure.smul_absolutelyContinuous.support_mono).trans hsupport
  have hbound (S : Set ((Fin m → E) × (Fin m → ℝ))) :=
    projectionLaw_set_bound hlocal hs m n hn (by exact_mod_cast hmargin) S
  have he : projectionLaw ν' m = C⁻¹ • projectionLaw ν m := by
    simp only [projectionLaw, ν', Measure.prod_smul_right]
    exact Measure.map_smul (R := ℝ≥0∞) _ _ _
  intro S hS
  have h := hbound S
  rw [hS, ENNReal.zero_rpow_of_pos (by
    have : (1 : ℝ) < n+1 := by exact_mod_cast (by omega : 1 < n+1)
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr this)), mul_zero, he,
    Measure.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp (le_antisymm h bot_le)).resolve_left (ENNReal.inv_ne_zero.mpr hCt)

lemma sphere_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × E => (z.2, ⟪z.1.val,z.2⟫))
      ((sphereLaw (E := E)).prod (stdGaussian E)) ((stdGaussian E).prod volume) := by
  have hac : projectionLaw (ambientSphereLaw (E := E)) 1 ≪ matrixLabelReference (E := E) 1 := by
    apply projectionLaw_absolutelyContinuous (a := 2) (n := 1)
      (C := ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E))
    · intro z r hr
      exact ambientSphereLaw_closedBall z hr 2 (by omega)
    · positivity
    · exact ENNReal.ofReal_ne_top
    · exact ambientSphereLaw_support.trans Metric.sphere_subset_closedBall
    · omega
    · omega
  have hp : Measure.QuasiMeasurePreserving
      (fun z : (Fin 1 → E) × E => (z.1, fun j => ⟪z.2,z.1 j⟫))
      ((Measure.pi (fun _ : Fin 1 => stdGaussian E)).prod (ambientSphereLaw (E := E)))
      (matrixLabelReference (E := E) 1) := ⟨by fun_prop, hac⟩
  have h1 := ((measurePreserving_funUnique (stdGaussian E) (Fin 1)).symm
      (MeasurableEquiv.funUnique (Fin 1) E)).prod
    (measurable_subtype_coe.measurePreserving (sphereLaw (E := E)))
  have h2 := (measurePreserving_funUnique (stdGaussian E) (Fin 1)).prod
    (volume_preserving_funUnique (Fin 1) ℝ)
  have h3 := h2.quasiMeasurePreserving.comp (hp.comp (h1.quasiMeasurePreserving.comp
    Measure.measurePreserving_swap.quasiMeasurePreserving))
  convert h3 using 1
  ext z <;> simp [MeasurableEquiv.funUnique]

end ObservationAC

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Sequential routing and continuation mass propagation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section


namespace NoiselessRegression

section StreamAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

lemma measurable_select {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {h : J → X → Y} (hh : ∀ j, Measurable (h j)) {φ : X → J} (hφ : Measurable φ) :
    Measurable (fun x => h (φ x) x) :=
  (measurable_from_prod_countable_right (f := fun p : J × X => h p.1 p.2) hh).comp (hφ.prodMk measurable_id)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma lintegral_pi_cons (ν : Measure E) [SigmaFinite ν] {n : ℕ}
    (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v, f v ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, ∫⁻ v : Fin n → E, f (Fin.cons x v) ∂Measure.pi (fun _ => ν) ∂ν := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (0 : Fin (n+1))).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f, lintegral_prod]
  · congr 1
    ext x
    congr 1
    ext v
    congr 1
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    simp
  · exact (hf.comp hp.measurable).aemeasurable

def streamRoute (δ : ℕ → J → (E × ℝ) → J) (n : ℕ) :
    (k : ℕ) → J → ((Fin k → E) × (Fin k → ℝ)) → J
  | 0, j, _ => j
  | k+1, j, x => streamRoute δ (n+1) k (δ (n+1) j (x.1 0, x.2 0)) (Fin.tail x.1, Fin.tail x.2)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_streamRoute {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (n k : ℕ) (j : J) :
    Measurable (streamRoute δ n k j) := by
  induction k generalizing n j with
  | zero => exact measurable_const
  | succ k ih =>
    change Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) => streamRoute δ (n+1) k (δ (n+1) j (x.1 0,x.2 0)) (Fin.tail x.1,Fin.tail x.2))
    have ht : Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        (Fin.tail x.1, Fin.tail x.2)) := by
      change Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        ((fun i : Fin k => x.1 i.succ), (fun i : Fin k => x.2 i.succ)))
      fun_prop
    have hd : Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        δ (n+1) j (x.1 0,x.2 0)) := (hδ (n+1) j).comp (by fun_prop)
    exact measurable_select (fun a => (ih (n+1) a).comp ht) hd

def continuation (δ : ℕ → J → (E × ℝ) → J) (w : ℕ → J → E → ℝ≥0∞)
    (n : ℕ) : ℕ → J → E → ℝ≥0∞
  | 0, j, s => w n j s
  | k+1, j, s => ∫⁻ x, continuation δ w (n+1) k (δ (n+1) j (x, ⟪s,x⟫)) s ∂stdGaussian E

lemma measurable_continuation {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j)) (n k : ℕ) (j : J) :
    Measurable (continuation δ w n k j) := by
  induction k generalizing n j with
  | zero => exact hw n j
  | succ k ih =>
    apply Measurable.lintegral_prod_left
    exact measurable_select (fun a => (ih (n+1) a).comp measurable_snd)
      ((hδ (n+1) j).comp (by fun_prop))

omit [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma continuation_le_one {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hw : ∀ n j s, w n j s ≤ 1) (n k : ℕ) (j : J) (s : E) :
    continuation δ w n k j s ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hw n j s
  | succ k ih =>
    refine (lintegral_mono (fun x => ih _ _)).trans_eq ?_
    rw [lintegral_const, one_mul, stdGaussian,
      Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ]
    exact measure_univ

lemma continuation_unroll {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j))
    (n m k : ℕ) (j : J) (s : E) :
    continuation δ w n (m+k) j s =
      blockValue (fun a => continuation δ w (n+m) k a) (streamRoute δ n m j) s := by
  induction m generalizing n j with
  | zero =>
    simp [blockValue, streamRoute]
  | succ m ih =>
    rw [Nat.succ_add, continuation]
    simp_rw [ih]
    unfold blockValue
    have hf : Measurable (fun A : Fin (m+1) → E =>
        continuation δ w (n+(m+1)) k (streamRoute δ n (m+1) j (A,fun i => ⟪s,A i⟫)) s) := by
      exact (measurable_of_finite (fun a => continuation δ w (n+(m+1)) k a s)).comp
        ((measurable_streamRoute hδ n (m+1) j).comp (by fun_prop))
    rw [lintegral_pi_cons _ _ hf]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro A
    have he : Fin.tail (fun i : Fin (m+1) => ⟪s,(Fin.cons x A : Fin (m+1) → E) i⟫) = (fun i => ⟪s,A i⟫) := by
      ext i
      simp [Fin.tail]
    simp [streamRoute, he, Nat.add_left_comm, Nat.add_comm]

def streamFactor (q : ℕ) : ℝ≥0∞ :=
  (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/(q : ℝ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma streamFactor_ne_top (q : ℕ) : streamFactor (E := E) (J := J) q ≠ ∞ := by
  exact ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma one_le_streamFactor [Nonempty J] {q : ℕ} (hq : 0 < q) :
    1 ≤ streamFactor (E := E) (J := J) q := by
  apply one_le_mul (one_le_pow₀ (by norm_num))
  exact ENNReal.one_le_rpow (by exact_mod_cast Fintype.card_pos (α := J)) (by positivity)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma PolynomialMass.mono {μ : Measure E} {a : ℕ} {C D : ℝ≥0∞}
    (h : PolynomialMass μ a C) (hCD : C ≤ D) : PolynomialMass μ a D :=
  fun z r hr => (h z r hr).trans (mul_le_mul' hCD le_rfl)

lemma continuation_mass_bound [Nonempty J] (μ : Measure E) [IsFiniteMeasure μ]
    {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (μ.withDensity (w n j)) a C)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    PolynomialMass (μ.withDensity (continuation δ w n k j)) a
      (C * streamFactor (E := E) (J := J) q ^ (k/q+1)) := by
  have hden : ((q-1 : ℕ) : ℝ)+1 = (q : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    ring
  have hq0 : 0 < q := by omega
  have hK1 := one_le_streamFactor (E := E) (J := J) hq0
  have hK0 : streamFactor (E := E) (J := J) q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK1)
  have hKt := streamFactor_ne_top (E := E) (J := J) q
  induction k using Nat.strong_induction_on generalizing n j with
  | h k ih =>
    by_cases hk : q ≤ k
    · have hki : k-q < k := by omega
      have hC1 : C * streamFactor (E := E) (J := J) q ^ ((k-q)/q+1) ≠ 0 :=
        mul_ne_zero hC (pow_ne_zero _ hK0)
      have hC1t : C * streamFactor (E := E) (J := J) q ^ ((k-q)/q+1) ≠ ∞ :=
        ENNReal.mul_ne_top hCt (ENNReal.pow_ne_top hKt)
      have hb := blockValue_mass_bound μ
        (fun b => measurable_continuation hδ hw (n+q) (k-q) b)
        (fun b s => continuation_le_one hw1 (n+q) (k-q) b s)
        (fun b => ih (k-q) hki (n+q) b) hC1 hC1t hd ha
        (by omega : q ≤ Module.finrank ℝ E) (by omega : 1 ≤ q-1)
        (by omega : q-1+q ≤ a) (measurable_streamRoute hδ n q j)
      have he : continuation δ w n k j =
          blockValue (fun b => continuation δ w (n+q) (k-q) b) (streamRoute δ n q j) := by
        funext s
        simpa [Nat.add_sub_of_le hk] using continuation_unroll hδ n q (k-q) j s
      rw [he]
      have hdiv : k/q = (k-q)/q+1 := by
        conv_lhs => rw [← Nat.add_sub_of_le hk]
        exact Nat.add_div_left _ hq0
      convert hb using 1
      rw [hden, ← streamFactor, hdiv, pow_succ]
      ring
    · have hkm : k ≤ q := by omega
      have hb := blockValue_mass_bound μ
        (fun b => hw (n+k) b) (fun b s => hw1 (n+k) b s) (hlocal (n+k)) hC hCt hd ha
        (by omega : k ≤ Module.finrank ℝ E) (by omega : 1 ≤ q-1)
        (by omega : q-1+k ≤ a) (measurable_streamRoute hδ n k j)
      have he : continuation δ w n k j = blockValue (w (n+k)) (streamRoute δ n k j) := by
        funext s
        simpa [continuation] using continuation_unroll hδ n k 0 j s
      rw [he]
      convert hb using 1
      rw [hden, ← streamFactor, Nat.div_eq_of_lt (by omega : k < q)]
      simp [mul_comm]

lemma fin_tail_snoc {X : Type*} {k : ℕ} (A : Fin (k+1) → X) (x : X) :
    Fin.tail (Fin.snoc A x : Fin (k+2) → X) =
      (Fin.snoc (Fin.tail A : Fin k → X) x : Fin (k+1) → X) := by
  rw [← Fin.cons_self_tail A, ← Fin.cons_snoc_eq_snoc_cons, Fin.tail_cons, Fin.tail_cons]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma streamRoute_snoc (δ : ℕ → J → (E × ℝ) → J) (n k : ℕ) (j : J)
    (A : Fin k → E) (b : Fin k → ℝ) (x : E) (y : ℝ) :
    streamRoute δ n (k+1) j (Fin.snoc A x, Fin.snoc b y) =
      δ (n+k+1) (streamRoute δ n k j (A,b)) (x,y) := by
  induction k generalizing n j with
  | zero => simp [streamRoute, Fin.snoc_zero]
  | succ k ih =>
    rw [streamRoute]
    simp only [Fin.snoc_apply_zero, fin_tail_snoc]
    rw [ih, streamRoute]
    congr 1; omega

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma lintegral_pi_prefix (ν : Measure E) [IsProbabilityMeasure ν] {t T : ℕ} (ht : t ≤ T)
    (f : (Fin t → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Fin T → E, f (fun i => x (Fin.castLE ht i)) ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, f x ∂Measure.pi (fun _ => ν) := by
  induction T with
  | zero =>
    have : t = 0 := by omega
    subst t
    rfl
  | succ T ih =>
    by_cases h : t ≤ T
    · have he (x : Fin T → E) (y : E) :
          (fun i : Fin t => (Fin.snoc x y : Fin (T+1) → E) (Fin.castLE ht i)) =
            (fun i : Fin t => x (Fin.castLE h i)) := by
        ext i
        change (Fin.snoc x y : Fin (T+1) → E) (Fin.castLE h i).castSucc = _
        exact Fin.snoc_castSucc _ _ _
      rw [lintegral_pi_snoc ν (fun x : Fin (T+1) → E => f (fun i => x (Fin.castLE ht i)))
        (hf.comp (by fun_prop))]
      simp_rw [he, lintegral_const, measure_univ, mul_one]
      exact ih h
    · have he : t = T+1 := by omega
      subst t
      rfl

end StreamAux

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Spherical cap mass bounds along sequential routes.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section


namespace NoiselessRegression

section StreamCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

def capWeight (y : E) (ε : ℝ) : E → ℝ≥0∞ :=
  (Metric.closedBall y ε).indicator (fun _ => 1)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma measurable_capWeight (y : E) (ε : ℝ) : Measurable (capWeight y ε) :=
  measurable_const.indicator Metric.isClosed_closedBall.measurableSet

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma capWeight_le_one (y s : E) (ε : ℝ) : capWeight y ε s ≤ 1 := by
  classical
  simp only [capWeight, Set.indicator_apply]
  split <;> simp

lemma capWeight_mass (y : E) {ε : ℝ} (hε : 0 < ε) (a : ℕ)
    (ha : 2*a ≤ Module.finrank ℝ E - 1) :
    PolynomialMass ((ambientSphereLaw (E := E)).withDensity (capWeight y ε)) a
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) := by
  change PolynomialMass ((ambientSphereLaw (E := E)).withDensity ((Metric.closedBall y ε).indicator 1)) a _
  rw [withDensity_indicator_one Metric.isClosed_closedBall.measurableSet]
  exact fun z r hr => terminal_cap_mass y z hε hr a ha

lemma ambient_mass_bound {f : E → ℝ≥0∞} {a : ℕ} {C : ℝ≥0∞}
    (h : PolynomialMass ((ambientSphereLaw (E := E)).withDensity f) a C) :
    (∫⁻ s, f s ∂ambientSphereLaw) ≤ C := by
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ]
  apply (measure_mono_ae ?_).trans (by simpa using h 0 1 zero_lt_one)
  filter_upwards [(withDensity_absolutelyContinuous (ambientSphereLaw (E := E)) f).ae_le
    (ambientSphereLaw_ae_norm (E := E))] with s hs
  intro _
  change dist s 0 ≤ 1
  simp [dist_zero_right, hs]

lemma continuation_cap_integral_bound {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : ℕ → J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    (∫⁻ s, continuation δ (fun n j => capWeight (y n j) ε) n k j s ∂ambientSphereLaw) ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ (k/q+1) := by
  apply ambient_mass_bound
  apply continuation_mass_bound _ hδ (fun n j => measurable_capWeight _ _)
    (fun n j s => capWeight_le_one _ _ _)
    (mul_ne_zero (by positivity) (by positivity)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (fun n j => capWeight_mass (y n j) hε a ha)
    (Module.finrank_pos (R := ℝ) (M := E)) (by omega) hq hqa

lemma route_cap_bound {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (k : ℕ) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin k => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ (k/q+1) := by
  let w : ℕ → J → E → ℝ≥0∞ := fun _ j => capWeight (y j) ε
  have hV := measurable_continuation (w := w) hδ (fun _ j => measurable_capWeight (y j) ε) 0 k j
  have he (s : E) : continuation δ w 0 k j s =
      ∫⁻ A : Fin k → E, capWeight (y (streamRoute δ 0 k j (A,fun i => ⟪s,A i⟫))) ε s
        ∂Measure.pi (fun _ => stdGaussian E) := by
    simpa [w, blockValue, continuation] using continuation_unroll (w := w) hδ 0 k 0 j s
  let S : Set ((Metric.sphere (0 : E) 1) × (Fin k → E)) :=
    {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε}
  have hS : MeasurableSet S := by
    apply measurableSet_le _ measurable_const
    exact measurable_subtype_coe.comp measurable_fst |>.dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  change ((sphereLaw (E := E)).prod _) S ≤ _
  rw [← one_mul (((sphereLaw (E := E)).prod _) S), ← lintegral_indicator_const hS 1,
    lintegral_prod _ (measurable_const.indicator hS).aemeasurable]
  have hf : ∀ s : Metric.sphere (0 : E) 1,
      (∫⁻ A, S.indicator (fun _ => (1 : ℝ≥0∞)) (s,A) ∂Measure.pi (fun _ => stdGaussian E)) =
        continuation δ w 0 k j s.val := by
    intro s
    rw [he]
    apply lintegral_congr
    intro A
    classical
    change (if dist s.val (y (streamRoute δ 0 k j (A,fun i => ⟪s.val,A i⟫))) ≤ ε then 1 else 0) = _
    unfold capWeight
    rw [Set.indicator_apply]
    rfl
  simp_rw [hf]
  rw [← lintegral_map hV measurable_subtype_coe]
  exact continuation_cap_integral_bound hδ (fun _ => y) hε ha hq hqa 0 k j

end StreamCaps

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Finite-state sequential execution and terminal-state witnesses.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section


namespace NoiselessRegression

lemma fin_prefix_snoc {X : Type*} {n T : ℕ} (h : n+1 ≤ T) (x : Fin T → X) :
    (fun i : Fin (n+1) => x (Fin.castLE h i)) =
      (Fin.snoc (fun i : Fin n => x (Fin.castLE (by omega) i))
        (x ⟨n, by omega⟩) : Fin (n+1) → X) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    rfl
  · simp

namespace Learner
variable {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)

def forcedRun (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ → State M
  | 0 => (L.initialChoice ω).2
  | n+1 =>
    if hn : n < T then
      (L.transition (n+1) ω (L.forcedRun s ω x n) (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s.val⟫)).2
    else L.forcedRun s ω x n

lemma forcedRun_eq_route (s : UnitSphere d) (ω : Ω) (x : Samples d T)
    {n : ℕ} (hn : n ≤ T) :
    L.forcedRun s ω x n =
      streamRoute (fun t j obs => (L.transition t ω j obs).2) 0 n (L.initialChoice ω).2
        ((fun i => x (Fin.castLE hn i)), (fun i => ⟪s.val,x (Fin.castLE hn i)⟫)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [forcedRun, dite_eq_left (by omega), ih (by omega)]
    rw [fin_prefix_snoc hn x, fin_prefix_snoc hn (fun i => ⟪s.val,x i⟫), streamRoute_snoc]
    simp only [zero_add, real_inner_comm]

lemma run_forced_witness (s : UnitSphere d) (ω : Ω) (x : Samples d T)
    (n : ℕ) (hn : n ≤ T) :
    (L.run s ω x n = .inl (L.forcedRun s ω x n)) ∨
      ∃ t ≤ n, L.run s ω x n = .inr (t, L.forcedRun s ω x t) := by
  induction n with
  | zero =>
    simp only [run, start, forcedRun]
    split
    · exact Or.inr ⟨0, le_rfl, rfl⟩
    · exact Or.inl rfl
  | succ n ih =>
    rcases ih (by omega) with h | ⟨t,ht,h⟩
    · have hnt : n < T := by omega
      rw [run, h]
      simp only [dite_eq_left hnt, forcedRun]
      split
      · exact Or.inr ⟨n+1, le_rfl, by simp [forcedRun, hnt]⟩
      · exact Or.inl rfl
    · right
      exact ⟨t, by omega, by rw [run, h]⟩

lemma terminal_forced_witness (s : UnitSphere d) (ω : Ω) (x : Samples d T) :
    ∃ t ≤ T, L.terminal s ω x = (t, L.forcedRun s ω x t) := by
  rcases L.run_forced_witness s ω x T le_rfl with h | ⟨t,ht,h⟩
  · exact ⟨T, le_rfl, by simp [terminal, h]⟩
  · exact ⟨t, ht, by simp [terminal, h]⟩

end Learner

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Prefix integration and transfer between almost-everywhere equal transitions.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section


namespace NoiselessRegression

section StreamTransfer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurePreserving_pi_prefix (ν : Measure E) [IsProbabilityMeasure ν]
    {t T : ℕ} (ht : t ≤ T) :
    MeasurePreserving (fun x : Fin T → E => fun i : Fin t => x (Fin.castLE ht i))
      (Measure.pi (fun _ => ν)) (Measure.pi (fun _ => ν)) := by
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop)]
  exact lintegral_pi_prefix ν ht f hf

lemma sphere_sample_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E)
    {T : ℕ} (i : Fin T) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × (Fin T → E) => (z.2 i, ⟪z.1.val,z.2 i⟫))
      ((sphereLaw (E := E)).prod (Measure.pi (fun _ => stdGaussian E)))
      ((stdGaussian E).prod volume) := by
  exact (sphere_observation_quasi hd).comp
    ((MeasurePreserving.id (sphereLaw (E := E))).prod
      (measurePreserving_eval (fun _ : Fin T => stdGaussian E) i)).quasiMeasurePreserving

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
lemma streamRoute_congr {J : Type*} (δ δ' : ℕ → J → (E × ℝ) → J)
    (n k : ℕ) (j : J) (A : Fin k → E) (b : Fin k → ℝ)
    (h : ∀ t j i, δ t j (A i,b i) = δ' t j (A i,b i)) :
    streamRoute δ n k j (A,b) = streamRoute δ' n k j (A,b) := by
  induction k generalizing n j with
  | zero => rfl
  | succ k ih =>
    rw [streamRoute, streamRoute, h]
    exact ih (n+1) _ (Fin.tail A) (Fin.tail b) (fun t j i => h t j i.succ)

lemma prefix_route_cap_bound [Nontrivial E]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]
    {δ : ℕ → J → (E × ℝ) → J} (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) {k T : ℕ} (hk : k ≤ T) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin T => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j
        ((fun i => z.2 (Fin.castLE hk i)),fun i => ⟪z.1.val,z.2 (Fin.castLE hk i)⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ (T/q+1) := by
  have hp := (MeasurePreserving.id (sphereLaw (E := E))).prod
    (measurePreserving_pi_prefix (stdGaussian E) hk)
  have hs : MeasurableSet
      {z : (Metric.sphere (0 : E) 1) × (Fin k → E) |
        dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} := by
    apply measurableSet_le _ measurable_const
    exact (measurable_subtype_coe.comp measurable_fst).dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  apply (le_of_eq (hp.measure_preimage hs.nullMeasurableSet)).trans
  apply (route_cap_bound hδ y hε ha hq hqa k j).trans
  apply mul_le_mul' le_rfl
  exact pow_le_pow_right₀ (one_le_streamFactor (by omega : 0 < q))
    (Nat.add_le_add_right (Nat.div_le_div_right hk) 1)

end StreamTransfer

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Fubini bounds and rotational lower bounds for sequential estimation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section


namespace NoiselessRegression

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
lemma ae_fiber_aemeasurable {f : X × Y → Z} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, AEMeasurable (fun x => f (x,y)) μ := by
  have he := Measure.ae_ae_of_ae_prod hf.prod_swap.ae_eq_mk
  filter_upwards [he] with y hy
  have hm : Measurable (fun x => hf.prod_swap.mk _ (y,x)) :=
    hf.prod_swap.measurable_mk.comp (measurable_const.prodMk measurable_id)
  exact hm.aemeasurable.congr (Filter.EventuallyEq.symm hy)

lemma prod_null_set_bound {S : Set (X × Y)} (hS : NullMeasurableSet S (μ.prod ν))
    {c : ℝ≥0∞} (h : ∀ᵐ y ∂ν, μ {x | (x,y) ∈ S} ≤ c) :
    (μ.prod ν) S ≤ c * ν univ := by
  have hm : AEMeasurable (S.indicator (fun _ => (1 : ℝ≥0∞))) (μ.prod ν) :=
    aemeasurable_const.indicator₀ hS
  rw [← one_mul ((μ.prod ν) S), ← lintegral_indicator_const₀ hS 1, lintegral_prod_symm _ hm]
  apply (lintegral_mono_ae ?_).trans_eq (lintegral_const c)
  filter_upwards [h, ae_fiber_aemeasurable hm] with y hy hmy
  have hs : NullMeasurableSet {x | (x,y) ∈ S} μ := by
    have heq : {x | (x,y) ∈ S} = {x | S.indicator (fun _ => (1 : ℝ≥0∞)) (x,y) = 1} := by
      ext x
      by_cases hx : (x,y) ∈ S <;> simp [hx]
    rw [heq]
    exact nullMeasurableSet_eq_fun hmy aemeasurable_const
  change (∫⁻ x, ({x | (x,y) ∈ S}).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) ≤ c
  simpa [lintegral_indicator_const₀ hs] using hy
end FubiniAux

instance sampleLaw_probability (d T : ℕ) : IsProbabilityMeasure (sampleLaw d T) := by
  unfold sampleLaw
  infer_instance
instance uniformSphere_probability (d : ℕ) [NeZero d] : IsProbabilityMeasure (uniformSphere d) := by
  change IsProbabilityMeasure (sphereLaw (E := Vector d))
  infer_instance

namespace Learner
lemma run_congr_labels {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s t : UnitSphere d) (ω : Ω) (x : Samples d T)
    (h : ∀ i, ⟪x i,s.val⟫ = ⟪x i,t.val⟫) (n : ℕ) :
    L.run s ω x n = L.run t ω x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    split
    · rfl
    · split
      · rw [h]
      · rfl

lemma estimate_congr_labels {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s t : UnitSphere d) (ω : Ω) (x : Samples d T)
    (h : ∀ i, ⟪x i,s.val⟫ = ⟪x i,t.val⟫) : L.estimate s ω x = L.estimate t ω x := by
  simp only [estimate, terminal, run_congr_labels L s t ω x h]

lemma angularSuccess_nullMeasurable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (hL : L.Admissible ρ) :
    NullMeasurableSet {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := by
  apply nullMeasurableSet_le _ aemeasurable_const
  exact Real.continuous_arccos.measurable.comp_aemeasurable
    ((measurable_subtype_coe.comp_aemeasurable hL.uniform_experiment).inner
      (measurable_subtype_coe.comp measurable_fst).aemeasurable)

lemma linear_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 0 < d) (hT : 4*T ≤ d) {ε : ℝ} (hε : ε ≤ 1/10) (hL : L.Admissible ρ) :
    L.uniformSuccess ρ ε ≤ ENNReal.ofReal (21/32 : ℝ) := by
  classical
  let : NeZero d := ⟨hd.ne'⟩
  have hmeas := ae_fiber_aemeasurable hL.uniform_experiment
  unfold uniformSuccess
  refine (prod_null_set_bound (L.angularSuccess_nullMeasurable ρ ε hL)
    (c := ENNReal.ofReal (21/32 : ℝ)) ?_).trans_eq (by simp)
  filter_upwards [hmeas] with z hz
  let U : Submodule ℝ (Vector d) := Submodule.span ℝ (Set.range z.2)
  have hdim : Module.finrank ℝ U ≤ T := by
    have h := finrank_span_le_card (R := ℝ) (Set.range z.2)
    apply h.trans
    rw [Set.toFinset_range]
    exact (Finset.card_image_le).trans_eq (by simp)
  have hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ (Vector d) := by
    simpa only [Vector, finrank_euclideanSpace_fin] using (Nat.mul_le_mul_left 4 hdim).trans hT
  change sphereLaw {s : UnitSphere d | angularError s (L.estimate s z.1 z.2) ≤ ε} ≤ _
  apply sphere_reflection_success_bound U hU
  · exact nullMeasurableSet_le
      (Real.continuous_arccos.measurable.comp_aemeasurable
        ((measurable_subtype_coe.comp_aemeasurable hz).inner measurable_subtype_coe.aemeasurable))
      aemeasurable_const
  · intro s hs ht
    let t := sphereIsometry U.reflection s
    have he : L.estimate s z.1 z.2 = L.estimate t z.1 z.2 := by
      apply L.estimate_congr_labels
      intro i
      have hi : z.2 i ∈ U := Submodule.subset_span (Set.mem_range_self i)
      have he := U.reflection.inner_map_map (z.2 i) s.val
      rw [(Submodule.reflection_eq_self_iff (z.2 i)).2 hi] at he
      exact he.symm
    have hs' : dist s.val (L.estimate s z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos s (L.estimate s z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using hs
    have ht' : dist t.val (L.estimate t z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos t (L.estimate t z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using ht
    calc
      _ = dist s.val t.val := rfl
      _ ≤ dist s.val (L.estimate s z.1 z.2).val + dist (L.estimate s z.1 z.2).val t.val := dist_triangle _ _ _
      _ ≤ ε + ε := by rw [he, dist_comm (L.estimate t z.1 z.2).val t.val] at *; exact add_le_add hs' ht'
      _ ≤ 1/5 := by linarith
end Learner

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Uniform-prior success bounds for finite-state estimators.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section


namespace NoiselessRegression

namespace Learner

lemma frozen_success_bound {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (ω : Ω) (hd : 3 ≤ d)
    (htrans : ∀ t j, AEMeasurable (fun obs => (L.transition t ω j obs).2) (observationReference d))
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤
      (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let δ : ℕ → State M → (Vector d × ℝ) → State M := fun t j => (htrans t j).mk _
  have hδ (t : ℕ) (j : State M) : Measurable (δ t j) := (htrans t j).measurable_mk
  let μ := (uniformSphere d).prod (sampleLaw d T)
  have hgood : ∀ᵐ z ∂μ, ∀ t j (i : Fin T),
      (L.transition t ω j (z.2 i,⟪z.1.val,z.2 i⟫)).2 = δ t j (z.2 i,⟪z.1.val,z.2 i⟫) := by
    simp only [ae_all_iff]
    intro t j i
    exact (sphere_sample_observation_quasi (by simpa using hd) i).ae (htrans t j).ae_eq_mk
  let S : Fin (T+1) → Set (UnitSphere d × Samples d T) := fun t =>
    {z | dist z.1.val (L.output t ω (streamRoute δ 0 t (L.initialChoice ω).2
      ((fun i => z.2 (Fin.castLE (by omega) i)),fun i => ⟪z.1.val,z.2 (Fin.castLE (by omega) i)⟫))).val ≤ ε}
  have hmono : {z : UnitSphere d × Samples d T | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε}
      ≤ᵐ[μ] ⋃ t, S t := by
    filter_upwards [hgood] with z hz
    intro hs
    rcases L.terminal_forced_witness z.1 ω z.2 with ⟨t,ht,he⟩
    have hf : L.forcedRun z.1 ω z.2 t = streamRoute δ 0 t (L.initialChoice ω).2
        ((fun i => z.2 (Fin.castLE ht i)),fun i => ⟪z.1.val,z.2 (Fin.castLE ht i)⟫) := by
      rw [L.forcedRun_eq_route z.1 ω z.2 ht]
      exact streamRoute_congr _ _ 0 t _ _ _ (fun n j i => hz n j (Fin.castLE ht i))
    have hc : dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε := by
      apply le_trans _ hs
      simpa only [angularError, dist_comm] using chord_le_arccos (L.estimate z.1 ω z.2) z.1
    refine Set.mem_iUnion.mpr ⟨⟨t,by omega⟩, ?_⟩
    change dist z.1.val (L.output t ω _) ≤ ε
    simpa only [estimate, he, hf] using hc
  let B : ℝ≥0∞ := (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
    streamFactor (E := Vector d) (J := State M) q ^ (T/q+1)
  have hb (t : Fin (T+1)) : μ (S t) ≤ B := by
    simpa only [B, μ, S, uniformSphere, sphereLaw, sampleLaw, finrank_euclideanSpace_fin] using
      prefix_route_cap_bound hδ (fun j => (L.output t ω j).val) hε
        (by simpa using ha) hq hqa (by omega : (t : ℕ) ≤ T) (L.initialChoice ω).2
  calc
    _ ≤ μ (⋃ t, S t) := measure_mono_ae hmono
    _ ≤ ∑' t, μ (S t) := measure_iUnion_le S
    _ ≤ ∑' _ : Fin (T+1), B := ENNReal.tsum_le_tsum hb
    _ = _ := by simp [B, tsum_fintype, nsmul_eq_mul, mul_assoc]

lemma streaming_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) := by
  let : NeZero d := ⟨by omega⟩
  let : SigmaFinite (observationReference d) := by unfold observationReference; infer_instance
  have hω : ∀ᵐ ω ∂ρ, ∀ t j,
      AEMeasurable (fun obs => (L.transition t ω j obs).2) (observationReference d) := by
    simp only [ae_all_iff]
    intro t j
    filter_upwards [ae_fiber_aemeasurable (hL.transition t j).prod_swap] with ω hω
    exact measurable_snd.comp_aemeasurable hω
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d T) |
    angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    L.angularSuccess_nullMeasurable ρ ε hL
  have he := hp.measure_preimage hS
  have hb := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
      streamFactor (E := Vector d) (J := State M) q ^ (T/q+1))
    (by
      filter_upwards [hω] with ω hω
      exact L.frozen_success_bound ω hd hω hε ha hq hqa)
  simpa only [he, measure_univ, mul_one, S, uniformSuccess] using hb

end Learner

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Real-valued success bounds and accuracy-uniform precision tradeoffs.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section


namespace NoiselessRegression

namespace Learner

lemma streaming_success_bound_real {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (hs : (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) :
    (2/3 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1) := by
  have hb := hs.trans (L.streaming_success_bound ρ hL hd hε ha hq hqa)
  have ht : (T+1 : ℝ≥0∞) *
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
      streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top (by simp)
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · exact ENNReal.pow_ne_top (streamFactor_ne_top q)
  have hr := ENNReal.toReal_mono ht hb
  simpa [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    ENNReal.toReal_add, ENNReal.toReal_natCast, ENNReal.toReal_one,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3*4^d),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ε^a), streamFactor,
    ENNReal.toReal_pow, ← ENNReal.toReal_rpow, finrank_euclideanSpace_fin,
    Fintype.card_fin, State, Nat.cast_pow, Nat.cast_ofNat, Vector] using hr

end Learner

lemma precision_from_stream_bound {d M T a q : ℕ} {ε A : ℝ}
    (hd : 32 ≤ d) (hT : d ≤ 4*T) (hq : 0 < q) (hdq : d ≤ 8*q)
    (ha : d ≤ 4*a) (hM : (M : ℝ) ≤ A * (d : ℝ)^2) (hA : 0 < A)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbound : (2/3 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1)) :
    (1 / (4*(400000+100*A))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hdp : (d : ℝ) ≤ 4*T := by exact_mod_cast hT
  have hdqp : (d : ℝ) ≤ 8*q := by exact_mod_cast hdq
  have hap : (d : ℝ) ≤ 4*a := by exact_mod_cast ha
  have hB : ((T/q+1 : ℕ) : ℝ) * d ≤ 12*T := by
    have hbd : (T/q+1)*d ≤ 12*T := by
      have hmul := Nat.div_mul_le_self T q
      calc
        (T/q+1)*d = (T/q)*d+d := by ring
        _ ≤ (T/q)*(8*q)+d := Nat.add_le_add_right (Nat.mul_le_mul_left _ hdq) _
        _ = 8*((T/q)*q)+d := by ring
        _ ≤ 8*T+d := Nat.add_le_add_right (Nat.mul_le_mul_left 8 hmul) _
        _ ≤ 12*T := by omega
    exact_mod_cast hbd
  have hMq : (M : ℝ) / q ≤ 8*A*d := by
    apply (div_le_iff₀ hq0).2
    calc
      (M : ℝ) ≤ A*d^2 := hM
      _ ≤ A*d*(8*q) := by nlinarith [mul_le_mul_of_nonneg_left hdqp (by positivity : 0 ≤ A*d)]
      _ = 8*A*d*q := by ring
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2/3) hbound
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_rpow (by positivity), Real.log_pow] at hlog
  have hlogε : Real.log (1/ε) = -Real.log ε := by simp
  have hlogε0 : 0 ≤ Real.log (1/ε) := Real.log_nonneg ((le_div_iff₀ hε).2 (by simpa using hε1))
  have heq : (1/(q : ℝ)) * ((M : ℝ)*Real.log 2) = ((M : ℝ)/q)*Real.log 2 := by ring
  rw [heq] at hlog
  have hlT : Real.log ((T : ℝ)+1) ≤ T := by
    simpa using Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T+1)
  have hl3 : Real.log (3 : ℝ) ≤ 3 := Real.log_le_self (by norm_num)
  have hl4 : Real.log (4 : ℝ) ≤ 4 := Real.log_le_self (by norm_num)
  have hl32 : Real.log (32768 : ℝ) ≤ 32768 := Real.log_le_self (by norm_num)
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
  have hl23 : -(1 : ℝ) ≤ Real.log (2/3 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2/3)
    norm_num at h
    linarith
  have hinside : (d : ℝ)*Real.log 32768 + ((M : ℝ)/q)*Real.log 2 ≤
      (32768+8*A)*d := by
    have hm0 : (0 : ℝ) ≤ (M : ℝ)/q := by positivity
    have h1 := mul_le_mul_of_nonneg_left hl32 hd0.le
    have h2 := mul_le_mul_of_nonneg_left hl2 hm0
    nlinarith
  have hfull : ((T/q+1 : ℕ) : ℝ) *
      ((d : ℝ)*Real.log 32768 + ((M : ℝ)/q)*Real.log 2) ≤
      12*T*(32768+8*A) := by
    calc
      _ ≤ ((T/q+1 : ℕ) : ℝ) * ((32768+8*A)*d) :=
        mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg _)
      _ = (32768+8*A)*(((T/q+1 : ℕ) : ℝ)*d) := by ring
      _ ≤ (32768+8*A)*(12*T) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by ring
  have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast (by omega : 4 ≤ d)
  have hlogbound : (a : ℝ)*Real.log (1/ε) ≤ (400000+100*A)*T := by
    have h4 := mul_le_mul_of_nonneg_left hl4 hd0.le
    rw [hlogε]
    nlinarith [mul_nonneg hA.le hT0]
  have hmain : (d : ℝ)*Real.log (1/ε) ≤ 4*(400000+100*A)*T := by
    have ham := mul_le_mul_of_nonneg_right hap hlogε0
    linarith
  have hden : (0 : ℝ) < 4*(400000+100*A) := by positivity
  calc
    _ = ((d : ℝ)*Real.log (1/ε))/(4*(400000+100*A)) := by ring
    _ ≤ T := (div_le_iff₀ hden).2 (by nlinarith [hmain])

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

/-!
Quadratic and subquadratic memory lower bounds for Gaussian regression.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section


namespace NoiselessRegression

theorem fixed_quadratic_memory : FixedQuadraticMemory.{u} := by
  intro A hA
  refine ⟨1/(4*(400000+100*A)), by positivity, 32, ?_⟩
  intro d hd M T hM ε hε hε10 Ω _ ρ hρ L hL hs
  let : IsProbabilityMeasure ρ := hρ
  have hT : d ≤ 4*T := by
    by_contra h
    have hb := hs.trans (L.linear_success_bound ρ (by omega) (by omega) hε10 hL)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    norm_num [ENNReal.toReal_div] at hr
  let q := (d-1)/4
  let a := 2*q
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hqa : 2*q ≤ a := le_rfl
  have ha : 2*a ≤ d-1 := by dsimp [a, q]; omega
  have hdq : d ≤ 8*q := by dsimp [q]; omega
  have hda : d ≤ 4*a := by dsimp [a]; omega
  exact precision_from_stream_bound hd hT (by omega) hdq hda hM hA hε (by linarith)
    (L.streaming_success_bound_real ρ hL (by omega) hε ha hq hqa hs)

section LowerFubini
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
lemma prod_null_set_lower_bound {S : Set (X × Y)} (hS : NullMeasurableSet S (μ.prod ν))
    {c : ℝ≥0∞} (h : ∀ᵐ x ∂μ, c ≤ ν {y | (x,y) ∈ S}) :
    c * μ univ ≤ (μ.prod ν) S := by
  have hm : AEMeasurable (S.indicator (fun _ => (1 : ℝ≥0∞))) (μ.prod ν) :=
    aemeasurable_const.indicator₀ hS
  rw [← one_mul ((μ.prod ν) S), ← lintegral_indicator_const₀ hS 1, lintegral_prod _ hm]
  have hc : c * μ univ = ∫⁻ _ : X, c ∂μ := (lintegral_const c).symm
  rw [hc]
  apply lintegral_mono_ae
  filter_upwards [h, ae_fiber_aemeasurable hm.prod_swap] with x hx hmx
  have hs : NullMeasurableSet {y | (x,y) ∈ S} ν := by
    have heq : {y | (x,y) ∈ S} = {y | S.indicator (fun _ => (1 : ℝ≥0∞)) (x,y) = 1} := by
      ext y
      by_cases hy : (x,y) ∈ S <;> simp [hy]
    rw [heq]
    exact nullMeasurableSet_eq_fun hmx aemeasurable_const
  change c ≤ ∫⁻ y, ({y | (x,y) ∈ S}).indicator (fun _ => (1 : ℝ≥0∞)) y ∂ν
  simpa [lintegral_indicator_const₀ hs] using hx
end LowerFubini

namespace Learner
lemma uniformSuccess_of_pointwise {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 0 < d) (ε : ℝ) {c : ℝ≥0∞}
    (hs : ∀ s, c ≤ L.success ρ ε s) : c ≤ L.uniformSuccess ρ ε := by
  let : NeZero d := ⟨hd.ne'⟩
  have hb := prod_null_set_lower_bound (L.angularSuccess_nullMeasurable ρ ε hL)
    (c := c) (Filter.Eventually.of_forall hs)
  simpa only [measure_univ, mul_one, uniformSuccess] using hb
end Learner

theorem subquadratic_memory : SubquadraticMemory.{u} := by
  obtain ⟨c, hc, d₁, hfixed⟩ := fixed_quadratic_memory (1 : ℝ) (by norm_num)
  refine ⟨c, hc, ?_⟩
  intro M hM
  obtain ⟨d₂, hd₂⟩ := eventually_atTop.1 hM.eventuallyLE
  refine ⟨max d₁ (max d₂ 1), ?_⟩
  intro d hd T ε hε hε10 Ω _ ρ hρ L hL hs
  let : IsProbabilityMeasure ρ := hρ
  have hmem : (M d : ℝ) ≤ 1 * (d : ℝ)^2 := by
    have hm := hd₂ d (by omega)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (M d) : (0 : ℝ) ≤ M d),
      abs_of_nonneg (sq_nonneg (d : ℝ)), one_mul] using hm
  apply hfixed d (by omega) (M d) T hmem ε hε hε10 Ω ρ hρ L hL
  rcases hs with hs | hs
  · exact hs
  · exact L.uniformSuccess_of_pointwise ρ hL (by omega) ε hs

theorem main : SubquadraticMemory.{u} ∧ FixedQuadraticMemory.{u} :=
  ⟨subquadratic_memory, fixed_quadratic_memory⟩

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments

lemma volume_preserving_curry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℝ) := by
  apply MeasurePreserving.symm (MeasurableEquiv.curry ι κ ℝ).symm
  refine ⟨(MeasurableEquiv.curry ι κ ℝ).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have he : (MeasurableEquiv.curry ι κ ℝ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i,j))) := by
    ext x
    simp [Set.mem_pi, MeasurableEquiv.curry, Function.uncurry]
  rw [he, volume_pi_pi]
  simp_rw [volume_pi_pi]
  exact (Fintype.prod_prod_type (fun p : ι × κ => (volume : Measure ℝ) (s p))).symm

lemma volume_preserving_transpose (m n : ℕ) :
    MeasurePreserving (fun A : Fin m → Fin n → ℝ => fun i j => A j i) := by
  have h1 := (volume_preserving_curry (Fin m) (Fin n)).symm
  have h2 := volume_measurePreserving_piCongrLeft
    (fun _ : Fin n × Fin m => ℝ) (Equiv.prodComm (Fin m) (Fin n))
  have h3 := volume_preserving_curry (Fin n) (Fin m)
  exact h3.comp (h2.comp h1)

section GaussianGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_graph_kernel_bound {n : ℕ} (v : Fin n → E)
    (hv : LinearIndependent ℝ v) (m : ℕ)
    (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ y, φ y = 1) (b : Fin m → ℝ) :
    ∫⁻ A : Fin m → E, ∏ i, φ (fun j => b j - ⟪v i, A j⟫)
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) := by
  let H : (Fin m → Fin n → ℝ) → ℝ≥0∞ :=
    fun Z => ∏ i, φ (fun j => b j - Z j i)
  have hH : Measurable H := by dsimp [H]; fun_prop
  change (∫⁻ A : Fin m → E, H (fun j i => ⟪v i, A j⟫)
    ∂Measure.pi (fun _ => stdGaussian E)) ≤ _
  rw [← lintegral_map hH (by fun_prop)]
  calc
    _ ≤ ∫⁻ Z, H Z ∂(ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) •
        (volume : Measure (Fin m → Fin n → ℝ))) :=
      lintegral_mono' (NoiselessRegression.gaussian_rows_pairings_le v hv m) (fun _ => le_rfl)
    _ = ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) := by
      rw [lintegral_smul_measure]
      have hL : ∫⁻ Z, H Z = 1 := by
        have h := (volume_preserving_transpose m n).lintegral_comp
          (show Measurable (fun Z : Fin n → Fin m → ℝ => ∏ i, φ (b - Z i)) by fun_prop)
        change (∫⁻ Z : Fin m → Fin n → ℝ, ∏ i, φ (b - fun j => Z j i)) = _ at h
        rw [show (∫⁻ Z, H Z) = ∫⁻ Z : Fin n → Fin m → ℝ, ∏ i, φ (b - Z i) from h]
        rw [volume_pi, NoiselessRegression.lintegral_fin_prod volume n
          (fun _ y => φ (b - y)) (by intro i; fun_prop)]
        simp_rw [lintegral_sub_left_eq_self φ b, hφ1]
        simp
      simp [hL, smul_eq_mul]

lemma measurable_vectorSmoothing (ν : Measure E) [SFinite ν] (m : ℕ)
    (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (vectorSmoothing ν m φ) := by
  apply Measurable.lintegral_prod_right
  exact hφ.comp (by fun_prop)

theorem vectorSmoothing_graph_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m q : ℕ) (hmargin : (q : ℝ) + m ≤ a)
    (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ y, φ y = 1) (z : E) (b : Fin m → ℝ) :
    ∫⁻ A : Fin m → E,
      (vectorSmoothing ν m φ (A, fun j => ⟪z, A j⟫ + b j)) ^ q
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      (NoiselessRegression.replicaConstant ν a m) ^ q := by
  have he (A : Fin m → E) (t : E) :
      (fun j => (⟪z, A j⟫ + b j) - ⟪t, A j⟫) =
        (fun j => b j - ⟪t-z, A j⟫) := by
    funext j
    rw [inner_sub_left]
    ring
  simp only [vectorSmoothing, he]
  have hp (A : Fin m → E) := NoiselessRegression.lintegral_pow_pi ν
    (fun t => φ (fun j => b j - ⟪t-z, A j⟫)) (by fun_prop) q
  simp_rw [hp]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ ≤ ∫⁻ v : Fin q → E, NoiselessRegression.replicaWeight m z v
        ∂Measure.pi (fun _ => ν) := by
      apply lintegral_mono_ae
      filter_upwards [NoiselessRegression.ae_replica_linearIndependent hν hsupport z q
        (le_trans (le_add_of_nonneg_right (Nat.cast_nonneg m)) hmargin)] with v hv
      rw [NoiselessRegression.replicaWeight_eq_det, NoiselessRegression.sqrt_det_gram]
      exact gaussian_graph_kernel_bound (fun i => v i - z) hv m φ hφ hφ1 b
    _ ≤ _ := NoiselessRegression.replica_integral_bound hν hsupport m z q hmargin
end GaussianGraph

lemma measurable_ballKernel (m : ℕ) (η : ℝ) : Measurable (ballKernel m η) := by
  exact (measurable_const.indicator Metric.isClosed_closedBall.measurableSet).comp
    (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable

lemma ballKernel_integral (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∫⁻ y, ballKernel m η y = 1 := by
  have hm : Measurable ((Metric.closedBall (0 : Label m) η).indicator
      (fun _ => (volume (Metric.closedBall (0 : Label m) η))⁻¹)) :=
    measurable_const.indicator Metric.isClosed_closedBall.measurableSet
  change (∫⁻ y, (Metric.closedBall (0 : Label m) η).indicator
    (fun _ => (volume (Metric.closedBall (0 : Label m) η))⁻¹) (WithLp.toLp 2 y)) = 1
  rw [(PiLp.volume_preserving_toLp (Fin m)).lintegral_comp hm,
    lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp only [lintegral_const, Measure.restrict_apply_univ]
  apply ENNReal.inv_mul_cancel
  · exact ne_of_gt ((Metric.isOpen_ball.measure_pos volume
      (Metric.nonempty_ball.mpr hη)).trans_le (measure_mono Metric.ball_subset_closedBall))
  · exact (isCompact_closedBall (0 : Label m) η).measure_lt_top.ne

section BallDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma rowMap_apply {m : ℕ} (A : Fin m → E) (t : E) :
    rowMap A t = WithLp.toLp 2 (fun j => ⟪t, A j⟫) := by
  ext j
  simp [rowMap, real_inner_comm]

lemma measurable_ballAverage (ν : Measure E) [SFinite ν] (m : ℕ) (η : ℝ) :
    Measurable (ballAverage ν m η) := by
  exact (measurable_vectorSmoothing ν m (ballKernel m η)
    (measurable_ballKernel m η)).comp
      (measurable_fst.prodMk ((PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ)).measurable.comp
        measurable_snd))

omit [FiniteDimensional ℝ E] in
lemma ballAverage_eq (ν : Measure E) [SFinite ν] (m : ℕ) (η : ℝ)
    (A : Fin m → E) (y : Label m) :
    ballAverage ν m η (A,y) =
      (ν.map (rowMap A)) (Metric.closedBall y η) /
        volume (Metric.closedBall y η) := by
  have he (t : E) :
      (fun j => WithLp.ofLp y j - ⟪t, A j⟫) = WithLp.ofLp (y - rowMap A t) := by
    simp only [rowMap_apply, WithLp.ofLp_sub]
    rfl
  have hpoint (t : E) :
      ballKernel m η (fun j => WithLp.ofLp y j - ⟪t, A j⟫) =
        (Metric.closedBall y η).indicator
          (fun _ => (volume (Metric.closedBall y η))⁻¹) (rowMap A t) := by
    rw [ballKernel, he, WithLp.toLp_ofLp, Measure.addHaar_closedBall_center volume y]
    have hh : y - rowMap A t ∈ Metric.closedBall (0 : Label m) η ↔
        rowMap A t ∈ Metric.closedBall y η := by
      simp [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    by_cases h : rowMap A t ∈ Metric.closedBall y η
    · simp only [Set.indicator_of_mem h, Set.indicator_of_mem (hh.mpr h)]
    · simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem (not_congr hh |>.mpr h)]
  simp only [ballAverage, vectorSmoothing, hpoint]
  rw [← lintegral_map (measurable_const.indicator Metric.isClosed_closedBall.measurableSet)
    (rowMap A).continuous.measurable,
    lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp [div_eq_mul_inv, mul_comm]

lemma measurable_lowerDensity (ν : Measure E) [SFinite ν] (m : ℕ) :
    Measurable (lowerDensity ν m) :=
  Measurable.liminf (fun _n => measurable_ballAverage ν m _)

lemma ballAverage_graph_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m q : ℕ) (hmargin : (q : ℝ) + m ≤ a)
    (z : E) (b : Label m) {η : ℝ} (hη : 0 < η) :
    ∫⁻ A : Fin m → E, (ballAverage ν m η (A, rowMap A z + b)) ^ q
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      (NoiselessRegression.replicaConstant ν a m) ^ q := by
  simpa only [ballAverage, rowMap_apply, WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_def] using
    vectorSmoothing_graph_moment hν hsupport m q hmargin (ballKernel m η)
      (measurable_ballKernel m η) (ballKernel_integral m hη) z (WithLp.ofLp b)

theorem lowerDensity_graph_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m q : ℕ) (hmargin : (q : ℝ) + m ≤ a) (z : E) (b : Label m) :
    ∫⁻ A : Fin m → E, (lowerDensity ν m (A, rowMap A z + b)) ^ q
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      (NoiselessRegression.replicaConstant ν a m) ^ q := by
  have hp (u : ℕ → ℝ≥0∞) : (liminf u atTop) ^ q = liminf (fun n => u n ^ q) atTop :=
    (show Monotone (fun x : ℝ≥0∞ => x ^ q) from (fun _ _ h => pow_le_pow_left' h q)).map_liminf_of_continuousAt
      u (ENNReal.continuous_pow q).continuousAt
  simp only [lowerDensity, hp]
  apply (lintegral_liminf_le (fun n => ?_)).trans
  · apply liminf_le_of_frequently_le'
    exact Filter.Frequently.of_forall (fun n => ballAverage_graph_moment hν hsupport m q hmargin z b
      (inv_pos.mpr (by positivity)))
  · apply Measurable.pow_const
    apply (measurable_ballAverage ν m _).comp
    exact measurable_id.prodMk (by simp only [rowMap_apply]; fun_prop)

theorem lowerDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (hA : ν.map (rowMap A) ≪ (volume : Measure (Label m))) :
    volume.withDensity (fun y => lowerDensity ν m (A,y)) = ν.map (rowMap A) := by
  let ρ := ν.map (rowMap A)
  let v := IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure (Label m)) 1
  have hneg : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun n => ?_)⟩
    · simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · change (0 : ℝ) < ((n : ℝ) + 1)⁻¹
      positivity
  have hae : (fun y => lowerDensity ν m (A,y)) =ᵐ[volume] ρ.rnDeriv volume := by
    filter_upwards [v.ae_tendsto_rnDeriv_of_absolutelyContinuous hA] with y hy
    have ht := IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt volume
      (K := (1 : ℝ)) (x := y) (fun _ : ℕ => y) (fun n => ((n : ℝ) + 1)⁻¹) hneg
      (Filter.Eventually.of_forall (fun n => Metric.mem_closedBall_self (by positivity)))
    have hlim := (hy.comp ht).liminf_eq
    simpa only [lowerDensity, ballAverage_eq, ρ, Function.comp_def] using hlim
  rw [withDensity_congr_ae hae]
  exact Measure.withDensity_rnDeriv_eq _ _ hA

lemma ballAverage_eq_zero_of_far (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (z : E) (R η : ℝ) (y : Label m)
    (hsupport : ν.support ⊆ Metric.closedBall z R)
    (hfar : ‖rowMap A‖ * R + η < ‖y - rowMap A z‖) :
    ballAverage ν m η (A,y) = 0 := by
  have hz : (ν.map (rowMap A)) (Metric.closedBall y η) = 0 := by
    rw [Measure.map_apply (rowMap A).continuous.measurable Metric.isClosed_closedBall.measurableSet]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ν.support_mem_ae] with t ht hty
    have htR : ‖t-z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hsupport ht
    have hty' : ‖y - rowMap A t‖ ≤ η := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hty
    have hn : ‖rowMap A t - rowMap A z‖ ≤ ‖rowMap A‖ * R := by
      rw [← map_sub]
      exact ((rowMap A).le_opNorm _).trans (mul_le_mul_of_nonneg_left htR (norm_nonneg _))
    have hb : ‖y - rowMap A z‖ ≤ η + ‖rowMap A‖ * R := by
      calc
        _ = ‖(y - rowMap A t) + (rowMap A t - rowMap A z)‖ := by congr 1; abel
        _ ≤ ‖y - rowMap A t‖ + ‖rowMap A t - rowMap A z‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hty' hn
    linarith
  simp only [ballAverage_eq, hz, ENNReal.zero_div]

theorem lowerDensity_eq_zero_of_far (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (z : E) (R : ℝ) (y : Label m)
    (hsupport : ν.support ⊆ Metric.closedBall z R)
    (hfar : ‖rowMap A‖ * R < ‖y - rowMap A z‖) :
    lowerDensity ν m (A,y) = 0 := by
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he : ∀ᶠ n : ℕ in atTop, ballAverage ν m ((n : ℝ) + 1)⁻¹ (A,y) = 0 := by
    filter_upwards [ht (Iio_mem_nhds (sub_pos.mpr hfar))] with n hn
    apply ballAverage_eq_zero_of_far ν m A z R _ y hsupport
    have hnn : ((n : ℝ) + 1)⁻¹ < ‖y - rowMap A z‖ - ‖rowMap A‖ * R := hn
    linarith
  exact (liminf_congr he).trans (liminf_const _)
end BallDensity

section Rescaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rescale (z : E) (R : ℝ) (x : E) : E := R⁻¹ • (x-z)
def dilate (z : E) (R : ℝ) (x : E) : E := R • x + z

omit [FiniteDimensional ℝ E] in
@[fun_prop] lemma measurable_rescale (z : E) (R : ℝ) : Measurable (rescale z R) := by
  unfold rescale; fun_prop
omit [FiniteDimensional ℝ E] in
@[fun_prop] lemma measurable_dilate (z : E) (R : ℝ) : Measurable (dilate z R) := by
  unfold dilate; fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dilate_rescale (z : E) {R : ℝ} (hR : R ≠ 0) (x : E) :
    dilate z R (rescale z R x) = x := by
  simp [dilate, rescale, smul_smul, hR]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rescale_preimage_closedBall (z b : E) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    rescale z R ⁻¹' Metric.closedBall b t = Metric.closedBall (dilate z R b) (R*t) := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  have he : rescale z R x - b = R⁻¹ • (x - dilate z R b) := by
    simp [rescale, dilate, smul_sub, smul_add, smul_smul, hR.ne', sub_sub, add_comm]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  rw [inv_mul_le_iff₀ hR]

def normalizedRescale (ν : Measure E) (K a : ℝ) (z : E) (R : ℝ) : Measure E :=
  (ENNReal.ofReal (K * R ^ a))⁻¹ • ν.map (rescale z R)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma normalizedRescale_finite (ν : Measure E) [IsFiniteMeasure ν]
    (K a : ℝ) (z : E) (R : ℝ) (hKR : 0 < K * R ^ a) :
    IsFiniteMeasure (normalizedRescale ν K a z R) := by
  dsimp [normalizedRescale]
  exact Measure.smul_finite _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hKR))

omit [FiniteDimensional ℝ E] in
lemma normalizedRescale_local {ν : Measure E} {K a : ℝ} (hν : AllBallMass ν K a)
    (hK : 0 < K) (z : E) {R : ℝ} (hR : 0 < R) :
    NoiselessRegression.HasLocalMassBound (normalizedRescale ν K a z R) a := by
  intro b _ t ht
  rw [normalizedRescale, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_rescale z R) Metric.isClosed_closedBall.measurableSet,
    rescale_preimage_closedBall z b hR]
  apply (mul_le_mul' le_rfl (hν (dilate z R b) (R*t) (mul_pos hR ht))).trans
  rw [Real.mul_rpow hR.le ht.le, ← mul_assoc,
    ENNReal.ofReal_mul (mul_nonneg hK.le (Real.rpow_nonneg hR.le a)),
    ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
      ENNReal.ofReal_ne_top, one_mul]

lemma normalizedRescale_support {ν : Measure E} (K a : ℝ) (z : E) {R : ℝ}
    (hR : 0 < R) (hsupport : ν.support ⊆ Metric.closedBall z R) :
    (normalizedRescale ν K a z R).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  apply Measure.smul_absolutelyContinuous.ae_le
  change ∀ᵐ x ∂ν.map (rescale z R), x ∈ Metric.closedBall 0 1
  apply (ae_map_iff (measurable_rescale z R).aemeasurable
    (show MeasurableSet {x : E | x ∈ Metric.closedBall 0 1} from
      Metric.isClosed_closedBall.measurableSet)).mpr
  filter_upwards [ν.support_mem_ae] with x hx
  have he := rescale_preimage_closedBall z (0 : E) hR (1 : ℝ)
  have hx' : x ∈ rescale z R ⁻¹' Metric.closedBall 0 1 := by
    rw [he]
    simpa [dilate] using hsupport hx
  exact hx'

omit [FiniteDimensional ℝ E] in
lemma normalizedRescale_recover (ν : Measure E) (K a : ℝ) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (K * R ^ a) • (normalizedRescale ν K a z R).map (dilate z R) = ν := by
  rw [normalizedRescale, Measure.map_smul, smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top,
    one_smul, Measure.map_map (measurable_dilate z R) (measurable_rescale z R)]
  have he : dilate z R ∘ rescale z R = id := by
    funext x; exact dilate_rescale z hR.ne' x
  rw [he, Measure.map_id]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma ballAverage_smul (ν : Measure E) (c : ℝ≥0∞) (m : ℕ) (η : ℝ)
    (A : Fin m → E) (y : Label m) :
    ballAverage (c • ν) m η (A,y) = c * ballAverage ν m η (A,y) := by
  simp only [ballAverage, vectorSmoothing, lintegral_smul_measure, smul_eq_mul]

lemma ballAverage_dilate (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (z : E) {R η : ℝ} (hR : 0 < R) (hη : 0 < η) (A : Fin m → E) (b : Label m) :
    ballAverage (ν.map (dilate z R)) m η (A, rowMap A z + b) =
      (ENNReal.ofReal (R ^ m))⁻¹ * ballAverage ν m (η/R) (A, R⁻¹ • b) := by
  rw [ballAverage_eq, ballAverage_eq]
  have hn : ((ν.map (dilate z R)).map (rowMap A)) (Metric.closedBall (rowMap A z + b) η) =
      (ν.map (rowMap A)) (Metric.closedBall (R⁻¹ • b) (η/R)) := by
    rw [Measure.map_apply (rowMap A).continuous.measurable Metric.isClosed_closedBall.measurableSet,
      Measure.map_apply (measurable_dilate z R)
        (Metric.isClosed_closedBall.measurableSet.preimage (rowMap A).continuous.measurable),
      Measure.map_apply (rowMap A).continuous.measurable Metric.isClosed_closedBall.measurableSet]
    congr 1
    ext x
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    have he : rowMap A (dilate z R x) - (rowMap A z + b) =
        R • (rowMap A x - R⁻¹ • b) := by
      simp only [dilate, map_add, map_smul, smul_sub, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
      abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hR, le_div_iff₀ hR, mul_comm]
  have hv : volume (Metric.closedBall (rowMap A z + b) η) =
      ENNReal.ofReal (R ^ m) * volume (Metric.closedBall (R⁻¹ • b) (η/R)) := by
    rw [Measure.addHaar_closedBall volume _ hη.le,
      Measure.addHaar_closedBall volume _ (div_pos hη hR).le,
      finrank_euclideanSpace_fin, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      ← mul_pow, mul_div_cancel₀ _ hR.ne']
  rw [hn, hv, ENNReal.div_eq_inv_mul, ENNReal.mul_inv
    (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))) (Or.inl ENNReal.ofReal_ne_top)]
  rw [ENNReal.div_eq_inv_mul, mul_assoc]

lemma normalizedRescale_mass {ν : Measure E} {K a : ℝ} (hν : AllBallMass ν K a)
    (hK : 0 < K) (z : E) {R : ℝ} (hR : 0 < R)
    (hsupport : ν.support ⊆ Metric.closedBall z R) :
    normalizedRescale ν K a z R Set.univ ≤ 1 := by
  have he : ν Set.univ = ν (Metric.closedBall z R) := by
    apply measure_congr
    filter_upwards [ν.support_mem_ae] with x hx
    apply propext
    exact iff_of_true (Set.mem_univ x) (hsupport hx)
  rw [normalizedRescale, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_rescale z R) MeasurableSet.univ, Set.preimage_univ, he]
  exact (mul_le_mul' le_rfl (hν z R hR)).trans_eq
    (ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top)

lemma ballAverage_normalizedRescale {ν : Measure E} [IsFiniteMeasure ν]
    (K a : ℝ) (hK : 0 < K) (z : E) {R η : ℝ} (hR : 0 < R) (hη : 0 < η)
    (m : ℕ) (A : Fin m → E) (b : Label m) :
    ballAverage ν m η (A, rowMap A z + b) =
      ENNReal.ofReal (K * R ^ (a-m)) *
        ballAverage (normalizedRescale ν K a z R) m (η/R) (A, R⁻¹ • b) := by
  let μ := normalizedRescale ν K a z R
  have : IsFiniteMeasure μ := normalizedRescale_finite ν K a z R (by positivity)
  conv_lhs => rw [← normalizedRescale_recover ν K a hK z hR]
  rw [ballAverage_smul, ballAverage_dilate μ m z hR hη, ← mul_assoc]
  congr 1
  rw [Real.rpow_sub_natCast hR.ne', ← mul_div_assoc, ENNReal.ofReal_div_of_pos (by positivity)]
  rfl

theorem ballAverage_graph_moment_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) (hsupport : ν.support ⊆ Metric.closedBall z R)
    (m q : ℕ) (hmargin : (q : ℝ) + m ≤ a) (b : Label m) {η : ℝ} (hη : 0 < η) :
    ∫⁻ A : Fin m → E, (ballAverage ν m η (A, rowMap A z + b)) ^ q
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      (ENNReal.ofReal (K * R ^ (a-m)) *
        (1 + ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * (4 : ℝ)^a) *
          (2 : ℝ≥0∞)^(m+1))) ^ q := by
  let μ := normalizedRescale ν K a z R
  have : IsFiniteMeasure μ := normalizedRescale_finite ν K a z R (by positivity)
  have hl := normalizedRescale_local hν hK z hR
  have hs := normalizedRescale_support K a z hR hsupport
  have hc : NoiselessRegression.replicaConstant μ a m ≤
      1 + ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * (4 : ℝ)^a) * (2 : ℝ≥0∞)^(m+1) := by
    exact add_le_add (normalizedRescale_mass hν hK z hR hsupport) le_rfl
  simp_rw [ballAverage_normalizedRescale K a hK z hR hη, mul_pow]
  rw [lintegral_const_mul _ (by apply Measurable.pow_const; exact
    (measurable_ballAverage μ m (η/R)).comp (measurable_id.prodMk measurable_const))]
  apply mul_le_mul' le_rfl
  have hm := ballAverage_graph_moment hl hs m q hmargin (0 : E)
    (R⁻¹ • b) (div_pos hη hR)
  have hz (A : Fin m → E) : rowMap A (0 : E) = 0 := map_zero (rowMap A)
  simp only [hz, zero_add] at hm
  exact hm.trans (pow_le_pow_left' hc q)

theorem lowerDensity_graph_moment_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) (hsupport : ν.support ⊆ Metric.closedBall z R)
    (m q : ℕ) (hmargin : (q : ℝ) + m ≤ a) (b : Label m) :
    ∫⁻ A : Fin m → E, (lowerDensity ν m (A, rowMap A z + b)) ^ q
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      (ENNReal.ofReal (K * R ^ (a-m)) *
        (1 + ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * (4 : ℝ)^a) *
          (2 : ℝ≥0∞)^(m+1))) ^ q := by
  have hp (u : ℕ → ℝ≥0∞) : (liminf u atTop) ^ q = liminf (fun n => u n ^ q) atTop :=
    (show Monotone (fun x : ℝ≥0∞ => x ^ q) from (fun _ _ h => pow_le_pow_left' h q)).map_liminf_of_continuousAt
      u (ENNReal.continuous_pow q).continuousAt
  simp only [lowerDensity, hp]
  apply (lintegral_liminf_le (fun n => ?_)).trans
  · apply liminf_le_of_frequently_le'
    exact Filter.Frequently.of_forall (fun n => ballAverage_graph_moment_scaled hν hK z hR
      hsupport m q hmargin b (inv_pos.mpr (by positivity)))
  · apply Measurable.pow_const
    apply (measurable_ballAverage ν m _).comp
    exact measurable_id.prodMk (by simp only [rowMap_apply]; fun_prop)

end Rescaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_vector_replica_bound {n : ℕ} (p : E) (v : Fin n → E)
    (hv : LinearIndependent ℝ (fun i => v i - p))
    (m : ℕ) (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ y, φ y = 1) :
    ∫⁻ A : Fin m → E, ∫⁻ y : Fin m → ℝ,
      φ (fun j => y j - ⟪p, A j⟫) *
        ∏ i, φ (fun j => y j - ⟪v i, A j⟫)
      ∂volume ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i-p) i‖)⁻¹ ^ m) := by
  have ht (A : Fin m → E) :
      (∫⁻ y : Fin m → ℝ, φ (fun j => y j - ⟪p, A j⟫) *
        ∏ i, φ (fun j => y j - ⟪v i, A j⟫)) =
      ∫⁻ y : Fin m → ℝ, φ y * ∏ i, φ (fun j => y j - ⟪v i-p, A j⟫) := by
    have he (y : Fin m → ℝ) (i : Fin n) :
        (fun j => y j - ⟪p, A j⟫ - ⟪v i-p, A j⟫) =
        (fun j => y j - ⟪v i, A j⟫) := by
      funext j; rw [inner_sub_left]; ring
    convert (lintegral_sub_right_eq_self (μ := (volume : Measure (Fin m → ℝ)))
        (fun y : Fin m → ℝ => φ y * ∏ i, φ (fun j => y j - ⟪v i-p, A j⟫))
        (fun j => ⟪p, A j⟫)) using 1
    apply lintegral_congr
    intro y
    simp only [Pi.sub_apply, he]
    rfl
  simp_rw [ht]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ ≤ ∫⁻ y, φ y * ENNReal.ofReal
        ((∏ i, ‖gramSchmidt ℝ (fun i => v i-p) i‖)⁻¹ ^ m) := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [lintegral_const_mul _ (by fun_prop)]
      exact mul_le_mul' le_rfl (gaussian_graph_kernel_bound _ hv m φ hφ hφ1 y)
    _ = _ := by rw [lintegral_mul_const _ hφ, hφ1, one_mul]

lemma vectorSmoothing_pow (ν : Measure E) [IsFiniteMeasure ν]
    (m n : ℕ) (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (z : (Fin m → E) × (Fin m → ℝ)) :
    (vectorSmoothing ν m φ z)^(n+1) =
      ∫⁻ w : E × (Fin n → E),
        φ (fun j => z.2 j - ⟪w.1, z.1 j⟫) *
          ∏ i, φ (fun j => z.2 j - ⟪w.2 i, z.1 j⟫)
        ∂ν.prod (Measure.pi (fun _ => ν)) := by
  rw [lintegral_prod _ (by fun_prop)]
  have hG : Measurable (fun v : Fin n → E =>
      ∏ i, φ (fun j => z.2 j - ⟪v i, z.1 j⟫)) := by fun_prop
  simp_rw [lintegral_const_mul _ hG]
  rw [lintegral_mul_const _ (by fun_prop), ← NoiselessRegression.lintegral_pow_pi ν
    (fun t : E => φ (fun j => z.2 j - ⟪t, z.1 j⟫)) (by fun_prop) n]
  exact pow_succ' _ _

theorem vectorSmoothing_integrated_moment {m : ℕ} {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ y, φ y = 1)
    (n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ z : (Fin m → E) × (Fin m → ℝ), (vectorSmoothing ν m φ z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
      ν Set.univ * (NoiselessRegression.replicaConstant ν a m)^n := by
  simp_rw [vectorSmoothing_pow ν m n φ hφ]
  rw [lintegral_lintegral_swap (by fun_prop), lintegral_prod _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ p, ∫⁻ v : Fin n → E, NoiselessRegression.replicaWeight m p v
        ∂Measure.pi (fun _ => ν) ∂ν := by
      apply lintegral_mono
      intro p
      apply lintegral_mono_ae
      filter_upwards [NoiselessRegression.ae_replica_linearIndependent hν hsupport p n
        (le_trans (le_add_of_nonneg_right (Nat.cast_nonneg m)) hmargin)] with v hv
      rw [lintegral_prod _ (by fun_prop), NoiselessRegression.replicaWeight_eq_det,
        NoiselessRegression.sqrt_det_gram]
      exact gaussian_vector_replica_bound p v hv m φ hφ hφ1
    _ ≤ ∫⁻ _p, (NoiselessRegression.replicaConstant ν a m)^n ∂ν :=
      lintegral_mono fun p => NoiselessRegression.replica_integral_bound hν hsupport m p n hmargin
    _ = _ := by rw [lintegral_const, mul_comm]

theorem ballAverage_integrated_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hmargin : (n : ℝ) + m ≤ a) {η : ℝ} (hη : 0 < η) :
    ∫⁻ z : (Fin m → E) × Label m, (ballAverage ν m η z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
      ν Set.univ * (NoiselessRegression.replicaConstant ν a m)^n := by
  have hm := (MeasurePreserving.id (Measure.pi (fun _ : Fin m => stdGaussian E))).prod
    (PiLp.volume_preserving_toLp (Fin m))
  rw [← hm.lintegral_comp ((measurable_ballAverage ν m η).pow_const (n+1))]
  exact vectorSmoothing_integrated_moment hν hsupport _ (measurable_ballKernel m η)
    (ballKernel_integral m hη) n hmargin

theorem lowerDensity_integrated_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ z : (Fin m → E) × Label m, (lowerDensity ν m z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
      ν Set.univ * (NoiselessRegression.replicaConstant ν a m)^n := by
  have hp (u : ℕ → ℝ≥0∞) : (liminf u atTop) ^ (n+1) =
      liminf (fun j => u j ^ (n+1)) atTop :=
    (show Monotone (fun x : ℝ≥0∞ => x ^ (n+1)) from
      (fun _ _ h => pow_le_pow_left' h (n+1))).map_liminf_of_continuousAt
      u (ENNReal.continuous_pow (n+1)).continuousAt
  simp only [lowerDensity, hp]
  apply (lintegral_liminf_le (fun j => (measurable_ballAverage ν m _).pow_const _)).trans
  apply liminf_le_of_frequently_le'
  exact Filter.Frequently.of_forall (fun j => ballAverage_integrated_moment hν hsupport m n
    hmargin (inv_pos.mpr (by positivity)))

end ProjectionMoments
end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_le_volume : stdGaussian E ≤ volume := by
  let b := stdOrthonormalBasis ℝ E
  have hp : MeasurePreserving (fun x : Fin (Module.finrank ℝ E) → ℝ =>
      ∑ i, x i • b i) (volume : Measure (Fin (Module.finrank ℝ E) → ℝ)) volume := by
    have he : (fun x : Fin (Module.finrank ℝ E) → ℝ => ∑ i, x i • b i) =
        (fun x => b.repr.symm (WithLp.toLp 2 x)) := by
      funext x
      exact b.sum_repr_symm (WithLp.toLp 2 x)
    rw [he]
    exact b.measurePreserving_repr_symm.comp
      (PiLp.volume_preserving_toLp (Fin (Module.finrank ℝ E)))
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, ← hp.map_eq]
  exact Measure.map_mono (NoiselessRegression.pi_gaussianReal_le_volume _) hp.measurable

lemma stdGaussian_submodule_null (S : Submodule ℝ E) (hS : S ≠ ⊤) :
    stdGaussian E S = 0 := by
  apply le_antisymm _ zero_le
  exact (stdGaussian_le_volume (E := E) S).trans_eq (Measure.addHaar_submodule volume S hS)

lemma gaussian_rows_ae_gramSchmidt_ne_zero (m : ℕ) (hm : m ≤ Module.finrank ℝ E) :
    ∀ᵐ A : Fin m → E ∂Measure.pi (fun _ => stdGaussian E), ∀ i, gramSchmidt ℝ A i ≠ 0 := by
  induction m with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ m ih =>
    rw [NoiselessRegression.ae_pi_snoc _ (by
      simpa only [sub_zero] using NoiselessRegression.measurableSet_gramSchmidt_ne_zero (0 : E) (m+1))]
    filter_upwards [ih (by omega)] with v hv
    let S := Submodule.span ℝ (Set.range v)
    have hd : Module.finrank ℝ S ≤ m := by
      simpa only [S, Fintype.card_fin, Set.finrank] using finrank_range_le_card (R := ℝ) v
    have hs : S ≠ ⊤ := by
      intro he
      rw [he, finrank_top] at hd
      omega
    have ha : ∀ᵐ x ∂stdGaussian E, x ∉ S := by
      rw [ae_iff]
      convert stdGaussian_submodule_null S hs using 2
      ext x
      simp
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [NoiselessRegression.norm_gramSchmidt_eq_infDist,
        NoiselessRegression.image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact ne_of_gt ((S.closed_of_finiteDimensional.notMem_iff_infDist_pos
        ⟨0, S.zero_mem⟩).mp hx)
    | cast j => simpa only [NoiselessRegression.gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

lemma gaussian_rows_ae_linearIndependent (m : ℕ) (hm : m ≤ Module.finrank ℝ E) :
    ∀ᵐ A : Fin m → E ∂Measure.pi (fun _ => stdGaussian E), LinearIndependent ℝ A := by
  filter_upwards [gaussian_rows_ae_gramSchmidt_ne_zero m hm] with A hA
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [NoiselessRegression.det_gram_eq_prod_gramSchmidt]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hA i))

lemma lintegral_gaussianReal_sq :
    ∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂gaussianReal 0 1 = 1 := by
  have hi : Integrable (fun x : ℝ => x^2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' 2 (by norm_num)).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x => sq_nonneg x))]
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at hv
  simpa only [integral_id_gaussianReal, sub_zero, NNReal.coe_one, ENNReal.ofReal_one] using
    congrArg ENNReal.ofReal hv

lemma lintegral_stdGaussian_norm_sq :
    ∫⁻ x : E, ENNReal.ofReal (‖x‖^2) ∂stdGaussian E = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, lintegral_map (by fun_prop) (by fun_prop)]
  have he (x : Fin (Module.finrank ℝ E) → ℝ) :
      ‖∑ i, x i • b i‖^2 = ∑ i, (x i)^2 := by
    rw [b.sum_repr_symm (WithLp.toLp 2 x), LinearIsometryEquiv.norm_map]
    exact EuclideanSpace.real_norm_sq_eq _
  simp_rw [he, ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  rw [lintegral_finsetSum _ (fun i _ => by fun_prop)]
  have hi (i : Fin (Module.finrank ℝ E)) :
      ∫⁻ x : Fin (Module.finrank ℝ E) → ℝ, ENNReal.ofReal (x i ^ 2)
        ∂Measure.pi (fun _ => gaussianReal 0 1) = 1 := by
    rw [← lintegral_gaussianReal_sq]
    exact (measurePreserving_eval (fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1) i).lintegral_comp
      (show Measurable (fun x : ℝ => ENNReal.ofReal (x^2)) by fun_prop)
  simp_rw [hi]
  simp

lemma gaussian_norm_ball_mass (hd : 0 < Module.finrank ℝ E) :
    (2 : ℝ≥0∞)⁻¹ ≤ stdGaussian E (Metric.closedBall 0 (Real.sqrt (2 * Module.finrank ℝ E))) := by
  let d : ℝ := Module.finrank ℝ E
  have hd' : 0 < d := by dsimp [d]; exact_mod_cast hd
  have hneg : stdGaussian E {x | ENNReal.ofReal (2*d) ≤ ENNReal.ofReal (‖x‖^2)} ≤ (2 : ℝ≥0∞)⁻¹ := by
    have h := meas_ge_le_lintegral_div (μ := stdGaussian E)
      (f := fun x => ENNReal.ofReal (‖x‖^2)) (by fun_prop)
      (ε := ENNReal.ofReal (2*d)) (by positivity) ENNReal.ofReal_ne_top
    rw [lintegral_stdGaussian_norm_sq] at h
    convert h using 1
    have hd0 : (Module.finrank ℝ E : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat, d,
      ENNReal.ofReal_natCast, div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_left_comm, ENNReal.mul_inv_cancel hd0 (by simp), mul_one]
  have hsub : (Metric.closedBall (0 : E) (Real.sqrt (2*d)))ᶜ ⊆
      {x | ENNReal.ofReal (2*d) ≤ ENNReal.ofReal (‖x‖^2)} := by
    intro x hx
    have hx' : Real.sqrt (2*d) < ‖x‖ := by simpa only [mem_compl_iff, Metric.mem_closedBall,
      dist_zero_right, not_le] using hx
    apply ENNReal.ofReal_le_ofReal
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (2*d)) (norm_nonneg x)).mpr hx'.le
    rwa [Real.sq_sqrt (by positivity)] at hsq
  have hc := (measure_mono hsub).trans hneg
  rw [measure_compl measurableSet_closedBall (measure_ne_top _ _), measure_univ] at hc
  change (2 : ℝ≥0∞)⁻¹ ≤ stdGaussian E (Metric.closedBall 0 (Real.sqrt (2*d)))
  have := tsub_le_iff_left.mp hc
  have he : (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by norm_num
  rw [← he]
  exact tsub_le_iff_right.mpr this

end

lemma map_withDensity_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X ≃ᵐ Y) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_map (show Measurable (s.indicator (fun y => f (e.symm y))) from
      (hf.comp e.symm.measurable).indicator hs) e.measurable]
  have he (x : X) : s.indicator (fun y => f (e.symm y)) (e x) =
      (e ⁻¹' s).indicator f x := by
    by_cases hx : e x ∈ s <;> simp [hx]
  simp_rw [he]
  exact (lintegral_indicator (hs.preimage e.measurable) f).symm

lemma density_moment_equiv {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (e : X ≃ᵐ X) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (he : μ.map e = c • μ) {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : (μ.withDensity f).map e = μ.withDensity g) (n : ℕ) :
    ∫⁻ y, g y ^ (n+1) ∂μ = c^n * ∫⁻ x, f x ^ (n+1) ∂μ := by
  have hd : g =ᵐ[μ] (fun y => c * f (e.symm y)) := by
    apply (withDensity_eq_iff_of_sigmaFinite hg.aemeasurable (by fun_prop)).mp
    rw [← hfg, map_withDensity_equiv μ e f hf, he, withDensity_smul_measure]
    exact (withDensity_smul c (hf.comp e.symm.measurable)).symm
  have hd' : (fun y => g y ^ (n+1)) =ᵐ[μ]
      (fun y => (c * f (e.symm y)) ^ (n+1)) := by
    filter_upwards [hd] with y hy
    rw [hy]
  rw [lintegral_congr_ae hd']
  simp_rw [mul_pow]
  rw [lintegral_const_mul _ (by fun_prop)]
  have hchange : c * (∫⁻ y, f (e.symm y) ^ (n+1) ∂μ) = ∫⁻ x, f x ^ (n+1) ∂μ := by
    calc
      _ = ∫⁻ y, f (e.symm y) ^ (n+1) ∂(c • μ) := by
        simp only [lintegral_smul_measure, smul_eq_mul]
      _ = _ := by
        rw [← he, lintegral_map_equiv]
        simp
  have hchange' : (∫⁻ y, f (e.symm y) ^ (n+1) ∂μ) =
      c⁻¹ * ∫⁻ x, f x ^ (n+1) ∂μ := by
    rw [← hchange, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  rw [hchange', pow_succ, mul_assoc, ← mul_assoc c, ENNReal.mul_inv_cancel hc0 hct,
    one_mul]

end ProjectionMoments

end

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments
attribute [fun_prop] measurable_lowerDensity

section Rotations
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

instance rotationLaw_probability : IsProbabilityMeasure (rotationLaw E) := by
  constructor
  simp only [rotationLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel ((ne_of_gt (isOpen_univ.measure_pos (Measure.haar : Measure (Rotation E)) Set.univ_nonempty))) (measure_ne_top _ _)

instance rotationLaw_haar : (rotationLaw E).IsHaarMeasure := by
  unfold rotationLaw
  apply Measure.IsHaarMeasure.smul _
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · exact ENNReal.inv_ne_top.mpr (ne_of_gt (isOpen_univ.measure_pos (Measure.haar : Measure (Rotation E)) Set.univ_nonempty))

instance rotationLaw_right : (rotationLaw E).IsMulRightInvariant := by
  constructor
  intro Q
  let μ := (rotationLaw E).map (fun O => O * Q)
  have hprob : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by
    first | fun_prop | exact (measurable_mul_const Q).aemeasurable | exact (continuous_mul_right Q).measurable.aemeasurable)
  have he := Measure.isMulInvariant_eq_smul_of_compactSpace μ (rotationLaw E)
  have hc := congrArg (fun ν : Measure (Rotation E) => ν Set.univ) he
  simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at hc
  have hc' : Measure.haarScalarFactor μ (rotationLaw E) = 1 :=
    ENNReal.coe_injective hc.symm
  simpa [hc'] using he

variable {E}

lemma rotation_transitive {ι : Type*} [Fintype ι] {u v : ι → E}
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    ∃ O : Rotation E, ∀ i, (O : E →L[ℝ] E) (u i) = v i := by
  classical
  let U := Submodule.span ℝ (Set.range u)
  let V := Submodule.span ℝ (Set.range v)
  let bu : OrthonormalBasis ι ℝ U := (Module.Basis.span hu.linearIndependent).toOrthonormalBasis
    (by convert! orthonormal_span hu using 1; ext i; simp)
  let bv : OrthonormalBasis ι ℝ V := (Module.Basis.span hv.linearIndependent).toOrthonormalBasis
    (by convert! orthonormal_span hv using 1; ext i; simp)
  let e : U ≃ₗᵢ[ℝ] V := bu.repr.trans bv.repr.symm
  let L : U →ₗᵢ[ℝ] E := V.subtypeₗᵢ.comp e.toLinearIsometry
  let O : E ≃ₗᵢ[ℝ] E := L.extend.toLinearIsometryEquiv rfl
  refine ⟨Unitary.linearIsometryEquiv.symm O, ?_⟩
  intro i
  change O (u i) = v i
  change L.extend (u i) = v i
  have he : e (bu i) = bv i := by
    simp only [e, LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self,
      OrthonormalBasis.repr_symm_single]
  have hbui : (bu i : E) = u i := by simp [bu, Module.Basis.span_apply]
  have hbvi : (bv i : E) = v i := by simp [bv, Module.Basis.span_apply]
  rw [← hbui, LinearIsometry.extend_apply]
  change (e (bu i) : E) = _
  rw [he, hbvi]

variable [MeasurableSpace E] [BorelSpace E]

lemma measurable_rotateRows {ι : Type*} [Fintype ι] :
    Measurable (fun z : Rotation E × (ι → E) => rotateRows z.1 z.2) := by
  apply Continuous.measurable
  apply continuous_pi
  intro i
  exact (continuous_subtype_val.comp continuous_fst).clm_apply (continuous_apply i |>.comp continuous_snd)

@[fun_prop] lemma measurable_rotateRows_left {ι : Type*} [Fintype ι] (v : ι → E) :
    Measurable (fun O : Rotation E => rotateRows O v) :=
  measurable_rotateRows.comp (measurable_id.prodMk measurable_const)

@[fun_prop] lemma measurable_rotateRows_right {ι : Type*} [Fintype ι] (O : Rotation E) :
    Measurable (fun v : ι → E => rotateRows O v) :=
  measurable_rotateRows.comp (measurable_const.prodMk measurable_id)

omit [MeasurableSpace E] [BorelSpace E] in
lemma rotateRows_mul [MeasurableSpace E] [BorelSpace E] {ι : Type*} (O Q : Rotation E) (v : ι → E) :
    rotateRows (O*Q) v = rotateRows O (rotateRows Q v) := rfl

lemma rotationLaw_orbit_eq {ι : Type*} [Fintype ι] {u v : ι → E}
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    (rotationLaw E).map (fun O => rotateRows O u) =
      (rotationLaw E).map (fun O => rotateRows O v) := by
  obtain ⟨Q, hQ⟩ := rotation_transitive hu hv
  have he : rotateRows Q u = v := funext hQ
  have hm : Measurable (fun O : Rotation E => rotateRows O u) :=
    measurable_rotateRows.comp (measurable_id.prodMk measurable_const)
  rw [← he]
  conv_lhs => rw [← (measurePreserving_mul_right (rotationLaw E) Q).map_eq]
  rw [Measure.map_map hm (by fun_prop)]
  rfl

lemma gaussianRows_rotation_invariant (m : ℕ) (O : Rotation E) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map (rotateRows O) =
      Measure.pi (fun _ : Fin m => stdGaussian E) := by
  change (Measure.pi (fun _ : Fin m => stdGaussian E)).map
    (fun v i => O.val (v i)) = _
  rw [Measure.pi_map_pi (f := fun _ : Fin m => (O.val : E →L[ℝ] E))
    (fun _ => O.val.continuous.measurable.aemeasurable)]
  congr 1
  funext j
  exact stdGaussian_map (Unitary.linearIsometryEquiv O)

end Rotations

section Triangular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma coordinateMap_apply [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} (A : Fin m → E) (x : E) (i : Fin m) :
    coordinateMap A x i = ⟪x, A i⟫ := by
  change WithLp.ofLp (rowMap A x) i = _
  rw [rowMap_apply]

def rowJacobian {m : ℕ} (A : Fin m → E) : ℝ :=
  ∏ i, ‖gramSchmidt ℝ A i‖

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowJacobian_pos [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} {A : Fin m → E} (hA : LinearIndependent ℝ A) :
    0 < rowJacobian A := Finset.prod_pos (fun i _ => norm_pos_iff.mpr (gramSchmidt_ne_zero i hA))

lemma rows_factor {m : ℕ} (A : Fin m → E) (hA : LinearIndependent ℝ A) :
    ∃ u : Fin m → E, Orthonormal ℝ u ∧
      ∃ T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ),
        (∀ x, coordinateMap A x = T (coordinateMap u x)) ∧
        (volume : Measure (Fin m → ℝ)).map T =
          (ENNReal.ofReal (rowJacobian A))⁻¹ • volume := by
  let u := gramSchmidtNormed ℝ A
  let R : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.diagonal (fun i => ‖gramSchmidt ℝ A i‖) * NoiselessRegression.gsUpper m A
  have hu : Orthonormal ℝ u := gramSchmidtNormed_orthonormal hA
  have hn (i : Fin m) : ‖gramSchmidt ℝ A i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hA)
  have hexp (j : Fin m) : ∑ i, R i j • u i = A j := by
    rw [← NoiselessRegression.gsUpper_expansion m A j]
    apply Finset.sum_congr rfl
    intro i _
    simp only [R, u, Matrix.diagonal_mul, gramSchmidtNormed, smul_smul]
    congr 1
    simp [hn i, mul_comm]
  have hdet : R.transpose.det = rowJacobian A := by
    dsimp only [R, rowJacobian]
    rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal,
      NoiselessRegression.gsUpper_det, mul_one]
  have hd : R.transpose.det ≠ 0 := by rw [hdet]; exact (rowJacobian_pos hA).ne'
  let T := (R.transpose.toLinearEquiv' (Matrix.invertibleOfIsUnitDet R.transpose (isUnit_iff_ne_zero.mpr hd))).toContinuousLinearEquiv
  refine ⟨u, hu, T, ?_, ?_⟩
  · intro x
    ext j
    rw [coordinateMap_apply, ← hexp j]
    change ⟪x, ∑ i, R i j • u i⟫ = Matrix.mulVec R.transpose (coordinateMap u x) j
    simp only [inner_sum, inner_smul_right, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, coordinateMap_apply]
  · change (volume : Measure (Fin m → ℝ)).map (Matrix.toLin' R.transpose) = _
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hd,
      abs_of_pos (inv_pos.mpr (by rw [hdet]; exact rowJacobian_pos hA)), hdet,
      ENNReal.ofReal_inv_of_pos (rowJacobian_pos hA)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_rowMap_le [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} {u : Fin m → E} (hu : Orthonormal ℝ u) :
    ‖rowMap u‖ ≤ 1 := by
  apply (rowMap u).opNorm_le_bound zero_le_one
  intro x
  rw [one_mul]
  have h := hu.sum_inner_products_le (x := x) (s := Finset.univ)
  apply (sq_le_sq₀ (norm_nonneg (rowMap u x)) (norm_nonneg x)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [rowMap_apply, Real.norm_eq_abs, sq_abs,
    WithLp.ofLp_toLp, real_inner_comm] using h

omit [MeasurableSpace E] [BorelSpace E] in
lemma rowJacobian_le [MeasurableSpace E] [BorelSpace E] {m : ℕ} (A : Fin m → E) :
    rowJacobian A ≤ ∏ i, ‖A i‖ := by
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [NoiselessRegression.norm_gramSchmidt_eq_infDist]
  simpa only [dist_zero_right] using
    Metric.infDist_le_dist_of_mem (x := A i) (Submodule.zero_mem (Submodule.span ℝ (A '' Set.Iio i)))

lemma coordinateMap_rotateRows {m : ℕ} (O : Rotation E) (A : Fin m → E) (x : E) :
    coordinateMap (rotateRows O A) x =
      coordinateMap A ((Unitary.linearIsometryEquiv O).symm x) := by
  ext i
  simp only [coordinateMap_apply, rotateRows]
  calc
    _ = ⟪(Unitary.linearIsometryEquiv O) (A i), x⟫ := real_inner_comm _ _
    _ = ⟪A i, (Unitary.linearIsometryEquiv O).symm x⟫ :=
      LinearIsometryEquiv.inner_map_eq_flip _ _ _
    _ = _ := real_inner_comm _ _

end Triangular

section CoordinateDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

@[fun_prop] lemma measurable_coordinateDensity (ν : Measure E) [SFinite ν] (m : ℕ) :
    Measurable (coordinateDensity ν m) := by
  exact (measurable_lowerDensity ν m).comp (by fun_prop)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowMap_eq_toLp_coordinateMap [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} (A : Fin m → E) :
    (rowMap A : E → Label m) = (WithLp.toLp 2) ∘ coordinateMap A := rfl

lemma coordinateDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (hA : ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ))) :
    volume.withDensity (fun y => coordinateDensity ν m (A,y)) = ν.map (coordinateMap A) := by
  have hr : ν.map (rowMap A) ≪ (volume : Measure (Label m)) := by
    rw [rowMap_eq_toLp_coordinateMap, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← (PiLp.volume_preserving_toLp (Fin m)).map_eq]
    exact hA.map (by fun_prop)
  have h := congrArg (fun μ : Measure (Label m) => μ.map (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm)
    (lowerDensity_is_density ν m A hr)
  rw [map_withDensity_equiv _ _ _ (by fun_prop),
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h

def labelMoment (ν : Measure E) (m n : ℕ) (A : Fin m → E) : ℝ≥0∞ :=
  ∫⁻ y, coordinateDensity ν m (A,y)^(n+1)

@[fun_prop] lemma measurable_labelMoment (ν : Measure E) [SFinite ν] (m n : ℕ) :
    Measurable (labelMoment ν m n) := by
  exact Measurable.lintegral_prod_right (by fun_prop)

lemma labelMoment_factor (ν : Measure E) [IsFiniteMeasure ν] {m n : ℕ}
    (A u : Fin m → E) (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    (hf : ∀ x, coordinateMap A x = T (coordinateMap u x))
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hT : (volume : Measure (Fin m → ℝ)).map T = c • volume)
    (hu : ν.map (coordinateMap u) ≪ (volume : Measure (Fin m → ℝ))) :
    labelMoment ν m n A = c^n * labelMoment ν m n u := by
  have he : ν.map (coordinateMap A) = (ν.map (coordinateMap u)).map T := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    exact funext hf
  have ha : ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ)) := by
    rw [he]
    have h := hu.map T.continuous.measurable
    rw [hT] at h
    exact h.trans Measure.smul_absolutelyContinuous
  apply density_moment_equiv volume T.toHomeomorph.toMeasurableEquiv c hc0 hct hT
    (by fun_prop) (by fun_prop)
  rw [coordinateDensity_is_density ν m A ha, coordinateDensity_is_density ν m u hu, he]
  rfl

end CoordinateDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance frameLaw_probability {m : ℕ} (u : Fin m → E) : IsProbabilityMeasure (frameLaw u) :=
  (Measure.isProbabilityMeasure_map (measurable_rotateRows_left u).aemeasurable :
    IsProbabilityMeasure ((rotationLaw E).map (fun O => rotateRows O u)))

lemma frameLaw_eq {m : ℕ} {u v : Fin m → E} (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    frameLaw u = frameLaw v := rotationLaw_orbit_eq hu hv

def orbitMoment (ν : Measure E) (m n : ℕ) (A : Fin m → E) : ℝ≥0∞ :=
  ∫⁻ O, labelMoment ν m n (rotateRows O A) ∂rotationLaw E

@[fun_prop] lemma measurable_orbitMoment (ν : Measure E) [SFinite ν] (m n : ℕ) :
    Measurable (orbitMoment ν m n) := by
  apply Measurable.lintegral_prod_right
  exact (measurable_labelMoment ν m n).comp (measurable_rotateRows.comp measurable_swap)

lemma orbitMoment_eq_frame (ν : Measure E) [SFinite ν] (m n : ℕ) (u : Fin m → E) :
    orbitMoment ν m n u = ∫⁻ A, labelMoment ν m n A ∂frameLaw u := by
  rw [frameLaw, lintegral_map (measurable_labelMoment ν m n) (measurable_rotateRows_left u)]
  rfl

lemma orbitMoment_factor (ν : Measure E) [IsFiniteMeasure ν] {m n : ℕ}
    (u : Fin m → E) (hu : Orthonormal ℝ u)
    (hac : ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ)))
    (A : Fin m → E) (hA : LinearIndependent ℝ A) :
    orbitMoment ν m n A = (ENNReal.ofReal (rowJacobian A))⁻¹ ^ n * orbitMoment ν m n u := by
  obtain ⟨v, hv, T, hT, hvol⟩ := rows_factor A hA
  have hacv : ∀ᵐ O ∂rotationLaw E,
      ν.map (coordinateMap (rotateRows O v)) ≪ (volume : Measure (Fin m → ℝ)) := by
    apply ae_of_ae_map (p := fun B : Fin m → E => ν.map (coordinateMap B) ≪ (volume : Measure (Fin m → ℝ)))
      (measurable_rotateRows_left v).aemeasurable
    change ∀ᵐ B ∂frameLaw v, _
    rwa [← frameLaw_eq hu hv]
  have hi : orbitMoment ν m n A =
      (ENNReal.ofReal (rowJacobian A))⁻¹ ^ n * orbitMoment ν m n v := by
    unfold orbitMoment
    rw [← lintegral_const_mul _ (by fun_prop)]
    apply lintegral_congr_ae
    filter_upwards [hacv] with O hO
    apply labelMoment_factor ν (rotateRows O A) (rotateRows O v) T
      (fun x => ?_) ((ENNReal.ofReal (rowJacobian A))⁻¹) (by simp)
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (rowJacobian_pos hA))) hvol hO
    rw [coordinateMap_rotateRows, coordinateMap_rotateRows, hT]
  rw [hi, orbitMoment_eq_frame, ← frameLaw_eq hu hv, ← orbitMoment_eq_frame]

lemma gaussian_lintegral_orbitMoment (ν : Measure E) [SFinite ν] (m n : ℕ) :
    ∫⁻ A, orbitMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) =
      ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) := by
  unfold orbitMoment
  rw [lintegral_lintegral_swap (by
    exact ((measurable_labelMoment ν m n).comp (measurable_rotateRows.comp measurable_swap)).aemeasurable)]
  have hi (O : Rotation E) :
      ∫⁻ A, labelMoment ν m n (rotateRows O A) ∂Measure.pi (fun _ => stdGaussian E) =
        ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) := by
    rw [← lintegral_map (measurable_labelMoment ν m n) (measurable_rotateRows_right O),
      gaussianRows_rotation_invariant]
  simp_rw [hi]
  simp

lemma gaussian_labelMoment_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) ≤
      ν Set.univ * (NoiselessRegression.replicaConstant ν a m)^n := by
  have he (A : Fin m → E) : labelMoment ν m n A =
      ∫⁻ y : Label m, lowerDensity ν m (A,y)^(n+1) :=
    (PiLp.volume_preserving_toLp (Fin m)).lintegral_comp
      (show Measurable (fun y : Label m => lowerDensity ν m (A,y)^(n+1)) by fun_prop)
  simp_rw [he]
  rw [← lintegral_prod _ (show AEMeasurable (fun z : (Fin m → E) × Label m => lowerDensity ν m z^(n+1)) _ by fun_prop)]
  exact lowerDensity_integrated_moment hν hsupport m n hmargin

theorem frame_gaussian_comparison (ν : Measure E) [IsFiniteMeasure ν]
    {m n : ℕ} (hm : m ≤ Module.finrank ℝ E) (hd : 0 < Module.finrank ℝ E)
    (u : Fin m → E) (hu : Orthonormal ℝ u)
    (hac : ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ))) :
    orbitMoment ν m n u ≤
      (2 : ℝ≥0∞)^m * ENNReal.ofReal (Real.sqrt (2 * Module.finrank ℝ E))^(m*n) *
        ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) := by
  let γ : Measure (Fin m → E) := Measure.pi (fun _ => stdGaussian E)
  let t : ℝ := Real.sqrt (2 * Module.finrank ℝ E)
  let G : Set (Fin m → E) := Set.univ.pi (fun _ => Metric.closedBall (0 : E) t)
  have ht : 0 < t := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < 2 * Module.finrank ℝ E by omega))
  have hG : MeasurableSet G := MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)
  have hGmass : (2 : ℝ≥0∞)⁻¹^m ≤ γ G := by
    rw [show γ G = ∏ _ : Fin m, stdGaussian E (Metric.closedBall 0 t) from Measure.pi_pi _ _]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod' (s := Finset.univ) (fun (_ : Fin m) _ => gaussian_norm_ball_mass (E := E) hd)
  let B : ℝ≥0∞ := ENNReal.ofReal t ^ m
  have hB0 : B ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr ht)
  have hBt : B ≠ ∞ := by simp [B]
  have hJ (A : Fin m → E) (hA : A ∈ G) : ENNReal.ofReal (rowJacobian A) ≤ B := by
    have hnorm (i : Fin m) : ‖A i‖ ≤ t := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hA i (Set.mem_univ i)
    have h := (rowJacobian_le A).trans (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hnorm i))
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    simpa only [B, ENNReal.ofReal_pow ht.le] using ENNReal.ofReal_le_ofReal h
  have hlow : B⁻¹^n * orbitMoment ν m n u * γ G ≤
      ∫⁻ A, orbitMoment ν m n A ∂γ := by
    calc
      _ = ∫⁻ A in G, B⁻¹^n * orbitMoment ν m n u ∂γ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ A in G, orbitMoment ν m n A ∂γ := by
        apply setLIntegral_mono_ae' hG
        filter_upwards [gaussian_rows_ae_linearIndependent m hm] with A hA
        intro hAG
        rw [orbitMoment_factor ν u hu hac A hA]
        exact mul_le_mul' (pow_le_pow_left' (ENNReal.inv_le_inv.mpr (hJ A hAG)) n) le_rfl
      _ ≤ ∫⁻ A, orbitMoment ν m n A ∂γ := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
  have hlow' : ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n) * orbitMoment ν m n u ≤
      ∫⁻ A, labelMoment ν m n A ∂γ := by
    rw [← gaussian_lintegral_orbitMoment ν m n]
    exact (show ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n) * orbitMoment ν m n u ≤
        B⁻¹^n * orbitMoment ν m n u * γ G from by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul' hGmass (le_rfl : B⁻¹^n * orbitMoment ν m n u ≤ B⁻¹^n * orbitMoment ν m n u)).trans hlow
  have hc0 : (2 : ℝ≥0∞)⁻¹^m * B⁻¹^n ≠ 0 := by simp [hBt]
  have hct : (2 : ℝ≥0∞)⁻¹^m * B⁻¹^n ≠ ∞ :=
    ENNReal.mul_ne_top (by finiteness) (by finiteness)
  have h := mul_le_mul' (le_rfl : ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n)⁻¹ ≤ ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n)⁻¹) hlow'
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul] at h
  have he : ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n)⁻¹ = (2 : ℝ≥0∞)^m * ENNReal.ofReal t^(m*n) := by
    rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by finiteness)),
      ← ENNReal.inv_pow, ← ENNReal.inv_pow, inv_inv, inv_inv]
    simp only [B, ← pow_mul]
  rw [he] at h
  exact h

end ProjectionMoments
end

end OAI
end
end

section
section
namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[fun_prop] lemma measurable_coordinateMap (m : ℕ) :
    Measurable (fun z : (Fin m → E) × E => coordinateMap z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  simp only [coordinateMap_apply]
  fun_prop

def projectionKernel (ν : Measure E) [SFinite ν] (m : ℕ) : Kernel (Fin m → E) (Fin m → ℝ) where
  toFun A := ν.map (coordinateMap A)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have he (A : Fin m → E) : (ν.map (coordinateMap A)) s =
        ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) (coordinateMap A x) ∂ν := by
      rw [← lintegral_map (measurable_const.indicator hs) (by fun_prop)]
      simp [lintegral_indicator hs]
    simp_rw [he]
    apply Measurable.lintegral_prod_right
    exact (measurable_const.indicator hs).comp (measurable_coordinateMap m)

instance projectionKernel_finite (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ) :
    IsFiniteKernel (projectionKernel ν m) := by
  refine ⟨ν Set.univ, measure_lt_top _ _, ?_⟩
  intro A
  change (ν.map (coordinateMap A)) Set.univ ≤ _
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ]

lemma projectionKernel_compProd (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)) ⊗ₘ projectionKernel ν m =
      NoiselessRegression.projectionLaw ν m := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_compProd hf, NoiselessRegression.projectionLaw,
    lintegral_map hf (by fun_prop), lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro A
  change (∫⁻ y, f (A,y) ∂ν.map (coordinateMap A)) = _
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  apply congrArg f
  exact Prod.ext (by rfl) (funext fun i => coordinateMap_apply A x i)

lemma ae_projection_ac (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (h : NoiselessRegression.projectionLaw ν m ≪ NoiselessRegression.matrixLabelReference (E := E) m) :
    ∀ᵐ A : Fin m → E ∂Measure.pi (fun _ => stdGaussian E),
      ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ)) := by
  let γ : Measure (Fin m → E) := Measure.pi (fun _ => stdGaussian E)
  let η : Measure (Fin m → ℝ) := volume.toFinite
  have hh : γ ⊗ₘ projectionKernel ν m ≪ γ ⊗ₘ Kernel.const (Fin m → E) η := by
    rw [projectionKernel_compProd, Measure.compProd_const]
    exact h.trans (Measure.AbsolutelyContinuous.refl γ |>.prod (absolutelyContinuous_toFinite volume))
  filter_upwards [hh.kernel_of_compProd] with A hA
  exact hA.trans (toFinite_absolutelyContinuous volume)

lemma sphere_ae_projection_ac [Nontrivial E] {m : ℕ} (hm : m+2 ≤ Module.finrank ℝ E) :
    ∀ᵐ A : Fin m → E ∂Measure.pi (fun _ => stdGaussian E),
      NoiselessRegression.ambientSphereLaw.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ)) := by
  apply ae_projection_ac
  apply NoiselessRegression.projectionLaw_absolutelyContinuous (a := m+1) (n := 1)
    (C := ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E))
  · intro z r hr
    exact NoiselessRegression.ambientSphereLaw_closedBall z hr (m+1) (by omega)
  · positivity
  · exact ENNReal.ofReal_ne_top
  · exact NoiselessRegression.ambientSphereLaw_support.trans Metric.sphere_subset_closedBall
  · omega
  · omega

lemma linearEquiv_preserves_ac {m : ℕ} (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    {μ : Measure (Fin m → ℝ)} (hμ : μ ≪ volume) : μ.map T ≪ volume := by
  exact (T.toHomeomorph.toMeasurableEquiv.measurableEmbedding.absolutelyContinuous_map hμ).trans
    (Measure.LinearMap.quasiMeasurePreserving volume T.toLinearEquiv.toLinearMap
      (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero).absolutelyContinuous

lemma sphere_projection_rotation [Nontrivial E] {m : ℕ} (O : Rotation E) (A : Fin m → E) :
    NoiselessRegression.ambientSphereLaw.map (coordinateMap (rotateRows O A)) =
      NoiselessRegression.ambientSphereLaw.map (coordinateMap A) := by
  have hfun : (coordinateMap (rotateRows O A) : E → (Fin m → ℝ)) =
      coordinateMap A ∘ (Unitary.linearIsometryEquiv O).symm :=
    funext (coordinateMap_rotateRows O A)
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    (NoiselessRegression.ambientSphereLaw_isometry (Unitary.linearIsometryEquiv O).symm).map_eq]

theorem sphere_frame_ac [Nontrivial E] {m : ℕ} (hm : m+2 ≤ Module.finrank ℝ E)
    {u : Fin m → E} (hu : Orthonormal ℝ u) :
    NoiselessRegression.ambientSphereLaw.map (coordinateMap u) ≪ (volume : Measure (Fin m → ℝ)) := by
  obtain ⟨B,hB,hac⟩ := ((gaussian_rows_ae_linearIndependent m (by omega)).and
    (sphere_ae_projection_ac hm)).exists
  obtain ⟨v,hv,T,hT,hvol⟩ := rows_factor B hB
  have he : (NoiselessRegression.ambientSphereLaw.map (coordinateMap B)).map T.symm =
      NoiselessRegression.ambientSphereLaw.map (coordinateMap v) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp only [Function.comp_apply, hT, T.symm_apply_apply]
  have hvac := linearEquiv_preserves_ac T.symm hac
  rw [he] at hvac
  obtain ⟨O,hO⟩ := rotation_transitive hv hu
  have heu : rotateRows O v = u := funext hO
  rw [← heu, sphere_projection_rotation]
  exact hvac

theorem sphere_fullRank_ac [Nontrivial E] {m : ℕ} (hm : m+2 ≤ Module.finrank ℝ E)
    {A : Fin m → E} (hA : LinearIndependent ℝ A) :
    NoiselessRegression.ambientSphereLaw.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ)) := by
  obtain ⟨u,hu,T,hT,hvol⟩ := rows_factor A hA
  have he : NoiselessRegression.ambientSphereLaw.map (coordinateMap A) =
      (NoiselessRegression.ambientSphereLaw.map (coordinateMap u)).map T := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    exact funext hT
  rw [he]
  exact linearEquiv_preserves_ac T (sphere_frame_ac hm hu)

end ProjectionMoments
end

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
attribute [fun_prop] measurable_ballAverage
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma replicaConstant_real_le [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : Measure E} (hν : ν Set.univ ≤ 1) {a : ℝ} {m : ℕ}
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) :
    NoiselessRegression.replicaConstant ν a m ≤ (128 : ℝ≥0∞)^Module.finrank ℝ E := by
  apply le_trans _ (NoiselessRegression.replicaConstant_le hν hd le_rfl hm)
  have hr : (4 : ℝ)^a ≤ (4 : ℝ)^(Module.finrank ℝ E : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
  have hc : ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * 4^a) ≤
      ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * 4^(Module.finrank ℝ E : ℝ)) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hr (by positivity))
  exact add_le_add le_rfl (mul_le_mul' hc le_rfl)

theorem frame_moment_unit {ν : Measure E} [IsFiniteMeasure ν] {a : ℝ}
    (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hs : ν.support ⊆ Metric.closedBall 0 1) (hmass : ν Set.univ ≤ 1)
    {m n : ℕ} (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hmargin : (n : ℝ)+m ≤ a)
    (u : Fin m → E) (hu : Orthonormal ℝ u)
    (hac : ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ))) :
    ∫⁻ A, labelMoment ν m n A ∂frameLaw u ≤
      (2 : ℝ≥0∞)^m * ENNReal.ofReal (Real.sqrt (2 * Module.finrank ℝ E))^(m*n) *
        (128 : ℝ≥0∞)^(Module.finrank ℝ E*n) := by
  rw [← orbitMoment_eq_frame]
  apply (frame_gaussian_comparison ν hm hd u hu hac).trans
  apply mul_le_mul' le_rfl
  apply (gaussian_labelMoment_bound hν hs m n hmargin).trans
  simpa only [one_mul, pow_mul] using
    mul_le_mul' hmass (pow_le_pow_left' (replicaConstant_real_le hmass hd ha hm) n)

lemma lintegral_inv_smul_label {m : ℕ} (f : Label m → ℝ≥0∞)
    (hf : Measurable f) {R : ℝ} (hR : 0 < R) :
    ∫⁻ y, f (R⁻¹ • y) = ENNReal.ofReal (R^m) * ∫⁻ y, f y := by
  rw [← lintegral_map hf (by fun_prop), Measure.map_addHaar_smul volume (inv_ne_zero hR.ne'),
    finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hR.le m),
    lintegral_smul_measure, smul_eq_mul]

lemma ballAverage_label_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hK : 0 < K) (z : E) {R η : ℝ} (hR : 0 < R) (hη : 0 < η)
    (m n : ℕ) (A : Fin m → E) :
    (∫⁻ y : Label m, ballAverage ν m η (A,y)^(n+1)) =
      (ENNReal.ofReal (K*R^(a-m)))^(n+1) * ENNReal.ofReal (R^m) *
        ∫⁻ y : Label m, ballAverage (normalizedRescale ν K a z R) m (η/R) (A,y)^(n+1) := by
  let μ := normalizedRescale ν K a z R
  have : IsFiniteMeasure μ := normalizedRescale_finite ν K a z R (by positivity)
  rw [← lintegral_add_left_eq_self (fun y : Label m => ballAverage ν m η (A,y)^(n+1)) (rowMap A z)]
  simp_rw [ballAverage_normalizedRescale K a hK z hR hη, mul_pow]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_inv_smul_label (fun y : Label m => ballAverage (normalizedRescale ν K a z R) m (η/R) (A,y)^(n+1)) (by fun_prop) hR,
    mul_assoc]

theorem ballAverage_integrated_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 < K)
    (z : E) {R η : ℝ} (hR : 0 < R) (hη : 0 < η)
    (hs : ν.support ⊆ Metric.closedBall z R)
    (m n : ℕ) (hmargin : (n : ℝ)+m ≤ a)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) :
    ∫⁻ x : (Fin m → E) × Label m, ballAverage ν m η x^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
      ENNReal.ofReal (K*R^(a-m))^(n+1) * ENNReal.ofReal (R^m) *
        (128 : ℝ≥0∞)^(Module.finrank ℝ E*n) := by
  let μ := normalizedRescale ν K a z R
  have : IsFiniteMeasure μ := normalizedRescale_finite ν K a z R (by positivity)
  rw [lintegral_prod _ (by fun_prop)]
  simp_rw [ballAverage_label_scaled (ν := ν) (a := a) hK z hR hη m n]
  rw [lintegral_const_mul _ (by fun_prop)]
  apply mul_le_mul' le_rfl
  rw [← lintegral_prod _ (show AEMeasurable (fun x : (Fin m → E) × Label m =>
    ballAverage μ m (η/R) x^(n+1)) _ by fun_prop)]
  apply (ballAverage_integrated_moment (normalizedRescale_local hν hK z hR)
    (normalizedRescale_support K a z hR hs) m n hmargin (div_pos hη hR)).trans
  have hmass := normalizedRescale_mass hν hK z hR hs
  simpa only [one_mul, pow_mul] using mul_le_mul' hmass
    (pow_le_pow_left' (replicaConstant_real_le hmass hd ha hm) n)

theorem lowerDensity_integrated_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) (hs : ν.support ⊆ Metric.closedBall z R)
    (m n : ℕ) (hmargin : (n : ℝ)+m ≤ a)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) :
    ∫⁻ x : (Fin m → E) × Label m, lowerDensity ν m x^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
      ENNReal.ofReal (K*R^(a-m))^(n+1) * ENNReal.ofReal (R^m) *
        (128 : ℝ≥0∞)^(Module.finrank ℝ E*n) := by
  have hp (v : ℕ → ℝ≥0∞) : (liminf v atTop)^(n+1) =
      liminf (fun j => v j^(n+1)) atTop :=
    (show Monotone (fun x : ℝ≥0∞ => x^(n+1)) from
      (fun _ _ h => pow_le_pow_left' h (n+1))).map_liminf_of_continuousAt
      v (ENNReal.continuous_pow (n+1)).continuousAt
  simp only [lowerDensity, hp]
  apply (lintegral_liminf_le (fun j => (measurable_ballAverage ν m _).pow_const _)).trans
  apply liminf_le_of_frequently_le'
  exact Filter.Frequently.of_forall (fun j => ballAverage_integrated_scaled hν hK z hR
    (inv_pos.mpr (by positivity)) hs m n hmargin hd ha hm)

theorem gaussian_labelMoment_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) (hs : ν.support ⊆ Metric.closedBall z R)
    (m n : ℕ) (hmargin : (n : ℝ)+m ≤ a)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) :
    ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal (K*R^(a-m))^(n+1) * ENNReal.ofReal (R^m) *
        (128 : ℝ≥0∞)^(Module.finrank ℝ E*n) := by
  have he (A : Fin m → E) : labelMoment ν m n A =
      ∫⁻ y : Label m, lowerDensity ν m (A,y)^(n+1) :=
    (PiLp.volume_preserving_toLp (Fin m)).lintegral_comp
      (show Measurable (fun y : Label m => lowerDensity ν m (A,y)^(n+1)) by fun_prop)
  simp_rw [he]
  rw [← lintegral_prod _ (show AEMeasurable (fun x : (Fin m → E) × Label m =>
    lowerDensity ν m x^(n+1)) _ by fun_prop)]
  exact lowerDensity_integrated_scaled hν hK z hR hs m n hmargin hd ha hm

theorem frame_moment_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) (hs : ν.support ⊆ Metric.closedBall z R)
    (m n : ℕ) (hmargin : (n : ℝ)+m ≤ a)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (u : Fin m → E) (hu : Orthonormal ℝ u)
    (hac : ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ))) :
    ∫⁻ A, labelMoment ν m n A ∂frameLaw u ≤
      (2 : ℝ≥0∞)^m * ENNReal.ofReal (Real.sqrt (2*Module.finrank ℝ E))^(m*n) *
        (ENNReal.ofReal (K*R^(a-m))^(n+1) * ENNReal.ofReal (R^m) *
          (128 : ℝ≥0∞)^(Module.finrank ℝ E*n)) := by
  rw [← orbitMoment_eq_frame]
  exact (frame_gaussian_comparison ν hm hd u hu hac).trans
    (mul_le_mul' le_rfl (gaussian_labelMoment_scaled hν hK z hR hs m n hmargin hd ha hm))

end

lemma frame_cost_power {d m n : ℕ} (hd : 1 ≤ d) (hm : m ≤ d)
    (a K R : ℝ) (hK : 0 ≤ K) (hR : 0 < R) :
    (2 : ℝ)^m * (Real.sqrt (2*d))^(m*n) *
      ((K*R^(a-m))^(n+1) * R^m * (128 : ℝ)^(d*n)) ≤
      ((256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
        R^(a-(m:ℝ)*(1-1/((n:ℝ)+1))))^(n+1) := by
  have hq : (n : ℝ)+1 ≠ 0 := by positivity
  have hexp : ((m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1) = (m*n:ℕ) := by
    push_cast
    field_simp
    ring
  have hRexp : (a-(m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1) =
      (a-m)*((n:ℝ)+1)+m := by
    field_simp
    ring
  have hscale : (K*R^(a-m))^(n+1)*R^m =
      K^(n+1)*R^((a-(m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1)) := by
    rw [mul_pow, mul_assoc, ← Real.rpow_mul_natCast hR.le,
      ← Real.rpow_natCast R m, ← Real.rpow_add hR]
    congr 2
    rw [Nat.cast_add, Nat.cast_one, hRexp]
  have h2 : (2 : ℝ)^m ≤ 256^d := by
    apply (pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ 256) m).trans
    exact pow_le_pow_right₀ (by norm_num) hm
  have h128 : (128 : ℝ)^(d*n) ≤ 256^(d*n) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) (d*n)
  have hcoef : (2 : ℝ)^m * 128^(d*n) ≤ 256^(d*(n+1)) := by
    apply (mul_le_mul h2 h128 (by positivity) (by positivity)).trans_eq
    rw [← pow_add]
    congr 1
    ring
  have hsqrt : Real.sqrt (2*d) ≤ 256*Real.sqrt d := by
    rw [Real.sqrt_mul (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
  have hS : ((256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
      R^(a-(m:ℝ)*(1-1/((n:ℝ)+1))))^(n+1) =
      256^(d*(n+1)) * (256*Real.sqrt d)^(m*n) *
        (K^(n+1)*R^((a-(m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1))) := by
    simp only [mul_pow]
    rw [← pow_mul, ← Real.rpow_mul_natCast (by positivity),
      ← Real.rpow_mul_natCast hR.le]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hexp, Real.rpow_natCast]
    ring
  rw [hS]
  calc
    _ = (2^m*128^(d*n))*(Real.sqrt (2*d))^(m*n) *
        (K^(n+1)*R^((a-(m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1))) := by
      rw [← hscale]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul hcoef (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt (m*n))
        (by positivity) (by positivity)) (by positivity)

lemma ennreal_root_bound {q : ℕ} (hq : q ≠ 0) {v : ℝ≥0∞} {B : ℝ}
    (hB : 0 ≤ B) (h : v ≤ ENNReal.ofReal B ^ q) :
    v ^ (1/(q:ℝ)) ≤ ENNReal.ofReal B := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hh := ENNReal.rpow_le_rpow h (by positivity : 0 ≤ 1/(q:ℝ))
  rwa [← ENNReal.ofReal_pow hB,
    ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hB q) (by positivity),
    ← Real.rpow_natCast_mul hB, mul_one_div_cancel hq', Real.rpow_one] at hh

lemma frame_cost_root {d m n : ℕ} (hd : 1 ≤ d) (hm : m ≤ d)
    (a K R : ℝ) (hK : 0 ≤ K) (hR : 0 < R) {v : ℝ≥0∞}
    (h : v ≤ (2 : ℝ≥0∞)^m * ENNReal.ofReal (Real.sqrt (2*d))^(m*n) *
      (ENNReal.ofReal (K*R^(a-m))^(n+1) * ENNReal.ofReal (R^m) *
        (128 : ℝ≥0∞)^(d*n))) :
    v ^ (1/((n:ℝ)+1)) ≤
      ENNReal.ofReal ((256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
        R^(a-(m:ℝ)*(1-1/((n:ℝ)+1)))) := by
  have hb := ENNReal.ofReal_le_ofReal (frame_cost_power (n := n) hd hm a K R hK hR)
  simp (discharger := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
    ENNReal.ofReal_ofNat] at hb
  simp (discharger := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow] at h
  have hB : 0 ≤ (256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
      R^(a-(m:ℝ)*(1-1/((n:ℝ)+1))) := by positivity
  have hb' : v ≤ (ENNReal.ofReal ((256 : ℝ)^d *
      (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
      R^(a-(m:ℝ)*(1-1/((n:ℝ)+1)))))^(n+1) := by
    simp (discharger := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
      ENNReal.ofReal_ofNat]
    exact h.trans hb
  have hh := ennreal_root_bound (show n+1 ≠ 0 by omega) hB hb'
  simpa only [Nat.cast_add, Nat.cast_one] using hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
lemma measure_eq_zero_of_allBall_zero [BorelSpace E] {ν : Measure E} {a : ℝ}
    (hν : AllBallMass ν 0 a) (z : E) {R : ℝ} (hR : 0 < R)
    (hs : ν.support ⊆ Metric.closedBall z R) : ν = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  have he : ν Set.univ = ν (Metric.closedBall z R) := by
    apply measure_congr
    filter_upwards [ν.support_mem_ae] with x hx
    exact propext (iff_of_true (Set.mem_univ x) (hs hx))
  rw [he]
  apply le_antisymm _ bot_le
  simpa using hν z R hR

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma lowerDensity_zero [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (m : ℕ) (x : (Fin m → E) × Label m) :
    lowerDensity (0 : Measure E) m x = 0 := by
  simp [lowerDensity, ballAverage, vectorSmoothing]

@[simp] lemma coordinateDensity_zero (m : ℕ) (x : (Fin m → E) × (Fin m → ℝ)) :
    coordinateDensity (0 : Measure E) m x = 0 := lowerDensity_zero m _

lemma coordinateDensity_frame_support (ν : Measure E) [IsFiniteMeasure ν] {m : ℕ}
    (z : E) {R : ℝ} (hR : 0 ≤ R) (hs : ν.support ⊆ Metric.closedBall z R)
    (A : Fin m → E) (hA : Orthonormal ℝ A) (y : Fin m → ℝ)
    (hy : R < ‖WithLp.toLp 2 (y-coordinateMap A z)‖) :
    coordinateDensity ν m (A,y) = 0 := by
  apply lowerDensity_eq_zero_of_far ν m A z R (WithLp.toLp 2 y) hs
  have he : WithLp.toLp 2 (y-coordinateMap A z) = WithLp.toLp 2 y - rowMap A z := rfl
  rw [he] at hy
  exact (show ‖rowMap A‖ * R ≤ R from by nlinarith [norm_rowMap_le hA]).trans_lt hy

theorem integrated_frame_moment :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d k q : ℕ) (β K R : ℝ)
      (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
      (z : EuclideanSpace ℝ (Fin d)) (u : Fin k → EuclideanSpace ℝ (Fin d)),
      1 ≤ k → 2 ≤ q → k+q ≤ d → 0 < β → β ≤ d →
      1 ≤ β-k-((q:ℝ)-2) → 0 ≤ K → 0 < R →
      ν.support ⊆ Metric.closedBall z R → AllBallMass ν K β →
      Orthonormal ℝ u →
      (∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))) →
      Measurable (coordinateDensity ν k) ∧
      (∀ᵐ A ∂frameLaw u,
        (volume : Measure (Fin k → ℝ)).withDensity (fun y => coordinateDensity ν k (A,y)) =
          ν.map (coordinateMap A)) ∧
      (∀ (A : Fin k → EuclideanSpace ℝ (Fin d)), Orthonormal ℝ A →
        ∀ y : Fin k → ℝ,
          R < ‖WithLp.toLp 2 (y-coordinateMap A z)‖ → coordinateDensity ν k (A,y) = 0) ∧
      (∫⁻ A, ∫⁻ y : Fin k → ℝ, coordinateDensity ν k (A,y)^q ∂volume ∂frameLaw u) ^ (1/(q:ℝ)) ≤
        ENNReal.ofReal (C^d * (C*Real.sqrt d)^((k:ℝ)*(1-1/(q:ℝ))) *
          K * R^(β-(k:ℝ)*(1-1/(q:ℝ)))) := by
  refine ⟨256, by norm_num, ?_⟩
  intro d k q β K R ν _ z u hk hq hdim hβ hβd hmargin hK hR hs hν hu hac
  refine ⟨measurable_coordinateDensity ν k, ?_, ?_, ?_⟩
  · filter_upwards [hac] with A hA
    exact coordinateDensity_is_density ν k A hA
  · intro A hA y hy
    exact coordinateDensity_frame_support ν z hR.le hs A hA y hy
  · rcases eq_or_lt_of_le hK with hK0 | hK0
    · have hzero : ν = 0 := measure_eq_zero_of_allBall_zero (hK0 ▸ hν) z hR hs
      subst ν
      simp only [coordinateDensity_zero, zero_pow (by omega : q ≠ 0), lintegral_zero]
      rw [ENNReal.zero_rpow_of_pos (by positivity : 0 < 1/(q:ℝ))]
      exact bot_le
    · have hn : q-1+1 = q := by omega
      have hnR : ((q-1:ℕ):ℝ)+1 = q := by exact_mod_cast hn
      have hmm : ((q-1:ℕ):ℝ)+k ≤ β := by linarith
      have h := frame_moment_scaled hν hK0 z hR hs k (q-1) hmm
        (by simpa using (show 1 ≤ d by omega)) (by simpa using hβd)
        (by simpa using (show k ≤ d by omega)) u hu hac
      have ht := frame_cost_root (d := d) (m := k) (n := q-1) (by omega) (by omega)
        β K R hK hR (by simpa only [finrank_euclideanSpace_fin] using h)
      simpa only [labelMoment, hn, hnR] using ht

end ProjectionMoments

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_fixed_offset {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 ≤ K)
    (z : E) {R : ℝ} (hR : 0 < R) (hs : ν.support ⊆ Metric.closedBall z R)
    (m q : ℕ) (hq : 1 ≤ q) (hmargin : (q:ℝ)+m ≤ a)
    (ha : a ≤ Module.finrank ℝ E) (b : Label m) :
    (∫⁻ A : Fin m → E, (lowerDensity ν m (A,rowMap A z+b))^q
      ∂Measure.pi (fun _ => stdGaussian E))^(1/(q:ℝ)) ≤
      ENNReal.ofReal ((128:ℝ)^Module.finrank ℝ E * K * R^(a-m)) := by
  have hd : 1 ≤ Module.finrank ℝ E := by
    have hq' : 1 ≤ (q:ℝ) := by exact_mod_cast hq
    have hdd : (1:ℝ) ≤ Module.finrank ℝ E := by linarith [(show (0:ℝ) ≤ m from Nat.cast_nonneg m)]
    exact_mod_cast hdd
  have hm : m ≤ Module.finrank ℝ E := by
    exact_mod_cast (show (m:ℝ) ≤ Module.finrank ℝ E by linarith [(show (0:ℝ) ≤ q from Nat.cast_nonneg q)])
  rcases eq_or_lt_of_le hK with hK | hK
  · have hz := measure_eq_zero_of_allBall_zero (hK ▸ hν) z hR hs
    subst ν
    simp only [lowerDensity_zero,zero_pow (by omega : q ≠ 0),lintegral_zero]
    rw [ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1/q)]
    exact bot_le
  · have hc : 1+ENNReal.ofReal ((3:ℝ)^Module.finrank ℝ E*(4:ℝ)^a)*(2:ℝ≥0∞)^(m+1) ≤
        (128:ℝ≥0∞)^Module.finrank ℝ E := by
      simpa only [NoiselessRegression.replicaConstant,Measure.dirac_apply_of_mem (Set.mem_univ (0:E))] using
        replicaConstant_real_le (ν := Measure.dirac (0:E)) (by simp) hd ha hm
    apply ennreal_root_bound (q := q) (by omega) (by positivity)
    have hh := lowerDensity_graph_moment_scaled hν hK z hR hs m q hmargin b
    apply hh.trans
    apply pow_le_pow_left'
    calc
      _ ≤ ENNReal.ofReal (K*R^(a-m))*(128:ℝ≥0∞)^Module.finrank ℝ E := mul_le_mul' le_rfl hc
      _ = _ := by
        rw [mul_comm]
        simp only [ENNReal.ofReal_mul (by positivity : 0 ≤ (128:ℝ)^Module.finrank ℝ E),
          ENNReal.ofReal_mul hK.le,ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 128),
          ENNReal.ofReal_ofNat,mul_assoc]

lemma ambientSphereLaw_nullSingleton [Nontrivial E] (hd : 2 ≤ Module.finrank ℝ E) :
    NullSingletonClass (NoiselessRegression.ambientSphereLaw (E := E)) := by
  constructor
  intro z
  let C : ℝ := 3*4^Module.finrank ℝ E
  have ht : Tendsto (fun r : ℝ => ENNReal.ofReal (C*r)) (𝓝 (0:ℝ)) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => ENNReal.ofReal (C*r)) := ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
    simpa only [mul_zero, ENNReal.ofReal_zero] using hc.tendsto (0:ℝ)
  apply le_antisymm _ bot_le
  apply ge_of_tendsto (ht.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ))] with r hr
  have hs : {z} ⊆ Metric.closedBall z r := Set.singleton_subset_iff.mpr (Metric.mem_closedBall_self hr.le)
  apply (measure_mono hs).trans
  have hh := NoiselessRegression.ambientSphereLaw_closedBall (E := E) z hr 1 (by omega)
  simpa only [pow_one, ENNReal.ofReal_mul (show 0 ≤ C by positivity)] using hh

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[fun_prop] lemma measurable_rieszKernel [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (α : ℝ) (z : E) : Measurable (rieszKernel α z) := by
  unfold rieszKernel
  fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rieszKernel_le_inverse_nat [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {α : ℝ} (hα : 0 ≤ α) {m : ℕ} (hm : α ≤ m)
    (z s : E) (hneq : s ≠ z) :
    rieszKernel α z s ≤ 1 + ENNReal.ofReal (‖s-z‖⁻¹^m) := by
  have hn : 0 < ‖s-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hneq)
  by_cases h1 : 1 ≤ ‖s-z‖
  · apply le_add_of_le_left
    simpa only [rieszKernel, ENNReal.rpow_zero] using ENNReal.rpow_le_rpow_of_exponent_le
      (ENNReal.one_le_ofReal.mpr h1) (show -α ≤ 0 by linarith)
  · have hh := ENNReal.rpow_le_rpow_of_exponent_ge
      (show ENNReal.ofReal ‖s-z‖ ≤ 1 by exact ENNReal.ofReal_le_one.mpr (le_of_not_ge h1))
      (show -(m:ℝ) ≤ -α by linarith)
    have he : (ENNReal.ofReal ‖s-z‖)^(-(m:ℝ)) = ENNReal.ofReal (‖s-z‖⁻¹^m) := by
      rw [ENNReal.rpow_neg,ENNReal.rpow_natCast,ENNReal.ofReal_pow (inv_nonneg.mpr hn.le),
        ENNReal.ofReal_inv_of_pos hn,ENNReal.inv_pow]
    exact hh.trans (by rw [he]; exact le_add_left le_rfl)

lemma rieszPotential_finite [Nontrivial E] {α : ℝ} (hα : 0 ≤ α) {m : ℕ}
    (hm : α ≤ m) (hmd : m+1 ≤ Module.finrank ℝ E-1)
    {h : E → ℝ≥0∞} (h1 : ∀ s, h s ≤ 1) : rieszPotential α h < ∞ := by
  have hd : 2 ≤ Module.finrank ℝ E := by omega
  let := ambientSphereLaw_nullSingleton hd
  let C : ℝ≥0∞ := ENNReal.ofReal ((3:ℝ)*4^Module.finrank ℝ E)
  have hbound (z : E) : (∫⁻ s, h s*rieszKernel α z s ∂NoiselessRegression.ambientSphereLaw) ≤
      2+C*(2:ℝ≥0∞)^(m+1) := by
    have hmom := NoiselessRegression.inverse_moment_of_tube_bound
      (NoiselessRegression.ambientSphereLaw (E := E)) (fun s => ‖s-z‖) m
      (by fun_prop) (fun _ => norm_nonneg _) C
      (fun r hr _ => by
        simpa only [Metric.closedBall, dist_eq_norm, C] using NoiselessRegression.ambientSphereLaw_closedBall z hr (m+1) hmd)
    have hcmp : ∀ᵐ s ∂NoiselessRegression.ambientSphereLaw,
        h s*rieszKernel α z s ≤ 1+ENNReal.ofReal (‖s-z‖⁻¹^m) := by
      filter_upwards [(NoiselessRegression.ambientSphereLaw (E := E)).ae_ne z] with s hs
      exact (mul_le_of_le_one_left' (h1 s)).trans (rieszKernel_le_inverse_nat hα hm z s hs)
    calc
      _ ≤ ∫⁻ s, 1+ENNReal.ofReal (‖s-z‖⁻¹^m) ∂NoiselessRegression.ambientSphereLaw := lintegral_mono_ae hcmp
      _ = 1+∫⁻ s, ENNReal.ofReal (‖s-z‖⁻¹^m) ∂NoiselessRegression.ambientSphereLaw := by
        rw [lintegral_add_left measurable_const]; simp
      _ ≤ 1+(1+C*2^(m+1)) := add_le_add le_rfl (by simpa only [measure_univ] using hmom)
      _ = _ := by ring
  exact (iSup_le hbound).trans_lt (by
    apply ENNReal.add_lt_top.mpr
    constructor
    · norm_num
    · exact ENNReal.mul_lt_top (show C < ∞ from ENNReal.ofReal_lt_top) (by finiteness))

lemma rieszPotential_ball_control [Nontrivial E] {α : ℝ} (hα : 0 ≤ α)
    {h : E → ℝ≥0∞} (hh : Measurable h) (z : E) {r : ℝ} (hr : 0 < r) :
    (NoiselessRegression.ambientSphereLaw.withDensity h) (Metric.closedBall z r) ≤
      rieszPotential α h * ENNReal.ofReal (r^α) := by
  have hr0 : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hr)
  have hrt : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hnorm (s : E) (hs : s ∈ Metric.closedBall z r) :
      1 ≤ ENNReal.ofReal (r^α) * rieszKernel α z s := by
    have hs' : ‖s-z‖ ≤ r := by simpa [dist_eq_norm] using hs
    have hb := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hs') hα
    rw [rieszKernel, ENNReal.rpow_neg, ← ENNReal.ofReal_rpow_of_pos hr]
    calc
      _ = (ENNReal.ofReal r)^α*((ENNReal.ofReal r)^α)⁻¹ :=
        (ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hr0) hrt)) (ENNReal.rpow_ne_top_of_nonneg hα hrt)).symm
      _ ≤ _ := mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr hb)
  rw [withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
  calc
    _ ≤ ∫⁻ s in Metric.closedBall z r, ENNReal.ofReal (r^α)*(h s*rieszKernel α z s)
        ∂NoiselessRegression.ambientSphereLaw := by
      apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
      intro s hs
      simpa only [mul_one,mul_left_comm] using mul_le_mul' le_rfl (hnorm s hs)
    _ ≤ ∫⁻ s, ENNReal.ofReal (r^α)*(h s*rieszKernel α z s)
        ∂NoiselessRegression.ambientSphereLaw := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (r^α)*(∫⁻ s, h s*rieszKernel α z s ∂NoiselessRegression.ambientSphereLaw) :=
      lintegral_const_mul _ (hh.mul (measurable_rieszKernel α z))
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul' (show _ ≤ rieszPotential α h from le_iSup (fun z => ∫⁻ s, h s*rieszKernel α z s ∂NoiselessRegression.ambientSphereLaw) z) le_rfl

end ProjectionMoments

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance realMatrixMeasurableSpace (k : ℕ) : MeasurableSpace (Matrix (Fin k) (Fin k) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin k → Fin k → ℝ))
instance realMatrixBorelSpace (k : ℕ) : BorelSpace (Matrix (Fin k) (Fin k) ℝ) :=
  inferInstanceAs (BorelSpace (Fin k → Fin k → ℝ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mixRows_mul [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (M N : Matrix (Fin k) (Fin k) ℝ) (X : Fin k → E) :
    mixRows (M*N) X = mixRows M (mixRows N X) := by
  ext i
  simp only [mixRows, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma mixRows_one [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) : mixRows 1 X = X := by
  ext i
  simp [mixRows, Matrix.one_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gram_mixRows [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (X : Fin k → E) :
    Matrix.gram ℝ (mixRows M X) = M * Matrix.gram ℝ X * M.transpose := by
  ext i j
  simp only [Matrix.gram_apply, mixRows, inner_sum, sum_inner, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_polarRadial [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} : Continuous (polarRadial (E := E) (k := k)) := by
  apply CFC.continuousOn_sqrt.comp_continuous
  · exact continuous_matrix (fun i j => by simp only [Matrix.gram_apply]; fun_prop)
  · intro X
    exact (Matrix.posSemidef_gram ℝ X).nonneg

lemma measurable_matrix_inverse {k : ℕ} :
    Measurable (fun M : Matrix (Fin k) (Fin k) ℝ => M⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  fun_prop

lemma measurable_rawPolarRows {k : ℕ} : Measurable (rawPolarRows (E := E) (k := k)) := by
  have hH := measurable_matrix_inverse.comp (continuous_polarRadial (E := E) (k := k)).measurable
  apply Measurable.of_eval
  intro i
  change Measurable (fun X : Fin k → E => ∑ j, (polarRadial X)⁻¹ i j • X j)
  apply Finset.measurable_sum
  intro j hj
  have hh : Measurable (fun X : Fin k → E => (polarRadial X)⁻¹ i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hH)
  exact hh.smul (measurable_pi_apply j)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma polarRadial_squared [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) :
    polarRadial X * polarRadial X = Matrix.gram ℝ X :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_gram ℝ X).nonneg

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma polarRadial_pos [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) : 0 ≤ polarRadial X := CFC.sqrt_nonneg _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma polarRadial_isUnit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X) :
    IsUnit (polarRadial X) :=
  (CFC.isUnit_sqrt_iff _ (Matrix.posSemidef_gram ℝ X).nonneg).mpr
    (Matrix.posDef_gram_iff_linearIndependent.mpr hX).isUnit

lemma rawPolarRows_orthonormal {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X) :
    Orthonormal ℝ (rawPolarRows X) := by
  have hH := polarRadial_isUnit hX
  have hdet : IsUnit (polarRadial X).det := (Matrix.isUnit_iff_isUnit_det _).mp hH
  have hsym : (polarRadial X)⁻¹.transpose = (polarRadial X)⁻¹ := by
    have hh : (polarRadial X).IsHermitian := (polarRadial_pos X).isSelfAdjoint
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hh.inv
  have hgram : Matrix.gram ℝ (rawPolarRows X) = 1 := by
    rw [rawPolarRows, gram_mixRows, hsym, ← polarRadial_squared,
      ← mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul, Matrix.mul_nonsing_inv _ hdet]
  apply orthonormal_iff_ite.mpr
  intro i j
  simpa only [Matrix.gram_apply, Matrix.one_apply] using congrFun (congrFun hgram i) j

lemma polar_reconstruction {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X) :
    mixRows (polarRadial X) (rawPolarRows X) = X := by
  rw [rawPolarRows, ← mixRows_mul, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (polarRadial_isUnit hX)), mixRows_one]

omit [MeasurableSpace E] [BorelSpace E] in
lemma gram_rotateRows [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) (O : Rotation E) :
    Matrix.gram ℝ (rotateRows O X) = Matrix.gram ℝ X := by
  ext i j
  exact (Unitary.linearIsometryEquiv O).inner_map_map (X i) (X j)

lemma polarRadial_rotateRows {k : ℕ} (X : Fin k → E) (O : Rotation E) :
    polarRadial (rotateRows O X) = polarRadial X := by
  simp only [polarRadial, gram_rotateRows]

lemma rawPolarRows_rotateRows {k : ℕ} (X : Fin k → E) (O : Rotation E) :
    rawPolarRows (rotateRows O X) = rotateRows O (rawPolarRows X) := by
  ext i
  simp only [rawPolarRows, polarRadial_rotateRows, mixRows, rotateRows, map_sum, map_smul]

lemma measurableSet_linearIndependent {k : ℕ} :
    MeasurableSet {X : Fin k → E | LinearIndependent ℝ X} := by
  simp only [← Matrix.det_gram_ne_zero_iff_linearIndependent]
  have hg : Continuous (fun X : Fin k → E => Matrix.gram ℝ X) :=
    continuous_matrix (fun i j => by simp only [Matrix.gram_apply]; fun_prop)
  exact (isClosed_eq hg.matrix_det continuous_const).measurableSet.compl

lemma measurable_polarRows {k : ℕ} (u : Fin k → E) : Measurable (polarRows u) := by
  classical
  exact Measurable.ite measurableSet_linearIndependent measurable_rawPolarRows measurable_const

lemma polarRows_orthonormal {k : ℕ} {u : Fin k → E} (hu : Orthonormal ℝ u)
    (X : Fin k → E) : Orthonormal ℝ (polarRows u X) := by
  by_cases hX : LinearIndependent ℝ X
  · simpa only [polarRows, ite_eq_left hX] using rawPolarRows_orthonormal hX
  · simpa only [polarRows, ite_eq_right hX] using hu

lemma polarRows_rotateRows {k : ℕ} (u : Fin k → E) {X : Fin k → E}
    (hX : LinearIndependent ℝ X) (O : Rotation E) :
    polarRows u (rotateRows O X) = rotateRows O (polarRows u X) := by
  have hXO : LinearIndependent ℝ (rotateRows O X) := by
    rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, gram_rotateRows,
      Matrix.det_gram_ne_zero_iff_linearIndependent]
    exact hX
  simp only [polarRows, ite_eq_left hX, ite_eq_left hXO, rawPolarRows_rotateRows]

lemma lintegral_polarRows_eq_frame {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {u : Fin k → E} (hu : Orthonormal ℝ u) (f : (Fin k → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ X, f (polarRows u X) ∂Measure.pi (fun _ => stdGaussian E)) = ∫⁻ A, f A ∂frameLaw u := by
  let γ := Measure.pi (fun _ : Fin k => stdGaussian E)
  have hrot (O : Rotation E) : (∫⁻ X, f (polarRows u X) ∂γ) =
      ∫⁻ X, f (rotateRows O (polarRows u X)) ∂γ := by
    calc
      _ = ∫⁻ X, f (polarRows u (rotateRows O X)) ∂γ := by
        have hm : Measurable (rotateRows O : (Fin k → E) → (Fin k → E)) :=
          measurable_rotateRows.comp (measurable_const.prodMk measurable_id)
        have hh := lintegral_map (μ := γ) (hf.comp (measurable_polarRows u)) hm
        rw [show γ.map (rotateRows O) = γ from gaussianRows_rotation_invariant k O] at hh
        exact hh
      _ = _ := lintegral_congr_ae (by
        filter_upwards [gaussian_rows_ae_linearIndependent k hk] with X hX
        rw [polarRows_rotateRows u hX])
  calc
    _ = ∫⁻ O, ∫⁻ X, f (rotateRows O (polarRows u X)) ∂γ ∂rotationLaw E := by
      simp_rw [← hrot]
      simp only [lintegral_const, measure_univ, mul_one]
      rfl
    _ = ∫⁻ X, ∫⁻ O, f (rotateRows O (polarRows u X)) ∂rotationLaw E ∂γ := by
      apply lintegral_lintegral_swap
      exact (hf.comp (measurable_rotateRows.comp
        (measurable_fst.prodMk ((measurable_polarRows u).comp measurable_snd)))).aemeasurable
    _ = ∫⁻ X, ∫⁻ A, f A ∂frameLaw u ∂γ := by
      apply lintegral_congr
      intro X
      rw [frameLaw_eq hu (polarRows_orthonormal hu X), frameLaw]
      have hm : Measurable (fun O : Rotation E => rotateRows O (polarRows u X)) :=
        measurable_rotateRows.comp (measurable_id.prodMk measurable_const)
      exact (lintegral_map hf hm).symm
    _ = _ := by simp [γ]

lemma polarRows_law {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {u : Fin k → E} (hu : Orthonormal ℝ u) :
    (Measure.pi (fun _ : Fin k => stdGaussian E)).map (polarRows u) = frameLaw u := by
  apply Measure.ext
  intro s hs
  have hf : Measurable (s.indicator (1 : (Fin k → E) → ℝ≥0∞)) := measurable_const.indicator hs
  rw [← lintegral_indicator_one hs, lintegral_map hf (measurable_polarRows u),
    lintegral_polarRows_eq_frame hk hu _ hf, lintegral_indicator_one hs]

end

lemma euclidean_gaussian_integral (k : ℕ) :
    (∫⁻ x : Fin k → ℝ, ENNReal.ofReal (Real.exp (-‖WithLp.toLp 2 x‖^2)) ∂volume) =
      ENNReal.ofReal (Real.sqrt Real.pi ^ k) := by
  have hex (x : Fin k → ℝ) : Real.exp (-‖WithLp.toLp 2 x‖^2) =
      ∏ i, Real.exp (-(x i)^2) := by
    rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_neg_distrib, Real.exp_sum]
    congr 1
    funext i
    simp only [Real.norm_eq_abs, sq_abs]
  have hscalar : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x^2)) ∂volume) =
      ENNReal.ofReal (Real.sqrt Real.pi) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · simpa using congrArg ENNReal.ofReal (integral_gaussian 1)
    · simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
    · exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
  simp_rw [hex, ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  rw [volume_pi, NoiselessRegression.lintegral_fin_prod (volume : Measure ℝ) k
    (fun _ x => ENNReal.ofReal (Real.exp (-x^2))) (fun _ => by fun_prop)]
  simp only [hscalar, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow (Real.sqrt_nonneg _)]

lemma unit_ball_volume_bound (k : ℕ) (hk : 1 ≤ k) :
    (volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1) ≤
      ENNReal.ofReal ((6 / Real.sqrt k)^k) := by
  let r := Real.sqrt (k : ℝ)
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hr : 0 < r := Real.sqrt_pos.mpr hk0
  have hr2 : r^2 = k := Real.sq_sqrt hk0.le
  have hlower : ENNReal.ofReal (Real.exp (-(k:ℝ))) *
      (volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 r) ≤
      ENNReal.ofReal (Real.sqrt Real.pi ^ k) := by
    calc
      _ = ∫⁻ _x in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) r,
          ENNReal.ofReal (Real.exp (-(k:ℝ))) ∂volume := by simp
      _ ≤ ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) r,
          ENNReal.ofReal (Real.exp (-‖x‖^2)) ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hx' : ‖x‖ ≤ r := by simpa [Metric.mem_ball, dist_zero_right] using (Metric.mem_ball.mp hx).le
        nlinarith [norm_nonneg x]
      _ ≤ ∫⁻ x : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (Real.exp (-‖x‖^2)) ∂volume :=
        setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (Real.sqrt Real.pi ^ k) := by
        rw [← (PiLp.volume_preserving_toLp (Fin k)).map_eq,
          lintegral_map (by fun_prop) (by fun_prop)]
        exact euclidean_gaussian_integral k
  rw [Measure.addHaar_ball_of_pos volume 0 hr, finrank_euclideanSpace_fin] at hlower
  have h := ENNReal.toReal_le_of_le_ofReal (by positivity) hlower
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)] at h
  have hexp : Real.exp (-(k:ℝ)) * Real.exp (k:ℝ) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 ≤ ((volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1)).toReal :=
    ENNReal.toReal_nonneg
  have hnum : Real.exp (k:ℝ) * Real.sqrt Real.pi ^ k ≤ (6:ℝ)^k := by
    rw [show (k:ℝ) = (k:ℝ)*1 by ring, Real.exp_nat_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hs : Real.sqrt Real.pi < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith [Real.pi_lt_four])
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1, Real.sqrt_nonneg Real.pi]
  have hv : ((volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1)).toReal ≤
      (6/r)^k := by
    rw [div_pow, le_div_iff₀ (pow_pos hr _)]
    calc
      _ = Real.exp (k:ℝ)*(Real.exp (-(k:ℝ))*r^k*
          ((volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1)).toReal) := by
          nlinarith [congrArg (fun t : ℝ => t * (r^k *
            ((volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1)).toReal)) hexp]
      _ ≤ Real.exp (k:ℝ)*Real.sqrt Real.pi^k := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (Real.exp_pos (k:ℝ)).le
      _ ≤ _ := hnum
  exact (ENNReal.le_ofReal_iff_toReal_le measure_ball_lt_top.ne (by positivity)).mpr hv

end ProjectionMoments

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
attribute [fun_prop] measurable_polarRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma rowMap_ac_iff {ν : Measure E} {k : ℕ} (A : Fin k → E) :
    ν.map (rowMap A) ≪ (volume : Measure (Label k)) ↔
      ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by
  constructor
  · intro h
    have hh := h.map (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm.measurable
    rw [(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin k)).map_eq,
      Measure.map_map (by fun_prop) (by fun_prop)] at hh
    exact hh
  · intro h
    rw [rowMap_eq_toLp_coordinateMap, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← (PiLp.volume_preserving_toLp (Fin k)).map_eq]
    exact h.map (by fun_prop)

lemma measurableSet_projection_ac (ν : Measure E) [IsFiniteMeasure ν] (k : ℕ) :
    MeasurableSet {A : Fin k → E | ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))} := by
  have h := Kernel.measurableSet_absolutelyContinuous (projectionKernel ν k)
    (Kernel.const (Fin k → E) (volume : Measure (Fin k → ℝ)).toFinite)
  convert h using 1
  ext A
  exact ⟨fun h => h.trans (absolutelyContinuous_toFinite volume),
    fun h => h.trans (toFinite_absolutelyContinuous volume)⟩

lemma polar_ac_to_frame (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) {u : Fin k → E} (hu : Orthonormal ℝ u)
    (h : ∀ᵐ X ∂Measure.pi (fun _ : Fin k => stdGaussian E),
      ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by
  rw [← polarRows_law hk hu]
  apply (ae_map_iff (measurable_polarRows u).aemeasurable (measurableSet_projection_ac ν k)).mpr
  filter_upwards [h] with X hX
  exact (rowMap_ac_iff _).mp hX

lemma unitBallVolume_ne_zero (k : ℕ) : unitBallVolume k ≠ 0 := by
  apply ne_of_gt
  exact (Metric.measure_ball_pos volume 0 one_pos).trans_le (measure_mono Metric.ball_subset_closedBall)
lemma unitBallVolume_ne_top (k : ℕ) : unitBallVolume k ≠ ∞ :=
  (isCompact_closedBall (0 : Label k) (1:ℝ)).measure_ne_top
instance unitBallLaw_probability (k : ℕ) : IsProbabilityMeasure (unitBallLaw k) := by
  constructor
  simp only [unitBallLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (unitBallVolume_ne_zero k) (unitBallVolume_ne_top k)

lemma unitBallVolume_bound (k : ℕ) (hk : 1 ≤ k) :
    unitBallVolume k ≤ ENNReal.ofReal ((6/Real.sqrt k)^k) := by
  rw [unitBallVolume, Measure.addHaar_unitClosedBall_eq_addHaar_unitBall]
  exact unit_ball_volume_bound k hk

@[fun_prop] lemma measurable_normalizedDensity (ν : Measure E) [SFinite ν] (k : ℕ) (u : Fin k → E) :
    Measurable (normalizedDensity ν k u) := by
  exact measurable_const.mul ((measurable_lowerDensity ν k).comp
    (((measurable_polarRows u).comp measurable_fst).prodMk measurable_snd))

lemma normalizedDensity_support (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    {u : Fin k → E} (hu : Orthonormal ℝ u) (hs : ν.support ⊆ Metric.closedBall 0 1)
    (X : Fin k → E) (y : Label k) (hy : 1 < ‖y‖) : normalizedDensity ν k u (X,y) = 0 := by
  have h := lowerDensity_eq_zero_of_far ν k (polarRows u X) 0 1 y hs
    (by simpa only [map_zero, sub_zero, mul_one] using (norm_rowMap_le (polarRows_orthonormal hu X)).trans_lt hy)
  simp only [normalizedDensity, h, mul_zero]

lemma normalizedDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    {u : Fin k → E} (X : Fin k → E)
    (h : ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    ((unitBallVolume k)⁻¹ • (volume : Measure (Label k))).withDensity
      (fun y => normalizedDensity ν k u (X,y)) = ν.map (rowMap (polarRows u X)) := by
  rw [withDensity_smul_measure]
  change (unitBallVolume k)⁻¹ • volume.withDensity
    (unitBallVolume k • (fun y => lowerDensity ν k (polarRows u X,y))) = _
  rw [withDensity_smul _ (by fun_prop), smul_smul,
    ENNReal.inv_mul_cancel (unitBallVolume_ne_zero k) (unitBallVolume_ne_top k), one_smul]
  exact lowerDensity_is_density ν k _ h

lemma normalizedMoment_le (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) {u : Fin k → E} (hu : Orthonormal ℝ u) (n : ℕ) :
    (∫⁻ X, ∫⁻ y, normalizedDensity ν k u (X,y)^(n+1) ∂unitBallLaw k
      ∂Measure.pi (fun _ => stdGaussian E)) ≤
      unitBallVolume k ^ n * ∫⁻ A, labelMoment ν k n A ∂frameLaw u := by
  have hpoint (X : Fin k → E) :
      (∫⁻ y, normalizedDensity ν k u (X,y)^(n+1) ∂unitBallLaw k) ≤
        unitBallVolume k ^ n * labelMoment ν k n (polarRows u X) := by
    simp only [unitBallLaw, normalizedDensity, mul_pow, lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_const_mul _ (by fun_prop), ← mul_assoc,
      pow_succ', ← mul_assoc, ENNReal.inv_mul_cancel (unitBallVolume_ne_zero k) (unitBallVolume_ne_top k), one_mul]
    apply mul_le_mul' le_rfl
    have he : labelMoment ν k n (polarRows u X) =
        ∫⁻ y : Label k, lowerDensity ν k (polarRows u X,y)^(n+1) :=
      (PiLp.volume_preserving_toLp (Fin k)).lintegral_comp
        (show Measurable (fun y : Label k => lowerDensity ν k (polarRows u X,y)^(n+1)) by fun_prop)
    rw [he]
    exact setLIntegral_le_lintegral _ _
  apply (lintegral_mono hpoint).trans
  rw [lintegral_const_mul _ (by fun_prop), lintegral_polarRows_eq_frame hk hu _ (by fun_prop)]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphereWeightedRestriction_le [Nontrivial E] {h : E → ℝ≥0∞}
    (h1 : ∀ s, h s ≤ 1) (H : Set E) :
    sphereWeightedRestriction h H ≤ NoiselessRegression.ambientSphereLaw := by
  apply Measure.restrict_le_self.trans
  calc
    _ ≤ NoiselessRegression.ambientSphereLaw.withDensity (1 : E → ℝ≥0∞) :=
      withDensity_mono (Filter.Eventually.of_forall h1)
    _ = _ := withDensity_one

lemma sphereWeightedRestriction_finite [Nontrivial E] {h : E → ℝ≥0∞}
    (h1 : ∀ s, h s ≤ 1) (H : Set E) : IsFiniteMeasure (sphereWeightedRestriction h H) :=
  ⟨(Measure.le_iff.mp (sphereWeightedRestriction_le h1 H) Set.univ MeasurableSet.univ).trans_lt (by simp)⟩

lemma sphereWeightedRestriction_support {h : E → ℝ≥0∞} {H : Set E}
    {z : E} {ρ : ℝ} (hH : H ⊆ Metric.closedBall z ρ) :
    (sphereWeightedRestriction h H).support ⊆ Metric.closedBall z ρ :=
  Measure.support_restrict_subset.trans (fun _ hx =>
    (closure_minimal hH Metric.isClosed_closedBall) hx.1)

theorem riesz_deterministic_offsets :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/8
      let α : ℝ := (d:ℝ)/2
      ∀ h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable h → (∀ s, h s ≤ 1) →
      ∀ z : EuclideanSpace ℝ (Fin d), ∀ ρ : ℝ, 0 < ρ →
      ∀ H : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet H → H ⊆ Metric.closedBall z ρ →
      rieszPotential α h < ∞ ∧
      Measurable (lowerDensity (sphereWeightedRestriction h H) k) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), LinearIndependent ℝ A →
        volume.withDensity (fun y => lowerDensity (sphereWeightedRestriction h H) k (A,y)) =
          (sphereWeightedRestriction h H).map (rowMap A)) ∧
      (∀ b : Label k, (∫⁻ A, (lowerDensity (sphereWeightedRestriction h H) k (A,rowMap A z+b))^k
          ∂Measure.pi (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d))))^(1/(k:ℝ)) ≤
        ENNReal.ofReal (C^d) * rieszPotential α h * ENNReal.ofReal (ρ^(α-k))) ∧
      (∀ A y, ‖rowMap A‖*ρ < ‖y-rowMap A z‖ →
        lowerDensity (sphereWeightedRestriction h H) k (A,y) = 0) := by
  refine ⟨128,by norm_num,?_⟩
  intro d hd k α h hh h1 z ρ hρ H hH hHz
  let : NeZero d := ⟨by omega⟩
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkd : k+2 ≤ d := by dsimp [k]; omega
  have hαd : α ≤ d := by dsimp [α]; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hmargin : (k:ℝ)+k ≤ α := by
    have hn : 4*k ≤ d := by dsimp [k]; omega
    have hn' : 4*(k:ℝ) ≤ d := by exact_mod_cast hn
    dsimp [α]; linarith
  have hfinite : rieszPotential α h < ∞ := by
    apply rieszPotential_finite hα (m := d/2+1) _ _ h1
    · have hn : d ≤ 2*(d/2+1) := by omega
      have hn' : (d:ℝ) ≤ 2*((d/2+1:ℕ):ℝ) := by exact_mod_cast hn
      dsimp [α]; linarith
    · simp only [finrank_euclideanSpace_fin]; omega
  let μ := sphereWeightedRestriction h H
  let : IsFiniteMeasure μ := sphereWeightedRestriction_finite h1 H
  have hs : μ.support ⊆ Metric.closedBall z ρ := sphereWeightedRestriction_support hHz
  have hball : AllBallMass μ (rieszPotential α h).toReal α := by
    intro c r hr
    apply (Measure.restrict_le_self _).trans
    apply (rieszPotential_ball_control hα hh c hr).trans_eq
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfinite.ne]
  refine ⟨hfinite,measurable_lowerDensity μ k,?_,?_,?_⟩
  · intro A hA
    apply lowerDensity_is_density
    apply (rowMap_ac_iff _).mpr
    exact ((Measure.absolutelyContinuous_of_le (sphereWeightedRestriction_le h1 H)).map
      (show Measurable (coordinateMap A) by fun_prop)).trans (sphere_fullRank_ac (by simpa using hkd) hA)
  · intro b
    have hb := gaussian_fixed_offset hball ENNReal.toReal_nonneg z hρ hs k k (by omega)
      hmargin (by simpa using hαd) b
    simpa only [finrank_euclideanSpace_fin,ENNReal.ofReal_mul (by positivity : 0 ≤ (128:ℝ)^d),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (128:ℝ)^d*(rieszPotential α h).toReal),
      ENNReal.ofReal_toReal hfinite.ne] using hb
  · intro A y hy
    exact lowerDensity_eq_zero_of_far μ k A z ρ y hs hy

end

theorem all_radii_sphere_moment :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/4
      let β : ℝ := (d:ℝ)-1-k
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      Measurable f → (∀ s, f s ≤ 1) →
      ∀ K : ℝ, 0 ≤ K →
      AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity f) K β →
      ∀ z : EuclideanSpace ℝ (Fin d), ∀ R : ℝ, 0 < R →
      ∀ u : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ u →
      let μ := sphereWeightedRestriction f (Metric.closedBall z R)
      Measurable (coordinateDensity μ k) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ A →
        (volume : Measure (Fin k → ℝ)).withDensity (fun y => coordinateDensity μ k (A,y)) =
          μ.map (coordinateMap A)) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ A →
        ∀ y : Fin k → ℝ, R < ‖WithLp.toLp 2 (y-coordinateMap A z)‖ →
          coordinateDensity μ k (A,y) = 0) ∧
      (∫⁻ A, ∫⁻ y : Fin k → ℝ, coordinateDensity μ k (A,y)^k ∂volume ∂frameLaw u) ^ (1/(k:ℝ)) ≤
        ENNReal.ofReal (C^d*(C*Real.sqrt d)^((k:ℝ)*(1-1/(k:ℝ)))*
          K*R^(β-(k:ℝ)*(1-1/(k:ℝ)))) := by
  obtain ⟨C,hC,h⟩ := integrated_frame_moment
  refine ⟨C,hC,?_⟩
  intro d hd k β f hf hf1 K hK hball z R hR u hu μ
  let : NeZero d := ⟨by omega⟩
  let : IsFiniteMeasure μ := sphereWeightedRestriction_finite hf1 _
  have hk : 4 ≤ k := by dsimp [k]; omega
  have h3k : 3*k ≤ d := by dsimp [k]; omega
  have h3kR : 3*(k:ℝ) ≤ d := by exact_mod_cast h3k
  have hkR : (4:ℝ) ≤ k := by exact_mod_cast hk
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβd : β ≤ d := by dsimp [β]; linarith
  have hm : 1 ≤ β-(k:ℝ)-((k:ℝ)-2) := by dsimp [β]; linarith
  have hs : μ.support ⊆ Metric.closedBall z R := sphereWeightedRestriction_support Subset.rfl
  have hball' : AllBallMass μ K β := fun c r hr => (Measure.restrict_le_self _).trans (hball c r hr)
  have hac (A : Fin k → EuclideanSpace ℝ (Fin d)) (hA : Orthonormal ℝ A) :
      μ.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) :=
    ((Measure.absolutelyContinuous_of_le (sphereWeightedRestriction_le hf1 _)).map
      (by fun_prop)).trans (sphere_frame_ac (by simp only [finrank_euclideanSpace_fin]; omega) hA)
  have hframe := h d k k β K R μ z u (by omega) (by omega) (by omega)
    hβ (by exact_mod_cast hβd) hm hK hR hs hball' hu
      (polar_ac_to_frame μ (by simpa only [finrank_euclideanSpace_fin] using (show k ≤ d by omega)) hu
        (Filter.Eventually.of_forall (fun X => (rowMap_ac_iff _).mpr (hac _ (polarRows_orthonormal hu X)))))
  refine ⟨hframe.1,?_,hframe.2.2.1,hframe.2.2.2⟩
  intro A hA
  exact coordinateDensity_is_density μ k A (hac A hA)

lemma normalized_cost (d k n : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (hdk : d ≤ 32*k)
    (D : ℝ) (hD : 0 < D) :
    unitBallVolume k ^ n *
      ((2 : ℝ≥0∞)^k * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) *
        (ENNReal.ofReal (D^d)^(n+1) * (128 : ℝ≥0∞)^(d*n))) ≤
      ENNReal.ofReal ((16384 * max D 1)^(d*(n+1))) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hdR : (d:ℝ) ≤ 32*k := by exact_mod_cast hdk
  have hroot : Real.sqrt (2*d) ≤ 8*Real.sqrt k := by
    have h1 := Real.sq_sqrt (show (0:ℝ) ≤ 2*d by positivity)
    have h2 := Real.sq_sqrt hkR.le
    have h3 := Real.sqrt_nonneg (2*(d:ℝ))
    have h4 := Real.sqrt_pos.mpr hkR
    nlinarith
  have hc : 0 ≤ 6/Real.sqrt k := by positivity
  have hcs : 6/Real.sqrt k * Real.sqrt (2*d) ≤ 48 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (Real.sqrt_pos.mpr hkR)]
    nlinarith
  have hvol : unitBallVolume k ^ n * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) ≤
      (48 : ℝ≥0∞)^(k*n) := by
    calc
      _ ≤ ENNReal.ofReal ((6/Real.sqrt k)^k)^n * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) :=
        mul_le_mul' (pow_le_pow_left' (unitBallVolume_bound k hk) n) le_rfl
      _ = ENNReal.ofReal (6/Real.sqrt k * Real.sqrt (2*d))^(k*n) := by
        rw [ENNReal.ofReal_pow hc, ← pow_mul, ENNReal.ofReal_mul hc, mul_pow]
      _ ≤ (48 : ℝ≥0∞)^(k*n) := pow_le_pow_left' (by exact_mod_cast ENNReal.ofReal_le_ofReal hcs) _
  have h2 : (2 : ℝ≥0∞)^k ≤ (2 : ℝ≥0∞)^(d*(n+1)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have h48 : (48 : ℝ≥0∞)^(k*n) ≤ (64 : ℝ≥0∞)^(d*(n+1)) :=
    (pow_le_pow_left' (by norm_num : (48:ℝ≥0∞) ≤ 64) _).trans
      (pow_le_pow_right₀ (by norm_num) (by nlinarith))
  have h128 : (128 : ℝ≥0∞)^(d*n) ≤ (128 : ℝ≥0∞)^(d*(n+1)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have hDD : ENNReal.ofReal (D^d)^(n+1) ≤ ENNReal.ofReal (max D 1)^(d*(n+1)) := by
    rw [ENNReal.ofReal_pow hD.le, ← pow_mul]
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  calc
    _ = (2 : ℝ≥0∞)^k *
        (unitBallVolume k ^ n * ENNReal.ofReal (Real.sqrt (2*d))^(k*n)) *
        ENNReal.ofReal (D^d)^(n+1) * (128 : ℝ≥0∞)^(d*n) := by ring
    _ ≤ (2 : ℝ≥0∞)^(d*(n+1)) * (64 : ℝ≥0∞)^(d*(n+1)) *
        ENNReal.ofReal (max D 1)^(d*(n+1)) * (128 : ℝ≥0∞)^(d*(n+1)) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' h2 (hvol.trans h48)) hDD) h128
    _ = ENNReal.ofReal ((16384 * max D 1)^(d*(n+1))) := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat]
      rw [← mul_pow, ← mul_pow, ← mul_pow]
      congr 1
      ring

theorem normalized_unitBall_moment (D : ℝ) (hD : 0 < D) :
    ∃ C_D : ℝ, 0 < C_D ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let lam : ℝ := ((d:ℝ)-1)/2
      ∀ (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
        (u : Fin k → EuclideanSpace ℝ (Fin d)),
        ν Set.univ ≤ 1 → ν.support ⊆ Metric.closedBall 0 1 →
        AllBallMass ν (D^d) lam → Orthonormal ℝ u →
        (∀ᵐ X ∂Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d))),
          ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) →
        Measurable (normalizedDensity ν k u) ∧
        (∀ᵐ X ∂Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d))),
          ((unitBallVolume k)⁻¹ • (volume : Measure (Label k))).withDensity
            (fun y => normalizedDensity ν k u (X,y)) = ν.map (rowMap (polarRows u X))) ∧
        (∀ X y, 1 < ‖y‖ → normalizedDensity ν k u (X,y) = 0) ∧
        (∫⁻ X, ∫⁻ y, normalizedDensity ν k u (X,y)^k ∂unitBallLaw k
          ∂Measure.pi (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤
          ENNReal.ofReal (Real.exp (C_D*d*k)) := by
  refine ⟨Real.log (16384*max D 1), Real.log_pos (by nlinarith [le_max_right D 1]), ?_⟩
  intro d hd k lam ν _ u hmass hs hν hu hac
  have hk2 : 2 ≤ k := by dsimp [k]; omega
  have hk : 1 ≤ k := by omega
  have hkd : k ≤ d := by dsimp [k]; omega
  have hdk : d ≤ 32*k := by dsimp [k]; omega
  have h16 : 16*k ≤ d := by dsimp [k]; omega
  have hnc : k-1+1 = k := by omega
  have hncR : ((k-1:ℕ):ℝ)+1 = k := by exact_mod_cast hnc
  have h16R : 16*(k:ℝ) ≤ d := by exact_mod_cast h16
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk2
  have hdR : (32:ℝ) ≤ d := by exact_mod_cast hd
  have hmargin : ((k-1:ℕ):ℝ)+k ≤ lam := by dsimp [lam]; linarith
  have hlamd : lam ≤ (d:ℝ) := by dsimp [lam]; linarith
  have hac' := polar_ac_to_frame ν (by simpa using hkd) hu hac
  refine ⟨measurable_normalizedDensity ν k u, ?_, ?_, ?_⟩
  · filter_upwards [hac] with X hX
    exact normalizedDensity_is_density ν X hX
  · exact normalizedDensity_support ν hu hs
  · have hframe := frame_moment_scaled hν (pow_pos hD d) (0 : EuclideanSpace ℝ (Fin d))
      (by norm_num : (0:ℝ) < 1) hs k (k-1) hmargin
      (by simpa using (show 1 ≤ d by omega)) (by simpa using hlamd) (by simpa using hkd) u hu hac'
    simp only [Real.one_rpow, mul_one, one_pow, ENNReal.ofReal_one, finrank_euclideanSpace_fin] at hframe
    have hnorm := (normalizedMoment_le ν (by simpa using hkd) hu (k-1)).trans
      (mul_le_mul' le_rfl hframe)
    have hcost := normalized_cost d k (k-1) hk hkd hdk D hD
    have hres := hnorm.trans hcost
    rw [hnc] at hres
    have he : (16384*max D 1)^(d*k) = Real.exp (Real.log (16384*max D 1)*d*k) := by
      rw [show Real.log (16384*max D 1)*(d:ℝ)*k = ((d*k:ℕ):ℝ)*Real.log (16384*max D 1) by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log (by positivity)]
    simpa only [he] using hres

end ProjectionMoments

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphere_packing_annulus (s : Finset E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : ∀ x ∈ s, ‖x‖ = 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) :
    (s.card : ℝ) * (r/2)^Module.finrank ℝ E ≤
      (1+r/2)^Module.finrank ℝ E - (1-r/2)^Module.finrank ℝ E := by
  classical
  let δ := r/2
  let U : Set E := ⋃ c ∈ s, Metric.ball c δ
  let V : Set E := Metric.ball 0 (1-δ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hinner : 0 < 1-δ := by dsimp [δ]; linarith
  have houter : 0 < 1+δ := by positivity
  have hdis : Set.Pairwise (s : Set E) (fun c d => Disjoint (Metric.ball c δ) (Metric.ball d δ)) := by
    intro c hc d hd hcd
    apply Metric.ball_disjoint_ball
    simpa [δ] using hsep c hc d hd hcd
  have hUV : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro x hx hxV
    obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp hx
    have hxc' : dist x c < δ := hxc
    have hx0 : ‖x‖ < 1-δ := by simpa [V, Metric.mem_ball, dist_zero_right] using hxV
    have hc1 := hs c hc
    have htri := dist_triangle c x (0 : E)
    rw [dist_zero_right, dist_zero_right, dist_comm c x, hc1] at htri
    linarith
  have hsub : U ∪ V ⊆ Metric.ball (0 : E) (1+δ) := by
    rintro x (hx | hx)
    · obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp hx
      apply Metric.mem_ball.mpr
      have htri := dist_triangle x c (0 : E)
      rw [dist_zero_right c, hs c hc] at htri
      exact htri.trans_lt (by have hh : dist x c < δ := hxc; linarith)
    · exact (Metric.ball_subset_ball (by linarith : 1-δ ≤ 1+δ)) hx
  have hU : MeasurableSet U := MeasurableSet.biUnion s.finite_toSet.countable
    (fun c _ => Metric.isOpen_ball.measurableSet)
  have hvol : ((s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E) +
      ENNReal.ofReal ((1-δ)^Module.finrank ℝ E)) * volume (Metric.ball (0 : E) 1) ≤
      ENNReal.ofReal ((1+δ)^Module.finrank ℝ E)*volume (Metric.ball (0 : E) 1) := by
    calc
      _ = volume (U ∪ V) := by
        rw [measure_union hUV Metric.isOpen_ball.measurableSet,
          show volume U = (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E)*
            volume (Metric.ball (0 : E) 1) by
            rw [measure_biUnion_finset hdis (fun _ _ => Metric.isOpen_ball.measurableSet)]
            simp only [Measure.addHaar_ball_of_pos volume _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc],
          Measure.addHaar_ball_of_pos volume 0 hinner, add_mul]
      _ ≤ volume (Metric.ball (0 : E) (1+δ)) := measure_mono hsub
      _ = _ := Measure.addHaar_ball_of_pos volume 0 houter
  have hv0 : volume (Metric.ball (0 : E) 1) ≠ 0 := (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
  have hvt : volume (Metric.ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hh := (ENNReal.mul_le_mul_iff_left hv0 hvt).mp hvol
  have hreal := ENNReal.toReal_le_of_le_ofReal (pow_nonneg houter.le _) hh
  simp only [ENNReal.toReal_add (by finiteness :
    (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E) ≠ ∞) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (pow_nonneg hδ.le _),
    ENNReal.toReal_ofReal (pow_nonneg hinner.le _)] at hreal
  dsimp [δ] at hreal
  linarith

lemma sphere_packing_bound (s : Finset E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hd : 1 ≤ Module.finrank ℝ E) (hs : ∀ x ∈ s, ‖x‖ = 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) :
    (s.card : ℝ)*r^(Module.finrank ℝ E-1) ≤ (8 : ℝ)^Module.finrank ℝ E := by
  let d := Module.finrank ℝ E
  have hi : 0 ≤ 1-r/2 := by linarith
  have ho : 0 ≤ 1+r/2 := by positivity
  have hio : 1-r/2 ≤ 1+r/2 := by linarith
  have h := sphere_packing_annulus s hr hr1 hs hsep
  have hdiff : (1+r/2)^d - (1-r/2)^d ≤ r*d*(1+r/2)^(d-1) := by
    have hh := abs_pow_sub_pow_le (a := (1+r/2)) (b := (1-r/2)) (n := d)
    rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hi hio d)),
      abs_of_nonneg ho, abs_of_nonneg hi, max_eq_left hio,
      show (1+r/2)-(1-r/2) = r by ring, abs_of_pos hr] at hh
    exact hh
  have hpow : (1+r/2)^(d-1) ≤ (2 : ℝ)^d := by
    exact (pow_le_pow_left₀ ho (by linarith : 1+r/2 ≤ 2) _).trans
      (pow_le_pow_right₀ (by norm_num) (Nat.sub_le d 1))
  have hd2 : (d : ℝ) ≤ (2 : ℝ)^d := by
    have hn : ∀ n : ℕ, (n : ℝ) ≤ (2 : ℝ)^n := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        have hp : (1 : ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
        rw [Nat.cast_succ, pow_succ]
        linarith
    exact hn d
  have hupper : r*d*(1+r/2)^(d-1) ≤ r*(4 : ℝ)^d := by
    calc
      _ ≤ r*2^d*2^d := mul_le_mul (mul_le_mul_of_nonneg_left hd2 hr.le) hpow (by positivity) (by positivity)
      _ = _ := by rw [mul_assoc, ← mul_pow]; norm_num
  have hall := h.trans (hdiff.trans hupper)
  have htwo : 0 < (2 : ℝ)^d := by positivity
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ htwo] at hall
  have hp : r^d = r^(d-1)*r := by rw [← pow_succ, Nat.sub_add_cancel hd]
  rw [hp, ← mul_assoc, mul_assoc r, ← mul_pow] at hall
  norm_num only at hall
  nlinarith

lemma sphere_cap_mass_center [Nontrivial E] {c c' : E} (hc : ‖c‖ = 1) (hc' : ‖c'‖ = 1)
    (r : ℝ) :
    NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) =
      NoiselessRegression.ambientSphereLaw (Metric.closedBall c' r) := by
  obtain ⟨O,hO⟩ := rotation_transitive
    (show Orthonormal ℝ (fun _ : Fin 1 => c) by simpa using hc)
    (show Orthonormal ℝ (fun _ : Fin 1 => c') by simpa using hc')
  let e : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv O
  have he : e c = c' := hO 0
  have hh := (NoiselessRegression.ambientSphereLaw_isometry e).map_eq
  have hpre : e ⁻¹' Metric.closedBall c' r = Metric.closedBall c r := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_closedBall, ← he, e.dist_map]
  have h := congrArg (fun μ : Measure E => μ (Metric.closedBall c' r)) hh
  rw [Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet, hpre] at h
  exact h

lemma sphere_finite_net {r : ℝ} (hr : 0 < r) :
    ∃ s : Finset E, (∀ c ∈ s, ‖c‖ = 1) ∧
      (∀ c ∈ s, ∀ c' ∈ s, c ≠ c' → r < dist c c') ∧
      ∀ x : E, ‖x‖ = 1 → ∃ c ∈ s, dist x c ≤ r := by
  classical
  let N := ⌈((1+r/2)/(r/2))^Module.finrank ℝ E⌉₊
  obtain ⟨s,hs,hsep,hnet⟩ := NoiselessRegression.exists_net_of_finite_packing_bound
    {x : E | ‖x‖ = 1} hr.le N (by
      intro s hs hsep
      have hh := NoiselessRegression.card_le_volume_ratio s hr (by norm_num : (0:ℝ) ≤ 1)
        (fun c hc => (hs c hc).le) (fun c hc c' hc' hne => (hsep c hc c' hc' hne).le)
      exact_mod_cast hh.trans (Nat.le_ceil _))
  exact ⟨s,hs,hsep,hnet⟩

lemma sphere_cap_lower_one [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (r^(Module.finrank ℝ E-1)) ≤
      ENNReal.ofReal ((8:ℝ)^Module.finrank ℝ E) *
        NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) := by
  classical
  let μ : Measure E := NoiselessRegression.ambientSphereLaw
  obtain ⟨s,hs,hsep,hnet⟩ := sphere_finite_net (E := E) hr
  have hcard := sphere_packing_bound s hr hr1
    (Module.finrank_pos (R := ℝ) (M := E)) hs
    (fun x hx y hy hxy => (hsep x hx y hy hxy).le)
  have hcover : μ (⋃ x ∈ s, Metric.closedBall x r) = 1 := by
    rw [← measure_univ (μ := μ)]
    apply measure_congr
    filter_upwards [NoiselessRegression.ambientSphereLaw_ae_norm (E := E)] with x hx
    apply propext
    change (x ∈ ⋃ y ∈ s, Metric.closedBall y r) ↔ x ∈ Set.univ
    simp only [Set.mem_univ, iff_true]
    obtain ⟨y,hy,hxy⟩ := hnet x hx
    exact Set.mem_iUnion₂.mpr ⟨y,hy,hxy⟩
  have hone : (1 : ℝ≥0∞) ≤ (s.card : ℝ≥0∞)*μ (Metric.closedBall c r) := by
    calc
      _ = μ (⋃ x ∈ s, Metric.closedBall x r) := hcover.symm
      _ ≤ ∑ x ∈ s, μ (Metric.closedBall x r) := measure_biUnion_finset_le _ _
      _ = _ := by
        have hm : ∀ x ∈ s, μ (Metric.closedBall x r) = μ (Metric.closedBall c r) :=
          fun x hx => sphere_cap_mass_center (hs x hx) hc r
        simp_rw [Finset.sum_congr rfl hm]
        simp
  calc
    _ = ENNReal.ofReal (r^(Module.finrank ℝ E-1))*1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal (r^(Module.finrank ℝ E-1))*
        ((s.card : ℝ≥0∞)*μ (Metric.closedBall c r)) := mul_le_mul' le_rfl hone
    _ = ENNReal.ofReal ((s.card:ℝ)*r^(Module.finrank ℝ E-1))*
        μ (Metric.closedBall c r) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]; ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hcard) le_rfl

lemma sphere_cap_lower [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    ENNReal.ofReal (r^(Module.finrank ℝ E-1)) ≤
      ENNReal.ofReal ((16:ℝ)^Module.finrank ℝ E) *
        NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) := by
  by_cases hr1 : r ≤ 1
  · exact (sphere_cap_lower_one hc hr hr1).trans (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8)
        (by norm_num : (8:ℝ) ≤ 16) _)) le_rfl)
  · have h1 := sphere_cap_lower_one hc (by norm_num : (0:ℝ) < 1) le_rfl
    simp only [one_pow, ENNReal.ofReal_one] at h1
    have h2 : r^(Module.finrank ℝ E-1) ≤ (2:ℝ)^Module.finrank ℝ E :=
      (pow_le_pow_left₀ hr.le hr2 _).trans
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
    calc
      _ ≤ ENNReal.ofReal ((2:ℝ)^Module.finrank ℝ E)*1 := by
        simpa using ENNReal.ofReal_le_ofReal h2
      _ ≤ ENNReal.ofReal ((2:ℝ)^Module.finrank ℝ E)*
          (ENNReal.ofReal ((8:ℝ)^Module.finrank ℝ E)*
            NoiselessRegression.ambientSphereLaw (Metric.closedBall c 1)) := mul_le_mul' le_rfl h1
      _ ≤ ENNReal.ofReal ((2:ℝ)^Module.finrank ℝ E)*
          (ENNReal.ofReal ((8:ℝ)^Module.finrank ℝ E)*
            NoiselessRegression.ambientSphereLaw (Metric.closedBall c r)) := by
          gcongr
          exact le_of_not_ge hr1
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]; norm_num

end

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma cap_mass_pos [Nontrivial E] {c : E} (hc : ‖c‖ = 1) {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) ≠ 0 := by
  intro h
  have hh := sphere_cap_lower hc hr hr2
  rw [h,mul_zero] at hh
  exact (ENNReal.ofReal_pos.mpr (pow_pos hr _)).not_ge hh

lemma capMeasure_probability [Nontrivial E] {c : E} (hc : ‖c‖ = 1) {r : ℝ}
    (hr : 0 < r) (hr2 : r ≤ 2) : IsProbabilityMeasure (capMeasure c r) := by
  constructor
  simp only [capMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (cap_mass_pos hc hr hr2) (measure_ne_top _ _)

lemma capMeasure_ac (c : E) (r : ℝ) : capMeasure c r ≪ NoiselessRegression.ambientSphereLaw :=
  Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict

lemma capMeasure_support (c : E) (r : ℝ) : (capMeasure c r).support ⊆ Metric.closedBall c r := by
  intro x hx
  have hh := (Measure.support_restrict_subset
    (Measure.smul_absolutelyContinuous.support_mono hx)).1
  simpa only [Metric.isClosed_closedBall.closure_eq] using hh

lemma reciprocal_scale {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 1/4) :
    ∃ j : ℕ, 4*t ≤ 1/((j:ℝ)+1) ∧ 1/((j:ℝ)+1) < 8*t := by
  let n := ⌊1/(4*t)⌋₊
  have hx : 1 ≤ 1/(4*t) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hn : 1 ≤ n := (Nat.one_le_floor_iff _).mpr hx
  have hnle : (n:ℝ) ≤ 1/(4*t) := Nat.floor_le (by positivity)
  have hnlt : 1/(4*t) < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have he : ((n-1:ℕ):ℝ)+1 = n := by exact_mod_cast (Nat.sub_add_cancel hn)
  refine ⟨n-1, ?_, ?_⟩
  · rw [he]
    rw [le_div_iff₀ (by exact_mod_cast (show 0 < n by omega))]
    rw [le_div_iff₀ (by positivity)] at hnle
    nlinarith
  · rw [he, div_lt_iff₀ (by exact_mod_cast (show 0 < n by omega))]
    rw [div_lt_iff₀ (by positivity)] at hnlt
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

lemma exists_capDictionary {c : E} (hc : ‖c‖ = 1) {r α : ℝ}
    (hr : 0 < r) (hα : 1 ≤ α) : Nonempty (CapDictionary c r α) := by
  classical
  let ρ : ℕ → ℝ := fun j => r/((j:ℝ)+1)
  have hρ : ∀ j, 0 < ρ j := fun j => div_pos hr (by positivity)
  choose net hnetnorm hnetsep hnetcover using
    (fun j : ℕ => sphere_finite_net (E := E) (half_pos (hρ j)))
  let I := Option (Σ j : ℕ, {s : E // s ∈ net j})
  let center : I → E := fun i => match i with | none => c | some p => p.2.val
  let radius : I → ℝ := fun i => match i with | none => r | some p => ρ p.1
  have hw (j : ℕ) : (r/ρ j)^α = ((j:ℝ)+1)^α := by
    congr 1
    dsimp [ρ]
    field_simp
  have hproper : ∀ R : ℝ, {i : I | (r/radius i)^α ≤ R}.Finite := by
    intro R
    have hlevel (j : ℕ) : (j:ℝ) ≤ (r/ρ j)^α := by
      rw [hw]
      calc
        _ ≤ (j:ℝ)+1 := by linarith
        _ = ((j:ℝ)+1)^(1:ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith [show (0:ℝ) ≤ j from Nat.cast_nonneg j]) hα
    have hsubset : {i : I | (r/radius i)^α ≤ R} ⊆
        insert none (⋃ j ∈ Finset.range (⌈R⌉₊+1), Option.some ''
          (Sigma.mk j '' (Set.univ : Set {s : E // s ∈ net j}))) := by
      intro i hi
      cases i with
      | none => exact Set.mem_insert _ _
      | some p =>
        right
        have hjR : (p.1:ℝ) ≤ R := (hlevel p.1).trans hi
        have hj : p.1 ∈ Finset.range (⌈R⌉₊+1) := by
          apply Finset.mem_range.mpr
          have hh : p.1 ≤ ⌈R⌉₊ := by exact_mod_cast hjR.trans (Nat.le_ceil R)
          omega
        exact Set.mem_iUnion₂.mpr ⟨p.1,hj,⟨p,⟨p.2,Set.mem_univ _,rfl⟩,rfl⟩⟩
    apply Set.Finite.subset _ hsubset
    apply Set.Finite.insert
    apply Set.Finite.biUnion (Finset.finite_toSet _)
    intro j hj
    exact ((Set.toFinite (Set.univ : Set {s : E // s ∈ net j})).image (Sigma.mk j)).image Option.some
  refine ⟨{
    I := I
    countable := inferInstance
    center := center
    radius := radius
    center_norm := ?_
    radius_pos := ?_
    radius_le := ?_
    parent := none
    parent_center := rfl
    parent_radius := rfl
    proper := hproper
    cover := ?_ }⟩
  · rintro (_|⟨j,s,hs⟩)
    · exact hc
    · exact hnetnorm j s hs
  · rintro (_|⟨j,s⟩)
    · exact hr
    · exact hρ j
  · rintro (_|⟨j,s⟩)
    · exact le_rfl
    · change r/((j:ℝ)+1) ≤ r
      exact div_le_self hr.le (by linarith [show (0:ℝ) ≤ j from Nat.cast_nonneg j])
  · intro s hs t ht ht4
    obtain ⟨j,hj1,hj2⟩ := reciprocal_scale ht ht4
    obtain ⟨s',hs',hss'⟩ := hnetcover j s hs
    refine ⟨some ⟨j,s',hs'⟩,?_,?_,hss'⟩
    · change 4*r*t ≤ r/((j:ℝ)+1)
      have hh := mul_le_mul_of_nonneg_left hj1 hr.le
      rw [mul_one_div] at hh
      nlinarith only [hh]
    · change r/((j:ℝ)+1) < 8*r*t
      have hh := mul_lt_mul_of_pos_left hj2 hr
      rw [mul_one_div] at hh
      nlinarith only [hh]

end ProjectionMoments

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma cap_mass_inv_bound [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    (NoiselessRegression.ambientSphereLaw (Metric.closedBall c r))⁻¹ ≤
      ENNReal.ofReal ((r^(Module.finrank ℝ E-1))⁻¹ * (16:ℝ)^Module.finrank ℝ E) := by
  let p := NoiselessRegression.ambientSphereLaw (Metric.closedBall c r)
  let a := ENNReal.ofReal (r^(Module.finrank ℝ E-1))
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
  have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
  have h := mul_le_mul' (le_rfl : a⁻¹ ≤ a⁻¹) (sphere_cap_lower hc hr hr2)
  change a⁻¹*a ≤ a⁻¹ * (ENNReal.ofReal ((16:ℝ)^Module.finrank ℝ E) * p) at h
  rw [ENNReal.inv_mul_cancel ha0 hat, ← mul_assoc] at h
  have hh : p⁻¹ ≤ a⁻¹ * ENNReal.ofReal ((16:ℝ)^Module.finrank ℝ E) := by
    apply (ENNReal.mul_le_mul_iff_right (cap_mass_pos hc hr hr2) (measure_ne_top _ _)).mp
    change p*p⁻¹ ≤ p*(a⁻¹ * ENNReal.ofReal ((16:ℝ)^Module.finrank ℝ E))
    rw [ENNReal.mul_inv_cancel (cap_mass_pos hc hr hr2) (measure_ne_top _ _)]
    simpa only [mul_comm] using h
  simpa only [a, ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hr.le _)),
    ENNReal.ofReal_inv_of_pos (pow_pos hr _)] using hh

lemma cap_ratio_algebra (d n : ℕ) {r ρ α : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hα : 2*α = n) :
    (r^n)⁻¹ * (16:ℝ)^d * (3*4^d*ρ^n) * (r/ρ)^α =
      3*64^d*(ρ/r)^α := by
  have hre : r^n = (r^α)^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hr.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    linarith
  have hρe : ρ^n = (ρ^α)^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hρ.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    linarith
  rw [hre,hρe,Real.div_rpow hr.le hρ.le, Real.div_rpow hρ.le hr.le]
  have hc : (16:ℝ)^d * 4^d = 64^d := by rw [← mul_pow]; norm_num
  field_simp [(Real.rpow_pos_of_pos hr α).ne', (Real.rpow_pos_of_pos hρ α).ne']
  nlinarith [hc]

lemma cap_cost_ratio [Nontrivial E] {c c' : E} (hc : ‖c‖ = 1)
    {r ρ α : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hρ : 0 < ρ)
    (hα : 2*α = (Module.finrank ℝ E-1:ℕ)) :
    (NoiselessRegression.ambientSphereLaw (Metric.closedBall c r))⁻¹ *
      NoiselessRegression.ambientSphereLaw (Metric.closedBall c' ρ) * ENNReal.ofReal ((r/ρ)^α) ≤
        ENNReal.ofReal (3*64^Module.finrank ℝ E*(ρ/r)^α) := by
  have hu := NoiselessRegression.ambientSphereLaw_closedBall c' hρ (Module.finrank ℝ E-1) le_rfl
  have h := mul_le_mul' (mul_le_mul' (cap_mass_inv_bound hc hr hr2) hu)
    (le_rfl : ENNReal.ofReal ((r/ρ)^α) ≤ _)
  rw [← ENNReal.ofReal_mul (by positivity)] at hu
  apply le_trans (mul_le_mul' (mul_le_mul' (cap_mass_inv_bound hc hr hr2) hu) le_rfl)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    cap_ratio_algebra _ _ hr hρ hα]

lemma cap_small_scale_constant (d : ℕ) (hd : 1 ≤ d) {α ρ r t : ℝ}
    (hα0 : 0 ≤ α) (hαd : α ≤ d) (hr : 0 < r) (ht : 0 < t)
    (hρ : 0 ≤ ρ) (hρt : ρ ≤ 8*r*t) :
    3*64^d*(ρ/r)^α ≤ (2048:ℝ)^d*t^α := by
  have hratio : ρ/r ≤ 8*t := (div_le_iff₀ hr).mpr (by nlinarith)
  have h8 : (8:ℝ)^α ≤ (8:ℝ)^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hαd
  have h3 : (3:ℝ) ≤ 3^d := by simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hd
  calc
    _ ≤ 3*64^d*(8*t)^α := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg hρ hr.le) hratio hα0) (by positivity)
    _ = 3*64^d*8^α*t^α := by rw [Real.mul_rpow (by norm_num) ht.le]; ring
    _ ≤ 3^d*64^d*8^d*t^α := by rw [Real.rpow_natCast] at h8; gcongr
    _ = (1536:ℝ)^d*t^α := by rw [← mul_pow, ← mul_pow]; norm_num
    _ ≤ _ := by gcongr; norm_num

lemma weighted_cap_set_le [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r b : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (h : E → ℝ≥0∞)
    (hb : ∫⁻ x, h x ∂capMeasure c r ≤ ENNReal.ofReal b) :
    (NoiselessRegression.ambientSphereLaw.withDensity h) (Metric.closedBall c r) ≤
      NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) * ENNReal.ofReal b := by
  rw [capMeasure, lintegral_smul_measure, smul_eq_mul] at hb
  rw [withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
  exact (ENNReal.inv_mul_le_iff (cap_mass_pos hc hr hr2) (measure_ne_top _ _)).mp hb

def capTestMeasure (h : E → ℝ≥0∞) (c : E) (r : ℝ) : Measure E :=
  ((capMeasure c r).withDensity h).map (rescale c r)

lemma capTestMeasure_mass {h : E → ℝ≥0∞} {c : E} {r α : ℝ} (hr : 0 < r)
    (D : CapDictionary c r α)
    (hdual : ∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) :
    capTestMeasure h c r Set.univ ≤ 1 := by
  have hp := hdual D.parent
  rw [D.parent_center,D.parent_radius,div_self hr.ne',Real.one_rpow,ENNReal.ofReal_one] at hp
  simpa only [capTestMeasure,Measure.map_apply (measurable_rescale c r) MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hp

lemma capTestMeasure_finite {h : E → ℝ≥0∞} {c : E} {r α : ℝ} (hr : 0 < r)
    (D : CapDictionary c r α)
    (hdual : ∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) :
    IsFiniteMeasure (capTestMeasure h c r) :=
  ⟨(capTestMeasure_mass hr D hdual).trans_lt (by simp)⟩

lemma capTestMeasure_support (h : E → ℝ≥0∞) (c : E) {r : ℝ} (hr : 0 < r) :
    (capTestMeasure h c r).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  apply (ae_map_iff (measurable_rescale c r).aemeasurable Metric.isClosed_closedBall.measurableSet).mpr
  filter_upwards [((capMeasure c r).withDensity h).support_mem_ae] with x hx
  have hx' := capMeasure_support c r ((withDensity_absolutelyContinuous (capMeasure c r) h).support_mono hx)
  change x ∈ rescale c r ⁻¹' Metric.closedBall 0 1
  rw [rescale_preimage_closedBall c 0 hr, dilate, smul_zero, zero_add, mul_one]
  exact hx'

lemma capTestMeasure_ball (h : E → ℝ≥0∞) (c : E) {r : ℝ} (hr : 0 < r) (b : E) (t : ℝ) :
    capTestMeasure h c r (Metric.closedBall b t) =
      (NoiselessRegression.ambientSphereLaw (Metric.closedBall c r))⁻¹ *
        (NoiselessRegression.ambientSphereLaw.withDensity h)
          (Metric.closedBall (dilate c r b) (r*t) ∩ Metric.closedBall c r) := by
  rw [capTestMeasure, Measure.map_apply (measurable_rescale c r) Metric.isClosed_closedBall.measurableSet,
    rescale_preimage_closedBall c b hr, capMeasure, withDensity_smul_measure,
    Measure.smul_apply, smul_eq_mul, ← restrict_withDensity Metric.isClosed_closedBall.measurableSet,
    Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]

lemma capTest_allBall [Nontrivial E] {h : E → ℝ≥0∞} {c : E} (hc : ‖c‖ = 1)
    {r α : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hα0 : 0 ≤ α)
    (hα : 2*α = (Module.finrank ℝ E-1:ℕ)) (D : CapDictionary c r α)
    (hdual : ∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) :
    AllBallMass (capTestMeasure h c r) ((2048:ℝ)^Module.finrank ℝ E) α := by
  have hd : 1 ≤ Module.finrank ℝ E := Module.finrank_pos (R := ℝ) (M := E)
  have hαd : α ≤ Module.finrank ℝ E := by
    have hn : ((Module.finrank ℝ E-1:ℕ):ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast Nat.sub_le (Module.finrank ℝ E) 1
    linarith
  intro b t ht
  by_cases ht4 : t ≤ 1/4
  · let ξ := NoiselessRegression.ambientSphereLaw.withDensity h
    let T := (Metric.closedBall (dilate c r b) (r*t) ∩ Metric.closedBall c r) ∩ Metric.sphere 0 1
    have he : ξ (Metric.closedBall (dilate c r b) (r*t) ∩ Metric.closedBall c r) = ξ T := by
      apply measure_congr
      filter_upwards [(withDensity_absolutelyContinuous NoiselessRegression.ambientSphereLaw h).ae_le
        (NoiselessRegression.ambientSphereLaw_ae_norm (E := E))] with x hx
      have hs : x ∈ Metric.sphere (0:E) 1 := by simpa using hx
      apply propext
      show x ∈ (Metric.closedBall (dilate c r b) (r*t) ∩ Metric.closedBall c r) ↔ x ∈ T
      simp only [T, Set.mem_inter_iff, hs, and_true]
    rw [capTestMeasure_ball h c hr, he]
    by_cases hT : T.Nonempty
    · obtain ⟨s,hs⟩ := hT
      have hsn : ‖s‖ = 1 := by simpa using hs.2
      obtain ⟨i,hi1,hi2,hsi⟩ := D.cover s hsn t ht ht4
      have hsub : T ⊆ Metric.closedBall (D.center i) (D.radius i) := by
        intro x hx
        change dist x (D.center i) ≤ D.radius i
        have hxB : dist x (dilate c r b) ≤ r*t := hx.1.1
        have hsB : dist s (dilate c r b) ≤ r*t := hs.1.1
        calc
          _ ≤ dist x s + dist s (D.center i) := dist_triangle _ _ _
          _ ≤ (dist x (dilate c r b) + dist (dilate c r b) s) + D.radius i/2 :=
            add_le_add (dist_triangle _ _ _) hsi
          _ ≤ D.radius i := by rw [dist_comm (dilate c r b) s]; linarith
      apply (mul_le_mul' le_rfl (measure_mono hsub)).trans
      have htest := weighted_cap_set_le (D.center_norm i) (D.radius_pos i)
        ((D.radius_le i).trans hr2) h (hdual i)
      apply (mul_le_mul' le_rfl htest).trans
      rw [← mul_assoc]
      exact (cap_cost_ratio hc hr hr2 (D.radius_pos i) hα).trans
        (ENNReal.ofReal_le_ofReal (cap_small_scale_constant _ hd hα0 hαd hr ht (D.radius_pos i).le hi2.le))
    · rw [Set.not_nonempty_iff_eq_empty.mp hT, measure_empty, mul_zero]
      exact bot_le
  · apply (measure_mono (Set.subset_univ _)).trans ((capTestMeasure_mass hr D hdual).trans ?_)
    have h4t : 1 ≤ 4*t := by linarith
    have hpow : 1 ≤ (4*t)^α := Real.one_le_rpow h4t hα0
    have h4 : (4:ℝ)^α ≤ (2048:ℝ)^Module.finrank ℝ E := by
      calc
        _ ≤ (4:ℝ)^(Module.finrank ℝ E:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hαd
        _ = (4:ℝ)^Module.finrank ℝ E := Real.rpow_natCast _ _
        _ ≤ _ := by gcongr; norm_num
    rw [Real.mul_rpow (by norm_num) ht.le] at hpow
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hpow.trans (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg ht.le α)))

lemma rescaled_projection_ac {ν : Measure E} {k : ℕ} (A : Fin k → E) (c : E) {r : ℝ} (hr : 0 < r)
    (hν : ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))) :
    (ν.map (rescale c r)).map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by
  let T : (Fin k → ℝ) → (Fin k → ℝ) := fun y => r⁻¹ • (y-coordinateMap A c)
  have hT : Measurable T := by fun_prop
  have hv : (volume : Measure (Fin k → ℝ)).map T ≪ volume := by
    have he : T = (fun y : Fin k → ℝ => r⁻¹ • y) ∘ (fun y => y + -coordinateMap A c) := by
      funext y; simp [T,sub_eq_add_neg]
    rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
      Measure.IsAddRightInvariant.map_add_right_eq_self, Measure.map_addHaar_smul volume (inv_ne_zero hr.ne')]
    exact Measure.smul_absolutelyContinuous
  have hh := (hν.map hT).trans hv
  rw [Measure.map_map hT (by fun_prop)] at hh
  rw [Measure.map_map (by fun_prop) (measurable_rescale c r)]
  convert hh using 1
  congr 1
  funext s
  ext i
  simp [T, rescale, coordinateMap_apply, real_inner_smul_left, inner_sub_left]

lemma capTest_frame_ac [Nontrivial E] (h : E → ℝ≥0∞) (c : E) {r : ℝ} (hr : 0 < r)
    {k : ℕ} (hk : k+2 ≤ Module.finrank ℝ E) (A : Fin k → E) (hA : Orthonormal ℝ A) :
    (capTestMeasure h c r).map (rowMap A) ≪ (volume : Measure (Label k)) := by
  apply (rowMap_ac_iff _).mpr
  apply rescaled_projection_ac A c hr
  have hh := (((withDensity_absolutelyContinuous (capMeasure c r) h).trans (capMeasure_ac c r)).map
    (show Measurable (coordinateMap A) by fun_prop)).trans (sphere_frame_ac hk hA)
  exact hh

end ProjectionMoments

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[fun_prop] lemma measurable_radialLabel {k : ℕ} :
    Measurable (fun z : (Fin k → E) × Label k => radialLabel z.1 z.2) := by
  have hH : Measurable (fun z : (Fin k → E) × Label k => polarRadial z.1) := (continuous_polarRadial (E := E) (k := k)).measurable.comp measurable_fst
  apply (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp
  apply Measurable.of_eval
  intro i
  change Measurable (fun z : (Fin k → E) × Label k => ∑ j, polarRadial z.1 i j * z.2.ofLp j)
  apply Finset.measurable_sum
  intro j hj
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hH)).mul (by fun_prop)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowMap_mixRows [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (X : Fin k → E) (s : E) :
    rowMap (mixRows M X) s = WithLp.toLp 2 (M *ᵥ (rowMap X s).ofLp) := by
  ext i
  simp [rowMap, mixRows, Matrix.mulVec, dotProduct]

lemma polar_label_identity {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X)
    (u : Fin k → E) (c s : E) (r : ℝ) :
    rowMap X (dilate c r s) = rowMap X c + r • radialLabel X (rowMap (polarRows u X) s) := by
  have he : radialLabel X (rowMap (polarRows u X) s) = rowMap X s := by
    rw [radialLabel, ← rowMap_mixRows]
    simp only [polarRows, ite_eq_left hX, polar_reconstruction hX]
  rw [he, dilate, map_add, map_smul]
  exact add_comm _ _

lemma normalizedDensity_unitBall (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    {u : Fin k → E} (hu : Orthonormal ℝ u) (hs : ν.support ⊆ Metric.closedBall 0 1)
    (X : Fin k → E) (hac : ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    (unitBallLaw k).withDensity (fun y => normalizedDensity ν k u (X,y)) =
      ν.map (rowMap (polarRows u X)) := by
  have he : (Metric.closedBall (0:Label k) 1).indicator
      (fun y => normalizedDensity ν k u (X,y)) = fun y => normalizedDensity ν k u (X,y) := by
    funext y
    by_cases hy : y ∈ Metric.closedBall (0:Label k) 1
    · simp [hy]
    · rw [Set.indicator_of_notMem hy]
      have hh : 1 < ‖y‖ := by simpa using hy
      exact (normalizedDensity_support ν hu hs X y hh).symm
  rw [unitBallLaw, withDensity_smul_measure, ← withDensity_indicator Metric.isClosed_closedBall.measurableSet, he,
    ← withDensity_smul_measure]
  exact normalizedDensity_is_density ν X hac

@[fun_prop] lemma measurable_capReferenceLabel {k : ℕ} (c : E) (r : ℝ) :
    Measurable (fun z : (Fin k → E) × Label k => capReferenceLabel c r z.1 z.2) := by
  unfold capReferenceLabel
  exact (show Measurable (fun z : (Fin k → E) × Label k => rowMap z.1 c) by
    simp only [rowMap_apply]; fun_prop).add (measurable_radialLabel.const_smul r)

@[fun_prop] lemma measurable_capKernelValue {k : ℕ} {K : (Fin k → E) × Label k → ℝ≥0∞}
    (hK : Measurable K) : Measurable (capKernelValue K) := by
  apply Measurable.lintegral_prod_right
  exact hK.comp (measurable_snd.prodMk (by simp only [rowMap_apply]; fun_prop))

omit [BorelSpace E] in
lemma capReference_le_one [BorelSpace E] {k : ℕ} {K : (Fin k → E) × Label k → ℝ≥0∞}
    (hK1 : ∀ z, K z ≤ 1) (c : E) (r : ℝ) : capReference K c r ≤ 1 := by
  calc
    _ ≤ ∫⁻ X, ∫⁻ z : Label k, (1:ℝ≥0∞) ∂unitBallLaw k ∂Measure.pi (fun _ : Fin k => stdGaussian E) :=
      lintegral_mono (fun X => lintegral_mono (fun z => hK1 _))
    _ = 1 := by simp

omit [BorelSpace E] in
lemma capKernelValue_le_one [BorelSpace E] {k : ℕ} {K : (Fin k → E) × Label k → ℝ≥0∞}
    (hK1 : ∀ z, K z ≤ 1) (s : E) : capKernelValue K s ≤ 1 := by
  calc
    _ ≤ ∫⁻ X : Fin k → E, (1:ℝ≥0∞) ∂Measure.pi (fun _ => stdGaussian E) :=
      lintegral_mono (fun X => hK1 _)
    _ = 1 := by simp

lemma cap_kernel_test_identity {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {K : (Fin k → E) × Label k → ℝ≥0∞} (hK : Measurable K)
    (h : E → ℝ≥0∞) (hh : Measurable h) (c : E) {r : ℝ} (hr : 0 < r)
    {u : Fin k → E} (hu : Orthonormal ℝ u)
    [IsFiniteMeasure ((capMeasure c r).withDensity h)]
    (hac : ∀ X, (capTestMeasure h c r).map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    (∫⁻ s, h s * capKernelValue K s ∂capMeasure c r) =
      ∫⁻ X, ∫⁻ z, normalizedDensity (capTestMeasure h c r) k u (X,z) *
        K (X,capReferenceLabel c r X z) ∂unitBallLaw k ∂Measure.pi (fun _ => stdGaussian E) := by
  let μ := (capMeasure c r).withDensity h
  let ν := capTestMeasure h c r
  have : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  have hf (X : Fin k → E) : Measurable (fun s => K (X,rowMap X s)) := by fun_prop
  have he (X : Fin k → E) (hX : LinearIndependent ℝ X) :
      (∫⁻ s, K (X,rowMap X s) ∂μ) =
      ∫⁻ z, normalizedDensity ν k u (X,z)*K (X,capReferenceLabel c r X z) ∂unitBallLaw k := by
    have hid := lintegral_withDensity_eq_lintegral_mul (unitBallLaw k)
      (show Measurable (fun z => normalizedDensity ν k u (X,z)) by fun_prop)
      (show Measurable (fun z => K (X,capReferenceLabel c r X z)) by fun_prop)
    simp only [Pi.mul_apply] at hid
    rw [← hid,
      normalizedDensity_unitBall ν hu (capTestMeasure_support h c hr) X (hac X),
      lintegral_map (by fun_prop) (by fun_prop)]
    change _ = ∫⁻ s, K (X,capReferenceLabel c r X (rowMap (polarRows u X) s)) ∂μ.map (rescale c r)
    rw [lintegral_map (by fun_prop) (measurable_rescale c r)]
    apply lintegral_congr
    intro s
    congr 1
    rw [capReferenceLabel, ← polar_label_identity hX u c (rescale c r s) r,
      dilate_rescale c hr.ne']
  have hid := lintegral_withDensity_eq_lintegral_mul (capMeasure c r) hh (measurable_capKernelValue hK)
  simp only [Pi.mul_apply] at hid
  rw [← hid]
  change (∫⁻ s, ∫⁻ X, K (X,rowMap X s) ∂Measure.pi (fun _ => stdGaussian E) ∂μ) = _
  rw [lintegral_lintegral_swap (show AEMeasurable (fun z : E × (Fin k → E) => K (z.2,rowMap z.2 z.1)) _ by
    apply Measurable.aemeasurable; exact hK.comp (measurable_snd.prodMk (by simp only [rowMap_apply]; fun_prop)))]
  exact lintegral_congr_ae (by filter_upwards [gaussian_rows_ae_linearIndependent k hk] with X hX; exact he X hX)

end

lemma holder_bounded_kernel {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {g f : Ω → ℝ≥0∞} (hg : Measurable g) (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1)
    {p : ℝ} (hp : 1 < p) {D : ℝ≥0∞} (hD : (∫⁻ x, g x^p ∂μ) ≤ D) :
    (∫⁻ x, g x*f x ∂μ) ≤ D^(1/p) * (∫⁻ x, f x ∂μ)^(1-1/p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hg.aemeasurable hf.aemeasurable
  have he : 1 / Real.conjExponent p = 1-1/p := by
    simpa only [one_div] using hpq.one_sub_inv.symm
  have hpow : ∀ x, f x ^ Real.conjExponent p ≤ f x := by
    intro x
    simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_ge (hf1 x) hpq.symm.lt.le
  simp only [Pi.mul_apply, he] at hh
  exact hh.trans (mul_le_mul' (ENNReal.rpow_le_rpow hD (by positivity))
    (ENNReal.rpow_le_rpow (lintegral_mono hpow) (by rw [← he]; exact one_div_nonneg.mpr hpq.symm.pos.le)))

lemma cap_exp_root (C d : ℝ) {p : ℝ} (hp : 0 < p) :
    (ENNReal.ofReal (Real.exp (C*d*p))) ^ (1/p) = ENNReal.ofReal (Real.exp (C*d)) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 2
  field_simp

lemma cap_dual_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      ∀ (c : EuclideanSpace ℝ (Fin d)), ‖c‖ = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∀ D : CapDictionary c r α,
      ∀ K : (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      Measurable K → (∀ z, K z ≤ 1) →
      ∀ h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable h →
      (∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) →
      (∫⁻ s, h s*capKernelValue K s ∂capMeasure c r) ≤
        ENNReal.ofReal (Real.exp (C*d)) * (capReference K c r)^(1-1/(k:ℝ)) := by
  obtain ⟨C,hC,hmoment⟩ := normalized_unitBall_moment 2048 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro d hd k α c hc r hr hr2 D K hK hK1 h hh hdual
  let : NeZero d := ⟨by omega⟩
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkd : k ≤ d := by dsimp [k]; omega
  have hkd2 : k+2 ≤ d := by dsimp [k]; omega
  have hdR : (32:ℝ) ≤ d := by exact_mod_cast hd
  have hα : 2*α = (Module.finrank ℝ (EuclideanSpace ℝ (Fin d))-1:ℕ) := by
    simp only [finrank_euclideanSpace_fin, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    dsimp [α]
    ring
  let u : Fin k → EuclideanSpace ℝ (Fin d) := (EuclideanSpace.basisFun (Fin d) ℝ) ∘ Fin.castLE hkd
  have hu : Orthonormal ℝ u := (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp _ (Fin.castLE_injective hkd)
  let ν := capTestMeasure h c r
  have hmass := capTestMeasure_mass hr D hdual
  let : IsFiniteMeasure ν := capTestMeasure_finite hr D hdual
  have hs := capTestMeasure_support h c hr
  have hball := capTest_allBall hc hr hr2 (by dsimp [α]; linarith : 0 ≤ α) hα D hdual
  simp only [finrank_euclideanSpace_fin] at hball
  have hac : ∀ X, ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k)) :=
    fun X => capTest_frame_ac h c hr (by simpa using hkd2) _ (polarRows_orthonormal hu X)
  have hm := (hmoment d hd ν u hmass hs hball hu (Filter.Eventually.of_forall hac)).2.2.2
  have hp : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  let γ := Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d)))
  let F : (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞ :=
    fun z => K (z.1,capReferenceLabel c r z.1 z.2)
  have hF : Measurable F := hK.comp (measurable_fst.prodMk (measurable_capReferenceLabel c r))
  have hnorm : (∫⁻ z, normalizedDensity ν k u z ^ (k:ℝ) ∂γ.prod (unitBallLaw k)) ≤
      ENNReal.ofReal (Real.exp (C*d*k)) := by
    rw [lintegral_prod _ (by fun_prop)]
    simpa only [ENNReal.rpow_natCast] using hm
  have hb := holder_bounded_kernel (γ.prod (unitBallLaw k))
    (measurable_normalizedDensity ν k u) hF (fun z => hK1 _) hp hnorm
  rw [cap_exp_root C d (by positivity : (0:ℝ)<k), lintegral_prod _ (by fun_prop),
    lintegral_prod _ (by fun_prop)] at hb
  have hparent : (∫⁻ s, h s ∂capMeasure c r) ≤ 1 := by
    simpa only [D.parent_center,D.parent_radius,div_self hr.ne',Real.one_rpow,ENNReal.ofReal_one] using hdual D.parent
  let : IsFiniteMeasure ((capMeasure c r).withDensity h) :=
    isFiniteMeasure_withDensity (ne_of_lt (hparent.trans_lt (by simp)))
  rw [cap_kernel_test_identity (by simpa using hkd) hK h hh c hr hu hac]
  exact hb

end ProjectionMoments

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped Topology BigOperators Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace ProjectionMoments
namespace Weighted

section
variable {ι : Type*}

def budget (b : ι → ℝ) (K : ℝ) : Set (ι → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ ∀ s : Finset ι, ∑ i ∈ s, a i*b i ≤ K}

lemma budget_closed (b : ι → ℝ) (K : ℝ) : IsClosed (budget b K) := by
  have he : budget b K = (⋂ i, {a | 0 ≤ a i}) ∩
      (⋂ s : Finset ι, {a | ∑ i ∈ s, a i*b i ≤ K}) := by ext a; simp [budget]
  rw [he]
  exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
    (isClosed_iInter (fun s => isClosed_le (by fun_prop) continuous_const))

lemma budget_mem_single {b : ι → ℝ} {K : ℝ} {a : ι → ℝ} (ha : a ∈ budget b K) (i : ι) :
    a i * b i ≤ K := by
  classical
  simpa using ha.2 {i}

lemma budget_compact {b : ι → ℝ} (hb : ∀ i, 0 < b i) (K : ℝ) : IsCompact (budget b K) := by
  apply (isCompact_pi_infinite (fun i => isCompact_Icc (a := (0:ℝ)) (b := K/b i))).of_isClosed_subset
    (budget_closed b K)
  intro a ha
  exact fun i => ⟨ha.1 i, (le_div_iff₀ (hb i)).mpr (budget_mem_single ha i)⟩

lemma budget_convex (b : ι → ℝ) (K : ℝ) : Convex ℝ (budget b K) := by
  intro a ha a' ha' t u ht hu htu
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ht (ha.1 i)) (mul_nonneg hu (ha'.1 i))
  · intro s
    have he : (∑ i ∈ s, (t • a + u • a') i * b i) =
        t*(∑ i ∈ s, a i*b i) + u*(∑ i ∈ s, a' i*b i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        mul_assoc, ← Finset.mul_sum]
    rw [he]
    calc
      _ ≤ t*K+u*K := add_le_add (mul_le_mul_of_nonneg_left (ha.2 s) ht)
        (mul_le_mul_of_nonneg_left (ha'.2 s) hu)
      _ = K := by rw [← add_mul, htu, one_mul]

lemma cost_summable {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) {K : ℝ} {a : ι → ℝ}
    (ha : a ∈ budget b K) : Summable (fun i => a i*b i) :=
  summable_of_sum_le (fun i => mul_nonneg (ha.1 i) (hb i)) ha.2

lemma cost_le {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) {K : ℝ} {a : ι → ℝ}
    (ha : a ∈ budget b K) : (∑' i, a i*b i) ≤ K :=
  (cost_summable hb ha).tsum_le_of_sum_le ha.2

lemma eval_summable {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i) {K : ℝ} {a v : ι → ℝ}
    (ha : a ∈ budget b K) (hv : ∀ i, v i ∈ Icc (0:ℝ) 1) : Summable (fun i => a i*v i) := by
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (ha.1 i) (hv i).1)
    (fun i => mul_le_mul_of_nonneg_left ((hv i).2.trans (hb i)) (ha.1 i))
    (cost_summable (fun i => (zero_le_one.trans (hb i))) ha)

lemma eval_le {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i) {K : ℝ} {a v : ι → ℝ}
    (ha : a ∈ budget b K) (hv : ∀ i, v i ∈ Icc (0:ℝ) 1) : (∑' i, a i*v i) ≤ K := by
  exact ((eval_summable hb ha hv).tsum_le_tsum
    (fun i => mul_le_mul_of_nonneg_left ((hv i).2.trans (hb i)) (ha.1 i))
    (cost_summable (fun i => (zero_le_one.trans (hb i))) ha)).trans (cost_le (fun i => (zero_le_one.trans (hb i))) ha)

lemma eval_tail {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i) {K : ℝ} {a v : ι → ℝ}
    (ha : a ∈ budget b K) (hv : ∀ i, v i ∈ Icc (0:ℝ) 1)
    (s : Finset ι) {R : ℝ} (hR : 0 < R) (hs : ∀ i ∉ s, R ≤ b i) :
    0 ≤ (∑' i, a i*v i) - ∑ i ∈ s, a i*v i ∧
      (∑' i, a i*v i) - ∑ i ∈ s, a i*v i ≤ K/R := by
  classical
  have hc := cost_summable (fun i => zero_le_one.trans (hb i)) ha
  have he := eval_summable hb ha hv
  have hid := he.sum_add_tsum_subtype_compl s
  have hnon : 0 ≤ ∑' i : {i // i ∉ s}, a i*v i :=
    tsum_nonneg (fun i => mul_nonneg (ha.1 i) (hv i).1)
  have hcost : (∑' i : {i // i ∉ s}, a i*b i) ≤ K := by
    have heq := hc.sum_add_tsum_subtype_compl s
    have hsum : 0 ≤ ∑ i ∈ s, a i*b i :=
      Finset.sum_nonneg (fun i hi => mul_nonneg (ha.1 i) (zero_le_one.trans (hb i)))
    have htot := cost_le (fun i => zero_le_one.trans (hb i)) ha
    linarith
  have hbound : (∑' i : {i // i ∉ s}, a i*v i) ≤ K/R := by
    calc
      _ ≤ ∑' i : {i // i ∉ s}, (a i*b i)/R := by
        apply (he.subtype _).tsum_le_tsum _ ((hc.subtype _).div_const R)
        intro i
        apply (le_div_iff₀ hR).mpr
        calc
          a i*v i*R ≤ a i*1*R :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hv i).2 (ha.1 i)) hR.le
          _ ≤ a i*b i := by simpa using mul_le_mul_of_nonneg_left (hs i i.2) (ha.1 i)
      _ = (∑' i : {i // i ∉ s}, a i*b i)/R := tsum_div_const
      _ ≤ K/R := div_le_div_of_nonneg_right hcost hR.le
  constructor <;> linarith

lemma eval_continuousOn {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i)
    (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite) {K : ℝ} (hK : 0 ≤ K)
    {v : ι → ℝ} (hv : ∀ i, v i ∈ Icc (0:ℝ) 1) :
    ContinuousOn (fun a : ι → ℝ => ∑' i, a i*v i) (budget b K) := by
  classical
  have hconv : TendstoUniformlyOn (fun s : Finset ι => fun a : ι → ℝ => ∑ i ∈ s, a i*v i)
      (fun a => ∑' i, a i*v i) atTop (budget b K) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    let R := (K+1)/ε
    have hR : 0 < R := by dsimp [R]; positivity
    let s := (hproper R).toFinset
    filter_upwards [eventually_ge_atTop s] with t ht
    intro a ha
    have hsmall : ∀ i ∉ t, R ≤ b i := by
      intro i hi
      apply le_of_lt
      by_contra! hh
      exact hi (ht (by simpa [s] using hh))
    have hh := eval_tail hb ha hv t hR hsmall
    rw [Real.dist_eq, abs_of_nonneg hh.1]
    apply hh.2.trans_lt
    apply (div_lt_iff₀ hR).mpr
    have he : ε*R = K+1 := by dsimp [R]; field_simp
    linarith
  apply hconv.continuousOn
  exact Filter.Eventually.frequently (Filter.Eventually.of_forall (fun _ => (by fun_prop : Continuous _).continuousOn))

lemma zero_mem_budget {b : ι → ℝ} {K : ℝ} (hK : 0 ≤ K) : (0 : ι → ℝ) ∈ budget b K := by
  constructor
  · simp
  · simpa using (fun _ : Finset ι => hK)

lemma single_mem_budget [DecidableEq ι] {b : ι → ℝ} (hb : ∀ i, 0 < b i) {K : ℝ} (hK : 0 ≤ K) (i : ι) :
    (Pi.single i (K/b i) : ι → ℝ) ∈ budget b K := by
  classical
  constructor
  · intro j
    simp only [Pi.single_apply]
    split_ifs
    · exact div_nonneg hK (hb i).le
    · exact le_rfl
  · intro s
    have he : (fun j => (Pi.single i (K/b i) : ι → ℝ) j * b j) = (Pi.single i K : ι → ℝ) := by
      ext j
      by_cases hj : j = i
      · subst j; simp [div_mul_cancel₀ K (hb i).ne']
      · simp [hj]
    rw [he]
    simp only [Pi.single_apply]
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact hK

lemma eval_single [DecidableEq ι] {b : ι → ℝ} (K : ℝ) (i : ι) (v : ι → ℝ) :
    (∑' j, (Pi.single i (K/b i) : ι → ℝ) j * v j) = (K/b i)*v i := by
  classical
  rw [tsum_eq_single i (by intro j hj; simp [hj])]
  simp

lemma eval_smul_add {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i) {K : ℝ} {a a' v : ι → ℝ}
    (ha : a ∈ budget b K) (ha' : a' ∈ budget b K) (hv : ∀ i, v i ∈ Icc (0:ℝ) 1)
    (t u : ℝ) :
    (∑' i, (t • a + u • a') i * v i) = t*(∑' i, a i*v i)+u*(∑' i, a' i*v i) := by
  have he : (fun i => (t • a + u • a') i * v i) =
      fun i => t*(a i*v i)+u*(a' i*v i) := by ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [he, ((eval_summable hb ha hv).mul_left t).tsum_add ((eval_summable hb ha' hv).mul_left u),
    tsum_mul_left, tsum_mul_left]

lemma finite_dual_domination {J : Type*} [Fintype J] {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 < K) (v : J → ι → ℝ) (hv : ∀ j i, v j i ∈ Icc (0:ℝ) 1)
    (y : J → ℝ)
    (hdual : ∀ c : J → ℝ, (∀ j, 0 ≤ c j) →
      (∀ i, ∑ j, c j*v j i ≤ b i) → ∑ j, c j*y j ≤ K) :
    ∃ a ∈ budget b K, ∀ j, y j ≤ ∑' i, a i*v j i := by
  classical
  let F : (ι → ℝ) → (J → ℝ) := fun a j => ∑' i, a i*v j i
  let C := F '' budget b K
  let D := C + Set.Iic (0 : J → ℝ)
  have hCc : IsCompact C := (budget_compact (fun i => zero_lt_one.trans_le (hb i)) K).image_of_continuousOn
    (continuousOn_pi.mpr (fun j => eval_continuousOn hb hproper hK.le (hv j)))
  have hCv : Convex ℝ C := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨a',ha',rfl⟩ t u ht hu htu
    refine ⟨t • a + u • a', budget_convex b K ha ha' ht hu htu, ?_⟩
    ext j
    exact eval_smul_add hb ha ha' (hv j) t u
  have hDc : IsClosed D := isClosed_Iic.add_left_of_isCompact hCc
  have hDv : Convex ℝ D := hCv.add (convex_Iic (0 : J → ℝ))
  have h00 : (0 : J → ℝ) ∈ C := ⟨0,zero_mem_budget hK.le,by ext j; simp [F]⟩
  have hneg : ∀ w : J → ℝ, w ≤ 0 → w ∈ D := by
    intro w hw
    exact ⟨0,h00,w,hw,zero_add _⟩
  have hymem : y ∈ D := by
    by_contra hy
    obtain ⟨f,U,hf,hUy⟩ := geometric_hahn_banach_closed_point hDv hDc hy
    have hU : 0 < U := by simpa using hf 0 (hneg 0 le_rfl)
    let c : J → ℝ := fun j => f (Pi.single j 1)
    have hfe (x : J → ℝ) : f x = ∑ j, c j*x j := by
      have he : x = ∑ j, x j • Pi.single j (1:ℝ) := by
        ext i
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [he, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]
      change x j * c j = c j * x j
      ring
    have hc : ∀ j, 0 ≤ c j := by
      intro j
      by_contra! hj
      let t := (U+1)/(-c j)
      have ht : 0 < t := div_pos (by linarith) (neg_pos.mpr hj)
      have hw : -t • Pi.single j (1:ℝ) ≤ (0 : J → ℝ) := by
        intro i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.single_apply]
        split_ifs <;> nlinarith
      have hh := hf _ (hneg _ hw)
      rw [map_smul] at hh
      change -t*c j < U at hh
      have he : -t*c j = U+1 := by dsimp [t]; field_simp [hj.ne]
      linarith
    have hsingle (i : ι) : (K/b i)*(∑ j, c j*v j i) < U := by
      have ha := single_mem_budget (fun i => zero_lt_one.trans_le (hb i)) hK.le i
      have hmem : F ((Pi.single i (K/b i) : ι → ℝ)) ∈ D :=
        ⟨F ((Pi.single i (K/b i) : ι → ℝ)),⟨_,ha,rfl⟩,0,by simp,add_zero _⟩
      have hh := hf _ hmem
      rw [hfe] at hh
      simp only [F, eval_single] at hh
      convert hh using 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have htest : ∀ i, ∑ j, (K/U*c j)*v j i ≤ b i := by
      intro i
      have hh := hsingle i
      rw [div_mul_eq_mul_div, div_lt_iff₀ (zero_lt_one.trans_le (hb i))] at hh
      have he : (∑ j, (K/U*c j)*v j i) = (K/U)*(∑ j, c j*v j i) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
      rw [he, div_mul_eq_mul_div, div_le_iff₀ hU]
      nlinarith
    have hres := hdual (fun j => K/U*c j) (fun j => mul_nonneg (div_nonneg hK.le hU.le) (hc j)) htest
    have he : (∑ j, K/U*c j*y j) = (K/U)*f y := by
      rw [hfe, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
    rw [he, div_mul_eq_mul_div, div_le_iff₀ hU] at hres
    nlinarith
  obtain ⟨z,⟨a,ha,rfl⟩,w,hw,he⟩ := hymem
  refine ⟨a,ha,?_⟩
  intro j
  have hj := congrFun he j
  have hh := hw j
  change F a j + w j = y j at hj
  change w j ≤ 0 at hh
  dsimp [F] at hj
  linarith

theorem dual_domination {J : Type*} {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 < K) (v : J → ι → ℝ) (hv : ∀ j i, v j i ∈ Icc (0:ℝ) 1)
    (y : J → ℝ)
    (hdual : ∀ s : Finset J, ∀ c : s → ℝ, (∀ j, 0 ≤ c j) →
      (∀ i, ∑ j, c j*v j i ≤ b i) → ∑ j, c j*y j ≤ K) :
    ∃ a ∈ budget b K, ∀ j, y j ≤ ∑' i, a i*v j i := by
  classical
  let B := budget b K
  let : CompactSpace B := isCompact_iff_compactSpace.mp (budget_compact (fun i => zero_lt_one.trans_le (hb i)) K)
  let t : J → Set B := fun j => {a | y j ≤ ∑' i, a.val i*v j i}
  have hclosed : ∀ j, IsClosed (t j) := by
    intro j
    exact isClosed_le continuous_const (eval_continuousOn hb hproper hK.le (hv j)).domRestrict
  have hfinite : ∀ s : Finset J, (Set.univ ∩ ⋂ j ∈ s, t j).Nonempty := by
    intro s
    obtain ⟨a,ha,haj⟩ := finite_dual_domination hb hproper hK
      (fun j : s => v j) (fun j => hv j) (fun j : s => y j) (hdual s)
    refine ⟨⟨a,ha⟩,Set.mem_univ _,?_⟩
    simp only [Set.mem_iInter]
    intro j hj
    exact haj ⟨j,hj⟩
  obtain ⟨a,_,ha⟩ := isCompact_univ.inter_iInter_nonempty t hclosed hfinite
  exact ⟨a.val,a.property,fun j => Set.mem_iInter.mp ha j⟩

end

variable {Ω ι : Type*} [MeasurableSpace Ω]

lemma lintegral_finite_test {J : Type*} [Fintype J] (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : J → Set Ω) (hS : ∀ j, MeasurableSet (S j)) (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) :
    (∫⁻ x, ∑ j, ENNReal.ofReal (c j) * (S j).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) =
      ENNReal.ofReal (∑ j, c j * μ.real (S j)) := by
  rw [lintegral_finsetSum (f := fun j x => ENNReal.ofReal (c j) * (S j).indicator (fun _ => (1 : ℝ≥0∞)) x) _ (fun j _ => measurable_const.mul (measurable_const.indicator (hS j)))]
  simp only [lintegral_const_mul _ (measurable_const.indicator (hS _))]
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hc j) (measureReal_nonneg))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ENNReal.ofReal_mul (hc j), measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [lintegral_indicator (hS j)]
  simp

theorem measure_domination [Countable ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)] {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 < K)
    (hdual : ∀ h : Ω → ℝ≥0∞, Measurable h →
      (∃ H : ℝ≥0, ∀ x, h x ≤ H) →
      (∀ i, ∫⁻ x, h x ∂P i ≤ ENNReal.ofReal (b i)) →
      ∫⁻ x, h x ∂μ ≤ ENNReal.ofReal K) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*b i) ∧ (∑' i, a i*b i) ≤ K ∧
      μ ≤ Measure.sum (fun i => ENNReal.ofReal (a i) • P i) := by
  classical
  let J := {S : Set Ω // MeasurableSet S}
  let v : J → ι → ℝ := fun S i => (P i).real S
  let y : J → ℝ := fun S => μ.real S
  have hv : ∀ S i, v S i ∈ Icc (0:ℝ) 1 := by
    intro S i
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  have hd : ∀ s : Finset J, ∀ c : s → ℝ, (∀ j, 0 ≤ c j) →
      (∀ i, ∑ j, c j*v j i ≤ b i) → ∑ j, c j*y j ≤ K := by
    intro s c hc hci
    let h : Ω → ℝ≥0∞ := fun x => ∑ j : s,
      ENNReal.ofReal (c j) * (j.val.val).indicator (fun _ => (1:ℝ≥0∞)) x
    have hm : Measurable h := by
      exact Finset.measurable_sum _ (fun j _ => measurable_const.mul
        (measurable_const.indicator j.val.property))
    have hbnd : ∃ H : ℝ≥0, ∀ x, h x ≤ H := by
      refine ⟨∑ j : s, (c j).toNNReal, ?_⟩
      intro x
      rw [ENNReal.ofNNReal_finsetSum]
      change (∑ j : s, ENNReal.ofReal (c j) * (j.val.val).indicator (fun _ => (1:ℝ≥0∞)) x) ≤ _
      apply Finset.sum_le_sum
      intro j hj
      by_cases hx : x ∈ j.val.val <;> simp [Set.indicator, hx, ENNReal.ofReal]
    have he (ν : Measure Ω) [IsFiniteMeasure ν] : (∫⁻ x, h x ∂ν) =
        ENNReal.ofReal (∑ j : s, c j*ν.real j.val.val) :=
      lintegral_finite_test ν (fun j : s => j.val.val) (fun j => j.val.property) c hc
    have ht := hdual h hm hbnd (fun i => by rw [he]; exact ENNReal.ofReal_le_ofReal (hci i))
    rw [he, ENNReal.ofReal_le_ofReal_iff hK.le] at ht
    exact ht
  obtain ⟨a,ha,has⟩ := dual_domination hb hproper hK v hv y hd
  refine ⟨a,ha.1,cost_summable (fun i => zero_le_one.trans (hb i)) ha,
    cost_le (fun i => zero_le_one.trans (hb i)) ha,?_⟩
  apply Measure.le_iff.mpr
  intro S hS
  have hs := has ⟨S,hS⟩
  have hsum := eval_summable hb ha (hv ⟨S,hS⟩)
  have hc : ∀ i, 0 ≤ a i*(P i).real S := fun i => mul_nonneg (ha.1 i) measureReal_nonneg
  have hh := ENNReal.ofReal_le_ofReal hs
  change ENNReal.ofReal (μ.real S) ≤ ENNReal.ofReal (∑' i, a i*(P i).real S) at hh
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_tsum_of_nonneg hc hsum] at hh
  rw [Measure.sum_apply _ hS]
  convert hh using 1
  congr 1
  funext i
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_mul (ha.1 i),
    measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem measure_domination_nonneg [Countable ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)] {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 ≤ K)
    (hdual : ∀ h : Ω → ℝ≥0∞, Measurable h →
      (∃ H : ℝ≥0, ∀ x, h x ≤ H) →
      (∀ i, ∫⁻ x, h x ∂P i ≤ ENNReal.ofReal (b i)) →
      ∫⁻ x, h x ∂μ ≤ ENNReal.ofReal K) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*b i) ∧
      (∑' i, a i*b i) ≤ K ∧ μ ≤ Measure.sum (fun i => ENNReal.ofReal (a i) • P i) := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · subst K
    have hm := hdual (fun _ => 1) measurable_const ⟨1,fun _ => le_rfl⟩
      (fun i => by simp only [lintegral_const,measure_univ,mul_one]; exact ENNReal.one_le_ofReal.mpr (hb i))
    simp only [lintegral_const,one_mul,ENNReal.ofReal_zero,nonpos_iff_eq_zero] at hm
    have hμ : μ = 0 := Measure.measure_univ_eq_zero.mp hm
    refine ⟨fun _ => 0,fun _ => le_rfl,?_,?_,?_⟩ <;> simp [hμ]
  · exact measure_domination μ P hb hproper hKpos hdual

end Weighted
end ProjectionMoments

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

theorem positive_cap_domination :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      ∀ (c : EuclideanSpace ℝ (Fin d)), ‖c‖ = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∀ K : (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      Measurable K → (∀ z, K z ≤ 1) →
      ∃ D : CapDictionary c r α, ∃ a : D.I → ℝ,
        (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*(r/D.radius i)^α) ∧
        (∑' i, a i*(r/D.radius i)^α) ≤ Real.exp (C*d)*(capReference K c r).toReal^(1-1/(k:ℝ)) ∧
        (capMeasure c r).withDensity (capKernelValue K) ≤
          Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i)) ∧
        (Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i))) Set.univ < ∞ := by
  obtain ⟨C,hC,hdual⟩ := cap_dual_estimate
  refine ⟨C,hC,?_⟩
  intro d hd k α c hc r hr hr2 K hK hK1
  let : NeZero d := ⟨by omega⟩
  have hdR : (32:ℝ) ≤ d := by exact_mod_cast hd
  have hα : 1 ≤ α := by dsimp [α]; linarith
  obtain ⟨D⟩ := exists_capDictionary hc hr hα
  let := D.countable
  let : IsProbabilityMeasure (capMeasure c r) := capMeasure_probability hc hr hr2
  let P : D.I → Measure (EuclideanSpace ℝ (Fin d)) := fun i => capMeasure (D.center i) (D.radius i)
  let (i : D.I) : IsProbabilityMeasure (P i) :=
    capMeasure_probability (D.center_norm i) (D.radius_pos i) ((D.radius_le i).trans hr2)
  let b : D.I → ℝ := fun i => (r/D.radius i)^α
  have hb : ∀ i, 1 ≤ b i := fun i => Real.one_le_rpow
    ((one_le_div (D.radius_pos i)).mpr (D.radius_le i)) (zero_le_one.trans hα)
  let μ := (capMeasure c r).withDensity (capKernelValue K)
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity (ne_of_lt
    ((lintegral_mono (capKernelValue_le_one hK1)).trans_lt (by simp)))
  let B := Real.exp (C*d)*(capReference K c r).toReal^(1-1/(k:ℝ))
  have hkR : (1:ℝ) < k := by
    have hk : 2 ≤ k := by dsimp [k]; omega
    exact_mod_cast (show 1 < k by omega)
  have hθ : 0 ≤ 1-1/(k:ℝ) := by
    have hpq := Real.HolderConjugate.conjExponent hkR
    rw [one_div,hpq.one_sub_inv]
    exact inv_nonneg.mpr hpq.symm.pos.le
  have hqtop : capReference K c r ≠ ∞ := ne_of_lt ((capReference_le_one hK1 c r).trans_lt (by simp))
  have hB : ENNReal.ofReal B = ENNReal.ofReal (Real.exp (C*d))* (capReference K c r)^(1-1/(k:ℝ)) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hθ,
      ENNReal.ofReal_toReal hqtop]
  have htest : ∀ h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable h →
      (∃ H : ℝ≥0, ∀ x, h x ≤ H) →
      (∀ i, ∫⁻ x, h x ∂P i ≤ ENNReal.ofReal (b i)) → ∫⁻ x, h x ∂μ ≤ ENNReal.ofReal B := by
    intro h hh _ hhD
    rw [hB,lintegral_withDensity_eq_lintegral_mul _ (measurable_capKernelValue hK) hh]
    simp only [Pi.mul_apply]
    simpa only [mul_comm] using hdual d hd c hc r hr hr2 D K hK hK1 h hh hhD
  obtain ⟨a,ha,has,hcost,hdom⟩ := Weighted.measure_domination_nonneg μ P hb D.proper
    (show 0 ≤ B by positivity) htest
  refine ⟨D,a,ha,has,hcost,hdom,?_⟩
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  have has' : Summable a := Summable.of_nonneg_of_le ha
    (fun i => by simpa using mul_le_mul_of_nonneg_left (hb i) (ha i)) has
  rw [← ENNReal.ofReal_tsum_of_nonneg ha has']
  exact ENNReal.ofReal_lt_top

lemma capReference_sum_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {k : ℕ} {J : Type*} [Fintype J]
    (K : J → (Fin k → E) × Label k → ℝ≥0∞) (hK : ∀ j, Measurable (K j))
    (hKsum : ∀ z, ∑ j, K j z ≤ 1) (c : E) (r : ℝ) : ∑ j, capReference (K j) c r ≤ 1 := by
  classical
  simp only [capReference]
  rw [← lintegral_finsetSum _ (fun j _ => by fun_prop)]
  calc
    _ = ∫⁻ X, ∫⁻ z, ∑ j, K j (X,capReferenceLabel c r X z) ∂unitBallLaw k
        ∂Measure.pi (fun _ => stdGaussian E) := by
      apply lintegral_congr
      intro X
      exact (lintegral_finsetSum _ (fun j _ => by fun_prop)).symm
    _ ≤ ∫⁻ X, ∫⁻ z : Label k, (1 : ℝ≥0∞) ∂unitBallLaw k
        ∂Measure.pi (fun _ : Fin k => stdGaussian E) :=
      lintegral_mono (fun X => lintegral_mono (fun z => hKsum _))
    _ = 1 := by simp

theorem positive_family_cap_domination :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      ∀ (c : EuclideanSpace ℝ (Fin d)), ‖c‖ = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 2 → ∀ N : ℕ,
      ∀ K : Fin N → (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      (∀ j, Measurable (K j)) → (∀ z, ∑ j, K j z ≤ 1) →
      (∑ j, capReference (K j) c r) ≤ 1 ∧
      ∀ j, ∃ D : CapDictionary c r α, ∃ a : D.I → ℝ,
        (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*(r/D.radius i)^α) ∧
        (∑' i, a i*(r/D.radius i)^α) ≤ Real.exp (C*d)*(capReference (K j) c r).toReal^(1-1/(k:ℝ)) ∧
        (capMeasure c r).withDensity (capKernelValue (K j)) ≤
          Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i)) ∧
        (Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i))) Set.univ < ∞ := by
  obtain ⟨C,hC,h⟩ := positive_cap_domination
  refine ⟨C,hC,?_⟩
  intro d hd k α c hc r hr hr2 N K hK hKsum
  refine ⟨capReference_sum_le_one K hK hKsum c r,?_⟩
  intro j
  apply h d hd c hc r hr hr2 (K j) (hK j)
  intro z
  exact (Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ j)).trans (hKsum z)

end ProjectionMoments

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma normalized_strong_moment {ν : Measure E} [IsFiniteMeasure ν] {a : ℝ}
    (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hs : ν.support ⊆ Metric.closedBall 0 1) (hmass : ν Set.univ ≤ 1)
    {k n : ℕ} (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℝ E)
    (hdk : Module.finrank ℝ E ≤ 32*k) (ha : a ≤ Module.finrank ℝ E)
    (hmargin : (n:ℝ)+k ≤ a) {u : Fin k → E} (hu : Orthonormal ℝ u)
    (hac : ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))) :
    (∫⁻ X, ∫⁻ y, normalizedDensity ν k u (X,y)^(n+1) ∂unitBallLaw k
      ∂Measure.pi (fun _ => stdGaussian E)) ≤
      ENNReal.ofReal ((16384:ℝ)^(Module.finrank ℝ E*(n+1))) := by
  apply (normalizedMoment_le ν hkd hu n).trans
  apply (mul_le_mul' le_rfl (frame_moment_unit hν hs hmass (by omega) ha hkd hmargin u hu hac)).trans
  simpa only [one_pow, ENNReal.ofReal_one, one_mul, max_self, mul_one] using
    normalized_cost (Module.finrank ℝ E) k n hk hkd hdk 1 one_pos

lemma rescaled_kernel_identity {μ : Measure E} [IsFiniteMeasure μ] {K a : ℝ}
    (hK : 0 < K) (c : E) {r : ℝ} (hr : 0 < r)
    (hs : μ.support ⊆ Metric.closedBall c r) {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {Q : (Fin k → E) × Label k → ℝ≥0∞} (hQ : Measurable Q)
    {u : Fin k → E} (hu : Orthonormal ℝ u)
    (hac : ∀ X, (normalizedRescale μ K a c r).map (rowMap (polarRows u X)) ≪
      (volume : Measure (Label k))) :
    (∫⁻ s, capKernelValue Q s ∂μ) =
      ENNReal.ofReal (K*r^a) * ∫⁻ X, ∫⁻ y,
        normalizedDensity (normalizedRescale μ K a c r) k u (X,y) *
          Q (X,capReferenceLabel c r X y) ∂unitBallLaw k ∂Measure.pi (fun _ => stdGaussian E) := by
  let ν := normalizedRescale μ K a c r
  let : IsFiniteMeasure ν := normalizedRescale_finite μ K a c r (by positivity)
  have hsν : ν.support ⊆ Metric.closedBall 0 1 := normalizedRescale_support K a c hr hs
  have he (X : Fin k → E) (hX : LinearIndependent ℝ X) :
      (∫⁻ s, Q (X,rowMap X s) ∂μ) =
      ENNReal.ofReal (K*r^a) * ∫⁻ y, normalizedDensity ν k u (X,y)*
        Q (X,capReferenceLabel c r X y) ∂unitBallLaw k := by
    have hid := lintegral_withDensity_eq_lintegral_mul (unitBallLaw k)
      (show Measurable (fun y => normalizedDensity ν k u (X,y)) by fun_prop)
      (show Measurable (fun y => Q (X,capReferenceLabel c r X y)) by fun_prop)
    simp only [Pi.mul_apply] at hid
    rw [← hid,normalizedDensity_unitBall ν hu hsν X (hac X),lintegral_map (by fun_prop) (by fun_prop)]
    have hrec : ENNReal.ofReal (K*r^a) • ν.map (dilate c r) = μ := normalizedRescale_recover μ K a hK c hr
    calc
      _ = ∫⁻ s, Q (X,rowMap X s) ∂(ENNReal.ofReal (K*r^a) • ν.map (dilate c r)) := by rw [hrec]
      _ = _ := by
        rw [lintegral_smul_measure,lintegral_map (by fun_prop) (measurable_dilate c r)]
        congr 1
        apply lintegral_congr
        intro s
        rw [capReferenceLabel, ← polar_label_identity hX u c s r]
  change (∫⁻ s, ∫⁻ X, Q (X,rowMap X s) ∂Measure.pi (fun _ => stdGaussian E) ∂μ) = _
  rw [lintegral_lintegral_swap (show AEMeasurable (fun z : E × (Fin k → E) => Q (z.2,rowMap z.2 z.1)) _ by
    apply Measurable.aemeasurable; exact hQ.comp (measurable_snd.prodMk (by simp only [rowMap_apply]; fun_prop)))]
  rw [← lintegral_const_mul _ (by fun_prop)]
  exact lintegral_congr_ae (by filter_upwards [gaussian_rows_ae_linearIndependent k hk] with X hX; exact he X hX)

lemma localized_fractional_kernel_bound {μ : Measure E} [IsFiniteMeasure μ] {K a : ℝ}
    (hlocal : AllBallMass μ K a) (hK : 0 ≤ K)
    (c : E) {r : ℝ} (hr : 0 < r) (hs : μ.support ⊆ Metric.closedBall c r)
    {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hkd : k ≤ Module.finrank ℝ E)
    (hdk : Module.finrank ℝ E ≤ 32*k) (ha : a ≤ Module.finrank ℝ E)
    (hmargin : (n:ℝ)+k ≤ a)
    {Q : (Fin k → E) × Label k → ℝ≥0∞} (hQ : Measurable Q) (hQ1 : ∀ z, Q z ≤ 1)
    {u : Fin k → E} (hu : Orthonormal ℝ u)
    (hac : ∀ A, Orthonormal ℝ A → μ.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))) :
    (∫⁻ s, capKernelValue Q s ∂μ) ≤
      ENNReal.ofReal ((16384:ℝ)^Module.finrank ℝ E) * ENNReal.ofReal (K*r^a) *
        (capReference Q c r)^(1-1/((n:ℝ)+1)) := by
  rcases eq_or_lt_of_le hK with hK | hK
  · have hz := measure_eq_zero_of_allBall_zero (hK ▸ hlocal) c hr hs
    subst μ
    simp
  let ν := normalizedRescale μ K a c r
  let : IsFiniteMeasure ν := normalizedRescale_finite μ K a c r (by positivity)
  have hsν : ν.support ⊆ Metric.closedBall 0 1 := normalizedRescale_support K a c hr hs
  have hmass : ν Set.univ ≤ 1 := normalizedRescale_mass hlocal hK c hr hs
  have hacν (A : Fin k → E) (hA : Orthonormal ℝ A) :
      ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by
    change (normalizedRescale μ K a c r).map (coordinateMap A) ≪ _
    rw [normalizedRescale, Measure.map_smul]
    exact Measure.smul_absolutelyContinuous.trans (rescaled_projection_ac A c hr (hac A hA))
  have hacX (X : Fin k → E) : ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k)) :=
    (rowMap_ac_iff _).mpr (hacν _ (polarRows_orthonormal hu X))
  have hm := normalized_strong_moment (normalizedRescale_local hlocal hK c hr) hsν hmass hk hkd hdk ha hmargin hu
    (polar_ac_to_frame ν hkd hu (Filter.Eventually.of_forall hacX))
  let γ := Measure.pi (fun _ : Fin k => stdGaussian E)
  let F : (Fin k → E) × Label k → ℝ≥0∞ := fun z => Q (z.1,capReferenceLabel c r z.1 z.2)
  have hF : Measurable F := hQ.comp (measurable_fst.prodMk (measurable_capReferenceLabel c r))
  have hp : (1:ℝ) < (n:ℝ)+1 := by exact_mod_cast (show 1 < n+1 by omega)
  have hnorm : (∫⁻ z, normalizedDensity ν k u z ^ ((n:ℝ)+1) ∂γ.prod (unitBallLaw k)) ≤
      ENNReal.ofReal ((16384:ℝ)^Module.finrank ℝ E)^(n+1) := by
    rw [lintegral_prod _ (by fun_prop)]
    simpa only [←Nat.cast_add_one,ENNReal.rpow_natCast,pow_mul,ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 16384),
      ENNReal.ofReal_pow (by positivity : 0 ≤ (16384:ℝ)^Module.finrank ℝ E)] using hm
  have hb := holder_bounded_kernel (γ.prod (unitBallLaw k))
    (measurable_normalizedDensity ν k u) hF (fun z => hQ1 _) hp hnorm
  have hroot : (ENNReal.ofReal ((16384:ℝ)^Module.finrank ℝ E)^(n+1))^(1/((n:ℝ)+1)) ≤
      ENNReal.ofReal ((16384:ℝ)^Module.finrank ℝ E) := by
    simpa only [Nat.cast_add,Nat.cast_one] using ennreal_root_bound (q := n+1) (by omega)
      (by positivity : 0 ≤ (16384:ℝ)^Module.finrank ℝ E) le_rfl
  have hb' := hb.trans (mul_le_mul' hroot le_rfl)
  rw [lintegral_prod _ (by fun_prop),lintegral_prod _ (by fun_prop)] at hb'
  rw [rescaled_kernel_identity hK c hr hs hkd hQ hu hacX]
  apply (mul_le_mul' le_rfl hb').trans_eq
  dsimp only [F,γ,capReference]
  ring

lemma fractionalBlock_mass_identity {J : Type*} [Fintype J] {k : ℕ}
    (Q : J → (Fin k → E) × Label k → ℝ≥0∞) (hQ : ∀ j, Measurable (Q j))
    (f : J → E → ℝ≥0∞) (hf : ∀ j, Measurable (f j))
    (μ : Measure E) [SFinite μ] {S : Set E} (hS : MeasurableSet S) :
    (∫⁻ s in S, fractionalBlock Q f s ∂μ) =
      ∑ j, ∫⁻ s, capKernelValue (Q j) s ∂(μ.withDensity (f j)).restrict S := by
  have he (s : E) : fractionalBlock Q f s = ∑ j, f j s * capKernelValue (Q j) s := by
    unfold fractionalBlock capKernelValue
    rw [lintegral_finsetSum _ (fun j _ => by simp only [rowMap_apply]; fun_prop)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [lintegral_mul_const _ (by simp only [rowMap_apply]; fun_prop)]
    exact mul_comm _ _
  simp_rw [he]
  rw [lintegral_finsetSum _ (fun j _ => show Measurable (fun s => f j s * capKernelValue (Q j) s) from
    (hf j).mul (measurable_capKernelValue (hQ j)))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [restrict_withDensity hS]
  exact (lintegral_withDensity_eq_lintegral_mul _ (hf j) (measurable_capKernelValue (hQ j))).symm

theorem one_block_all_radii :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/4
      let β : ℝ := (d:ℝ)-1-k
      ∀ N : ℕ, ∀ f : Fin N → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      (∀ j, Measurable (f j)) → (∀ j s, f j s ≤ 1) →
      ∀ K : ℝ, 0 ≤ K →
      (∀ j, AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity (f j)) K β) →
      ∀ Q : Fin N → (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      (∀ j, Measurable (Q j)) → (∀ z, ∑ j, Q j z ≤ 1) →
      AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity (fractionalBlock Q f))
        (C^d*(N:ℝ)^(1/(k:ℝ))*K) β := by
  refine ⟨16384,by norm_num,?_⟩
  intro d hd k β N f hf hf1 K hK hlocal Q hQ hQsum z R hR
  let : NeZero d := ⟨by omega⟩
  have hk : 4 ≤ k := by dsimp [k]; omega
  have hkd : k ≤ d := by dsimp [k]; omega
  have hdk : d ≤ 32*k := by dsimp [k]; omega
  have hk2 : k+2 ≤ d := by dsimp [k]; omega
  have hkn : k-1+1=k := by omega
  have hknR : ((k-1:ℕ):ℝ)+1=k := by exact_mod_cast hkn
  have hβ : β ≤ d := by dsimp [β]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hmargin : ((k-1:ℕ):ℝ)+k ≤ β := by
    have hn : 3*k ≤ d := by dsimp [k]; omega
    have hnR : 3*(k:ℝ) ≤ d := by exact_mod_cast hn
    dsimp [β]; linarith
  let u : Fin k → EuclideanSpace ℝ (Fin d) := (EuclideanSpace.basisFun (Fin d) ℝ) ∘ Fin.castLE hkd
  have hu : Orthonormal ℝ u := (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp _ (Fin.castLE_injective hkd)
  let μ (j : Fin N) := sphereWeightedRestriction (f j) (Metric.closedBall z R)
  let (j : Fin N) : IsFiniteMeasure (μ j) := sphereWeightedRestriction_finite (hf1 j) _
  have hs (j : Fin N) : (μ j).support ⊆ Metric.closedBall z R := sphereWeightedRestriction_support Subset.rfl
  have hl (j : Fin N) : AllBallMass (μ j) K β := fun c r hr =>
    (Measure.restrict_le_self _).trans (hlocal j c r hr)
  have hac (j : Fin N) (A : Fin k → EuclideanSpace ℝ (Fin d)) (hA : Orthonormal ℝ A) :
      (μ j).map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) :=
    ((Measure.absolutelyContinuous_of_le (sphereWeightedRestriction_le (hf1 j) _)).map
      (by fun_prop)).trans (sphere_frame_ac (by simpa using hk2) hA)
  have hQ1 (j : Fin N) (x) : Q j x ≤ 1 :=
    (Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ j)).trans (hQsum x)
  have hb' (j : Fin N) : (∫⁻ s, capKernelValue (Q j) s ∂μ j) ≤
      ENNReal.ofReal ((16384:ℝ)^d)*ENNReal.ofReal (K*R^β)*(capReference (Q j) z R)^(1-1/(k:ℝ)) := by
    have hh := localized_fractional_kernel_bound (hl j) hK z hR (hs j) (n := k-1)
      (by omega) (by omega) (by simpa using hkd) (by simpa using hdk) (by simpa using hβ)
      hmargin (hQ j) (hQ1 j) hu (hac j)
    simpa only [finrank_euclideanSpace_fin,hknR] using hh
  have hp : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hθ : 0 ≤ 1-1/(k:ℝ) := by
    have hh : 1/(k:ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hp.le
    linarith
  rw [withDensity_apply _ Metric.isClosed_closedBall.measurableSet,
    fractionalBlock_mass_identity Q hQ f hf _ Metric.isClosed_closedBall.measurableSet]
  calc
    _ ≤ ∑ j, ENNReal.ofReal ((16384:ℝ)^d)*ENNReal.ofReal (K*R^β)*(capReference (Q j) z R)^(1-1/(k:ℝ)) :=
      Finset.sum_le_sum (fun j _ => hb' j)
    _ = ENNReal.ofReal ((16384:ℝ)^d)*ENNReal.ofReal (K*R^β)*
        ∑ j, (capReference (Q j) z R)^(1-1/(k:ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal ((16384:ℝ)^d)*ENNReal.ofReal (K*R^β)*
        ((N:ℝ≥0∞)^(1/(k:ℝ))) := by
      apply mul_le_mul' le_rfl
      apply (NoiselessRegression.finite_rpow_holder (fun j => capReference (Q j) z R) hp).trans
      have hsum := capReference_sum_le_one Q hQ hQsum z R
      simpa only [Fintype.card_fin,ENNReal.one_rpow,mul_one] using
        mul_le_mul' (le_rfl : (N:ℝ≥0∞)^(1/(k:ℝ)) ≤ _) (ENNReal.rpow_le_rpow hsum hθ)
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (16384:ℝ)^d*(N:ℝ)^(1/(k:ℝ))*K),
        ENNReal.ofReal_mul (by positivity : 0 ≤ (16384:ℝ)^d*(N:ℝ)^(1/(k:ℝ))),
        ENNReal.ofReal_mul (by positivity : 0 ≤ (16384:ℝ)^d),ENNReal.ofReal_mul hK,
        ← ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ N) (by positivity : (0:ℝ) ≤ 1/k),
        ENNReal.ofReal_natCast]
      ring

end ProjectionMoments

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

lemma continuation_mass_bound_ceil [Nonempty J] (μ : Measure E) [IsFiniteMeasure μ]
    {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (μ.withDensity (w n j)) a C)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    PolynomialMass (μ.withDensity (continuation δ w n k j)) a
      (C * streamFactor (E := E) (J := J) q ^ ((k+q-1)/q)) := by
  have hden : ((q-1 : ℕ) : ℝ)+1 = (q : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    ring
  have hq0 : 0 < q := by omega
  have hK1 := one_le_streamFactor (E := E) (J := J) hq0
  have hK0 : streamFactor (E := E) (J := J) q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK1)
  have hKt := streamFactor_ne_top (E := E) (J := J) q
  induction k using Nat.strong_induction_on generalizing n j with
  | h k ih =>
    by_cases hk0 : k = 0
    · subst k
      simpa only [Nat.zero_add,Nat.div_eq_of_lt (by omega : q-1 < q),pow_zero,mul_one,continuation] using hlocal n j
    by_cases hk : q ≤ k
    · have hki : k-q < k := by omega
      have hC1 : C * streamFactor (E := E) (J := J) q ^ ((k-q+q-1)/q) ≠ 0 :=
        mul_ne_zero hC (pow_ne_zero _ hK0)
      have hC1t : C * streamFactor (E := E) (J := J) q ^ ((k-q+q-1)/q) ≠ ∞ :=
        ENNReal.mul_ne_top hCt (ENNReal.pow_ne_top hKt)
      have hb := blockValue_mass_bound μ
        (fun b => measurable_continuation hδ hw (n+q) (k-q) b)
        (fun b s => continuation_le_one hw1 (n+q) (k-q) b s)
        (fun b => ih (k-q) hki (n+q) b) hC1 hC1t hd ha
        (by omega : q ≤ Module.finrank ℝ E) (by omega : 1 ≤ q-1)
        (by omega : q-1+q ≤ a) (measurable_streamRoute hδ n q j)
      have he : continuation δ w n k j =
          blockValue (fun b => continuation δ w (n+q) (k-q) b) (streamRoute δ n q j) := by
        funext s
        simpa [Nat.add_sub_of_le hk] using continuation_unroll hδ n q (k-q) j s
      rw [he]
      have hdiv : (k+q-1)/q = (k-q+q-1)/q+1 := by
        have he : k+q-1 = q+(k-q+q-1) := by omega
        rw [he,Nat.add_div_left _ hq0]
      convert hb using 1
      rw [hden, ← streamFactor, hdiv, pow_succ]
      ring
    · have hkm : k ≤ q := by omega
      have hb := blockValue_mass_bound μ
        (fun b => hw (n+k) b) (fun b s => hw1 (n+k) b s) (hlocal (n+k)) hC hCt hd ha
        (by omega : k ≤ Module.finrank ℝ E) (by omega : 1 ≤ q-1)
        (by omega : q-1+k ≤ a) (measurable_streamRoute hδ n k j)
      have he : continuation δ w n k j = blockValue (w (n+k)) (streamRoute δ n k j) := by
        funext s
        simpa [continuation] using continuation_unroll hδ n k 0 j s
      rw [he]
      convert hb using 1
      have hdiv : (k+q-1)/q = 1 := by
        have he : k+q-1 = q+(k-1) := by omega
        rw [he,Nat.add_div_left _ hq0,Nat.div_eq_of_lt (by omega : k-1 < q)]
      rw [hden, ← streamFactor,hdiv,pow_one]
      exact mul_comm _ _

variable [Nontrivial E] [Nonempty J]

lemma continuation_cap_integral_bound_ceil {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : ℕ → J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    (∫⁻ s, continuation δ (fun n j => capWeight (y n j) ε) n k j s ∂ambientSphereLaw) ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ ((k+q-1)/q) := by
  apply ambient_mass_bound
  apply continuation_mass_bound_ceil _ hδ (fun n j => measurable_capWeight _ _)
    (fun n j s => capWeight_le_one _ _ _)
    (mul_ne_zero (by positivity) (by positivity)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (fun n j => capWeight_mass (y n j) hε a ha)
    (Module.finrank_pos (R := ℝ) (M := E)) (by omega) hq hqa

lemma route_cap_bound_ceil {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (k : ℕ) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin k => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ ((k+q-1)/q) := by
  let w : ℕ → J → E → ℝ≥0∞ := fun _ j => capWeight (y j) ε
  have hV := measurable_continuation (w := w) hδ (fun _ j => measurable_capWeight (y j) ε) 0 k j
  have he (s : E) : continuation δ w 0 k j s =
      ∫⁻ A : Fin k → E, capWeight (y (streamRoute δ 0 k j (A,fun i => ⟪s,A i⟫))) ε s
        ∂Measure.pi (fun _ => stdGaussian E) := by
    simpa [w, blockValue, continuation] using continuation_unroll (w := w) hδ 0 k 0 j s
  let S : Set ((Metric.sphere (0 : E) 1) × (Fin k → E)) :=
    {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε}
  have hS : MeasurableSet S := by
    apply measurableSet_le _ measurable_const
    exact measurable_subtype_coe.comp measurable_fst |>.dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  change ((sphereLaw (E := E)).prod _) S ≤ _
  rw [← one_mul (((sphereLaw (E := E)).prod _) S), ← lintegral_indicator_const hS 1,
    lintegral_prod _ (measurable_const.indicator hS).aemeasurable]
  have hf : ∀ s : Metric.sphere (0 : E) 1,
      (∫⁻ A, S.indicator (fun _ => (1 : ℝ≥0∞)) (s,A) ∂Measure.pi (fun _ => stdGaussian E)) =
        continuation δ w 0 k j s.val := by
    intro s
    rw [he]
    apply lintegral_congr
    intro A
    classical
    change (if dist s.val (y (streamRoute δ 0 k j (A,fun i => ⟪s.val,A i⟫))) ≤ ε then 1 else 0) = _
    unfold capWeight
    rw [Set.indicator_apply]
    rfl
  simp_rw [hf]
  rw [← lintegral_map hV measurable_subtype_coe]
  exact continuation_cap_integral_bound_ceil hδ (fun _ => y) hε ha hq hqa 0 k j

end

namespace Learner
variable {d M T : ℕ} {Ω : Type u}

instance taggedMeasurableSingletonClass : MeasurableSingletonClass (TaggedState M T) :=
  ⟨fun _ => trivial⟩

lemma card_taggedState (M T : ℕ) : Fintype.card (TaggedState M T) = (T+2)*2^M := by
  simp only [TaggedState, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, State]
  ring

def decodeTagged : TaggedState M T → RunStatus M
  | .inl j => .inl j
  | .inr (t,j) => .inr (t.val,j)

def taggedStep (τ : ℕ → State M → (Vector d × ℝ) → Bool × State M)
    (t : ℕ) : TaggedState M T → (Vector d × ℝ) → TaggedState M T
  | .inr done, _ => .inr done
  | .inl j, obs =>
    if ht : t ≤ T then
      let a := τ t j obs
      if a.1 then .inr (⟨t,by omega⟩,a.2) else .inl a.2
    else .inl j

lemma measurable_taggedStep {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (hτ : ∀ t j, Measurable (τ t j)) (t : ℕ) (j : TaggedState M T) :
    Measurable (taggedStep (T := T) τ t j) := by
  classical
  cases j with
  | inr done => exact measurable_const
  | inl j =>
    unfold taggedStep
    split_ifs with ht
    · exact (measurable_of_finite (fun a : Bool × State M =>
        if a.1 then Sum.inr ((⟨t,by omega⟩ : Fin (T+1)),a.2) else Sum.inl a.2)).comp (hτ t j)
    · exact measurable_const

def taggedOutput (L : Learner d M T Ω) (ω : Ω) : TaggedState M T → UnitSphere d
  | .inl j => L.output T ω j
  | .inr (t,j) => L.output t ω j

lemma decode_taggedStart (a : Bool × State M) :
    decodeTagged (taggedStart (T := T) a) = if a.1 then .inr (0,a.2) else .inl a.2 := by
  simp only [taggedStart]; split_ifs <;> rfl

lemma run_eq_taggedRoute (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω) (x : Samples d T)
    {n : ℕ} (hn : n ≤ T) :
    L.run s ω x n = decodeTagged (streamRoute (taggedStep (T := T) (fun t j => L.transition t ω j))
      0 n (taggedStart (L.initialChoice ω))
      ((fun i => x (Fin.castLE hn i)),fun i => ⟪s.val,x (Fin.castLE hn i)⟫)) := by
  induction n with
  | zero => exact (decode_taggedStart _).symm
  | succ n ih =>
    rw [fin_prefix_snoc hn x, fin_prefix_snoc hn (fun i => ⟪s.val,x i⟫),streamRoute_snoc]
    rw [run,ih (by omega)]
    generalize streamRoute (taggedStep (T := T) (fun t j => L.transition t ω j)) 0 n
      (taggedStart (L.initialChoice ω))
      ((fun i => x (Fin.castLE (by omega : n ≤ T) i)),fun i => ⟪s.val,x (Fin.castLE (by omega : n ≤ T) i)⟫) = j
    cases j with
    | inr done => rfl
    | inl j =>
      simp only [decodeTagged, taggedStep, Nat.zero_add,dite_eq_left (by omega : n < T),
        dite_eq_left (by omega : n+1 ≤ T),real_inner_comm]
      split_ifs <;> rfl

lemma estimate_eq_taggedRoute (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω) (x : Samples d T) :
    L.estimate s ω x = L.taggedOutput ω (streamRoute
      (taggedStep (T := T) (fun t j => L.transition t ω j)) 0 T (taggedStart (L.initialChoice ω))
      (x,fun i => ⟪s.val,x i⟫)) := by
  unfold estimate terminal
  rw [L.run_eq_taggedRoute s ω x le_rfl]
  have hi : (fun i : Fin T => x (Fin.castLE le_rfl i)) = x := by funext i; exact congrArg x (Fin.ext rfl)
  have hb : (fun i : Fin T => ⟪s.val,x (Fin.castLE le_rfl i)⟫) = (fun i => ⟪s.val,x i⟫) := by funext i; rfl
  rw [hi,hb]
  generalize streamRoute (taggedStep (T := T) (fun t j => L.transition t ω j)) 0 T
    (taggedStart (L.initialChoice ω)) (x,fun i => ⟪s.val,x i⟫) = j
  cases j with
  | inl j => rfl
  | inr done => rfl

lemma taggedStep_congr {τ τ' : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (t : ℕ) (j : TaggedState M T) (obs : Vector d × ℝ)
    (h : ∀ a, τ t a obs = τ' t a obs) :
    taggedStep τ t j obs = taggedStep τ' t j obs := by
  cases j with
  | inr done => rfl
  | inl j => simp only [taggedStep,h]

lemma frozen_success_bound_tagged (L : Learner d M T Ω) (ω : Ω) (hd : 3 ≤ d)
    (htrans : ∀ t j, AEMeasurable (L.transition t ω j) (observationReference d))
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := TaggedState M T) q ^ ((T+q-1)/q) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let τ : ℕ → State M → (Vector d × ℝ) → Bool × State M := fun t j => (htrans t j).mk _
  have hτ (t : ℕ) (j : State M) : Measurable (τ t j) := (htrans t j).measurable_mk
  let μ := (uniformSphere d).prod (sampleLaw d T)
  have hgood : ∀ᵐ z ∂μ, ∀ t j (i : Fin T),
      L.transition t ω j (z.2 i,⟪z.1.val,z.2 i⟫) = τ t j (z.2 i,⟪z.1.val,z.2 i⟫) := by
    simp only [ae_all_iff]
    intro t j i
    exact (sphere_sample_observation_quasi (by simpa using hd) i).ae (htrans t j).ae_eq_mk
  let S := {z : UnitSphere d × Samples d T | dist z.1.val
    (L.taggedOutput ω (streamRoute (taggedStep (T := T) τ) 0 T (taggedStart (L.initialChoice ω))
      (z.2,fun i => ⟪z.1.val,z.2 i⟫))).val ≤ ε}
  have hmono : {z : UnitSphere d × Samples d T | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε}
      ≤ᵐ[μ] S := by
    filter_upwards [hgood] with z hz
    intro hs
    have he := streamRoute_congr (taggedStep (T := T) (fun t j => L.transition t ω j))
      (taggedStep (T := T) τ) 0 T (taggedStart (L.initialChoice ω)) z.2
      (fun i => ⟪z.1.val,z.2 i⟫) (fun t j i => taggedStep_congr t j _ (fun a => hz t a i))
    have hc : dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε := by
      apply le_trans _ hs
      simpa only [angularError,dist_comm] using chord_le_arccos (L.estimate z.1 ω z.2) z.1
    change dist z.1.val _ ≤ ε
    rw [L.estimate_eq_taggedRoute,he] at hc
    exact hc
  apply (measure_mono_ae hmono).trans
  simpa only [S,μ,uniformSphere,sphereLaw,sampleLaw,finrank_euclideanSpace_fin] using
    route_cap_bound_ceil (measurable_taggedStep hτ) (fun j => (L.taggedOutput ω j).val)
      hε (by simpa using ha) hq hqa T (taggedStart (L.initialChoice ω))

lemma streaming_success_bound_tagged [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := TaggedState M T) q ^ ((T+q-1)/q) := by
  let : NeZero d := ⟨by omega⟩
  let : SigmaFinite (observationReference d) := by unfold observationReference; infer_instance
  have hω : ∀ᵐ ω ∂ρ, ∀ t j,
      AEMeasurable (L.transition t ω j) (observationReference d) := by
    simp only [ae_all_iff]
    intro t j
    exact ae_fiber_aemeasurable (hL.transition t j).prod_swap
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d T) |
    angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    L.angularSuccess_nullMeasurable ρ ε hL
  have he := hp.measure_preimage hS
  have hb := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
      streamFactor (E := Vector d) (J := TaggedState M T) q ^ ((T+q-1)/q))
    (by
      filter_upwards [hω] with ω hω
      exact L.frozen_success_bound_tagged ω hd hω hε ha hq hqa)
  simpa only [he,measure_univ,mul_one,S,uniformSuccess] using hb

end Learner
end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace Learner
variable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]

instance runStatusMeasurable : MeasurableSpace (RunStatus M) := ⊤
instance runStatusSingleton : MeasurableSingletonClass (RunStatus M) := ⟨fun _ => trivial⟩

lemma measurable_countable_select {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]
    {f : J → X → Y} (hf : ∀ j, Measurable (f j)) {g : X → J} (hg : Measurable g) :
    Measurable (fun x => f (g x) x) :=
  (measurable_from_prod_countable_right (f := fun z : J × X => f z.1 z.2) hf).comp (hg.prodMk measurable_id)

lemma measurable_run (L : Learner d M T Ω) (hL : L.MeasurableRules) (n : ℕ) :
    Measurable (fun z : UnitSphere d × (Ω × Samples d T) => L.run z.1 z.2.1 z.2.2 n) := by
  classical
  induction n with
  | zero =>
    exact (measurable_of_finite (fun a : Bool × State M =>
      if a.1 then Sum.inr (0,a.2) else Sum.inl a.2)).comp
        (hL.initial.comp (measurable_fst.comp measurable_snd))
  | succ n ih =>
    let F : RunStatus M → (UnitSphere d × (Ω × Samples d T)) → RunStatus M := fun j z =>
      match j with
      | .inr done => .inr done
      | .inl j => if hn : n < T then
          let row := z.2.2 ⟨n,hn⟩
          let a := L.transition (n+1) z.2.1 j (row,⟪row,z.1.val⟫)
          if a.1 then .inr (n+1,a.2) else .inl a.2
        else .inl j
    change Measurable (fun z => F (L.run z.1 z.2.1 z.2.2 n) z)
    apply measurable_countable_select _ ih
    intro j
    cases j with
    | inr done => exact measurable_const
    | inl j =>
      dsimp [F]
      split_ifs with hn
      · exact (measurable_of_finite (fun a : Bool × State M =>
          if a.1 then Sum.inr (n+1,a.2) else Sum.inl a.2)).comp
            ((hL.transition (n+1) j).comp (show Measurable (fun z : UnitSphere d × (Ω × Samples d T) =>
              (z.2.1,(z.2.2 ⟨n,hn⟩,⟪z.2.2 ⟨n,hn⟩,z.1.val⟫))) from by fun_prop))
      · exact measurable_const

lemma measurable_terminal (L : Learner d M T Ω) (hL : L.MeasurableRules) :
    Measurable (fun z : UnitSphere d × (Ω × Samples d T) => L.terminal z.1 z.2.1 z.2.2) := by
  exact (measurable_of_countable (fun j : RunStatus M =>
    match j with | .inl j => (T,j) | .inr done => done)).comp (L.measurable_run hL T)

lemma measurable_estimate (L : Learner d M T Ω) (hL : L.MeasurableRules) :
    Measurable (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2) := by
  exact measurable_countable_select (f := fun a z => L.output a.1 z.2.1 a.2)
    (fun a => (hL.output a.1 a.2).comp (by fun_prop)) (L.measurable_terminal hL)

lemma admissible_of_measurable (L : Learner d M T Ω) (hL : L.MeasurableRules) (ρ : Measure Ω) :
    L.Admissible ρ := by
  refine ⟨hL.initial.aemeasurable,fun t j => (hL.transition t j).aemeasurable,
    fun t j => (hL.output t j).aemeasurable,?_,(L.measurable_estimate hL).aemeasurable⟩
  intro s
  exact ((L.measurable_estimate hL).comp (measurable_const.prodMk measurable_id)).aemeasurable

end Learner


lemma joint_sphere_sample_observation_quasi {d T : ℕ} (hd : 3 ≤ d)
    {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω) [SFinite ρ] (i : Fin T) :
    Measure.QuasiMeasurePreserving
      (fun z : UnitSphere d × (Ω × Samples d T) => (z.2.1,(z.2.2 i,⟪z.1.val,z.2.2 i⟫)))
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) (ρ.prod (observationReference d)) := by
  let : NeZero d := ⟨by omega⟩
  have hp := (measurePreserving_prodAssoc ρ (uniformSphere d) (sampleLaw d T)).comp
    (((Measure.measurePreserving_swap (μ := uniformSphere d) (ν := ρ)).prod
      (MeasurePreserving.id (sampleLaw d T))).comp
        ((measurePreserving_prodAssoc (uniformSphere d) ρ (sampleLaw d T)).symm
          MeasurableEquiv.prodAssoc))
  have h := QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id ρ)
    (sphere_sample_observation_quasi (E := Vector d) (by simpa using hd) i)
  exact h.comp hp.quasiMeasurePreserving

namespace Learner
variable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]

theorem exists_borel_version (L : Learner d M T Ω) (ρ : Measure Ω) [SFinite ρ]
    (hd : 3 ≤ d)
    (hi : AEMeasurable L.initialChoice ρ)
    (ht : ∀ t j, AEMeasurable (fun z : Ω × (Vector d × ℝ) => L.transition t z.1 j z.2)
      (ρ.prod (observationReference d)))
    (ho : ∀ t j, AEMeasurable (fun ω => L.output t ω j) ρ) :
    ∃ L' : Learner d M T Ω, L'.MeasurableRules ∧
      (∀ᵐ z ∂((uniformSphere d).prod (ρ.prod (sampleLaw d T))),
        (∀ n, L.run z.1 z.2.1 z.2.2 n = L'.run z.1 z.2.1 z.2.2 n) ∧
        L.estimate z.1 z.2.1 z.2.2 = L'.estimate z.1 z.2.1 z.2.2) := by
  classical
  let L' : Learner d M T Ω := ⟨hi.mk _,fun t ω j obs => (ht t j).mk _ (ω,obs),
    fun t ω j => (ho t j).mk _ ω⟩
  have hL' : L'.MeasurableRules := ⟨hi.measurable_mk,fun t j => (ht t j).measurable_mk,
    fun t j => (ho t j).measurable_mk⟩
  refine ⟨L',hL',?_⟩
  let μ := (uniformSphere d).prod (ρ.prod (sampleLaw d T))
  have hp : Measure.QuasiMeasurePreserving (fun z : UnitSphere d × (Ω × Samples d T) => z.2.1) μ ρ :=
    QuasiMeasurePreserving.fst Measure.quasiMeasurePreserving_snd
  have hinit : ∀ᵐ z ∂μ, L.initialChoice z.2.1 = L'.initialChoice z.2.1 := hp.ae hi.ae_eq_mk
  have hout : ∀ᵐ z ∂μ, ∀ t j, L.output t z.2.1 j = L'.output t z.2.1 j := by
    simp only [ae_all_iff]
    intro t j
    exact hp.ae (ho t j).ae_eq_mk
  have htrans : ∀ᵐ z ∂μ, ∀ t j (i : Fin T),
      L.transition t z.2.1 j (z.2.2 i,⟪z.2.2 i,z.1.val⟫) =
      L'.transition t z.2.1 j (z.2.2 i,⟪z.2.2 i,z.1.val⟫) := by
    simp only [ae_all_iff]
    intro t j i
    simpa only [real_inner_comm] using (joint_sphere_sample_observation_quasi hd ρ i).ae (ht t j).ae_eq_mk
  filter_upwards [hinit,hout,htrans] with z hi ho ht
  have hr (n : ℕ) : L.run z.1 z.2.1 z.2.2 n = L'.run z.1 z.2.1 z.2.2 n := by
    induction n with
    | zero => simp only [run,start,hi]
    | succ n ih =>
      rw [run,run,ih]
      cases L'.run z.1 z.2.1 z.2.2 n with
      | inr done => rfl
      | inl j =>
        split_ifs with hn
        · dsimp only
          rw [ht (n+1) j ⟨n,hn⟩]
        · rfl
  refine ⟨hr,?_⟩
  have he : L.terminal z.1 z.2.1 z.2.2 = L'.terminal z.1 z.2.1 z.2.2 := by
    simp only [terminal,hr]
  simp only [estimate,he,ho]

lemma aemeasurable_terminal_of_rules (L : Learner d M T Ω) (ρ : Measure Ω) [SFinite ρ]
    (hd : 3 ≤ d) (hL : L.Admissible ρ) :
    AEMeasurable (fun z : UnitSphere d × (Ω × Samples d T) => L.terminal z.1 z.2.1 z.2.2)
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := by
  obtain ⟨L',hL',he⟩ := L.exists_borel_version ρ hd hL.initialChoice hL.transition hL.output
  apply (L'.measurable_terminal hL').aemeasurable.congr
  filter_upwards [he] with z hz
  simp only [terminal,hz.1]

lemma uniformSuccess_borel_version (L : Learner d M T Ω) (ρ : Measure Ω) [SFinite ρ]
    (hd : 3 ≤ d) (hL : L.Admissible ρ) :
    ∃ L' : Learner d M T Ω, L'.MeasurableRules ∧ L'.Admissible ρ ∧
      ∀ ε, L.uniformSuccess ρ ε = L'.uniformSuccess ρ ε := by
  obtain ⟨L',hL',he⟩ := L.exists_borel_version ρ hd hL.initialChoice hL.transition hL.output
  refine ⟨L',hL',L'.admissible_of_measurable hL' ρ,fun ε => measure_congr ?_⟩
  filter_upwards [he] with z hz
  show (angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε) = (angularError z.1 (L'.estimate z.1 z.2.1 z.2.2) ≤ ε)
  rw [hz.2]

end Learner
end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

lemma finite_kernel_borel_version {X J : Type*} [MeasurableSpace X]
    [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure X) (P : X → Measure J) (hP : ∀ x, IsProbabilityMeasure (P x))
    (hm : ∀ j, AEMeasurable (fun x => P x {j}) μ) :
    ∃ κ : Kernel X J, IsMarkovKernel κ ∧ (fun x => κ x) =ᵐ[μ] P := by
  classical
  let v : X → Measure J := fun x => ∑ j, ((hm j).mk _ x) • Measure.dirac j
  have hv : Measurable v := by
    apply Finset.measurable_sum
    intro j _
    exact (hm j).measurable_mk.smul_measure (Measure.dirac j)
  have he : v =ᵐ[μ] P := by
    have hh : ∀ᵐ x ∂μ, ∀ j, (hm j).mk _ x = P x {j} := by
      simp only [ae_all_iff]
      intro j
      exact (hm j).ae_eq_mk.symm
    filter_upwards [hh] with x hx
    simp only [v,hx,← Measure.sum_fintype,Measure.sum_smul_dirac]
  let κ : Kernel X J := ⟨fun x => if v x Set.univ = 1 then v x else Measure.dirac (Classical.choice ‹Nonempty J›),
    hv.ite (measurableSet_eq_fun ((Measure.measurable_coe MeasurableSet.univ).comp hv) measurable_const)
      measurable_const⟩
  refine ⟨κ,⟨fun x => ⟨?_⟩⟩,?_⟩
  · dsimp [κ]
    split_ifs with h
    · exact h
    · simp
  · filter_upwards [he] with x hx
    have hx1 : v x Set.univ = 1 := by rw [hx]; exact (hP x).measure_univ
    dsimp only [κ,Kernel.coe_mk]
    rw [ite_eq_left hx1,hx]

namespace FiniteKernelLearner
variable {d M T : ℕ}

structure BorelRules (K : FiniteKernelLearner d M T) : Prop where
  transition : ∀ t j, Measurable (K.transition t j)

lemma exists_borel_version (K : FiniteKernelLearner d M T) (hK : K.CompletedRules) :
    ∃ K' : FiniteKernelLearner d M T, K'.BorelRules ∧ K'.initial = K.initial ∧
      K'.output = K.output ∧ ∀ t j, K'.transition t j =ᵐ[observationReference d] K.transition t j := by
  classical
  choose κ hκ he using fun t j => finite_kernel_borel_version (observationReference d)
    (K.transition t j) (K.transition_probability t j) (hK.transition t j)
  let K' : FiniteKernelLearner d M T := ⟨K.initial,K.initial_probability,
    fun t j obs => κ t j obs,fun t j obs => (hκ t j).isProbabilityMeasure obs,
    K.output,K.output_probability⟩
  exact ⟨K',⟨fun t j => (κ t j).measurable⟩,rfl,rfl,he⟩

end FiniteKernelLearner

variable {J O : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace O]

def coinRun (F : ℕ → J → O → I → J) :
    (n : ℕ) → J → (Fin n → O) → (Fin n → I) → J
  | 0, j, _, _ => j
  | n+1, j, obs, u => F (n+1) (coinRun F n j (Fin.init obs) (Fin.init u)) (obs (Fin.last n)) (u (Fin.last n))

omit [MeasurableSpace O] in
lemma measurable_coinRun [MeasurableSpace O] {F : ℕ → J → O → I → J}
    (hF : ∀ t j obs, Measurable (F t j obs)) (n : ℕ) (j : J) (obs : Fin n → O) :
    Measurable (coinRun F n j obs) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun u : Fin (n+1) → I => F (n+1) (coinRun F n j (Fin.init obs) (Fin.init u)) (obs (Fin.last n)) (u (Fin.last n)))
    have hi : Measurable (fun u : Fin (n+1) → I => Fin.init u) := by
      change Measurable (fun u : Fin (n+1) → I => fun i : Fin n => u i.castSucc)
      fun_prop
    have hg : Measurable (fun u : Fin (n+1) → I => coinRun F n j (Fin.init obs) (Fin.init u)) :=
      (ih (Fin.init obs)).comp hi
    exact measurable_select (h := fun a (u : Fin (n+1) → I) => F (n+1) a (obs (Fin.last n)) (u (Fin.last n)))
      (fun a => (hF (n+1) a (obs (Fin.last n))).comp (measurable_pi_apply _)) hg

lemma lintegral_coinRun {F : ℕ → J → O → I → J} {P : ℕ → J → O → Measure J}
    (hF : ∀ t j obs, Measurable (F t j obs))
    (hP : ∀ t j obs, volume.map (F t j obs) = P t j obs)
    (n : ℕ) (j : J) (obs : Fin n → O) (f : J → ℝ≥0∞) :
    (∫⁻ u, f (coinRun F n j obs u) ∂Measure.pi (fun _ => (volume : Measure I))) =
      ∫⁻ a, f a ∂kernelRun P n j obs := by
  induction n generalizing f with
  | zero => simp [coinRun,kernelRun]
  | succ n ih =>
    rw [lintegral_pi_snoc volume (fun u => f (coinRun F (n+1) j obs u))
      ((measurable_of_finite f).comp (measurable_coinRun hF (n+1) j obs))]
    simp only [coinRun,Fin.init_snoc,Fin.snoc_last]
    have hh (a : J) : (∫⁻ u, f (F (n+1) a (obs (Fin.last n)) u) ∂volume) =
        ∫⁻ b, f b ∂P (n+1) a (obs (Fin.last n)) := by
      rw [←hP]
      exact (lintegral_map (measurable_of_finite f) (hF _ _ _)).symm
    simp_rw [hh]
    rw [ih (Fin.init obs) (fun a => ∫⁻ b, f b ∂P (n+1) a (obs (Fin.last n)))]
    exact (Measure.lintegral_bind (measurable_of_finite _).aemeasurable
      (measurable_of_finite f).aemeasurable).symm

lemma coinRun_law {F : ℕ → J → O → I → J} {P : ℕ → J → O → Measure J}
    (hF : ∀ t j obs, Measurable (F t j obs))
    (hP : ∀ t j obs, volume.map (F t j obs) = P t j obs)
    (n : ℕ) (j : J) (obs : Fin n → O) :
    (Measure.pi (fun _ => (volume : Measure I))).map (coinRun F n j obs) = kernelRun P n j obs := by
  apply Measure.ext
  intro s hs
  have hh := lintegral_coinRun hF hP n j obs (s.indicator (fun _ => (1 : ℝ≥0∞)))
  rw [← lintegral_map (by fun_prop) (measurable_coinRun hF n j obs)] at hh
  simpa only [lintegral_indicator_const hs,one_mul] using hh

omit [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [MeasurableSpace O] in
lemma kernelRun_congr [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace O] {P P' : ℕ → J → O → Measure J} (n : ℕ) (j : J) (obs : Fin n → O)
    (h : ∀ t a i, P t a (obs i) = P' t a (obs i)) :
    kernelRun P n j obs = kernelRun P' n j obs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [kernelRun]
    rw [ih (Fin.init obs) (fun t a i => h t a i.castSucc)]
    congr 1
    funext a
    exact h _ _ _

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace FiniteKernelLearner
open Learner
variable {d M T : ℕ}

structure Realizer (K : FiniteKernelLearner d M T) where
  transition : ℕ → State M → (Vector d × ℝ) → I → Bool × State M
  transition_measurable : ∀ t j, Measurable (Function.uncurry (transition t j))
  transition_law : ∀ t j obs, volume.map (transition t j obs) = K.transition t j obs
  output : ℕ → State M → I → UnitSphere d
  output_measurable : ∀ t j, Measurable (output t j)
  output_law : ∀ t j, volume.map (output t j) = K.output t j

lemma exists_realizer (K : FiniteKernelLearner d M T) (hK : K.BorelRules) : Nonempty K.Realizer := by
  classical
  let j₀ : State M := ⟨0,by simp⟩
  let : IsProbabilityMeasure (K.output 0 j₀) := K.output_probability 0 j₀
  let : Nonempty (UnitSphere d) := nonempty_of_isProbabilityMeasure (K.output 0 j₀)
  have ht (t : ℕ) (j : State M) : ∃ f : (Vector d × ℝ) → I → Bool × State M,
      Measurable (Function.uncurry f) ∧ ∀ obs, volume.map (f obs) = K.transition t j obs := by
    let κ : Kernel (Vector d × ℝ) (Bool × State M) := ⟨K.transition t j,hK.transition t j⟩
    let : IsMarkovKernel κ := ⟨K.transition_probability t j⟩
    exact κ.exists_measurable_map_eq_unitInterval
  have ho (t : ℕ) (j : State M) : ∃ g : I → UnitSphere d, Measurable g ∧ volume.map g = K.output t j := by
    let : IsProbabilityMeasure (K.output t j) := K.output_probability t j
    exact (K.output t j).exists_measurable_map_eq
  choose f hf hfl using ht
  choose g hg hgl using ho
  exact ⟨⟨f,hf,hfl,g,hg,hgl⟩⟩

def tapeLaw (K : FiniteKernelLearner d M T) : Measure (Tape M T) :=
  K.initial.prod ((Measure.pi (fun _ => (volume : Measure I))).prod volume)

instance tapeLaw_probability (K : FiniteKernelLearner d M T) : IsProbabilityMeasure K.tapeLaw := by
  let := K.initial_probability
  unfold tapeLaw
  infer_instance

def Realizer.toLearner {K : FiniteKernelLearner d M T} (R : K.Realizer) : Learner d M T (Tape M T) where
  initialChoice := Prod.fst
  transition := fun t ω j obs => if ht : 0 < t ∧ t ≤ T then
    R.transition t j obs (ω.2.1 ⟨t-1,by omega⟩) else (false,j)
  output := fun t ω j => R.output t j ω.2.2

lemma Realizer.measurableRules {K : FiniteKernelLearner d M T} (R : K.Realizer) :
    R.toLearner.MeasurableRules := by
  refine ⟨measurable_fst,fun t j => ?_,fun t j => (R.output_measurable t j).comp (by fun_prop)⟩
  dsimp [Realizer.toLearner]
  split_ifs with ht
  · exact (R.transition_measurable t j).comp (show Measurable (fun z : Tape M T × (Vector d × ℝ) =>
      (z.2,z.1.2.1 ⟨t-1,by omega⟩)) from by fun_prop)
  · exact measurable_const

def Realizer.taggedTransition {K : FiniteKernelLearner d M T} (R : K.Realizer) (t : ℕ) :
    TaggedState M T → (Vector d × ℝ) → I → TaggedState M T
  | .inr a, _, _ => .inr a
  | .inl j, obs, u => if ht : t ≤ T then destination t ht (R.transition t j obs u) else .inl j

lemma Realizer.tagged_measurable {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (t : ℕ) (j : TaggedState M T) (obs : Vector d × ℝ) : Measurable (R.taggedTransition t j obs) := by
  cases j with
  | inr a => exact measurable_const
  | inl j =>
    change Measurable (fun u => R.taggedTransition t (.inl j) obs u)
    simp only [Realizer.taggedTransition]
    split_ifs with ht
    · exact (measurable_of_finite (destination t ht)).comp (R.transition_measurable t j).of_uncurry_left
    · exact measurable_const

lemma Realizer.tagged_law {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (t : ℕ) (j : TaggedState M T) (obs : Vector d × ℝ) :
    volume.map (R.taggedTransition t j obs) = K.taggedKernel t j obs := by
  cases j with
  | inr a =>
    change volume.map (fun _ : I => Sum.inr a) = Measure.dirac (.inr a)
    simp [Measure.map_const]
  | inl j =>
    change volume.map (fun u => R.taggedTransition t (.inl j) obs u) = _
    simp only [Realizer.taggedTransition,taggedKernel]
    split_ifs with ht
    · rw [← R.transition_law,Measure.map_map (measurable_of_finite _)
        (R.transition_measurable t j).of_uncurry_left]
      rfl
    · simp [Measure.map_const]

def Realizer.terminalOutput {K : FiniteKernelLearner d M T} (R : K.Realizer) :
    TaggedState M T → I → UnitSphere d
  | .inl j => R.output T j
  | .inr (t,j) => R.output t j

lemma Realizer.terminalOutput_measurable {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) : Measurable (R.terminalOutput j) := by
  cases j with
  | inl j => exact R.output_measurable T j
  | inr a => exact R.output_measurable a.1 a.2

lemma Realizer.terminalOutput_law {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) : volume.map (R.terminalOutput j) = K.terminalOutput j := by
  cases j with
  | inl j => exact R.output_law T j
  | inr a => exact R.output_law a.1 a.2

def experimentLaw (K : FiniteKernelLearner d M T) (obs : Fin T → (Vector d × ℝ)) : Measure (UnitSphere d) :=
  K.initial.bind (fun a => (kernelRun K.taggedKernel T (taggedStart a) obs).bind K.terminalOutput)

lemma Realizer.run_eq_coinRun {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (ω : Tape M T) (x : Samples d T) {n : ℕ} (hn : n ≤ T) :
    R.toLearner.run s ω x n = decodeTagged
      (coinRun R.taggedTransition n (taggedStart ω.1)
        (fun i => (x (Fin.castLE hn i),⟪s.val,x (Fin.castLE hn i)⟫))
        (fun i => ω.2.1 (Fin.castLE hn i))) := by
  induction n with
  | zero => exact (decode_taggedStart _).symm
  | succ n ih =>
    rw [Learner.run,ih (by omega)]
    have hp := fin_prefix_snoc hn (fun i => (x i,⟪s.val,x i⟫))
    rw [hp,fin_prefix_snoc hn ω.2.1,coinRun,Fin.init_snoc,Fin.init_snoc,Fin.snoc_last,Fin.snoc_last]
    generalize coinRun R.taggedTransition n (taggedStart ω.1)
      (fun i => (x (Fin.castLE (by omega : n ≤ T) i),⟪s.val,x (Fin.castLE (by omega : n ≤ T) i)⟫))
      (fun i => ω.2.1 (Fin.castLE (by omega : n ≤ T) i)) = j
    cases j with
    | inr a => rfl
    | inl j =>
      simp only [decodeTagged,Realizer.taggedTransition,Realizer.toLearner,
        dite_eq_left (by omega : n < T),dite_eq_left (by omega : 0 < n+1 ∧ n+1 ≤ T),
        dite_eq_left (by omega : n+1 ≤ T),destination,real_inner_comm,Nat.add_sub_cancel]
      split_ifs <;> rfl

lemma Realizer.estimate_eq_coinRun {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (ω : Tape M T) (x : Samples d T) :
    R.toLearner.estimate s ω x = R.terminalOutput
      (coinRun R.taggedTransition T (taggedStart ω.1) (fun i => (x i,⟪s.val,x i⟫)) ω.2.1) ω.2.2 := by
  unfold Learner.estimate Learner.terminal
  rw [R.run_eq_coinRun s ω x le_rfl]
  have hi (i : Fin T) : Fin.castLE le_rfl i = i := Fin.ext rfl
  simp only [hi]
  generalize coinRun R.taggedTransition T (taggedStart ω.1) (fun i => (x i,⟪s.val,x i⟫)) ω.2.1 = j
  cases j <;> rfl

end FiniteKernelLearner

lemma map_finite_prod_eq_bind {A B C : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) [SFinite ν] {f : A × B → C} (hf : Measurable f) :
    (μ.prod ν).map f = μ.bind (fun a => ν.map (fun b => f (a,b))) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hf,lintegral_prod (fun z => g (f z)) (hg.comp hf).aemeasurable,
    Measure.lintegral_bind (measurable_of_finite _).aemeasurable hg.aemeasurable]
  apply lintegral_congr
  intro a
  exact (lintegral_map hg (hf.comp (measurable_const.prodMk measurable_id))).symm

lemma coinRun_output_law {J O Y : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] [MeasurableSpace O] [MeasurableSpace Y]
    {F : ℕ → J → O → I → J} {P : ℕ → J → O → Measure J}
    (hF : ∀ t j obs, Measurable (F t j obs))
    (hP : ∀ t j obs, volume.map (F t j obs) = P t j obs)
    {g : J → I → Y} {Q : J → Measure Y} (hg : ∀ j, Measurable (g j))
    (hQ : ∀ j, volume.map (g j) = Q j) (n : ℕ) (j : J) (obs : Fin n → O) :
    ((Measure.pi (fun _ => (volume : Measure I))).prod volume).map
      (fun z => g (coinRun F n j obs z.1) z.2) = (kernelRun P n j obs).bind Q := by
  have hm : Measurable (fun z : (Fin n → I) × I => g (coinRun F n j obs z.1) z.2) :=
    measurable_select (h := fun a (z : (Fin n → I) × I) => g a z.2)
      (fun a => (hg a).comp measurable_snd) ((measurable_coinRun hF n j obs).comp measurable_fst)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm,lintegral_prod (fun z => f (g (coinRun F n j obs z.1) z.2)) (hf.comp hm).aemeasurable]
  have ho (a : J) : (∫⁻ u, f (g a u) ∂volume) = ∫⁻ y, f y ∂Q a := by
    rw [← hQ]
    exact (lintegral_map hf (hg a)).symm
  simp_rw [ho]
  rw [lintegral_coinRun hF hP n j obs (fun a => ∫⁻ y, f y ∂Q a)]
  exact (Measure.lintegral_bind (measurable_of_finite _).aemeasurable hf.aemeasurable).symm

namespace FiniteKernelLearner
open Learner
variable {d M T : ℕ}

def Realizer.terminalJointOutput {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) (u : I) : Result d M := (terminalTag j,R.terminalOutput j u)

lemma Realizer.terminalJointOutput_measurable {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) : Measurable (R.terminalJointOutput j) :=
  measurable_const.prodMk (R.terminalOutput_measurable j)

lemma Realizer.terminalJointOutput_law {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) : volume.map (R.terminalJointOutput j) = K.terminalJointOutput j := by
  rw [FiniteKernelLearner.terminalJointOutput,← R.terminalOutput_law,
    Measure.map_map (by fun_prop) (R.terminalOutput_measurable j)]
  rfl

lemma Realizer.terminal_eq_coinRun {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (ω : Tape M T) (x : Samples d T) :
    R.toLearner.terminal s ω x = terminalTag
      (coinRun R.taggedTransition T (taggedStart ω.1) (fun i => (x i,⟪s.val,x i⟫)) ω.2.1) := by
  unfold Learner.terminal
  rw [R.run_eq_coinRun s ω x le_rfl]
  have hi (i : Fin T) : Fin.castLE le_rfl i = i := Fin.ext rfl
  simp only [hi]
  generalize coinRun R.taggedTransition T (taggedStart ω.1) (fun i => (x i,⟪s.val,x i⟫)) ω.2.1 = j
  cases j <;> rfl

theorem Realizer.conditional_joint_law {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (x : Samples d T) :
    K.tapeLaw.map (fun ω => (R.toLearner.terminal s ω x,R.toLearner.estimate s ω x)) =
      K.jointExperimentLaw (fun i => (x i,⟪s.val,x i⟫)) := by
  have hm : Measurable (fun ω : Tape M T =>
      (R.toLearner.terminal s ω x,R.toLearner.estimate s ω x)) :=
    ((R.toLearner.measurable_terminal R.measurableRules).prodMk
      (R.toLearner.measurable_estimate R.measurableRules)).comp
        (show Measurable (fun ω : Tape M T => (s,(ω,x))) from by fun_prop)
  unfold tapeLaw jointExperimentLaw
  have : IsProbabilityMeasure ((Measure.pi (fun _ : Fin T => (volume : Measure I))).prod
      (volume : Measure I)) := inferInstance
  have : IsFiniteMeasure ((Measure.pi (fun _ : Fin T => (volume : Measure I))).prod
      (volume : Measure I)) := inferInstance
  have : SigmaFinite ((Measure.pi (fun _ : Fin T => (volume : Measure I))).prod
      (volume : Measure I)) := IsFiniteMeasure.toSigmaFinite _
  rw [map_finite_prod_eq_bind K.initial
    ((Measure.pi (fun _ : Fin T => (volume : Measure I))).prod (volume : Measure I)) hm]
  congr 1
  funext a
  have he : (fun z : (Fin T → I) × I =>
      (R.toLearner.terminal s (a,z) x,R.toLearner.estimate s (a,z) x)) =
      (fun z => R.terminalJointOutput
        (coinRun R.taggedTransition T (taggedStart a) (fun i => (x i,⟪s.val,x i⟫)) z.1) z.2) := by
    funext z
    rw [R.terminal_eq_coinRun,R.estimate_eq_coinRun]
    rfl
  rw [he]
  exact coinRun_output_law R.tagged_measurable R.tagged_law R.terminalJointOutput_measurable
    R.terminalJointOutput_law T (taggedStart a) _

end FiniteKernelLearner
end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma capWeight_mass_mixed (y : E) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (a : ℕ) {b : ℝ} (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (Module.finrank ℝ E-1:ℕ)) :
    PolynomialMass ((ambientSphereLaw (E := E)).withDensity (capWeight y ε)) a
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^b)) := by
  change PolynomialMass ((ambientSphereLaw (E := E)).withDensity ((Metric.closedBall y ε).indicator 1)) a _
  rw [withDensity_indicator_one Metric.isClosed_closedBall.measurableSet]
  intro z r hr
  rw [Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]
  by_cases h : r ≤ ε
  · apply (measure_mono Set.inter_subset_left).trans
    apply (ambientSphereLaw_closedBall z hr (Module.finrank ℝ E-1) le_rfl).trans
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hpow : r^(Module.finrank ℝ E-1) ≤ r^((a:ℝ)+b) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hr (h.trans hε1) hab
    apply hpow.trans
    rw [Real.rpow_add hr,Real.rpow_natCast,mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hr.le h hb) (pow_nonneg hr.le _)
  · apply (measure_mono Set.inter_subset_right).trans
    apply (ambientSphereLaw_closedBall y hε (Module.finrank ℝ E-1) le_rfl).trans
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hpow : ε^(Module.finrank ℝ E-1) ≤ ε^((a:ℝ)+b) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hε hε1 hab
    apply hpow.trans
    rw [Real.rpow_add hε,Real.rpow_natCast,mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le (le_of_not_ge h) a) (Real.rpow_nonneg hε.le _)

variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

lemma continuation_mixed_integral_bound {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : ℕ → J → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (Module.finrank ℝ E-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    (∫⁻ s, continuation δ (fun n j => capWeight (y n j) ε) n k j s ∂ambientSphereLaw) ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^b)) *
        streamFactor (E := E) (J := J) q ^ ((k+q-1)/q) := by
  have ha : a ≤ Module.finrank ℝ E := by
    have : (a:ℝ) ≤ (Module.finrank ℝ E:ℝ) := by
      have hh : ((Module.finrank ℝ E-1:ℕ):ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast Nat.sub_le (Module.finrank ℝ E) 1
      linarith
    exact_mod_cast this
  apply ambient_mass_bound
  apply continuation_mass_bound_ceil _ hδ (fun n j => measurable_capWeight _ _)
    (fun n j s => capWeight_le_one _ _ _)
    (mul_ne_zero (by positivity) (by positivity)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (fun n j => capWeight_mass_mixed (y n j) hε hε1 a hb hab)
    (Module.finrank_pos (R := ℝ) (M := E)) ha hq hqa

lemma route_mixed_bound {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (Module.finrank ℝ E-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (k : ℕ) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin k => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^b)) *
        streamFactor (E := E) (J := J) q ^ ((k+q-1)/q) := by
  let w : ℕ → J → E → ℝ≥0∞ := fun _ j => capWeight (y j) ε
  have hV := measurable_continuation (w := w) hδ (fun _ j => measurable_capWeight (y j) ε) 0 k j
  have he (s : E) : continuation δ w 0 k j s =
      ∫⁻ A : Fin k → E, capWeight (y (streamRoute δ 0 k j (A,fun i => ⟪s,A i⟫))) ε s
        ∂Measure.pi (fun _ => stdGaussian E) := by
    simpa [w, blockValue, continuation] using continuation_unroll (w := w) hδ 0 k 0 j s
  let S : Set ((Metric.sphere (0 : E) 1) × (Fin k → E)) :=
    {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε}
  have hS : MeasurableSet S := by
    apply measurableSet_le _ measurable_const
    exact measurable_subtype_coe.comp measurable_fst |>.dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  change ((sphereLaw (E := E)).prod _) S ≤ _
  rw [← one_mul (((sphereLaw (E := E)).prod _) S), ← lintegral_indicator_const hS 1,
    lintegral_prod _ (measurable_const.indicator hS).aemeasurable]
  have hf : ∀ s : Metric.sphere (0 : E) 1,
      (∫⁻ A, S.indicator (fun _ => (1 : ℝ≥0∞)) (s,A) ∂Measure.pi (fun _ => stdGaussian E)) =
        continuation δ w 0 k j s.val := by
    intro s
    rw [he]
    apply lintegral_congr
    intro A
    classical
    change (if dist s.val (y (streamRoute δ 0 k j (A,fun i => ⟪s.val,A i⟫))) ≤ ε then 1 else 0) = _
    unfold capWeight
    rw [Set.indicator_apply]
    rfl
  simp_rw [hf]
  rw [← lintegral_map hV measurable_subtype_coe]
  exact continuation_mixed_integral_bound hδ (fun _ => y) hε hε1 hb hab hq hqa 0 k j

end

namespace Learner

section
variable {d M : ℕ}

def haltShift {k : ℕ} : TaggedState M k → TaggedState M (k+1)
  | .inl j => .inl j
  | .inr (t,j) => .inr (t.succ,j)

def haltRoute (τ : ℕ → State M → (Vector d × ℝ) → Bool × State M) (n : ℕ) :
    (k : ℕ) → State M → ((Fin k → Vector d) × (Fin k → ℝ)) → TaggedState M k
  | 0, j, _ => .inl j
  | k+1, j, X =>
    let a := τ (n+1) j (X.1 0,X.2 0)
    if a.1 then .inr (⟨1,by omega⟩,a.2)
    else haltShift (haltRoute τ (n+1) k a.2 (Fin.tail X.1,Fin.tail X.2))

lemma measurable_haltRoute {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (hτ : ∀ t j, Measurable (τ t j)) (n k : ℕ) (j : State M) :
    Measurable (haltRoute τ n k j) := by
  induction k generalizing n j with
  | zero => exact measurable_const
  | succ k ih =>
    let h : (Bool × State M) → ((Fin (k+1) → Vector d) × (Fin (k+1) → ℝ)) → TaggedState M (k+1) :=
      fun a X => if a.1 then .inr (⟨1,by omega⟩,a.2)
        else haltShift (haltRoute τ (n+1) k a.2 (Fin.tail X.1,Fin.tail X.2))
    change Measurable (fun X => h (τ (n+1) j (X.1 0,X.2 0)) X)
    apply measurable_select (J := Bool × State M) _ ((hτ (n+1) j).comp (by fun_prop))
    intro a
    dsimp [h]
    split_ifs
    · exact measurable_const
    · exact (measurable_of_finite haltShift).comp ((ih (n+1) a.2).comp (by
        change Measurable (fun X : ((Fin (k+1) → Vector d) × (Fin (k+1) → ℝ)) =>
          ((fun i : Fin k => X.1 i.succ),(fun i : Fin k => X.2 i.succ)))
        fun_prop))

def haltChild (w : ℕ → State M → Vector d → ℝ≥0∞)
    (v : State M → Vector d → ℝ≥0∞) (n : ℕ) {k : ℕ} : TaggedState M k → Vector d → ℝ≥0∞
  | .inl j => v j
  | .inr (t,j) => w (n+t) j

def stoppedContinuation (τ : ℕ → State M → (Vector d × ℝ) → Bool × State M)
    (w : ℕ → State M → Vector d → ℝ≥0∞) (n : ℕ) : ℕ → State M → Vector d → ℝ≥0∞
  | 0, j, s => w n j s
  | k+1, j, s => ∫⁻ x, let a := τ (n+1) j (x,⟪s,x⟫)
      if a.1 then w (n+1) a.2 s else stoppedContinuation τ w (n+1) k a.2 s ∂stdGaussian (Vector d)

lemma measurable_stoppedContinuation {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hτ : ∀ t j, Measurable (τ t j)) (hw : ∀ n j, Measurable (w n j)) (n k : ℕ) (j : State M) :
    Measurable (stoppedContinuation τ w n k j) := by
  induction k generalizing n j with
  | zero => exact hw n j
  | succ k ih =>
    apply Measurable.lintegral_prod_left
    change Measurable (fun z : Vector d × Vector d =>
      if (τ (n+1) j (z.1,⟪z.2,z.1⟫)).1 then w (n+1) (τ (n+1) j (z.1,⟪z.2,z.1⟫)).2 z.2
      else stoppedContinuation τ w (n+1) k (τ (n+1) j (z.1,⟪z.2,z.1⟫)).2 z.2)
    apply measurable_select (J := Bool × State M) (h := fun a (z : Vector d × Vector d) =>
      if a.1 then w (n+1) a.2 z.2 else stoppedContinuation τ w (n+1) k a.2 z.2) _
      ((hτ (n+1) j).comp (by fun_prop))
    intro a
    split_ifs
    · exact (hw (n+1) a.2).comp measurable_snd
    · exact (ih (n+1) a.2).comp measurable_snd

lemma stoppedContinuation_le_one
    {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hw : ∀ n j s, w n j s ≤ 1) (n k : ℕ) (j : State M) (s : Vector d) :
    stoppedContinuation τ w n k j s ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hw n j s
  | succ k ih =>
    change (∫⁻ x, (if (τ (n+1) j (x,⟪s,x⟫)).1 then w (n+1) (τ (n+1) j (x,⟪s,x⟫)).2 s else stoppedContinuation τ w (n+1) k (τ (n+1) j (x,⟪s,x⟫)).2 s) ∂stdGaussian (Vector d)) ≤ 1
    apply (lintegral_mono (g := fun _ => (1:ℝ≥0∞)) (fun x => ?_)).trans_eq (by simp)
    split_ifs
    · exact hw _ _ _
    · exact ih _ _

lemma stoppedContinuation_unroll
    {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hτ : ∀ t j, Measurable (τ t j)) (n m k : ℕ) (j : State M) (s : Vector d) :
    stoppedContinuation τ w n (m+k) j s =
      blockValue (haltChild w (stoppedContinuation τ w (n+m) k) n) (haltRoute τ n m j) s := by
  induction m generalizing n j with
  | zero => simp [blockValue,haltRoute,haltChild]
  | succ m ih =>
    rw [Nat.succ_add,stoppedContinuation]
    unfold blockValue
    have hf : Measurable (fun X : Fin (m+1) → Vector d =>
        haltChild w (stoppedContinuation τ w (n+(m+1)) k) n
          (haltRoute τ n (m+1) j (X,fun i => ⟪s,X i⟫)) s) :=
      (measurable_of_finite (fun a => haltChild w (stoppedContinuation τ w (n+(m+1)) k) n a s)).comp
        ((measurable_haltRoute hτ n (m+1) j).comp (by fun_prop))
    rw [lintegral_pi_cons _ _ hf]
    apply lintegral_congr
    intro x
    have htail (X : Fin m → Vector d) : Fin.tail (fun i : Fin (m+1) => ⟪s,(Fin.cons x X : Fin (m+1) → Vector d) i⟫) = (fun i => ⟪s,X i⟫) := by funext i; rfl
    simp only [haltRoute,Fin.cons_zero,Fin.tail_cons,htail]
    split_ifs with h
    · simp [haltChild]
    · rw [ih]
      unfold blockValue
      apply lintegral_congr
      intro X
      have h1 : n+(m+1) = n+1+m := by omega
      rw [h1]
      generalize haltRoute τ (n+1) m (τ (n+1) j (x,⟪s,x⟫)).2 (X,fun i => ⟪s,X i⟫) = a
      cases a with
      | inl j => rfl
      | inr done =>
        simp only [haltShift,haltChild,Fin.val_succ]
        rw [show n+1+done.1.val = n+(done.1.val+1) by omega]

lemma stoppedContinuation_mass_bound {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hτ : ∀ t j, Measurable (τ t j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (ambientSphereLaw.withDensity (w n j)) a C)
    (hd : 1 ≤ d) (ha : a ≤ d) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (n k : ℕ) (j : State M) :
    PolynomialMass (ambientSphereLaw.withDensity (stoppedContinuation τ w n k j)) a
      (C * streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((k+q-1)/q)) := by
  let : NeZero d := ⟨by omega⟩
  let K := streamFactor (E := Vector d) (J := TaggedState M q) q
  have hK1 : 1 ≤ K := one_le_streamFactor (by omega)
  have hK0 : K ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK1)
  have hKt : K ≠ ∞ := streamFactor_ne_top _
  have hden : ((q-1 : ℕ) : ℝ)+1 = (q : ℝ) := by rw [Nat.cast_sub (by omega),Nat.cast_one]; ring
  have hq0 : 0 < q := by omega
  change PolynomialMass _ a (C*K^_)
  induction k using Nat.strong_induction_on generalizing n j with
  | h k ih =>
    by_cases hk0 : k = 0
    · subst k
      simpa only [Nat.zero_add,Nat.div_eq_of_lt (by omega : q-1 < q),pow_zero,mul_one,stoppedContinuation] using hlocal n j
    let m := min k q
    have hm0 : 0 < m := by dsimp [m]; omega
    have hm : m ≤ q := min_le_right _ _
    have hmk : m ≤ k := min_le_left _ _
    have hki : k-m < k := by omega
    let C' := C*K^((k-m+q-1)/q)
    have hC' : C' ≠ 0 := mul_ne_zero hC (pow_ne_zero _ hK0)
    have hC't : C' ≠ ∞ := ENNReal.mul_ne_top hCt (ENNReal.pow_ne_top hKt)
    have hCC' : C ≤ C' := le_mul_of_one_le_right' (one_le_pow₀ hK1)
    let f := haltChild w (stoppedContinuation τ w (n+m) (k-m)) n (k := m)
    have hf (a : TaggedState M m) : Measurable (f a) := by
      cases a with
      | inl j => exact measurable_stoppedContinuation hτ hw _ _ _
      | inr done => exact hw _ _
    have hf1 (a : TaggedState M m) (s : Vector d) : f a s ≤ 1 := by
      cases a with
      | inl j => exact stoppedContinuation_le_one hw1 _ _ _ _
      | inr done => exact hw1 _ _ _
    have hflocal (a' : TaggedState M m) : PolynomialMass (ambientSphereLaw.withDensity (f a')) a C' := by
      cases a' with
      | inl j => exact ih (k-m) hki (n+m) j
      | inr done =>
        intro z r hr
        exact (hlocal (n+done.1) done.2 z r hr).trans (mul_le_mul' hCC' le_rfl)
    have hb := blockValue_mass_bound ambientSphereLaw hf hf1 hflocal hC' hC't
      (by simpa using hd) (by simpa using ha) (by simpa using (show m ≤ d by omega))
      (by omega : 1 ≤ q-1) (by omega : q-1+m ≤ a) (measurable_haltRoute hτ n m j)
    have he : stoppedContinuation τ w n k j = blockValue f (haltRoute τ n m j) := by
      funext s
      simpa [f,Nat.add_sub_of_le hmk] using stoppedContinuation_unroll hτ n m (k-m) j s
    rw [he]
    intro z r hr
    apply (hb z r hr).trans
    apply mul_le_mul' _ le_rfl
    have hdiv : (k+q-1)/q = (k-m+q-1)/q+1 := by
      by_cases hqk : q ≤ k
      · have hme : m = q := min_eq_right hqk
        rw [hme]
        have he : k+q-1 = q+(k-q+q-1) := by omega
        rw [he,Nat.add_div_left _ hq0]
      · have hme : m = k := min_eq_left (by omega)
        rw [hme,Nat.sub_self,Nat.zero_add,Nat.div_eq_of_lt (by omega : q-1 < q)]
        have he : k+q-1 = q+(k-1) := by omega
        rw [he,Nat.add_div_left _ hq0,Nat.div_eq_of_lt (by omega : k-1 < q)]
    rw [hden]
    have hcard : (Fintype.card (TaggedState M m):ℝ≥0∞)^(1/(q:ℝ)) ≤
        (Fintype.card (TaggedState M q):ℝ≥0∞)^(1/(q:ℝ)) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      exact_mod_cast (show Fintype.card (TaggedState M m) ≤ Fintype.card (TaggedState M q) by
        rw [card_taggedState,card_taggedState]
        exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hm 2))
    calc
      _ ≤ K*C' := mul_le_mul' (mul_le_mul' le_rfl hcard) le_rfl
      _ = _ := by rw [hdiv,pow_succ]; dsimp [C']; ring

end

variable {d M T : ℕ}

def taggedWeight (w : ℕ → State M → Vector d → ℝ≥0∞) (n : ℕ) : TaggedState M T → Vector d → ℝ≥0∞
  | .inl j => w n j
  | .inr (t,j) => w t j

lemma measurable_taggedWeight {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hw : ∀ n j, Measurable (w n j)) (n : ℕ) (j : TaggedState M T) :
    Measurable (taggedWeight w n j) := by cases j <;> exact hw _ _

lemma continuation_tagged_eq {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (n k : ℕ) (hnk : n+k ≤ T) (j : TaggedState M T) (s : Vector d) :
    continuation (taggedStep τ) (taggedWeight w) n k j s =
      match j with
      | .inl a => stoppedContinuation τ w n k a s
      | .inr (t,a) => w t a s := by
  induction k generalizing n j with
  | zero => cases j <;> rfl
  | succ k ih =>
    cases j with
    | inl j =>
      simp only [continuation,stoppedContinuation]
      apply lintegral_congr
      intro x
      rw [ih (n+1) (by omega)]
      simp only [taggedStep,dite_eq_left (by omega : n+1 ≤ T)]
      split_ifs <;> rfl
    | inr done =>
      simp only [continuation,taggedStep]
      simp only [ih (n+1) (by omega),lintegral_const,measure_univ,mul_one]

lemma tagged_continuation_mass {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hτ : ∀ t j, Measurable (τ t j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (ambientSphereLaw.withDensity (w n j)) a C)
    (hd : 1 ≤ d) (ha : a ≤ d) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (j : TaggedState M T) :
    PolynomialMass (ambientSphereLaw.withDensity
      (continuation (taggedStep τ) (taggedWeight w) 0 T j)) a
      (C * streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q)) := by
  have he := fun s => continuation_tagged_eq (τ := τ) (w := w) 0 T (by omega) j s
  cases j with
  | inl j =>
    have he' : continuation (taggedStep (T := T) τ) (taggedWeight w) 0 T (.inl j) = stoppedContinuation τ w 0 T j :=
      funext he
    rw [he']
    exact stoppedContinuation_mass_bound hτ hw hw1 hC hCt hlocal hd ha hq hqa 0 T j
  | inr done =>
    have he' : continuation (taggedStep (T := T) τ) (taggedWeight w) 0 T (.inr done) = w done.1 done.2 :=
      funext he
    rw [he']
    intro z r hr
    apply (hlocal _ _ z r hr).trans
    apply mul_le_mul' _ le_rfl
    exact le_mul_of_one_le_right' (one_le_pow₀ (one_le_streamFactor (by omega)))

variable [NeZero d]

lemma stopped_route_mixed_bound {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (hτ : ∀ t j, Measurable (τ t j)) (y : ℕ → State M → Vector d)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (j : TaggedState M T) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | dist z.1.val
        (match streamRoute (taggedStep (T := T) τ) 0 T j (z.2,fun i => ⟪z.1.val,z.2 i⟫) with
        | .inl a => y T a
        | .inr (t,a) => y t a) ≤ ε} ≤
      (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q) := by
  let w : ℕ → State M → Vector d → ℝ≥0∞ := fun n j => capWeight (y n j) ε
  let δ := taggedStep (T := T) τ
  let w' : ℕ → TaggedState M T → Vector d → ℝ≥0∞ := taggedWeight w
  let yy : TaggedState M T → Vector d := fun a => match a with
    | .inl a => y T a
    | .inr (t,a) => y t a
  have hw' (n : ℕ) (a : TaggedState M T) : Measurable (w' n a) :=
    measurable_taggedWeight (fun n j => measurable_capWeight _ _) n a
  have hδ := measurable_taggedStep (T := T) hτ
  have hV := measurable_continuation hδ hw' 0 T j
  have he (s : Vector d) : continuation δ w' 0 T j s =
      ∫⁻ A : Fin T → Vector d, capWeight (yy (streamRoute δ 0 T j (A,fun i => ⟪s,A i⟫))) ε s
        ∂Measure.pi (fun _ => stdGaussian (Vector d)) := by
    have hu := continuation_unroll (w := w') hδ 0 T 0 j s
    simp only [Nat.add_zero,continuation] at hu
    rw [hu]
    unfold blockValue
    apply lintegral_congr
    intro A
    cases streamRoute δ 0 T j (A,fun i => ⟪s,A i⟫) <;> simp [w',w,yy,taggedWeight]
  let S : Set (UnitSphere d × Samples d T) :=
    {z | dist z.1.val (yy (streamRoute δ 0 T j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε}
  have hS : MeasurableSet S := by
    apply measurableSet_le _ measurable_const
    exact (measurable_subtype_coe.comp measurable_fst).dist
      ((measurable_of_finite yy).comp ((measurable_streamRoute hδ 0 T j).comp (by fun_prop)))
  change ((sphereLaw (E := Vector d)).prod _) S ≤ _
  rw [← one_mul (((sphereLaw (E := Vector d)).prod _) S), ← lintegral_indicator_const hS 1,
    lintegral_prod _ (measurable_const.indicator hS).aemeasurable]
  have hf : ∀ s : UnitSphere d,
      (∫⁻ A, S.indicator (fun _ => (1:ℝ≥0∞)) (s,A) ∂sampleLaw d T) = continuation δ w' 0 T j s.val := by
    intro s
    rw [he]
    apply lintegral_congr
    intro A
    classical
    change (if dist s.val (yy (streamRoute δ 0 T j (A,fun i => ⟪s.val,A i⟫))) ≤ ε then 1 else 0) = _
    unfold capWeight
    rw [Set.indicator_apply]
    rfl
  simp_rw [hf]
  rw [← lintegral_map hV measurable_subtype_coe]
  apply ambient_mass_bound (a := a)
  have ha : a ≤ d := by
    have hdn : ((d-1:ℕ):ℝ) ≤ (d:ℝ) := by exact_mod_cast Nat.sub_le d 1
    have : (a:ℝ) ≤ d := by linarith
    exact_mod_cast this
  have hl (n : ℕ) (j : State M) : PolynomialMass (ambientSphereLaw.withDensity (w n j)) a
      (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal (ε^b)) := by
    simpa only [finrank_euclideanSpace_fin] using capWeight_mass_mixed (y n j) hε hε1 a hb (by simpa using hab)
  exact tagged_continuation_mass hτ (fun n j => measurable_capWeight _ _)
    (fun n j s => capWeight_le_one _ _ _)
    (mul_ne_zero (by positivity) (by positivity))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    hl
    (Nat.pos_of_ne_zero (NeZero.ne d)) ha hq hqa j

end Learner
end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
namespace Learner

theorem riesz_success :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
      ∀ L : Learner d M T Ω, L.Admissible ρ →
      let q := d/8
      let W : ℝ := ((T:ℝ)+2)*2^M
      L.uniformSuccess ρ ε ≤ ENNReal.ofReal
        (C₀^d*ε^((d:ℝ)/2-1)*(1+C₀^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)))^((T+q-1)/q)) := by
  refine ⟨32768,by norm_num,?_⟩
  intro d M T hd ε hε hε10 Ω _ ρ hρ L hL q W
  let : IsProbabilityMeasure ρ := hρ
  let a := (d-1)/2
  have hq : 2 ≤ q := by dsimp [q]; omega
  have ha : 2*a ≤ d-1 := by dsimp [a]; omega
  have hqa : 2*q ≤ a := by dsimp [a,q]; omega
  have hb := L.streaming_success_bound_tagged ρ hL (by omega) hε ha hq hqa
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hqn : 0 ≤ 1/(q:ℝ) := by positivity
  have he : ((T+2)*2^M:ℝ≥0∞)^(1/(q:ℝ)) = ENNReal.ofReal (W^(1/(q:ℝ))) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hW hqn]
    congr 1
    dsimp [W]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (T:ℝ)+2),
      ENNReal.ofReal_add (by positivity : 0 ≤ (T:ℝ)) (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
  have hfactor : streamFactor (E := Vector d) (J := TaggedState M T) q =
      ENNReal.ofReal ((32768:ℝ)^d*W^(1/(q:ℝ))) := by
    unfold streamFactor
    rw [finrank_euclideanSpace_fin,card_taggedState,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,he]
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_ofNat]
  rw [hfactor, ← ENNReal.ofReal_pow (by positivity : 0 ≤ (32768:ℝ)^d*W^(1/(q:ℝ))),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d*ε^a)] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hε1 : ε ≤ 1 := by linarith
  have hexp : (d:ℝ)/2-1 ≤ a := by
    have hh : d-1 ≤ 2*a+1 := by dsimp [a]; omega
    have hd1 : 1 ≤ d := by omega
    have hh' : (d:ℝ) ≤ 2*(a:ℝ)+2 := by
      exact_mod_cast (show d ≤ 2*a+2 by omega)
    linarith
  have heps : ε^a ≤ ε^((d:ℝ)/2-1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1 hexp
  have hconst : (3:ℝ)*4^d ≤ (32768:ℝ)^d := by
    have hp' : (3:ℝ)^1 ≤ 3^d := pow_le_pow_right₀ (by norm_num) (by omega)
    have hsmall : (12:ℝ)^d ≤ (32768:ℝ)^d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
    calc
      (3:ℝ)*4^d ≤ 3^d*4^d := mul_le_mul_of_nonneg_right (by simpa using hp') (by positivity)
      _ = 12^d := by rw [← mul_pow]; norm_num
      _ ≤ _ := hsmall
  have hlog : 0 ≤ Real.log (1/ε) := Real.log_nonneg ((one_le_div hε).mpr hε1)
  have hstep : (32768:ℝ)^d*W^(1/(q:ℝ)) ≤
      1+(32768:ℝ)^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)) := by
    have hm : (32768:ℝ)^d*W^(1/(q:ℝ)) ≤
        (32768:ℝ)^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hW _)
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 32768) d]
    linarith
  exact mul_le_mul (mul_le_mul hconst heps (by positivity) (by positivity))
    (pow_le_pow_left₀ (by positivity) hstep _) (by positivity) (by positivity)

end Learner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma prefix_route_mixed_bound
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]
    {δ : ℕ → J → (E × ℝ) → J} (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (Module.finrank ℝ E-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) {k T : ℕ} (hk : k ≤ T) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin T => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j
        ((fun i => z.2 (Fin.castLE hk i)),fun i => ⟪z.1.val,z.2 (Fin.castLE hk i)⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3:ℝ)*4^Module.finrank ℝ E)*ENNReal.ofReal (ε^b)) *
        streamFactor (E := E) (J := J) q ^ ((k+q-1)/q) := by
  have hp := (MeasurePreserving.id (sphereLaw (E := E))).prod
    (measurePreserving_pi_prefix (stdGaussian E) hk)
  have hs : MeasurableSet
      {z : (Metric.sphere (0:E) 1) × (Fin k → E) |
        dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} := by
    apply measurableSet_le _ measurable_const
    exact (measurable_subtype_coe.comp measurable_fst).dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  apply (le_of_eq (hp.measure_preimage hs.nullMeasurableSet)).trans
  exact route_mixed_bound hδ y hε hε1 hb hab hq hqa k j

namespace Learner
variable {d M T : ℕ} {Ω : Type u}

lemma terminal_eq_forced_of_index (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω)
    (x : Samples d T) {t : ℕ} (ht : (L.terminal s ω x).1 = t) :
    L.terminal s ω x = (t,L.forcedRun s ω x t) := by
  rcases L.terminal_forced_witness s ω x with ⟨t',ht',he⟩
  have h : t' = t := (congrArg Prod.fst he).symm.trans ht
  subst t'
  exact he

lemma frozen_fixed_success_bound (L : Learner d M T Ω) (ω : Ω) (hd : 3 ≤ d)
    (htrans : ∀ t j, AEMeasurable (fun obs => (L.transition t ω j obs).2) (observationReference d))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) {t : ℕ} (ht : t ≤ T) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | (L.terminal z.1 ω z.2).1 = t ∧ angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤
      (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := State M) q ^ ((t+q-1)/q) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let δ : ℕ → State M → (Vector d × ℝ) → State M := fun t j => (htrans t j).mk _
  have hδ (t : ℕ) (j : State M) : Measurable (δ t j) := (htrans t j).measurable_mk
  let μ := (uniformSphere d).prod (sampleLaw d T)
  have hgood : ∀ᵐ z ∂μ, ∀ t j (i : Fin T),
      (L.transition t ω j (z.2 i,⟪z.1.val,z.2 i⟫)).2 = δ t j (z.2 i,⟪z.1.val,z.2 i⟫) := by
    simp only [ae_all_iff]
    intro t j i
    exact (sphere_sample_observation_quasi (by simpa using hd) i).ae (htrans t j).ae_eq_mk
  let S := {z : UnitSphere d × Samples d T |
    dist z.1.val (L.output t ω (streamRoute δ 0 t (L.initialChoice ω).2
      ((fun i => z.2 (Fin.castLE ht i)),fun i => ⟪z.1.val,z.2 (Fin.castLE ht i)⟫))).val ≤ ε}
  have hmono : {z : UnitSphere d × Samples d T |
      (L.terminal z.1 ω z.2).1 = t ∧ angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤ᵐ[μ] S := by
    filter_upwards [hgood] with z hz
    rintro ⟨hzt,hs⟩
    have he := L.terminal_eq_forced_of_index z.1 ω z.2 hzt
    have hf : L.forcedRun z.1 ω z.2 t = streamRoute δ 0 t (L.initialChoice ω).2
        ((fun i => z.2 (Fin.castLE ht i)),fun i => ⟪z.1.val,z.2 (Fin.castLE ht i)⟫) := by
      rw [L.forcedRun_eq_route z.1 ω z.2 ht]
      exact streamRoute_congr _ _ 0 t _ _ _ (fun n j i => hz n j (Fin.castLE ht i))
    have hc : dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε := by
      apply le_trans _ hs
      simpa only [angularError,dist_comm] using chord_le_arccos (L.estimate z.1 ω z.2) z.1
    change dist z.1.val _ ≤ ε
    simpa only [estimate,he,hf] using hc
  apply (measure_mono_ae hmono).trans
  simpa only [S,μ,uniformSphere,sphereLaw,sampleLaw,finrank_euclideanSpace_fin] using
    prefix_route_mixed_bound hδ (fun j => (L.output t ω j).val) hε hε1 hb (by simpa using hab)
      hq hqa ht (L.initialChoice ω).2

lemma streaming_fixed_success_bound [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ)
    (hstop : AEMeasurable (fun z : UnitSphere d × (Ω × Samples d T) =>
      (L.terminal z.1 z.2.1 z.2.2).1) ((uniformSphere d).prod (ρ.prod (sampleLaw d T))))
    (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) {t : ℕ} (ht : t ≤ T) :
    L.uniformFixedSuccess ρ ε t ≤
      (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := State M) q ^ ((t+q-1)/q) := by
  let : NeZero d := ⟨by omega⟩
  let : SigmaFinite (observationReference d) := by unfold observationReference; infer_instance
  have hω : ∀ᵐ ω ∂ρ, ∀ t j,
      AEMeasurable (fun obs => (L.transition t ω j obs).2) (observationReference d) := by
    simp only [ae_all_iff]
    intro t j
    filter_upwards [ae_fiber_aemeasurable (hL.transition t j).prod_swap] with ω hω
    exact measurable_snd.comp_aemeasurable hω
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d T) |
    (L.terminal z.1 z.2.1 z.2.2).1 = t ∧ angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    (nullMeasurableSet_eq_fun hstop aemeasurable_const).inter (L.angularSuccess_nullMeasurable ρ ε hL)
  have he := hp.measure_preimage hS
  have hbound := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal (ε^b)) *
      streamFactor (E := Vector d) (J := State M) q ^ ((t+q-1)/q))
    (by
      filter_upwards [hω] with ω hω
      exact L.frozen_fixed_success_bound ω hd hω hε hε1 hb hab hq hqa ht)
  simpa only [he,measure_univ,mul_one,S,uniformFixedSuccess] using hbound

end Learner
end

lemma streamFactor_ofReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {J : Type*} [Fintype J] (q : ℕ) :
    streamFactor (E := E) (J := J) q = ENNReal.ofReal
      ((32768:ℝ)^Module.finrank ℝ E*(Fintype.card J:ℝ)^(1/(q:ℝ))) := by
  unfold streamFactor
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by positivity : 0 ≤ 1/(q:ℝ)),
    ENNReal.ofReal_natCast]

lemma three_mul_four_pow_le (d : ℕ) (hd : 1 ≤ d) : (3:ℝ)*4^d ≤ (32768:ℝ)^d := by
  have hp : (3:ℝ)^1 ≤ 3^d := pow_le_pow_right₀ (by norm_num) hd
  calc
    (3:ℝ)*4^d ≤ 3^d*4^d := mul_le_mul_of_nonneg_right (by simpa using hp) (by positivity)
    _ = 12^d := by rw [← mul_pow]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num) d

namespace Learner

section

theorem cap_fixed_stop :
    ∃ C : ℝ, 0 < C ∧ ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
      ∀ L : Learner d M T Ω, L.Admissible ρ →
      AEMeasurable (fun z : UnitSphere d × (Ω × Samples d T) =>
        (L.terminal z.1 z.2.1 z.2.2).1) ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) →
      ∀ t : ℕ, t ≤ T →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      L.uniformFixedSuccess ρ ε t ≤ ENNReal.ofReal
        (Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((t+k-1)/k)) := by
  refine ⟨Real.log 65536,Real.log_pos (by norm_num),?_⟩
  intro d M T hd ε hε hε10 Ω _ ρ hρ L hL hstop t ht k α
  let : IsProbabilityMeasure ρ := hρ
  let a := (d-1)/2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hka : 2*k ≤ a := by dsimp [k,a]; omega
  have hα : 0 ≤ α := by
    dsimp [α]
    have hdR : (32:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hαd : α ≤ (d:ℝ) := by
    dsimp [α]
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hab : (a:ℝ)+α ≤ (d-1:ℕ) := by
    have hh : (2:ℝ)*a ≤ (d-1:ℕ) := by exact_mod_cast (show 2*a ≤ d-1 by dsimp [a]; omega)
    rw [Nat.cast_sub (by omega : 1 ≤ d),Nat.cast_one] at hh ⊢
    dsimp [α]; linarith
  have hb := L.streaming_fixed_success_bound ρ hL hstop (by omega) hε (by linarith)
    hα hab hk hka ht
  have he : Real.exp (Real.log 65536*(d:ℝ)) = (65536:ℝ)^d := by
    rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by norm_num)]
  rw [he]
  rw [streamFactor_ofReal,finrank_euclideanSpace_fin,Fintype.card_fin,
    Nat.cast_pow,Nat.cast_ofNat] at hb
  have hroot : ((2:ℝ)^M)^(1/(k:ℝ)) = (2:ℝ)^((M:ℝ)/k) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num)]
    congr 1; ring
  rw [hroot, ← ENNReal.ofReal_pow (by positivity : 0 ≤ (32768:ℝ)^d*(2:ℝ)^((M:ℝ)/k)),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d*ε^α)] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hbase : (3:ℝ)*4^d*ε^α ≤ (65536:ℝ)^d*(ε/2)^α := by
    have heps : ε^α = 2^α*(ε/2)^α := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : 0 ≤ ε/2)]
      congr 1; ring
    rw [heps,← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      (3:ℝ)*4^d*2^α ≤ (32768:ℝ)^d*(2:ℝ)^d := by
        apply mul_le_mul (three_mul_four_pow_le d (by omega)) _ (by positivity) (by positivity)
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hαd
      _ = 65536^d := by rw [← mul_pow]; norm_num
  apply mul_le_mul hbase _ (by positivity) (by positivity)
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) d) (by positivity)) _

end

variable {d M T : ℕ} {Ω : Type u}

lemma frozen_success_bound_local (L : Learner d M T Ω) (ω : Ω) (hd : 3 ≤ d)
    (htrans : ∀ t j, AEMeasurable (L.transition t ω j) (observationReference d))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ)) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let τ : ℕ → State M → (Vector d × ℝ) → Bool × State M := fun t j => (htrans t j).mk _
  have hτ (t : ℕ) (j : State M) : Measurable (τ t j) := (htrans t j).measurable_mk
  let μ := (uniformSphere d).prod (sampleLaw d T)
  have hgood : ∀ᵐ z ∂μ, ∀ t j (i : Fin T),
      L.transition t ω j (z.2 i,⟪z.1.val,z.2 i⟫) = τ t j (z.2 i,⟪z.1.val,z.2 i⟫) := by
    simp only [ae_all_iff]
    intro t j i
    exact (sphere_sample_observation_quasi (by simpa using hd) i).ae (htrans t j).ae_eq_mk
  let S := {z : UnitSphere d × Samples d T | dist z.1.val
    (L.taggedOutput ω (streamRoute (taggedStep (T := T) τ) 0 T (taggedStart (L.initialChoice ω))
      (z.2,fun i => ⟪z.1.val,z.2 i⟫))).val ≤ ε}
  have hmono : {z : UnitSphere d × Samples d T | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε}
      ≤ᵐ[μ] S := by
    filter_upwards [hgood] with z hz
    intro hs
    have he := streamRoute_congr (taggedStep (T := T) (fun t j => L.transition t ω j))
      (taggedStep (T := T) τ) 0 T (taggedStart (L.initialChoice ω)) z.2
      (fun i => ⟪z.1.val,z.2 i⟫) (fun t j i => taggedStep_congr t j _ (fun a => hz t a i))
    have hc : dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε := by
      apply le_trans _ hs
      simpa only [angularError,dist_comm] using chord_le_arccos (L.estimate z.1 ω z.2) z.1
    change dist z.1.val _ ≤ ε
    rw [L.estimate_eq_taggedRoute,he] at hc
    exact hc
  apply (measure_mono_ae hmono).trans
  have hy (a : TaggedState M T) : (L.taggedOutput ω a).val =
      (match a with | .inl a => (L.output T ω a).val | .inr (t,a) => (L.output t ω a).val) := by
    cases a <;> rfl
  have hh := stopped_route_mixed_bound hτ (fun t j => (L.output t ω j).val) hε hε1 hb hab hq hqa
    (T := T) (taggedStart (L.initialChoice ω))
  have hset : S = {z : UnitSphere d × Samples d T | dist z.1.val
      (match streamRoute (taggedStep (T := T) τ) 0 T (taggedStart (L.initialChoice ω))
        (z.2,fun i => ⟪z.1.val,z.2 i⟫) with
      | .inl a => (L.output T ω a).val | .inr (t,a) => (L.output t ω a).val) ≤ ε} := by
    ext z
    change (dist z.1.val (L.taggedOutput ω _).val ≤ ε) ↔ _
    rw [hy]
    rfl
  rw [hset]
  exact hh

lemma streaming_success_bound_local [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {a q : ℕ} {b : ℝ} (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ)) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q) := by
  let : NeZero d := ⟨by omega⟩
  let : SigmaFinite (observationReference d) := by unfold observationReference; infer_instance
  have hω : ∀ᵐ ω ∂ρ, ∀ t j,
      AEMeasurable (L.transition t ω j) (observationReference d) := by
    simp only [ae_all_iff]
    intro t j
    exact ae_fiber_aemeasurable (hL.transition t j).prod_swap
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d T) |
    angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    L.angularSuccess_nullMeasurable ρ ε hL
  have he := hp.measure_preimage hS
  have hb := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^b)) *
      streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q))
    (by
      filter_upwards [hω] with ω hω
      exact L.frozen_success_bound_local ω hd hω hε hε1 hb hab hq hqa)
  simpa only [he,measure_univ,mul_one,S,uniformSuccess] using hb

theorem haar_success :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
      ∀ L : Learner d M T Ω, L.Admissible ρ →
      let k := d/4
      let Nstar : ℝ := ((k:ℝ)+2)*2^M
      L.uniformSuccess ρ ε ≤ ENNReal.ofReal
        (C^d*ε^k*(C^d*Nstar^(1/(k:ℝ)))^((T+k-1)/k)) := by
  refine ⟨32768,by norm_num,?_⟩
  intro d M T hd ε hε hε10 Ω _ ρ hρ L hL k Nstar
  let : IsProbabilityMeasure ρ := hρ
  let a := d-1-k
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hka : 2*k ≤ a := by dsimp [k,a]; omega
  have hab : (a:ℝ)+(k:ℝ) ≤ (d-1:ℕ) := by
    exact_mod_cast (show a+k ≤ d-1 by dsimp [a,k]; omega)
  have hb := L.streaming_success_bound_local ρ hL (by omega) hε (by linarith)
    (Nat.cast_nonneg k) hab hk hka
  have hcard : (Fintype.card (TaggedState M k):ℝ) = Nstar := by
    rw [card_taggedState]; simp [Nstar,Nat.cast_mul,Nat.cast_add,Nat.cast_pow]
  rw [Real.rpow_natCast,streamFactor_ofReal,finrank_euclideanSpace_fin,hcard,
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ (32768:ℝ)^d*Nstar^(1/(k:ℝ))),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d*ε^k)] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (three_mul_four_pow_le d (by omega)) (by positivity)) (by positivity)

end Learner
end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace FiniteKernelLearner

section
open Learner
variable {d M T : ℕ}

lemma Realizer.uniform_event_law [NeZero d] {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (S : Set (UnitSphere d × Result d M)) (hS : MeasurableSet S) :
    ((uniformSphere d).prod (K.tapeLaw.prod (sampleLaw d T)))
      {z | (z.1,(R.toLearner.terminal z.1 z.2.1 z.2.2,R.toLearner.estimate z.1 z.2.1 z.2.2)) ∈ S} =
    ∫⁻ z : UnitSphere d × Samples d T,
      K.jointExperimentLaw (fun i => (z.2 i,⟪z.1.val,z.2 i⟫))
        {r | (z.1,r) ∈ S} ∂((uniformSphere d).prod (sampleLaw d T)) := by
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := K.tapeLaw))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) K.tapeLaw)
  have hE : MeasurableSet {z : UnitSphere d × (Tape M T × Samples d T) |
      (z.1,(R.toLearner.terminal z.1 z.2.1 z.2.2,R.toLearner.estimate z.1 z.2.1 z.2.2)) ∈ S} :=
    (measurable_fst.prodMk ((R.toLearner.measurable_terminal R.measurableRules).prodMk
      (R.toLearner.measurable_estimate R.measurableRules))) hS
  rw [← hp.measure_preimage hE.nullMeasurableSet,Measure.prod_apply (hp.measurable hE)]
  apply lintegral_congr
  intro z
  have hs : MeasurableSet {r : Result d M | (z.1,r) ∈ S} :=
    (measurable_const.prodMk measurable_id) hS
  rw [←R.conditional_joint_law z.1 z.2,Measure.map_apply _ hs]
  · rfl
  · exact ((R.toLearner.measurable_terminal R.measurableRules).prodMk
      (R.toLearner.measurable_estimate R.measurableRules)).comp
        (show Measurable (fun ω : Tape M T => (z.1,(ω,z.2))) from by fun_prop)

lemma Realizer.uniformSuccess_eq [NeZero d] {K : FiniteKernelLearner d M T} (R : K.Realizer) (ε : ℝ) :
    R.toLearner.uniformSuccess K.tapeLaw ε = K.uniformSuccess ε := by
  exact R.uniform_event_law {z | angularError z.1 z.2.2 ≤ ε}
    (measurableSet_le (show Measurable (fun z : UnitSphere d × Result d M => angularError z.1 z.2.2) from by unfold angularError; fun_prop) measurable_const)

lemma Realizer.uniformFixedSuccess_eq [NeZero d] {K : FiniteKernelLearner d M T} (R : K.Realizer) (ε : ℝ) (t : ℕ) :
    R.toLearner.uniformFixedSuccess K.tapeLaw ε t = K.uniformFixedSuccess ε t := by
  exact R.uniform_event_law {z | z.2.1.1 = t ∧ angularError z.1 z.2.2 ≤ ε}
    ((measurableSet_eq_fun (show Measurable (fun z : UnitSphere d × Result d M => z.2.1.1) from by fun_prop) measurable_const).inter
      (measurableSet_le (show Measurable (fun z : UnitSphere d × Result d M => angularError z.1 z.2.2) from by unfold angularError; fun_prop) measurable_const))

lemma jointExperimentLaw_congr {K K' : FiniteKernelLearner d M T}
    (hi : K.initial = K'.initial) (ho : K.output = K'.output)
    (obs : Fin T → (Vector d × ℝ))
    (ht : ∀ t j i, K.transition t j (obs i) = K'.transition t j (obs i)) :
    K.jointExperimentLaw obs = K'.jointExperimentLaw obs := by
  have htag : ∀ t j i, K.taggedKernel t j (obs i) = K'.taggedKernel t j (obs i) := by
    intro t j i
    cases j with
    | inr a => rfl
    | inl j => simp only [taggedKernel,ht]
  have hout : K.terminalJointOutput = K'.terminalJointOutput := by
    funext j
    unfold terminalJointOutput
    congr 1
    cases j with
    | inl j => exact congrFun (congrFun ho T) j
    | inr a => exact congrFun (congrFun ho a.1) a.2
  unfold jointExperimentLaw
  rw [hi,hout]
  congr 1
  funext a
  rw [kernelRun_congr T (taggedStart a) obs htag]

lemma exists_borel_same_joint (K : FiniteKernelLearner d M T) (hK : K.CompletedRules) (hd : 3 ≤ d) :
    ∃ K' : FiniteKernelLearner d M T, K'.BorelRules ∧
      ∀ᵐ z ∂((uniformSphere d).prod (sampleLaw d T)),
        K.jointExperimentLaw (fun i => (z.2 i,⟪z.1.val,z.2 i⟫)) =
        K'.jointExperimentLaw (fun i => (z.2 i,⟪z.1.val,z.2 i⟫)) := by
  obtain ⟨K',hK',hi,ho,ht⟩ := K.exists_borel_version hK
  refine ⟨K',hK',?_⟩
  let : NeZero d := ⟨by omega⟩
  have hg : ∀ᵐ z ∂((uniformSphere d).prod (sampleLaw d T)), ∀ t j (i : Fin T),
      K.transition t j (z.2 i,⟪z.1.val,z.2 i⟫) = K'.transition t j (z.2 i,⟪z.1.val,z.2 i⟫) := by
    simp only [ae_all_iff]
    intro t j i
    exact (sphere_sample_observation_quasi (E := Vector d) (by simpa using hd) i).ae (ht t j).symm
  filter_upwards [hg] with z hz
  exact jointExperimentLaw_congr hi.symm ho.symm _ hz

theorem exists_equivalent_tape (K : FiniteKernelLearner d M T) (hK : K.CompletedRules) (hd : 3 ≤ d) :
    ∃ (ρ : Measure (Tape M T)) (L : Learner d M T (Tape M T)),
      IsProbabilityMeasure ρ ∧ L.MeasurableRules ∧ L.Admissible ρ ∧
      (∀ ε, L.uniformSuccess ρ ε = K.uniformSuccess ε) ∧
      (∀ ε t, L.uniformFixedSuccess ρ ε t = K.uniformFixedSuccess ε t) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨K',hK',he⟩ := K.exists_borel_same_joint hK hd
  let R := Classical.choice (K'.exists_realizer hK')
  refine ⟨K'.tapeLaw,R.toLearner,inferInstance,R.measurableRules,
    R.toLearner.admissible_of_measurable R.measurableRules K'.tapeLaw,?_,?_⟩
  · intro ε
    rw [R.uniformSuccess_eq]
    apply lintegral_congr_ae
    filter_upwards [he] with z hz
    rw [hz]
  · intro ε t
    rw [R.uniformFixedSuccess_eq]
    apply lintegral_congr_ae
    filter_upwards [he] with z hz
    rw [hz]

end

variable {d M T : ℕ}

lemma seed_average_bound {Ξ : Type u} [MeasurableSpace Ξ] (ρ : Measure Ξ)
    [IsProbabilityMeasure ρ] {f : Ξ → ℝ≥0∞} {C : ℝ≥0∞}
    (h : ∀ᵐ ξ ∂ρ, f ξ ≤ C) : ∫⁻ ξ, f ξ ∂ρ ≤ C := by
  calc
    _ ≤ ∫⁻ _, C ∂ρ := lintegral_mono_ae h
    _ = C := by simp

lemma exists_successful_seed {Ξ : Type u} [MeasurableSpace Ξ] (ρ : Measure Ξ)
    [IsProbabilityMeasure ρ] {P : Ξ → Prop} (hP : ∀ᵐ ξ ∂ρ, P ξ)
    {f : Ξ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (hs : c ≤ ∫⁻ ξ, f ξ ∂ρ) :
    ∃ ξ, P ξ ∧ c ≤ f ξ := by
  by_contra h
  have hlt : ∀ᵐ ξ ∂ρ, f ξ < c := by
    filter_upwards [hP] with ξ hξ
    exact lt_of_not_ge (fun hf => h ⟨ξ,hξ,hf⟩)
  have hbound : ∫⁻ ξ, f ξ ∂ρ ≤ c := seed_average_bound ρ (ae_le_of_ae_lt hlt)
  have hstrict := lintegral_strict_mono (show ρ ≠ 0 from by
    intro he; have hh := measure_univ (μ := ρ); rw [he] at hh; simp at hh)
    (aemeasurable_const (b := c)) (ne_top_of_le_ne_top hc hbound) hlt
  have hh : ∫⁻ ξ, f ξ ∂ρ < c := by simpa using hstrict
  exact not_lt_of_ge hs hh

theorem riesz_success :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let q := d/8
      let W : ℝ := ((T:ℝ)+2)*2^M
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (C₀^d*ε^((d:ℝ)/2-1)*(1+C₀^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)))^((T+q-1)/q)) := by
  obtain ⟨C,hC,h⟩ := Learner.riesz_success.{0}
  refine ⟨C,hC,?_⟩
  intro d M T hd ε hε hε10 Ξ _ ρ hρ K hK q W
  let : IsProbabilityMeasure ρ := hρ
  apply seed_average_bound
  filter_upwards [hK] with ξ hξ
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  rw [←he ε]
  exact h d M T hd ε hε hε10 (Tape M T) ν hν L hL

theorem haar_success :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let k := d/4
      let Nstar : ℝ := ((k:ℝ)+2)*2^M
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (C^d*ε^k*(C^d*Nstar^(1/(k:ℝ)))^((T+k-1)/k)) := by
  obtain ⟨C,hC,h⟩ := Learner.haar_success.{0}
  refine ⟨C,hC,?_⟩
  intro d M T hd ε hε hε10 Ξ _ ρ hρ K hK k Nstar
  let : IsProbabilityMeasure ρ := hρ
  apply seed_average_bound
  filter_upwards [hK] with ξ hξ
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  rw [←he ε]
  exact h d M T hd ε hε hε10 (Tape M T) ν hν L hL

theorem cap_fixed_stop :
    ∃ C : ℝ, 0 < C ∧ ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      ∀ t : ℕ, t ≤ T →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      seededFixedSuccess K ρ ε t ≤ ENNReal.ofReal
        (Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((t+k-1)/k)) := by
  obtain ⟨C,hC,h⟩ := Learner.cap_fixed_stop.{0}
  refine ⟨C,hC,?_⟩
  intro d M T hd ε hε hε10 Ξ _ ρ hρ K hK t ht k α
  let : IsProbabilityMeasure ρ := hρ
  apply seed_average_bound
  filter_upwards [hK] with ξ hξ
  obtain ⟨ν,L,hν,hB,hL,_,he⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  rw [←he ε t]
  exact h d M T hd ε hε hε10 (Tape M T) ν hν L hL
    (L.measurable_terminal hB).fst.aemeasurable t ht

theorem fixed_quadratic_memory : FixedQuadraticMemory.{u} := by
  intro A hA
  obtain ⟨c,hc,d₀,h⟩ := NoiselessRegression.fixed_quadratic_memory.{0} A hA
  refine ⟨c,hc,max d₀ 3,?_⟩
  intro d hd M T hM ε hε hε10 Ξ _ ρ hρ K hK hs
  let : IsProbabilityMeasure ρ := hρ
  obtain ⟨ξ,hξ,hsξ⟩ := exists_successful_seed ρ hK (ENNReal.div_ne_top (by norm_num) (by norm_num) : (2/3 : ℝ≥0∞) ≠ ∞) hs
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  apply h d (by omega) M T hM ε hε hε10 (Tape M T) ν hν L hL
  rwa [he ε]

def SubquadraticMemory : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d:ℝ)^2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1/10 →
    ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
    ∀ K : Ξ → FiniteKernelLearner d (M d) T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
    (2/3 : ℝ≥0∞) ≤ seededSuccess K ρ ε →
    c*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ)

theorem subquadratic_memory : SubquadraticMemory.{u} := by
  obtain ⟨c,hc,h⟩ := NoiselessRegression.subquadratic_memory.{0}
  refine ⟨c,hc,?_⟩
  intro M hM
  obtain ⟨d₀,hd₀⟩ := h M hM
  refine ⟨max d₀ 3,?_⟩
  intro d hd T ε hε hε10 Ξ _ ρ hρ K hK hs
  let : IsProbabilityMeasure ρ := hρ
  obtain ⟨ξ,hξ,hsξ⟩ := exists_successful_seed ρ hK (ENNReal.div_ne_top (by norm_num) (by norm_num) : (2/3 : ℝ≥0∞) ≠ ∞) hs
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  apply hd₀ d (by omega) T ε hε hε10 (Tape (M d) T) ν hν L hL
  exact Or.inl ((he ε).symm ▸ hsξ)

end FiniteKernelLearner

lemma fresh_seed_kernel_version {X Ξ J : Type*} [MeasurableSpace X]
    [MeasurableSpace Ξ] [Fintype J] [Nonempty J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (μ : Measure X) [SFinite μ]
    (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
    (P : X × Ξ → Measure J) (hP : ∀ z, IsProbabilityMeasure (P z))
    (hm : ∀ j, AEMeasurable (fun z => P z {j}) (μ.prod ρ)) :
    ∃ κ : Kernel X J, IsMarkovKernel κ ∧
      ∀ᵐ x ∂μ, ∀ j, κ x {j} = ∫⁻ ξ, P (x,ξ) {j} ∂ρ := by
  obtain ⟨κ,hκ,he⟩ := finite_kernel_borel_version (μ.prod ρ) P hP hm
  let : IsMarkovKernel κ := hκ
  let η : Kernel X J := κ ∘ₖ ((Kernel.id : Kernel X X) ×ₖ Kernel.const X ρ)
  refine ⟨η,inferInstance,?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod he] with x hx
  intro j
  rw [show η x {j} = ∫⁻ ξ, κ (x,ξ) {j} ∂ρ from ?_]
  · apply lintegral_congr_ae
    filter_upwards [hx] with ξ hξ
    rw [hξ]
  · change (κ ∘ₖ ((Kernel.id : Kernel X X) ×ₖ Kernel.const X ρ)) x {j} = _
    rw [Kernel.comp_apply' _ _ _ (measurableSet_singleton j),Kernel.prod_apply,
      Kernel.id_apply,Kernel.const_apply]
    rw [lintegral_prod _ (κ.measurable_coe (measurableSet_singleton j)).aemeasurable]
    apply lintegral_dirac'
    exact (κ.measurable_coe (measurableSet_singleton j)).lintegral_prod_right

end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace Learner
variable {d M T : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma uniformSuccess_le_sum_fixed (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) :
    L.uniformSuccess ρ ε ≤ ∑ t : Fin (T+1), L.uniformFixedSuccess ρ ε t := by
  classical
  let μ := (uniformSphere d).prod (ρ.prod (sampleLaw d T))
  have hs : {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε} =
      ⋃ t : Fin (T+1), {z | (L.terminal z.1 z.2.1 z.2.2).1 = t ∧
        angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε} := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro hz
      obtain ⟨t,ht,he⟩ := L.terminal_forced_witness z.1 z.2.1 z.2.2
      exact ⟨⟨t,by omega⟩,by simpa [he] using hz⟩
    · rintro ⟨t,ht,hz⟩
      exact hz
  change μ _ ≤ ∑ t : Fin (T+1), μ _
  rw [hs]
  exact (measure_iUnion_le _).trans_eq (tsum_fintype _)

end Learner
namespace FiniteKernelLearner

section

theorem cap_total_success :
    ∃ C : ℝ, 0 < C ∧ ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (((T:ℝ)+1)*Real.exp (C*d)*(ε/2)^α*
          (Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((T+k-1)/k)) := by
  obtain ⟨C,hC,h⟩ := Learner.cap_fixed_stop.{0}
  refine ⟨C,hC,?_⟩
  intro d M T hd ε hε hε10 Ξ _ ρ hρ K hK k α
  let : IsProbabilityMeasure ρ := hρ
  apply seed_average_bound
  filter_upwards [hK] with ξ hξ
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  rw [←he ε]
  have hs := L.uniformSuccess_le_sum_fixed ν ε
  have hbase : 1 ≤ Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity))
      (Real.one_le_rpow (by norm_num) (by positivity))
  apply hs.trans
  calc
    _ ≤ ∑ _t : Fin (T+1), ENNReal.ofReal
        (Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((T+k-1)/k)) := by
      apply Finset.sum_le_sum
      intro t _
      apply (h d M T hd ε hε hε10 (Tape M T) ν hν L hL
        (L.measurable_terminal hB).fst.aemeasurable t (by omega)).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_right₀ hbase (Nat.div_le_div_right (by omega))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
      rw [nsmul_eq_mul, ←ENNReal.ofReal_natCast,
        ←ENNReal.ofReal_mul (by positivity : 0 ≤ ((T+1:ℕ):ℝ))]
      congr 1
      push_cast
      ring

end

section

variable {d M T : ℕ} {Ξ : Type u} [MeasurableSpace Ξ]

lemma seededSuccess_eq_integral_pointwise [NeZero d]
    (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ) [SFinite ρ] (ε : ℝ)
    (hm : JointSuccessMeasurable K ρ ε) :
    seededSuccess K ρ ε = ∫⁻ s, seededPointwiseSuccess K ρ ε s ∂uniformSphere d := by
  let f := fun z : UnitSphere d × (Ξ × Samples d T) =>
    (K z.2.1).conditionalSuccess ε z.1 z.2.2
  let e : ((UnitSphere d × Samples d T) × Ξ) ≃ᵐ UnitSphere d × (Ξ × Samples d T) :=
    MeasurableEquiv.prodAssoc.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.prodComm))
  have hp : MeasurePreserving e (((uniformSphere d).prod (sampleLaw d T)).prod ρ)
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
      (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  have hf : AEMeasurable f ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := hm
  have hfD : AEMeasurable (fun z : (UnitSphere d × Samples d T) × Ξ => f (e z))
      (((uniformSphere d).prod (sampleLaw d T)).prod ρ) :=
    hf.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  calc
    _ = ∫⁻ ξ, ∫⁻ z : UnitSphere d × Samples d T, f (z.1,(ξ,z.2))
          ∂((uniformSphere d).prod (sampleLaw d T)) ∂ρ := rfl
    _ = ∫⁻ z : UnitSphere d × Samples d T, ∫⁻ ξ, f (z.1,(ξ,z.2)) ∂ρ
          ∂((uniformSphere d).prod (sampleLaw d T)) := (lintegral_lintegral_swap hfD).symm
    _ = ∫⁻ z, f (e z) ∂(((uniformSphere d).prod (sampleLaw d T)).prod ρ) :=
      (lintegral_prod _ hfD).symm
    _ = ∫⁻ z, f z ∂((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
      hp.lintegral_comp_emb e.measurableEmbedding f
    _ = _ := lintegral_prod _ hf

lemma seededSuccess_of_pointwise [NeZero d]
    (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ) [SFinite ρ] (ε : ℝ)
    (hm : JointSuccessMeasurable K ρ ε)
    (hs : ∀ s, (2/3 : ℝ≥0∞) ≤ seededPointwiseSuccess K ρ ε s) :
    (2/3 : ℝ≥0∞) ≤ seededSuccess K ρ ε := by
  rw [seededSuccess_eq_integral_pointwise K ρ ε hm]
  calc
    _ = ∫⁻ _ : UnitSphere d, (2/3 : ℝ≥0∞) ∂uniformSphere d := by simp
    _ ≤ _ := lintegral_mono hs

theorem subquadratic_memory_with_pointwise : SubquadraticMemoryWithPointwise.{u} := by
  obtain ⟨c,hc,h⟩ := subquadratic_memory.{u}
  refine ⟨c,hc,?_⟩
  intro M hM
  obtain ⟨d₀,hd₀⟩ := h M hM
  refine ⟨max d₀ 1,?_⟩
  intro d hd T ε hε hε10 Ξ _ ρ hρ K hK hs
  let : IsProbabilityMeasure ρ := hρ
  let : NeZero d := ⟨by omega⟩
  apply hd₀ d (by omega) T ε hε hε10 Ξ ρ hρ K hK
  rcases hs with hs | ⟨hm,hs⟩
  · exact hs
  · exact seededSuccess_of_pointwise K ρ ε hm hs

end


lemma cap_memory_factor (C : ℝ) {d M : ℕ} (hd : 32 ≤ d)
    (hM : (M:ℝ) ≤ (d:ℝ)^2) :
    Real.exp (C*d)*(2:ℝ)^((M:ℝ)/(d/16:ℕ)) ≤ Real.exp ((C+32)*d) := by
  have hk : 0 < (d/16:ℕ) := by omega
  have hkR : (0:ℝ) < (d/16:ℕ) := by exact_mod_cast hk
  have hdk : d ≤ 32*(d/16) := by omega
  have hdkR : (d:ℝ) ≤ 32*(d/16:ℕ) := by exact_mod_cast hdk
  have hfrac : (M:ℝ)/(d/16:ℕ) ≤ 32*d := by
    rw [div_le_iff₀ hkR]
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  rw [Real.rpow_def_of_pos (by norm_num),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hnon : (0:ℝ) ≤ (M:ℝ)/(d/16:ℕ) := by positivity
  have hl := mul_le_mul_of_nonneg_right hlog hnon
  nlinarith

lemma cap_finite_to_asymptotic (C : ℝ) {d M : ℕ} (hd : 32 ≤ d)
    (hM : (M:ℝ) ≤ (d:ℝ)^2) (ε α : ℝ) (n : ℕ) (hε : 0 ≤ ε) :
    Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/(d/16:ℕ)))^n ≤
      Real.exp ((C+32)*d*(1+n))*(ε/2)^α := by
  have hbase := cap_memory_factor C hd hM
  have hfront : Real.exp (C*d) ≤ Real.exp ((C+32)*d) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have ht := mul_le_mul (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg (by positivity : 0 ≤ ε/2) α))
    (pow_le_pow_left₀ (by positivity) hbase n) (by positivity) (by positivity)
  apply ht.trans_eq
  rw [← Real.exp_nat_mul]
  calc
    Real.exp ((C+32)*d)*(ε/2)^α*Real.exp ((n:ℝ)*((C+32)*d)) =
        (Real.exp ((C+32)*d)*Real.exp ((n:ℝ)*((C+32)*d)))*(ε/2)^α := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem cap_fixed_stop_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ → ℕ,
      Asymptotics.IsLittleO atTop (fun d => (M d:ℝ)) (fun d => (d:ℝ)^2) →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d (M d) T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      ∀ t : ℕ, t ≤ T →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      seededFixedSuccess K ρ ε t ≤ ENNReal.ofReal
        (Real.exp (C*d*(1+((t+k-1)/k:ℕ)))*(ε/2)^α) := by
  obtain ⟨C,hC,h⟩ := cap_fixed_stop.{u}
  refine ⟨C+32,by linarith,?_⟩
  intro M hM
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.1 hM.eventuallyLE
  refine ⟨max d₀ 32,?_⟩
  intro d hd T ε hε hε10 Ξ _ ρ hρ K hK t ht k α
  have hm : (M d:ℝ) ≤ (d:ℝ)^2 := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (M d)),
      abs_of_nonneg (sq_nonneg (d:ℝ))] using hd₀ d (by omega)
  exact (h d (M d) T (by omega) ε hε hε10 Ξ ρ hρ K hK t ht).trans
    (ENNReal.ofReal_le_ofReal (cap_finite_to_asymptotic C (by omega) hm ε α _ hε.le))

lemma cap_ceil_cost {d T : ℕ} (hd : 32 ≤ d) :
    (d:ℝ)*(1+((T+d/16-1)/(d/16):ℕ)) ≤ 2*d+32*T := by
  let k := d/16
  let n := (T+k-1)/k
  have hk : 0 < k := by dsimp [k]; omega
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hdiv : n*k ≤ T+k := (Nat.div_mul_le_self _ _).trans (by omega)
  have hdivR : (n:ℝ)*k ≤ (T:ℝ)+k := by exact_mod_cast hdiv
  have hdR : (d:ℝ) ≤ 32*k := by exact_mod_cast (show d ≤ 32*k by dsimp [k]; omega)
  have hn : (n:ℝ) ≤ (T:ℝ)/k+1 := by
    have he := div_mul_cancel₀ (T:ℝ) hkR.ne'
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (α := ℝ) d)
  have hdk : (d:ℝ)/(k:ℝ) ≤ 32 := (div_le_iff₀ hkR).mpr hdR
  have hT := mul_le_mul_of_nonneg_right hdk (Nat.cast_nonneg (α := ℝ) T)
  change (d:ℝ)*(1+(n:ℝ)) ≤ _
  calc
    _ ≤ (d:ℝ)*((T:ℝ)/k+2) := by nlinarith
    _ = (d:ℝ)/k*T+2*d := by ring
    _ ≤ _ := by linarith

lemma cap_accuracy_cost {d : ℕ} (hd : 3 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (ε/2)^(((d:ℝ)-1)/2) ≤ Real.exp (-(d:ℝ)*Real.log (1/ε)/3) := by
  have hdR : (3:ℝ) ≤ d := by exact_mod_cast hd
  have ha : 0 ≤ ((d:ℝ)-1)/2 := by linarith
  calc
    _ ≤ ε^(((d:ℝ)-1)/2) := Real.rpow_le_rpow (by positivity) (by linarith) ha
    _ ≤ ε^((d:ℝ)/3) := Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
    _ = _ := by
      rw [Real.rpow_def_of_pos hε,one_div,Real.log_inv]
      congr 1
      ring

theorem cap_total_success_asymptotic :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ M : ℕ → ℕ,
      Asymptotics.IsLittleO atTop (fun d => (M d:ℝ)) (fun d => (d:ℝ)^2) →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d (M d) T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (((T:ℝ)+1)*Real.exp (C₁*d+C₂*T-(d:ℝ)*Real.log (1/ε)/3)) := by
  obtain ⟨C,hC,h⟩ := cap_total_success.{u}
  refine ⟨2*(C+32),32*(C+32),by positivity,by positivity,?_⟩
  intro M hM
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.1 hM.eventuallyLE
  refine ⟨max d₀ 32,?_⟩
  intro d hd T ε hε hε10 Ξ _ ρ hρ K hK
  have hm : (M d:ℝ) ≤ (d:ℝ)^2 := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (M d)),
      abs_of_nonneg (sq_nonneg (d:ℝ))] using hd₀ d (by omega)
  apply (h d (M d) T (by omega) ε hε hε10 Ξ ρ hρ K hK).trans
  apply ENNReal.ofReal_le_ofReal
  simp only [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (T:ℝ)+1)
  have hfinite := cap_finite_to_asymptotic C (by omega) hm ε (((d:ℝ)-1)/2)
    ((T+d/16-1)/(d/16)) hε.le
  simp only [mul_assoc] at hfinite
  apply hfinite.trans
  have hcost := mul_le_mul_of_nonneg_left (cap_ceil_cost (T := T) (by omega : 32 ≤ d))
    (by positivity : (0:ℝ) ≤ C+32)
  have he : Real.exp ((C+32)*d*(1+((T+d/16-1)/(d/16):ℕ))) ≤
      Real.exp (2*(C+32)*d+32*(C+32)*T) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  simp only [mul_assoc] at he
  apply (mul_le_mul he (cap_accuracy_cost (d := d) (by omega) hε (by linarith)) (by positivity) (by positivity)).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

end FiniteKernelLearner
end NoiselessRegression

end

end OAI
end
end

section
section
namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace ProjectionMoments
open NoiselessRegression
variable {d : ℕ}

def extendSphereWeight (f : UnitSphere d → ℝ≥0∞) : Vector d → ℝ≥0∞ :=
  Function.extend Subtype.val f (fun _ => 0)

@[simp] lemma extendSphereWeight_val (f : UnitSphere d → ℝ≥0∞) (s : UnitSphere d) :
    extendSphereWeight f s.val = f s :=
  Subtype.val_injective.extend_apply f (fun _ => 0) s

lemma measurable_extendSphereWeight {f : UnitSphere d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (extendSphereWeight f) :=
  (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).measurable_extend hf measurable_const

lemma extendSphereWeight_le_one {f : UnitSphere d → ℝ≥0∞} (hf : ∀ s, f s ≤ 1) :
    ∀ x, extendSphereWeight f x ≤ 1 := by
  intro x
  by_cases hx : ∃ s : UnitSphere d, s.val = x
  · obtain ⟨s,rfl⟩ := hx
    simpa using hf s
  · rw [extendSphereWeight,Function.extend_apply' _ _ _ hx]
    exact zero_le_one

lemma sphereWeight_measure (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f) :
    ambientSphereLaw.withDensity (extendSphereWeight f) =
      ((uniformSphere d).withDensity f).map Subtype.val := by
  ext S hS
  rw [withDensity_apply _ hS,Measure.map_apply measurable_subtype_coe hS,
    withDensity_apply _ (measurable_subtype_coe hS)]
  change (∫⁻ x in S, extendSphereWeight f x ∂(uniformSphere d).map Subtype.val) = _
  rw [← lintegral_indicator hS,lintegral_map ((measurable_extendSphereWeight hf).indicator hS)
      measurable_subtype_coe,← lintegral_indicator (measurable_subtype_coe hS)]
  apply lintegral_congr
  intro s
  by_cases hs : s.val ∈ S <;> simp [hs,extendSphereWeight_val]

lemma sphereWeight_potential (α : ℝ) (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f) :
    rieszPotential α (extendSphereWeight f) =
      ⨆ z : Vector d, ∫⁻ s, f s * (ENNReal.ofReal ‖s.val-z‖)^(-α) ∂uniformSphere d := by
  unfold rieszPotential
  congr 1
  funext z
  change (∫⁻ x, extendSphereWeight f x*rieszKernel α z x ∂(uniformSphere d).map Subtype.val) = _
  rw [lintegral_map (show Measurable (fun x => extendSphereWeight f x*rieszKernel α z x) from
    (measurable_extendSphereWeight hf).mul (measurable_rieszKernel α z)) measurable_subtype_coe]
  apply lintegral_congr
  intro s
  simp only [extendSphereWeight_val,rieszKernel]

lemma sphereWeight_restriction (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f)
    (H : Set (UnitSphere d)) (hH : MeasurableSet H) :
    sphereWeightedRestriction (extendSphereWeight f) (Subtype.val '' H) =
      (((uniformSphere d).withDensity f).restrict H).map Subtype.val := by
  have he := MeasurableEmbedding.subtype_coe (Metric.isClosed_sphere.measurableSet :
    MeasurableSet (Metric.sphere (0 : Vector d) 1))
  rw [sphereWeightedRestriction,sphereWeight_measure f hf,Measure.restrict_map measurable_subtype_coe
    (he.measurableSet_image.mpr hH)]
  congr 1
  congr 1
  exact Set.preimage_image_eq _ Subtype.val_injective

lemma sphere_weight_representation (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f)
    (hf1 : ∀ s, f s ≤ 1) :
    ∃ F : Vector d → ℝ≥0∞, Measurable F ∧ (∀ x, F x ≤ 1) ∧
      (∀ s : UnitSphere d, F s.val = f s) ∧
      ambientSphereLaw.withDensity F = ((uniformSphere d).withDensity f).map Subtype.val :=
  ⟨extendSphereWeight f,measurable_extendSphereWeight hf,extendSphereWeight_le_one hf1,
    extendSphereWeight_val f,sphereWeight_measure f hf⟩

end ProjectionMoments
end

end

end OAI
end
end

section
section
namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open NoiselessRegression NoiselessRegression.FiniteKernelLearner
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments

theorem main_oai : MainStatement.{u} := by
  refine ⟨integrated_frame_moment, normalized_unitBall_moment, all_radii_sphere_moment,
    positive_family_cap_domination, riesz_deterministic_offsets, one_block_all_radii,
    NoiselessRegression.FiniteKernelLearner.haar_success,
    NoiselessRegression.FiniteKernelLearner.riesz_success,
    NoiselessRegression.FiniteKernelLearner.cap_fixed_stop,
    NoiselessRegression.FiniteKernelLearner.cap_total_success,
    NoiselessRegression.FiniteKernelLearner.cap_fixed_stop_asymptotic,
    NoiselessRegression.FiniteKernelLearner.cap_total_success_asymptotic, ?_,
    NoiselessRegression.FiniteKernelLearner.subquadratic_memory_with_pointwise,
    NoiselessRegression.FiniteKernelLearner.fixed_quadratic_memory⟩
  intro d M T hd K hK
  exact K.exists_equivalent_tape hK hd

end ProjectionMoments

end

end

end OAI
end
end

theorem solution : type_of% @OAI.ProjectionMoments.main_oai := @OAI.ProjectionMoments.main_oai
