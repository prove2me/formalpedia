-- Prove2me | solution 1 for LesHouchesWidth.jacobian_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T12:01:19.760561+00:00
-- url     : https://prove2.me/submissions/55419a35-d333-47ed-b865-c67ae759a04e

import Mathlib
import Definitions.Def_LesHouchesWidth_ReLUNet

/-! cd91d20d LesHouchesWidth.jacobian_second_moment (Les Houches lectures, eq. (124)).

Route: sensitivities `sens` (the path-sum Jacobian column) satisfy, on a full-measure event,
`jacobianEntry = sens (L+1) q` (the network is locally linear near `x`). Their second moments are
computed as lower Lebesgue integrals: resampling one weight coordinate at a time gives
`E[(Σ_j W_ij u_j)^2] = (2/n_ℓ) Σ_j E[u_j^2]`, and a sign flip of one weight row shows
`E[1{z>0} s^2] = E[s^2]/2`. Hence `E[(sens ℓ j)^2] = 2/n_0` for every layer. -/

set_option autoImplicit false

namespace LesHouchesWidth.JacLib

open MeasureTheory ProbabilityTheory LesHouchesWidth
open scoped ENNReal

variable {n : ℕ → ℕ} {L : ℕ}

/-- The activation feeding layer `ℓ + 1`. -/
noncomputable def act (ω : Weights n L) (x : Fin (n 0) → ℝ) (ℓ : ℕ) (j : Fin (n ℓ)) : ℝ :=
  if ℓ = 0 then netZ ω x ℓ j else relu (netZ ω x ℓ j)

/-- The ReLU gate `1{z > 0}` (identity at the input layer). -/
noncomputable def gate (ω : Weights n L) (x : Fin (n 0) → ℝ) (ℓ : ℕ) (j : Fin (n ℓ)) : ℝ :=
  if ℓ = 0 then 1 else if 0 < netZ ω x ℓ j then 1 else 0

/-- Sensitivities along the input direction `p`. -/
noncomputable def sens (ω : Weights n L) (x : Fin (n 0) → ℝ) (p : Fin (n 0)) :
    (ℓ : ℕ) → Fin (n ℓ) → ℝ
  | 0 => fun j => if j = p then 1 else 0
  | ℓ + 1 => fun i => ∑ j, weight ω ℓ i j * (gate ω x ℓ j * sens ω x p ℓ j)

theorem netZ_succ (ω : Weights n L) (x : Fin (n 0) → ℝ) (ℓ : ℕ) (i : Fin (n (ℓ + 1))) :
    netZ ω x (ℓ + 1) i = ∑ j, weight ω ℓ i j * act ω x ℓ j := rfl

theorem sens_succ (ω : Weights n L) (x : Fin (n 0) → ℝ) (p : Fin (n 0)) (ℓ : ℕ)
    (i : Fin (n (ℓ + 1))) :
    sens ω x p (ℓ + 1) i = ∑ j, weight ω ℓ i j * (gate ω x ℓ j * sens ω x p ℓ j) := rfl

theorem weight_congr {ω ω' : Weights n L} {ℓ : ℕ}
    (h : ∀ a : WeightIndex n L, a.1.val = ℓ → ω a = ω' a)
    (i : Fin (n (ℓ + 1))) (j : Fin (n ℓ)) : weight ω ℓ i j = weight ω' ℓ i j := by
  unfold weight
  split_ifs with hl
  · rw [h _ rfl]
  · rfl

theorem netZ_congr {ω ω' : Weights n L} (x : Fin (n 0) → ℝ) :
    ∀ m : ℕ, (∀ a : WeightIndex n L, a.1.val < m → ω a = ω' a) → netZ ω x m = netZ ω' x m
  | 0, _ => rfl
  | m + 1, h => by
    have ih := netZ_congr x m (fun a ha => h a (by omega))
    funext i
    rw [netZ_succ, netZ_succ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [weight_congr (fun a ha => h a (by omega)), act, act, ih]

theorem gate_congr {ω ω' : Weights n L} (x : Fin (n 0) → ℝ) (m : ℕ)
    (h : ∀ a : WeightIndex n L, a.1.val < m → ω a = ω' a) : gate ω x m = gate ω' x m := by
  funext j
  rw [gate, gate, netZ_congr x m h]

theorem act_congr {ω ω' : Weights n L} (x : Fin (n 0) → ℝ) (m : ℕ)
    (h : ∀ a : WeightIndex n L, a.1.val < m → ω a = ω' a) : act ω x m = act ω' x m := by
  funext j
  rw [act, act, netZ_congr x m h]

theorem sens_congr {ω ω' : Weights n L} (x : Fin (n 0) → ℝ) (p : Fin (n 0)) :
    ∀ m : ℕ, (∀ a : WeightIndex n L, a.1.val < m → ω a = ω' a) → sens ω x p m = sens ω' x p m
  | 0, _ => rfl
  | m + 1, h => by
    have ih := sens_congr x p m (fun a ha => h a (by omega))
    funext i
    rw [sens_succ, sens_succ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [weight_congr (fun a ha => h a (by omega)), gate_congr x m (fun a ha => h a (by omega)),
      ih]

theorem measurable_weight (ℓ : ℕ) (i : Fin (n (ℓ + 1))) (j : Fin (n ℓ)) :
    Measurable (fun ω : Weights n L => weight ω ℓ i j) := by
  unfold weight
  by_cases hl : ℓ < L + 1
  · simp only [hl, dite_true]
    exact (measurable_pi_apply _).const_mul _
  · simp only [hl, dite_false]
    exact measurable_const

theorem measurable_netZ (x : Fin (n 0) → ℝ) :
    ∀ (m : ℕ) (i : Fin (n m)), Measurable (fun ω : Weights n L => netZ ω x m i)
  | 0, _ => measurable_const
  | m + 1, i => by
    simp only [netZ_succ]
    refine Finset.measurable_sum _ fun j _ => (measurable_weight _ _ _).mul ?_
    unfold act
    by_cases hm : m = 0
    · simp only [hm, if_true]
      exact measurable_netZ x _ _
    · simp only [hm, if_false]
      exact (measurable_netZ x m j).max measurable_const

theorem measurable_act (x : Fin (n 0) → ℝ) (m : ℕ) (j : Fin (n m)) :
    Measurable (fun ω : Weights n L => act ω x m j) := by
  unfold act
  by_cases hm : m = 0
  · simp only [hm, if_true]
    exact measurable_netZ x _ _
  · simp only [hm, if_false]
    exact (measurable_netZ x m j).max measurable_const

theorem measurable_gate (x : Fin (n 0) → ℝ) (m : ℕ) (j : Fin (n m)) :
    Measurable (fun ω : Weights n L => gate ω x m j) := by
  unfold gate
  by_cases hm : m = 0
  · simp only [hm, if_true]
    exact measurable_const
  · simp only [hm, if_false]
    exact Measurable.ite (measurableSet_lt measurable_const (measurable_netZ x m j))
      measurable_const measurable_const

theorem measurable_sens (x : Fin (n 0) → ℝ) (p : Fin (n 0)) :
    ∀ (m : ℕ) (i : Fin (n m)), Measurable (fun ω : Weights n L => sens ω x p m i)
  | 0, _ => measurable_const
  | m + 1, i => by
    simp only [sens_succ]
    exact Finset.measurable_sum _ fun j _ =>
      (measurable_weight _ _ _).mul ((measurable_gate x m j).mul (measurable_sens x p m j))

/-- Resampling one coordinate of a product measure. -/
theorem resample {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) (i : ι) :
    ∫⁻ ω, f ω ∂(Measure.pi fun _ => μ) =
      ∫⁻ ω, ∫⁻ t, f (Function.update ω i t) ∂μ ∂(Measure.pi fun _ => μ) := by
  have hg : Measurable (∫⋯∫⁻_{i}, f ∂(fun _ => μ)) := hf.lmarginal _
  have hsing := lmarginal_singleton (μ := fun _ : ι => μ) f i
  rw [← hsing, lintegral_eq_lmarginal_univ 0, lintegral_eq_lmarginal_univ 0,
    lmarginal_erase' f hf (Finset.mem_univ i), lmarginal_erase' _ hg (Finset.mem_univ i)]
  congr 1
  funext x
  simp only [lmarginal_update_of_mem (fun _ : ι => μ) (Finset.mem_singleton_self i),
    lintegral_const, measure_univ, mul_one]
  exact (congrFun hsing x).symm

section Scalar

variable {μ : Measure ℝ}

theorem int_sq (hvar : ∫ t, t ^ 2 ∂μ = 1) : Integrable (fun t : ℝ => t ^ 2) μ :=
  Integrable.of_integral_ne_zero (by rw [hvar]; norm_num)

theorem int_id [IsProbabilityMeasure μ] (hvar : ∫ t, t ^ 2 ∂μ = 1) : Integrable (fun t : ℝ => t) μ := by
  refine Integrable.mono' (g := fun t => 1 + t ^ 2) ((integrable_const (1 : ℝ)).add (int_sq hvar))
    measurable_id.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  show ‖t‖ ≤ 1 + t ^ 2
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs t, sq_nonneg (|t| - 1), abs_nonneg t]

theorem mean_zero (hsymm : μ.map (fun t : ℝ => -t) = μ) : ∫ t, t ∂μ = 0 := by
  have h : ∫ t, t ∂μ = ∫ t, -t ∂μ := by
    calc ∫ t, t ∂μ = ∫ t, t ∂(μ.map (fun t : ℝ => -t)) := by rw [hsymm]
      _ = ∫ t, -t ∂μ := integral_map measurable_neg.aemeasurable aestronglyMeasurable_id
  rw [integral_neg] at h
  linarith

theorem lint_sq [IsProbabilityMeasure μ] (hsymm : μ.map (fun t : ℝ => -t) = μ) (hvar : ∫ t, t ^ 2 ∂μ = 1)
    (a b A : ℝ) (hA : 0 ≤ A) :
    ∫⁻ t, ENNReal.ofReal ((a * t + b) ^ 2 + A) ∂μ = ENNReal.ofReal (a ^ 2 + b ^ 2 + A) := by
  have hsq := int_sq hvar
  have h1 := int_id hvar
  have hfun : (fun t : ℝ => (a * t + b) ^ 2 + A) =
      fun t => a ^ 2 * t ^ 2 + (2 * a * b) * t + (b ^ 2 + A) := by
    funext t; ring
  have hint : Integrable (fun t => (a * t + b) ^ 2 + A) μ := by
    rw [hfun]
    exact ((hsq.const_mul _).add (h1.const_mul _)).add (integrable_const _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun t => by positivity)]
  congr 1
  have i1 : Integrable (fun t : ℝ => a ^ 2 * t ^ 2 + (2 * a * b) * t) μ :=
    (hsq.const_mul _).add (h1.const_mul _)
  rw [hfun, integral_add i1 (integrable_const _),
    integral_add (hsq.const_mul _) (h1.const_mul _), integral_const_mul, integral_const_mul,
    hvar, mean_zero hsymm]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero, mul_one]
  ring

end Scalar

section Expand

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq J]

theorem sq_expand (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun t : ℝ => -t) = μ) (hvar : ∫ t, t ^ 2 ∂μ = 1)
    (e : J → ι) (he : Function.Injective e) (c : ℝ) (u : J → (ι → ℝ) → ℝ)
    (hu_meas : ∀ j, Measurable (u j))
    (hu_inv : ∀ j j' ω t, u j (Function.update ω (e j') t) = u j ω) :
    ∀ (s : Finset J) (A : (ι → ℝ) → ℝ), Measurable A → (∀ ω, 0 ≤ A ω) →
      (∀ j ∈ s, ∀ ω t, A (Function.update ω (e j) t) = A ω) →
      ∫⁻ ω, ENNReal.ofReal ((∑ j ∈ s, c * ω (e j) * u j ω) ^ 2 + A ω)
          ∂(Measure.pi fun _ => μ) =
      ∫⁻ ω, ENNReal.ofReal (c ^ 2 * ∑ j ∈ s, u j ω ^ 2 + A ω) ∂(Measure.pi fun _ => μ) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro A _ _ _; simp
  | insert j₀ s hj₀ ih =>
    intro A hA hA0 hAinv
    have hB : ∀ ω t, (∑ j ∈ s, c * (Function.update ω (e j₀) t) (e j) *
        u j ω) = ∑ j ∈ s, c * ω (e j) * u j ω := by
      intro ω t
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : e j ≠ e j₀ := fun h => hj₀ (he h ▸ hj)
      rw [Function.update_of_ne hne]
    have hmeas : Measurable (fun ω : ι → ℝ =>
        ENNReal.ofReal ((∑ j ∈ insert j₀ s, c * ω (e j) * u j ω) ^ 2 + A ω)) :=
      ENNReal.measurable_ofReal.comp (((Finset.measurable_sum
        (f := fun j (ω : ι → ℝ) => c * ω (e j) * u j ω) _ fun j _ =>
        (measurable_const.mul (measurable_pi_apply _)).mul (hu_meas j)).pow_const 2).add hA)
    rw [resample μ _ hmeas (e j₀)]
    have step : ∀ ω : ι → ℝ, ∫⁻ t, ENNReal.ofReal ((∑ j ∈ insert j₀ s,
        c * (Function.update ω (e j₀) t) (e j) * u j (Function.update ω (e j₀) t)) ^ 2 +
        A (Function.update ω (e j₀) t)) ∂μ =
        ENNReal.ofReal ((∑ j ∈ s, c * ω (e j) * u j ω) ^ 2 + (c ^ 2 * u j₀ ω ^ 2 + A ω)) := by
      intro ω
      simp only [Finset.sum_insert hj₀, Function.update_self, hu_inv,
        hAinv j₀ (Finset.mem_insert_self _ _)]
      simp only [hB]
      have := lint_sq hsymm hvar (c * u j₀ ω) (∑ j ∈ s, c * ω (e j) * u j ω) (A ω) (hA0 ω)
      rw [show (fun t => ENNReal.ofReal ((c * t * u j₀ ω + ∑ j ∈ s, c * ω (e j) * u j ω) ^ 2
          + A ω)) = fun t => ENNReal.ofReal ((c * u j₀ ω * t + ∑ j ∈ s, c * ω (e j) * u j ω) ^ 2
          + A ω) by funext t; ring_nf, this]
      congr 1
      ring
    rw [lintegral_congr step]
    rw [ih (fun ω => c ^ 2 * u j₀ ω ^ 2 + A ω)
      ((measurable_const.mul ((hu_meas j₀).pow_const 2)).add hA)
      (fun ω => by have := hA0 ω; positivity)
      (fun j hj ω t => by
        simp only [hu_inv, hAinv j (Finset.mem_insert_of_mem hj)])]
    refine lintegral_congr fun ω => ?_
    rw [Finset.sum_insert hj₀]
    congr 1
    ring

end Expand

section Null

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem null_fiber (μ : Measure ℝ) [IsProbabilityMeasure μ] (hatom : ∀ a : ℝ, μ {a} = 0)
    (i₀ : ι) (c r : (ι → ℝ) → ℝ) (hc : Measurable c) (hr : Measurable r)
    (hci : ∀ ω t, c (Function.update ω i₀ t) = c ω)
    (hri : ∀ ω t, r (Function.update ω i₀ t) = r ω) :
    (Measure.pi fun _ => μ) {ω | c ω ≠ 0 ∧ c ω * ω i₀ + r ω = 0} = 0 := by
  set S := {ω : ι → ℝ | c ω ≠ 0 ∧ c ω * ω i₀ + r ω = 0} with hSdef
  have hS : MeasurableSet S :=
    (hc (measurableSet_singleton 0).compl).inter
      (measurableSet_eq_fun ((hc.mul (measurable_pi_apply i₀)).add hr) measurable_const)
  rw [← lintegral_indicator_one hS, resample μ (S.indicator 1) (measurable_const.indicator hS) i₀]
  have hin : ∀ ω : ι → ℝ, ∫⁻ t, S.indicator 1 (Function.update ω i₀ t) ∂μ = 0 := by
    intro ω
    refine le_antisymm ?_ zero_le
    calc ∫⁻ t, S.indicator 1 (Function.update ω i₀ t) ∂μ
        ≤ ∫⁻ t, ({-(r ω) / c ω} : Set ℝ).indicator 1 t ∂μ := by
          refine lintegral_mono fun t => ?_
          by_cases ht : Function.update ω i₀ t ∈ S
          · have h' := ht
            simp only [hSdef, Set.mem_ofPred_eq, hci, hri, Function.update_self] at h'
            have : t = -(r ω) / c ω := by
              rw [eq_div_iff h'.1]; linear_combination h'.2
            rw [Set.indicator_of_mem ht, Set.indicator_of_mem (by simpa using this)]
            simp only [Pi.one_apply, le_refl]
          · rw [Set.indicator_of_notMem ht]; exact zero_le
      _ = μ {-(r ω) / c ω} := lintegral_indicator_one (measurableSet_singleton _)
      _ = 0 := hatom _
  simp [hin]

end Null

section Flip

/-- Flip the sign of row `j` of the weight layer `ℓ`. -/
noncomputable def flipRow (ℓ j : ℕ) : Weights n L → Weights n L :=
  fun ω a => (fun (a : WeightIndex n L) (t : ℝ) => if a.1.val = ℓ ∧ a.2.1.val = j then -t else t)
    a (ω a)

theorem flipRow_mp (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun t : ℝ => -t) = μ) (ℓ j : ℕ) :
    MeasurePreserving (flipRow (n := n) (L := L) ℓ j) (weightLaw n L μ) (weightLaw n L μ) := by
  unfold weightLaw flipRow
  refine measurePreserving_pi (ι := WeightIndex n L) (α := fun _ => ℝ) (β := fun _ => ℝ)
    (fun _ => μ) (fun _ => μ)
    (f := fun (a : WeightIndex n L) (t : ℝ) => if a.1.val = ℓ ∧ a.2.1.val = j then -t else t)
    fun a => ?_
  by_cases h : a.1.val = ℓ ∧ a.2.1.val = j
  · simp only [h, and_self, if_true]
    exact ⟨measurable_neg, hsymm⟩
  · simp only [h, if_false]
    exact MeasurePreserving.id μ

theorem flipRow_low (ℓ j : ℕ) (ω : Weights n L) (a : WeightIndex n L) (ha : a.1.val < ℓ) :
    flipRow ℓ j ω a = ω a := by
  unfold flipRow
  have : ¬(a.1.val = ℓ ∧ a.2.1.val = j) := fun h => by omega
  simp only [this, if_false]

theorem weight_flipRow (ℓ : ℕ) (hℓ : ℓ < L + 1) (j : Fin (n (ℓ + 1))) (ω : Weights n L)
    (k : Fin (n ℓ)) : weight (flipRow ℓ j.val ω) ℓ j k = -weight ω ℓ j k := by
  simp only [weight, dif_pos hℓ, flipRow, and_self, if_true]
  ring

theorem netZ_flipRow (x : Fin (n 0) → ℝ) (ℓ : ℕ) (hℓ : ℓ < L + 1) (j : Fin (n (ℓ + 1)))
    (ω : Weights n L) : netZ (flipRow ℓ j.val ω) x (ℓ + 1) j = -netZ ω x (ℓ + 1) j := by
  rw [netZ_succ, netZ_succ, act_congr x ℓ (fun a ha => flipRow_low ℓ j.val ω a ha),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [weight_flipRow ℓ hℓ j ω k, neg_mul]

theorem sens_flipRow (x : Fin (n 0) → ℝ) (p : Fin (n 0)) (ℓ : ℕ) (hℓ : ℓ < L + 1)
    (j : Fin (n (ℓ + 1))) (ω : Weights n L) :
    sens (flipRow ℓ j.val ω) x p (ℓ + 1) j = -sens ω x p (ℓ + 1) j := by
  rw [sens_succ, sens_succ, gate_congr x ℓ (fun a ha => flipRow_low ℓ j.val ω a ha),
    sens_congr x p ℓ (fun a ha => flipRow_low ℓ j.val ω a ha), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [weight_flipRow ℓ hℓ j ω k, neg_mul]

end Flip

section Net

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

theorem update_low (ω : Weights n L) (i₀ : WeightIndex n L) (t : ℝ) (m : ℕ)
    (hm : m ≤ i₀.1.val) :
    ∀ a : WeightIndex n L, a.1.val < m → Function.update ω i₀ t a = ω a := by
  intro a ha
  have : a ≠ i₀ := fun h => by subst h; omega
  exact Function.update_of_ne this t ω

theorem null_net (hatom : ∀ a : ℝ, μ {a} = 0) (x : Fin (n 0) → ℝ) (ℓ : ℕ) (hℓ : ℓ < L + 1)
    (hn : 1 ≤ n ℓ) (j : Fin (n (ℓ + 1))) (k : Fin (n ℓ)) :
    weightLaw n L μ {ω | netZ ω x (ℓ + 1) j = 0 ∧ act ω x ℓ k ≠ 0} = 0 := by
  classical
  let i₀ : WeightIndex n L := ⟨⟨ℓ, hℓ⟩, (j, k)⟩
  let c : Weights n L → ℝ := fun ω => Real.sqrt (2 / (n ℓ : ℝ)) * act ω x ℓ k
  let r : Weights n L → ℝ := fun ω =>
    ∑ k' ∈ Finset.univ.erase k, weight ω ℓ j k' * act ω x ℓ k'
  have hdecomp : ∀ ω, netZ ω x (ℓ + 1) j = c ω * ω i₀ + r ω := by
    intro ω
    rw [netZ_succ, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    simp only [c, r, weight, dif_pos hℓ, i₀]
    ring
  have hsqrt : 0 < Real.sqrt (2 / (n ℓ : ℝ)) :=
    Real.sqrt_pos.2 (div_pos two_pos (by exact_mod_cast hn))
  have hc : Measurable c := measurable_const.mul (measurable_act x ℓ k)
  have hr : Measurable r := Finset.measurable_sum
    (f := fun k' (ω : Weights n L) => weight ω ℓ j k' * act ω x ℓ k') _
    fun k' _ => (measurable_weight ℓ j k').mul (measurable_act x ℓ k')
  have hact : ∀ ω t, act (Function.update ω i₀ t) x ℓ = act ω x ℓ :=
    fun ω t => act_congr x ℓ (update_low ω i₀ t ℓ le_rfl)
  have hci : ∀ ω t, c (Function.update ω i₀ t) = c ω := by
    intro ω t
    simp only [c]
    rw [hact]
  have hri : ∀ ω t, r (Function.update ω i₀ t) = r ω := by
    intro ω t
    simp only [r]
    rw [hact]
    refine Finset.sum_congr rfl fun k' hk' => ?_
    have hne : (⟨⟨ℓ, hℓ⟩, (j, k')⟩ : WeightIndex n L) ≠ i₀ := by
      intro h
      simp only [i₀, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
      exact (Finset.ne_of_mem_erase hk') h
    simp only [weight, dif_pos hℓ, Function.update_of_ne hne]
  refine measure_mono_null (fun ω hω => ?_) (null_fiber μ hatom i₀ c r hc hr hci hri)
  refine ⟨mul_ne_zero hsqrt.ne' hω.2, ?_⟩
  rw [← hdecomp]
  exact hω.1

theorem sens_zero_of_act (x : Fin (n 0) → ℝ) (hx : x ≠ 0) (p : Fin (n 0)) (ℓ : ℕ)
    (ω : Weights n L) (hall : ∀ k, act ω x ℓ k = 0) (j : Fin (n (ℓ + 1))) :
    sens ω x p (ℓ + 1) j = 0 := by
  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · subst h0
    exact (hx (funext fun k => by simpa [act, netZ] using hall k)).elim
  · rw [sens_succ]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hg : gate ω x ℓ k = 0 := by
      have h1 := hall k
      simp only [act, hpos.ne', if_false, relu] at h1
      simp only [gate, hpos.ne', if_false]
      rw [if_neg (not_lt.2 (max_eq_right_iff.1 h1))]
    rw [hg]
    ring

theorem half (hsymm : μ.map (fun t : ℝ => -t) = μ) (hatom : ∀ a : ℝ, μ {a} = 0)
    (x : Fin (n 0) → ℝ) (hx : x ≠ 0) (p : Fin (n 0)) (ℓ : ℕ) (hℓ : ℓ < L)
    (hn : 1 ≤ n ℓ) (j : Fin (n (ℓ + 1))) :
    2 * ∫⁻ ω, ENNReal.ofReal ((gate ω x (ℓ + 1) j * sens ω x p (ℓ + 1) j) ^ 2)
        ∂(weightLaw n L μ) =
      ∫⁻ ω, ENNReal.ofReal ((sens ω x p (ℓ + 1) j) ^ 2) ∂(weightLaw n L μ) := by
  let z := fun ω : Weights n L => netZ ω x (ℓ + 1) j
  let s := fun ω : Weights n L => sens ω x p (ℓ + 1) j
  let Fp := fun ω => ENNReal.ofReal (if 0 < z ω then s ω ^ 2 else 0)
  let Fm := fun ω => ENNReal.ofReal (if z ω < 0 then s ω ^ 2 else 0)
  let F0 := fun ω => ENNReal.ofReal (if z ω = 0 then s ω ^ 2 else 0)
  have hz : Measurable z := measurable_netZ x _ _
  have hs : Measurable s := measurable_sens x p _ _
  have hFp : Measurable Fp := ENNReal.measurable_ofReal.comp
    (Measurable.ite (measurableSet_lt measurable_const hz) (hs.pow_const 2) measurable_const)
  have hFm : Measurable Fm := ENNReal.measurable_ofReal.comp
    (Measurable.ite (measurableSet_lt hz measurable_const) (hs.pow_const 2) measurable_const)
  have hsplit : ∀ ω, ENNReal.ofReal (s ω ^ 2) = Fp ω + Fm ω + F0 ω := by
    intro ω
    rcases lt_trichotomy (z ω) 0 with h | h | h
    · simp [Fp, Fm, F0, h, h.ne, not_lt.2 h.le]
    · simp [Fp, Fm, F0, h]
    · simp [Fp, Fm, F0, h, h.ne', not_lt.2 h.le]
  have hgate : ∀ ω, ENNReal.ofReal ((gate ω x (ℓ + 1) j * s ω) ^ 2) = Fp ω := by
    intro ω
    simp only [gate, Nat.add_one_ne_zero, if_false, Fp, z]
    split_ifs <;> simp
  have hF0 : ∀ᵐ ω ∂(weightLaw n L μ), F0 ω = 0 := by
    have hae : ∀ᵐ ω ∂(weightLaw n L μ), ∀ k : Fin (n ℓ),
        ω ∉ {ω : Weights n L | netZ ω x (ℓ + 1) j = 0 ∧ act ω x ℓ k ≠ 0} :=
      ae_all_iff.2 fun k => measure_eq_zero_iff_ae_notMem.1
        (null_net μ hatom x ℓ (by omega) hn j k)
    filter_upwards [hae] with ω hω
    simp only [F0]
    split_ifs with hz0
    · have hall : ∀ k, act ω x ℓ k = 0 := fun k => by
        by_contra hk
        exact hω k ⟨hz0, hk⟩
      simp only [s, sens_zero_of_act x hx p ℓ ω hall j]
      simp
    · simp
  have hflip : ∫⁻ ω, Fm ω ∂(weightLaw n L μ) = ∫⁻ ω, Fp ω ∂(weightLaw n L μ) := by
    rw [← (flipRow_mp μ hsymm ℓ j.val).lintegral_comp hFm]
    refine lintegral_congr fun ω => ?_
    simp only [Fm, Fp, z, s, netZ_flipRow x ℓ (by omega) j ω,
      sens_flipRow x p ℓ (by omega) j ω, neg_lt_zero, neg_sq]
  rw [lintegral_congr hgate, lintegral_congr hsplit,
    lintegral_add_left (f := fun ω => Fp ω + Fm ω) (hFp.add hFm),
    lintegral_add_left hFp, lintegral_congr_ae hF0, lintegral_zero, hflip, add_zero, two_mul]

theorem sq_step (hsymm : μ.map (fun t : ℝ => -t) = μ) (hvar : ∫ t, t ^ 2 ∂μ = 1)
    (x : Fin (n 0) → ℝ) (p : Fin (n 0)) (ℓ : ℕ) (hℓ : ℓ < L + 1) (i : Fin (n (ℓ + 1))) :
    ∫⁻ ω, ENNReal.ofReal ((sens ω x p (ℓ + 1) i) ^ 2) ∂(weightLaw n L μ) =
      ∫⁻ ω, ENNReal.ofReal (2 / (n ℓ : ℝ) *
        ∑ j, (gate ω x ℓ j * sens ω x p ℓ j) ^ 2) ∂(weightLaw n L μ) := by
  classical
  let e : Fin (n ℓ) → WeightIndex n L := fun j => ⟨⟨ℓ, hℓ⟩, (i, j)⟩
  have he : Function.Injective e := by
    intro j j' h
    simpa [e] using h
  let u : Fin (n ℓ) → Weights n L → ℝ := fun j ω => gate ω x ℓ j * sens ω x p ℓ j
  have hu_meas : ∀ j, Measurable (u j) := fun j =>
    (measurable_gate x ℓ j).mul (measurable_sens x p ℓ j)
  have hu_inv : ∀ j j' ω t, u j (Function.update ω (e j') t) = u j ω := by
    intro j j' ω t
    simp only [u]
    rw [gate_congr x ℓ (update_low ω (e j') t ℓ le_rfl),
      sens_congr x p ℓ (update_low ω (e j') t ℓ le_rfl)]
  have key := sq_expand μ hsymm hvar e he (Real.sqrt (2 / (n ℓ : ℝ))) u hu_meas hu_inv
    Finset.univ (fun _ => 0) measurable_const (fun _ => le_rfl) (fun _ _ _ _ => rfl)
  simp only [add_zero] at key
  have hsq : Real.sqrt (2 / (n ℓ : ℝ)) ^ 2 = 2 / (n ℓ : ℝ) := Real.sq_sqrt (by positivity)
  rw [hsq] at key
  unfold weightLaw
  rw [← key]
  refine lintegral_congr fun ω => ?_
  congr 3
  rw [sens_succ]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [weight, dif_pos hℓ, u, e]

theorem moment (hsymm : μ.map (fun t : ℝ => -t) = μ) (hvar : ∫ t, t ^ 2 ∂μ = 1)
    (hatom : ∀ a : ℝ, μ {a} = 0) (x : Fin (n 0) → ℝ) (hx : x ≠ 0) (p : Fin (n 0))
    (hn : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ) :
    ∀ ℓ, ℓ ≤ L → ∀ i : Fin (n (ℓ + 1)),
      ∫⁻ ω, ENNReal.ofReal ((sens ω x p (ℓ + 1) i) ^ 2) ∂(weightLaw n L μ) =
        ENNReal.ofReal (2 / (n 0 : ℝ))
  | 0, _, i => by
    rw [sq_step μ hsymm hvar x p 0 (by omega) i]
    have h1 : ∀ ω : Weights n L, ∑ j, (gate ω x 0 j * sens ω x p 0 j) ^ 2 = 1 := by
      intro ω
      simp [gate, sens]
    simp only [h1, mul_one, lintegral_const, measure_univ]
  | ℓ + 1, hℓ, i => by
    have ih := moment hsymm hvar hatom x hx p hn ℓ (by omega)
    have hnl : 1 ≤ n (ℓ + 1) := hn (ℓ + 1) (by omega)
    have hX : ∀ j : Fin (n (ℓ + 1)),
        ∫⁻ ω, ENNReal.ofReal ((gate ω x (ℓ + 1) j * sens ω x p (ℓ + 1) j) ^ 2)
          ∂(weightLaw n L μ) = ENNReal.ofReal (1 / (n 0 : ℝ)) := by
      intro j
      have h2 := half (L := L) μ hsymm hatom x hx p ℓ (by omega) (hn ℓ (by omega)) j
      rw [ih j] at h2
      have h3 : ENNReal.ofReal (2 / (n 0 : ℝ)) = 2 * ENNReal.ofReal (1 / (n 0 : ℝ)) := by
        rw [show (2 / (n 0 : ℝ)) = 2 * (1 / (n 0 : ℝ)) by ring,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      rw [h3] at h2
      exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).1 h2
    rw [sq_step μ hsymm hvar x p (ℓ + 1) (by omega) i]
    have hpt : ∀ ω : Weights n L, ENNReal.ofReal (2 / (n (ℓ + 1) : ℝ) *
        ∑ j, (gate ω x (ℓ + 1) j * sens ω x p (ℓ + 1) j) ^ 2) =
        ∑ j, ENNReal.ofReal (2 / (n (ℓ + 1) : ℝ)) *
          ENNReal.ofReal ((gate ω x (ℓ + 1) j * sens ω x p (ℓ + 1) j) ^ 2) := by
      intro ω
      rw [ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _), Finset.mul_sum]
    have hmj : ∀ j : Fin (n (ℓ + 1)), Measurable (fun ω : Weights n L =>
        ENNReal.ofReal ((gate ω x (ℓ + 1) j * sens ω x p (ℓ + 1) j) ^ 2)) := fun j =>
      ENNReal.measurable_ofReal.comp (((measurable_gate x (ℓ + 1) j).mul
        (measurable_sens x p (ℓ + 1) j)).pow_const 2)
    rw [lintegral_congr hpt, lintegral_finsetSum _ (fun j _ => (hmj j).const_mul _),
      Finset.sum_congr rfl fun j _ => by rw [lintegral_const_mul _ (hmj j), hX j]]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : (n (ℓ + 1) : ℝ) ≠ 0 := by exact_mod_cast (show n (ℓ + 1) ≠ 0 by omega)
    field_simp

/-- Good event: no preactivation vanishes while its incoming activation is nonzero. -/
def good (ω : Weights n L) (x : Fin (n 0) → ℝ) : Prop :=
  ∀ ℓ < L, ∀ (j : Fin (n (ℓ + 1))) (k : Fin (n ℓ)),
    ¬(netZ ω x (ℓ + 1) j = 0 ∧ act ω x ℓ k ≠ 0)

theorem good_ae (hatom : ∀ a : ℝ, μ {a} = 0) (x : Fin (n 0) → ℝ)
    (hn : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ) : ∀ᵐ ω ∂(weightLaw n L μ), good ω x := by
  unfold good
  refine ae_all_iff.2 fun ℓ => ?_
  by_cases hℓ : ℓ < L
  · have h : ∀ᵐ ω ∂(weightLaw n L μ), ∀ (j : Fin (n (ℓ + 1))) (k : Fin (n ℓ)),
        ω ∉ {ω : Weights n L | netZ ω x (ℓ + 1) j = 0 ∧ act ω x ℓ k ≠ 0} :=
      ae_all_iff.2 fun j => ae_all_iff.2 fun k => measure_eq_zero_iff_ae_notMem.1
        (null_net μ hatom x ℓ (by omega) (hn ℓ (by omega)) j k)
    exact h.mono fun ω hω _ => hω
  · exact ae_of_all _ fun ω h => absurd h hℓ

theorem local_lin (x : Fin (n 0) → ℝ) (hx : x ≠ 0) (ω : Weights n L) (hg : good ω x) :
    ∀ m, m ≤ L + 1 → ∀ᶠ y in nhds x, ∀ i : Fin (n m),
      netZ ω y m i = ∑ k, sens ω x k m i * y k
  | 0, _ => Filter.Eventually.of_forall fun y i => by simp [netZ, sens]
  | m + 1, hm => by
    have ih := local_lin x hx ω hg m (by omega)
    have hact : ∀ᶠ y in nhds x, ∀ j : Fin (n m),
        act ω y m j = gate ω x m j * ∑ k, sens ω x k m j * y k := by
      refine Filter.eventually_all.2 fun j => ?_
      rcases m with _ | ℓ
      · exact ih.mono fun y h => by simp [act, gate, h j]
      · have hx0 : netZ ω x (ℓ + 1) j = ∑ k, sens ω x k (ℓ + 1) j * x k := ih.self_of_nhds j
        have hcont : Continuous (fun y : Fin (n 0) → ℝ => ∑ k, sens ω x k (ℓ + 1) j * y k) :=
          continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k)
        rcases lt_trichotomy (netZ ω x (ℓ + 1) j) 0 with h | h | h
        · have h' : ∑ k, sens ω x k (ℓ + 1) j * x k < 0 := by rwa [hx0] at h
          have hev : ∀ᶠ y in nhds x, (∑ k, sens ω x k (ℓ + 1) j * y k) < 0 :=
            hcont.continuousAt.eventually (gt_mem_nhds h')
          filter_upwards [ih, hev] with y h1 h2
          simp only [act, gate, Nat.add_one_ne_zero, if_false, not_lt.2 h.le, relu, h1 j,
            max_eq_right h2.le, zero_mul]
        · have hall : ∀ k, act ω x ℓ k = 0 := fun k => by
            by_contra hk
            exact hg ℓ (by omega) j k ⟨h, hk⟩
          have hrow : ∀ k, sens ω x k (ℓ + 1) j = 0 := fun k => sens_zero_of_act x hx k ℓ ω hall j
          filter_upwards [ih] with y h1
          simp only [act, gate, Nat.add_one_ne_zero, if_false, h1 j, hrow, zero_mul,
            Finset.sum_const_zero, relu, max_self, h, lt_irrefl]
        · have h' : 0 < ∑ k, sens ω x k (ℓ + 1) j * x k := by rwa [hx0] at h
          have hev : ∀ᶠ y in nhds x, 0 < (∑ k, sens ω x k (ℓ + 1) j * y k) :=
            hcont.continuousAt.eventually (lt_mem_nhds h')
          filter_upwards [ih, hev] with y h1 h2
          simp only [act, gate, Nat.add_one_ne_zero, if_false, h, if_true, relu, h1 j,
            max_eq_left h2.le, one_mul]
    filter_upwards [hact] with y hy i
    rw [netZ_succ]
    simp only [hy, sens_succ, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

theorem jac_eq (x : Fin (n 0) → ℝ) (hx : x ≠ 0) (ω : Weights n L) (hg : good ω x)
    (p : Fin (n 0)) (q : Fin (n (L + 1))) :
    jacobianEntry ω x p q = sens ω x p (L + 1) q := by
  have hev := local_lin x hx ω hg (L + 1) le_rfl
  let c : Fin (n 0) → ℝ := fun k => sens ω x k (L + 1) q
  let Φ : (Fin (n 0) → ℝ) →L[ℝ] ℝ := ∑ k, c k • ContinuousLinearMap.proj k
  have hΦ : ∀ y, Φ y = ∑ k, c k * y k := fun y => by simp [Φ]
  have heq : (fun y : Fin (n 0) → ℝ => output ω y q) =ᶠ[nhds x] Φ := by
    filter_upwards [hev] with y hy
    rw [hΦ]
    exact hy q
  unfold jacobianEntry
  rw [heq.fderiv_eq, Φ.fderiv, hΦ]
  simp [c, Pi.single_apply]

end Net

end LesHouchesWidth.JacLib

set_option maxHeartbeats 4000000 in
open MeasureTheory ProbabilityTheory LesHouchesWidth in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_ac : μ ≪ volume) (hμ_symm : μ.map (fun t : ℝ => -t) = μ)
    (hμ_var : ∫ t, t ^ 2 ∂μ = 1)
    (L : ℕ) (_hL : 1 ≤ L) (n : ℕ → ℕ) (hn : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ)
    (x : Fin (n 0) → ℝ) (hx : x ≠ 0) (p : Fin (n 0)) (q : Fin (n (L + 1))) :
    ∫ ω, (jacobianEntry ω x p q) ^ 2 ∂(weightLaw n L μ) = 2 / (n 0 : ℝ) := by
  have hatom : ∀ a : ℝ, μ {a} = 0 := fun a => hμ_ac Real.volume_singleton
  have hae : ∀ᵐ ω ∂(weightLaw n L μ), jacobianEntry ω x p q = JacLib.sens ω x p (L + 1) q :=
    (JacLib.good_ae μ hatom x hn).mono fun ω hg => JacLib.jac_eq x hx ω hg p q
  rw [integral_congr_ae (g := fun ω => (JacLib.sens ω x p (L + 1) q) ^ 2)
      (hae.mono fun ω h => by simp only [h]),
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg _)
      ((JacLib.measurable_sens x p (L + 1) q).pow_const 2).aestronglyMeasurable,
    JacLib.moment μ hμ_symm hμ_var hatom x hx p hn L le_rfl q,
    ENNReal.toReal_ofReal (by positivity)]
