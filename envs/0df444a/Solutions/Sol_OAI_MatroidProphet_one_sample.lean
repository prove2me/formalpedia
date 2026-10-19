-- Prove2me | solution 1 for OAI.MatroidProphet.one_sample
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T16:19:28.830281+00:00
-- url     : https://prove2.me/submissions/b3c654f4-e27b-48c5-8e04-5c322552301f

import Mathlib
import Definitions.Def_MatroidProphet

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
end OAICompat434

section
section
namespace OAI

/-!
# One-sample matroid selection

The rule and its finite seed law depend only on the known labeled matroid.
A decision sees the initial sample vector, the entire seed, and the arriving
label/value prefix. Every prefix is feasible, and decisions are irrevocable.
The arrival permutation may depend on all samples, values, and seed bits.
Only the actual offline optimum is required to be integrable.
-/

open scoped BigOperators

section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MatroidProphet

end MatroidProphet

end

section

open MeasureTheory
open scoped BigOperators

namespace MatroidProphet

instance arrivalOrderMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (ArrivalOrder n) := ⟨fun _ => trivial⟩

structure HiddenRule (n bits : ℕ) where
  mask : Seed bits → Finset (Fin n)
  core : OnlineRule n bits

noncomputable def observed {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (w : Weights n) : Weights n := by
  classical
  exact fun e => if e ∈ A.mask r then w e else 0

noncomputable def hiddenAcceptedThrough {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) (t : ℕ) : Finset (Fin n) :=
  acceptedThrough A.core r (observed A r w) w π t \ A.mask r

noncomputable def hiddenReward {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) : ℝ :=
  ∑ e ∈ hiddenAcceptedThrough A r w π n, w e

noncomputable def hiddenWorstReward {n bits : ℕ} (A : HiddenRule n bits)
    (w : Weights n) (r : Seed bits) : ℝ := by
  classical
  exact Finset.univ.inf' Finset.univ_nonempty (hiddenReward A r w)

end MatroidProphet

end

section

open MeasureTheory ProbabilityTheory

namespace MatroidProphet

def HiddenVectorChallenge : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
    ∃ (bits : ℕ) (ν : Measure (Seed bits)), IsProbabilityMeasure ν ∧
    ∃ (A : HiddenRule n bits),
      (∀ (w : Weights n), (∀ e, 0 ≤ w e) →
        ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
          M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n))) ∧
      ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
        ((2 : ℝ) ^ 293)⁻¹ * optimum M w ≤
          ∫ r, hiddenWorstReward A w r ∂ν

end MatroidProphet

end

section

open MeasureTheory

namespace MatroidProphet

/-- A measurable secretary rule with an initially fixed observation-prefix length. -/
structure SecretaryRule (n : ℕ) (Q : Type*) [MeasurableSpace Q] where
  prefixLength : Q → Fin (n + 1)
  measurable_prefixLength : Measurable prefixLength
  decide : (k : Fin n) → Q → History n k → Bool
  measurable_decide : ∀ k, Measurable
    (fun x : Q × History n k => decide k x.1 x.2)

/-- Full permutations describing the same ordered observation prefix. -/
def SamePrefix {n : ℕ} (K : ℕ) (σ π : ArrivalOrder n) : Prop :=
  ∀ k : Fin n, k.val < K → σ k = π k

/-- Execution forces rejection of every observation-prefix arrival. -/
def secretaryDecisionAt {n : ℕ} {Q : Type*} [MeasurableSpace Q]
    (A : SecretaryRule n Q) (q : Q) (w : Weights n) (π : ArrivalOrder n)
    (k : Fin n) : Bool :=
  if k.val < (A.prefixLength q).val then false else A.decide k q (history w π k)

/-- Irrevocable accepted labels through an arbitrary number of arrivals. -/
noncomputable def secretaryAcceptedThrough {n : ℕ} {Q : Type*} [MeasurableSpace Q]
    (A : SecretaryRule n Q) (q : Q) (w : Weights n) (π : ArrivalOrder n)
    (t : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun e =>
    (π.symm e).val < t ∧ secretaryDecisionAt A q w π (π.symm e) = true

noncomputable def secretaryReward {n : ℕ} {Q : Type*} [MeasurableSpace Q]
    (A : SecretaryRule n Q) (q : Q) (w : Weights n) (π : ArrivalOrder n) : ℝ :=
  ∑ e ∈ secretaryAcceptedThrough A q w π n, w e

/-- Feasibility is pointwise for every seed, vector, order, and arrival prefix. -/
def SecretaryFeasible {n : ℕ} {Q : Type*} [MeasurableSpace Q]
    (M : Matroid (Fin n)) (A : SecretaryRule n Q) : Prop :=
  ∀ (q : Q) (w : Weights n), (∀ e, 0 ≤ w e) →
    ∀ (π : ArrivalOrder n) (t : ℕ),
      M.Indep (secretaryAcceptedThrough A q w π t : Set (Fin n))

end MatroidProphet

end

section

namespace MatroidProphet.Secretary

open MeasureTheory

/-- Uniform random arrival order, including the unique order on the empty ground set. -/
noncomputable def uniformArrivalLaw (n : ℕ) : Measure (ArrivalOrder n) :=
  (PMF.uniformOfFintype (ArrivalOrder n)).toMeasure

end MatroidProphet.Secretary

end

section

open MeasureTheory ProbabilityTheory

namespace MatroidProphet

/-- The full order-oblivious conclusion of `cor:secretary`, including a
measurable history-only rule, every-prefix feasibility, prefix rejection,
arbitrary full-seed suffix adversaries, and the unchanged `2⁻²⁹³` ratio. -/
def SecretaryChallenge.{u} : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
    ∃ (q : ℕ) (ν : Measure (Fin q)), IsProbabilityMeasure ν ∧
    ∃ (A : SecretaryRule n (Fin q)), SecretaryFeasible M A ∧
      ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Q : Ω → Fin q) (σ π : Ω → ArrivalOrder n),
        Measurable Q → Measurable σ → Measurable π →
        Measure.map Q μ = ν →
        Measure.map σ μ = Secretary.uniformArrivalLaw n →
        IndepFun Q σ μ →
        (∀ᵐ ω ∂μ, SamePrefix (A.prefixLength (Q ω)).val (σ ω) (π ω)) →
        Integrable (fun ω => secretaryReward A (Q ω) w (π ω)) μ ∧
          ((2 : ℝ) ^ 293)⁻¹ * optimum M w ≤
            ∫ ω, secretaryReward A (Q ω) w (π ω) ∂μ

end MatroidProphet

end

end OAI
end
end

section
section
namespace OAI

open MeasureTheory
open scoped BigOperators

namespace MatroidProphet

theorem decisionAt_congr {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v v' : Weights n) (π π' : ArrivalOrder n) (k : Fin n)
    (h : history v π k = history v' π' k) :
    decisionAt A r s v π k = decisionAt A r s v' π' k := by
  simp only [decisionAt, h]

theorem acceptedThrough_mono {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) {t t' : ℕ} (h : t ≤ t') :
    acceptedThrough A r s v π t ⊆ acceptedThrough A r s v π t' := by
  classical
  intro e he
  simp only [acceptedThrough, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact ⟨lt_of_lt_of_le he.1 h, he.2⟩

theorem acceptedThrough_arrived {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) (e : Fin n)
    (he : e ∈ acceptedThrough A r s v π t) : (π.symm e).val < t := by
  classical
  exact ((Finset.mem_filter.mp he).2).1

theorem acceptedThrough_iff_decision {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) (e : Fin n)
    (he : (π.symm e).val < t) :
    e ∈ acceptedThrough A r s v π t ↔ decisionAt A r s v π (π.symm e) = true := by
  classical
  simp only [acceptedThrough, Finset.mem_filter, Finset.mem_univ, true_and, he]

theorem sum_le_optimum {n : ℕ} (M : Matroid (Fin n)) (v : Weights n)
    (I : Finset (Fin n)) (hI : M.Indep (I : Set (Fin n))) :
    (∑ e ∈ I, v e) ≤ optimum M v := by
  classical
  have h := Finset.le_sup' (s := (Finset.univ : Finset (Finset (Fin n))))
    (f := fun J => if M.Indep (J : Set (Fin n)) then ∑ e ∈ J, v e else 0)
    (Finset.mem_univ I)
  change _ ≤ Finset.univ.sup' Finset.univ_nonempty _
  simpa only [ite_eq_left hI] using h

theorem measurable_optimum {n : ℕ} (M : Matroid (Fin n)) : Measurable (optimum M) := by
  classical
  have hm (I : Finset (Fin n)) :
      Measurable (fun v : Weights n =>
        if M.Indep (I : Set (Fin n)) then ∑ e ∈ I, v e else 0) := by
    by_cases hI : M.Indep (I : Set (Fin n))
    · simpa [hI] using I.measurable_sum (fun e _ => measurable_pi_apply e)
    · simp [hI]
  have hsup := Finset.measurable_sup' (s := (Finset.univ : Finset (Finset (Fin n))))
    Finset.univ_nonempty (fun I _ => hm I)
  convert hsup using 1
  ext v
  simp only [optimum, Finset.sup'_apply]

theorem optimum_nonneg {n : ℕ} (M : Matroid (Fin n)) (v : Weights n) :
    0 ≤ optimum M v := by
  simpa using sum_le_optimum M v ∅ (by simp)

theorem reward_nonneg {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (hv : ∀ e, 0 ≤ v e) :
    0 ≤ reward A r s v π := by
  exact Finset.sum_nonneg fun e _ => hv e

theorem reward_le_optimum {n bits : ℕ} (M : Matroid (Fin n)) (A : OnlineRule n bits)
    (hA : Feasible M A) (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n)
    (hs : ∀ e, 0 ≤ s e) (hv : ∀ e, 0 ≤ v e) :
    reward A r s v π ≤ optimum M v :=
  sum_le_optimum M v (accepted A r s v π) (hA r s v π n hs hv)

lemma measurable_history {n : ℕ} (π : ArrivalOrder n) (k : Fin n) :
    Measurable (fun v : Weights n => history v π k) := by
  apply Measurable.of_eval
  intro j
  exact measurable_const.prodMk (measurable_pi_apply (π (prefixIndex k j)))

lemma measurable_decisionAt {n bits : ℕ} (A : OnlineRule n bits)
    (π : ArrivalOrder n) (k : Fin n) :
    Measurable (fun x : Seed bits × (Weights n × Weights n) =>
      decisionAt A x.1 x.2.1 x.2.2 π k) :=
  (A.measurable_decide k).comp
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_history π k).comp (measurable_snd.comp measurable_snd))))

lemma reward_eq_sum {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) :
    reward A r s v π =
      ∑ e : Fin n, if decisionAt A r s v π (π.symm e) = true then v e else 0 := by
  classical
  unfold reward accepted acceptedThrough
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  simp only [(π.symm e).isLt, true_and]

lemma measurable_reward_fixed_order {n bits : ℕ} (A : OnlineRule n bits)
    (π : ArrivalOrder n) :
    Measurable (fun x : Seed bits × (Weights n × Weights n) =>
      reward A x.1 x.2.1 x.2.2 π) := by
  classical
  simp_rw [reward_eq_sum]
  apply Finset.measurable_sum
  intro e _
  have hd := measurable_decisionAt A π (π.symm e)
  have ht : MeasurableSet {x : Seed bits × (Weights n × Weights n) |
      decisionAt A x.1 x.2.1 x.2.2 π (π.symm e) = true} :=
    hd (measurableSet_singleton true)
  exact Measurable.ite ht
    ((measurable_pi_apply e).comp (measurable_snd.comp measurable_snd)) measurable_const

theorem measurable_reward {n bits : ℕ} (A : OnlineRule n bits) :
    Measurable (fun x : ArrivalOrder n × (Seed bits × (Weights n × Weights n)) =>
      reward A x.2.1 x.2.2.1 x.2.2.2 x.1) :=
  measurable_from_prod_countable_right (measurable_reward_fixed_order A)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

noncomputable section

def weightBase : ℝ := 2 ^ 32
def densityThreshold : ℝ := 2 ^ 100
def thinningRate : ℝ := ((2 : ℝ) ^ 140)⁻¹
def exitThreshold : ℝ := ((2 : ℝ) ^ 12)⁻¹
def retainedFraction : ℝ := ((2 : ℝ) ^ 16)⁻¹

theorem constants_positive : 0 < weightBase ∧ 0 < densityThreshold ∧
    0 < thinningRate ∧ 0 < exitThreshold ∧ 0 < retainedFraction := by
  norm_num [weightBase, densityThreshold, thinningRate, exitThreshold, retainedFraction]

theorem error_constant :
    ((2 : ℝ) ^ 23)⁻¹ + thinningRate * densityThreshold +
      (1 + thinningRate * densityThreshold) / (weightBase - 1) < ((2 : ℝ) ^ 21)⁻¹ := by
  norm_num [thinningRate, densityThreshold, weightBase]

theorem retained_fraction_slack :
    retainedFraction / 8 ≤ retainedFraction / 4 - ((2 : ℝ) ^ 21)⁻¹ := by
  norm_num [retainedFraction]

theorem hidden_fraction_exact :
    thinningRate * retainedFraction / (32 * densityThreshold * weightBase) =
      ((2 : ℝ) ^ 293)⁻¹ := by
  rw [show 293 = 140 + 153 from rfl, pow_add]
  norm_num [thinningRate, retainedFraction, densityThreshold, weightBase]

theorem public_fraction_slack : ((2 : ℝ) ^ 310)⁻¹ ≤ ((2 : ℝ) ^ 293)⁻¹ := by
  rw [show 310 = 155 + 155 from rfl, show 293 = 140 + 153 from rfl, pow_add, pow_add]
  norm_num

theorem branch_mixture_lower (W maximumWeight mainPayoff maximumPayoff : ℝ)
    (hW : 0 ≤ W) (hmw : 0 ≤ maximumWeight) (hmain : 0 ≤ mainPayoff)
    (hmax : maximumWeight / 4 ≤ maximumPayoff)
    (hsmall : maximumWeight ≤ W / (8 * densityThreshold) →
      thinningRate * retainedFraction / (16 * densityThreshold) * W ≤ mainPayoff) :
    thinningRate * retainedFraction / (32 * densityThreshold) * W ≤
      (mainPayoff + maximumPayoff) / 2 := by
  by_cases hm : maximumWeight ≤ W / (8 * densityThreshold)
  · have hs := hsmall hm
    have hz : 0 ≤ maximumPayoff := by linarith
    norm_num [thinningRate, retainedFraction, densityThreshold] at hs ⊢
    linarith
  · have hm' : W / (8 * densityThreshold) < maximumWeight := lt_of_not_ge hm
    have hc : thinningRate * retainedFraction / (32 * densityThreshold) ≤
        1 / (64 * densityThreshold) := by
      norm_num [thinningRate, retainedFraction, densityThreshold]
    have hcW := mul_le_mul_of_nonneg_right hc hW
    norm_num [densityThreshold] at hm' hcW ⊢
    linarith

end

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open MeasureTheory

instance levelMeasurableSpace : MeasurableSpace (Option ℤ) := ⊤
instance levelMeasurableSingletonClass : MeasurableSingletonClass (Option ℤ) :=
  ⟨fun _ => trivial⟩

noncomputable def roundedLevel (B x : ℝ) : Option ℤ :=
  if 0 < x then some ⌊Real.logb B x⌋ else none

noncomputable def levelWeight (B : ℝ) : Option ℤ → ℝ
  | none => 0
  | some i => B ^ i

noncomputable def roundedWeight (B x : ℝ) : ℝ := levelWeight B (roundedLevel B x)

theorem measurable_roundedLevel (B : ℝ) : Measurable (roundedLevel B) := by
  unfold roundedLevel
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · exact (measurable_of_countable (some : ℤ → Option ℤ)).comp
      (Int.measurable_floor.comp (Real.measurable_log.div_const _))
  · exact measurable_const

lemma roundedWeight_nonneg {B : ℝ} (hB : 0 < B) (x : ℝ) :
    0 ≤ roundedWeight B x := by
  unfold roundedWeight roundedLevel
  split_ifs <;> simp only [levelWeight]
  · exact (zpow_pos hB _).le
  · exact le_rfl

lemma roundedWeight_le {B : ℝ} (hB : 1 < B) {x : ℝ} (hx : 0 ≤ x) :
    roundedWeight B x ≤ x := by
  by_cases hpos : 0 < x
  · unfold roundedWeight roundedLevel
    rw [ite_eq_left hpos, levelWeight]
    have h := (Real.le_logb_iff_rpow_le hB hpos).mp (Int.floor_le (Real.logb B x))
    simpa only [Real.rpow_intCast] using h
  · have hz : x = 0 := le_antisymm (le_of_not_gt hpos) hx
    simp [hz, roundedWeight, roundedLevel, levelWeight]

lemma le_base_mul_roundedWeight {B : ℝ} (hB : 1 < B) {x : ℝ} (hx : 0 ≤ x) :
    x ≤ B * roundedWeight B x := by
  by_cases hpos : 0 < x
  · unfold roundedWeight roundedLevel
    rw [ite_eq_left hpos, levelWeight]
    have h := (Real.logb_lt_iff_lt_rpow hB hpos).mp (Int.lt_floor_add_one (Real.logb B x))
    rw [← Int.cast_one, ← Int.cast_add, Real.rpow_intCast,
      zpow_add_one₀ (ne_of_gt (zero_lt_one.trans hB))] at h
    simpa only [mul_comm] using h.le
  · have hz : x = 0 := le_antisymm (le_of_not_gt hpos) hx
    simp [hz, roundedWeight, roundedLevel, levelWeight]

noncomputable def discreteOnlineRule {K : Type*} [Countable K] [MeasurableSpace K]
    [MeasurableSingletonClass K] {n bits : ℕ}
    (key : ℝ → K) (hkey : Measurable key)
    (choose : (k : Fin n) → Seed bits → (Fin n → K) →
      (Fin (k.val + 1) → Fin n × K) → Bool) : OnlineRule n bits where
  decide k r s hist := choose k r (fun e => key (s e))
    (fun j => ((hist j).1, key (hist j).2))
  measurable_decide k := by
    have hc : Measurable (fun x : Seed bits × ((Fin n → K) ×
        (Fin (k.val + 1) → Fin n × K)) => choose k x.1 x.2.1 x.2.2) :=
      measurable_of_countable _
    have hs : Measurable (fun x : Seed bits × (Weights n × History n k) =>
        fun e => key (x.2.1 e)) := by
      apply Measurable.of_eval
      intro e
      exact hkey.comp ((measurable_pi_apply e).comp (measurable_fst.comp measurable_snd))
    have hh : Measurable (fun x : Seed bits × (Weights n × History n k) =>
        fun j => ((x.2.2 j).1, key (x.2.2 j).2)) := by
      apply Measurable.of_eval
      intro j
      have hj : Measurable (fun x : Seed bits × (Weights n × History n k) => x.2.2 j) :=
        (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
      exact (measurable_fst.comp hj).prodMk (hkey.comp (measurable_snd.comp hj))
    exact hc.comp (measurable_fst.prodMk (hs.prodMk hh))

lemma optimum_le_of_independent_bound {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ I : Finset (Fin n), M.Indep (I : Set (Fin n)) → (∑ e ∈ I, w e) ≤ c) :
    optimum M w ≤ c := by
  classical
  apply Finset.sup'_le
  intro I hI
  by_cases hi : M.Indep (I : Set (Fin n))
  · simpa only [ite_eq_left hi] using hbound I hi
  · simpa only [ite_eq_right hi] using hc

theorem optimum_mono {n : ℕ} (M : Matroid (Fin n)) (v w : Weights n)
    (hvw : ∀ e, v e ≤ w e) : optimum M v ≤ optimum M w := by
  apply optimum_le_of_independent_bound M v _ (optimum_nonneg M w)
  intro I hI
  exact (Finset.sum_le_sum (fun e _ => hvw e)).trans (sum_le_optimum M w I hI)

theorem optimum_rounding_bound {n : ℕ} (M : Matroid (Fin n)) (B : ℝ) (hB : 1 < B)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    optimum M w ≤ B * optimum M (fun e => roundedWeight B (w e)) := by
  apply optimum_le_of_independent_bound M w _
    (mul_nonneg (zero_lt_one.trans hB).le (optimum_nonneg M _))
  intro I hI
  calc
    (∑ e ∈ I, w e) ≤ ∑ e ∈ I, B * roundedWeight B (w e) :=
      Finset.sum_le_sum (fun e _ => le_base_mul_roundedWeight hB (hw e))
    _ = B * ∑ e ∈ I, roundedWeight B (w e) := (Finset.mul_sum ..).symm
    _ ≤ B * optimum M (fun e => roundedWeight B (w e)) :=
      mul_le_mul_of_nonneg_left (sum_le_optimum M _ I hI) (zero_lt_one.trans hB).le

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set

variable {α : Type*} [Fintype α]

noncomputable def natRank (M : Matroid α) (X : Set α) : ℕ :=
  (M.eRk X).toNat

lemma rank_ne_top (M : Matroid α) (X : Set α) : M.eRk X ≠ ⊤ :=
  (M.isRkFinite_set X).eRk_lt_top.ne

lemma natRank_mono (M : Matroid α) {X Y : Set α} (h : X ⊆ Y) :
    natRank M X ≤ natRank M Y :=
  ENat.toNat_le_toNat (M.eRk_mono h) (rank_ne_top M Y)

omit [Fintype α] in
@[simp] lemma natRank_closure (M : Matroid α) (X : Set α) :
    natRank M (M.closure X) = natRank M X := by
  simp [natRank]

omit [Fintype α] in
@[simp] lemma natRank_empty (M : Matroid α) : natRank M ∅ = 0 := by
  simp [natRank]

lemma natRank_submod (M : Matroid α) (X Y : Set α) :
    natRank M (X ∩ Y) + natRank M (X ∪ Y) ≤ natRank M X + natRank M Y := by
  have h := ENat.toNat_le_toNat (M.eRk_submod X Y)
    (WithTop.add_ne_top.2 ⟨rank_ne_top M X, rank_ne_top M Y⟩)
  simpa only [ENat.toNat_add (rank_ne_top M _) (rank_ne_top M _), natRank] using h

omit [Fintype α] in
lemma flat_inter (M : Matroid α) {X Y : Set α} (hX : M.IsFlat X)
    (hY : M.IsFlat Y) : M.IsFlat (X ∩ Y) := by
  apply Matroid.isFlat_iff_closure_eq.2
  apply Subset.antisymm
  · exact subset_inter ((M.closure_subset_closure inter_subset_left).trans_eq hX.closure)
      ((M.closure_subset_closure inter_subset_right).trans_eq hY.closure)
  · exact M.subset_closure _ (inter_subset_left.trans hX.subset_ground)

noncomputable def densityObjective (M : Matroid α) (κ : ℕ) (D X : Set α) : ℤ :=
  (D ∩ X).ncard - (κ : ℤ) * natRank M X

lemma densityObjective_supermod (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D X Y : Set α) :
    densityObjective M κ D X + densityObjective M κ D Y ≤
      densityObjective M κ D (X ∩ Y) + densityObjective M κ D (M.closure (X ∪ Y)) := by
  have hc := ncard_union_add_ncard_inter (D ∩ X) (D ∩ Y)
  have hm := ncard_mono (inter_subset_inter_right D
    (M.subset_closure (X ∪ Y) (by simp [hE])))
  have hr := natRank_submod M X Y
  have hu : (D ∩ X) ∪ (D ∩ Y) = D ∩ (X ∪ Y) := (Set.inter_union_distrib_left D X Y).symm
  have hi : (D ∩ X) ∩ (D ∩ Y) = D ∩ (X ∩ Y) := (Set.inter_inter_distrib_left D X Y).symm
  rw [hu, hi] at hc
  have hmul : (κ : ℤ) * (natRank M (X ∩ Y) + natRank M (X ∪ Y)) ≤
      (κ : ℤ) * (natRank M X + natRank M Y) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hr) (by exact_mod_cast (Nat.zero_le κ))
  dsimp [densityObjective]
  rw [natRank_closure]
  simp only [mul_add] at hmul
  omega

def IsDensityMax (M : Matroid α) (κ : ℕ) (D P Q : Set α) : Prop :=
  M.IsFlat Q ∧ P ⊆ Q ∧ ∀ Z, M.IsFlat Z → P ⊆ Z →
    densityObjective M κ D Z ≤ densityObjective M κ D Q

lemma exists_densityMax (M : Matroid α) (κ : ℕ) (D P : Set α)
    (hP : P ⊆ M.E) : ∃ Q, IsDensityMax M κ D P Q := by
  obtain ⟨Q, hQ, hmax⟩ := Set.exists_max_image {Z | M.IsFlat Z ∧ P ⊆ Z}
    (densityObjective M κ D) (Set.toFinite _) ⟨M.E, M.ground_isFlat, hP⟩
  exact ⟨Q, hQ.1, hQ.2, fun Z hZ hPZ => hmax Z ⟨hZ, hPZ⟩⟩

lemma densityMax_union (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) {Q Q' : Set α}
    (hQ : IsDensityMax M κ D P Q) (hQ' : IsDensityMax M κ D P Q') :
    IsDensityMax M κ D P (M.closure (Q ∪ Q')) := by
  have hPQQ' : P ⊆ Q ∩ Q' := subset_inter hQ.2.1 hQ'.2.1
  have hPc : P ⊆ M.closure (Q ∪ Q') :=
    hQ.2.1.trans ((subset_union_left).trans (M.subset_closure _ (by simp [hE])))
  refine ⟨Matroid.isFlat_closure (M := M) _, hPc, ?_⟩
  intro Z hZ hPZ
  have h1 := hQ.2.2 Z hZ hPZ
  have h2 := hQ'.2.2 (Q ∩ Q') (flat_inter M hQ.1 hQ'.1) hPQQ'
  have h3 := densityObjective_supermod M hE κ D Q Q'
  omega

lemma exists_largest_densityMax (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) :
    ∃ Q, IsDensityMax M κ D P Q ∧ ∀ Q', IsDensityMax M κ D P Q' → Q' ⊆ Q := by
  obtain ⟨Q₀, hQ₀⟩ := exists_densityMax M κ D P (by simp [hE])
  obtain ⟨Q, hQ, hmax⟩ := Set.exists_max_image {Z | IsDensityMax M κ D P Z}
    Set.ncard (Set.toFinite _) ⟨Q₀, hQ₀⟩
  refine ⟨Q, hQ, ?_⟩
  intro Q' hQ'
  have hu := densityMax_union M hE κ D P hQ hQ'
  have hcard := hmax _ hu
  have hsub : Q ⊆ M.closure (Q ∪ Q') :=
    subset_union_left.trans (M.subset_closure _ (by simp [hE]))
  have heq : Q = M.closure (Q ∪ Q') := Set.eq_of_subset_of_ncard_le hsub hcard
  rw [heq]
  exact subset_union_right.trans (M.subset_closure _ (by simp [hE]))

noncomputable def densityExpansion (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) : Set α :=
  (exists_largest_densityMax M hE κ D P).choose

lemma densityExpansion_spec (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) :
    IsDensityMax M κ D P (densityExpansion M hE κ D P) ∧
      ∀ Q, IsDensityMax M κ D P Q → Q ⊆ densityExpansion M hE κ D P :=
  (exists_largest_densityMax M hE κ D P).choose_spec

lemma densityExpansion_extensive (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) : P ⊆ densityExpansion M hE κ D P :=
  (densityExpansion_spec M hE κ D P).1.2.1

lemma densityExpansion_flat (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) : M.IsFlat (densityExpansion M hE κ D P) :=
  (densityExpansion_spec M hE κ D P).1.1

lemma densityExpansion_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) {P P' : Set α} (hPP' : P ⊆ P') :
    densityExpansion M hE κ D P ⊆ densityExpansion M hE κ D P' := by
  let Q := densityExpansion M hE κ D P
  let Q' := densityExpansion M hE κ D P'
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hQ' : IsDensityMax M κ D P' Q' := (densityExpansion_spec M hE κ D P').1
  have hPint : P ⊆ Q ∩ Q' := subset_inter hQ.2.1 (hPP'.trans hQ'.2.1)
  have hP'cl : P' ⊆ M.closure (Q ∪ Q') :=
    hQ'.2.1.trans (subset_union_right.trans (M.subset_closure _ (by simp [hE])))
  have hInt := hQ.2.2 (Q ∩ Q') (flat_inter M hQ.1 hQ'.1) hPint
  have hSup := densityObjective_supermod M hE κ D Q Q'
  have hjoin : IsDensityMax M κ D P' (M.closure (Q ∪ Q')) := by
    refine ⟨Matroid.isFlat_closure (M := M) _, hP'cl, ?_⟩
    intro Z hZ hPZ
    have hm := hQ'.2.2 Z hZ hPZ
    omega
  exact (subset_union_left.trans (M.subset_closure _ (by simp [hE]))).trans
    ((densityExpansion_spec M hE κ D P').2 _ hjoin)

lemma densityExpansion_residual (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P Z : Set α) :
    let Q := densityExpansion M hE κ D P
    (D ∩ (M.closure (Q ∪ Z) \ Q)).ncard + κ * natRank M Q ≤
      κ * natRank M (Q ∪ Z) := by
  dsimp only
  let Q := densityExpansion M hE κ D P
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hQc : Q ⊆ M.closure (Q ∪ Z) :=
    subset_union_left.trans (M.subset_closure _ (by simp [hE]))
  have hmax := hQ.2.2 (M.closure (Q ∪ Z)) (Matroid.isFlat_closure (M := M) _) (hQ.2.1.trans hQc)
  have hc := Set.ncard_sdiff_add_ncard_of_subset (inter_subset_inter_right D hQc)
  have heq : D ∩ (M.closure (Q ∪ Z) \ Q) =
      (D ∩ M.closure (Q ∪ Z)) \ (D ∩ Q) := by ext; simp; tauto
  change (D ∩ (M.closure (Q ∪ Z) \ Q)).ncard + κ * natRank M Q ≤
    κ * natRank M (Q ∪ Z)
  rw [heq]
  dsimp [densityObjective] at hmax
  rw [natRank_closure] at hmax
  exact_mod_cast (show ((D ∩ M.closure (Q ∪ Z)) \ (D ∩ Q)).ncard +
    (κ : ℤ) * natRank M Q ≤ (κ : ℤ) * natRank M (Q ∪ Z) by omega)

omit [Fintype α] in
lemma natRank_eq_ncard_of_basis (M : Matroid α) {I X : Set α}
    (hI : M.IsBasis I X) : natRank M X = I.ncard := by
  rw [natRank, ← hI.encard_eq_eRk, Set.ncard_def]

lemma closure_eq_of_subset_of_natRank_le (M : Matroid α) {X Y : Set α}
    (hXY : X ⊆ Y) (hr : natRank M Y ≤ natRank M X) : M.closure X = M.closure Y := by
  apply (M.isRkFinite_set X).closure_eq_closure_of_subset_of_eRk_ge_eRk hXY
  have hcast : (natRank M Y : ℕ∞) ≤ (natRank M X : ℕ∞) := by exact_mod_cast hr
  simpa only [natRank, ENat.natCast_toNat (rank_ne_top M _)] using hcast

lemma densityExpansion_generated (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D P : Set α) :
    let Q := densityExpansion M hE κ D P
    M.closure (P ∪ (D ∩ Q)) = Q := by
  dsimp only
  let Q := densityExpansion M hE κ D P
  let A := M.closure (P ∪ (D ∩ Q))
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hAQ : A ⊆ Q := by
    exact (M.closure_subset_closure (union_subset hQ.2.1 inter_subset_right)).trans_eq hQ.1.closure
  have hPA : P ⊆ A := subset_union_left.trans (M.subset_closure _ (by simp [hE]))
  have hDA : D ∩ A = D ∩ Q := by
    apply Subset.antisymm (inter_subset_inter_right D hAQ)
    exact fun e he => ⟨he.1, M.subset_closure _ (by simp [hE]) (Or.inr he)⟩
  have hm := hQ.2.2 A (Matroid.isFlat_closure (M := M) _) hPA
  have hr : natRank M Q ≤ natRank M A := by
    dsimp [densityObjective] at hm
    rw [hDA] at hm
    have hm' : (κ : ℤ) * natRank M Q ≤ (κ : ℤ) * natRank M A := by omega
    have hk' : (0 : ℤ) < κ := by exact_mod_cast hκ
    exact_mod_cast (le_of_mul_le_mul_left hm' hk')
  have heq := closure_eq_of_subset_of_natRank_le M hAQ hr
  simpa only [A, M.closure_closure, hQ.1.closure] using heq

lemma exists_extension_generators (M : Matroid α) (hE : M.E = univ)
    (R D Q : Set α) (_hR : M.IsFlat R) (hgen : M.closure (R ∪ D) = Q) :
    ∃ K : Set α, K ⊆ D \ R ∧ M.closure (R ∪ K) = Q ∧
      K.ncard + natRank M R = natRank M Q := by
  obtain ⟨I, hI, hIR⟩ := M.exists_isBasis_union_inter_isBasis D R
    (by simp [hE]) (by simp [hE])
  refine ⟨I \ R, ?_, ?_, ?_⟩
  · intro e he
    refine ⟨?_, he.2⟩
    rcases hI.subset he.1 with hD | hr
    · exact hD
    · exact (he.2 hr).elim
  · apply Subset.antisymm
    · have hsub : R ∪ (I \ R) ⊆ R ∪ D := by
        intro e he
        rcases he with hr | hi
        · exact Or.inl hr
        · rcases hI.subset hi.1 with hd | hr
          · exact Or.inr hd
          · exact Or.inl hr
      exact (M.closure_subset_closure hsub).trans_eq hgen
    · have hIsub : I ⊆ R ∪ (I \ R) := by intro e he; by_cases hr : e ∈ R <;> simp_all
      calc
        Q = M.closure (D ∪ R) := by rw [union_comm D R, hgen]
        _ = M.closure I := hI.closure_eq_closure.symm
        _ ⊆ M.closure (R ∪ (I \ R)) := M.closure_subset_closure hIsub
  · have hiRank : natRank M Q = I.ncard := by
      rw [← hgen, natRank_closure, union_comm R D]
      exact natRank_eq_ncard_of_basis M hI
    rw [natRank_eq_ncard_of_basis M hIR, hiRank]
    simpa only [add_comm] using Set.ncard_inter_add_ncard_sdiff_eq_ncard I R

lemma densityExpansion_generator_step (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D P R : Set α) (hR : M.IsFlat R)
    (hPR : P ⊆ R) (hRQ : R ⊆ densityExpansion M hE κ D P) :
    ∃ K : Set α,
      K ⊆ (D ∩ densityExpansion M hE κ D P) \ R ∧
      M.closure (R ∪ K) = densityExpansion M hE κ D P ∧
      κ * K.ncard + (D ∩ R).ncard ≤
        (D ∩ densityExpansion M hE κ D P).ncard := by
  let Q := densityExpansion M hE κ D P
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hgen : M.closure (R ∪ (D ∩ Q)) = Q := by
    apply Subset.antisymm
    · exact (M.closure_subset_closure (union_subset hRQ inter_subset_right)).trans_eq hQ.1.closure
    · calc
        Q = M.closure (P ∪ (D ∩ Q)) := (densityExpansion_generated M hE κ hκ D P).symm
        _ ⊆ M.closure (R ∪ (D ∩ Q)) :=
          M.closure_subset_closure (union_subset_union hPR Subset.rfl)
  obtain ⟨K, hK, hKgen, hKcard⟩ := exists_extension_generators M hE R (D ∩ Q) Q hR hgen
  refine ⟨K, hK, hKgen, ?_⟩
  have hm := hQ.2.2 R hR hPR
  dsimp [densityObjective] at hm
  have hmul := congrArg (fun x : ℕ => κ * x) hKcard
  rw [Nat.mul_add] at hmul
  exact_mod_cast (show (κ : ℤ) * K.ncard + (D ∩ R).ncard ≤ (D ∩ Q).ncard by
    have hmul' : (κ : ℤ) * K.ncard + (κ : ℤ) * natRank M R =
        (κ : ℤ) * natRank M Q := by exact_mod_cast hmul
    omega)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open Set Finset

variable {α : Type*} [Fintype α]

noncomputable def conditionalRank (M : Matroid α) (S P : Set α) : ℕ :=
  natRank M (S ∪ P) - natRank M P

lemma conditionalRank_add_base (M : Matroid α) (S P : Set α) :
    conditionalRank M S P + natRank M P = natRank M (S ∪ P) := by
  exact Nat.sub_add_cancel (natRank_mono M subset_union_right)

lemma conditionalRank_antitone (M : Matroid α) (S : Set α)
    {P Q : Set α} (hPQ : P ⊆ Q) :
    conditionalRank M S Q ≤ conditionalRank M S P := by
  have hsub := natRank_submod M (S ∪ P) Q
  have hi := natRank_mono M (show P ⊆ (S ∪ P) ∩ Q from
    fun x hx => ⟨Or.inr hx, hPQ hx⟩)
  have hu : (S ∪ P) ∪ Q = S ∪ Q := by
    ext x
    simp only [mem_union]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (hPQ h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  rw [hu] at hsub
  have hP := conditionalRank_add_base M S P
  have hQ := conditionalRank_add_base M S Q
  omega

lemma conditionalRank_exchange (M : Matroid α) (S J A : Set α) :
    conditionalRank M S A + conditionalRank M J (A ∪ S) =
      conditionalRank M J A + conditionalRank M S (A ∪ J) := by
  have hSA := conditionalRank_add_base M S A
  have hJA := conditionalRank_add_base M J A
  have hJAS := conditionalRank_add_base M J (A ∪ S)
  have hSAJ := conditionalRank_add_base M S (A ∪ J)
  have hUS : S ∪ A = A ∪ S := union_comm _ _
  have hUJ : J ∪ A = A ∪ J := union_comm _ _
  have hU : J ∪ (A ∪ S) = S ∪ (A ∪ J) := by
    ext x
    simp only [mem_union]
    tauto
  rw [hUS] at hSA
  rw [hUJ] at hJA
  rw [hU] at hJAS
  omega

omit [Fintype α] in
lemma conditionalRank_closure (M : Matroid α) (S P : Set α) :
    conditionalRank M S (M.closure P) = conditionalRank M S P := by
  simp only [conditionalRank, natRank, M.eRk_union_closure_right_eq,
    M.eRk_closure_eq]

lemma conditionalRank_le_rank (M : Matroid α) (J A : Set α) :
    conditionalRank M J A ≤ natRank M J := by
  have h := conditionalRank_antitone M J (empty_subset A)
  simpa [conditionalRank] using h

lemma rankCost_step (M : Matroid α) (J S A B X Y : Set α)
    (hXA : X ⊆ A) (hAB : A ⊆ B)
    (hB : B ⊆ M.closure (A ∪ J)) (hY : A ∪ S ⊆ Y) :
    conditionalRank M S A - conditionalRank M S B ≤
      conditionalRank M J X - conditionalRank M J Y := by
  have hSJ := conditionalRank_antitone M S hB
  rw [conditionalRank_closure] at hSJ
  have hSA := conditionalRank_antitone M S hAB
  have hJA := conditionalRank_antitone M J hXA
  have hJY := conditionalRank_antitone M J hY
  have heq := conditionalRank_exchange M S J A
  omega

lemma sum_potential_drop_le (p : ℕ → ℕ) (m : ℕ)
    (hp : ∀ k < m, p (k + 1) ≤ p k) :
    (∑ k ∈ range m, (p k - p (k + 1))) ≤ p 0 := by
  suffices h : (∑ k ∈ range m, (p k - p (k + 1))) + p m = p 0 by omega
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hprev := ih (fun k hk => hp k (Nat.lt_trans hk (Nat.lt_succ_self m)))
    have hlast := hp m (Nat.lt_succ_self m)
    omega

lemma rankCost_chain (M : Matroid α) (J : Set α) (m : ℕ)
    (X A B S : ℕ → Set α)
    (hXA : ∀ k < m, X k ⊆ A k)
    (hAB : ∀ k < m, A k ⊆ B k)
    (hB : ∀ k < m, B k ⊆ M.closure (A k ∪ J))
    (hY : ∀ k < m, A k ∪ S k ⊆ X (k + 1)) :
    (∑ k ∈ range m, conditionalRank M (S k) (A k)) ≤
      (∑ k ∈ range m, conditionalRank M (S k) (B k)) + natRank M J := by
  have hmono : ∀ k < m, X k ⊆ X (k + 1) := by
    intro k hk
    exact (hXA k hk).trans (subset_union_left.trans (hY k hk))
  have hp : ∀ k < m, conditionalRank M J (X (k + 1)) ≤
      conditionalRank M J (X k) := fun k hk => conditionalRank_antitone M J (hmono k hk)
  have hdrop := sum_potential_drop_le (fun k => conditionalRank M J (X k)) m hp
  have hsum : (∑ k ∈ range m, conditionalRank M (S k) (A k)) ≤
      ∑ k ∈ range m, (conditionalRank M (S k) (B k) +
        (conditionalRank M J (X k) - conditionalRank M J (X (k + 1)))) := by
    apply sum_le_sum
    intro k hk
    have hk' := mem_range.1 hk
    have hs := rankCost_step M J (S k) (A k) (B k) (X k) (X (k + 1))
      (hXA k hk') (hAB k hk') (hB k hk') (hY k hk')
    have ha := conditionalRank_antitone M (S k) (hAB k hk')
    omega
  rw [sum_add_distrib] at hsum
  have hbound := conditionalRank_le_rank M J (X 0)
  omega

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [DecidableEq α]

noncomputable def layerPrior (E : Finset α) (layer : α → ℤ) (time : α → ℕ)
    (b : ℤ) (k : ℕ) : Set α := {e | e ∈ E ∧ layer e = b ∧ time e < k}

noncomputable def layerGreedy (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ) : Finset α := by
  classical
  exact E.filter fun e => e ∉ M.closure (base (layer e) ∪ layerPrior E layer time (layer e) (time e))

omit [DecidableEq α] in
lemma layerGreedy_subset (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ) :
    layerGreedy M E base layer time ⊆ E := by
  classical
  exact filter_subset _ _

omit [DecidableEq α] in
lemma layerPrior_mono (E : Finset α) (layer : α → ℤ) (time : α → ℕ)
    (b : ℤ) {k k' : ℕ} (h : k ≤ k') :
    layerPrior E layer time b k ⊆ layerPrior E layer time b k' := by
  rintro e ⟨he, hb, ht⟩
  exact ⟨he, hb, lt_of_lt_of_le ht h⟩

lemma layerGreedy_spans_prefix (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (hE : M.E = Set.univ) (e : α) (he : e ∈ E) :
    e ∈ M.closure (base (layer e) ∪
      {f | f ∈ layerGreedy M E base layer time ∧ layer f = layer e ∧ time f ≤ time e}) := by
  have aux : ∀ k, ∀ e ∈ E, time e = k →
      e ∈ M.closure (base (layer e) ∪
        {f | f ∈ layerGreedy M E base layer time ∧ layer f = layer e ∧ time f ≤ k}) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro e he htime
      by_cases hkeep : e ∈ layerGreedy M E base layer time
      · exact M.mem_closure_of_mem' (Or.inr ⟨hkeep, rfl, htime.le⟩) (by simp [hE])
      have hdep : e ∈ M.closure (base (layer e) ∪ layerPrior E layer time (layer e) (time e)) := by
        simpa only [layerGreedy, mem_filter, he, true_and, not_not] using hkeep
      apply M.closure_subset_closure_of_subset_closure ?_ hdep
      rintro f (hf | ⟨hf, hl, ht⟩)
      · exact M.mem_closure_of_mem' (Or.inl hf) (by simp [hE])
      · have hfk : time f < k := by simpa [htime] using ht
        have hrec := ih (time f) hfk f hf rfl
        apply M.closure_subset_closure ?_ hrec
        rintro g (hg | ⟨hg, hgl, hgt⟩)
        · exact Or.inl (by simpa [hl] using hg)
        · exact Or.inr ⟨hg, hgl.trans hl, hgt.trans hfk.le⟩
  exact aux (time e) e he rfl

theorem layerGreedy_indep (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (hE : M.E = Set.univ) (htime : Function.Injective time)
    (hlower : ∀ e ∈ E, ∀ f ∈ E, layer e < layer f → e ∈ base (layer f)) :
    M.Indep (layerGreedy M E base layer time : Set α) := by
  classical
  suffices aux : ∀ A : Finset α, A ⊆ layerGreedy M E base layer time →
      M.Indep (A : Set α) from aux _ Finset.Subset.rfl
  intro A
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    intro hA
    by_cases hne : A.Nonempty
    · obtain ⟨p₀, hp₀, hmaxLayer⟩ := exists_max_image A layer hne
      have htne : (A.filter (fun e => layer e = layer p₀)).Nonempty :=
        ⟨p₀, mem_filter.mpr ⟨hp₀, rfl⟩⟩
      obtain ⟨p, hpt, hmaxTime⟩ := exists_max_image
        (A.filter (fun e => layer e = layer p₀)) time htne
      have hp : p ∈ A := (mem_filter.mp hpt).1
      have hpl : layer p = layer p₀ := (mem_filter.mp hpt).2
      have hpE := layerGreedy_subset M E base layer time (hA hp)
      have hI := ih (A.erase p) (erase_ssubset hp)
        (fun e he => hA (mem_of_mem_erase he))
      have hnot : p ∉ M.closure (A.erase p : Set α) := by
        intro hmem
        have hpnot := (mem_filter.mp (hA hp)).2
        apply hpnot
        apply M.closure_subset_closure ?_ hmem
        intro q hq
        have hqA := mem_of_mem_erase hq
        have hqE := layerGreedy_subset M E base layer time (hA hqA)
        have hqle : layer q ≤ layer p := by simpa [hpl] using hmaxLayer q hqA
        rcases lt_or_eq_of_le hqle with hqlt | hqeq
        · exact Or.inl (hlower q hqE p hpE hqlt)
        · refine Or.inr ⟨hqE, hqeq, ?_⟩
          have hqt : q ∈ A.filter (fun e => layer e = layer p₀) :=
            mem_filter.mpr ⟨hqA, hqeq.trans hpl⟩
          exact lt_of_le_of_ne (hmaxTime q hqt) (fun h => (ne_of_mem_erase hq) (htime h))
      have hins := hI.insert_indep_iff.mpr (Or.inl ⟨by simp [hE], hnot⟩)
      simpa only [← Finset.coe_insert, insert_erase hp] using hins
    · have hzero := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hzero]

lemma layerGreedy_spans (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (hE : M.E = Set.univ) (b : ℤ) :
    {e | e ∈ E ∧ layer e = b} ⊆
      M.closure (base b ∪ {e | e ∈ layerGreedy M E base layer time ∧ layer e = b}) := by
  rintro e ⟨he, hb⟩
  have h := layerGreedy_spans_prefix M E base layer time hE e he
  apply M.closure_subset_closure ?_ h
  rintro f (hf | ⟨hf, hfb, _⟩)
  · exact Or.inl (by simpa [hb] using hf)
  · exact Or.inr ⟨hf, hfb.trans hb⟩

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset

noncomputable def assignedEligible {n : ℕ} {K : Type*}
    (assign : Fin n → K → Option ℤ) (v : Fin n → K) : Finset (Fin n) := by
  classical
  exact univ.filter fun e => assign e (v e) ≠ none

def assignedLayer {n : ℕ} {K : Type*}
    (assign : Fin n → K → Option ℤ) (v : Fin n → K) (e : Fin n) : ℤ :=
  (assign e (v e)).getD 0

noncomputable def layerKeyDecision {n : ℕ} {K : Type*}
    (M : Matroid (Fin n)) (base : ℤ → Set (Fin n))
    (assign : Fin n → K → Option ℤ) (k : Fin n)
    (hist : Fin (k.val+1) → Fin n × K) : Bool := by
  classical
  let current := hist ⟨k.val, Nat.lt_succ_self _⟩
  exact match assign current.1 current.2 with
  | none => false
  | some b => decide (current.1 ∉ M.closure (base b ∪
      {f | ∃ j : Fin (k.val+1), j.val < k.val ∧ (hist j).1 = f ∧
        assign (hist j).1 (hist j).2 = some b}))

def keyHistory {n : ℕ} {K : Type*} (v : Fin n → K)
    (π : ArrivalOrder n) (k : Fin n) : Fin (k.val+1) → Fin n × K :=
  fun j => (π (prefixIndex k j), v (π (prefixIndex k j)))

lemma keyHistory_current {n : ℕ} {K : Type*} (v : Fin n → K)
    (π : ArrivalOrder n) (k : Fin n) :
    keyHistory v π k ⟨k.val, Nat.lt_succ_self _⟩ = (π k, v (π k)) := by
  rfl

lemma keyHistory_prior {n : ℕ} {K : Type*} (v : Fin n → K)
    (assign : Fin n → K → Option ℤ) (π : ArrivalOrder n) (k : Fin n) (b : ℤ) :
    {f | ∃ j : Fin (k.val+1), j.val < k.val ∧ (keyHistory v π k j).1 = f ∧
      assign (keyHistory v π k j).1 (keyHistory v π k j).2 = some b} =
    layerPrior (assignedEligible assign v) (assignedLayer assign v)
      (fun e => (π.symm e).val) b k.val := by
  classical
  ext f
  have hel : f ∈ assignedEligible assign v ∧ assignedLayer assign v f = b ↔
      assign f (v f) = some b := by
    cases h : assign f (v f) <;> simp [assignedEligible, assignedLayer, h]
  constructor
  · rintro ⟨j, hj, rfl, hb⟩
    simp only [keyHistory] at *
    refine ⟨?_, ?_, ?_⟩
    · simp [assignedEligible, hb]
    · simp [assignedLayer, hb]
    · simpa [prefixIndex] using hj
  · rintro ⟨he, hb, ht⟩
    change (π.symm f).val < k.val at ht
    have hass := hel.mp ⟨he, hb⟩
    let j : Fin (k.val+1) := ⟨(π.symm f).val, by omega⟩
    have hidx : prefixIndex k j = π.symm f := by rfl
    refine ⟨j, ht, ?_, ?_⟩
    · simp [keyHistory, hidx]
    · simpa [keyHistory, hidx] using hass

theorem layerKeyDecision_eq_greedy {n : ℕ} {K : Type*}
    (M : Matroid (Fin n)) (base : ℤ → Set (Fin n))
    (assign : Fin n → K → Option ℤ) (v : Fin n → K)
    (π : ArrivalOrder n) (k : Fin n) :
    layerKeyDecision M base assign k (keyHistory v π k) = true ↔
      π k ∈ layerGreedy M (assignedEligible assign v) base (assignedLayer assign v)
        (fun e => (π.symm e).val) := by
  classical
  unfold layerKeyDecision
  rw [keyHistory_current]
  dsimp only
  cases h : assign (π k) (v (π k)) with
  | none => simp [assignedEligible, layerGreedy, h]
  | some b =>
    dsimp only
    rw [keyHistory_prior]
    simp [layerGreedy, assignedEligible, assignedLayer, h]

noncomputable def layerOnlineRule {n bits : ℕ} {K : Type*} [Countable K]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (M : Matroid (Fin n)) (key : ℝ → K) (hkey : Measurable key)
    (base : Seed bits → (Fin n → K) → ℤ → Set (Fin n))
    (assign : Seed bits → (Fin n → K) → Fin n → K → Option ℤ) : OnlineRule n bits :=
  discreteOnlineRule key hkey fun k r s hist =>
    layerKeyDecision M (base r s) (assign r s) k hist

theorem layerOnlineRule_accepted {n bits : ℕ} {K : Type*} [Countable K]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (M : Matroid (Fin n)) (key : ℝ → K) (hkey : Measurable key)
    (base : Seed bits → (Fin n → K) → ℤ → Set (Fin n))
    (assign : Seed bits → (Fin n → K) → Fin n → K → Option ℤ)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) :
    accepted (layerOnlineRule M key hkey base assign) r s v π =
      layerGreedy M (assignedEligible (assign r (fun e => key (s e))) (fun e => key (v e)))
        (base r (fun e => key (s e)))
        (assignedLayer (assign r (fun e => key (s e))) (fun e => key (v e)))
        (fun e => (π.symm e).val) := by
  classical
  ext e
  simp only [accepted, acceptedThrough, mem_filter, Finset.mem_univ, true_and,
    (π.symm e).isLt]
  change layerKeyDecision M (base r (fun e => key (s e))) (assign r (fun e => key (s e)))
    (π.symm e) (keyHistory (fun f => key (v f)) π (π.symm e)) = true ↔ _
  simpa only [Equiv.apply_symm_apply] using
    layerKeyDecision_eq_greedy M (base r (fun e => key (s e)))
      (assign r (fun e => key (s e))) (fun e => key (v e)) π (π.symm e)

lemma acceptedThrough_subset_accepted {n bits : ℕ} (A : OnlineRule n bits)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    acceptedThrough A r s v π t ⊆ accepted A r s v π := by
  classical
  intro e he
  have hd := (mem_filter.mp he).2.2
  exact mem_filter.mpr ⟨mem_univ e, (π.symm e).isLt, hd⟩

theorem layerOnlineRule_feasible {n bits : ℕ} {K : Type*} [Countable K]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (M : Matroid (Fin n)) (hE : M.E = Set.univ) (key : ℝ → K) (hkey : Measurable key)
    (base : Seed bits → (Fin n → K) → ℤ → Set (Fin n))
    (assign : Seed bits → (Fin n → K) → Fin n → K → Option ℤ)
    (hlower : ∀ r s v, ∀ e ∈ assignedEligible (assign r s) v,
      ∀ f ∈ assignedEligible (assign r s) v,
      assignedLayer (assign r s) v e < assignedLayer (assign r s) v f →
        e ∈ base r s (assignedLayer (assign r s) v f)) :
    Feasible M (layerOnlineRule M key hkey base assign) := by
  intro r s v π t _ _
  have htime : Function.Injective (fun e => (π.symm e).val) := by
    intro e f h
    exact π.symm.injective (Fin.ext h)
  have hi := layerGreedy_indep M
    (assignedEligible (assign r (fun e => key (s e))) (fun e => key (v e)))
    (base r (fun e => key (s e)))
    (assignedLayer (assign r (fun e => key (s e))) (fun e => key (v e)))
    (fun e => (π.symm e).val) hE htime
    (hlower r (fun e => key (s e)) (fun e => key (v e)))
  apply hi.subset
  intro e he
  have hm := acceptedThrough_subset_accepted (layerOnlineRule M key hkey base assign)
    r s v π t he
  rwa [layerOnlineRule_accepted] at hm

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set

variable {α : Type*} [Fintype α]

private lemma densityPath_prefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D : Set α) (P : ℕ → Set α) (hP : Monotone P) (N : ℕ) :
    ∃ J : ℕ → Set α, Monotone J ∧ (∀ k, J k ⊆ D) ∧
      (∀ k ≤ N, M.closure (P k ∪ J k) = densityExpansion M hE κ D (P k)) ∧
      κ * (J N).ncard ≤ (D ∩ densityExpansion M hE κ D (P N)).ncard ∧
      (∀ k, N ≤ k → J k = J N) := by
  induction N with
  | zero =>
    have hPQ : M.closure (P 0) ⊆ densityExpansion M hE κ D (P 0) := by
      exact (M.closure_subset_closure (densityExpansion_extensive M hE κ D (P 0))).trans_eq
        (densityExpansion_flat M hE κ D (P 0)).closure
    obtain ⟨K, hK, hgen, hcard⟩ := densityExpansion_generator_step M hE κ hκ D (P 0)
      (M.closure (P 0)) (Matroid.isFlat_closure (M := M) _)
      (M.subset_closure _ (by simp [hE])) hPQ
    refine ⟨fun _ => K, fun _ _ _ => Subset.rfl, ?_, ?_, ?_, ?_⟩
    · exact fun _ _ he => (hK he).1.1
    · intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simpa only [M.closure_union_closure_left_eq] using hgen
    · dsimp only
      omega
    · exact fun _ _ => rfl
  | succ N ih =>
    obtain ⟨J, hJmono, hJD, hJgen, hJcard, hJsat⟩ := ih
    let Q := densityExpansion M hE κ D (P N)
    let Q' := densityExpansion M hE κ D (P (N + 1))
    let R := M.closure (P (N + 1) ∪ Q)
    have hQQ' : Q ⊆ Q' := densityExpansion_mono M hE κ D (hP (Nat.le_succ N))
    have hRflat : M.IsFlat R := Matroid.isFlat_closure (M := M) _
    have hPR : P (N + 1) ⊆ R :=
      subset_union_left.trans (M.subset_closure _ (by simp [hE]))
    have hQR : Q ⊆ R := subset_union_right.trans (M.subset_closure _ (by simp [hE]))
    have hRQ' : R ⊆ Q' := by
      exact (M.closure_subset_closure
        (union_subset (densityExpansion_extensive M hE κ D _) hQQ')).trans_eq
        (densityExpansion_flat M hE κ D _).closure
    obtain ⟨K, hK, hKgen, hKcard⟩ :=
      densityExpansion_generator_step M hE κ hκ D (P (N + 1)) R hRflat hPR hRQ'
    have hJNQ : J N ⊆ Q := by
      change J N ⊆ densityExpansion M hE κ D (P N)
      rw [← hJgen N le_rfl]
      exact subset_union_right.trans (M.subset_closure _ (by simp [hE]))
    have hJNR : J N ⊆ R := hJNQ.trans hQR
    have hdisj : Disjoint (J N) K := by
      rw [Set.disjoint_left]
      intro e heJ heK
      exact (hK heK).2 (hJNR heJ)
    have hRgen : M.closure (P (N + 1) ∪ J N) = R := by
      apply Subset.antisymm
      · exact M.closure_subset_closure (union_subset_union Subset.rfl hJNQ)
      · apply Matroid.closure_subset_closure_of_subset_closure
        apply union_subset
        · exact subset_union_left.trans (M.subset_closure _ (by simp [hE]))
        · change densityExpansion M hE κ D (P N) ⊆ _
          rw [← hJgen N le_rfl]
          exact M.closure_subset_closure (union_subset_union (hP (Nat.le_succ N)) Subset.rfl)
    have hnewgen : M.closure (P (N + 1) ∪ (J N ∪ K)) = Q' := by
      calc
        M.closure (P (N + 1) ∪ (J N ∪ K)) =
            M.closure ((P (N + 1) ∪ J N) ∪ K) := by rw [union_assoc]
        _ = M.closure (M.closure (P (N + 1) ∪ J N) ∪ K) :=
          (M.closure_union_closure_left_eq _ _).symm
        _ = M.closure (R ∪ K) := by rw [hRgen]
        _ = Q' := hKgen
    have hnewcard : κ * (J N ∪ K).ncard ≤ (D ∩ Q').ncard := by
      rw [Set.ncard_union_eq hdisj, Nat.mul_add]
      have hm := Set.ncard_mono (inter_subset_inter_right D hQR)
      change κ * K.ncard + (D ∩ R).ncard ≤ (D ∩ Q').ncard at hKcard
      change κ * (J N).ncard ≤ (D ∩ Q).ncard at hJcard
      omega
    let J' : ℕ → Set α := fun k => if k ≤ N then J k else J N ∪ K
    have hJ'last : J' (N + 1) = J N ∪ K := by simp [J']
    refine ⟨J', ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      by_cases hi : i ≤ N
      · by_cases hj : j ≤ N
        · simpa [J', hi, hj] using hJmono hij
        · change (if i ≤ N then J i else J N ∪ K) ⊆ _
          rw [ite_eq_left hi]
          simpa only [J', ite_eq_right hj] using (hJmono hi).trans subset_union_left
      · have hj : ¬j ≤ N := by omega
        simp only [J', ite_eq_right hi, ite_eq_right hj]
        exact Subset.rfl
    · intro k e he
      by_cases hk : k ≤ N
      · exact hJD k (by simpa [J', hk] using he)
      · have he' : e ∈ J N ∪ K := by simpa [J', hk] using he
        rcases he' with heJ | heK
        · exact hJD N heJ
        · exact (hK heK).1.1
    · intro k hk
      by_cases hk' : k ≤ N
      · simpa [J', hk'] using hJgen k hk'
      · have heq : k = N + 1 := by omega
        subst k
        rw [hJ'last]
        exact hnewgen
    · rw [hJ'last]
      exact hnewcard
    · intro k hk
      have hk' : ¬ k ≤ N := by omega
      rw [hJ'last]
      simp [J', hk']

lemma densityPath_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D : Set α) (P : ℕ → Set α) (hP : Monotone P) (N : ℕ) :
    ∃ Jtotal : Set α, Jtotal ⊆ D ∧ κ * Jtotal.ncard ≤ D.ncard ∧
      ∃ J : ℕ → Set α, Monotone J ∧ (∀ k ≤ N, J k ⊆ Jtotal) ∧
        (∀ k ≤ N, M.closure (P k ∪ J k) = densityExpansion M hE κ D (P k)) := by
  obtain ⟨J, hmono, hD, hgen, hcard, _⟩ := densityPath_prefix M hE κ hκ D P hP N
  refine ⟨J N, hD N, ?_, J, hmono, ?_, hgen⟩
  · exact hcard.trans (Set.ncard_mono inter_subset_left)
  · exact fun k hk => hmono hk

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

noncomputable def densityEnabled (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a k : ℤ) (P : Set α) : Set α :=
  if a ≤ k then densityExpansion M hE κ D P else P

lemma densityEnabled_extensive (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a k : ℤ) (P : Set α) :
    P ⊆ densityEnabled M hE κ D a k P := by
  by_cases hak : a ≤ k
  · simpa only [densityEnabled, ite_eq_left hak] using densityExpansion_extensive M hE κ D P
  · simp only [densityEnabled, ite_eq_right hak, Subset.rfl]

lemma densityEnabled_flat (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a k : ℤ) {P : Set α} (hP : M.IsFlat P) :
    M.IsFlat (densityEnabled M hE κ D a k P) := by
  by_cases hak : a ≤ k
  · simpa only [densityEnabled, ite_eq_left hak] using densityExpansion_flat M hE κ D P
  · simpa only [densityEnabled, ite_eq_right hak] using hP

lemma densityEnabled_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a : ℤ) {k k' : ℤ} {P P' : Set α}
    (hkk' : k ≤ k') (hPP' : P ⊆ P') :
    densityEnabled M hE κ D a k P ⊆ densityEnabled M hE κ D a k' P' := by
  by_cases hak : a ≤ k
  · have hak' := hak.trans hkk'
    simpa only [densityEnabled, ite_eq_left hak, ite_eq_left hak'] using
      densityExpansion_mono M hE κ D hPP'
  · by_cases hak' : a ≤ k'
    · simpa only [densityEnabled, ite_eq_right hak, ite_eq_left hak'] using
        hPP'.trans (densityExpansion_extensive M hE κ D P')
    · simpa only [densityEnabled, ite_eq_right hak, ite_eq_right hak'] using hPP'

lemma densityEnabled_univ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a k : ℤ) : densityEnabled M hE κ D a k univ = univ :=
  Set.eq_univ_of_univ_subset (densityEnabled_extensive M hE κ D a k univ)

def activation (h : ℕ) : ℤ := -3 * ((h : ℤ) + 1)

noncomputable def guardedPath (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) : ℕ → ℤ → Set α
  | 0, k => if k < 0 then M.closure ∅ else univ
  | h + 1, k =>
      M.closure (densityEnabled M hE κ (D h) (activation h) k
          (guardedPath M hE κ D C h k) ∪
        (C h ∩ densityEnabled M hE κ (D h) (activation h) (k + 1)
          (guardedPath M hE κ D C h (k + 1))))

noncomputable def nominalPath (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) : Set α :=
  densityEnabled M hE κ (D h) (activation h) k (guardedPath M hE κ D C h k)

lemma guardedPath_succ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    guardedPath M hE κ D C (h+1) k =
      M.closure (nominalPath M hE κ D C h k ∪ (C h ∩ nominalPath M hE κ D C h (k+1))) := rfl

lemma guardedPath_flat (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    M.IsFlat (guardedPath M hE κ D C h k) := by
  cases h with
  | zero =>
    by_cases hk : k < 0
    · simpa only [guardedPath, ite_eq_left hk] using Matroid.isFlat_closure (M := M) ∅
    · simpa only [guardedPath, ite_eq_right hk, ← hE] using M.ground_isFlat
  | succ h => exact Matroid.isFlat_closure (M := M) _

lemma nominalPath_flat (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    M.IsFlat (nominalPath M hE κ D C h k) :=
  densityEnabled_flat M hE κ (D h) (activation h) k (guardedPath_flat M hE κ D C h k)

lemma guardedPath_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) : Monotone (guardedPath M hE κ D C h) := by
  induction h with
  | zero =>
    intro i j hij
    by_cases hi : i < 0
    · by_cases hj : j < 0
      · simp only [guardedPath, ite_eq_left hi, ite_eq_left hj, Subset.rfl]
      · simp only [guardedPath, ite_eq_left hi, ite_eq_right hj, subset_univ]
    · have hj : ¬ j < 0 := by omega
      simp only [guardedPath, ite_eq_right hi, ite_eq_right hj, Subset.rfl]
  | succ h ih =>
    intro i j hij
    apply M.closure_subset_closure
    exact union_subset_union (densityEnabled_mono M hE κ (D h) (activation h) hij (ih hij))
      (inter_subset_inter_right (C h)
        (densityEnabled_mono M hE κ (D h) (activation h) (by omega) (ih (by omega))))

lemma nominalPath_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) : Monotone (nominalPath M hE κ D C h) := by
  intro i j hij
  exact densityEnabled_mono M hE κ (D h) (activation h) hij
    (guardedPath_mono M hE κ D C h hij)

lemma guarded_subset_nominal (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    guardedPath M hE κ D C h k ⊆ nominalPath M hE κ D C h k :=
  densityEnabled_extensive M hE κ (D h) (activation h) k _

lemma nominal_subset_guarded (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    nominalPath M hE κ D C h k ⊆ guardedPath M hE κ D C (h+1) k :=
  subset_union_left.trans (M.subset_closure _ (by simp [hE]))

lemma guarded_subset_next_nominal (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    guardedPath M hE κ D C (h+1) k ⊆ nominalPath M hE κ D C h (k+1) := by
  have hs : nominalPath M hE κ D C h k ∪ (C h ∩ nominalPath M hE κ D C h (k+1)) ⊆
      nominalPath M hE κ D C h (k+1) :=
    union_subset (nominalPath_mono M hE κ D C h (by omega)) inter_subset_right
  exact (M.closure_subset_closure hs).trans_eq (nominalPath_flat M hE κ D C h (k+1)).closure

lemma guardedPath_nonnegative (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : 0 ≤ k) :
    guardedPath M hE κ D C h k = univ := by
  induction h generalizing k with
  | zero => simp [guardedPath, not_lt_of_ge hk]
  | succ h ih =>
    rw [guardedPath, ih hk, ih (by omega), densityEnabled_univ, densityEnabled_univ]
    simp [hE]

lemma nominalPath_nonnegative (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : 0 ≤ k) :
    nominalPath M hE κ D C h k = univ := by
  rw [nominalPath, guardedPath_nonnegative M hE κ D C h hk, densityEnabled_univ]

lemma guardedPath_early (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : k < -3 * (h : ℤ) - 1) :
    guardedPath M hE κ D C h k = M.closure ∅ := by
  induction h generalizing k with
  | zero =>
    have hk' : k < 0 := by omega
    simp [guardedPath, hk']
  | succ h ih =>
    have hka : ¬ activation h ≤ k := by dsimp [activation]; push_cast at hk; omega
    have hk'a : ¬ activation h ≤ k+1 := by dsimp [activation]; push_cast at hk; omega
    have hkold : k < -3 * (h : ℤ) - 1 := by push_cast at hk; omega
    have hk'old : k+1 < -3 * (h : ℤ) - 1 := by omega
    rw [guardedPath, densityEnabled, densityEnabled, ite_eq_right hka, ite_eq_right hk'a,
      ih hkold, ih hk'old]
    rw [union_eq_self_of_subset_right inter_subset_right, M.closure_closure]

lemma nominalPath_early (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : k < activation h) :
    nominalPath M hE κ D C h k = M.closure ∅ := by
  rw [nominalPath, densityEnabled, ite_eq_right (not_le_of_gt hk)]
  apply guardedPath_early
  dsimp [activation] at hk
  omega

lemma nominalPath_baseline (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) :
    nominalPath M hE κ D C h (activation h) =
      densityExpansion M hE κ (D h) (M.closure ∅) := by
  rw [nominalPath, densityEnabled, ite_eq_left le_rfl, guardedPath_early]
  dsimp [activation]
  omega

lemma nominalPath_baseline_gap (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) :
    nominalPath M hE κ D C h (activation h + 1) =
      nominalPath M hE κ D C h (activation h) := by
  rw [nominalPath_baseline, nominalPath, densityEnabled, ite_eq_left (by omega), guardedPath_early]
  dsimp [activation]
  omega

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

def pathHorizon (h : ℕ) : ℕ := 3 * (h + 1)

lemma activation_add_horizon (h : ℕ) : activation h + (pathHorizon h : ℤ) = 0 := by
  dsimp [activation, pathHorizon]
  omega

lemma exists_nominal_member (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    ∃ j : ℕ, e ∈ nominalPath M hE κ D C h (activation h + j) := by
  refine ⟨pathHorizon h, ?_⟩
  rw [activation_add_horizon, nominalPath_nonnegative M hE κ D C h (by omega)]
  trivial

noncomputable def nominalBirth (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) : ℤ :=
  activation h + Nat.find (exists_nominal_member M hE κ D C h e)

lemma nominalBirth_mem (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    e ∈ nominalPath M hE κ D C h (nominalBirth M hE κ D C h e) :=
  Nat.find_spec (exists_nominal_member M hE κ D C h e)

lemma nominalBirth_bounds (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    activation h ≤ nominalBirth M hE κ D C h e ∧ nominalBirth M hE κ D C h e ≤ 0 := by
  have hmem : e ∈ nominalPath M hE κ D C h (activation h + (pathHorizon h : ℤ)) := by
    rw [activation_add_horizon, nominalPath_nonnegative M hE κ D C h (by omega)]
    trivial
  have hle := Nat.find_min' (exists_nominal_member M hE κ D C h e) hmem
  have hi : (Nat.find (exists_nominal_member M hE κ D C h e) : ℤ) ≤ pathHorizon h := by
    exact_mod_cast hle
  have hh := activation_add_horizon h
  dsimp only [nominalBirth]
  omega

lemma nominalBirth_not_activation_succ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    nominalBirth M hE κ D C h e ≠ activation h + 1 := by
  intro heq
  have hm := nominalBirth_mem M hE κ D C h e
  rw [heq, nominalPath_baseline_gap] at hm
  have hm0 : e ∈ nominalPath M hE κ D C h (activation h + (0 : ℕ)) := by simpa using hm
  have hj := Nat.find_min' (exists_nominal_member M hE κ D C h e) hm0
  have hj0 : Nat.find (exists_nominal_member M hE κ D C h e) = 0 := Nat.eq_zero_of_le_zero hj
  dsimp only [nominalBirth] at heq
  rw [hj0] at heq
  omega

lemma nominalBirth_range (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    nominalBirth M hE κ D C h e = activation h ∨
      (activation h + 2 ≤ nominalBirth M hE κ D C h e ∧ nominalBirth M hE κ D C h e ≤ 0) := by
  have hb := nominalBirth_bounds M hE κ D C h e
  have hg := nominalBirth_not_activation_succ M hE κ D C h e
  omega

lemma not_mem_nominal_before_birth (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) (he : e ∉ M.closure ∅)
    {k : ℤ} (hk : k < nominalBirth M hE κ D C h e) :
    e ∉ nominalPath M hE κ D C h k := by
  by_cases hka : k < activation h
  · rwa [nominalPath_early M hE κ D C h hka]
  · intro hm
    have heq : activation h + ((k - activation h).toNat : ℤ) = k := by
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hm' : e ∈ nominalPath M hE κ D C h
        (activation h + ((k - activation h).toNat : ℤ)) := by rwa [heq]
    have hf := Nat.find_min' (exists_nominal_member M hE κ D C h e) hm'
    have hfi : (Nat.find (exists_nominal_member M hE κ D C h e) : ℤ) ≤
        ((k - activation h).toNat : ℤ) := by exact_mod_cast hf
    dsimp only [nominalBirth] at hk
    omega

lemma mem_nominal_iff_birth_le (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) (he : e ∉ M.closure ∅) (k : ℤ) :
    e ∈ nominalPath M hE κ D C h k ↔ nominalBirth M hE κ D C h e ≤ k := by
  constructor
  · intro hm
    by_contra hn
    exact not_mem_nominal_before_birth M hE κ D C h e he (by omega) hm
  · intro hk
    exact nominalPath_mono M hE κ D C h hk (nominalBirth_mem M hE κ D C h e)

lemma nominalPath_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ) :
    ∃ Jtotal : Set α, Jtotal ⊆ D h ∧ κ * Jtotal.ncard ≤ (D h).ncard ∧
      ∃ J : ℕ → Set α, Monotone J ∧ (∀ j ≤ pathHorizon h, J j ⊆ Jtotal) ∧
        (∀ j ≤ pathHorizon h,
          M.closure (guardedPath M hE κ D C h (activation h + j) ∪ J j) =
            nominalPath M hE κ D C h (activation h + j)) := by
  have hmono : Monotone (fun j : ℕ => guardedPath M hE κ D C h (activation h + j)) := by
    intro i j hij
    apply guardedPath_mono M hE κ D C h
    have hi : (i : ℤ) ≤ j := by exact_mod_cast hij
    omega
  obtain ⟨Jtotal, hJD, hcard, J, hJmono, hJJ, hgen⟩ :=
    densityPath_generators M hE κ hκ (D h)
      (fun j : ℕ => guardedPath M hE κ D C h (activation h + j)) hmono (pathHorizon h)
  refine ⟨Jtotal, hJD, hcard, J, hJmono, hJJ, ?_⟩
  intro j hj
  rw [nominalPath, densityEnabled, ite_eq_left (by omega)]
  exact hgen j hj

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset

structure MainMasks (n : ℕ) where
  H : Finset (Fin n)
  D : Finset (Fin n)
  C : Finset (Fin n)
  T : Finset (Fin n)
  odd : Bool

def mainSeedBits (n : ℕ) : ℕ := 4*n+2

def seedMask {n : ℕ} (r : Seed (mainSeedBits n)) (j : Fin 4) : Finset (Fin n) :=
  univ.filter fun e => r ⟨4*e.val+j.val, by dsimp [mainSeedBits]; omega⟩ = true

def mainMasks {n : ℕ} (r : Seed (mainSeedBits n)) : MainMasks n where
  H := seedMask r 0
  D := seedMask r 1
  C := seedMask r 2
  T := seedMask r 3
  odd := r ⟨4*n+1, by dsimp [mainSeedBits]; omega⟩

def mainBranch {n : ℕ} (r : Seed (mainSeedBits n)) : Bool :=
  r ⟨4*n, by dsimp [mainSeedBits]; omega⟩

namespace MainAlgorithm
variable {n : ℕ}

def higher (f : Fin n) (a : Option ℤ) (e : Fin n) (b : Option ℤ) : Prop :=
  match a, b with
  | some i, some j => j < i ∨ j = i ∧ f < e
  | some _, none => True
  | _, _ => False

def candidate (M : Matroid (Fin n)) (d : MainMasks n) (seen : Fin n → Option ℤ)
    (e : Fin n) (w : Option ℤ) : Prop :=
  w ≠ none ∧ e ∉ d.H ∧ e ∉ M.closure {f | f ∈ d.H ∧ higher f (seen f) e w}

noncomputable def listed (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : Finset ℤ := by
  classical
  exact d.D.biUnion fun e => if candidate M d seen e (seen e) then (seen e).toFinset else ∅

noncomputable def groups (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : List ℤ := (listed M d seen).sort (· ≤ ·)

def groupMask (M : Matroid (Fin n)) (d : MainMasks n) (seen : Fin n → Option ℤ)
    (mask : Finset (Fin n)) (h : ℕ) : Set (Fin n) :=
  {e | e ∈ mask ∧ candidate M d seen e (seen e) ∧ seen e = (groups M d seen)[h]?}

noncomputable def finalPath (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) : ℤ → Set (Fin n) :=
  guardedPath M hE (2^100) (groupMask M d seen d.D) (groupMask M d seen d.C)
    (groups M d seen).length

noncomputable def birth (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (i : ℤ) : ℤ :=
  nominalBirth M hE (2^100) (groupMask M d seen d.D) (groupMask M d seen d.C)
    ((groups M d seen).idxOf i) e

def eligible (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (i : ℤ) : Prop :=
  e ∉ d.H ∪ d.D ∪ d.C ∧ candidate M d seen e (some i) ∧ i ∈ groups M d seen ∧
  e ∈ d.T ∧ activation ((groups M d seen).idxOf i) + 2 ≤ birth M hE d seen e i ∧
  (birth M hE d seen e i) % 2 = (if d.odd then 1 else 0) ∧
  e ∉ finalPath M hE d seen (birth M hE d seen e i - 2)

noncomputable def assign (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) : Option ℤ → Option ℤ := by
  classical
  exact fun w => match w with
    | none => none
    | some i => if eligible M hE d seen e i then some (birth M hE d seen e i) else none

noncomputable def core (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    OnlineRule n (mainSeedBits n) :=
  layerOnlineRule M (roundedLevel weightBase) (measurable_roundedLevel weightBase)
    (fun r seen b => finalPath M hE (mainMasks r) seen (b-2))
    (fun r seen => assign M hE (mainMasks r) seen)

noncomputable def hidden (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    HiddenRule n (mainSeedBits n) where
  mask r := (mainMasks r).H ∪ (mainMasks r).D ∪ (mainMasks r).C
  core := core M hE

end MainAlgorithm
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset

lemma guardedPath_group_mono {α : Type*} [Fintype α]
    (M : Matroid α) (hE : M.E = Set.univ) (κ : ℕ) (D C : ℕ → Set α) (k : ℤ) :
    Monotone (fun h => guardedPath M hE κ D C h k) := by
  apply monotone_nat_of_le_succ
  intro h
  exact (guarded_subset_nominal M hE κ D C h k).trans
    (nominal_subset_guarded M hE κ D C h k)

lemma assigned_some_of_eligible {n : ℕ} {K : Type*}
    (assign : Fin n → K → Option ℤ) (v : Fin n → K) (e : Fin n)
    (he : e ∈ assignedEligible assign v) :
    assign e (v e) = some (assignedLayer assign v e) := by
  classical
  cases h : assign e (v e) <;> simp_all [assignedEligible, assignedLayer]

namespace MainAlgorithm
variable {n : ℕ}

lemma assign_spec (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (w : Option ℤ) (b : ℤ) :
    assign M hE d seen e w = some b ↔
      ∃ i, w = some i ∧ eligible M hE d seen e i ∧ birth M hE d seen e i = b := by
  classical
  cases w with
  | none => simp [assign]
  | some i =>
    by_cases h : eligible M hE d seen e i <;> simp [assign, h]

lemma eligible_mem_final (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (i : ℤ)
    (he : eligible M hE d seen e i) :
    e ∈ finalPath M hE d seen (birth M hE d seen e i) := by
  have hi : i ∈ groups M d seen := he.2.2.1
  have hidx : (groups M d seen).idxOf i < (groups M d seen).length :=
    List.idxOf_lt_length_of_mem hi
  have hm := nominalBirth_mem M hE (2^100) (groupMask M d seen d.D)
    (groupMask M d seen d.C) ((groups M d seen).idxOf i) e
  have hs := nominal_subset_guarded M hE (2^100) (groupMask M d seen d.D)
    (groupMask M d seen d.C) ((groups M d seen).idxOf i) (birth M hE d seen e i) hm
  exact guardedPath_group_mono M hE (2^100) (groupMask M d seen d.D)
    (groupMask M d seen d.C) _ (Nat.succ_le_of_lt hidx) hs

lemma assigned_lower_in_base (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen v : Fin n → Option ℤ)
    (e : Fin n) (he : e ∈ assignedEligible (assign M hE d seen) v)
    (f : Fin n) (hf : f ∈ assignedEligible (assign M hE d seen) v)
    (hlt : assignedLayer (assign M hE d seen) v e < assignedLayer (assign M hE d seen) v f) :
    e ∈ finalPath M hE d seen (assignedLayer (assign M hE d seen) v f - 2) := by
  obtain ⟨i, _, hei, hbi⟩ := (assign_spec M hE d seen e _ _).mp
    (assigned_some_of_eligible (assign M hE d seen) v e he)
  obtain ⟨j, _, hfj, hbj⟩ := (assign_spec M hE d seen f _ _).mp
    (assigned_some_of_eligible (assign M hE d seen) v f hf)
  have heiParity := hei.2.2.2.2.2.1
  have hfjParity := hfj.2.2.2.2.2.1
  rw [hbi] at heiParity
  rw [hbj] at hfjParity
  have hgap : assignedLayer (assign M hE d seen) v e ≤
      assignedLayer (assign M hE d seen) v f - 2 := by omega
  have hm := eligible_mem_final M hE d seen e i hei
  rw [hbi] at hm
  exact guardedPath_mono M hE (2^100) (groupMask M d seen d.D)
    (groupMask M d seen d.C) (groups M d seen).length hgap hm

theorem core_feasible (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    Feasible M (core M hE) := by
  apply layerOnlineRule_feasible M hE (roundedLevel weightBase) (measurable_roundedLevel weightBase)
  intro r seen v e he f hf hlt
  exact assigned_lower_in_base M hE (mainMasks r) seen v e he f hf hlt

theorem hidden_feasible (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (r : Seed (mainSeedBits n))
    (π : ArrivalOrder n) (t : ℕ) :
    M.Indep (hiddenAcceptedThrough (hidden M hE) r w π t : Set (Fin n)) := by
  have hobs : ∀ e, 0 ≤ observed (hidden M hE) r w e := by
    intro e
    unfold observed
    split_ifs
    · exact hw e
    · exact le_rfl
  exact (core_feasible M hE r (observed (hidden M hE) r w) w π t hobs hw).subset
    (by intro e he; exact (Finset.mem_sdiff.mp he).1)

end MainAlgorithm
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset
variable {n : ℕ}

lemma candidate_congr (M : Matroid (Fin n)) (d : MainMasks n)
    (s s' : Fin n → Option ℤ) (h : ∀ e ∈ d.H, s e = s' e) (e : Fin n) (w : Option ℤ) :
    candidate M d s e w ↔ candidate M d s' e w := by
  have heq : {f | f ∈ d.H ∧ higher f (s f) e w} = {f | f ∈ d.H ∧ higher f (s' f) e w} := by
    ext f
    by_cases hf : f ∈ d.H
    · simp only [Set.mem_ofPred_eq, hf, true_and, h f hf]
    · simp [hf]
  simp only [candidate, heq]

lemma listed_congr (M : Matroid (Fin n)) (d : MainMasks n)
    (s s' : Fin n → Option ℤ)
    (hH : ∀ e ∈ d.H, s e = s' e) (hD : ∀ e ∈ d.D, s e = s' e) :
    listed M d s = listed M d s' := by
  classical
  unfold listed
  apply Finset.biUnion_congr rfl
  intro e he
  have hc := candidate_congr M d s s' hH e (s e)
  rw [hD e he] at hc
  simp only [hD e he, hc]

lemma groups_congr (M : Matroid (Fin n)) (d : MainMasks n)
    (s s' : Fin n → Option ℤ)
    (hH : ∀ e ∈ d.H, s e = s' e) (hD : ∀ e ∈ d.D, s e = s' e) :
    groups M d s = groups M d s' := by
  rw [groups, groups, listed_congr M d s s' hH hD]

lemma groupMask_congr (M : Matroid (Fin n)) (d : MainMasks n)
    (s s' : Fin n → Option ℤ) (mask : Finset (Fin n))
    (hH : ∀ e ∈ d.H, s e = s' e) (hD : ∀ e ∈ d.D, s e = s' e)
    (hmask : ∀ e ∈ mask, s e = s' e) :
    groupMask M d s mask = groupMask M d s' mask := by
  funext j
  ext e
  by_cases he : e ∈ mask
  · have hc := candidate_congr M d s s' hH e (s e)
    rw [hmask e he] at hc
    simp only [groupMask, Set.mem_ofPred_eq, he, true_and,
      hmask e he, hc, groups_congr M d s s' hH hD]
  · simp [groupMask, he]

lemma preprocessing_congr (M : Matroid (Fin n)) (hE : M.E = Set.univ) (d : MainMasks n)
    (s s' : Fin n → Option ℤ) (h : ∀ e ∈ d.H ∪ d.D ∪ d.C, s e = s' e) :
    finalPath M hE d s = finalPath M hE d s' ∧
      birth M hE d s = birth M hE d s' ∧ assign M hE d s = assign M hE d s' := by
  classical
  have hH : ∀ e ∈ d.H, s e = s' e := fun e he => h e (mem_union_left _ (mem_union_left _ he))
  have hD : ∀ e ∈ d.D, s e = s' e := fun e he => h e (mem_union_left _ (mem_union_right _ he))
  have hC : ∀ e ∈ d.C, s e = s' e := fun e he => h e (mem_union_right _ he)
  have hgd := groupMask_congr M d s s' d.D hH hD hD
  have hgc := groupMask_congr M d s s' d.C hH hD hC
  have hgs := groups_congr M d s s' hH hD
  have hf : finalPath M hE d s = finalPath M hE d s' := by
    simp only [finalPath, hgd, hgc, hgs]
  have hb : birth M hE d s = birth M hE d s' := by
    funext e i
    simp only [birth, hgd, hgc, hgs]
  refine ⟨hf, hb, ?_⟩
  funext e w
  have hel (i : ℤ) : eligible M hE d s e i ↔ eligible M hE d s' e i := by
    simp only [eligible, hf, hb, hgs, candidate_congr M d s s' hH]
  cases w <;> simp only [assign, hel, hb]

lemma observed_preprocessing (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (r : Seed (mainSeedBits n)) (w : Weights n) :
    let s := fun e => roundedLevel weightBase (observed (hidden M hE) r w e)
    let s' := fun e => roundedLevel weightBase (w e)
    finalPath M hE (mainMasks r) s = finalPath M hE (mainMasks r) s' ∧
      birth M hE (mainMasks r) s = birth M hE (mainMasks r) s' ∧
      assign M hE (mainMasks r) s = assign M hE (mainMasks r) s' := by
  apply preprocessing_congr
  intro e he
  unfold observed
  have hm : e ∈ (hidden M hE).mask r := he
  rw [ite_eq_left hm]

end MatroidProphet.MainAlgorithm

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset
variable {n : ℕ}

noncomputable def selection (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n) : Finset (Fin n) :=
  layerGreedy M (assignedEligible (assign M hE d w) w)
    (fun b => finalPath M hE d w (b-2)) (assignedLayer (assign M hE d w) w)
    (fun e => (π.symm e).val)

lemma selection_not_observed (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n)
    (e : Fin n) (he : e ∈ selection M hE d w π) : e ∉ d.H ∪ d.D ∪ d.C := by
  have hel := layerGreedy_subset M _ _ _ _ he
  have ha := assigned_some_of_eligible (assign M hE d w) w e hel
  obtain ⟨i, _, hei, _⟩ := (assign_spec M hE d w e _ _).mp ha
  exact hei.1

theorem hiddenAccepted_eq_selection (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (r : Seed (mainSeedBits n)) (w : Weights n) (π : ArrivalOrder n) :
    hiddenAcceptedThrough (hidden M hE) r w π n =
      selection M hE (mainMasks r) (fun e => roundedLevel weightBase (w e)) π := by
  classical
  have hA : accepted (core M hE) r (observed (hidden M hE) r w) w π =
      selection M hE (mainMasks r) (fun e => roundedLevel weightBase (w e)) π := by
    unfold core
    rw [layerOnlineRule_accepted]
    obtain ⟨hf, _, ha⟩ := observed_preprocessing M hE r w
    rw [hf, ha]
    rfl
  change accepted (core M hE) r (observed (hidden M hE) r w) w π \ (hidden M hE).mask r = _
  rw [hA]
  ext e
  simp only [Finset.mem_sdiff]
  constructor
  · exact fun he => he.1
  · intro he
    exact ⟨he, selection_not_observed M hE (mainMasks r) _ π e he⟩

theorem hiddenReward_eq_selection (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (r : Seed (mainSeedBits n)) (w : Weights n) (π : ArrivalOrder n) :
    hiddenReward (hidden M hE) r w π =
      ∑ e ∈ selection M hE (mainMasks r) (fun e => roundedLevel weightBase (w e)) π, w e := by
  unfold hiddenReward
  rw [hiddenAccepted_eq_selection]

theorem rounded_selection_le_hiddenReward (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (r : Seed (mainSeedBits n)) (w : Weights n) (hw : ∀ e, 0 ≤ w e) (π : ArrivalOrder n) :
    (∑ e ∈ selection M hE (mainMasks r) (fun e => roundedLevel weightBase (w e)) π,
      roundedWeight weightBase (w e)) ≤ hiddenReward (hidden M hE) r w π := by
  rw [hiddenReward_eq_selection]
  apply Finset.sum_le_sum
  intro e he
  exact roundedWeight_le (by norm_num [weightBase]) (hw e)

end MatroidProphet.MainAlgorithm

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset

variable {n : ℕ}

@[simp] lemma mem_groups (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (i : ℤ) :
    i ∈ groups M d seen ↔ i ∈ listed M d seen := by
  simp [groups]

lemma groups_nodup (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : (groups M d seen).Nodup :=
  Finset.sort_nodup _ _

lemma groups_sorted (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : (groups M d seen).SortedLT :=
  Finset.sortedLT_sort _

@[simp] lemma groups_length (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : (groups M d seen).length = (listed M d seen).card := by
  simp [groups]

lemma groups_get_lt (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (i j : Fin (groups M d seen).length) (h : i < j) :
    (groups M d seen).get i < (groups M d seen).get j :=
  groups_sorted M d seen h

lemma groups_get?_idxOf (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (i : ℤ) (hi : i ∈ groups M d seen) :
    (groups M d seen)[(groups M d seen).idxOf i]? = some i :=
  List.getElem?_idxOf hi

lemma groups_idxOf_lt_iff (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (i j : ℤ)
    (hi : i ∈ groups M d seen) (hj : j ∈ groups M d seen) :
    (groups M d seen).idxOf i < (groups M d seen).idxOf j ↔ i < j := by
  have hii := List.idxOf_lt_length_of_mem hi
  have hjj := List.idxOf_lt_length_of_mem hj
  have h := (groups_sorted M d seen).getElem_lt_getElem_iff (hi := hii) (hj := hjj)
  simpa using h.symm

lemma groups_earlier_key (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) {j h : ℕ} {i : ℤ}
    (hh : (groups M d seen)[h]? = some i) (hjh : j < h) :
    ∃ k, (groups M d seen)[j]? = some k ∧ k < i := by
  obtain ⟨hh', hi⟩ := List.getElem?_eq_some_iff.mp hh
  have hj : j < (groups M d seen).length := hjh.trans hh'
  refine ⟨(groups M d seen)[j], List.getElem?_eq_getElem hj, ?_⟩
  rw [← hi]
  exact (groups_sorted M d seen).getElem_lt_getElem_of_lt hjh

end MatroidProphet.MainAlgorithm

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open Set

variable {α : Type*} [Fintype α]

lemma monotone_set_timing
    {α : Type u_1} [Fintype α] (J : ℕ → Set α) (hJ : Monotone J) (N : ℕ) :
    ∃ τ : α → ℕ, ∀ j ≤ N, J j = {g | g ∈ J N ∧ τ g ≤ j} := by
  classical
  let hex := fun g (hg : g ∈ J N) => show ∃ j, g ∈ J j from ⟨N, hg⟩
  let τ := fun g => if hg : g ∈ J N then Nat.find (hex g hg) else 0
  refine ⟨τ, ?_⟩
  intro j hj
  ext g
  constructor
  · intro hg
    have hgN := hJ hj hg
    refine ⟨hgN, ?_⟩
    simpa [τ, hgN] using Nat.find_min' (hex g hgN) hg
  · rintro ⟨hgN, hτ⟩
    have hfind : Nat.find (hex g hgN) ≤ j := by simpa [τ, hgN] using hτ
    exact hJ hfind (Nat.find_spec (hex g hgN))

lemma nominalPath_timed_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ) :
    ∃ G : Set α, G ⊆ D h ∧ κ * G.ncard ≤ (D h).ncard ∧ ∃ τ : α → ℕ,
      (∀ g ∈ G, τ g ≤ pathHorizon h) ∧
      (∀ j ≤ pathHorizon h,
        M.closure (guardedPath M hE κ D C h (activation h + j) ∪
          {g | g ∈ G ∧ τ g ≤ j}) = nominalPath M hE κ D C h (activation h + j)) := by
  obtain ⟨G, hGD, hGcard, J, hJmono, hJG, hgen⟩ := nominalPath_generators M hE κ hκ D C h
  obtain ⟨τ, hτ⟩ := monotone_set_timing J hJmono (pathHorizon h)
  refine ⟨J (pathHorizon h), (hJG _ le_rfl).trans hGD, ?_, τ, ?_, ?_⟩
  · exact (Nat.mul_le_mul_left κ (Set.ncard_mono (hJG _ le_rfl))).trans hGcard
  · intro g hg
    exact ((Set.ext_iff.mp (hτ _ le_rfl) g).mp hg).2
  · intro j hj
    rw [← hτ j hj]
    exact hgen j hj

noncomputable def timedGeneratorSet (G : Set α) (τ : α → ℕ) (a k : ℤ) : Set α :=
  {g | g ∈ G ∧ a + (τ g : ℤ) ≤ k}

lemma nominalPath_all_time_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ) :
    ∃ G : Set α, G ⊆ D h ∧ κ * G.ncard ≤ (D h).ncard ∧ ∃ τ : α → ℕ,
      (∀ g ∈ G, τ g ≤ pathHorizon h) ∧ ∀ k : ℤ,
        nominalPath M hE κ D C h k =
          M.closure (guardedPath M hE κ D C h k ∪ timedGeneratorSet G τ (activation h) k) := by
  obtain ⟨G, hGD, hGcard, τ, hbound, hgen⟩ := nominalPath_timed_generators M hE κ hκ D C h
  refine ⟨G, hGD, hGcard, τ, hbound, ?_⟩
  intro k
  by_cases hka : k < activation h
  · have hearly : k < -3 * (h : ℤ) - 1 := by
      dsimp [activation] at hka
      omega
    have hempty : timedGeneratorSet G τ (activation h) k = ∅ := by
      ext g
      simp only [timedGeneratorSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ htime
      omega
    rw [nominalPath_early M hE κ D C h hka, guardedPath_early M hE κ D C h hearly,
      hempty, union_empty, M.closure_closure]
  · by_cases hk0 : 0 ≤ k
    · rw [nominalPath_nonnegative M hE κ D C h hk0, guardedPath_nonnegative M hE κ D C h hk0]
      simp [M.closure_univ, hE]
    · let j := (k - activation h).toNat
      have hjcast : (j : ℤ) = k - activation h := Int.toNat_of_nonneg (by omega)
      have hj : j ≤ pathHorizon h := by
        have hhor := activation_add_horizon h
        omega
      have hkj : activation h + (j : ℤ) = k := by omega
      have hsets : {g | g ∈ G ∧ τ g ≤ j} = timedGeneratorSet G τ (activation h) k := by
        ext g
        simp only [timedGeneratorSet, Set.mem_ofPred_eq]
        constructor <;> rintro ⟨hg, ht⟩ <;> exact ⟨hg, by omega⟩
      have h := hgen j hj
      rw [hkj, hsets] at h
      exact h.symm

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

def commonPathGenerators (C J : ℕ → Set α) (h : ℕ) : ℕ → Set α
  | 0 => C h
  | t+1 => commonPathGenerators C J h t ∪ C (h+1+t) ∪ J (h+1+t)

omit [Fintype α] in
lemma commonPathGenerators_cost (κ : ℕ) (C D J : ℕ → Set α) (h t : ℕ)
    (hJ : ∀ j, κ * (J j).ncard ≤ (D j).ncard) :
    κ * (commonPathGenerators C J h t).ncard ≤ κ * (C h).ncard +
      ∑ j ∈ range t, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
  induction t with
  | zero => simp [commonPathGenerators]
  | succ t ih =>
    have hcard := ncard_union_le (commonPathGenerators C J h t ∪ C (h+1+t)) (J (h+1+t))
    have hcard' := ncard_union_le (commonPathGenerators C J h t) (C (h+1+t))
    have hc : (commonPathGenerators C J h (t+1)).ncard ≤
        (commonPathGenerators C J h t).ncard + (C (h+1+t)).ncard + (J (h+1+t)).ncard := by
      exact hcard.trans (Nat.add_le_add_right hcard' _)
    have hm := Nat.mul_le_mul_left κ hc
    simp only [Nat.mul_add] at hm
    rw [sum_range_succ]
    have hj := hJ (h+1+t)
    omega

lemma commonPathGenerators_spans (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C J : ℕ → Set α) (h t : ℕ)
    (hJ : ∀ j k, nominalPath M hE κ D C j k ⊆
      M.closure (guardedPath M hE κ D C j k ∪ J j)) (k : ℤ) :
    guardedPath M hE κ D C (h+1+t) k ⊆
      M.closure (nominalPath M hE κ D C h k ∪ commonPathGenerators C J h t) := by
  induction t with
  | zero =>
    simp only [Nat.add_zero, commonPathGenerators, guardedPath_succ]
    exact M.closure_subset_closure (union_subset_union_right _ inter_subset_left)
  | succ t ih =>
    have hidx : h+1+(t+1) = (h+1+t)+1 := by omega
    rw [hidx, guardedPath_succ]
    apply M.closure_subset_closure_of_subset_closure
    apply Set.union_subset
    · apply (hJ (h+1+t) k).trans
      apply M.closure_subset_closure_of_subset_closure
      apply Set.union_subset
      · exact ih.trans (M.closure_subset_closure (by
          intro e he
          rcases he with he | he
          · exact Or.inl he
          · exact Or.inr (Or.inl (Or.inl he))))
      · intro e he
        exact M.mem_closure_of_mem (Or.inr (Or.inr he)) (by simp [hE])
    · intro e he
      exact M.mem_closure_of_mem (Or.inr (Or.inl (Or.inr he.1))) (by simp [hE])

theorem exists_commonPathBudget (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h t : ℕ) :
    ∃ Jtotal : Set α,
      κ * Jtotal.ncard ≤ κ * (C h).ncard +
        ∑ j ∈ range t, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) ∧
      ∀ k, guardedPath M hE κ D C (h+1+t) k ⊆
        M.closure (nominalPath M hE κ D C h k ∪ Jtotal) := by
  choose J hJD hcard τ htime hgen using
    (fun j => nominalPath_all_time_generators M hE κ hκ D C j)
  refine ⟨commonPathGenerators C J h t, commonPathGenerators_cost κ C D J h t hcard, ?_⟩
  intro k
  apply commonPathGenerators_spans M hE κ D C J h t _ k
  intro j l
  rw [hgen j l]
  apply M.closure_subset_closure
  exact union_subset_union_right _ (fun _ he => he.1)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

noncomputable def reversePrefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) : ℕ → Set α
  | 0 => if k < 0 then M.closure ∅ else univ
  | h+1 => M.closure (densityEnabled M hE κ (D h) (activation h) k
      (reversePrefix M hE κ D C S k h) ∪ (C h ∩ S h))

noncomputable def reverseNominal (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) : Set α :=
  densityEnabled M hE κ (D h) (activation h) k (reversePrefix M hE κ D C S k h)

lemma reversePrefix_succ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D C S k (h+1) =
      M.closure (reverseNominal M hE κ D C S k h ∪ (C h ∩ S h)) := rfl

lemma reversePrefix_agrees (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D C (fun j => nominalPath M hE κ D C j (k+1)) k h =
      guardedPath M hE κ D C h k := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [reversePrefix, ih]
    rfl

lemma reverseNominal_agrees (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reverseNominal M hE κ D C (fun j => nominalPath M hE κ D C j (k+1)) k h =
      nominalPath M hE κ D C h k := by
  rw [reverseNominal, reversePrefix_agrees]
  rfl

lemma reversePrefix_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' S S' : ℕ → Set α) {k k' : ℤ} (hkk' : k ≤ k')
    (hC : ∀ j, C j ⊆ C' j) (hS : ∀ j, S j ⊆ S' j) (h : ℕ) :
    reversePrefix M hE κ D C S k h ⊆ reversePrefix M hE κ D C' S' k' h := by
  induction h with
  | zero => exact guardedPath_mono M hE κ D C 0 hkk'
  | succ h ih =>
    exact M.closure_subset_closure
      (union_subset_union (densityEnabled_mono M hE κ (D h) (activation h) hkk' ih)
        (inter_subset_inter (hC h) (hS h)))

lemma reverseNominal_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' S S' : ℕ → Set α) {k k' : ℤ} (hkk' : k ≤ k')
    (hC : ∀ j, C j ⊆ C' j) (hS : ∀ j, S j ⊆ S' j) (h : ℕ) :
    reverseNominal M hE κ D C S k h ⊆ reverseNominal M hE κ D C' S' k' h :=
  densityEnabled_mono M hE κ (D h) (activation h) hkk'
    (reversePrefix_mono M hE κ D C C' S S' hkk' hC hS h)

lemma reversePrefix_congr_before (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' S S' : ℕ → Set α) (k : ℤ) (h : ℕ)
    (hC : ∀ j < h, C j = C' j) (hS : ∀ j < h, S j = S' j) :
    reversePrefix M hE κ D C S k h = reversePrefix M hE κ D C' S' k h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [reversePrefix, reversePrefix, ih (fun j hj => hC j (by omega))
      (fun j hj => hS j (by omega)), hC h (by omega), hS h (by omega)]

lemma reverseNominal_congr_before (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' S S' : ℕ → Set α) (k : ℤ) (h : ℕ)
    (hC : ∀ j < h, C j = C' j) (hS : ∀ j < h, S j = S' j) :
    reverseNominal M hE κ D C S k h = reverseNominal M hE κ D C' S' k h := by
  rw [reverseNominal, reverseNominal, reversePrefix_congr_before M hE κ D C C' S S' k h hC hS]

lemma reversePrefix_subset_later (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D C' (fun j => nominalPath M hE κ D C j (k+1)) k h ⊆
      guardedPath M hE κ D C h (k+1) := by
  induction h with
  | zero => exact guardedPath_mono M hE κ D C 0 (by omega)
  | succ h ih =>
    have hn := densityEnabled_mono M hE κ (D h) (activation h) (by omega : k ≤ k+1) ih
    have hs : reversePrefix M hE κ D C' (fun j => nominalPath M hE κ D C j (k+1)) k (h+1) ⊆
        nominalPath M hE κ D C h (k+1) := by
      exact (M.closure_subset_closure (union_subset hn inter_subset_right)).trans_eq
        (nominalPath_flat M hE κ D C h (k+1)).closure
    exact hs.trans (nominal_subset_guarded M hE κ D C h (k+1))

lemma reverseNominal_subset_later (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reverseNominal M hE κ D C' (fun j => nominalPath M hE κ D C j (k+1)) k h ⊆
      nominalPath M hE κ D C h (k+1) :=
  densityEnabled_mono M hE κ (D h) (activation h) (by omega)
    (reversePrefix_subset_later M hE κ D C C' k h)

lemma reversePrefix_subset_succ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D C S k h ⊆ reversePrefix M hE κ D C S k (h+1) :=
  (densityEnabled_extensive M hE κ (D h) (activation h) k _).trans
    (subset_union_left.trans (M.subset_closure _ (by simp [hE])))

omit [Fintype α] in
lemma union_inter_sdiff (N C S : Set α) : N ∪ (C ∩ (S \ N)) = N ∪ (C ∩ S) := by
  ext e
  change (e ∈ N ∨ (e ∈ C ∧ e ∈ S ∧ e ∉ N)) ↔ (e ∈ N ∨ (e ∈ C ∧ e ∈ S))
  tauto

noncomputable def departingGuards (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) : Set α :=
  C h ∩ (S h \ reverseNominal M hE κ D C S k h)

lemma reversePrefix_departing_only (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D (departingGuards M hE κ D C S k) S k h =
      reversePrefix M hE κ D C S k h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [reversePrefix, reversePrefix, ih]
    change M.closure (reverseNominal M hE κ D C S k h ∪
        ((C h ∩ (S h \ reverseNominal M hE κ D C S k h)) ∩ S h)) = _
    have hi : (C h ∩ (S h \ reverseNominal M hE κ D C S k h)) ∩ S h =
        C h ∩ (S h \ reverseNominal M hE κ D C S k h) := inter_eq_self_of_subset_left (fun _ he => he.2.1)
    rw [hi, union_inter_sdiff]
    rfl

lemma reverseNominal_departing_only (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reverseNominal M hE κ D (departingGuards M hE κ D C S k) S k h =
      reverseNominal M hE κ D C S k h := by
  rw [reverseNominal, reverseNominal, reversePrefix_departing_only]

noncomputable def departureBatch (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C G : ℕ → Set α) (h : ℕ) (k : ℤ) : Set α :=
  G h ∩ (nominalPath M hE κ D C h (k+1) \ nominalPath M hE κ D C h k)

lemma departureBatch_disjoint_time (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C G : ℕ → Set α) (h : ℕ) {k l : ℤ} (hkl : k ≠ l) :
    Disjoint (departureBatch M hE κ D C G h k) (departureBatch M hE κ D C G h l) := by
  apply Set.disjoint_left.mpr
  intro e he hf
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · exact hf.2.2 (nominalPath_mono M hE κ D C h (by omega : k+1 ≤ l) he.2.1)
  · exact he.2.2 (nominalPath_mono M hE κ D C h (by omega : l+1 ≤ k) hf.2.1)

lemma departureBatch_disjoint_group (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C G : ℕ → Set α) {h j : ℕ} (hG : Disjoint (G h) (G j)) (k l : ℤ) :
    Disjoint (departureBatch M hE κ D C G h k) (departureBatch M hE κ D C G j l) :=
  hG.mono inter_subset_left inter_subset_left

noncomputable def hybridGuards (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) (h : ℕ) : Set α :=
  (C h ∩ nominalPath M hE κ D C h (b-1)) ∪
    (T h ∩ (nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1)))

noncomputable def lowerCompetition (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) : ℕ → Set α
  | 0 => ∅
  | h+1 => lowerCompetition M hE κ D C T b h ∪
      (T h ∩ (nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1)))

lemma hybridPrefix_contains (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) (h : ℕ) :
    guardedPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h ⊆
      reversePrefix M hE κ D (hybridGuards M hE κ D C T b)
        (fun j => nominalPath M hE κ D C j b) (b-1) h := by
  induction h with
  | zero =>
    exact union_subset (guardedPath_mono M hE κ D C 0 (by omega)) (empty_subset _)
  | succ h ih =>
    let A := reversePrefix M hE κ D (hybridGuards M hE κ D C T b)
      (fun j => nominalPath M hE κ D C j b) (b-1) h
    let N := reverseNominal M hE κ D (hybridGuards M hE κ D C T b)
      (fun j => nominalPath M hE κ D C j b) (b-1) h
    have hFn : nominalPath M hE κ D C h (b-2) ⊆ N :=
      densityEnabled_mono M hE κ (D h) (activation h) (by omega)
        (subset_union_left.trans ih)
    have hguards : C h ∩ nominalPath M hE κ D C h (b-1) ⊆
        hybridGuards M hE κ D C T b h ∩ nominalPath M hE κ D C h b := by
      intro e he
      exact ⟨Or.inl he, nominalPath_mono M hE κ D C h (by omega) he.2⟩
    have hF : guardedPath M hE κ D C (h+1) (b-2) ⊆
        reversePrefix M hE κ D (hybridGuards M hE κ D C T b)
          (fun j => nominalPath M hE κ D C j b) (b-1) (h+1) := by
      rw [guardedPath_succ, reversePrefix_succ]
      have ht : b-2+1 = b-1 := by omega
      rw [ht]
      exact M.closure_subset_closure (union_subset_union hFn hguards)
    apply union_subset hF
    change lowerCompetition M hE κ D C T b h ∪ _ ⊆ _
    apply union_subset
    · exact (subset_union_right.trans ih).trans
        (reversePrefix_subset_succ M hE κ D (hybridGuards M hE κ D C T b)
          (fun j => nominalPath M hE κ D C j b) (b-1) h)
    · intro e he
      apply M.subset_closure _ (by simp [hE])
      exact Or.inr ⟨Or.inr he, he.2.1⟩

lemma hybrid_containment (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) (h : ℕ) (henabled : activation h ≤ b-1) :
    densityExpansion M hE κ (D h)
      (guardedPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h) ⊆
      reverseNominal M hE κ D (hybridGuards M hE κ D C T b)
        (fun j => nominalPath M hE κ D C j b) (b-1) h := by
  rw [reverseNominal, densityEnabled, ite_eq_left henabled]
  exact densityExpansion_mono M hE κ (D h) (hybridPrefix_contains M hE κ D C T b h)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

lemma natRank_le_ncard (M : Matroid α) (S : Set α) : natRank M S ≤ S.ncard := by
  have h := ENat.toNat_le_toNat (M.eRk_le_encard S) (Set.toFinite S).encard_lt_top.ne
  simpa only [natRank, Set.ncard_def] using h

lemma conditionalRank_mono_left (M : Matroid α) (P : Set α)
    {S T : Set α} (hST : S ⊆ T) : conditionalRank M S P ≤ conditionalRank M T P := by
  exact Nat.sub_le_sub_right (natRank_mono M (union_subset_union_left P hST)) _

lemma conditionalRank_spanned (M : Matroid α) (hE : M.E = Set.univ)
    (S P H : Set α) (hspan : S ⊆ M.closure (P ∪ H)) :
    conditionalRank M S P ≤ H.ncard := by
  have hP : P ⊆ M.closure (P ∪ H) :=
    subset_union_left.trans (M.subset_closure _ (by simp [hE]))
  have hr := natRank_mono M (union_subset hspan hP)
  rw [natRank_closure] at hr
  have ht : conditionalRank M S P ≤ conditionalRank M H P := by
    unfold conditionalRank
    rw [union_comm H P]
    exact Nat.sub_le_sub_right hr _
  exact ht.trans ((conditionalRank_le_rank M H P).trans (natRank_le_ncard M H))

theorem layerGreedy_rank_lower (M : Matroid α) (hE : M.E = Set.univ)
    (E : Finset α) (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (b : ℤ) (S K : Set α) (high : α → Prop) [DecidablePred high]
    (hS : S \ base b ⊆ {e | e ∈ E ∧ layer e = b})
    (hK : ∀ e ∈ layerGreedy M E base layer time, layer e = b → ¬ high e → e ∈ K) :
    conditionalRank M S (base b ∪ K) ≤
      ((layerGreedy M E base layer time).filter (fun e => layer e = b ∧ high e)).card := by
  classical
  let H := (layerGreedy M E base layer time).filter (fun e => layer e = b ∧ high e)
  have hspan : S ⊆ M.closure ((base b ∪ K) ∪ (H : Set α)) := by
    intro e he
    by_cases heF : e ∈ base b
    · exact M.mem_closure_of_mem (Or.inl (Or.inl heF)) (by simp [hE])
    have hel := hS ⟨he, heF⟩
    have hs := layerGreedy_spans M E base layer time hE b hel
    apply M.closure_subset_closure ?_ hs
    rintro f (hf | ⟨hf, hb⟩)
    · exact Or.inl (Or.inl hf)
    · by_cases hh : high f
      · exact Or.inr (mem_filter.mpr ⟨hf, hb, hh⟩)
      · exact Or.inl (Or.inr (hK f hf hb hh))
  have hc := conditionalRank_spanned M hE S (base b ∪ K) (H : Set α) hspan
  simpa only [Set.ncard_coe_finset, H] using hc

theorem layerGreedy_sum_rank_lower [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ)
    (E : Finset α) (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (points : Finset ℤ) (S K : ℤ → Set α) (high : α → Prop) [DecidablePred high]
    (hS : ∀ b ∈ points, S b \ base b ⊆ {e | e ∈ E ∧ layer e = b})
    (hK : ∀ b ∈ points, ∀ e ∈ layerGreedy M E base layer time,
      layer e = b → ¬ high e → e ∈ K b) :
    (∑ b ∈ points, conditionalRank M (S b) (base b ∪ K b)) ≤
      ((layerGreedy M E base layer time).filter high).card := by
  classical
  let A := layerGreedy M E base layer time
  calc
    _ ≤ ∑ b ∈ points, (A.filter (fun e => layer e = b ∧ high e)).card := by
      exact Finset.sum_le_sum fun b hb =>
        layerGreedy_rank_lower M hE E base layer time b (S b) (K b) high (hS b hb) (hK b hb)
    _ = ∑ b ∈ points, ((A.filter high).filter (fun e => layer e = b)).card := by
      apply Finset.sum_congr rfl
      intro b hb
      congr 1
      ext e
      simp only [Finset.mem_filter]
      tauto
    _ = ((A.filter high).filter (fun e => layer e ∈ points)).card :=
      Finset.sum_card_fiberwise_eq_card_filter (A.filter high) points layer
    _ ≤ (A.filter high).card := Finset.card_filter_le _ _

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

lemma lowerCompetition_subset_guarded (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) (h : ℕ) :
    lowerCompetition M hE κ D C T b h ⊆ guardedPath M hE κ D C h b := by
  induction h with
  | zero => exact Set.empty_subset _
  | succ h ih =>
    apply Set.union_subset
    · exact ih.trans ((guarded_subset_nominal M hE κ D C h b).trans
        (nominal_subset_guarded M hE κ D C h b))
    · exact fun _ he => nominal_subset_guarded M hE κ D C h b he.2.1

noncomputable def unobservedBirthRegion (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G O : Set α) (h : ℕ) (b : ℤ) : Set α :=
  if activation h + 2 ≤ b then
    (G ∩ (nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1))) \ O
  else ∅

lemma unobservedBirthRegion_subset (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G O : Set α) (h : ℕ) (b : ℤ) :
    unobservedBirthRegion M hE κ D C G O h b ⊆ nominalPath M hE κ D C h b := by
  unfold unobservedBirthRegion
  split_ifs
  · exact fun _ he => he.1.2.1
  · exact Set.empty_subset _

theorem actual_path_rank_cost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h later layers : ℕ)
    (start : ℤ) (S : ℤ → Set α)
    (hS : ∀ b, S b ⊆ nominalPath M hE κ D C h b) :
    κ * (∑ j ∈ range layers, conditionalRank M (S (start+2*j+2))
      (nominalPath M hE κ D C h (start+2*j) ∪
        lowerCompetition M hE κ D C T (start+2*j+2) h)) ≤
    κ * (∑ j ∈ range layers, conditionalRank M (S (start+2*j+2))
      (guardedPath M hE κ D C (h+1+later) (start+2*j) ∪
        lowerCompetition M hE κ D C T (start+2*j+2) h)) +
      κ * (C h).ncard +
        ∑ j ∈ range later, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
  obtain ⟨J, hJcost, hJ⟩ := exists_commonPathBudget M hE κ hκ D C h later
  have hXfinal (b : ℤ) : nominalPath M hE κ D C h b ⊆
      guardedPath M hE κ D C (h+1+later) b := by
    apply (nominal_subset_guarded M hE κ D C h b).trans
    have hm : Monotone (fun j => guardedPath M hE κ D C j b) :=
      monotone_nat_of_le_succ (fun j => (guarded_subset_nominal M hE κ D C j b).trans
        (nominal_subset_guarded M hE κ D C j b))
    exact hm (by omega)
  have hr := rankCost_chain M J layers
    (fun j => nominalPath M hE κ D C h (start+2*j))
    (fun j => nominalPath M hE κ D C h (start+2*j) ∪
      lowerCompetition M hE κ D C T (start+2*j+2) h)
    (fun j => guardedPath M hE κ D C (h+1+later) (start+2*j) ∪
      lowerCompetition M hE κ D C T (start+2*j+2) h)
    (fun j => S (start+2*j+2))
    (fun _ _ => Set.subset_union_left)
    (fun j _ => Set.union_subset_union_left _ (hXfinal _))
    (by
      intro j hj
      apply Set.union_subset
      · exact (hJ _).trans (M.closure_subset_closure (by
          intro e he
          rcases he with he | he
          · exact Or.inl (Or.inl he)
          · exact Or.inr he))
      · intro e he
        exact M.mem_closure_of_mem (Or.inl (Or.inr he)) (by simp [hE]))
    (by
      intro j hj
      have heq : start+2*(↑(j+1):ℤ) = start+2*j+2 := by push_cast; omega
      rw [heq]
      apply Set.union_subset
      · apply Set.union_subset
        · exact nominalPath_mono M hE κ D C h (by omega)
        · exact (lowerCompetition_subset_guarded M hE κ D C T _ h).trans
            (guarded_subset_nominal M hE κ D C h _)
      · exact hS _)
  have hmul := Nat.mul_le_mul_left κ hr
  rw [Nat.mul_add] at hmul
  have hcard := natRank_le_ncard M J
  have hbound := (Nat.mul_le_mul_left κ hcard).trans hJcost
  omega

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

lemma mem_nominal_difference_iff (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) (he : e ∉ M.closure ∅) (b : ℤ) :
    e ∈ nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1) ↔
      nominalBirth M hE κ D C h e = b := by
  simp only [Set.mem_sdiff, mem_nominal_iff_birth_le M hE κ D C h e he]
  omega

lemma lowerCompetition_member (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) {j h : ℕ} (hj : j < h)
    {e : α} (he : e ∈ T j ∩ (nominalPath M hE κ D C j b \
      nominalPath M hE κ D C j (b-1))) :
    e ∈ lowerCompetition M hE κ D C T b h := by
  induction h with
  | zero => omega
  | succ h ih =>
    change e ∈ lowerCompetition M hE κ D C T b h ∪
      (T h ∩ (nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1)))
    by_cases heq : j = h
    · exact Or.inr (heq ▸ he)
    · exact Or.inl (ih (by omega))

namespace MainAlgorithm
variable {n : ℕ}

lemma candidate_nonloop (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (e : Fin n) (v : Option ℤ)
    (he : candidate M d w e v) : e ∉ M.closure ∅ :=
  fun hx => he.2.2 (M.closure_subset_closure (Set.empty_subset _) hx)

lemma groups_index_of_get (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) {h : ℕ} {i : ℤ} (hi : (groups M d w)[h]? = some i) :
    i ∈ groups M d w ∧ (groups M d w).idxOf i = h := by
  obtain ⟨hh, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  exact ⟨List.getElem_mem hh, (groups_nodup M d w).idxOf_getElem h hh⟩

noncomputable def groupBirthRegion (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (b : ℤ) : Set (Fin n) :=
  unobservedBirthRegion M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w univ h) (d.H ∪ d.D ∪ d.C : Finset (Fin n)) h b

noncomputable def competition (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (b : ℤ) : Set (Fin n) :=
  lowerCompetition M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w d.T) b h

lemma groupBirthRegion_eligible (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (b : ℤ)
    (hb : b % 2 = (if d.odd then 1 else 0)) {e : Fin n}
    (he : e ∈ groupBirthRegion M hE d w h b ∩ (d.T : Set (Fin n)))
    (hf : e ∉ finalPath M hE d w (b-2)) :
    e ∈ assignedEligible (assign M hE d w) w ∧
      assignedLayer (assign M hE d w) w e = b := by
  classical
  have ht := he.2
  have hr := he.1
  unfold groupBirthRegion unobservedBirthRegion at hr
  split_ifs at hr with ha
  · obtain ⟨⟨⟨_, hc, hg⟩, hX⟩, hO⟩ := hr
    obtain ⟨i, hwi⟩ : ∃ i, w e = some i := Option.ne_none_iff_exists'.mp hc.1
    have hget : (groups M d w)[h]? = some i := hg.symm.trans hwi
    obtain ⟨hi, hidx⟩ := groups_index_of_get M d w hget
    have hbirth : birth M hE d w e i = b := by
      unfold birth
      rw [hidx]
      exact (mem_nominal_difference_iff M hE (2^100) _ _ h e
        (candidate_nonloop M d w e _ hc) b).mp hX
    have hel : eligible M hE d w e i := by
      refine ⟨hO, ?_, hi, ht, ?_, ?_, ?_⟩
      · rwa [← hwi]
      · rwa [hidx, hbirth]
      · rwa [hbirth]
      · rwa [hbirth]
    have has : assign M hE d w e (w e) = some b :=
      (assign_spec M hE d w e _ b).mpr ⟨i, hwi, hel, hbirth⟩
    constructor
    · simp [assignedEligible, has]
    · simp [assignedLayer, has]
  · exact False.elim hr

lemma selection_low_mem_competition (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n)
    (h : ℕ) (b : ℤ) {e : Fin n} (he : e ∈ selection M hE d w π)
    (hb : assignedLayer (assign M hE d w) w e = b)
    (hlow : ¬ ∃ i, w e = some i ∧ h ≤ (groups M d w).idxOf i) :
    e ∈ competition M hE d w h b := by
  have hel := layerGreedy_subset M _ _ _ _ he
  obtain ⟨i, hwi, hi, hbi⟩ := (assign_spec M hE d w e _ _).mp
    (assigned_some_of_eligible (assign M hE d w) w e hel)
  have hidx : (groups M d w).idxOf i < h := by
    by_contra hn
    exact hlow ⟨i, hwi, by omega⟩
  apply lowerCompetition_member M hE (2^100) _ _ _ b hidx
  constructor
  · exact ⟨hi.2.2.2.1, by simpa only [hwi] using hi.2.1, hwi.trans (groups_get?_idxOf M d w i hi.2.2.1).symm⟩
  · apply (mem_nominal_difference_iff M hE (2^100) _ _ _ e
      (candidate_nonloop M d w e _ hi.2.1) b).mpr
    exact hbi.trans hb

theorem selection_cumulative_rank (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n)
    (h : ℕ) (L : Finset ℤ) (hL : ∀ b ∈ L, b % 2 = (if d.odd then 1 else 0)) :
    (∑ b ∈ L, conditionalRank M
      (groupBirthRegion M hE d w h b ∩ (d.T : Set (Fin n)))
      (finalPath M hE d w (b-2) ∪ competition M hE d w h b)) ≤
      ((selection M hE d w π).filter (fun e =>
        ∃ i, w e = some i ∧ h ≤ (groups M d w).idxOf i)).card := by
  classical
  exact layerGreedy_sum_rank_lower M hE _ _ _ _ L _ _ _
    (fun b hb e he => groupBirthRegion_eligible M hE d w h b (hL b hb) he.1 he.2)
    (fun b _ e he hb hn => selection_low_mem_competition M hE d w π h b he hb hn)

end MainAlgorithm
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α : Type*} [Fintype α]

def oldPrefix (b : ℕ → α) (k : ℕ) : Set α := {x | ∃ i < k, b i = x}

@[simp] lemma oldPrefix_zero
    {α : Type u_1} [Fintype α] (b : ℕ → α) : oldPrefix b 0 = ∅ := by
  ext x
  simp [oldPrefix]

lemma oldPrefix_succ
    {α : Type u_1} [Fintype α] (b : ℕ → α) (k : ℕ) :
    oldPrefix b (k + 1) = insert (b k) (oldPrefix b k) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact Or.inr ⟨i, hi, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨k, Nat.lt_succ_self k, rfl⟩
    · exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self k), rfl⟩

lemma oldPrefix_mono
    {α : Type u_1} [Fintype α] (b : ℕ → α) : Monotone (oldPrefix b) := by
  intro j k hjk x hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, lt_of_lt_of_le hi hjk, rfl⟩

lemma conditionalRank_singleton_of_notMem_closure (M : Matroid α)
    (P : Set α) {e : α} (he : e ∈ M.E) (hne : e ∉ M.closure P) :
    conditionalRank M {e} P = 1 := by
  unfold conditionalRank natRank
  rw [Set.singleton_union, M.eRk_insert_eq_add_one ⟨he, hne⟩,
    ENat.toNat_add (rank_ne_top M P) (by simp)]
  simp

lemma conditionalRank_singleton_of_mem_closure
    {α : Type u_1} [Fintype α] (M : Matroid α)
    (P : Set α) {e : α} (he : e ∈ M.closure P) :
    conditionalRank M {e} P = 0 := by
  have h := congrArg (natRank M) (M.closure_insert_eq_of_mem_closure he)
  simp only [natRank_closure] at h
  simp only [conditionalRank, Set.singleton_union, h, Nat.sub_self]

noncomputable def omittable (M : Matroid α) (b : ℕ → α) (A : Set α) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range r).filter (fun k => b k ∈ M.closure (oldPrefix b k ∪ A))

lemma omittable_drop (M : Matroid α) (b : ℕ → α) (A : Set α) (k : ℕ)
    (he : b k ∈ M.E) (hind : b k ∉ M.closure (oldPrefix b k))
    (homit : b k ∈ M.closure (oldPrefix b k ∪ A)) :
    conditionalRank M A (oldPrefix b (k + 1)) + 1 =
      conditionalRank M A (oldPrefix b k) := by
  have hex := conditionalRank_exchange M {b k} A (oldPrefix b k)
  rw [conditionalRank_singleton_of_notMem_closure M _ he hind,
    conditionalRank_singleton_of_mem_closure M _ homit] at hex
  rw [oldPrefix_succ, Set.union_singleton] at *
  omega

lemma card_omittable_le_rank (M : Matroid α) (b : ℕ → α) (A : Set α) (r : ℕ)
    (he : ∀ k < r, b k ∈ M.E)
    (hind : ∀ k < r, b k ∉ M.closure (oldPrefix b k)) :
    (omittable M b A r).card ≤ natRank M A := by
  classical
  let p := fun k => conditionalRank M A (oldPrefix b k)
  have hp : ∀ k < r, p (k + 1) ≤ p k := by
    intro k _
    exact conditionalRank_antitone M A (oldPrefix_mono b (Nat.le_succ k))
  have hdrop := sum_potential_drop_le p r hp
  have hsum : (omittable M b A r).card ≤ ∑ k ∈ range r, (p k - p (k + 1)) := by
    rw [Finset.card_eq_sum_ones]
    calc
      (∑ k ∈ omittable M b A r, 1) ≤
          ∑ k ∈ omittable M b A r, (p k - p (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_filter.mp hk
        have hkr := Finset.mem_range.mp hk'.1
        have hd := omittable_drop M b A k (he k hkr) (hind k hkr) hk'.2
        change p (k + 1) + 1 = p k at hd
        omega
      _ ≤ ∑ k ∈ range r, (p k - p (k + 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro _ _ _
          exact Nat.zero_le _
  have hzero : p 0 = natRank M A := by simp [p, conditionalRank]
  omega

lemma notMem_closure_before_nonomittable
    {α : Type u_1} [Fintype α] (M : Matroid α) (b : ℕ → α)
    (A P : Set α) (r k : ℕ) (hk : k < r)
    (hkeep : k ∉ omittable M b A r) (hP : P ⊆ oldPrefix b k ∪ A) :
    b k ∉ M.closure P := by
  classical
  intro he
  apply hkeep
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,
    M.closure_subset_closure hP he⟩

noncomputable def vulnerable (M : Matroid α) (b : ℕ → α) (A : Set α) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range r).filter (fun k =>
    b k ∉ M.closure (oldPrefix b k) ∧ b k ∈ M.closure (oldPrefix b k ∪ A))

lemma card_vulnerable_le_rank (M : Matroid α) (b : ℕ → α) (A : Set α) (r : ℕ)
    (he : ∀ k < r, b k ∈ M.E) :
    (vulnerable M b A r).card ≤ natRank M A := by
  classical
  let p := fun k => conditionalRank M A (oldPrefix b k)
  have hp : ∀ k < r, p (k + 1) ≤ p k := by
    intro k _
    exact conditionalRank_antitone M A (oldPrefix_mono b (Nat.le_succ k))
  have hdrop := sum_potential_drop_le p r hp
  have hsum : (vulnerable M b A r).card ≤ ∑ k ∈ range r, (p k - p (k + 1)) := by
    rw [Finset.card_eq_sum_ones]
    calc
      (∑ k ∈ vulnerable M b A r, 1) ≤
          ∑ k ∈ vulnerable M b A r, (p k - p (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_filter.mp hk
        have hkr := Finset.mem_range.mp hk'.1
        have hd := omittable_drop M b A k (he k hkr) hk'.2.1 hk'.2.2
        change p (k + 1) + 1 = p k at hd
        omega
      _ ≤ ∑ k ∈ range r, (p k - p (k + 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro _ _ _
          exact Nat.zero_le _
  have hzero : p 0 = natRank M A := by simp [p, conditionalRank]
  omega

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

variable {α : Type*} [DecidableEq α]

lemma card_family_with_fixed_core (family : Finset (Finset α))
    (core extra : Finset α)
    (hcore : ∀ J ∈ family, core ⊆ J)
    (hcover : ∀ J ∈ family, J ⊆ core ∪ extra) :
    family.card ≤ 2 ^ extra.card := by
  rw [← Finset.card_powerset extra]
  apply Finset.card_le_card_of_injOn (fun J => J \ core)
  · intro J hJ
    apply Finset.mem_powerset.mpr
    intro x hx
    have hcov := hcover J hJ (Finset.mem_sdiff.mp hx).1
    exact (Finset.mem_union.mp hcov).resolve_left (Finset.mem_sdiff.mp hx).2
  · intro J hJ K hK heq
    apply Finset.ext
    intro x
    by_cases hx : x ∈ core
    · exact iff_of_true (hcore J hJ hx) (hcore K hK hx)
    · have hmem := congrArg (fun L : Finset α => x ∈ L) heq
      simpa [Finset.mem_sdiff, hx] using hmem

lemma card_retained_family (family : Finset (Finset α))
    (old movable omittable : Finset α) (s : ℕ)
    (hm : movable.card ≤ s) (ho : omittable.card ≤ s)
    (hcore : ∀ J ∈ family, old \ omittable ⊆ J)
    (hcover : ∀ J ∈ family, J ⊆ old ∪ movable) :
    family.card ≤ 4 ^ s := by
  have h := card_family_with_fixed_core family (old \ omittable)
    (omittable ∪ movable) hcore (by
      intro J hJ x hx
      rcases Finset.mem_union.mp (hcover J hJ hx) with hxold | hxmov
      · by_cases hxo : x ∈ omittable
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ hxo)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxold, hxo⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hxmov))
  have hcard : (omittable ∪ movable).card ≤ 2 * s :=
    (Finset.card_union_le _ _).trans (by omega)
  calc
    family.card ≤ 2 ^ (omittable ∪ movable).card := h
    _ ≤ 2 ^ (2 * s) := Nat.pow_le_pow_right (by decide) hcard
    _ = 4 ^ s := by rw [pow_mul]; rfl

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α : Type*} [Fintype α]

abbrev Occurrence (r s : ℕ) := Fin r ⊕ Fin s

def occurrenceLabel {r s : ℕ} (b : ℕ → α) (a : Fin s → α) : Occurrence r s → α :=
  Sum.elim (fun i => b i.val) a

def OldOrdered {r s : ℕ} (time : Occurrence r s → ℕ) : Prop :=
  ∀ i j : Fin r, i < j → time (Sum.inl i) < time (Sum.inl j)

noncomputable def retained {r s : ℕ} (M : Matroid α) (b : ℕ → α) (a : Fin s → α)
    (time : Occurrence r s → ℕ) : Finset (Occurrence r s) := by
  classical
  exact Finset.univ.filter (fun o => occurrenceLabel b a o ∉
    M.closure (occurrenceLabel b a '' {p | time p < time o}))

noncomputable def retainedFamily {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) : Finset (Finset (Occurrence r s)) := by
  classical
  exact Finset.univ.filter (fun J => ∃ time, OldOrdered time ∧ retained M b a time = J)

lemma before_old_subset
    {α : Type u_1} [Fintype α] {r s : ℕ} (b : ℕ → α) (a : Fin s → α)
    (time : Occurrence r s → ℕ) (horder : OldOrdered time) (i : Fin r) :
    occurrenceLabel b a '' {p | time p < time (Sum.inl i)} ⊆
      oldPrefix b i.val ∪ Set.range a := by
  rintro x ⟨o, ho, rfl⟩
  cases o with
  | inl j =>
    left
    have hji : j < i := by
      by_contra hji
      rcases lt_or_eq_of_le (le_of_not_gt hji) with hij | rfl
      · exact Nat.lt_asymm (horder i j hij) ho
      · exact Nat.lt_irrefl _ ho
    exact ⟨j.val, hji, rfl⟩
  | inr j => exact Or.inr ⟨j, rfl⟩

lemma retains_nonomittable_old {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) (time : Occurrence r s → ℕ) (horder : OldOrdered time)
    (i : Fin r) (hi : i.val ∉ omittable M b (Set.range a) r) :
    Sum.inl i ∈ retained M b a time := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact notMem_closure_before_nonomittable M b (Set.range a) _ r i.val i.isLt hi
    (before_old_subset b a time horder i)

lemma card_retainedFamily_le {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) (he : ∀ k < r, b k ∈ M.E)
    (hind : ∀ k < r, b k ∉ M.closure (oldPrefix b k)) :
    (retainedFamily (r := r) M b a).card ≤ 4 ^ s := by
  classical
  let old : Finset (Occurrence r s) := Finset.univ.image Sum.inl
  let movable : Finset (Occurrence r s) := Finset.univ.image Sum.inr
  let omissions : Finset (Occurrence r s) := old.filter (fun o =>
    match o with
    | Sum.inl i => i.val ∈ omittable M b (Set.range a) r
    | Sum.inr _ => False)
  have hmov : movable.card ≤ s := by
    simp [movable, Finset.card_image_of_injective, Sum.inr_injective]
  have homit : omissions.card ≤ (omittable M b (Set.range a) r).card := by
    apply Finset.card_le_card_of_injOn
      (fun o : Occurrence r s => Sum.elim Fin.val (fun _ => 0) o)
    · intro o ho
      rcases Finset.mem_filter.mp ho with ⟨_, ho⟩
      cases o with
      | inl i => exact ho
      | inr j => exact False.elim ho
    · intro o ho p hp hop
      have ho' := (Finset.mem_filter.mp ho).2
      have hp' := (Finset.mem_filter.mp hp).2
      cases o with
      | inr i => exact False.elim ho'
      | inl i =>
        cases p with
        | inr j => exact False.elim hp'
        | inl j => exact congrArg Sum.inl (Fin.ext hop)
  have hrank : natRank M (Set.range a) ≤ (Set.range a).ncard := by
    exact ENat.toNat_le_toNat (M.eRk_le_encard _)
      (Set.toFinite (Set.range a)).encard_lt_top.ne
  have hrange : (Set.range a).ncard ≤ s := by
    simpa using (Set.ncard_image_le (f := a) (s := Set.univ))
  apply card_retained_family (retainedFamily M b a) old movable omissions s hmov
    (homit.trans ((card_omittable_le_rank M b (Set.range a) r he hind).trans
      (hrank.trans hrange)))
  · intro J hJ o ho
    obtain ⟨time, horder, rfl⟩ := (Finset.mem_filter.mp hJ).2
    have hoo := (Finset.mem_sdiff.mp ho).1
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hoo
    apply retains_nonomittable_old M b a time horder i
    intro hi
    exact (Finset.mem_sdiff.mp ho).2 (Finset.mem_filter.mpr ⟨hoo, hi⟩)
  · intro J hJ o ho
    cases o with
    | inl i => exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    | inr j => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α : Type*} [Fintype α]

lemma oldPrefix_subset_before
    {α : Type u_1} [Fintype α] {r s : ℕ} (b : ℕ → α) (a : Fin s → α)
    (time : Occurrence r s → ℕ) (horder : OldOrdered time) (i : Fin r) :
    oldPrefix b i.val ⊆ occurrenceLabel b a '' {p | time p < time (Sum.inl i)} := by
  rintro x ⟨k, hk, rfl⟩
  let j : Fin r := ⟨k, lt_trans hk i.isLt⟩
  exact ⟨Sum.inl j, horder j i hk, rfl⟩

lemma retained_old_initially_nonredundant {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) (time : Occurrence r s → ℕ) (horder : OldOrdered time)
    (i : Fin r) (hi : Sum.inl i ∈ retained M b a time) :
    b i.val ∉ M.closure (oldPrefix b i.val) := by
  classical
  intro hdep
  exact (Finset.mem_filter.mp hi).2
    (M.closure_subset_closure (oldPrefix_subset_before b a time horder i) hdep)

lemma card_retainedFamily_arbitrary_old {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) (he : ∀ k < r, b k ∈ M.E) :
    (retainedFamily (r := r) M b a).card ≤ 4 ^ s := by
  classical
  let old : Finset (Occurrence r s) :=
    (Finset.univ.filter (fun i : Fin r => b i.val ∉ M.closure (oldPrefix b i.val))).image Sum.inl
  let movable : Finset (Occurrence r s) := Finset.univ.image Sum.inr
  let omissions : Finset (Occurrence r s) := old.filter (fun o =>
    match o with
    | Sum.inl i => i.val ∈ vulnerable M b (Set.range a) r
    | Sum.inr _ => False)
  have hmov : movable.card ≤ s := by
    simp [movable, Finset.card_image_of_injective, Sum.inr_injective]
  have homit : omissions.card ≤ (vulnerable M b (Set.range a) r).card := by
    apply Finset.card_le_card_of_injOn
      (fun o : Occurrence r s => Sum.elim Fin.val (fun _ => 0) o)
    · intro o ho
      have ho' := (Finset.mem_filter.mp ho).2
      cases o with
      | inl i => exact ho'
      | inr j => exact False.elim ho'
    · intro o ho p hp hop
      have ho' := (Finset.mem_filter.mp ho).2
      have hp' := (Finset.mem_filter.mp hp).2
      cases o with
      | inr i => exact False.elim ho'
      | inl i =>
        cases p with
        | inr j => exact False.elim hp'
        | inl j => exact congrArg Sum.inl (Fin.ext hop)
  have hrank : natRank M (Set.range a) ≤ (Set.range a).ncard := by
    exact ENat.toNat_le_toNat (M.eRk_le_encard _)
      (Set.toFinite (Set.range a)).encard_lt_top.ne
  have hrange : (Set.range a).ncard ≤ s := by
    simpa using (Set.ncard_image_le (f := a) (s := Set.univ))
  apply card_retained_family (retainedFamily M b a) old movable omissions s hmov
    (homit.trans ((card_vulnerable_le_rank M b (Set.range a) r he).trans
      (hrank.trans hrange)))
  · intro J hJ o ho
    obtain ⟨time, horder, rfl⟩ := (Finset.mem_filter.mp hJ).2
    have hoo := (Finset.mem_sdiff.mp ho).1
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hoo
    have hind := (Finset.mem_filter.mp hi).2
    apply retains_nonomittable_old M b a time horder i
    intro hom
    have hom' := (Finset.mem_filter.mp hom).2
    have hv : i.val ∈ vulnerable M b (Set.range a) r :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, hind, hom'⟩
    exact (Finset.mem_sdiff.mp ho).2 (Finset.mem_filter.mpr ⟨hoo, hv⟩)
  · intro J hJ o ho
    obtain ⟨time, horder, rfl⟩ := (Finset.mem_filter.mp hJ).2
    cases o with
    | inl i =>
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        retained_old_initially_nonredundant M b a time horder i ho⟩, rfl⟩
    | inr j => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open Finset

variable {r q : ℕ}

def oldBefore (time : Occurrence r q → ℕ) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin r => time (Sum.inl i) < t)).card

def movableBefore (time : Occurrence r q → ℕ) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin q => time (Sum.inr i) < t)).card

lemma oldBefore_mono (time : Occurrence r q → ℕ) : Monotone (oldBefore time) := by
  intro u v huv
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    lt_of_lt_of_le (Finset.mem_filter.mp hi).2 huv⟩

lemma movableBefore_mono (time : Occurrence r q → ℕ) : Monotone (movableBefore time) := by
  intro u v huv
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    lt_of_lt_of_le (Finset.mem_filter.mp hi).2 huv⟩

lemma oldBefore_lt_after (time : Occurrence r q → ℕ) (i : Fin r) {t : ℕ}
    (hit : time (Sum.inl i) < t) :
    oldBefore time (time (Sum.inl i)) < oldBefore time t := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hj).2 hit⟩
  · intro heq
    have hi : i ∈ Finset.univ.filter (fun j : Fin r => time (Sum.inl j) < t) := by simp [hit]
    rw [← heq] at hi
    simp at hi

lemma movableBefore_lt_after (time : Occurrence r q → ℕ) (i : Fin q) {t : ℕ}
    (hit : time (Sum.inr i) < t) :
    movableBefore time (time (Sum.inr i)) < movableBefore time t := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hj).2 hit⟩
  · intro heq
    have hi : i ∈ Finset.univ.filter (fun j : Fin q => time (Sum.inr j) < t) := by simp [hit]
    rw [← heq] at hi
    simp at hi

lemma movableBefore_self_lt (time : Occurrence r q → ℕ) (i : Fin q) :
    movableBefore time (time (Sum.inr i)) < q := by
  have hcard : (Finset.univ.filter (fun j : Fin q => time (Sum.inr j) < time (Sum.inr i))).card <
      (Finset.univ : Finset (Fin q)).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hi : i ∈ (Finset.univ : Finset (Fin q)) := Finset.mem_univ _
    rw [← heq] at hi
    simp at hi
  simpa [movableBefore] using hcard

lemma old_time_lt_iff (time : Occurrence r q → ℕ) (horder : OldOrdered time)
    (i j : Fin r) : time (Sum.inl i) < time (Sum.inl j) ↔ i < j := by
  refine ⟨fun hij => ?_, fun hij => horder i j hij⟩
  by_contra h
  rcases lt_or_eq_of_le (le_of_not_gt h) with hji | rfl
  · exact Nat.lt_asymm (horder j i hji) hij
  · exact Nat.lt_irrefl _ hij

lemma oldBefore_self (time : Occurrence r q → ℕ) (horder : OldOrdered time) (i : Fin r) :
    oldBefore time (time (Sum.inl i)) = i.val := by
  unfold oldBefore
  have heq : Finset.univ.filter (fun j : Fin r => time (Sum.inl j) < time (Sum.inl i)) =
      Finset.Iio i := by
    ext j
    simp [old_time_lt_iff time horder]
  rw [heq, Fin.card_Iio]

def scoreExponent (s : ℕ) (time : Occurrence r q → ℕ) : Occurrence r q → ℕ
  | Sum.inl i => (s + 1) * (i.val + 1)
  | Sum.inr i => (s + 1) * oldBefore time (time (Sum.inr i)) +
      movableBefore time (time (Sum.inr i)) + 1

@[simp] lemma scoreExponent_old (s : ℕ) (time : Occurrence r q → ℕ) (i : Fin r) :
    scoreExponent s time (Sum.inl i) = (s + 1) * (i.val + 1) := rfl

lemma scoreExponent_preserves_order (s : ℕ) (hqs : q ≤ s)
    (time : Occurrence r q → ℕ) (horder : OldOrdered time)
    {o p : Occurrence r q} (hop : time o < time p) :
    scoreExponent s time o < scoreExponent s time p := by
  cases o with
  | inl i =>
    cases p with
    | inl j =>
      have hij := (old_time_lt_iff time horder i j).mp hop
      exact Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right hij 1) (by omega)
    | inr j =>
      have hcnt := oldBefore_lt_after time i hop
      rw [oldBefore_self time horder i] at hcnt
      have hmul := Nat.mul_le_mul_left (s + 1) (Nat.succ_le_of_lt hcnt)
      simp only [Nat.succ_eq_add_one] at hmul
      simp only [scoreExponent]
      omega
  | inr i =>
    have hbound := lt_of_lt_of_le (movableBefore_self_lt time i) hqs
    have hmono := oldBefore_mono time (Nat.le_of_lt hop)
    cases p with
    | inl j =>
      rw [oldBefore_self time horder j] at hmono
      have hmul := Nat.mul_le_mul_left (s + 1) hmono
      simp only [scoreExponent, Nat.mul_add, Nat.mul_one]
      omega
    | inr j =>
      have hstrict := movableBefore_lt_after time i hop
      rcases Nat.eq_or_lt_of_le hmono with heq | hlt
      · simp only [scoreExponent]
        rw [heq]
        omega
      · have hmul := Nat.mul_le_mul_left (s + 1) (Nat.succ_le_of_lt hlt)
        simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hmul
        simp only [scoreExponent]
        omega

lemma scoreExponent_injective (s : ℕ) (hqs : q ≤ s)
    (time : Occurrence r q → ℕ) (horder : OldOrdered time) (htime : Function.Injective time) :
    Function.Injective (scoreExponent s time) := by
  intro o p heq
  apply htime
  apply le_antisymm
  · by_contra h
    have hlt := scoreExponent_preserves_order s hqs time horder (Nat.lt_of_not_ge h)
    omega
  · by_contra h
    have hlt := scoreExponent_preserves_order s hqs time horder (Nat.lt_of_not_ge h)
    omega

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open Set

variable {α : Type*} {M : Matroid α} {I J : Set α} {e : α}

def support (M : Matroid α) (I : Set α) (e : α) : Set α :=
  ⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J}

lemma support_subset (he : e ∈ M.closure I) : support M I e ⊆ I :=
  Set.sInter_subset_of_mem ⟨Subset.rfl, he⟩

lemma support_subset_of_mem_closure (hJI : J ⊆ I) (he : e ∈ M.closure J) :
    support M I e ⊆ J :=
  Set.sInter_subset_of_mem ⟨hJI, he⟩

lemma mem_closure_support (hI : M.Indep I) (he : e ∈ M.closure I) :
    e ∈ M.closure (support M I e) := by
  rw [support, hI.closure_sInter_eq_biInter_closure_of_forall_subset
    (Js := {J | J ⊆ I ∧ e ∈ M.closure J})
    ⟨I, Subset.rfl, he⟩ (fun _ hJ => hJ.1)]
  exact Set.mem_iInter₂.mpr (fun _ hJ => hJ.2)

lemma mem_closure_iff_support_subset (hI : M.Indep I)
    (he : e ∈ M.closure I) (hJI : J ⊆ I) :
    e ∈ M.closure J ↔ support M I e ⊆ J := by
  constructor
  · exact support_subset_of_mem_closure hJI
  · intro h
    exact M.closure_subset_closure h (mem_closure_support hI he)

lemma support_nonempty (hI : M.Indep I) (he : e ∈ M.closure I)
    (hne : e ∉ M.closure ∅) : (support M I e).Nonempty := by
  by_contra h
  have hem := mem_closure_support hI he
  rw [Set.not_nonempty_iff_eq_empty.mp h] at hem
  exact hne hem

lemma support_unique (hI : M.Indep I) (he : e ∈ M.closure I)
    (hJI : J ⊆ I) (hJe : e ∈ M.closure J)
    (hmin : ∀ K ⊆ I, e ∈ M.closure K → J ⊆ K) : J = support M I e := by
  exact Set.Subset.antisymm
    (hmin _ (support_subset he) (mem_closure_support hI he))
    (support_subset_of_mem_closure hJI hJe)

lemma old_redundant_after_insertions (he : e ∈ M.closure I) (A : Set α) :
    M.closure (insert e (I ∪ A)) = M.closure (I ∪ A) := by
  exact M.closure_insert_eq_of_mem_closure
    (M.closure_subset_closure Set.subset_union_left he)

lemma mem_closure_prefix_iff (hI : M.Indep I) (he : e ∈ M.closure I)
    (time : α → ℕ) (k : ℕ) :
    e ∈ M.closure {x | x ∈ I ∧ time x ≤ k} ↔
      ∀ x ∈ support M I e, time x ≤ k := by
  rw [mem_closure_iff_support_subset hI he (fun _ hx => hx.1)]
  constructor
  · intro h x hx
    exact (h hx).2
  · intro h x hx
    exact ⟨support_subset he hx, h x hx⟩

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α β : Type*} [Fintype β] [DecidableEq β]

noncomputable def keptOccurrences (M : Matroid α) (label : β → α) (time : β → ℕ) :
    Finset β := by
  classical
  exact Finset.univ.filter (fun o => label o ∉ M.closure (label '' {p | time p < time o}))

lemma mem_closure_kept_upto (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (o : β) :
    label o ∈ M.closure (label '' {p | p ∈ keptOccurrences M label time ∧ time p ≤ time o}) := by
  classical
  have aux : ∀ k, ∀ o, time o = k →
      label o ∈ M.closure (label '' {p | p ∈ keptOccurrences M label time ∧ time p ≤ k}) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro o ho
      by_cases hkeep : o ∈ keptOccurrences M label time
      · exact M.mem_closure_of_mem ⟨o, ⟨hkeep, ho.le⟩, rfl⟩
          (by rintro _ ⟨p, _, rfl⟩; exact hground p)
      have hdep : label o ∈ M.closure (label '' {p | time p < time o}) := by
        simpa [keptOccurrences] using hkeep
      apply M.closure_subset_closure_of_subset_closure ?_ hdep
      rintro _ ⟨p, hp, rfl⟩
      have hpk : time p < k := by simpa [ho] using hp
      have hih := ih (time p) hpk p rfl
      apply M.closure_subset_closure ?_ hih
      rintro _ ⟨q, ⟨hq, hqt⟩, rfl⟩
      exact ⟨q, ⟨hq, hqt.trans hpk.le⟩, rfl⟩
  exact aux (time o) o rfl

lemma greedy_prefix_closure (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (k : ℕ) :
    M.closure (label '' {o | time o < k}) =
      M.closure (label '' {o | o ∈ keptOccurrences M label time ∧ time o < k}) := by
  classical
  apply Set.Subset.antisymm
  · apply M.closure_subset_closure_of_subset_closure
    rintro _ ⟨o, ho, rfl⟩
    apply M.closure_subset_closure ?_ (mem_closure_kept_upto M label time hground o)
    rintro _ ⟨p, ⟨hp, hpt⟩, rfl⟩
    exact ⟨p, ⟨hp, lt_of_le_of_lt hpt ho⟩, rfl⟩
  · apply M.closure_subset_closure
    rintro _ ⟨o, ⟨_, ho⟩, rfl⟩
    exact ⟨o, ho, rfl⟩

private lemma indep_image_of_notMem_prior
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β] (M : Matroid α) (label : β → α)
    (time : β → ℕ) (htime : Function.Injective time) (s : Finset β)
    (hground : ∀ o ∈ s, label o ∈ M.E)
    (hprior : ∀ o ∈ s, label o ∉ M.closure (label '' {p | p ∈ s ∧ time p < time o})) :
    M.Indep (label '' (s : Set β)) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · simp [hs]
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image s time (Finset.nonempty_iff_ne_empty.mpr hs)
    have hI := ih (s.erase p) (Finset.erase_ssubset hp)
      (fun o ho => hground o (Finset.mem_of_mem_erase ho)) (by
        intro o ho hmem
        apply hprior o (Finset.mem_of_mem_erase ho)
        apply M.closure_subset_closure ?_ hmem
        rintro _ ⟨q, ⟨hq, hqt⟩, rfl⟩
        exact ⟨q, ⟨Finset.mem_of_mem_erase hq, hqt⟩, rfl⟩)
    have hnot : label p ∉ M.closure (label '' (s.erase p : Set β)) := by
      intro hmem
      apply hprior p hp
      apply M.closure_subset_closure ?_ hmem
      rintro _ ⟨q, hq, rfl⟩
      refine ⟨q, ⟨Finset.mem_of_mem_erase hq, ?_⟩, rfl⟩
      apply lt_of_le_of_ne (hmax q (Finset.mem_of_mem_erase hq))
      intro htimeeq
      exact (Finset.ne_of_mem_erase hq) (htime htimeeq)
    have hins := hI.insert_indep_iff.mpr (Or.inl ⟨hground p hp, hnot⟩)
    have hset : insert (label p) (label '' (s.erase p : Set β)) = label '' (s : Set β) := by
      rw [← Set.image_insert_eq, ← Finset.coe_insert, Finset.insert_erase hp]
    rwa [hset] at hins

lemma keptOccurrences_indep (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (htime : Function.Injective time) :
    M.Indep (label '' (keptOccurrences M label time : Set β)) := by
  classical
  apply indep_image_of_notMem_prior M label time htime
  · intro o _
    exact hground o
  · intro o ho hmem
    have hn := (Finset.mem_filter.mp ho).2
    apply hn
    apply M.closure_subset_closure ?_ hmem
    rintro _ ⟨p, ⟨_, hpt⟩, rfl⟩
    exact ⟨p, hpt, rfl⟩

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α β : Type*} [Fintype β] [DecidableEq β]

lemma kept_label_injOn
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β]
    (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (htime : Function.Injective time) :
    Set.InjOn label (keptOccurrences M label time : Set β) := by
  classical
  have hd : ∀ x y, x ∈ keptOccurrences M label time → y ∈ keptOccurrences M label time →
      time x < time y → label x ≠ label y := by
    intro x y _ hy hxy hlabels
    apply (Finset.mem_filter.mp hy).2
    rw [← hlabels]
    exact M.mem_closure_of_mem ⟨x, hxy, rfl⟩ (by rintro _ ⟨z, _, rfl⟩; exact hground z)
  intro x hx y hy hlabels
  apply htime
  rcases lt_trichotomy (time x) (time y) with hlt | heq | hgt
  · exact False.elim (hd x y hx hy hlt hlabels)
  · exact heq
  · exact False.elim (hd y x hy hx hgt hlabels.symm)

noncomputable def occurrenceSupport (M : Matroid α) (label : β → α)
    (J : Finset β) (e : α) : Finset β := by
  classical
  exact J.filter (fun o => label o ∈ support M (label '' (J : Set β)) e)

lemma mem_occurrenceSupport
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β]
    {M : Matroid α} {label : β → α} {J : Finset β} {e : α} {o : β} :
    o ∈ occurrenceSupport M label J e ↔
      o ∈ J ∧ label o ∈ support M (label '' (J : Set β)) e := by
  classical
  simp [occurrenceSupport]

lemma mem_closure_iff_occurrenceSupport (M : Matroid α) (label : β → α)
    (J : Finset β) (e : α) (hI : M.Indep (label '' (J : Set β)))
    (he : e ∈ M.closure (label '' (J : Set β)))
    (hinj : Set.InjOn label (J : Set β)) (P : β → Prop) :
    e ∈ M.closure (label '' {o | o ∈ J ∧ P o}) ↔
      ∀ o ∈ occurrenceSupport M label J e, P o := by
  classical
  rw [mem_closure_iff_support_subset hI he (by
    rintro _ ⟨o, ⟨ho, _⟩, rfl⟩; exact ⟨o, ho, rfl⟩)]
  constructor
  · intro h o ho
    obtain ⟨hoJ, hol⟩ := mem_occurrenceSupport.mp ho
    obtain ⟨p, ⟨hpJ, hpP⟩, hp⟩ := h hol
    exact (hinj hpJ hoJ hp) ▸ hpP
  · intro h x hx
    obtain ⟨o, ho, rfl⟩ := support_subset he hx
    exact ⟨o, ⟨ho, h o (mem_occurrenceSupport.mpr ⟨ho, hx⟩)⟩, rfl⟩

def IsPivot (M : Matroid α) (label : β → α) (time : β → ℕ) (e : α) (o : β) : Prop :=
  e ∈ M.closure (label '' {p | time p ≤ time o}) ∧
    e ∉ M.closure (label '' {p | time p < time o})

lemma pivot_mem_support_and_max (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (htime : Function.Injective time)
    {e : α} {o : β} (hpivot : IsPivot M label time e o) :
    o ∈ occurrenceSupport M label (keptOccurrences M label time) e ∧
      ∀ p ∈ occurrenceSupport M label (keptOccurrences M label time) e, time p ≤ time o := by
  classical
  let J := keptOccurrences M label time
  have hI := keptOccurrences_indep M label time hground htime
  have hinj := kept_label_injOn M label time hground htime
  have hup : e ∈ M.closure (label '' {p | p ∈ J ∧ time p ≤ time o}) := by
    have h := hpivot.1
    have hcl := greedy_prefix_closure M label time hground (time o + 1)
    simp only [Nat.lt_succ_iff] at hcl
    rw [hcl] at h
    exact h
  have he : e ∈ M.closure (label '' (J : Set β)) := by
    apply M.closure_subset_closure ?_ hup
    rintro _ ⟨p, ⟨hp, _⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  have hmax := (mem_closure_iff_occurrenceSupport M label J e hI he hinj
    (fun p => time p ≤ time o)).mp hup
  have hnot : ¬ ∀ p ∈ occurrenceSupport M label J e, time p < time o := by
    intro h
    apply hpivot.2
    rw [greedy_prefix_closure M label time hground (time o)]
    exact (mem_closure_iff_occurrenceSupport M label J e hI he hinj
      (fun p => time p < time o)).mpr h
  push Not at hnot
  obtain ⟨p, hp, hge⟩ := hnot
  have heq : p = o := htime (Nat.le_antisymm (hmax p hp) hge)
  exact ⟨heq ▸ hp, hmax⟩

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

lemma sum_positive_iff_pivot_positive (s : Finset α) (w : α → ℝ) {p : α}
    (hp : p ∈ s) (hdom : ∑ i ∈ s.erase p, |w i| < |w p|) :
    0 < ∑ i ∈ s, w i ↔ 0 < w p := by
  have habs : |∑ i ∈ s.erase p, w i| ≤ ∑ i ∈ s.erase p, |w i| :=
    Finset.abs_sum_le_sum_abs _ _
  have hbounds := abs_le.mp habs
  have hsum : (∑ i ∈ s, w i) = (∑ i ∈ s.erase p, w i) + w p :=
    (Finset.sum_erase_add _ _ hp).symm
  rw [hsum]
  by_cases hwp : 0 ≤ w p
  · rw [abs_of_nonneg hwp] at hdom
    constructor <;> intro h <;> linarith
  · rw [abs_of_neg (lt_of_not_ge hwp)] at hdom
    constructor <;> intro h <;> linarith

lemma sum_negative_iff_pivot_negative (s : Finset α) (w : α → ℝ) {p : α}
    (hp : p ∈ s) (hdom : ∑ i ∈ s.erase p, |w i| < |w p|) :
    (∑ i ∈ s, w i) < 0 ↔ w p < 0 := by
  have h := sum_positive_iff_pivot_positive s (fun i => -w i) hp (by simpa using hdom)
  simpa only [Finset.sum_neg_distrib, neg_pos] using h

lemma sum_range_two_pow (n : ℕ) : ∑ i ∈ Finset.range n, (2 : ℝ)^i = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

lemma sum_two_pow_lt (s : Finset ℕ) (k : ℕ) (hsk : ∀ i ∈ s, i < k) :
    (∑ i ∈ s, (2 : ℝ)^i) < 2^k := by
  have hsub : s ⊆ Finset.range k := fun i hi => Finset.mem_range.mpr (hsk i hi)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => show 0 ≤ (2 : ℝ)^i from pow_nonneg (by norm_num) _)
  rw [sum_range_two_pow] at hle
  linarith

lemma sum_signed_powers_positive_iff (s : Finset ℕ) (w : ℕ → ℝ) {p : ℕ}
    (hp : p ∈ s) (hmax : ∀ i ∈ s, i ≤ p) (hw : ∀ i ∈ s, |w i| = 2^i) :
    0 < ∑ i ∈ s, w i ↔ 0 < w p := by
  apply sum_positive_iff_pivot_positive s w hp
  rw [hw p hp]
  calc
    (∑ i ∈ s.erase p, |w i|) = ∑ i ∈ s.erase p, (2 : ℝ)^i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hw i (Finset.mem_of_mem_erase hi)
    _ < 2^p := sum_two_pow_lt _ _ (fun i hi =>
      lt_of_le_of_ne (hmax i (Finset.mem_of_mem_erase hi)) (Finset.ne_of_mem_erase hi))

lemma sum_positive_iff_max_exponent (s : Finset α) (w : α → ℝ) (exponent : α → ℕ)
    (hinj : Function.Injective exponent) {p : α} (hp : p ∈ s)
    (hmax : ∀ i ∈ s, i ≠ p → exponent i < exponent p)
    (hw : ∀ i ∈ s, |w i| = 2 ^ exponent i) :
    0 < ∑ i ∈ s, w i ↔ 0 < w p := by
  apply sum_positive_iff_pivot_positive s w hp
  rw [hw p hp]
  calc
    (∑ i ∈ s.erase p, |w i|) = ∑ i ∈ s.erase p, (2 : ℝ) ^ exponent i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hw i (Finset.mem_of_mem_erase hi)
    _ = ∑ j ∈ (s.erase p).image exponent, (2 : ℝ) ^ j := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact hinj hij
    _ < 2 ^ exponent p := by
      apply sum_two_pow_lt
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact hmax i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open scoped BigOperators

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
variable [AddCommGroup X] [Module ℝ X]

def RealizesSigns (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (t : Finset ι) (x : X) : Prop :=
  ∀ i, if i ∈ t then 0 < v i x + c i else v i x + c i < 0

noncomputable def affinePatterns (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ) :
    Finset (Finset ι) := by
  classical
  exact Finset.univ.filter (fun t => ∃ x, RealizesSigns v c t x)

lemma mem_affinePatterns {v : ι → X →ₗ[ℝ] ℝ} {c : ι → ℝ} {t : Finset ι} :
    t ∈ affinePatterns v c ↔ ∃ x, RealizesSigns v c t x := by
  classical
  simp [affinePatterns]

private lemma exists_positive_combination
    (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (hreal : ∀ t : Finset ι, ∃ x, RealizesSigns v c t x)
    (a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    ∃ x, 0 < ∑ i, a i * (v i x + c i) := by
  classical
  obtain ⟨x, hx⟩ := hreal (Finset.univ.filter (fun i => 0 < a i))
  have hpos (i : ι) (hai : 0 < a i) : 0 < v i x + c i := by
    simpa [RealizesSigns, hai] using hx i
  have hneg (i : ι) (hai : ¬ 0 < a i) : v i x + c i < 0 := by
    simpa [RealizesSigns, hai] using hx i
  refine ⟨x, Finset.sum_pos' (fun i _ => ?_) ?_⟩
  · by_cases hai : 0 < a i
    · exact mul_nonneg (le_of_lt hai) (le_of_lt (hpos i hai))
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hai) (le_of_lt (hneg i hai))
  · obtain ⟨i, hi⟩ := ha
    refine ⟨i, Finset.mem_univ i, ?_⟩
    by_cases hai : 0 < a i
    · exact mul_pos hai (hpos i hai)
    · exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (le_of_not_gt hai) hi) (hneg i hai)

omit [DecidableEq ι] in
private lemma sum_affine_eq_of_linear_combination_zero
    {v : ι → X →ₗ[ℝ] ℝ} (c : ι → ℝ) {a : ι → ℝ}
    (ha : ∑ i, a i • v i = 0) (x : X) :
    (∑ i, a i * (v i x + c i)) = ∑ i, a i * c i := by
  have hz := congrArg (fun f : X →ₗ[ℝ] ℝ => f x) ha
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.zero_apply] at hz
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hz, zero_add]

lemma linearIndependent_of_all_signs
    (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (hreal : ∀ t : Finset ι, ∃ x, RealizesSigns v c t x) :
    LinearIndependent ℝ v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  by_contra hi
  obtain ⟨x, hx⟩ := exists_positive_combination v c hreal a ⟨i, hi⟩
  obtain ⟨y, hy⟩ := exists_positive_combination v c hreal (fun j => -a j)
    ⟨i, neg_ne_zero.mpr hi⟩
  simp only [neg_mul, Finset.sum_neg_distrib] at hy
  rw [sum_affine_eq_of_linear_combination_zero c ha x] at hx
  rw [sum_affine_eq_of_linear_combination_zero c ha y] at hy
  linarith

lemma all_signs_of_shatters {v : ι → X →ₗ[ℝ] ℝ} {c : ι → ℝ}
    {s : Finset ι} (hs : (affinePatterns v c).Shatters s) :
    ∀ t : Finset s, ∃ x,
      RealizesSigns (fun i : s => v i) (fun i : s => c i) t x := by
  classical
  intro t
  obtain ⟨u, hu, hsu⟩ := hs (t := t.image Subtype.val) (by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact j.property)
  obtain ⟨x, hx⟩ := mem_affinePatterns.mp hu
  refine ⟨x, fun i => ?_⟩
  have hi : (i : ι) ∈ u ↔ i ∈ t := by
    have heq := congrArg (fun z : Finset ι => (i : ι) ∈ z) hsu
    simpa [Finset.mem_image, i.property] using heq
  simpa only [hi] using hx i

lemma shatters_card_le_finrank [FiniteDimensional ℝ X]
    {v : ι → X →ₗ[ℝ] ℝ} {c : ι → ℝ} {s : Finset ι}
    (hs : (affinePatterns v c).Shatters s) : s.card ≤ Module.finrank ℝ X := by
  have hli := linearIndependent_of_all_signs
    (fun i : s => v i) (fun i : s => c i) (all_signs_of_shatters hs)
  have hc := hli.fintype_card_le_finrank
  simpa using hc

lemma card_affinePatterns_le [FiniteDimensional ℝ X]
    (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ) :
    (affinePatterns v c).card ≤
      ∑ k ∈ Finset.Iic (Module.finrank ℝ X), (Fintype.card ι).choose k := by
  classical
  have hdim : (affinePatterns v c).vcDim ≤ Module.finrank ℝ X := by
    unfold Finset.vcDim
    exact Finset.sup_le (fun s hs => shatters_card_le_finrank (Finset.mem_shatterer.mp hs))
  exact (Finset.card_le_card_shatterer _).trans
    (Finset.card_shatterer_le_sum_vcDim.trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hdim)
        (fun _ _ _ => Nat.zero_le _)))

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] {r q n : ℕ}

def occurrenceMark (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) :
    Occurrence r q → Bool := Sum.elim oldMark movableMark

noncomputable def markedScore (s : ℕ) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) (o : Occurrence r q) : ℝ :=
  if occurrenceMark oldMark movableMark o then (2 : ℝ) ^ scoreExponent s time o
  else -(2 : ℝ) ^ scoreExponent s time o

lemma abs_markedScore (s : ℕ) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) (o : Occurrence r q) :
    |markedScore s time oldMark movableMark o| = (2 : ℝ) ^ scoreExponent s time o := by
  unfold markedScore
  split <;> simp [abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]

noncomputable def fixedOldScore (s : ℕ) (oldMark : Fin r → Bool) (i : Fin r) : ℝ :=
  if oldMark i then (2 : ℝ)^((s+1)*(i.val+1)) else -(2 : ℝ)^((s+1)*(i.val+1))

noncomputable def constantScore (s : ℕ) (oldMark : Fin r → Bool) : Occurrence r q → ℝ :=
  Sum.elim (fixedOldScore s oldMark) (fun _ => 0)

noncomputable def coordinateScore : Occurrence r q → ((Fin q → ℝ) →ₗ[ℝ] ℝ) :=
  Sum.elim (fun _ => 0) (fun i => LinearMap.proj i)

noncomputable def patternLinear (M : Matroid α) (label : Occurrence r q → α)
    (J : Finset (Occurrence r q)) (e : α) : (Fin q → ℝ) →ₗ[ℝ] ℝ :=
  ∑ o ∈ occurrenceSupport M label J e, coordinateScore o

noncomputable def patternConstant (M : Matroid α) (label : Occurrence r q → α)
    (J : Finset (Occurrence r q)) (e : α) (s : ℕ) (oldMark : Fin r → Bool) : ℝ :=
  ∑ o ∈ occurrenceSupport M label J e, constantScore s oldMark o

lemma affineScore_eq_sum
    {α : Type u_1} [Fintype α] {r : ℕ} {q : ℕ} (M : Matroid α) (label : Occurrence r q → α)
    (J : Finset (Occurrence r q)) (e : α) (s : ℕ) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) :
    patternLinear M label J e (fun i => markedScore s time oldMark movableMark (Sum.inr i)) +
      patternConstant M label J e s oldMark =
      ∑ o ∈ occurrenceSupport M label J e, markedScore s time oldMark movableMark o := by
  simp only [patternLinear, patternConstant, LinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro o _
  cases o <;> simp [coordinateScore, constantScore, fixedOldScore, markedScore,
    occurrenceMark, scoreExponent]
  all_goals rfl

def RecordsPivots (M : Matroid α) (label : Occurrence r q → α)
    (test : Fin n → α) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) (t : Finset (Fin n)) : Prop :=
  ∀ f, ∃ o, IsPivot M label time (test f) o ∧
    (occurrenceMark oldMark movableMark o = true ↔ f ∈ t)

lemma recordsPivots_affine (M : Matroid α) (b : ℕ → α) (a : Fin q → α)
    (test : Fin n → α) (s : ℕ) (hqs : q ≤ s)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool)
    (time : Occurrence r q → ℕ) (horder : OldOrdered time) (htime : Function.Injective time)
    (hground : ∀ o : Occurrence r q, occurrenceLabel b a o ∈ M.E) (t : Finset (Fin n))
    (hrecords : RecordsPivots M (occurrenceLabel b a) test time oldMark movableMark t) :
    ∃ x, RealizesSigns
      (fun f => patternLinear M (occurrenceLabel b a) (retained M b a time) (test f))
      (fun f => patternConstant M (occurrenceLabel b a) (retained M b a time) (test f) s oldMark)
      t x := by
  classical
  let label : Occurrence r q → α := occurrenceLabel b a
  let J := retained M b a time
  let w := markedScore s time oldMark movableMark
  let exponent := scoreExponent s time
  refine ⟨fun i => w (Sum.inr i), ?_⟩
  intro f
  rw [affineScore_eq_sum]
  obtain ⟨o, hpivot, hmark⟩ := hrecords f
  have hp := pivot_mem_support_and_max M label time hground htime hpivot
  change o ∈ occurrenceSupport M label J (test f) ∧
    (∀ p ∈ occurrenceSupport M label J (test f), time p ≤ time o) at hp
  have hmax : ∀ p ∈ occurrenceSupport M label J (test f), p ≠ o → exponent p < exponent o := by
    intro p hp' hne
    apply scoreExponent_preserves_order s hqs time horder
    exact lt_of_le_of_ne (hp.2 p hp') (fun heq => hne (htime heq))
  have hexp := scoreExponent_injective s hqs time horder htime
  have habs : ∀ p ∈ occurrenceSupport M label J (test f), |w p| = 2 ^ exponent p :=
    fun p _ => abs_markedScore s time oldMark movableMark p
  have hpos := sum_positive_iff_max_exponent _ w exponent hexp hp.1 hmax habs
  have hneg := sum_positive_iff_max_exponent _ (fun p => -w p) exponent hexp hp.1 hmax
    (by intro p hp'; simpa using habs p hp')
  simp only [Finset.sum_neg_distrib, neg_pos] at hneg
  have hpow : (0 : ℝ) < 2 ^ exponent o := pow_pos (by norm_num) _
  by_cases hf : f ∈ t
  · simp only [hf, ↓reduceIte]
    apply hpos.mpr
    have hm := hmark.mpr hf
    simp [w, markedScore, hm]
  · simp only [hf, ↓reduceIte]
    apply hneg.mpr
    have hm : occurrenceMark oldMark movableMark o = false := by
      cases h : occurrenceMark oldMark movableMark o
      · rfl
      · exact False.elim (hf (hmark.mp h))
    simp [w, markedScore, hm]

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] {r q n : ℕ}

noncomputable def markedPivotPatterns (M : Matroid α) (b : ℕ → α) (a : Fin q → α)
    (test : Fin n → α) (oldMark : Fin r → Bool) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (fun t => ∃ time : Occurrence r q → ℕ,
    OldOrdered time ∧ Function.Injective time ∧ ∃ movableMark : Fin q → Bool,
      RecordsPivots M (occurrenceLabel b a) test time oldMark movableMark t)

lemma card_markedPivotPatterns_le (M : Matroid α) (b : ℕ → α) (a : Fin q → α)
    (test : Fin n → α) (oldMark : Fin r → Bool) (s : ℕ) (hqs : q ≤ s)
    (hground : ∀ o : Occurrence r q, occurrenceLabel b a o ∈ M.E) :
    (markedPivotPatterns M b a test oldMark).card ≤
      4 ^ s * ∑ k ∈ Finset.Iic s, n.choose k := by
  classical
  let family := retainedFamily (r := r) M b a
  let affine := fun J : Finset (Occurrence r q) => affinePatterns
    (fun f : Fin n => patternLinear M (occurrenceLabel b a) J (test f))
    (fun f : Fin n => patternConstant M (occurrenceLabel b a) J (test f) s oldMark)
  have hsub : markedPivotPatterns M b a test oldMark ⊆ family.biUnion affine := by
    intro t ht
    obtain ⟨time, horder, htime, movableMark, hrecords⟩ := (Finset.mem_filter.mp ht).2
    apply Finset.mem_biUnion.mpr
    refine ⟨retained M b a time, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, time, horder, rfl⟩
    · apply mem_affinePatterns.mpr
      exact recordsPivots_affine M b a test s hqs oldMark movableMark time horder htime hground t hrecords
  have hcard (J : Finset (Occurrence r q)) :
      (affine J).card ≤ ∑ k ∈ Finset.Iic q, n.choose k := by
    simpa [affine] using card_affinePatterns_le
      (fun f : Fin n => patternLinear M (occurrenceLabel b a) J (test f))
      (fun f : Fin n => patternConstant M (occurrenceLabel b a) J (test f) s oldMark)
  have hfamily : family.card ≤ 4 ^ s :=
    (card_retainedFamily_arbitrary_old M b a
      (fun k hk => hground (Sum.inl ⟨k, hk⟩))).trans
      (Nat.pow_le_pow_right (by decide) hqs)
  have hsum : (∑ k ∈ Finset.Iic q, n.choose k) ≤ ∑ k ∈ Finset.Iic s, n.choose k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hqs) (fun _ _ _ => Nat.zero_le _)
  calc
    (markedPivotPatterns M b a test oldMark).card ≤ (family.biUnion affine).card := Finset.card_le_card hsub
    _ ≤ ∑ J ∈ family, (affine J).card := Finset.card_biUnion_le
    _ ≤ ∑ _J ∈ family, ∑ k ∈ Finset.Iic q, n.choose k := Finset.sum_le_sum (fun J _ => hcard J)
    _ = family.card * (∑ k ∈ Finset.Iic q, n.choose k) := by simp
    _ ≤ 4 ^ s * ∑ k ∈ Finset.Iic s, n.choose k := Nat.mul_le_mul hfamily hsum

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α β : Type*} [Fintype β] [DecidableEq β]

lemma exists_pivot
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β]
    (M : Matroid α) (label : β → α) (time : β → ℕ) {e : α}
    (hnonloop : e ∉ M.closure ∅) (hspan : e ∈ M.closure (Set.range label)) :
    ∃ o, IsPivot M label time e o := by
  classical
  let P := fun k => e ∈ M.closure (label '' {o | time o ≤ k})
  have hex : ∃ k, P k := by
    refine ⟨Finset.univ.sup time, M.closure_subset_closure ?_ hspan⟩
    rintro _ ⟨o, rfl⟩
    exact ⟨o, by
      change time o ≤ Finset.univ.sup time
      exact Finset.le_sup (Finset.mem_univ o), rfl⟩
  let k := Nat.find hex
  have hk : P k := Nat.find_spec hex
  have hnot : e ∉ M.closure (label '' {o | time o < k}) := by
    intro hn
    by_cases hk0 : k = 0
    · exact hnonloop (by simpa [hk0] using hn)
    have hprev : P (k - 1) := by
      apply M.closure_subset_closure ?_ hn
      rintro _ ⟨o, ho, rfl⟩
      exact ⟨o, by
        change time o ≤ k - 1
        change time o < k at ho
        omega, rfl⟩
    have hmin : k ≤ k - 1 := Nat.find_min' hex hprev
    omega
  have hat : ∃ o, time o = k := by
    by_contra h
    apply hnot
    apply M.closure_subset_closure ?_ hk
    rintro _ ⟨o, ho, rfl⟩
    refine ⟨o, ?_, rfl⟩
    have hne : time o ≠ k := fun heq => h ⟨o, heq⟩
    change time o < k
    change time o ≤ k at ho
    omega
  obtain ⟨o, ho⟩ := hat
  exact ⟨o, by simpa [IsPivot, ho] using And.intro hk hnot⟩

lemma pivot_unique
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β]
    (M : Matroid α) (label : β → α) (time : β → ℕ)
    (htime : Function.Injective time) {e : α} {o p : β}
    (ho : IsPivot M label time e o) (hp : IsPivot M label time e p) : o = p := by
  apply htime
  apply le_antisymm
  · by_contra h
    apply ho.2
    apply M.closure_subset_closure ?_ hp.1
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, lt_of_le_of_lt ha (Nat.lt_of_not_ge h), rfl⟩
  · by_contra h
    apply hp.2
    apply M.closure_subset_closure ?_ ho.1
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, lt_of_le_of_lt ha (Nat.lt_of_not_ge h), rfl⟩

lemma existsUnique_pivot (M : Matroid α) (label : β → α) (time : β → ℕ)
    (htime : Function.Injective time) {e : α}
    (hnonloop : e ∉ M.closure ∅) (hspan : e ∈ M.closure (Set.range label)) :
    ∃! o, IsPivot M label time e o := by
  obtain ⟨o, ho⟩ := exists_pivot M label time hnonloop hspan
  exact ⟨o, ho, fun p hp => pivot_unique M label time htime hp ho⟩

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α : Type*} [Fintype α] {r q n : ℕ}

lemma recordsPivots_exists
    {α : Type u_1} [Fintype α] {r : ℕ} {q : ℕ} {n : ℕ} (M : Matroid α) (label : Occurrence r q → α)
    (test : Fin n → α) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool)
    (hnonloop : ∀ f, test f ∉ M.closure ∅)
    (hspan : ∀ f, test f ∈ M.closure (Set.range label)) :
    ∃ t, RecordsPivots M label test time oldMark movableMark t := by
  classical
  choose pivot hpivot using fun f => exists_pivot M label time (hnonloop f) (hspan f)
  refine ⟨Finset.univ.filter (fun f => occurrenceMark oldMark movableMark (pivot f) = true), ?_⟩
  intro f
  exact ⟨pivot f, hpivot f, by simp⟩

lemma recorded_pattern_exists_of_old_spanning (M : Matroid α) (b : ℕ → α) (a : Fin q → α)
    (test : Fin n → α) (oldMark : Fin r → Bool)
    (holdspan : M.closure (oldPrefix b r) = M.E)
    (htest : ∀ f, test f ∈ M.E ∧ test f ∉ M.closure ∅)
    (time : Occurrence r q → ℕ) (horder : OldOrdered time) (htime : Function.Injective time)
    (movableMark : Fin q → Bool) :
    ∃ t ∈ markedPivotPatterns M b a test oldMark,
      RecordsPivots M (occurrenceLabel b a) test time oldMark movableMark t := by
  classical
  have hspan : ∀ f, test f ∈ M.closure (Set.range (occurrenceLabel (r := r) b a)) := by
    intro f
    have htest' : test f ∈ M.closure (oldPrefix b r) := holdspan.symm ▸ (htest f).1
    apply M.closure_subset_closure ?_ htest'
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨Sum.inl ⟨k, hk⟩, rfl⟩
  obtain ⟨t, ht⟩ := recordsPivots_exists M (occurrenceLabel b a) test time oldMark movableMark
    (fun f => (htest f).2) hspan
  exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, time, horder, htime, movableMark, ht⟩, ht⟩

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α β γ O A : Type*} [Fintype α]

lemma isPivot_reindex
    {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype α]
    (M : Matroid α) (label : β → α) (time : β → ℕ)
    (e : γ ≃ β) (f : α) (o : γ) :
    IsPivot M (label ∘ e) (time ∘ e) f o ↔ IsPivot M label time f (e o) := by
  have himage (p : β → Prop) : (label ∘ e) '' {x | p (e x)} = label '' {x | p x} := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e.symm x, by simpa using hx, by simp⟩
  unfold IsPivot
  simp only [Function.comp_apply] at himage ⊢
  rw [himage (fun x => time x ≤ time (e o)), himage (fun x => time x < time (e o))]

noncomputable def freeMarkedPatterns [Fintype O] [LinearOrder O] [Fintype A]
    (M : Matroid α) (oldLabel : O → α) (movableLabel : A → α)
    {n : ℕ} (test : Fin n → α) (oldMark : O → Bool) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun t => ∃ time : O ⊕ A → ℕ,
    StrictMono (fun o => time (Sum.inl o)) ∧ Function.Injective time ∧
    ∃ mark : A → Bool, ∀ f, ∃ o,
      IsPivot M (Sum.elim oldLabel movableLabel) time (test f) o ∧
        (Sum.elim oldMark mark o = true ↔ f ∈ t)

lemma card_freeMarkedPatterns_le [Fintype O] [LinearOrder O] [Fintype A]
    (M : Matroid α) (d : α) (oldLabel : O → α) (movableLabel : A → α)
    {n : ℕ} (test : Fin n → α) (oldMark : O → Bool)
    (s : ℕ) (hs : Fintype.card A ≤ s)
    (hground : ∀ o, Sum.elim oldLabel movableLabel o ∈ M.E) :
    (freeMarkedPatterns M oldLabel movableLabel test oldMark).card ≤
      4 ^ s * ∑ k ∈ Finset.Iic s, n.choose k := by
  classical
  let eO := Fintype.orderIsoFinOfCardEq O rfl
  let eA := (Fintype.equivFin A).symm
  let e := Equiv.sumCongr eO.toEquiv eA
  let b : ℕ → α := fun k => if hk : k < Fintype.card O then oldLabel (eO ⟨k, hk⟩) else d
  let a : Fin (Fintype.card A) → α := movableLabel ∘ eA
  let m : Fin (Fintype.card O) → Bool := oldMark ∘ eO
  have hlabel : occurrenceLabel b a = Sum.elim oldLabel movableLabel ∘ e := by
    funext o
    cases o <;> simp [occurrenceLabel, b, a, e]
  have hsub : freeMarkedPatterns M oldLabel movableLabel test oldMark ⊆
      markedPivotPatterns M b a test m := by
    intro t ht
    obtain ⟨time, horder, htime, mark, hrecord⟩ := (Finset.mem_filter.mp ht).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, time ∘ e, ?_, htime.comp e.injective,
      mark ∘ eA, ?_⟩
    · intro i j hij
      exact horder (eO.strictMono hij)
    · intro f
      obtain ⟨o, hp, hm⟩ := hrecord f
      refine ⟨e.symm o, ?_, ?_⟩
      · rw [hlabel]
        exact (isPivot_reindex M (Sum.elim oldLabel movableLabel) time e (test f) (e.symm o)).2
          (by simpa using hp)
      · cases o <;> simpa [occurrenceMark, e, m, Function.comp_def] using hm
  apply (Finset.card_le_card hsub).trans
  apply card_markedPivotPatterns_le M b a test m s hs
  intro o
  rw [hlabel]
  exact hground (e o)

end MatroidProphet.Pivots

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α A T : Type*} [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]

abbrev BlockOld (F : T → Set α) :=
  {p : T ×ₗ α // (ofLex p).2 ∈ F (ofLex p).1}

noncomputable instance (F : T → Set α) : Fintype (BlockOld F) := Fintype.ofFinite _

def blockOldStage {F : T → Set α} (o : BlockOld F) : T := (ofLex o.val).1

def blockOldLabel {F : T → Set α} (o : BlockOld F) : α := (ofLex o.val).2

def blockStage (F : T → Set α) (τ : A → T) : BlockOld F ⊕ A → T :=
  Sum.elim (blockOldStage (F := F)) τ

noncomputable def blockKey (F : T → Set α) (τ : A → T) :
    BlockOld F ⊕ A → T ×ₗ (WithTop α ×ₗ ℕ)
  | Sum.inl o => toLex (blockOldStage (F := F) o, toLex ((blockOldLabel (α := α) (F := F) o : WithTop α), 0))
  | Sum.inr a => toLex (τ a, toLex (⊤, ((Fintype.equivFin A) a).val))

lemma blockKey_injective
    {α : Type u_1} {A : Type u_2} {T : Type u_3}
    [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]
    (F : T → Set α) (τ : A → T) :
    Function.Injective (blockKey F τ) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hs : blockOldStage (F := F) x = blockOldStage (F := F) y := congrArg (fun z => (ofLex z).1) h
      have hl : (blockOldLabel (α := α) (F := F) x : WithTop α) = blockOldLabel (α := α) (F := F) y :=
        congrArg (fun z => (ofLex (ofLex z).2).1) h
      have hl' : blockOldLabel (α := α) (F := F) x = blockOldLabel (α := α) (F := F) y := WithTop.coe_inj.mp hl
      have heq : x = y := Subtype.ext (congrArg toLex (Prod.ext hs hl'))
      exact congrArg Sum.inl heq
    | inr y =>
      have hh : (blockOldLabel (α := α) (F := F) x : WithTop α) = ⊤ :=
        congrArg (fun z => (ofLex (ofLex z).2).1) h
      exact (WithTop.coe_ne_top hh).elim
  | inr x =>
    cases y with
    | inl y =>
      have hh : (blockOldLabel (α := α) (F := F) y : WithTop α) = ⊤ :=
        (congrArg (fun z => (ofLex (ofLex z).2).1) h).symm
      exact (WithTop.coe_ne_top hh).elim
    | inr y =>
      have hi : ((Fintype.equivFin A) x).val = ((Fintype.equivFin A) y).val :=
        congrArg (fun z => (ofLex (ofLex z).2).2) h
      exact congrArg Sum.inr ((Fintype.equivFin A).injective (Fin.ext hi))

noncomputable def blockTime (F : T → Set α) (τ : A → T) : BlockOld F ⊕ A → ℕ := by
  letI := LinearOrder.lift' (blockKey F τ) (blockKey_injective F τ)
  exact fun o => ((Fintype.orderIsoFinOfCardEq (BlockOld F ⊕ A) rfl).symm o).val

lemma blockTime_lt_iff (F : T → Set α) (τ : A → T) (x y : BlockOld F ⊕ A) :
    blockTime F τ x < blockTime F τ y ↔ blockKey F τ x < blockKey F τ y := by
  let := LinearOrder.lift' (blockKey F τ) (blockKey_injective F τ)
  change (Fintype.orderIsoFinOfCardEq (BlockOld F ⊕ A) rfl).symm x <
    (Fintype.orderIsoFinOfCardEq (BlockOld F ⊕ A) rfl).symm y ↔ _
  exact OrderIso.lt_iff_lt _

lemma blockTime_injective (F : T → Set α) (τ : A → T) :
    Function.Injective (blockTime F τ) := by
  intro x y h
  apply blockKey_injective F τ
  apply le_antisymm <;> apply le_of_not_gt <;> intro hh
  · exact (lt_irrefl _ (h ▸ (blockTime_lt_iff F τ y x).2 hh))
  · exact (lt_irrefl _ (h ▸ (blockTime_lt_iff F τ x y).2 hh))

lemma blockTime_old_strictMono (F : T → Set α) (τ : A → T) :
    StrictMono (fun o : BlockOld F => blockTime F τ (Sum.inl o)) := by
  intro x y hxy
  apply (blockTime_lt_iff F τ _ _).2
  change toLex (blockOldStage (F := F) x, toLex ((blockOldLabel (α := α) (F := F) x : WithTop α), 0)) <
    toLex (blockOldStage (F := F) y, toLex ((blockOldLabel (α := α) (F := F) y : WithTop α), 0))
  have hh : x.val < y.val := hxy
  rcases Prod.Lex.toLex_lt_toLex.mp hh with hs | ⟨hs, hl⟩
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hs)
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hs,
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl (WithTop.coe_lt_coe.mpr hl))⟩)

lemma stage_lt_implies_blockTime_lt (F : T → Set α) (τ : A → T)
    {x y : BlockOld F ⊕ A} (h : blockStage F τ x < blockStage F τ y) :
    blockTime F τ x < blockTime F τ y := by
  apply (blockTime_lt_iff F τ _ _).2
  apply Prod.Lex.toLex_lt_toLex.mpr
  left
  cases x <;> cases y <;> exact h

lemma blockTime_le_implies_stage_le (F : T → Set α) (τ : A → T)
    {x y : BlockOld F ⊕ A} (h : blockTime F τ x ≤ blockTime F τ y) :
    blockStage F τ x ≤ blockStage F τ y := by
  by_contra hh
  exact (not_lt_of_ge h) (stage_lt_implies_blockTime_lt F τ (lt_of_not_ge hh))

end MatroidProphet.Pivots

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α A T : Type*} [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T] {n : ℕ}

def blockLabel (F : T → Set α) (a : A → α) : BlockOld F ⊕ A → α :=
  Sum.elim (blockOldLabel (F := F)) a

def blockPrefix (F : T → Set α) (a : A → α) (τ : A → T) (k : T) : Set α :=
  blockLabel F a '' {o | blockStage F τ o ≤ k}

def blockBefore (F : T → Set α) (a : A → α) (τ : A → T) (k : T) : Set α :=
  blockLabel F a '' {o | blockStage F τ o < k}

noncomputable def blockBirthPattern (M : Matroid α) (F : T → Set α)
    (a : A → α) (τ : A → T) (test : Fin n → α) (mark : T → Bool) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => ∃ k, mark k = true ∧
    test f ∈ M.closure (blockPrefix F a τ k) ∧ test f ∉ M.closure (blockBefore F a τ k)

lemma pivot_block_birth (M : Matroid α) (F : T → Set α) (a : A → α)
    (τ : A → T) {e : α} {o : BlockOld F ⊕ A}
    (hp : IsPivot M (blockLabel F a) (blockTime F τ) e o) :
    e ∈ M.closure (blockPrefix F a τ (blockStage F τ o)) ∧
      e ∉ M.closure (blockBefore F a τ (blockStage F τ o)) := by
  constructor
  · apply M.closure_subset_closure (Set.image_mono ?_) hp.1
    exact fun p h => blockTime_le_implies_stage_le F τ h
  · intro h
    apply hp.2
    apply M.closure_subset_closure (Set.image_mono ?_) h
    exact fun p h => stage_lt_implies_blockTime_lt F τ h

lemma block_birth_unique
    {α : Type u_1} {A : Type u_2} {T : Type u_3}
    [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]
    (M : Matroid α) (F : T → Set α) (a : A → α)
    (τ : A → T) {e : α} {k l : T}
    (hk : e ∈ M.closure (blockPrefix F a τ k) ∧ e ∉ M.closure (blockBefore F a τ k))
    (hl : e ∈ M.closure (blockPrefix F a τ l) ∧ e ∉ M.closure (blockBefore F a τ l)) :
    k = l := by
  rcases lt_trichotomy k l with h | rfl | h
  · exact (hl.2 (M.closure_subset_closure (Set.image_mono (fun _ hx => lt_of_le_of_lt hx h)) hk.1)).elim
  · rfl
  · exact (hk.2 (M.closure_subset_closure (Set.image_mono (fun _ hx => lt_of_le_of_lt hx h)) hl.1)).elim

lemma blockBirthPattern_mem_freeMarkedPatterns (M : Matroid α) (F : T → Set α)
    (a : A → α) (τ : A → T) (test : Fin n → α) (mark : T → Bool)
    (hnonloop : ∀ f, test f ∉ M.closure ∅)
    (hspan : ∀ f, test f ∈ M.closure (Set.range (blockLabel F a))) :
    blockBirthPattern M F a τ test mark ∈
      freeMarkedPatterns M (blockOldLabel (F := F)) a test (fun o : BlockOld F => mark (blockOldStage (F := F) o)) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, blockTime F τ, blockTime_old_strictMono F τ,
    blockTime_injective F τ, mark ∘ τ, ?_⟩
  intro f
  obtain ⟨o, hp⟩ := exists_pivot M (blockLabel F a) (blockTime F τ) (hnonloop f) (hspan f)
  refine ⟨o, hp, ?_⟩
  have hb := pivot_block_birth M F a τ hp
  change Sum.elim (fun o : BlockOld F => mark (blockOldStage (F := F) o)) (mark ∘ τ) o = true ↔ _
  have hm : Sum.elim (fun o : BlockOld F => mark (blockOldStage (F := F) o)) (mark ∘ τ) o =
      mark (blockStage F τ o) := by cases o <;> rfl
  rw [hm]
  simp only [blockBirthPattern, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨blockStage F τ o, h, hb⟩
  · rintro ⟨k, hmark, hk⟩
    have heq := block_birth_unique M F a τ hb hk
    simpa only [heq] using hmark

lemma blockPrefix_eq
    {α : Type u_1} {A : Type u_2} {T : Type u_3}
    [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]
    (F : T → Set α) (hF : Monotone F)
    (a : A → α) (τ : A → T) (k : T) :
    blockPrefix F a τ k = F k ∪ a '' {g | τ g ≤ k} := by
  ext e
  constructor
  · rintro ⟨o, ho, rfl⟩
    cases o with
    | inl o => exact Or.inl (hF ho o.property)
    | inr g => exact Or.inr ⟨g, ho, rfl⟩
  · rintro (he | ⟨g, hg, rfl⟩)
    · exact ⟨Sum.inl ⟨toLex (k, e), he⟩, by change k ≤ k; exact le_rfl, rfl⟩
    · exact ⟨Sum.inr g, hg, rfl⟩

lemma blockBefore_eq_iUnion
    {α : Type u_1} {A : Type u_2} {T : Type u_3}
    [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]
    (F : T → Set α) (a : A → α) (τ : A → T)
    (k : T) :
    blockBefore F a τ k = (⋃ j : T, ⋃ (_ : j < k), F j) ∪ a '' {g | τ g < k} := by
  ext e
  constructor
  · rintro ⟨o, ho, rfl⟩
    cases o with
    | inl o => exact Or.inl (mem_iUnion.mpr ⟨blockOldStage (F := F) o, mem_iUnion.mpr ⟨ho, o.property⟩⟩)
    | inr g => exact Or.inr ⟨g, ho, rfl⟩
  · rintro (he | ⟨g, hg, rfl⟩)
    · obtain ⟨j, hj, he⟩ := mem_iUnion.mp he |>.imp fun _ h => mem_iUnion.mp h
      exact ⟨Sum.inl ⟨toLex (j, e), he⟩, hj, rfl⟩
    · exact ⟨Sum.inr g, hg, rfl⟩

end MatroidProphet.Pivots

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.Pivots

open Set

variable {α G Z B : Type*} [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z]
    [Fintype B] [LinearOrder B]

def phaseOld (F K : B → Set α) (p : B ×ₗ Bool) : Set α :=
  if (ofLex p).2 then F (ofLex p).1 else K (ofLex p).1

def phasePlacement (θ : G → B) (β : Z → B) : G ⊕ Z → B ×ₗ Bool :=
  Sum.elim (fun g => toLex (θ g, true)) (fun z => toLex (β z, false))

def upperPath (M : Matroid α) (F : B → Set α) (a : G → α) (θ : G → B) (b : B) : Set α :=
  M.closure (F b ∪ a '' {g | θ g ≤ b})

def lowerPath (M : Matroid α) (F : B → Set α) (a : G → α) (θ : G → B) (b : B) : Set α :=
  M.closure ((⋃ c, ⋃ (_ : c < b), F c) ∪ a '' {g | θ g < b})

lemma upperPath_mono
    {α : Type u_1} {G : Type u_2} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype B] [LinearOrder B]
    (M : Matroid α) (F : B → Set α) (hF : Monotone F)
    (a : G → α) (θ : G → B) : Monotone (upperPath M F a θ) := by
  intro b c hbc
  exact M.closure_subset_closure (union_subset_union (hF hbc)
    (image_mono (fun _ hx => hx.trans hbc)))

lemma upperPath_subset_lowerPath
    {α : Type u_1} {G : Type u_2} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype B] [LinearOrder B]
    (M : Matroid α) (F : B → Set α)
    (a : G → α) (θ : G → B) {b c : B} (hbc : b < c) :
    upperPath M F a θ b ⊆ lowerPath M F a θ c := by
  apply M.closure_subset_closure
  apply union_subset_union
  · exact fun e he => mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hbc, he⟩⟩
  · exact image_mono (fun _ hx => lt_of_le_of_lt hx hbc)

lemma phase_prefix_end_eq
    {α : Type u_1} {G : Type u_2} {Z : Type u_3} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z] [Fintype B] [LinearOrder B]
    (F K : B → Set α) (hF : Monotone F) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B) (b : B) :
    blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, true)) =
      (F b ∪ a '' {g | θ g ≤ b}) ∪ z '' {w | β w ≤ b} := by
  ext e
  constructor
  · rintro ⟨o, ho, rfl⟩
    cases o with
    | inl o =>
      have hc : (ofLex (blockOldStage (F := phaseOld F K) o)).1 ≤ b := by
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        exact ht.elim le_of_lt (fun h => h.1.le)
      have hl : blockOldLabel (F := phaseOld F K) o ∈ F (ofLex (blockOldStage (F := phaseOld F K) o)).1 := by
        have hp := o.property
        change blockOldLabel (F := phaseOld F K) o ∈ phaseOld F K (blockOldStage (F := phaseOld F K) o) at hp
        unfold phaseOld at hp
        split at hp
        · exact hp
        · exact hK _ hp
      exact Or.inl (Or.inl (hF hc hl))
    | inr o =>
      cases o with
      | inl g =>
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        exact Or.inl (Or.inr ⟨g, ht.elim le_of_lt (fun h => h.1.le), rfl⟩)
      | inr w =>
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        exact Or.inr ⟨w, ht.elim le_of_lt (fun h => h.1.le), rfl⟩
  · rintro ((he | ⟨g, hg, rfl⟩) | ⟨w, hw, rfl⟩)
    · refine ⟨Sum.inl ⟨toLex (toLex (b, true), e), he⟩, ?_, rfl⟩
      change toLex (b, true) ≤ toLex (b, true)
      exact le_rfl
    · refine ⟨Sum.inr (Sum.inl g), ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr ((lt_or_eq_of_le hg).imp id (fun h => ⟨h, le_rfl⟩))
    · refine ⟨Sum.inr (Sum.inr w), ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr ((lt_or_eq_of_le hw).imp id (fun h => ⟨h, show (false : Bool) ≤ true from by decide⟩))

lemma phase_endpoint (M : Matroid α) (hE : M.E = univ)
    (F K : B → Set α) (hF : Monotone F) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B)
    (hz : ∀ w, z w ∈ upperPath M F a θ (β w)) (b : B) :
    M.closure (blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, true))) =
      upperPath M F a θ b := by
  rw [phase_prefix_end_eq F K hF hK]
  apply Subset.antisymm
  · apply (M.closure_subset_closure ?_).trans_eq (M.closure_closure _)
    apply union_subset
    · exact M.subset_closure _ (by simp [hE])
    · rintro _ ⟨w, hw, rfl⟩
      exact upperPath_mono M F hF a θ hw (hz w)
  · exact M.closure_subset_closure subset_union_left

lemma phase_prefix_interior_eq
    {α : Type u_1} {G : Type u_2} {Z : Type u_3} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z] [Fintype B] [LinearOrder B]
    (F K : B → Set α) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B) (b : B) :
    blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, false)) =
      (((⋃ c, ⋃ (_ : c < b), F c) ∪ a '' {g | θ g < b}) ∪ K b) ∪ z '' {w | β w ≤ b} := by
  ext e
  constructor
  · rintro ⟨o, ho, rfl⟩
    cases o with
    | inl o =>
      have ht := Prod.Lex.toLex_le_toLex.mp ho
      have hp := o.property
      change blockOldLabel (F := phaseOld F K) o ∈ phaseOld F K (blockOldStage (F := phaseOld F K) o) at hp
      rcases ht with hc | ⟨hc, hb⟩
      · left; left; left
        refine mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨hc, ?_⟩⟩
        unfold phaseOld at hp
        split at hp
        · exact hp
        · exact hK _ hp
      · left; right
        have hf : (ofLex (blockOldStage (F := phaseOld F K) o)).2 = false := by
          change (ofLex (blockOldStage (F := phaseOld F K) o)).2 ≤ false at hb
          exact le_antisymm hb bot_le
        change (ofLex (blockOldStage (F := phaseOld F K) o)).1 = b at hc
        change blockOldLabel (F := phaseOld F K) o ∈ K b
        simpa [phaseOld, hf, hc] using hp
    | inr o =>
      cases o with
      | inl g =>
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        have hg : θ g < b := ht.elim id (fun h => by have hh : false = true := h.2 rfl; cases hh)
        exact Or.inl (Or.inl (Or.inr ⟨g, hg, rfl⟩))
      | inr w =>
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        exact Or.inr ⟨w, ht.elim le_of_lt (fun h => h.1.le), rfl⟩
  · rintro (((he | ⟨g, hg, rfl⟩) | hk) | ⟨w, hw, rfl⟩)
    · obtain ⟨c, hc, he⟩ := mem_iUnion.mp he |>.imp fun _ h => mem_iUnion.mp h
      refine ⟨Sum.inl ⟨toLex (toLex (c, true), e), he⟩, ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inl hc)
    · refine ⟨Sum.inr (Sum.inl g), ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inl hg)
    · refine ⟨Sum.inl ⟨toLex (toLex (b, false), e), hk⟩, ?_, rfl⟩
      change toLex (b, false) ≤ toLex (b, false)
      exact le_rfl
    · refine ⟨Sum.inr (Sum.inr w), ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr ((lt_or_eq_of_le hw).imp id (fun h => ⟨h, le_rfl⟩))

lemma phase_interior (M : Matroid α) (hE : M.E = univ)
    (F K : B → Set α) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B)
    (hz : ∀ w, z w ∈ upperPath M F a θ (β w)) (b : B) :
    M.closure (blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, false))) =
      M.closure (lowerPath M F a θ b ∪ K b ∪ z '' {w | β w = b}) := by
  rw [phase_prefix_interior_eq F K hK]
  apply Subset.antisymm
  · apply (M.closure_subset_closure ?_).trans_eq (M.closure_closure _)
    rintro e ((he | hk) | ⟨w, hw, rfl⟩)
    · apply M.subset_closure _ (by simp [hE])
      exact Or.inl (Or.inl (M.subset_closure _ (by simp [hE]) he))
    · exact M.subset_closure _ (by simp [hE]) (Or.inl (Or.inr hk))
    · rcases lt_or_eq_of_le hw with hw | hw
      · apply M.subset_closure _ (by simp [hE])
        exact Or.inl (Or.inl (upperPath_subset_lowerPath M F a θ hw (hz w)))
      · exact M.subset_closure _ (by simp [hE]) (Or.inr ⟨w, hw, rfl⟩)
  · rw [union_assoc (lowerPath M F a θ b), lowerPath, M.closure_union_closure_left_eq, ← union_assoc]
    apply M.closure_subset_closure
    exact union_subset_union Subset.rfl (image_mono (fun _ h => h.le))

end MatroidProphet.Pivots

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Pivots

open Set

abbrev IntWindow (a : ℤ) := {k : ℤ // k ∈ Set.Icc (a - 2) 1}

noncomputable instance (a : ℤ) : Fintype (IntWindow a) := Fintype.ofFinite _

abbrev ParityWindow (a : ℤ) (ε : Fin 2) := {k : IntWindow a // k.val % 2 = (ε.val : ℤ)}

noncomputable instance (a : ℤ) (ε : Fin 2) : Fintype (ParityWindow a ε) := Fintype.ofFinite _

def roundParity (ε : Fin 2) (k : ℤ) : ℤ := if k % 2 = (ε.val : ℤ) then k else k + 1

lemma roundParity_bounds (ε : Fin 2) (k : ℤ) : k ≤ roundParity ε k ∧ roundParity ε k ≤ k + 1 := by
  unfold roundParity
  split <;> omega

lemma roundParity_mod (ε : Fin 2) (k : ℤ) : roundParity ε k % 2 = (ε.val : ℤ) := by
  have hε := ε.isLt
  unfold roundParity
  split <;> omega

lemma roundParity_le_iff (ε : Fin 2) (k b : ℤ) (hb : b % 2 = (ε.val : ℤ)) :
    roundParity ε k ≤ b ↔ k ≤ b := by
  have hε := ε.isLt
  unfold roundParity
  split <;> omega

lemma roundParity_lt_iff (ε : Fin 2) (k b : ℤ) (hb : b % 2 = (ε.val : ℤ)) :
    roundParity ε k < b ↔ k ≤ b - 2 := by
  have hε := ε.isLt
  unfold roundParity
  split <;> omega

variable {α G : Type*} [Fintype α] [LinearOrder α] [Fintype G]

def windowPlacement (a : ℤ) (ν : G → ℤ) (hν : ∀ g, a ≤ ν g ∧ ν g ≤ 0) : G → IntWindow a :=
  fun g => ⟨ν g, by have := hν g; constructor <;> omega⟩

def parityPlacement (a : ℤ) (ε : Fin 2) (ν : G → ℤ)
    (hν : ∀ g, a ≤ ν g ∧ ν g ≤ 0) : G → ParityWindow a ε :=
  fun g => ⟨⟨roundParity ε (ν g), by
    have := hν g
    have := roundParity_bounds ε (ν g)
    constructor <;> omega⟩, roundParity_mod ε (ν g)⟩

def generatedPath (M : Matroid α) (F : ℤ → Set α) (g : G → α) (ν : G → ℤ) (k : ℤ) : Set α :=
  M.closure (F k ∪ g '' {i | ν i ≤ k})

lemma window_prefix (M : Matroid α) (F : ℤ → Set α) (hF : Monotone F)
    (a : ℤ) (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (k : IntWindow a) :
    M.closure (blockPrefix (fun t : IntWindow a => F t.val) g (windowPlacement a ν hν) k) =
      generatedPath M F g ν k.val := by
  rw [blockPrefix_eq (fun t : IntWindow a => F t.val) (fun _ _ h => hF h)]
  rfl

lemma parity_upperPath
    {α : Type u_1} {G : Type u_2} [Fintype α] [LinearOrder α] [Fintype G]
    (M : Matroid α) (F : ℤ → Set α) (a : ℤ) (ε : Fin 2)
    (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (b : ParityWindow a ε) :
    upperPath M (fun t : ParityWindow a ε => F t.val.val) g (parityPlacement a ε ν hν) b =
      generatedPath M F g ν b.val.val := by
  have hs : {i | parityPlacement a ε ν hν i ≤ b} = {i | ν i ≤ b.val.val} := by
    ext i
    exact roundParity_le_iff ε (ν i) b.val.val b.property
  unfold upperPath generatedPath
  rw [hs]

lemma parity_lowerPath
    {α : Type u_1} {G : Type u_2} [Fintype α] [LinearOrder α] [Fintype G]
    (M : Matroid α) (hE : M.E = univ)
    (F : ℤ → Set α) (hF : Monotone F) (a : ℤ)
    (hFe : ∀ k < a, F k = M.closure ∅) (ε : Fin 2)
    (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (b : ParityWindow a ε) :
    lowerPath M (fun t : ParityWindow a ε => F t.val.val) g (parityPlacement a ε ν hν) b =
      generatedPath M F g ν (b.val.val - 2) := by
  have hgen : g '' {i | parityPlacement a ε ν hν i < b} = g '' {i | ν i ≤ b.val.val - 2} := by
    congr 1
    ext i
    exact roundParity_lt_iff ε (ν i) b.val.val b.property
  unfold lowerPath generatedPath
  rw [hgen]
  apply Subset.antisymm
  · apply M.closure_subset_closure
    apply union_subset_union _ Subset.rfl
    intro e he
    obtain ⟨c, hc, he⟩ := mem_iUnion.mp he |>.imp fun _ h => mem_iUnion.mp h
    have hcb : c.val.val ≤ b.val.val - 2 := by
      have hb := b.property
      have hcmod := c.property
      change c.val.val < b.val.val at hc
      omega
    exact hF hcb he
  · apply (M.closure_subset_closure ?_).trans_eq (M.closure_closure _)
    apply union_subset
    · intro e he
      by_cases hlo : a - 2 ≤ b.val.val - 2
      · let c : ParityWindow a ε := ⟨⟨b.val.val - 2, ⟨hlo, by have := b.val.property.2; omega⟩⟩,
          by change (b.val.val - 2) % 2 = (ε.val : ℤ); have := b.property; omega⟩
        apply M.subset_closure _ (by simp [hE])
        left
        refine mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨?_, he⟩⟩
        change b.val.val - 2 < b.val.val
        omega
      · have hearly : b.val.val - 2 < a := by omega
        rw [hFe _ hearly] at he
        exact M.closure_subset_closure (empty_subset _) he
    · exact (subset_union_right.trans (M.subset_closure _ (by simp [hE])))

lemma window_before (M : Matroid α) (hE : M.E = univ)
    (F : ℤ → Set α) (hF : Monotone F) (a : ℤ)
    (hFe : ∀ k < a, F k = M.closure ∅)
    (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (k : IntWindow a) :
    M.closure (blockBefore (fun t : IntWindow a => F t.val) g (windowPlacement a ν hν) k) =
      generatedPath M F g ν (k.val - 1) := by
  rw [blockBefore_eq_iUnion]
  have hgen : g '' {i | windowPlacement a ν hν i < k} = g '' {i | ν i ≤ k.val - 1} := by
    congr 1
    ext i
    change ν i < k.val ↔ ν i ≤ k.val - 1
    omega
  rw [hgen]
  unfold generatedPath
  apply Subset.antisymm
  · apply M.closure_subset_closure
    apply union_subset_union _ Subset.rfl
    intro e he
    obtain ⟨c, hc, he⟩ := mem_iUnion.mp he |>.imp fun _ h => mem_iUnion.mp h
    apply hF (show c.val ≤ k.val - 1 from by change c.val < k.val at hc; omega) he
  · apply (M.closure_subset_closure ?_).trans_eq (M.closure_closure _)
    apply union_subset
    · intro e he
      by_cases hlo : a - 2 ≤ k.val - 1
      · let c : IntWindow a := ⟨k.val - 1, ⟨hlo, by have := k.property.2; omega⟩⟩
        apply M.subset_closure _ (by simp [hE])
        left
        refine mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨?_, he⟩⟩
        change k.val - 1 < k.val
        omega
      · have hearly : k.val - 1 < a := by omega
        rw [hFe _ hearly] at he
        exact M.closure_subset_closure (empty_subset _) he
    · exact (subset_union_right.trans (M.subset_closure _ (by simp [hE])))

end Pivots
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset

lemma sum_spaced_potential_drop (p : ℤ → ℕ) (hp : Antitone p)
    (L : Finset ℤ) (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hlo : ∀ b ∈ L, lo + 2 ≤ b) (hhi : ∀ b ∈ L, b ≤ hi)
    (hgap : ∀ b ∈ L, ∀ c ∈ L, b < c → b + 2 ≤ c) :
    (∑ b ∈ L, (p (b-2) - p b)) + p hi ≤ p lo := by
  induction L using Finset.induction_on_max generalizing lo hi with
  | empty => simpa using hp hlohi
  | @insert a L hmax ih =>
    have ha : a ∉ L := fun hm => (lt_irrefl a) (hmax a hm)
    have hla : lo ≤ a-2 := by have := hlo a (mem_insert_self a L); omega
    have harest : ∀ b ∈ L, b ≤ a-2 := by
      intro b hb
      have hb' := hmax b hb
      have hg := hgap b (mem_insert_of_mem hb) a (mem_insert_self a L) hb'
      omega
    have hrec := ih lo (a-2) hla
      (fun b hb => hlo b (mem_insert_of_mem hb)) harest
      (fun b hb c hc hbc => hgap b (mem_insert_of_mem hb) c (mem_insert_of_mem hc) hbc)
    have hahi := hhi a (mem_insert_self a L)
    have hphi := hp hahi
    have hpaa := hp (show a-2 ≤ a by omega)
    rw [sum_insert ha]
    omega

variable {α : Type*} [Fintype α]

theorem rankCost_spaced (M : Matroid α) (J : Set α) (L : Finset ℤ)
    (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hlo : ∀ b ∈ L, lo+2 ≤ b) (hhi : ∀ b ∈ L, b ≤ hi)
    (hgap : ∀ b ∈ L, ∀ c ∈ L, b < c → b+2 ≤ c)
    (X A B S : ℤ → Set α) (hX : Monotone X)
    (hXA : ∀ b ∈ L, X (b-2) ⊆ A b)
    (hAB : ∀ b ∈ L, A b ⊆ B b)
    (hB : ∀ b ∈ L, B b ⊆ M.closure (A b ∪ J))
    (hY : ∀ b ∈ L, A b ∪ S b ⊆ X b) :
    (∑ b ∈ L, conditionalRank M (S b) (A b)) ≤
      (∑ b ∈ L, conditionalRank M (S b) (B b)) + natRank M J := by
  have hp : Antitone (fun b => conditionalRank M J (X b)) :=
    fun _ _ hab => conditionalRank_antitone M J (hX hab)
  have hd := sum_spaced_potential_drop _ hp L lo hi hlohi hlo hhi hgap
  have hs : (∑ b ∈ L, conditionalRank M (S b) (A b)) ≤
      ∑ b ∈ L, (conditionalRank M (S b) (B b) +
        (conditionalRank M J (X (b-2)) - conditionalRank M J (X b))) := by
    apply sum_le_sum
    intro b hb
    have hc := rankCost_step M J (S b) (A b) (B b) (X (b-2)) (X b)
      (hXA b hb) (hAB b hb) (hB b hb) (hY b hb)
    have hm := conditionalRank_antitone M (S b) (hAB b hb)
    omega
  rw [sum_add_distrib] at hs
  have hb := conditionalRank_le_rank M J (X lo)
  omega

theorem actual_path_rank_cost_finset (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h later : ℕ)
    (L : Finset ℤ) (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hlo : ∀ b ∈ L, lo+2 ≤ b) (hhi : ∀ b ∈ L, b ≤ hi)
    (hgap : ∀ b ∈ L, ∀ c ∈ L, b < c → b+2 ≤ c)
    (S : ℤ → Set α) (hS : ∀ b, S b ⊆ nominalPath M hE κ D C h b) :
    κ * (∑ b ∈ L, conditionalRank M (S b)
      (nominalPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h)) ≤
    κ * (∑ b ∈ L, conditionalRank M (S b)
      (guardedPath M hE κ D C (h+1+later) (b-2) ∪ lowerCompetition M hE κ D C T b h)) +
      κ * (C h).ncard +
        ∑ j ∈ range later, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
  obtain ⟨J, hJcost, hJ⟩ := exists_commonPathBudget M hE κ hκ D C h later
  have hXfinal (b : ℤ) : nominalPath M hE κ D C h b ⊆
      guardedPath M hE κ D C (h+1+later) b := by
    apply (nominal_subset_guarded M hE κ D C h b).trans
    have hm : Monotone (fun j => guardedPath M hE κ D C j b) :=
      monotone_nat_of_le_succ (fun j => (guarded_subset_nominal M hE κ D C j b).trans
        (nominal_subset_guarded M hE κ D C j b))
    exact hm (by omega)
  have hr := rankCost_spaced M J L lo hi hlohi hlo hhi hgap
    (nominalPath M hE κ D C h)
    (fun b => nominalPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h)
    (fun b => guardedPath M hE κ D C (h+1+later) (b-2) ∪ lowerCompetition M hE κ D C T b h)
    S (nominalPath_mono M hE κ D C h)
    (fun _ _ => Set.subset_union_left)
    (fun b _ => Set.union_subset_union_left _ (hXfinal _))
    (by
      intro b hb
      apply Set.union_subset
      · exact (hJ _).trans (M.closure_subset_closure (by
          intro e he
          rcases he with he | he
          · exact Or.inl (Or.inl he)
          · exact Or.inr he))
      · intro e he
        exact M.mem_closure_of_mem (Or.inl (Or.inr he)) (by simp [hE]))
    (by
      intro b hb
      apply Set.union_subset
      · apply Set.union_subset
        · exact nominalPath_mono M hE κ D C h (by omega)
        · exact (lowerCompetition_subset_guarded M hE κ D C T _ h).trans
            (guarded_subset_nominal M hE κ D C h _)
      · exact hS _)
  have hmul := Nat.mul_le_mul_left κ hr
  rw [Nat.mul_add] at hmul
  have hcard := natRank_le_ncard M J
  have hbound := (Nat.mul_le_mul_left κ hcard).trans hJcost
  omega

noncomputable def parityPoints (a : ℤ) (ε : Fin 2) : Finset ℤ :=
  Finset.univ.image (fun b : Pivots.ParityWindow a ε => b.val.val)

lemma mem_parityPoints (a : ℤ) (ε : Fin 2) (b : ℤ) :
    b ∈ parityPoints a ε ↔ a-2 ≤ b ∧ b ≤ 1 ∧ b % 2 = (ε.val : ℤ) := by
  classical
  constructor
  · intro hb
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨c.val.property.1, c.val.property.2, c.property⟩
  · rintro ⟨hl, hr, hm⟩
    exact Finset.mem_image.mpr ⟨⟨⟨b, ⟨hl, hr⟩⟩, hm⟩, Finset.mem_univ _, rfl⟩

lemma sum_parityPoints {β : Type*} [AddCommMonoid β] (a : ℤ) (ε : Fin 2) (f : ℤ → β) :
    (∑ b ∈ parityPoints a ε, f b) = ∑ b : Pivots.ParityWindow a ε, f b.val.val := by
  classical
  apply Finset.sum_image
  intro x _ y _ hxy
  exact Subtype.ext (Subtype.ext hxy)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α G Z B : Type*} [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z]
    [Fintype B] [LinearOrder B] {n : ℕ}

lemma lex_lt_true_iff_le_false
    {B : Type u_4} [Fintype B] [LinearOrder B] (p : B ×ₗ Bool) (b : B) :
    p < toLex (b, true) ↔ p ≤ toLex (b, false) := by
  rw [Prod.Lex.lt_iff, Prod.Lex.le_iff]
  cases (ofLex p).2 <;> simp

lemma phase_before_true
    {α : Type u_1} {G : Type u_2} {Z : Type u_3} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z] [Fintype B] [LinearOrder B]
    (F K : B → Set α) (a : G → α) (z : Z → α)
    (θ : G → B) (β : Z → B) (b : B) :
    blockBefore (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, true)) =
      blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, false)) := by
  unfold blockBefore blockPrefix
  congr 1
  ext o
  exact lex_lt_true_iff_le_false _ _

lemma mem_phase_pattern (M : Matroid α) (hE : M.E = univ)
    (F K : B → Set α) (hF : Monotone F) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B)
    (hz : ∀ w, z w ∈ upperPath M F a θ (β w)) (test : Fin n → α) (f : Fin n) :
    f ∈ blockBirthPattern M (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) test
        (fun p => (ofLex p).2) ↔
      ∃ b, test f ∈ upperPath M F a θ b ∧
        test f ∉ M.closure (lowerPath M F a θ b ∪ K b ∪ z '' {w | β w = b}) := by
  classical
  simp only [blockBirthPattern, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, hafter, hbefore⟩
    change (ofLex p).2 = true at hp
    have hp' : p = toLex ((ofLex p).1, true) := congrArg toLex (Prod.ext rfl hp)
    rw [hp'] at hafter hbefore
    rw [phase_endpoint M hE F K hF hK a z θ β hz] at hafter
    rw [phase_before_true, phase_interior M hE F K hK a z θ β hz] at hbefore
    exact ⟨(ofLex p).1, hafter, hbefore⟩
  · rintro ⟨b, hafter, hbefore⟩
    refine ⟨toLex (b, true), rfl, ?_, ?_⟩
    · rwa [phase_endpoint M hE F K hF hK a z θ β hz]
    · rwa [phase_before_true, phase_interior M hE F K hK a z θ β hz]

noncomputable def residualOfLayers (M : Matroid α) (F K : B → Set α) (a : G → α)
    (z : Z → α) (θ : G → B) (β : Z → B) (test : Fin n → α)
    (P : B → Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => ∃ b, f ∈ P b ∧
    test f ∉ M.closure (lowerPath M F a θ b ∪ K b ∪ z '' {w | β w = b})

lemma first_inter_phase_eq_residual (M : Matroid α) (hE : M.E = univ)
    (F K : B → Set α) (hF : Monotone F) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B)
    (hz : ∀ w, z w ∈ upperPath M F a θ (β w)) (test : Fin n → α)
    (P : B → Finset (Fin n)) (first : Finset (Fin n))
    (hfirst : ∀ f, f ∈ first ↔ ∃ b, f ∈ P b)
    (hP : ∀ b f, f ∈ P b → test f ∈ upperPath M F a θ b ∧ test f ∉ lowerPath M F a θ b) :
    first ∩ blockBirthPattern M (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) test
        (fun p => (ofLex p).2) = residualOfLayers M F K a z θ β test P := by
  classical
  ext f
  rw [Finset.mem_inter, mem_phase_pattern M hE F K hF hK a z θ β hz]
  simp only [residualOfLayers, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hf, c, hc, hcnot⟩
    obtain ⟨b, hb⟩ := (hfirst f).1 hf
    have hpb := hP b f hb
    have hbc : b = c := by
      rcases lt_trichotomy b c with h | h | h
      · apply False.elim
        apply hcnot
        exact M.subset_closure _ (by simp [hE]) (Or.inl (Or.inl
          (upperPath_subset_lowerPath M F a θ h hpb.1)))
      · exact h
      · exact (hpb.2 (upperPath_subset_lowerPath M F a θ h hc)).elim
    exact ⟨b, hb, hbc.symm ▸ hcnot⟩
  · rintro ⟨b, hb, hnot⟩
    exact ⟨(hfirst f).2 ⟨b, hb⟩, b, (hP b f hb).1, hnot⟩

end MatroidProphet.Pivots

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.Pivots

open Finset

noncomputable def binomialSum (n d : ℕ) : ℕ := ∑ k ∈ Iic d, n.choose k

lemma binomialSum_le_weighted (n d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    (binomialSum n d : ℝ) ≤ κ ^ d * (1 + κ⁻¹) ^ n := by
  have hkpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have htrunc : (binomialSum n d : ℝ) = ∑ k ∈ Iic d ∩ Iic n, (n.choose k : ℝ) := by
    rw [binomialSum, Nat.cast_sum]
    apply (sum_subset inter_subset_left ?_).symm
    intro k hkd hnot
    have hnk : n < k := by simpa only [mem_inter, hkd, true_and, mem_Iic, not_le] using hnot
    simp [Nat.choose_eq_zero_of_lt hnk]
  have hp (k : ℕ) (hkd : k ≤ d) : 1 ≤ κ ^ d * (κ⁻¹) ^ k := by
    rw [inv_pow, ← div_eq_mul_inv]
    exact (one_le_div₀ (pow_pos hkpos k)).2 (pow_le_pow_right₀ hκ hkd)
  calc
    (binomialSum n d : ℝ) = ∑ k ∈ Iic d ∩ Iic n, (n.choose k : ℝ) := htrunc
    _ ≤ ∑ k ∈ Iic d ∩ Iic n, κ ^ d * ((κ⁻¹) ^ k * (n.choose k : ℝ)) := by
      apply sum_le_sum
      intro k hk
      have h := mul_le_mul_of_nonneg_right (hp k (mem_Iic.mp (mem_inter.mp hk).1))
        (Nat.cast_nonneg (n.choose k) : (0 : ℝ) ≤ n.choose k)
      simpa only [one_mul, mul_assoc] using h
    _ ≤ ∑ k ∈ Iic n, κ ^ d * ((κ⁻¹) ^ k * (n.choose k : ℝ)) :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right (by intros; positivity)
    _ = κ ^ d * (1 + κ⁻¹) ^ n := by
      rw [← mul_sum, add_comm 1, add_pow, Nat.range_succ_eq_Iic]
      simp

lemma binomialSum_le_exp (n d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    (binomialSum n d : ℝ) ≤ Real.exp ((d : ℝ) * Real.log κ + (n : ℝ) / κ) := by
  have hkpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hone : 1 + κ⁻¹ ≤ Real.exp κ⁻¹ := by simpa [add_comm] using Real.add_one_le_exp κ⁻¹
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + κ⁻¹) hone n
  calc
    (binomialSum n d : ℝ) ≤ κ ^ d * (1 + κ⁻¹) ^ n := binomialSum_le_weighted n d κ hκ
    _ ≤ κ ^ d * (Real.exp κ⁻¹) ^ n := mul_le_mul_of_nonneg_left hpow (pow_nonneg hkpos.le d)
    _ = Real.exp ((d : ℝ) * Real.log κ + (n : ℝ) / κ) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hkpos, div_eq_mul_inv, Real.exp_nat_mul]

lemma residual_raw_count_le_exp (n q : ℕ) (κ : ℝ) (hκ : 2 ≤ κ)
    (hq : (q : ℝ) ≤ (n : ℝ) / κ) :
    (((binomialSum n q) ^ 2 * (4 ^ (2 * q) * binomialSum n (2 * q)) ^ 2 : ℕ) : ℝ) ≤
      Real.exp (1000 * Real.log κ / κ * n) := by
  have hkone : 1 ≤ κ := by linarith
  have hkpos : 0 < κ := by linarith
  have hlog : 0 ≤ Real.log κ := Real.log_nonneg hkone
  have hloghalf : (1 : ℝ) / 2 ≤ Real.log κ := by
    have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    exact htwo.trans (Real.log_le_log (by norm_num) hκ)
  have h4 : (4 : ℝ) ^ (2 * q) ≤ Real.exp (((4 * q : ℕ) : ℝ) * Real.log κ) := by
    rw [Real.exp_nat_mul, Real.exp_log hkpos]
    calc
      (4 : ℝ) ^ (2 * q) = (2 : ℝ) ^ (4 * q) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        congr 1
        omega
      _ ≤ κ ^ (4 * q) := pow_le_pow_left₀ (by norm_num) hκ _
  have hs := binomialSum_le_exp n q κ hkone
  have hs2 := binomialSum_le_exp n (2 * q) κ hkone
  have hproduct := mul_le_mul h4 hs2 (by positivity) (Real.exp_nonneg _)
  have hsquare := pow_le_pow_left₀ (by positivity) hs 2
  have hproductsquare := pow_le_pow_left₀ (by positivity) hproduct 2
  have hall := mul_le_mul hsquare hproductsquare (by positivity) (by positivity)
  have hexp : (((binomialSum n q) ^ 2 * (4 ^ (2 * q) * binomialSum n (2 * q)) ^ 2 : ℕ) : ℝ) ≤
      Real.exp (14 * (q : ℝ) * Real.log κ + 4 * ((n : ℝ) / κ)) := by
    push_cast
    refine hall.trans (le_of_eq ?_)
    rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  apply hexp.trans (Real.exp_le_exp.mpr ?_)
  have hqlog := mul_le_mul_of_nonneg_right hq hlog
  have hn : (0 : ℝ) ≤ (n : ℝ) / κ := div_nonneg (Nat.cast_nonneg n) hkpos.le
  have hnlog : 4 * ((n : ℝ) / κ) ≤ 8 * ((n : ℝ) / κ) * Real.log κ := by
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hloghalf)]
  have hnlognonneg : 0 ≤ ((n : ℝ) / κ) * Real.log κ := mul_nonneg hn hlog
  calc
    14 * (q : ℝ) * Real.log κ + 4 * ((n : ℝ) / κ)
        ≤ 1000 * ((n : ℝ) / κ) * Real.log κ := by nlinarith
    _ = 1000 * Real.log κ / κ * n := by ring

end MatroidProphet.Pivots

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α O₁ O₂ : Type*} [Fintype α] [Fintype O₁] [LinearOrder O₁]
    [Fintype O₂] [LinearOrder O₂] {n : ℕ}

noncomputable def smallSubsets (U : Finset α) (q : ℕ) : Finset (Finset α) := by
  classical
  exact U.powerset.filter (fun J => J.card ≤ q)

lemma mem_smallSubsets
    {α : Type u_1} [Fintype α] (U J : Finset α) (q : ℕ) :
    J ∈ smallSubsets U q ↔ J ⊆ U ∧ J.card ≤ q := by
  classical
  simp [smallSubsets]

lemma card_smallSubsets_le (U : Finset α) (q : ℕ) :
    (smallSubsets U q).card ≤ binomialSum U.card q := by
  classical
  have hsub : smallSubsets U q ⊆ (Finset.Iic q).biUnion (fun k => U.powersetCard k) := by
    intro J hJ
    obtain ⟨hJU, hJq⟩ := (mem_smallSubsets U J q).1 hJ
    exact mem_biUnion.mpr ⟨J.card, mem_Iic.mpr hJq, mem_powersetCard.mpr ⟨hJU, rfl⟩⟩
  calc
    (smallSubsets U q).card ≤ ((Finset.Iic q).biUnion (fun k => U.powersetCard k)).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.Iic q, (U.powersetCard k).card := card_biUnion_le
    _ = binomialSum U.card q := by simp [binomialSum]

noncomputable def intersectionFamily (F G : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (F ×ˢ G).image (fun p => p.1 ∩ p.2)

lemma card_intersectionFamily_le (F G : Finset (Finset (Fin n))) :
    (intersectionFamily F G).card ≤ F.card * G.card := by
  exact card_image_le.trans_eq (card_product F G)

noncomputable def residualFamily (M : Matroid α) (U : Finset α) (q : ℕ)
    (old₁ : O₁ → α) (old₂ : O₂ → α) (mark₁ : O₁ → Bool) (mark₂ : O₂ → Bool)
    (test : Fin n → α) : Finset (Finset (Fin n)) := by
  classical
  exact (smallSubsets U q).biUnion fun J => (smallSubsets U q).biUnion fun Z =>
    intersectionFamily
      (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
      (freeMarkedPatterns M old₂ (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂)

lemma mem_residualFamily (M : Matroid α) (U J Z : Finset α) (q : ℕ)
    (old₁ : O₁ → α) (old₂ : O₂ → α) (mark₁ : O₁ → Bool) (mark₂ : O₂ → Bool)
    (test : Fin n → α) (T₁ T₂ : Finset (Fin n))
    (hJ : J ⊆ U) (hJq : J.card ≤ q) (hZ : Z ⊆ U) (hZq : Z.card ≤ q)
    (hT₁ : T₁ ∈ freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
    (hT₂ : T₂ ∈ freeMarkedPatterns M old₂
      (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂) :
    T₁ ∩ T₂ ∈ residualFamily M U q old₁ old₂ mark₁ mark₂ test := by
  classical
  apply mem_biUnion.mpr
  refine ⟨J, (mem_smallSubsets U J q).2 ⟨hJ, hJq⟩, mem_biUnion.mpr ?_⟩
  refine ⟨Z, (mem_smallSubsets U Z q).2 ⟨hZ, hZq⟩, ?_⟩
  exact mem_image.mpr ⟨(T₁, T₂), mem_product.mpr ⟨hT₁, hT₂⟩, rfl⟩

lemma card_residualFamily_le (M : Matroid α) (d : α) (U : Finset α) (q : ℕ)
    (old₁ : O₁ → α) (old₂ : O₂ → α) (mark₁ : O₁ → Bool) (mark₂ : O₂ → Bool)
    (test : Fin n → α) (hU : (U : Set α) ⊆ M.E)
    (h₁ : ∀ o, old₁ o ∈ M.E) (h₂ : ∀ o, old₂ o ∈ M.E) :
    (residualFamily M U q old₁ old₂ mark₁ mark₂ test).card ≤
      (binomialSum U.card q) ^ 2 * (4 ^ (2 * q) * binomialSum n (2 * q)) ^ 2 := by
  classical
  let B := 4 ^ (2 * q) * binomialSum n (2 * q)
  let C := smallSubsets U q
  have hpair (J : Finset α) (hJ : J ∈ C) (Z : Finset α) (hZ : Z ∈ C) :
      (intersectionFamily
        (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
        (freeMarkedPatterns M old₂ (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂)).card
        ≤ B ^ 2 := by
    obtain ⟨hJU, hJq⟩ := (mem_smallSubsets U J q).1 hJ
    obtain ⟨hZU, hZq⟩ := (mem_smallSubsets U Z q).1 hZ
    have hfirst : (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁).card ≤ B := by
      apply card_freeMarkedPatterns_le M d old₁ (fun a : J => a.val) test mark₁ (2 * q)
      · simpa using (show J.card ≤ 2 * q by omega)
      · intro o
        cases o with
        | inl o => exact h₁ o
        | inr a => exact hU (hJU a.property)
    have hsecond : (freeMarkedPatterns M old₂
        (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂).card ≤ B := by
      apply card_freeMarkedPatterns_le M d old₂
        (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂ (2 * q)
      · simpa using (show J.card + Z.card ≤ 2 * q by omega)
      · intro o
        cases o with
        | inl o => exact h₂ o
        | inr a =>
          cases a with
          | inl a => exact hU (hJU a.property)
          | inr a => exact hU (hZU a.property)
    exact (card_intersectionFamily_le _ _).trans ((Nat.mul_le_mul hfirst hsecond).trans_eq (pow_two B).symm)
  have hsum : (residualFamily M U q old₁ old₂ mark₁ mark₂ test).card ≤ C.card ^ 2 * B ^ 2 := by
    calc
      _ ≤ ∑ J ∈ C, ((C.biUnion fun Z => intersectionFamily
          (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
          (freeMarkedPatterns M old₂ (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂))).card :=
        card_biUnion_le
      _ ≤ ∑ J ∈ C, ∑ Z ∈ C, (intersectionFamily
          (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
          (freeMarkedPatterns M old₂ (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂)).card :=
        sum_le_sum fun _ _ => card_biUnion_le
      _ ≤ ∑ _J ∈ C, ∑ _Z ∈ C, B ^ 2 := sum_le_sum fun J hJ => sum_le_sum fun Z hZ => hpair J hJ Z hZ
      _ = C.card ^ 2 * B ^ 2 := by simp [pow_two, Nat.mul_assoc]
  exact hsum.trans (Nat.mul_le_mul_right (B ^ 2) (Nat.pow_le_pow_left (card_smallSubsets_le U q) 2))

lemma card_residualFamily_le_exp (M : Matroid α) (d : α) (U : Finset α) (q : ℕ)
    (old₁ : O₁ → α) (old₂ : O₂ → α) (mark₁ : O₁ → Bool) (mark₂ : O₂ → Bool)
    (test : Fin n → α) (hU : (U : Set α) ⊆ M.E)
    (h₁ : ∀ o, old₁ o ∈ M.E) (h₂ : ∀ o, old₂ o ∈ M.E)
    (hn : U.card = n) (κ : ℝ) (hκ : 2 ≤ κ) (hq : (q : ℝ) ≤ (n : ℝ) / κ) :
    ((residualFamily M U q old₁ old₂ mark₁ mark₂ test).card : ℝ) ≤
      Real.exp (1000 * Real.log κ / κ * n) := by
  have h := card_residualFamily_le M d U q old₁ old₂ mark₁ mark₂ test hU h₁ h₂
  rw [hn] at h
  exact (show ((residualFamily M U q old₁ old₂ mark₁ mark₂ test).card : ℝ) ≤
      (((binomialSum n q)^2 * (4^(2*q) * binomialSum n (2*q))^2 : ℕ) : ℝ) by exact_mod_cast h).trans
    (residual_raw_count_le_exp n q κ hκ hq)

end MatroidProphet.Pivots

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ}

noncomputable def validBirthMark (a : ℤ) (ε : Fin 2) (k : IntWindow a) : Bool :=
  decide (a + 2 ≤ k.val ∧ k.val ≤ 0 ∧ k.val % 2 = (ε.val : ℤ))

noncomputable def integerBirthLayer (X : ℤ → Set α) (test : Fin n → α) (a : ℤ)
    (ε : Fin 2) (b : ParityWindow a ε) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => a + 2 ≤ b.val.val ∧ b.val.val ≤ 0 ∧
    test f ∈ X b.val.val ∧ test f ∉ X (b.val.val - 1)

noncomputable def integerResidual {Z : Type*} (M : Matroid α) (X : ℤ → Set α)
    (test : Fin n → α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α)
    (z : Z → α) (β : Z → ParityWindow a ε) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => ∃ b, f ∈ integerBirthLayer X test a ε b ∧
    test f ∉ M.closure (X (b.val.val - 2) ∪ K b ∪ z '' {w | β w = b})

noncomputable def integerResidualFamily (M : Matroid α) (U : Finset α) (q : ℕ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α)
    (test : Fin n → α) : Finset (Finset (Fin n)) :=
  residualFamily M U q
    (blockOldLabel (F := fun t : IntWindow a => F t.val))
    (blockOldLabel (F := phaseOld (fun t : ParityWindow a ε => F t.val.val) K))
    (fun o => validBirthMark a ε (blockOldStage o))
    (fun o => (ofLex (blockOldStage o)).2) test

lemma generatedPath_mono
    {α : Type u_1} [Fintype α] [LinearOrder α] {G : Type*}
    (M : Matroid α) (F : ℤ → Set α) (hF : Monotone F)
    (g : G → α) (ν : G → ℤ) : Monotone (generatedPath M F g ν) := by
  intro k l hkl
  exact M.closure_subset_closure (union_subset_union (hF hkl)
    (image_mono (fun _ hx => hx.trans hkl)))

lemma first_integer_pattern {G : Type*} [Fintype G]
    (M : Matroid α) (hE : M.E = Set.univ) (F : ℤ → Set α) (hF : Monotone F)
    (a : ℤ) (hFe : ∀ k < a, F k = M.closure ∅) (ε : Fin 2)
    (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (test : Fin n → α) (f : Fin n) :
    f ∈ blockBirthPattern M (fun t : IntWindow a => F t.val) g (windowPlacement a ν hν)
      test (validBirthMark a ε) ↔
      ∃ b, f ∈ integerBirthLayer (generatedPath M F g ν) test a ε b := by
  classical
  simp only [blockBirthPattern, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hm, hx, hn⟩
    have hv : a + 2 ≤ k.val ∧ k.val ≤ 0 ∧ k.val % 2 = (ε.val : ℤ) := by
      simpa [validBirthMark] using hm
    rw [window_prefix M F hF] at hx
    rw [window_before M hE F hF a hFe] at hn
    exact ⟨⟨k, hv.2.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.1, hv.2.1, hx, hn⟩⟩
  · rintro ⟨b, hb⟩
    have hv : a + 2 ≤ b.val.val ∧ b.val.val ≤ 0 ∧
        test f ∈ generatedPath M F g ν b.val.val ∧ test f ∉ generatedPath M F g ν (b.val.val - 1) := by
      simpa [integerBirthLayer] using hb
    refine ⟨b.val, ?_, ?_, ?_⟩
    · simpa [validBirthMark] using And.intro hv.1 (And.intro hv.2.1 b.property)
    · rw [window_prefix M F hF]
      exact hv.2.2.1
    · rw [window_before M hE F hF a hFe]
      exact hv.2.2.2

lemma integerResidual_mem_family (M : Matroid α) (hE : M.E = Set.univ)
    (U J Z : Finset α) (q : ℕ) (F : ℤ → Set α) (hF : Monotone F)
    (a : ℤ) (ha : a ≤ 0) (hFe : ∀ k < a, F k = M.closure ∅)
    (hFl : ∀ k, 0 ≤ k → F k = Set.univ) (ε : Fin 2)
    (K : ParityWindow a ε → Set α) (hK : ∀ b, K b ⊆ F b.val.val)
    (ν : J → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0)
    (β : Z → ParityWindow a ε)
    (hz : ∀ w, w.val ∈ generatedPath M F (fun i : J => i.val) ν (β w).val.val)
    (test : Fin n → α) (hnonloop : ∀ f, test f ∉ M.closure ∅)
    (hJ : J ⊆ U) (hJq : J.card ≤ q) (hZ : Z ⊆ U) (hZq : Z.card ≤ q) :
    integerResidual M (generatedPath M F (fun i : J => i.val) ν) test a ε K
        (fun w : Z => w.val) β ∈ integerResidualFamily M U q F a ε K test := by
  classical
  let g : J → α := fun i => i.val
  let z : Z → α := fun i => i.val
  let FW := fun t : IntWindow a => F t.val
  let FP := fun t : ParityWindow a ε => F t.val.val
  let θ := parityPlacement a ε ν hν
  let first := blockBirthPattern M FW g (windowPlacement a ν hν) test (validBirthMark a ε)
  let second := blockBirthPattern M (phaseOld FP K) (Sum.elim g z) (phasePlacement θ β) test
    (fun p => (ofLex p).2)
  have hz' : ∀ w, z w ∈ upperPath M FP g θ (β w) := by
    intro w
    rw [parity_upperPath]
    exact hz w
  have hFP : Monotone FP := fun _ _ h => hF h
  have hfirst : ∀ f, f ∈ first ↔ ∃ b, f ∈ integerBirthLayer (generatedPath M F g ν) test a ε b :=
    first_integer_pattern M hE F hF a hFe ε g ν hν test
  have hP : ∀ b f, f ∈ integerBirthLayer (generatedPath M F g ν) test a ε b →
      test f ∈ upperPath M FP g θ b ∧ test f ∉ lowerPath M FP g θ b := by
    intro b f hf
    have hv : a + 2 ≤ b.val.val ∧ b.val.val ≤ 0 ∧
        test f ∈ generatedPath M F g ν b.val.val ∧ test f ∉ generatedPath M F g ν (b.val.val - 1) := by
      simpa [integerBirthLayer] using hf
    rw [parity_upperPath, parity_lowerPath M hE F hF a hFe]
    exact ⟨hv.2.2.1, fun he => hv.2.2.2 (generatedPath_mono M F hF g ν (by omega) he)⟩
  have hinter := first_inter_phase_eq_residual M hE FP K hFP hK g z θ β hz' test
    (integerBirthLayer (generatedPath M F g ν) test a ε) first hfirst hP
  have hres : residualOfLayers M FP K g z θ β test
      (integerBirthLayer (generatedPath M F g ν) test a ε) =
      integerResidual M (generatedPath M F g ν) test a ε K z β := by
    ext f
    simp only [residualOfLayers, integerResidual, Finset.mem_filter, Finset.mem_univ, true_and,
      FP, θ, parity_lowerPath M hE F hF a hFe]
  rw [hres] at hinter
  rw [← hinter]
  apply mem_residualFamily M U J Z q _ _ _ _ test first second hJ hJq hZ hZq
  · apply blockBirthPattern_mem_freeMarkedPatterns M FW g (windowPlacement a ν hν) test
      (validBirthMark a ε) hnonloop
    intro f
    apply M.subset_closure _ (by simp [hE])
    let k : IntWindow a := ⟨0, by constructor <;> omega⟩
    have he : test f ∈ FW k := by change test f ∈ F 0; simp [hFl 0 le_rfl]
    exact ⟨Sum.inl ⟨toLex (k, test f), he⟩, rfl⟩
  · apply blockBirthPattern_mem_freeMarkedPatterns M (phaseOld FP K) (Sum.elim g z)
      (phasePlacement θ β) test (fun p => (ofLex p).2) hnonloop
    intro f
    apply M.subset_closure _ (by simp [hE])
    let b : ParityWindow a ε := ⟨⟨roundParity ε 0, by
      have := roundParity_bounds ε 0
      constructor <;> omega⟩, roundParity_mod ε 0⟩
    have he : test f ∈ phaseOld FP K (toLex (b, true)) := by
      change test f ∈ F (roundParity ε 0)
      simp [hFl _ (roundParity_bounds ε 0).1]
    exact ⟨Sum.inl ⟨toLex (toLex (b, true), test f), he⟩, rfl⟩

end MatroidProphet.Pivots

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open Set Finset Pivots

variable {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ}

lemma nominal_residual_mem_family (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ)
    (U Z : Finset α) (hDU : D h ⊆ (U : Set α)) (hZU : Z ⊆ U)
    (hZcard : Z.card ≤ U.card / κ) (ε : Fin 2)
    (K : ParityWindow (activation h) ε → Set α)
    (hK : ∀ b, K b ⊆ guardedPath M hE κ D C h b.val.val)
    (β : Z → ParityWindow (activation h) ε)
    (hz : ∀ w, w.val ∈ nominalPath M hE κ D C h (β w).val.val)
    (test : Fin n → α) (hnonloop : ∀ f, test f ∉ M.closure ∅) :
    integerResidual M (nominalPath M hE κ D C h) test (activation h) ε K
        (fun w : Z => w.val) β ∈
      integerResidualFamily M U (U.card / κ) (guardedPath M hE κ D C h)
        (activation h) ε K test := by
  classical
  obtain ⟨G, hGD, hGcard, τ, hτ, hgen⟩ := nominalPath_all_time_generators M hE κ hκ D C h
  let J : Finset α := G.toFinset
  let ν : J → ℤ := fun i => activation h + (τ i.val : ℤ)
  have hJ : J ⊆ U := by
    intro e he
    exact hDU (hGD (Set.mem_toFinset.mp he))
  have hJcard : J.card ≤ U.card / κ := by
    apply (Nat.le_div_iff_mul_le hκ).2
    have hDUcard : (D h).ncard ≤ U.card := by simpa using Set.ncard_mono hDU
    have hcard : κ * J.card ≤ U.card := by
      simpa only [J, ← Set.ncard_eq_toFinset_card'] using hGcard.trans hDUcard
    simpa only [Nat.mul_comm] using hcard
  have hν : ∀ i, activation h ≤ ν i ∧ ν i ≤ 0 := by
    intro i
    have hτi := hτ i.val (Set.mem_toFinset.mp i.property)
    have hhor := activation_add_horizon h
    dsimp [ν]
    constructor <;> omega
  have hX : nominalPath M hE κ D C h = generatedPath M (guardedPath M hE κ D C h)
      (fun i : J => i.val) ν := by
    funext k
    rw [hgen k]
    unfold generatedPath
    congr 1
    congr 1
    ext e
    constructor
    · rintro ⟨he, ht⟩
      exact ⟨⟨e, Set.mem_toFinset.mpr he⟩, ht, rfl⟩
    · rintro ⟨i, ht, rfl⟩
      exact ⟨Set.mem_toFinset.mp i.property, ht⟩
  rw [hX] at hz ⊢
  apply integerResidual_mem_family M hE U J Z (U.card / κ)
    (guardedPath M hE κ D C h) (guardedPath_mono M hE κ D C h)
    (activation h) (by unfold activation; omega) _
    (fun k hk => guardedPath_nonnegative M hE κ D C h hk) ε K hK ν hν β hz test hnonloop hJ hJcard hZU hZcard
  intro k hk
  apply guardedPath_early M hE κ D C h
  unfold activation at hk
  omega

lemma integerResidualFamily_card_le_exp (M : Matroid α) (hE : M.E = Set.univ) (d : α)
    (U : Finset α) (κ : ℕ) (hκ : 2 ≤ κ) (F : ℤ → Set α) (a : ℤ) (ε : Fin 2)
    (K : ParityWindow a ε → Set α) (test : Fin n → α) (hn : U.card = n) :
    ((integerResidualFamily M U (U.card / κ) F a ε K test).card : ℝ) ≤
      Real.exp (1000 * Real.log (κ : ℝ) / (κ : ℝ) * n) := by
  apply card_residualFamily_le_exp M d U (U.card / κ) _ _ _ _ test
    (by simp [hE]) (by simp [hE]) (by simp [hE]) hn (κ : ℝ) (by exact_mod_cast hκ)
  have hkpos : (0 : ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  apply (le_div_iff₀ hkpos).2
  rw [← hn]
  exact_mod_cast Nat.div_mul_le_self U.card κ

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

noncomputable def bitsWeight (q : α → ℝ) (V S : Finset α) : ℝ :=
  ∏ e ∈ V, if e ∈ S then q e else 1 - q e

noncomputable def bitsExpectation (q : α → ℝ) (V : Finset α)
    (f : Finset α → ℝ) : ℝ :=
  ∑ S ∈ V.powerset, bitsWeight q V S * f S

lemma bitsWeight_nonneg (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V S : Finset α) : 0 ≤ bitsWeight q V S := by
  apply prod_nonneg
  intro e he
  split_ifs
  · exact hq0 e
  · exact sub_nonneg.2 (hq1 e)

lemma bitsWeight_insert_no (q : α → ℝ) (V S : Finset α) (e : α)
    (he : e ∉ V) (hS : S ⊆ V) :
    bitsWeight q (insert e V) S = (1 - q e) * bitsWeight q V S := by
  have heS : e ∉ S := fun h => he (hS h)
  simp [bitsWeight, he, heS]

lemma bitsWeight_insert_yes (q : α → ℝ) (V S : Finset α) (e : α)
    (he : e ∉ V) :
    bitsWeight q (insert e V) (insert e S) = q e * bitsWeight q V S := by
  simp only [bitsWeight, prod_insert he, mem_insert_self, ite_true]
  congr 1
  apply prod_congr rfl
  intro x hx
  have hxe : x ≠ e := fun h => he (h ▸ hx)
  simp [hxe]

lemma bitsExpectation_insert (q : α → ℝ) (V : Finset α) (e : α) (he : e ∉ V)
    (f : Finset α → ℝ) :
    bitsExpectation q (insert e V) f =
      (1 - q e) * bitsExpectation q V f +
        q e * bitsExpectation q V (fun S => f (insert e S)) := by
  unfold bitsExpectation
  rw [sum_powerset_insert he, mul_sum, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro S hS
    rw [bitsWeight_insert_no q V S e he (mem_powerset.1 hS)]
    ring
  · apply sum_congr rfl
    intro S hS
    rw [bitsWeight_insert_yes q V S e he]
    ring

@[simp] lemma bitsExpectation_empty (q : α → ℝ) (f : Finset α → ℝ) :
    bitsExpectation q ∅ f = f ∅ := by
  simp [bitsExpectation, bitsWeight]

@[simp] lemma bitsExpectation_one (q : α → ℝ) (V : Finset α) :
    bitsExpectation q V (fun _ => 1) = 1 := by
  induction V using Finset.induction_on with
  | empty => simp
  | @insert e V he ih =>
    rw [bitsExpectation_insert q V e he]
    simp only [ih]
    ring

lemma bitsExpectation_mono (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V : Finset α) {f g : Finset α → ℝ} (h : ∀ S ⊆ V, f S ≤ g S) :
    bitsExpectation q V f ≤ bitsExpectation q V g := by
  apply sum_le_sum
  intro S hS
  exact mul_le_mul_of_nonneg_left (h S (mem_powerset.1 hS)) (bitsWeight_nonneg q hq0 hq1 V S)

lemma bitsExpectation_congr (q : α → ℝ) (V : Finset α)
    {f g : Finset α → ℝ} (h : ∀ S ⊆ V, f S = g S) :
    bitsExpectation q V f = bitsExpectation q V g := by
  apply sum_congr rfl
  intro S hS
  rw [h S (mem_powerset.1 hS)]

lemma bitsExpectation_add (q : α → ℝ) (V : Finset α) (f g : Finset α → ℝ) :
    bitsExpectation q V (fun S => f S + g S) =
      bitsExpectation q V f + bitsExpectation q V g := by
  simp only [bitsExpectation, mul_add, sum_add_distrib]

lemma bitsExpectation_const (q : α → ℝ) (V : Finset α) (c : ℝ) :
    bitsExpectation q V (fun _ => c) = c := by
  have h := bitsExpectation_one q V
  simp only [bitsExpectation, mul_one] at h
  simp only [bitsExpectation, ← sum_mul, h, one_mul]

lemma bitsExpectation_nonneg (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V : Finset α) {f : Finset α → ℝ} (h : ∀ S ⊆ V, 0 ≤ f S) :
    0 ≤ bitsExpectation q V f := by
  apply sum_nonneg
  intro S hS
  exact mul_nonneg (bitsWeight_nonneg q hq0 hq1 V S) (h S (mem_powerset.1 hS))

noncomputable def bitsFailure (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (V I : Finset α) : ℝ :=
  bitsExpectation q V (fun S => if cert (I ∪ S) then 0 else 1)

lemma bitsFailure_nonneg (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V I : Finset α) : 0 ≤ bitsFailure cert q V I := by
  apply bitsExpectation_nonneg q hq0 hq1
  intro S hS
  split_ifs <;> norm_num

lemma bitsFailure_le_one (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V I : Finset α) : bitsFailure cert q V I ≤ 1 := by
  rw [← bitsExpectation_one q V]
  apply bitsExpectation_mono q hq0 hq1
  intro S hS
  split_ifs <;> norm_num

lemma bitsFailure_forced_antitone (cert : Finset α → Prop) [DecidablePred cert]
    (hcert : Monotone cert) (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V : Finset α) {I J : Finset α} (hIJ : I ⊆ J) :
    bitsFailure cert q V J ≤ bitsFailure cert q V I := by
  apply bitsExpectation_mono q hq0 hq1
  intro S hS
  have himp : cert (I ∪ S) → cert (J ∪ S) := hcert (union_subset_union hIJ Subset.rfl)
  by_cases hi : cert (I ∪ S)
  · simp [hi, himp hi]
  · split_ifs <;> norm_num

lemma bitsFailure_certifies (cert : Finset α → Prop) [DecidablePred cert]
    (hcert : Monotone cert) (q : α → ℝ) (V I : Finset α) (hI : cert I) :
    bitsFailure cert q V I = 0 := by
  unfold bitsFailure bitsExpectation
  apply sum_eq_zero
  intro S hS
  have hIS : cert (I ∪ S) := hcert subset_union_left hI
  simp [hIS]

lemma bitsFailure_insert (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (V I : Finset α) (e : α) (he : e ∉ V) :
    bitsFailure cert q (insert e V) I =
      (1 - q e) * bitsFailure cert q V I + q e * bitsFailure cert q V (insert e I) := by
  unfold bitsFailure
  rw [bitsExpectation_insert q V e he]
  congr 2
  apply bitsExpectation_congr
  intro S hS
  simp only [union_insert, insert_union]

lemma bitsFailure_split (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (V I : Finset α) (e : α) (he : e ∈ V) :
    bitsFailure cert q V I = (1 - q e) * bitsFailure cert q (V.erase e) I +
      q e * bitsFailure cert q (V.erase e) (insert e I) := by
  have h := bitsFailure_insert cert q (V.erase e) I e (notMem_erase e V)
  simpa only [insert_erase he] using h

lemma bitsFailure_antitone (cert : Finset α → Prop) [DecidablePred cert]
    (hcert : Monotone cert) (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (I : Finset α) : Antitone (fun V => bitsFailure cert q V I) := by
  apply Finset.antitone_iff_forall_insert_le.2
  intro V e he
  rw [bitsFailure_insert cert q V I e he]
  have h := bitsFailure_forced_antitone cert hcert q hq0 hq1 V (subset_insert e I)
  have hmul := mul_le_mul_of_nonneg_left h (hq0 e)
  nlinarith

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

theorem bitsExpectation_restrict (q : α → ℝ) (W V : Finset α) (hV : V ⊆ W)
    (f : Finset α → ℝ)
    (hf : ∀ S S', (∀ e ∈ V, e ∈ S ↔ e ∈ S') → f S = f S') :
    bitsExpectation q W f = bitsExpectation q V f := by
  induction W using Finset.strongInductionOn with
  | _ W ih =>
    by_cases hW : W ⊆ V
    · rw [subset_antisymm hW hV]
    · obtain ⟨e, heW, heV⟩ := Finset.not_subset.mp hW
      have hVerase : V ⊆ W.erase e := by
        intro x hx
        exact mem_erase.mpr ⟨fun h => heV (h ▸ hx), hV hx⟩
      have heq : bitsExpectation q (W.erase e) (fun S => f (insert e S)) =
          bitsExpectation q (W.erase e) f := by
        apply bitsExpectation_congr
        intro S _
        apply hf
        intro x hx
        have hxe : x ≠ e := fun h => heV (h ▸ hx)
        simp [hxe]
      have hs := bitsExpectation_insert q (W.erase e) e (notMem_erase e W) f
      rw [insert_erase heW, heq, ih (W.erase e) (erase_ssubset heW) hVerase] at hs
      linarith

lemma bitsExpectation_sum {ι : Type*} (q : α → ℝ) (V : Finset α) (I : Finset ι)
    (f : ι → Finset α → ℝ) :
    bitsExpectation q V (fun S => ∑ e ∈ I, f e S) = ∑ e ∈ I, bitsExpectation q V (f e) := by
  simp only [bitsExpectation, mul_sum]
  rw [sum_comm]

lemma bitsExpectation_mem (q : α → ℝ) (V : Finset α) (e : α) (he : e ∈ V) :
    bitsExpectation q V (fun S => if e ∈ S then 1 else 0) = q e := by
  rw [bitsExpectation_restrict q V {e} (singleton_subset_iff.mpr he)
    (fun S => if e ∈ S then 1 else 0) (by
      intro S S' h
      simp only [h e (mem_singleton_self e)])]
  rw [show ({e} : Finset α) = insert e ∅ from rfl,
    bitsExpectation_insert q ∅ e (notMem_empty e)]
  simp [bitsExpectation_empty]

lemma bitsExpectation_card_inter (q : α → ℝ) (V K : Finset α) (hKV : K ⊆ V) :
    bitsExpectation q V (fun S => ((K ∩ S).card : ℝ)) = ∑ e ∈ K, q e := by
  have hsum (S : Finset α) : ((K ∩ S).card : ℝ) =
      ∑ e ∈ K, if e ∈ S then (1 : ℝ) else 0 := by
    simp
  simp_rw [hsum]
  rw [bitsExpectation_sum]
  exact sum_congr rfl (fun e he => bitsExpectation_mem q V e (hKV he))

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

noncomputable def residualDelta : ℝ := ((2 : ℝ)^26)⁻¹

lemma residual_tail_coefficient :
    (1000 * Real.log densityThreshold / densityThreshold - residualDelta * Real.log 2) *
      densityThreshold ≤ -(26 * Real.log 2) := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  unfold densityThreshold residualDelta
  rw [Real.log_pow]
  norm_num
  nlinarith

theorem residual_tail_constant (n : ℝ) (hn : densityThreshold ≤ n) :
    Real.exp ((1000 * Real.log densityThreshold / densityThreshold - residualDelta * Real.log 2) * n)
      ≤ residualDelta := by
  have hk : 0 < densityThreshold := constants_positive.2.1
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hc := residual_tail_coefficient
  have hneg : 1000 * Real.log densityThreshold / densityThreshold - residualDelta * Real.log 2 ≤ 0 := by
    nlinarith
  have hmul := mul_le_mul_of_nonpos_left hn hneg
  have he := Real.exp_le_exp.mpr (hmul.trans hc)
  have hid : Real.exp (-(26 * Real.log (2 : ℝ))) = residualDelta := by
    rw [Real.exp_neg]
    have hpow := Real.exp_nat_mul (Real.log (2 : ℝ)) 26
    norm_num at hpow
    rw [hpow]
    rw [Real.exp_log (by norm_num)]
    rfl
  rwa [hid] at he

theorem residual_error_constant : densityThreshold⁻¹ + 2 * residualDelta ≤ ((2 : ℝ)^23)⁻¹ := by
  norm_num [densityThreshold, residualDelta]

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

lemma bitsExpectation_contains (q : α → ℝ) (V R : Finset α) (hR : R ⊆ V) :
    bitsExpectation q V (fun S => if R ⊆ S then 1 else 0) = ∏ e ∈ R, q e := by
  induction V using Finset.induction_on generalizing R with
  | empty =>
    have h : R = ∅ := Finset.subset_empty.mp hR
    subst R
    simp
  | @insert e V he ih =>
    rw [bitsExpectation_insert q V e he]
    by_cases heR : e ∈ R
    · have hRV : R.erase e ⊆ V := by
        intro x hx
        have hm := hR (mem_of_mem_erase hx)
        rcases mem_insert.mp hm with rfl | hm
        · exact (notMem_erase _ _ hx).elim
        · exact hm
      have hzero : bitsExpectation q V (fun S => if R ⊆ S then 1 else 0) = 0 := by
        conv_rhs => rw [← bitsExpectation_const q V 0]
        apply bitsExpectation_congr
        intro S hS
        have hn : ¬ R ⊆ S := fun hh => he (hS (hh heR))
        simp [hn]
      have hyes : bitsExpectation q V (fun S => if R ⊆ insert e S then 1 else 0) =
          bitsExpectation q V (fun S => if R.erase e ⊆ S then 1 else 0) := by
        apply bitsExpectation_congr
        intro S hS
        have hiff : R ⊆ insert e S ↔ R.erase e ⊆ S := by
          constructor
          · intro h x hx
            exact (mem_insert.mp (h (mem_of_mem_erase hx))).resolve_left (ne_of_mem_erase hx)
          · intro h x hx
            by_cases hxe : x = e
            · simp [hxe]
            · exact mem_insert_of_mem (h (mem_erase.mpr ⟨hxe, hx⟩))
        simp only [hiff]
      rw [hzero, hyes, ih _ hRV]
      simpa using (mul_prod_erase R q heR)
    · have hRV : R ⊆ V := by
        intro x hx
        exact (mem_insert.mp (hR hx)).resolve_left (fun h => heR (h ▸ hx))
      have hyes : bitsExpectation q V (fun S => if R ⊆ insert e S then 1 else 0) =
          bitsExpectation q V (fun S => if R ⊆ S then 1 else 0) := by
        apply bitsExpectation_congr
        intro S hS
        have hiff : R ⊆ insert e S ↔ R ⊆ S := by
          constructor
          · intro h x hx
            exact (mem_insert.mp (h hx)).resolve_left (fun h => heR (h ▸ hx))
          · exact fun h => h.trans (subset_insert e S)
        simp only [hiff]
      rw [hyes, ih _ hRV]
      ring

lemma bitsExpectation_mul_const (q : α → ℝ) (V : Finset α) (c : ℝ) (f : Finset α → ℝ) :
    bitsExpectation q V (fun S => c * f S) = c * bitsExpectation q V f := by
  simp only [bitsExpectation, mul_sum]
  apply sum_congr rfl
  intro S hS
  ring

lemma bitsExpectation_contains_le_half_pow (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqhalf : ∀ e, q e ≤ 1 / 2)
    (V R : Finset α) (hR : R ⊆ V) :
    bitsExpectation q V (fun S => if R ⊆ S then 1 else 0) ≤ (1 / 2 : ℝ) ^ R.card := by
  rw [bitsExpectation_contains q V R hR]
  simpa using prod_le_prod₀ (fun e _ => hq0 e) (fun e _ => hqhalf e)

noncomputable def residualBad (F : Finset (Finset α)) (t : ℝ) (S : Finset α) : Prop :=
  ∃ R ∈ F, t < (R.card : ℝ) ∧ R ⊆ S

noncomputable def residualBadIndicator (F : Finset (Finset α)) (t : ℝ) (S : Finset α) : ℝ := by
  classical
  exact if residualBad F t S then 1 else 0

lemma residualBad_indicator_le (F : Finset (Finset α)) (t : ℝ) (S : Finset α) :
    residualBadIndicator F t S ≤
      ∑ R ∈ F, if t < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0 := by
  classical
  unfold residualBadIndicator
  split_ifs with hb
  · obtain ⟨R, hRF, hRt, hRS⟩ := hb
    have h := single_le_sum (f := fun R : Finset α =>
      if t < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0)
      (fun R _ => by split_ifs <;> norm_num) hRF
    simpa [hRt, hRS] using h
  · exact sum_nonneg (fun R _ => by split_ifs <;> norm_num)

lemma bitsExpectation_residualBad_le (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqhalf : ∀ e, q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V) (t : ℝ) :
    bitsExpectation q V (fun S => residualBadIndicator F t S) ≤
      (F.card : ℝ) * Real.exp (-t * Real.log 2) := by
  classical
  have hq1 : ∀ e, q e ≤ 1 := fun e => (hqhalf e).trans (by norm_num)
  calc
    _ ≤ bitsExpectation q V (fun S => ∑ R ∈ F,
        if t < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0) :=
      bitsExpectation_mono q hq0 hq1 V (fun S _ => residualBad_indicator_le F t S)
    _ = ∑ R ∈ F, bitsExpectation q V (fun S =>
        if t < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0) := bitsExpectation_sum q V F _
    _ ≤ ∑ _R ∈ F, Real.exp (-t * Real.log 2) := by
      apply sum_le_sum
      intro R hRF
      by_cases hRt : t < (R.card : ℝ)
      · simp only [hRt, ite_true]
        apply (bitsExpectation_contains_le_half_pow q hq0 hqhalf V R (hF R hRF)).trans
        have heq : (1 / 2 : ℝ) ^ R.card = Real.exp (-(R.card : ℝ) * Real.log 2) := by
          rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
          simp
        rw [heq]
        apply Real.exp_le_exp.mpr
        have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        exact mul_le_mul_of_nonneg_right (by linarith) hlog
      · simp only [hRt, ite_false, bitsExpectation_const]
        exact Real.exp_nonneg _
    _ = _ := by simp

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma bitsExpectation_union (p q : α → ℝ) (V : Finset α) (f : Finset α → ℝ) :
    bitsExpectation p V (fun D => bitsExpectation q V (fun C => f (D ∪ C))) =
      bitsExpectation (fun e => p e + (1 - p e) * q e) V f := by
  induction V using Finset.induction_on generalizing f with
  | empty => simp
  | @insert e V he ih =>
    rw [bitsExpectation_insert p V e he,
      bitsExpectation_insert (fun e => p e + (1 - p e) * q e) V e he]
    have hno : bitsExpectation p V (fun D => bitsExpectation q (insert e V) (fun C => f (D ∪ C))) =
        (1 - q e) * bitsExpectation p V (fun D => bitsExpectation q V (fun C => f (D ∪ C))) +
        q e * bitsExpectation p V (fun D => bitsExpectation q V (fun C => f (insert e (D ∪ C)))) := by
      simp_rw [bitsExpectation_insert q V e he, union_insert]
      rw [bitsExpectation_add, bitsExpectation_mul_const, bitsExpectation_mul_const]
    have hyes : bitsExpectation p V (fun D => bitsExpectation q (insert e V) (fun C => f (insert e D ∪ C))) =
        bitsExpectation p V (fun D => bitsExpectation q V (fun C => f (insert e (D ∪ C)))) := by
      apply bitsExpectation_congr
      intro D hD
      rw [bitsExpectation_insert q V e he]
      simp only [insert_union, union_insert, insert_idem]
      ring
    rw [hno, hyes, ih f, ih (fun S => f (insert e S))]
    ring

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma residualDelta_nonneg : 0 ≤ residualDelta := by unfold residualDelta; positivity

lemma bitsExpectation_residualBad_delta (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqhalf : ∀ e, q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V)
    (hcard : (F.card : ℝ) ≤ Real.exp (1000 * Real.log densityThreshold / densityThreshold * V.card))
    (hn : densityThreshold ≤ (V.card : ℝ)) :
    bitsExpectation q V (residualBadIndicator F (residualDelta * V.card)) ≤ residualDelta := by
  have htail := bitsExpectation_residualBad_le q hq0 hqhalf V F hF (residualDelta * V.card)
  have hmul := mul_le_mul_of_nonneg_right hcard
    (Real.exp_nonneg (-(residualDelta * V.card) * Real.log 2))
  apply htail.trans (hmul.trans ?_)
  rw [← Real.exp_add]
  convert residual_tail_constant (V.card : ℝ) hn using 1
  congr 1
  ring

lemma capturedResidual_le
    {α : Type u_1} [DecidableEq α] (V S R : Finset α) (F : Finset (Finset α))
    (hS : S ⊆ V) (hR : R ∈ F) (hRS : R ⊆ S) :
    (R.card : ℝ) ≤ residualDelta * V.card +
      (V.card : ℝ) * residualBadIndicator F (residualDelta * V.card) S := by
  classical
  have hcard : (R.card : ℝ) ≤ V.card := by exact_mod_cast Finset.card_le_card (hRS.trans hS)
  have hδ : 0 ≤ residualDelta * (V.card : ℝ) := mul_nonneg residualDelta_nonneg (Nat.cast_nonneg _)
  by_cases hsmall : (R.card : ℝ) ≤ residualDelta * V.card
  · have hind : 0 ≤ residualBadIndicator F (residualDelta * V.card) S := by
      unfold residualBadIndicator
      split_ifs <;> norm_num
    nlinarith [mul_nonneg (Nat.cast_nonneg V.card) hind]
  · have hbad : residualBad F (residualDelta * V.card) S := ⟨R, hR, lt_of_not_ge hsmall, hRS⟩
    simp only [residualBadIndicator, hbad, ite_true, mul_one]
    linarith

lemma tripleMask_residual_error_le
    (p q r : α → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    (hpq : ∀ e, p e + (1 - p e) * q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V)
    (hcard : (F.card : ℝ) ≤ Real.exp (1000 * Real.log densityThreshold / densityThreshold * V.card))
    (hn : densityThreshold ≤ (V.card : ℝ))
    (error : Finset α → Finset α → Finset α → ℝ)
    (herror : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V,
      error D C T ≤ residualDelta * V.card + (V.card : ℝ) *
        residualBadIndicator F (residualDelta * V.card) (D ∪ C)) :
    bitsExpectation p V (fun D => bitsExpectation q V (fun C => bitsExpectation r V (error D C))) ≤
      2 * residualDelta * V.card := by
  have hpq0 : ∀ e, 0 ≤ p e + (1 - p e) * q e := by
    intro e
    exact add_nonneg (hp0 e) (mul_nonneg (sub_nonneg.mpr (hp1 e)) (hq0 e))
  have hbad := bitsExpectation_residualBad_delta (fun e => p e + (1 - p e) * q e)
    hpq0 hpq V F hF hcard hn
  calc
    _ ≤ bitsExpectation p V (fun D => bitsExpectation q V (fun C => bitsExpectation r V (fun _T =>
          residualDelta * V.card + (V.card : ℝ) * residualBadIndicator F (residualDelta * V.card) (D ∪ C)))) := by
      apply bitsExpectation_mono p hp0 hp1
      intro D hD
      apply bitsExpectation_mono q hq0 hq1
      intro C hC
      exact bitsExpectation_mono r hr0 hr1 V (fun T hT => herror D hD C hC T hT)
    _ = residualDelta * V.card + (V.card : ℝ) * bitsExpectation
        (fun e => p e + (1 - p e) * q e) V (residualBadIndicator F (residualDelta * V.card)) := by
      simp_rw [bitsExpectation_const, bitsExpectation_add, bitsExpectation_mul_const, bitsExpectation_const]
      rw [bitsExpectation_union]
    _ ≤ residualDelta * V.card + (V.card : ℝ) * residualDelta :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg V.card))
    _ = _ := by ring

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open Set

variable {α : Type*} [Fintype α]

lemma natRank_union_le_add_ncard (M : Matroid α) (X Z : Set α) :
    natRank M (X ∪ Z) ≤ natRank M X + Z.ncard := by
  have hz : Z.encard ≠ ⊤ := (Set.toFinite Z).encard_lt_top.ne
  have h := ENat.toNat_le_toNat (M.eRk_union_le_eRk_add_encard X Z)
    (WithTop.add_ne_top.2 ⟨rank_ne_top M X, hz⟩)
  simpa only [ENat.toNat_add (rank_ne_top M X) hz, natRank, Set.ncard_def] using h

lemma densityExpansion_residual_le_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P Z : Set α) :
    let Q := densityExpansion M hE κ D P
    (D ∩ (M.closure (Q ∪ Z) \ Q)).ncard ≤ κ * Z.ncard := by
  dsimp only
  have hd := densityExpansion_residual M hE κ D P Z
  have hr := Nat.mul_le_mul_left κ
    (natRank_union_le_add_ncard M (densityExpansion M hE κ D P) Z)
  rw [Nat.mul_add] at hr
  dsimp only at hd
  omega

lemma safe_layer_le_witness_residual (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D F K Z A S : Set α)
    (hS : S ⊆ (D ∩ A) \ densityExpansion M hE κ D (F ∪ K)) :
    S.ncard ≤ κ * Z.ncard +
      (A \ M.closure (densityExpansion M hE κ D F ∪ K ∪ Z)).ncard := by
  let Q := densityExpansion M hE κ D (F ∪ K)
  let R := A \ M.closure (densityExpansion M hE κ D F ∪ K ∪ Z)
  have hX : densityExpansion M hE κ D F ⊆ Q :=
    densityExpansion_mono M hE κ D subset_union_left
  have hK : K ⊆ Q := subset_union_right.trans
    (densityExpansion_extensive M hE κ D (F ∪ K))
  have hcl : M.closure (densityExpansion M hE κ D F ∪ K ∪ Z) ⊆
      M.closure (Q ∪ Z) :=
    M.closure_subset_closure (union_subset_union (union_subset hX hK) Subset.rfl)
  have hcharge : S \ R ⊆ D ∩ (M.closure (Q ∪ Z) \ Q) := by
    intro e he
    have hs := hS he.1
    refine ⟨hs.1.1, hcl ?_, hs.2⟩
    by_contra hn
    exact he.2 ⟨hs.1.2, hn⟩
  have hcount := (Set.ncard_mono hcharge).trans
    (densityExpansion_residual_le_generators M hE κ D (F ∪ K) Z)
  exact (Set.ncard_le_ncard_sdiff_add_ncard S R).trans (Nat.add_le_add_right hcount _)

lemma safe_sum_le_witness_residual {ι : Type*} (L : Finset ι)
    (M : Matroid α) (hE : M.E = univ) (κ : ℕ) (D : Set α)
    (F K Z A S : ι → Set α)
    (hS : ∀ b ∈ L, S b ⊆ (D ∩ A b) \ densityExpansion M hE κ D (F b ∪ K b)) :
    ∑ b ∈ L, (S b).ncard ≤ κ * (∑ b ∈ L, (Z b).ncard) +
      ∑ b ∈ L, (A b \ M.closure (densityExpansion M hE κ D (F b) ∪ K b ∪ Z b)).ncard := by
  calc
    _ ≤ ∑ b ∈ L, (κ * (Z b).ncard +
        (A b \ M.closure (densityExpansion M hE κ D (F b) ∪ K b ∪ Z b)).ncard) :=
      Finset.sum_le_sum fun b hb => safe_layer_le_witness_residual M hE κ D
        (F b) (K b) (Z b) (A b) (S b) (hS b hb)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

noncomputable def tripleMaskExpectation (p q r : α → ℝ) (V : Finset α)
    (f : Finset α → Finset α → Finset α → ℝ) : ℝ :=
  bitsExpectation p V (fun D => bitsExpectation q V (fun C => bitsExpectation r V (f D C)))

lemma tripleMaskExpectation_mono (p q r : α → ℝ)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    (V : Finset α) {f g : Finset α → Finset α → Finset α → ℝ}
    (h : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V, f D C T ≤ g D C T) :
    tripleMaskExpectation p q r V f ≤ tripleMaskExpectation p q r V g := by
  apply bitsExpectation_mono p hp0 hp1
  intro D hD
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  exact bitsExpectation_mono r hr0 hr1 V (fun T hT => h D hD C hC T hT)

lemma tripleMaskExpectation_add (p q r : α → ℝ) (V : Finset α)
    (f g : Finset α → Finset α → Finset α → ℝ) :
    tripleMaskExpectation p q r V (fun D C T => f D C T + g D C T) =
      tripleMaskExpectation p q r V f + tripleMaskExpectation p q r V g := by
  simp only [tripleMaskExpectation, bitsExpectation_add]

lemma tripleMaskExpectation_mul (p q r : α → ℝ) (V : Finset α) (c : ℝ)
    (f : Finset α → Finset α → Finset α → ℝ) :
    tripleMaskExpectation p q r V (fun D C T => c * f D C T) =
      c * tripleMaskExpectation p q r V f := by
  simp only [tripleMaskExpectation, bitsExpectation_mul_const]

lemma tripleMask_sample_to_rank (p q r : α → ℝ)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    (V : Finset α) (σ z error : Finset α → Finset α → Finset α → ℝ)
    (Y : ℝ)
    (hdet : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V, σ D C T ≤ densityThreshold * z D C T + error D C T)
    (hsafe : retainedFraction * Y - (V.card : ℝ) / densityThreshold ≤ tripleMaskExpectation p q r V σ)
    (herr : tripleMaskExpectation p q r V error ≤ 2 * residualDelta * V.card) :
    (retainedFraction * Y - ((2 : ℝ)^23)⁻¹ * V.card) / densityThreshold ≤
      tripleMaskExpectation p q r V z := by
  have hcompare := tripleMaskExpectation_mono p q r hp0 hp1 hq0 hq1 hr0 hr1 V hdet
  rw [tripleMaskExpectation_add, tripleMaskExpectation_mul] at hcompare
  have hc := mul_le_mul_of_nonneg_right residual_error_constant (Nat.cast_nonneg V.card)
  have hkpos : 0 < densityThreshold := constants_positive.2.1
  apply (div_le_iff₀ hkpos).2
  rw [div_eq_mul_inv] at hsafe
  nlinarith

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α]

noncomputable def nominalLayerSet (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2)
    (b : ParityWindow (activation h) ε) : Set α :=
  {e | e ∈ U ∧ activation h + 2 ≤ b.val.val ∧ b.val.val ≤ 0 ∧
    e ∈ nominalPath M hE κ D C h b.val.val ∧ e ∉ nominalPath M hE κ D C h (b.val.val - 1)}

noncomputable def nominalRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U O : Set α) (ε : Fin 2) : ℕ :=
  ∑ b : ParityWindow (activation h) ε,
    conditionalRank M (nominalLayerSet M hE κ D C h U ε b \ O)
      (nominalPath M hE κ D C h (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)

noncomputable def safeLayerSet (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (ε : Fin 2)
    (b : ParityWindow (activation h) ε) : Set α :=
  (I ∩ nominalLayerSet M hE κ D C h U ε b) \
    densityExpansion M hE κ (D h)
      (guardedPath M hE κ D C h (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)

noncomputable def safeLayerStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (ε : Fin 2) : ℕ :=
  ∑ b : ParityWindow (activation h) ε, (safeLayerSet M hE κ D C T h U I ε b).ncard

def boolParity (parity : Bool) : Fin 2 := if parity then 1 else 0

lemma boolParity_val (parity : Bool) : ((boolParity parity).val : ℤ) = (if parity then 1 else 0) := by
  cases parity <;> rfl

lemma nominalLayerSet_subset (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2)
    (b : ParityWindow (activation h) ε) : nominalLayerSet M hE κ D C h U ε b ⊆ U :=
  fun _ he => he.1

lemma nominalLayerSet_disjoint (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2) :
    Pairwise (fun b c => Disjoint (nominalLayerSet M hE κ D C h U ε b)
      (nominalLayerSet M hE κ D C h U ε c)) := by
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro e hb hc
  have hval : b.val.val ≠ c.val.val := by
    intro heq
    exact hbc (Subtype.ext (Subtype.ext heq))
  rcases lt_or_gt_of_ne hval with hlt | hlt
  · exact hc.2.2.2.2 (nominalPath_mono M hE κ D C h (by omega) hb.2.2.2.1)
  · exact hb.2.2.2.2 (nominalPath_mono M hE κ D C h (by omega) hc.2.2.2.1)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α β : Type*} [DecidableEq α]

lemma bitsExpectation_mul_left (q : α → ℝ) (V : Finset α) (c : ℝ) (f : Finset α → ℝ) :
    bitsExpectation q V (fun S => c * f S) = c * bitsExpectation q V f := by
  simp only [bitsExpectation, mul_sum]
  apply sum_congr rfl
  intro S hS
  ring

lemma bitsExpectation_mul_right (q : α → ℝ) (V : Finset α) (c : ℝ) (f : Finset α → ℝ) :
    bitsExpectation q V (fun S => f S * c) = bitsExpectation q V f * c := by
  simp only [bitsExpectation, sum_mul]
  apply sum_congr rfl
  intro S hS
  ring

inductive RevealTree (α β : Type*) where
  | leaf (value : β)
  | query (e : α) (no yes : RevealTree α β)

def RevealTree.Fresh : RevealTree α β → Finset α → Prop
  | .leaf _, _ => True
  | .query e no yes, V => e ∈ V ∧ no.Fresh (V.erase e) ∧ yes.Fresh (V.erase e)

def RevealTree.run : RevealTree α β → Finset α → β
  | .leaf value, _ => value
  | .query e no yes, S => if e ∈ S then yes.run (S.erase e) else no.run (S.erase e)

def RevealTree.queried : RevealTree α β → Finset α → Finset α
  | .leaf _, _ => ∅
  | .query e no yes, S => insert e (if e ∈ S then yes.queried (S.erase e) else no.queried (S.erase e))

def RevealTree.hybrid : RevealTree α β → Finset α → Finset α → Finset α
  | .leaf _, S, _ => S
  | .query e no yes, S, T =>
      let H := if e ∈ S then yes.hybrid (S.erase e) (T.erase e)
        else no.hybrid (S.erase e) (T.erase e)
      if e ∈ T then insert e H else H

lemma RevealTree.queried_subset (tree : RevealTree α β) (V S : Finset α) (fresh : tree.Fresh V) :
    tree.queried S ⊆ V := by
  induction tree generalizing V S with
  | leaf value => exact empty_subset V
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    apply insert_subset he
    by_cases heS : e ∈ S
    · simpa [queried, heS] using (ihy (V.erase e) (S.erase e) hy).trans (erase_subset e V)
    · simpa [queried, heS] using (ihn (V.erase e) (S.erase e) hn).trans (erase_subset e V)

lemma RevealTree.run_query_no (e : α) (no yes : RevealTree α β) (S : Finset α) (he : e ∉ S) :
    (RevealTree.query e no yes).run S = no.run S := by simp [run, he]

lemma RevealTree.run_query_yes (e : α) (no yes : RevealTree α β) (S : Finset α) (he : e ∉ S) :
    (RevealTree.query e no yes).run (insert e S) = yes.run S := by simp [run, he]

lemma RevealTree.hybrid_query (e : α) (no yes : RevealTree α β) (S T : Finset α)
    (heS : e ∉ S) (heT : e ∉ T) :
    (RevealTree.query e no yes).hybrid S T = no.hybrid S T ∧
    (RevealTree.query e no yes).hybrid S (insert e T) = insert e (no.hybrid S T) ∧
    (RevealTree.query e no yes).hybrid (insert e S) T = yes.hybrid S T ∧
    (RevealTree.query e no yes).hybrid (insert e S) (insert e T) = insert e (yes.hybrid S T) := by
  simp [hybrid, heS, heT]

lemma RevealTree.mean_run_query (q : α → ℝ) (V : Finset α) (e : α)
    (no yes : RevealTree α β) (φ : β → ℝ) (he : e ∈ V) :
    bitsExpectation q V (fun S => φ ((RevealTree.query e no yes).run S)) =
      (1-q e) * bitsExpectation q (V.erase e) (fun S => φ (no.run S)) +
        q e * bitsExpectation q (V.erase e) (fun S => φ (yes.run S)) := by
  have hs := bitsExpectation_insert q (V.erase e) e (notMem_erase e V)
    (fun S => φ ((RevealTree.query e no yes).run S))
  rw [insert_erase he] at hs
  rw [hs]
  congr 1
  · congr 1
    apply bitsExpectation_congr
    intro S hS
    rw [run_query_no _ _ _ _ (fun heS => notMem_erase e V (hS heS))]
  · congr 1
    apply bitsExpectation_congr
    intro S hS
    rw [run_query_yes _ _ _ _ (fun heS => notMem_erase e V (hS heS))]

theorem RevealTree.hybrid_independent (tree : RevealTree α β)
    (q : α → ℝ) (V : Finset α) (fresh : tree.Fresh V)
    (φ : β → ℝ) (ψ : Finset α → ℝ) :
    bitsExpectation q V (fun S => bitsExpectation q V (fun T => φ (tree.run S) * ψ (tree.hybrid S T))) =
      bitsExpectation q V (fun S => φ (tree.run S)) * bitsExpectation q V ψ := by
  induction tree generalizing V ψ with
  | leaf value =>
    simp only [run, hybrid, bitsExpectation_const]
    exact bitsExpectation_mul_left q V (φ value) ψ
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    let W := V.erase e
    have heW : e ∉ W := notMem_erase e V
    have hWV : insert e W = V := insert_erase he
    have hsplit (S : Finset α) := bitsExpectation_insert q W e heW
      (fun T => φ ((RevealTree.query e no yes).run S) * ψ ((RevealTree.query e no yes).hybrid S T))
    have hNo : bitsExpectation q W (fun S => bitsExpectation q V
        (fun T => φ ((RevealTree.query e no yes).run S) * ψ ((RevealTree.query e no yes).hybrid S T))) =
        (1-q e) * bitsExpectation q W (fun S => bitsExpectation q W
          (fun T => φ (no.run S) * ψ (no.hybrid S T))) +
        q e * bitsExpectation q W (fun S => bitsExpectation q W
          (fun T => φ (no.run S) * ψ (insert e (no.hybrid S T)))) := by
      rw [← bitsExpectation_mul_left, ← bitsExpectation_mul_left, ← bitsExpectation_add]
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun hs => heW (hS hs)
      have h := hsplit S
      rw [hWV] at h
      rw [h]
      congr 1
      · congr 1
        apply bitsExpectation_congr
        intro T hT
        have heT : e ∉ T := fun ht => heW (hT ht)
        rw [run_query_no _ _ _ _ heS, (hybrid_query e no yes S T heS heT).1]
      · congr 1
        apply bitsExpectation_congr
        intro T hT
        have heT : e ∉ T := fun ht => heW (hT ht)
        rw [run_query_no _ _ _ _ heS, (hybrid_query e no yes S T heS heT).2.1]
    have hYes : bitsExpectation q W (fun S => bitsExpectation q V
        (fun T => φ ((RevealTree.query e no yes).run (insert e S)) *
          ψ ((RevealTree.query e no yes).hybrid (insert e S) T))) =
        (1-q e) * bitsExpectation q W (fun S => bitsExpectation q W
          (fun T => φ (yes.run S) * ψ (yes.hybrid S T))) +
        q e * bitsExpectation q W (fun S => bitsExpectation q W
          (fun T => φ (yes.run S) * ψ (insert e (yes.hybrid S T)))) := by
      rw [← bitsExpectation_mul_left, ← bitsExpectation_mul_left, ← bitsExpectation_add]
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun hs => heW (hS hs)
      have h := hsplit (insert e S)
      rw [hWV] at h
      rw [h]
      congr 1
      · congr 1
        apply bitsExpectation_congr
        intro T hT
        have heT : e ∉ T := fun ht => heW (hT ht)
        rw [run_query_yes _ _ _ _ heS, (hybrid_query e no yes S T heS heT).2.2.1]
      · congr 1
        apply bitsExpectation_congr
        intro T hT
        have heT : e ∉ T := fun ht => heW (hT ht)
        rw [run_query_yes _ _ _ _ heS, (hybrid_query e no yes S T heS heT).2.2.2]
    have hOuter := bitsExpectation_insert q W e heW
      (fun S => bitsExpectation q V (fun T => φ ((RevealTree.query e no yes).run S) *
        ψ ((RevealTree.query e no yes).hybrid S T)))
    rw [hWV, hNo, hYes] at hOuter
    rw [hOuter, ihn W hn ψ, ihn W hn (fun S => ψ (insert e S)),
      ihy W hy ψ, ihy W hy (fun S => ψ (insert e S)), mean_run_query q V e no yes φ he]
    have hPsi := bitsExpectation_insert q W e heW ψ
    rw [hWV] at hPsi
    rw [hPsi]
    ring

lemma RevealTree.hybrid_eq_resample (tree : RevealTree α β) (V S T : Finset α)
    (fresh : tree.Fresh V) (hS : S ⊆ V) (hT : T ⊆ V) :
    tree.hybrid S T = (S \ tree.queried S) ∪ (T ∩ tree.queried S) := by
  induction tree generalizing V S T with
  | leaf value => simp [hybrid, queried]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have hSerase : S.erase e ⊆ V.erase e := erase_subset_erase e hS
    have hTerase : T.erase e ⊆ V.erase e := erase_subset_erase e hT
    by_cases heS : e ∈ S
    · have hq := yes.queried_subset (V.erase e) (S.erase e) hy
      have heq : e ∉ yes.queried (S.erase e) := fun h => notMem_erase e V (hq h)
      have hi := ihy (V.erase e) (S.erase e) (T.erase e) hy hSerase hTerase
      simp only [hybrid, queried, ite_eq_left heS, hi]
      by_cases heT : e ∈ T
      · rw [ite_eq_left heT]
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS, heT, heq]
        · simp [hxe]
      · rw [ite_eq_right heT]
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS, heT, heq]
        · simp [hxe]
    · have hq := no.queried_subset (V.erase e) (S.erase e) hn
      have heq : e ∉ no.queried (S.erase e) := fun h => notMem_erase e V (hq h)
      have hi := ihn (V.erase e) (S.erase e) (T.erase e) hn hSerase hTerase
      simp only [hybrid, queried, ite_eq_right heS, hi]
      by_cases heT : e ∈ T
      · rw [ite_eq_left heT]
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS, heT]
        · simp [hxe]
      · rw [ite_eq_right heT]
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS, heT]
        · simp [hxe]

lemma RevealTree.double_event (tree : RevealTree α β) (q : α → ℝ) (V : Finset α)
    (fresh : tree.Fresh V) (event : β → Prop) [DecidablePred event] :
    bitsExpectation q V (fun S => bitsExpectation q V (fun T =>
      (if event (tree.run S) then 1 else 0) *
        (if event (tree.run (tree.hybrid S T)) then 1 else 0))) =
      (bitsExpectation q V (fun S => if event (tree.run S) then 1 else 0)) ^ 2 := by
  rw [tree.hybrid_independent q V fresh (fun b => if event b then 1 else 0)
    (fun S => if event (tree.run S) then 1 else 0)]
  ring

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma bitsExpectation_comm (p : α → ℝ) (q : β → ℝ) (U : Finset α) (V : Finset β)
    (f : Finset α → Finset β → ℝ) :
    bitsExpectation p U (fun S => bitsExpectation q V (f S)) =
      bitsExpectation q V (fun T => bitsExpectation p U (fun S => f S T)) := by
  simp only [bitsExpectation, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  apply sum_congr rfl
  intro S hS
  ring

lemma bitsExpectation_disjoint_union (q : α → ℝ) (U V : Finset α) (hUV : Disjoint U V)
    (f : Finset α → ℝ) :
    bitsExpectation q (U ∪ V) f =
      bitsExpectation q U (fun S => bitsExpectation q V (fun T => f (S ∪ T))) := by
  induction U using Finset.induction_on generalizing f with
  | empty => simp only [empty_union, bitsExpectation_empty]
  | @insert e U he ih =>
    have heV : e ∉ V := fun hx => (Finset.disjoint_left.mp hUV (mem_insert_self e U) hx)
    have hU : Disjoint U V := hUV.mono_left (subset_insert e U)
    rw [insert_union, bitsExpectation_insert q (U ∪ V) e (by simp [he, heV]),
      bitsExpectation_insert q U e he, ih hU f, ih hU (fun S => f (insert e S))]
    simp only [insert_union]

lemma bitsExpectation_split (q : α → ℝ) (V U : Finset α) (hU : U ⊆ V)
    (f : Finset α → ℝ) :
    bitsExpectation q V f =
      bitsExpectation q (V \ U) (fun S => bitsExpectation q U (fun T => f (S ∪ T))) := by
  have heq : (V \ U) ∪ U = V := sdiff_union_of_subset hU
  rw [← bitsExpectation_disjoint_union q (V \ U) U sdiff_disjoint f, heq]

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

lemma conditionalRank_union_chain (M : Matroid α) (A B P : Set α) :
    conditionalRank M (A ∪ B) P =
      conditionalRank M A P + conditionalRank M B (P ∪ A) := by
  have hA := conditionalRank_add_base M A P
  have hB := conditionalRank_add_base M B (P ∪ A)
  have hAB := conditionalRank_add_base M (A ∪ B) P
  have heq : B ∪ (P ∪ A) = (A ∪ B) ∪ P := by ext x; simp only [Set.mem_union]; tauto
  rw [heq] at hB
  rw [union_comm A P] at hA
  omega

lemma conditionalRank_subset_witness (M : Matroid α) (K P A : Set α)
    (hK : conditionalRank M K P = K.ncard) (hAK : A ⊆ K) :
    conditionalRank M A P = A.ncard := by
  have hu : A ∪ (K \ A) = K := by
    ext e
    constructor
    · rintro (he | he)
      · exact hAK he
      · exact he.1
    · intro he
      by_cases ha : e ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨he, ha⟩
  have hc := conditionalRank_union_chain M A (K \ A) P
  rw [hu, hK] at hc
  have hd := (conditionalRank_le_rank M (K \ A) (P ∪ A)).trans (natRank_le_ncard M (K \ A))
  have ha := (conditionalRank_le_rank M A P).trans (natRank_le_ncard M A)
  have hn := Set.ncard_sdiff_add_ncard_of_subset hAK
  omega

lemma exists_conditionalRank_witness (M : Matroid α) (hE : M.E = Set.univ) (S P : Set α) :
    ∃ K : Set α, K ⊆ S ∧ conditionalRank M K P = K.ncard ∧
      K.ncard = conditionalRank M S P := by
  obtain ⟨K, hK, hgen, hcard⟩ := exists_extension_generators M hE (M.closure P) S
    (M.closure (M.closure P ∪ S)) (Matroid.isFlat_closure (M := M) P) rfl
  have hrS : K.ncard + natRank M P = natRank M (S ∪ P) := by
    simpa only [natRank, M.eRk_closure_eq, M.eRk_union_closure_left_eq, union_comm P S] using hcard
  have hrK : natRank M (K ∪ P) = natRank M (S ∪ P) := by
    have hh := congrArg (natRank M) hgen
    simpa only [natRank, M.eRk_closure_eq, M.eRk_union_closure_left_eq, union_comm P K,
      union_comm P S] using hh
  refine ⟨K, fun _ he => (hK he).1, ?_, ?_⟩ <;> unfold conditionalRank <;> omega

theorem independent_thinning_rank [DecidableEq α] (M : Matroid α) (hE : M.E = Set.univ)
    (V S : Finset α) (hSV : S ⊆ V) (P : Set α) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (conditionalRank M (S : Set α) P : ℝ) ≤
      bitsExpectation (fun _ => t) V (fun T => (conditionalRank M ((S ∩ T : Finset α) : Set α) P : ℝ)) := by
  classical
  obtain ⟨K, hKS, hKrank, hKcard⟩ := exists_conditionalRank_witness M hE (S : Set α) P
  let KF := K.toFinset
  have hKF : KF ⊆ V := fun e he => hSV (hKS (by simpa [KF] using he))
  have hpoint (T : Finset α) : ((KF ∩ T).card : ℝ) ≤
      (conditionalRank M ((S ∩ T : Finset α) : Set α) P : ℝ) := by
    have hw := conditionalRank_subset_witness M K P ((KF ∩ T : Finset α) : Set α) hKrank
      (by intro e he; exact (by simpa [KF] using (mem_inter.mp he).1))
    have hm := conditionalRank_mono_left M P
      (show ((KF ∩ T : Finset α) : Set α) ⊆ ((S ∩ T : Finset α) : Set α) from by
        intro e he
        rcases mem_inter.mp he with ⟨heK, heT⟩
        exact mem_inter.mpr ⟨hKS (by simpa [KF] using heK), heT⟩)
    rw [hw, Set.ncard_coe_finset] at hm
    exact_mod_cast hm
  have hm := bitsExpectation_mono (fun _ : α => t) (fun _ => ht0) (fun _ => ht1)
    V (fun T _ => hpoint T)
  rw [bitsExpectation_card_inter _ V KF hKF] at hm
  have hcardKF : KF.card = conditionalRank M (S : Set α) P := by
    change K.toFinset.card = _
    rw [← Set.ncard_eq_toFinset_card', hKcard]
  simpa only [sum_const, nsmul_eq_mul, hcardKF, mul_comm] using hm

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem conditionally_independent_thinning_rank
    (M : Matroid α) (hE : M.E = Set.univ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (V G : Finset α) (hG : G ⊆ V) (S : Set α) (hS : S ⊆ (G : Set α))
    (P : Finset α → Set α)
    (hP : ∀ A B : Finset α, B ⊆ G → P (A ∪ B) = P A) :
    t * bitsExpectation (fun _ => t) V (fun T => (conditionalRank M S (P T) : ℝ)) ≤
      bitsExpectation (fun _ => t) V
        (fun T => (conditionalRank M (S ∩ (T : Set α)) (P T) : ℝ)) := by
  classical
  have heq : bitsExpectation (fun _ => t) V (fun T => (conditionalRank M S (P T) : ℝ)) =
      bitsExpectation (fun _ => t) (V \ G) (fun A => (conditionalRank M S (P A) : ℝ)) := by
    rw [bitsExpectation_split (fun _ => t) V G hG]
    apply bitsExpectation_congr
    intro A hA
    calc
      _ = bitsExpectation (fun _ => t) G (fun _ => (conditionalRank M S (P A) : ℝ)) := by
        apply bitsExpectation_congr
        intro B hB
        rw [hP A B hB]
      _ = _ := bitsExpectation_const _ _ _
  rw [heq, ← bitsExpectation_mul_left, bitsExpectation_split (fun _ => t) V G hG]
  apply bitsExpectation_mono _ (fun _ => ht0) (fun _ => ht1)
  intro A hA
  have hdis : S ∩ (A : Set α) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro e ⟨heS, heA⟩
    exact (Finset.mem_sdiff.mp (hA heA)).2 (hS heS)
  have hb := independent_thinning_rank M hE G S.toFinset
    (fun e he => hS (by simpa only [Set.mem_toFinset] using he)) (P A) t ht0 ht1
  calc
    _ ≤ bitsExpectation (fun _ => t) G
        (fun B => (conditionalRank M (S ∩ (B : Set α)) (P A) : ℝ)) := by simpa only [Finset.coe_inter, Set.coe_toFinset] using hb
    _ = _ := by
      apply bitsExpectation_congr
      intro B hB
      rw [hP A B hB]
      have hset : S ∩ ((A ∪ B : Finset α) : Set α) = S ∩ (B : Set α) := by
        rw [Finset.coe_union, Set.inter_union_distrib_left, hdis, Set.empty_union]
      rw [hset]

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
lemma lowerCompetition_congr_test_before (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T T' : ℕ → Set α) (b : ℤ) (h : ℕ)
    (hT : ∀ j < h, T j = T' j) :
    lowerCompetition M hE κ D C T b h = lowerCompetition M hE κ D C T' b h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [lowerCompetition]
    rw [ih (fun j hj => hT j (by omega)), hT h (by omega)]

lemma lowerCompetition_ignore_focal (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (b : ℤ) (h : ℕ)
    (A B : Finset α) (hB : B ⊆ G h) :
    lowerCompetition M hE κ D C (fun j => ((A ∪ B : Finset α) : Set α) ∩ (G j : Set α)) b h =
      lowerCompetition M hE κ D C (fun j => (A : Set α) ∩ (G j : Set α)) b h := by
  apply lowerCompetition_congr_test_before
  intro j hj
  ext e
  have hd := Finset.disjoint_left.mp (hG (show h ≠ j by omega))
  simp only [Finset.coe_union, Set.mem_inter_iff, Set.mem_union, Finset.mem_coe]
  constructor
  · rintro ⟨ha | hb, hg⟩
    · exact ⟨ha, hg⟩
    · exact False.elim (hd (hB hb) hg)
  · rintro ⟨ha, hg⟩
    exact ⟨Or.inl ha, hg⟩

noncomputable def testRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U O test : Set α) (ε : Fin 2) : ℕ :=
  ∑ b : ParityWindow (activation h) ε,
    conditionalRank M ((nominalLayerSet M hE κ D C h U ε b \ O) ∩ test)
      (nominalPath M hE κ D C h (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)

noncomputable def finalRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h final : ℕ) (U O test : Set α) (ε : Fin 2) : ℕ :=
  ∑ b : ParityWindow (activation h) ε,
    conditionalRank M ((nominalLayerSet M hE κ D C h U ε b \ O) ∩ test)
      (guardedPath M hE κ D C final (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)

theorem thinning_nominalRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h : ℕ) (O : Set α) (ε : Fin 2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * bitsExpectation (fun _ : α => t) univ (fun T =>
      (nominalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h (G h) O ε : ℝ)) ≤
    bitsExpectation (fun _ : α => t) univ (fun T =>
      (testRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h (G h) O (T : Set α) ε : ℝ)) := by
  simp only [nominalRankStatistic, testRankStatistic, Nat.cast_sum, bitsExpectation_sum, mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  apply conditionally_independent_thinning_rank M hE t ht0 ht1 univ (G h) (subset_univ _)
  · exact fun e he => (nominalLayerSet_subset M hE κ D C h (G h) ε b he.1)
  · intro A B hB
    rw [lowerCompetition_ignore_focal M hE κ D C G hG b.val.val h A B hB]

omit [DecidableEq α] in
lemma unobservedBirthRegion_eq_nominalLayer (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U O : Set α) (ε : Fin 2)
    (b : ParityWindow (activation h) ε) :
    unobservedBirthRegion M hE κ D C U O h b.val.val =
      nominalLayerSet M hE κ D C h U ε b \ O := by
  classical
  ext e
  unfold unobservedBirthRegion nominalLayerSet
  by_cases ha : activation h+2 ≤ b.val.val
  · rw [ite_eq_left ha]
    constructor
    · rintro ⟨⟨hu, hx, hn⟩, ho⟩
      have hb : b.val.val ≤ 0 := by
        by_contra hb
        have heq := nominalPath_nonnegative M hE κ D C h (show 0 ≤ b.val.val-1 by omega)
        rw [heq] at hn
        exact hn (Set.mem_univ e)
      exact ⟨⟨hu, ha, hb, hx, hn⟩, ho⟩
    · rintro ⟨⟨hu, _, _, hx, hn⟩, ho⟩
      exact ⟨⟨hu, hx, hn⟩, ho⟩
  · rw [ite_eq_right ha]
    simp only [Set.mem_empty_iff_false, Set.mem_sdiff, Set.mem_ofPred_eq, false_iff,
      not_and]
    intro he
    exact (ha he.2.1).elim

theorem testRankStatistic_le_final_cost
    {α : Type u_1} [Fintype α] [DecidableEq α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h later : ℕ)
    (U O test : Set α) (ε : Fin 2) :
    κ * testRankStatistic M hE κ D C T h U O test ε ≤
      κ * finalRankStatistic M hE κ D C T h (h+1+later) U O test ε +
        κ * (C h).ncard +
          ∑ j ∈ range later, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
  let S : ℤ → Set α := fun b => unobservedBirthRegion M hE κ D C U O h b ∩ test
  have hc := actual_path_rank_cost_finset M hE κ hκ D C T h later
    (parityPoints (activation h) ε) (activation h-4) 1
    (by dsimp [activation]; omega)
    (by intro b hb; have := (mem_parityPoints _ _ _).mp hb; omega)
    (by intro b hb; exact ((mem_parityPoints _ _ _).mp hb).2.1)
    (by
      intro b hb c hc hbc
      have hbm := ((mem_parityPoints _ _ _).mp hb).2.2
      have hcm := ((mem_parityPoints _ _ _).mp hc).2.2
      omega)
    S (fun b e he => unobservedBirthRegion_subset M hE κ D C U O h b he.1)
  rw [sum_parityPoints, sum_parityPoints] at hc
  have hS (b : ParityWindow (activation h) ε) : S b.val.val =
      (nominalLayerSet M hE κ D C h U ε b \ O) ∩ test := by
    dsimp [S]
    rw [unobservedBirthRegion_eq_nominalLayer M hE κ D C h U O ε b]
  simp_rw [hS] at hc
  exact hc

theorem thinning_finalRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h final : ℕ) (O : Set α) (ε : Fin 2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * bitsExpectation (fun _ : α => t) univ (fun T =>
      (finalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h final
        (G h) O Set.univ ε : ℝ)) ≤
    bitsExpectation (fun _ : α => t) univ (fun T =>
      (finalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h final
        (G h) O (T : Set α) ε : ℝ)) := by
  simp only [finalRankStatistic, Set.inter_univ, Nat.cast_sum, bitsExpectation_sum, mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  apply conditionally_independent_thinning_rank M hE t ht0 ht1 univ (G h) (subset_univ _)
  · exact fun e he => (nominalLayerSet_subset M hE κ D C h (G h) ε b he.1)
  · intro A B hB
    rw [lowerCompetition_ignore_focal M hE κ D C G hG b.val.val h A B hB]

theorem expected_nominal_to_final (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h later : ℕ) (O : Set α) (ε : Fin 2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (κ:ℝ) * t * bitsExpectation (fun _ : α => t) univ (fun T =>
      (nominalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h (G h) O ε : ℝ)) ≤
    (κ:ℝ) * bitsExpectation (fun _ : α => t) univ (fun T =>
      (finalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h
        (h+1+later) (G h) O (T : Set α) ε : ℝ)) +
      t * (κ * (C h).ncard + ∑ j ∈ range later,
        (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) : ℕ) := by
  have ht := thinning_finalRankStatistic M hE κ D C G hG h (h+1+later) O ε t ht0 ht1
  have hp (T : Finset α) :
      (κ:ℝ) * (nominalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α))
        h (G h) O ε : ℝ) ≤
      (κ:ℝ) * (finalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α))
        h (h+1+later) (G h) O Set.univ ε : ℝ) +
        (κ * (C h).ncard + ∑ j ∈ range later,
          (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) : ℕ) := by
    have hn := testRankStatistic_le_final_cost M hE κ hκ D C
      (fun j => (T : Set α) ∩ (G j : Set α)) h later (G h) O Set.univ ε
    have htest : testRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α))
        h (G h) O Set.univ ε = nominalRankStatistic M hE κ D C
        (fun j => (T : Set α) ∩ (G j : Set α)) h (G h) O ε := by
      simp only [testRankStatistic, nominalRankStatistic, Set.inter_univ]
    rw [htest, Nat.add_assoc] at hn
    exact_mod_cast hn
  have hm := bitsExpectation_mono (fun _ : α => t) (fun _ => ht0) (fun _ => ht1)
    univ (fun T _ => hp T)
  simp only [bitsExpectation_add, bitsExpectation_mul_left, bitsExpectation_const] at hm
  have hs := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg κ : (0:ℝ) ≤ κ)
  have hc := mul_le_mul_of_nonneg_left hm ht0
  nlinarith

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset Pivots
variable {n : ℕ}

noncomputable def pathGroups (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (h : ℕ) : Finset (Fin n) := by
  classical
  exact (groupMask M d w univ h).toFinset

lemma pathGroups_coe (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (h : ℕ) :
    (pathGroups M d w h : Set (Fin n)) = groupMask M d w univ h := by
  classical
  exact Set.coe_toFinset _

lemma groupMask_eq_inter (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) (h : ℕ) :
    groupMask M d w mask h = (mask : Set (Fin n)) ∩ (pathGroups M d w h : Set (Fin n)) := by
  classical
  rw [pathGroups_coe]
  ext e
  simp [groupMask]

lemma pathGroups_disjoint (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) : Pairwise (fun i j => Disjoint (pathGroups M d w i) (pathGroups M d w j)) := by
  classical
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have heI : e ∈ groupMask M d w univ i := by simpa only [pathGroups, Set.mem_toFinset] using hei
  have heJ : e ∈ groupMask M d w univ j := by simpa only [pathGroups, Set.mem_toFinset] using hej
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp heI.2.1.1
  have hi := (groups_index_of_get M d w (heI.2.2.symm.trans hk)).2
  have hj := (groups_index_of_get M d w (heJ.2.2.symm.trans hk)).2
  exact hij (hi.symm.trans hj)

noncomputable def listedLambda (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) : ℕ :=
  finalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w d.T) h (groups M d w).length (groupMask M d w univ h)
    ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (d.T : Set (Fin n)) (boolParity d.odd)

noncomputable def listedZ (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) : ℕ :=
  nominalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w d.T) h (groupMask M d w univ h)
    ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd)

noncomputable def trueLambda (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) : ℕ := by
  classical
  exact if i ∈ groups M d w then listedLambda M hE d w ((groups M d w).idxOf i) else 0

noncomputable def trueZ (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) : ℕ := by
  classical
  exact if i ∈ groups M d w then listedZ M hE d w ((groups M d w).idxOf i) else 0

theorem listedLambda_le_count (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n) (h : ℕ) :
    listedLambda M hE d w h ≤
      ((selection M hE d w π).filter (fun e =>
        ∃ i, w e = some i ∧ h ≤ (groups M d w).idxOf i)).card := by
  classical
  have hc := selection_cumulative_rank M hE d w π h
    (parityPoints (activation h) (boolParity d.odd)) (by
      intro b hb
      have hm := ((mem_parityPoints _ _ _).mp hb).2.2
      rwa [boolParity_val] at hm)
  rw [sum_parityPoints] at hc
  have hreg (b : ParityWindow (activation h) (boolParity d.odd)) :
      groupBirthRegion M hE d w h b.val.val =
        nominalLayerSet M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
          h (groupMask M d w univ h) (boolParity d.odd) b \
          ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) :=
    unobservedBirthRegion_eq_nominalLayer M hE (2^100) _ _ h _ _ _ b
  simp_rw [hreg] at hc
  exact hc

theorem trueLambda_le_count (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n) (i : ℤ) :
    trueLambda M hE d w i ≤
      ((selection M hE d w π).filter (fun e => ∃ j, w e = some j ∧ i ≤ j)).card := by
  classical
  unfold trueLambda
  split_ifs with hi
  · apply (listedLambda_le_count M hE d w π _).trans
    apply Finset.card_le_card
    intro e he
    obtain ⟨hea, j, hwj, hij⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨hea, j, hwj, ?_⟩
    have hel := layerGreedy_subset M _ _ _ _ hea
    obtain ⟨k, hwk, hek, _⟩ := (assign_spec M hE d w e _ _).mp
      (assigned_some_of_eligible (assign M hE d w) w e hel)
    have hjk : j = k := Option.some.inj (hwj.symm.trans hwk)
    have hj : j ∈ groups M d w := hjk ▸ hek.2.2.1
    by_contra hn
    have hlt := (groups_idxOf_lt_iff M d w j i hj hi).mpr (by omega)
    omega
  · exact Nat.zero_le _

end MatroidProphet.MainAlgorithm

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def trueGroup (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) : Finset (Fin n) :=
  univ.filter fun e => candidate M d s e (s e) ∧ s e = some i

@[simp] lemma mem_trueGroup (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (e : Fin n) :
    e ∈ trueGroup M d s i ↔ candidate M d s e (s e) ∧ s e = some i := by
  simp [trueGroup]

lemma trueGroup_disjoint (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) : Pairwise (fun i j => Disjoint (trueGroup M d s i) (trueGroup M d s j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro e hei hej
  exact hij (Option.some.inj (((mem_trueGroup M d s i e).mp hei).2.symm.trans
    ((mem_trueGroup M d s j e).mp hej).2))

lemma trueGroup_disjoint_H (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) : Disjoint (trueGroup M d s i) d.H := by
  apply disjoint_left.mpr
  intro e he hh
  exact ((mem_trueGroup M d s i e).mp he).1.2.1 hh

lemma mem_listed_iff (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) :
    i ∈ listed M d s ↔ ∃ e ∈ d.D, e ∈ trueGroup M d s i := by
  simp only [listed, mem_biUnion, mem_trueGroup]
  constructor
  · rintro ⟨e, he, hi⟩
    by_cases hc : candidate M d s e (s e)
    · simp only [ite_eq_left hc, Option.mem_toFinset] at hi
      exact ⟨e, he, hc, hi⟩
    · simp only [ite_eq_right hc, Finset.notMem_empty] at hi
  · rintro ⟨e, he, hc, hi⟩
    exact ⟨e, he, by rw [ite_eq_left hc]; simp [hi]⟩

def withMasks (d : MainMasks n) (A B C : Finset (Fin n)) : MainMasks n :=
  { d with D := A, C := B, T := C }

@[simp] lemma candidate_withMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (A B C : Finset (Fin n)) (s : Fin n → Option ℤ) (e : Fin n) (v : Option ℤ) :
    candidate M (withMasks d A B C) s e v ↔ candidate M d s e v := Iff.rfl

@[simp] lemma trueGroup_withMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (A B C : Finset (Fin n)) (s : Fin n → Option ℤ) (i : ℤ) :
    trueGroup M (withMasks d A B C) s i = trueGroup M d s i := rfl

lemma groups_withMasks_guards (M : Matroid (Fin n)) (d : MainMasks n)
    (A B C B' C' : Finset (Fin n)) (s : Fin n → Option ℤ) :
    groups M (withMasks d A B C) s = groups M (withMasks d A B' C') s := rfl

def focalMasks (d : MainMasks n) (U A B C : Finset (Fin n)) : MainMasks n :=
  { d with D := (d.D \ U) ∪ A, C := (d.C \ U) ∪ B, T := (d.T \ U) ∪ C }

@[simp] lemma candidate_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (U A B C : Finset (Fin n)) (s : Fin n → Option ℤ) (e : Fin n) (v : Option ℤ) :
    candidate M (focalMasks d U A B C) s e v ↔ candidate M d s e v := Iff.rfl

@[simp] lemma trueGroup_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (U A B C : Finset (Fin n)) (s : Fin n → Option ℤ) (i : ℤ) :
    trueGroup M (focalMasks d U A B C) s i = trueGroup M d s i := rfl

lemma listed_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) :
    listed M (focalMasks d (trueGroup M d s i) A B C) s =
      (listed M d s \ {i}) ∪ (if A.Nonempty then {i} else ∅) := by
  ext j
  rw [mem_listed_iff]
  simp only [focalMasks, mem_union, mem_sdiff,
    mem_singleton, mem_listed_iff]
  by_cases hne : A.Nonempty
  · simp only [ite_eq_left hne, mem_singleton]
    constructor
    · rintro ⟨e, he | he, hej⟩
      · refine Or.inl ⟨⟨e, he.1, hej⟩, ?_⟩
        intro hji
        exact he.2 (hji ▸ hej)
      · exact Or.inr (Option.some.inj
          (((mem_trueGroup M d s j e).mp hej).2.symm.trans
            ((mem_trueGroup M d s i e).mp (hA he)).2))
    · rintro (⟨⟨e, heD, hej⟩, hji⟩ | rfl)
      · refine ⟨e, Or.inl ⟨heD, ?_⟩, hej⟩
        intro hei
        exact hji (Option.some.inj
          (((mem_trueGroup M d s j e).mp hej).2.symm.trans
            ((mem_trueGroup M d s i e).mp hei).2))
      · obtain ⟨e, he⟩ := hne
        exact ⟨e, Or.inr he, hA he⟩
  · simp only [ite_eq_right hne, Finset.notMem_empty, or_false]
    constructor
    · rintro ⟨e, he | he, hej⟩
      · refine ⟨⟨e, he.1, hej⟩, ?_⟩
        intro hji
        exact he.2 (hji ▸ hej)
      · exact False.elim (hne ⟨e, he⟩)
    · rintro ⟨⟨e, heD, hej⟩, hji⟩
      refine ⟨e, Or.inl ⟨heD, ?_⟩, hej⟩
      intro hei
      exact hji (Option.some.inj
        (((mem_trueGroup M d s j e).mp hej).2.symm.trans
          ((mem_trueGroup M d s i e).mp hei).2))

noncomputable def focalReference (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) : MainMasks n :=
  focalMasks d (trueGroup M d s i) (trueGroup M d s i) ∅ ∅

lemma groups_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty) :
    groups M (focalMasks d (trueGroup M d s i) A B C) s =
      groups M (focalReference M d s i) s := by
  have hU : (trueGroup M d s i).Nonempty := hne.mono hA
  unfold groups focalReference
  rw [listed_focalMasks M d s i A B C hA,
    listed_focalMasks M d s i _ ∅ ∅ Subset.rfl, ite_eq_left hne, ite_eq_left hU]

lemma focal_mem_reference_groups (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (hU : (trueGroup M d s i).Nonempty) :
    i ∈ groups M (focalReference M d s i) s := by
  rw [mem_groups]
  unfold focalReference
  rw [listed_focalMasks M d s i _ ∅ ∅ Subset.rfl, ite_eq_left hU]
  exact mem_union_right _ (mem_singleton_self i)

lemma groupMask_at_key (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (mask : Finset (Fin n)) (h : ℕ) (i : ℤ)
    (hi : (groups M d s)[h]? = some i) :
    groupMask M d s mask h = ((mask ∩ trueGroup M d s i : Finset (Fin n)) : Set (Fin n)) := by
  ext e
  simp only [groupMask, Set.mem_ofPred_eq, Finset.mem_coe, mem_inter, mem_trueGroup, hi]

lemma replaceMask_inter_self (X U A : Finset (Fin n)) (hA : A ⊆ U) :
    ((X \ U) ∪ A) ∩ U = A := by
  ext e
  simp only [mem_inter, mem_union, mem_sdiff]
  constructor
  · rintro ⟨he | he, heU⟩
    · exact False.elim (he.2 heU)
    · exact he
  · intro he
    exact ⟨Or.inr he, hA he⟩

lemma replaceMask_inter_other (X U A V : Finset (Fin n))
    (hA : A ⊆ U) (hUV : Disjoint U V) :
    ((X \ U) ∪ A) ∩ V = X ∩ V := by
  ext e
  simp only [mem_inter, mem_union, mem_sdiff]
  constructor
  · rintro ⟨he | he, heV⟩
    · exact ⟨he.1, heV⟩
    · exact False.elim (disjoint_left.mp hUV (hA he) heV)
  · rintro ⟨heX, heV⟩
    exact ⟨Or.inl ⟨heX, fun heU => disjoint_left.mp hUV heU heV⟩, heV⟩

noncomputable def focalIndex (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) : ℕ :=
  (groups M (focalReference M d s i) s).idxOf i

lemma focal_group_key (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty) :
    (groups M (focalMasks d (trueGroup M d s i) A B C) s)[focalIndex M d s i]? = some i := by
  rw [groups_focalMasks M d s i A B C hA hne]
  exact groups_get?_idxOf M _ s i (focal_mem_reference_groups M d s i (hne.mono hA))

lemma focal_group_mask (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C X Y : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty)
    (hY : Y ⊆ trueGroup M d s i) :
    groupMask M (focalMasks d (trueGroup M d s i) A B C) s
      ((X \ trueGroup M d s i) ∪ Y) (focalIndex M d s i) = (Y : Set (Fin n)) := by
  rw [groupMask_at_key M _ s _ _ i (focal_group_key M d s i A B C hA hne),
    trueGroup_focalMasks, replaceMask_inter_self X _ Y hY]

lemma lower_group_mask (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C X Y Z : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty)
    (hY : Y ⊆ trueGroup M d s i) (hZ : Z ⊆ trueGroup M d s i)
    (j : ℕ) (hj : j < focalIndex M d s i) :
    groupMask M (focalMasks d (trueGroup M d s i) A B C) s
      ((X \ trueGroup M d s i) ∪ Y) j =
    groupMask M (focalReference M d s i) s
      ((X \ trueGroup M d s i) ∪ Z) j := by
  have hi := groups_get?_idxOf M (focalReference M d s i) s i
    (focal_mem_reference_groups M d s i (hne.mono hA))
  obtain ⟨k, hk, hki⟩ := groups_earlier_key M (focalReference M d s i) s hi hj
  have hk' : (groups M (focalMasks d (trueGroup M d s i) A B C) s)[j]? = some k := by
    rwa [groups_focalMasks M d s i A B C hA hne]
  have hdisj := trueGroup_disjoint M d s (ne_of_gt hki)
  rw [groupMask_at_key M _ s _ j k hk', groupMask_at_key M _ s _ j k hk]
  simp only [focalReference, trueGroup_focalMasks]
  rw [replaceMask_inter_other X _ Y _ hY hdisj,
    replaceMask_inter_other X _ Z _ hZ hdisj]

end MatroidProphet.MainAlgorithm

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

lemma guardedPath_congr_prefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C D' C' : ℕ → Set α) (h : ℕ)
    (hD : ∀ j < h, D j = D' j) (hC : ∀ j < h, C j = C' j) (k : ℤ) :
    guardedPath M hE κ D C h k = guardedPath M hE κ D' C' h k := by
  induction h generalizing k with
  | zero => rfl
  | succ h ih =>
    simp only [guardedPath, hD h (Nat.lt_succ_self h), hC h (Nat.lt_succ_self h),
      ih (fun j hj => hD j (Nat.lt_succ_of_lt hj)) (fun j hj => hC j (Nat.lt_succ_of_lt hj))]

lemma nominalPath_congr_prefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C D' C' : ℕ → Set α) (h : ℕ)
    (hD : ∀ j ≤ h, D j = D' j) (hC : ∀ j < h, C j = C' j) (k : ℤ) :
    nominalPath M hE κ D C h k = nominalPath M hE κ D' C' h k := by
  rw [nominalPath, nominalPath, hD h le_rfl,
    guardedPath_congr_prefix M hE κ D C D' C' h (fun j hj => hD j hj.le) hC k]

lemma lowerCompetition_congr_prefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T D' C' T' : ℕ → Set α) (h : ℕ)
    (hD : ∀ j < h, D j = D' j) (hC : ∀ j < h, C j = C' j)
    (hT : ∀ j < h, T j = T' j) (k : ℤ) :
    lowerCompetition M hE κ D C T k h = lowerCompetition M hE κ D' C' T' k h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [lowerCompetition, lowerCompetition, hT h (Nat.lt_succ_self h),
      ih (fun j hj => hD j (Nat.lt_succ_of_lt hj)) (fun j hj => hC j (Nat.lt_succ_of_lt hj))
        (fun j hj => hT j (Nat.lt_succ_of_lt hj)),
      nominalPath_congr_prefix M hE κ D C D' C' h
        (fun j hj => hD j (Nat.lt_succ_of_le hj)) (fun j hj => hC j (Nat.lt_succ_of_lt hj)),
      nominalPath_congr_prefix M hE κ D C D' C' h
        (fun j hj => hD j (Nat.lt_succ_of_le hj)) (fun j hj => hC j (Nat.lt_succ_of_lt hj))]

namespace MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma focal_prefix_masks (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) (hne : A.Nonempty)
    (j : ℕ) (hj : j < focalIndex M d s i) :
    let f := focalMasks d (trueGroup M d s i) A B C
    let r := focalReference M d s i
    groupMask M f s f.D j = groupMask M r s r.D j ∧
    groupMask M f s f.C j = groupMask M r s r.C j ∧
    groupMask M f s f.T j = groupMask M r s r.T j := by
  exact ⟨lower_group_mask M d s i A B C d.D A _ hA hne hA Finset.Subset.rfl j hj,
    lower_group_mask M d s i A B C d.C B ∅ hA hne hB (empty_subset _) j hj,
    lower_group_mask M d s i A B C d.T C ∅ hA hne hC (empty_subset _) j hj⟩

lemma focal_incoming_path (M : Matroid (Fin n)) (hE : M.E = Set.univ) (κ : ℕ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) (hne : A.Nonempty) (k : ℤ) :
    let f := focalMasks d (trueGroup M d s i) A B C
    let r := focalReference M d s i
    guardedPath M hE κ (groupMask M f s f.D) (groupMask M f s f.C) (focalIndex M d s i) k =
      guardedPath M hE κ (groupMask M r s r.D) (groupMask M r s r.C) (focalIndex M d s i) k := by
  apply guardedPath_congr_prefix
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).1
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).2.1

lemma focal_lowerCompetition (M : Matroid (Fin n)) (hE : M.E = Set.univ) (κ : ℕ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) (hne : A.Nonempty) (k : ℤ) :
    let f := focalMasks d (trueGroup M d s i) A B C
    let r := focalReference M d s i
    lowerCompetition M hE κ (groupMask M f s f.D) (groupMask M f s f.C)
        (groupMask M f s f.T) k (focalIndex M d s i) =
      lowerCompetition M hE κ (groupMask M r s r.D) (groupMask M r s r.C)
        (groupMask M r s r.T) k (focalIndex M d s i) := by
  apply lowerCompetition_congr_prefix
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).1
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).2.1
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).2.2

lemma focal_nominal_path (M : Matroid (Fin n)) (hE : M.E = Set.univ) (κ : ℕ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) (hne : A.Nonempty) (k : ℤ) :
    let f := focalMasks d (trueGroup M d s i) A B C
    let r := focalReference M d s i
    nominalPath M hE κ (groupMask M f s f.D) (groupMask M f s f.C) (focalIndex M d s i) k =
      densityEnabled M hE κ (A : Set (Fin n)) (activation (focalIndex M d s i)) k
        (guardedPath M hE κ (groupMask M r s r.D) (groupMask M r s r.C) (focalIndex M d s i) k) := by
  dsimp only
  rw [nominalPath, focal_incoming_path M hE κ d s i A B C hA hB hC hne k]
  congr 1
  exact focal_group_mask M d s i A B C d.D A hA hne hA

lemma focal_observed_inter (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i) :
    let f := focalMasks d (trueGroup M d s i) A B C
    (f.H ∪ f.D ∪ f.C) ∩ trueGroup M d s i = A ∪ B := by
  dsimp only [focalMasks]
  rw [Finset.union_inter_distrib_right, Finset.union_inter_distrib_right,
    disjoint_iff_inter_eq_empty.mp (trueGroup_disjoint_H M d s i).symm,
    replaceMask_inter_self _ _ _ hA, replaceMask_inter_self _ _ _ hB, Finset.empty_union]

lemma focal_listed_iff_nonempty (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) :
    i ∈ groups M (focalMasks d (trueGroup M d s i) A B C) s ↔ A.Nonempty := by
  rw [mem_groups, listed_focalMasks M d s i A B C hA]
  by_cases hne : A.Nonempty <;> simp [hne]

noncomputable def listedSafeStatistic (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (ε : Fin 2) : ℕ :=
  if i ∈ groups M d s then
    safeLayerStatistic M hE κ (groupMask M d s d.D) (groupMask M d s d.C)
      (groupMask M d s d.T) ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
      ((d.D : Set (Fin n)) ∩ Y) ε
  else 0

noncomputable def listedRankStatistic (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (ε : Fin 2) : ℕ :=
  if i ∈ groups M d s then
    nominalRankStatistic M hE κ (groupMask M d s d.D) (groupMask M d s d.C)
      (groupMask M d s d.T) ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
      ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) ε
  else 0

lemma listedSafeStatistic_focal_empty (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (B C : Finset (Fin n)) (Y : Set (Fin n)) (ε : Fin 2) :
    listedSafeStatistic M hE κ (focalMasks d (trueGroup M d s i) ∅ B C) s i Y ε = 0 := by
  rw [listedSafeStatistic, ite_eq_right]
  simp only [focal_listed_iff_nonempty M d s i ∅ B C (Finset.empty_subset _),
    Finset.not_nonempty_empty, not_false_eq_true]

lemma listedRankStatistic_focal_empty (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (B C : Finset (Fin n)) (ε : Fin 2) :
    listedRankStatistic M hE κ (focalMasks d (trueGroup M d s i) ∅ B C) s i ε = 0 := by
  rw [listedRankStatistic, ite_eq_right]
  simp only [focal_listed_iff_nonempty M d s i ∅ B C (Finset.empty_subset _),
    Finset.not_nonempty_empty, not_false_eq_true]

lemma listedSafeStatistic_focal_nonempty (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (A B C : Finset (Fin n)) (Y : Set (Fin n)) (ε : Fin 2)
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty) :
    let f := focalMasks d (trueGroup M d s i) A B C
    listedSafeStatistic M hE κ f s i Y ε =
      safeLayerStatistic M hE κ (groupMask M f s f.D) (groupMask M f s f.C)
        (groupMask M f s f.T) (focalIndex M d s i) (trueGroup M d s i : Set (Fin n))
        ((f.D : Set (Fin n)) ∩ Y) ε := by
  dsimp only
  rw [listedSafeStatistic, ite_eq_left ((focal_listed_iff_nonempty M d s i A B C hA).mpr hne),
    groups_focalMasks M d s i A B C hA hne, trueGroup_focalMasks]
  rfl

lemma listedRankStatistic_focal_nonempty (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (A B C : Finset (Fin n)) (ε : Fin 2)
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty) :
    let f := focalMasks d (trueGroup M d s i) A B C
    listedRankStatistic M hE κ f s i ε =
      nominalRankStatistic M hE κ (groupMask M f s f.D) (groupMask M f s f.C)
        (groupMask M f s f.T) (focalIndex M d s i) (trueGroup M d s i : Set (Fin n))
        ((f.H ∪ f.D ∪ f.C : Finset (Fin n)) : Set (Fin n)) ε := by
  dsimp only
  rw [listedRankStatistic, ite_eq_left ((focal_listed_iff_nonempty M d s i A B C hA).mpr hne),
    groups_focalMasks M d s i A B C hA hne, trueGroup_focalMasks]
  rfl

lemma focal_density_inter (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) :
    ((focalMasks d (trueGroup M d s i) A B C).D : Set (Fin n)) ∩ Y =
      (A : Set (Fin n)) ∩ Y := by
  ext e
  simp only [Set.mem_inter_iff, Finset.mem_coe, focalMasks, Finset.mem_union,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨he | he, heY⟩
    · exact False.elim (he.2 (hY heY))
    · exact ⟨he, heY⟩
  · rintro ⟨heA, heY⟩
    exact ⟨Or.inr heA, heY⟩

end MainAlgorithm
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α β γ : Type*} [DecidableEq α]

def RevealTree.map (f : β → γ) : RevealTree α β → RevealTree α γ
  | .leaf b => .leaf (f b)
  | .query e no yes => .query e (no.map f) (yes.map f)

lemma RevealTree.fresh_map (tree : RevealTree α β) (f : β → γ) (V : Finset α) :
    (tree.map f).Fresh V ↔ tree.Fresh V := by
  induction tree generalizing V with
  | leaf b => rfl
  | query e no yes ihn ihy => simp only [map, Fresh, ihn, ihy]

lemma RevealTree.run_map (tree : RevealTree α β) (f : β → γ) (S : Finset α) :
    (tree.map f).run S = f (tree.run S) := by
  induction tree generalizing S with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    simp only [map, run]
    split_ifs <;> simp_all

def revealBatch : List α → (Finset α → RevealTree α β) → RevealTree α β
  | [], cont => cont ∅
  | e :: xs, cont => .query e (revealBatch xs cont)
      (revealBatch xs (fun I => cont (insert e I)))

lemma erase_sdiff_eq_sdiff_insert (S X : Finset α) (e : α) :
    S.erase e \ X = S \ insert e X := by
  ext x
  simp only [mem_sdiff, mem_erase, mem_insert]
  tauto

lemma revealBatch_fresh (xs : List α) (hxs : xs.Nodup)
    (cont : Finset α → RevealTree α β) (V : Finset α)
    (hXV : xs.toFinset ⊆ V)
    (hcont : ∀ I ⊆ xs.toFinset, (cont I).Fresh (V \ xs.toFinset)) :
    (revealBatch xs cont).Fresh V := by
  induction xs generalizing cont V with
  | nil => simpa [revealBatch] using hcont ∅ (empty_subset _)
  | cons e xs ih =>
    have heX : e ∉ xs.toFinset := by simpa using (List.nodup_cons.mp hxs).1
    have heV : e ∈ V := hXV (by simp)
    have hsub : xs.toFinset ⊆ V.erase e := by
      intro x hx
      refine mem_erase.mpr ⟨?_, hXV (by simp [hx])⟩
      intro h; subst x; exact heX hx
    have htail := (List.nodup_cons.mp hxs).2
    refine ⟨heV, ih htail cont (V.erase e) hsub ?_,
      ih htail (fun I => cont (insert e I)) (V.erase e) hsub ?_⟩
    · intro I hI
      rw [erase_sdiff_eq_sdiff_insert]
      simpa only [List.toFinset_cons] using hcont I (by simpa using hI.trans (subset_insert e xs.toFinset))
    · intro I hI
      rw [erase_sdiff_eq_sdiff_insert]
      simpa only [List.toFinset_cons] using hcont (insert e I) (by simpa using insert_subset_insert e hI)

lemma revealBatch_run (xs : List α) (hxs : xs.Nodup)
    (cont : Finset α → RevealTree α β) (S : Finset α) :
    (revealBatch xs cont).run S = (cont (S ∩ xs.toFinset)).run (S \ xs.toFinset) := by
  induction xs generalizing cont S with
  | nil => simp [revealBatch]
  | cons e xs ih =>
    have heX : e ∉ xs.toFinset := by simpa using (List.nodup_cons.mp hxs).1
    have htail := (List.nodup_cons.mp hxs).2
    have hinter : S.erase e ∩ xs.toFinset = S ∩ xs.toFinset := by
      ext x
      by_cases hx : x = e
      · subst x; simp [heX]
      · simp [hx]
    by_cases heS : e ∈ S
    · rw [revealBatch, RevealTree.run, ite_eq_left heS, ih htail,
        hinter, erase_sdiff_eq_sdiff_insert]
      have hins : insert e (S ∩ xs.toFinset) = S ∩ insert e xs.toFinset := by
        ext x
        by_cases hx : x = e
        · subst x; simp [heS]
        · simp [hx]
      simp only [List.toFinset_cons, hins]
    · rw [revealBatch, RevealTree.run, ite_eq_right heS, ih htail,
        hinter, erase_sdiff_eq_sdiff_insert]
      have hins : S ∩ xs.toFinset = S ∩ insert e xs.toFinset := by
        ext x
        by_cases hx : x = e
        · subst x; simp [heS]
        · simp [hx]
      simp only [List.toFinset_cons, hins]

lemma revealBatch_queried (xs : List α) (hxs : xs.Nodup)
    (cont : Finset α → RevealTree α β) (S : Finset α) :
    (revealBatch xs cont).queried S =
      xs.toFinset ∪ (cont (S ∩ xs.toFinset)).queried (S \ xs.toFinset) := by
  induction xs generalizing cont S with
  | nil => simp [revealBatch]
  | cons e xs ih =>
    have heX : e ∉ xs.toFinset := by simpa using (List.nodup_cons.mp hxs).1
    have htail := (List.nodup_cons.mp hxs).2
    have hinter : S.erase e ∩ xs.toFinset = S ∩ xs.toFinset := by
      ext x
      by_cases hx : x = e
      · subst x; simp [heX]
      · simp [hx]
    by_cases heS : e ∈ S
    · rw [revealBatch, RevealTree.queried, ite_eq_left heS, ih htail,
        hinter, erase_sdiff_eq_sdiff_insert]
      have hins : insert e (S ∩ xs.toFinset) = S ∩ insert e xs.toFinset := by
        ext x
        by_cases hx : x = e
        · subst x; simp [heS]
        · simp [hx]
      simp only [List.toFinset_cons, hins, insert_union]
    · rw [revealBatch, RevealTree.queried, ite_eq_right heS, ih htail,
        hinter, erase_sdiff_eq_sdiff_insert]
      have hins : S ∩ xs.toFinset = S ∩ insert e xs.toFinset := by
        ext x
        by_cases hx : x = e
        · subst x; simp [heS]
        · simp [hx]
      simp only [List.toFinset_cons, hins, insert_union]

lemma RevealTree.queried_map (tree : RevealTree α β) (f : β → γ) (S : Finset α) :
    (tree.map f).queried S = tree.queried S := by
  induction tree generalizing S with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    simp only [map, queried]
    split_ifs <;> simp_all

lemma RevealTree.hybrid_map (tree : RevealTree α β) (f : β → γ) (S T : Finset α) :
    (tree.map f).hybrid S T = tree.hybrid S T := by
  induction tree generalizing S T with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    simp only [map, hybrid, ihn, ihy]

structure RevealRecord (α β : Type*) where
  value : β
  queried : Finset α
  positive : Finset α

def RevealTree.record : RevealTree α β → RevealTree α (RevealRecord α β)
  | .leaf b => .leaf ⟨b, ∅, ∅⟩
  | .query e no yes => .query e
      (no.record.map (fun r => ⟨r.value, insert e r.queried, r.positive⟩))
      (yes.record.map (fun r => ⟨r.value, insert e r.queried, insert e r.positive⟩))

lemma RevealTree.record_fresh (tree : RevealTree α β) (V : Finset α) :
    tree.record.Fresh V ↔ tree.Fresh V := by
  induction tree generalizing V with
  | leaf b => rfl
  | query e no yes ihn ihy => simp only [record, Fresh, fresh_map, ihn, ihy]

lemma RevealTree.record_run (tree : RevealTree α β) (S : Finset α) :
    tree.record.run S = ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩ := by
  induction tree generalizing S with
  | leaf b => simp [record, run, queried]
  | query e no yes ihn ihy =>
    by_cases heS : e ∈ S
    · simp only [record, run, queried, ite_eq_left heS, run_map, ihy]
      congr 1
      ext x
      by_cases hxe : x = e
      · subst x; simp [heS]
      · simp [hxe]
    · simp only [record, run, queried, ite_eq_right heS, run_map, ihn]
      congr 1
      ext x
      by_cases hxe : x = e
      · subst x; simp [heS]
      · simp [hxe]

lemma RevealTree.record_hybrid (tree : RevealTree α β) (S T : Finset α) :
    tree.record.hybrid S T = tree.hybrid S T := by
  induction tree generalizing S T with
  | leaf b => rfl
  | query e no yes ihn ihy => simp only [record, hybrid, hybrid_map, ihn, ihy]

lemma RevealTree.transcript_hybrid_independent (tree : RevealTree α β)
    (q : α → ℝ) (V : Finset α) (fresh : tree.Fresh V)
    (φ : RevealRecord α β → ℝ) (ψ : Finset α → ℝ) :
    bitsExpectation q V (fun S => bitsExpectation q V (fun T =>
      φ ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩ * ψ (tree.hybrid S T))) =
      bitsExpectation q V (fun S => φ ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩) *
        bitsExpectation q V ψ := by
  have h := tree.record.hybrid_independent q V ((tree.record_fresh V).mpr fresh) φ ψ
  simpa only [record_run, record_hybrid] using h

lemma RevealTree.transcript_freshness (tree : RevealTree α β)
    (q : α → ℝ) (V Q : Finset α) (fresh : tree.Fresh V)
    (φ : RevealRecord α β → ℝ) (ψ : Finset α → ℝ)
    (support : ∀ r, r.queried ≠ Q → φ r = 0) :
    bitsExpectation q V (fun S =>
      φ ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩ * ψ (S \ Q)) =
      bitsExpectation q V (fun S => φ ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩) *
        bitsExpectation q V (fun S => ψ (S \ Q)) := by
  have h := tree.transcript_hybrid_independent q V fresh φ (fun S => ψ (S \ Q))
  rw [← h]
  apply bitsExpectation_congr
  intro S hS
  by_cases hQ : tree.queried S = Q
  · have hhybrid (T : Finset α) (hT : T ⊆ V) : tree.hybrid S T \ Q = S \ Q := by
      rw [tree.hybrid_eq_resample V S T fresh hS hT, hQ]
      ext e
      simp only [mem_sdiff, mem_union, mem_inter]
      tauto
    have hc : bitsExpectation q V (fun T =>
        φ ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩ * ψ (tree.hybrid S T \ Q)) =
        bitsExpectation q V (fun _ =>
          φ ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩ * ψ (S \ Q)) := by
      apply bitsExpectation_congr
      intro T hT
      rw [hhybrid T hT]
    rw [hc, bitsExpectation_const]
  · have hf := support ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩ hQ
    simp only [hf, zero_mul, bitsExpectation_const]

lemma RevealTree.record_queried (tree : RevealTree α β) (S : Finset α) :
    tree.record.queried S = tree.queried S := by
  induction tree generalizing S with
  | leaf b => rfl
  | query e no yes ihn ihy => simp only [record, queried, queried_map, ihn, ihy]

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

structure ReverseLayer (α : Type*) where
  group : Finset α
  density : Set α
  state : Set α
  enabledAt : ℤ

noncomputable def layerNominal (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) : Set α :=
  densityEnabled M hE κ L.density L.enabledAt k A

noncomputable def layerBatch (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) : Finset α :=
  L.group.filter (fun e => e ∈ L.state ∧ e ∉ layerNominal M hE κ k L A)

noncomputable def layerUpdate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) (C : Finset α) : Set α :=
  M.closure (layerNominal M hE κ k L A ∪ ((C : Set α) ∩ (L.group : Set α) ∩ L.state))

lemma layerUpdate_eq_batch (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) (C : Finset α) :
    layerUpdate M hE κ k L A C =
      M.closure (layerNominal M hE κ k L A ∪ (C ∩ layerBatch M hE κ k L A : Finset α)) := by
  unfold layerUpdate
  congr 1
  ext e
  simp only [layerBatch, Set.mem_union, Set.mem_inter_iff, mem_coe, mem_inter, mem_filter]
  tauto

noncomputable def runReverseLayers (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) : List (ReverseLayer α) → Set α → Finset α → Set α
  | [], A, _ => A
  | L::Ls, A, C => runReverseLayers M hE κ k Ls (layerUpdate M hE κ k L A C) C

noncomputable def reverseExposureTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) : List (ReverseLayer α) → Set α → RevealTree α (Set α)
  | [], A => .leaf A
  | L::Ls, A =>
      revealBatch (layerBatch M hE κ k L A).toList (fun I =>
        reverseExposureTree M hE κ k Ls (M.closure (layerNominal M hE κ k L A ∪ (I : Set α))))

lemma reverseExposureTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α))
    (hdisj : Ls.Pairwise (fun L L' => Disjoint L.group L'.group))
    (V : Finset α) (hV : ∀ L ∈ Ls, (L.group.filter (fun e => e ∈ L.state)) ⊆ V) (A : Set α) :
    (reverseExposureTree M hE κ k Ls A).Fresh V := by
  induction Ls generalizing V A with
  | nil => trivial
  | cons L Ls ih =>
    rw [List.pairwise_cons] at hdisj
    apply revealBatch_fresh _ (nodup_toList _) _ V
    · simp only [toList_toFinset]
      intro e he
      exact hV L (by simp) (mem_filter.mpr ⟨(mem_filter.mp he).1, (mem_filter.mp he).2.1⟩)
    · intro I hI
      simp only [toList_toFinset]
      apply ih hdisj.2
      intro L' hL' e he
      refine mem_sdiff.mpr ⟨hV L' (by simp [hL']) he, ?_⟩
      intro hb
      have heL := (mem_filter.mp hb).1
      exact Finset.disjoint_left.mp (hdisj.1 L' hL') heL (mem_filter.mp he).1

lemma layerUpdate_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) (C C' : Finset α)
    (hC : ∀ e ∈ L.group, (e ∈ C ↔ e ∈ C')) :
    layerUpdate M hE κ k L A C = layerUpdate M hE κ k L A C' := by
  unfold layerUpdate
  congr 1
  ext e
  by_cases heG : e ∈ L.group
  · simp only [Set.mem_union, Set.mem_inter_iff, mem_coe, hC e heG]
  · simp [heG]

lemma runReverseLayers_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α)) (A : Set α) (C C' : Finset α)
    (hC : ∀ L ∈ Ls, ∀ e ∈ L.group, (e ∈ C ↔ e ∈ C')) :
    runReverseLayers M hE κ k Ls A C = runReverseLayers M hE κ k Ls A C' := by
  induction Ls generalizing A with
  | nil => rfl
  | cons L Ls ih =>
    rw [runReverseLayers, runReverseLayers, layerUpdate_congr M hE κ k L A C C' (hC L (by simp))]
    exact ih _ (fun L' hL' => hC L' (by simp [hL']))

lemma reverseExposureTree_run (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α))
    (hdisj : Ls.Pairwise (fun L L' => Disjoint L.group L'.group))
    (A : Set α) (C : Finset α) :
    (reverseExposureTree M hE κ k Ls A).run C = runReverseLayers M hE κ k Ls A C := by
  induction Ls generalizing A C with
  | nil => rfl
  | cons L Ls ih =>
    rw [List.pairwise_cons] at hdisj
    rw [reverseExposureTree, revealBatch_run _ (nodup_toList _)]
    simp only [toList_toFinset]
    rw [ih hdisj.2, ← layerUpdate_eq_batch, runReverseLayers]
    apply runReverseLayers_congr
    intro L' hL' e he
    have heB : e ∉ layerBatch M hE κ k L A := by
      intro hb
      exact Finset.disjoint_left.mp (hdisj.1 L' hL') (mem_filter.mp hb).1 he
    simp [heB]

theorem reverseExposure_hybrid_independent (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α))
    (hdisj : Ls.Pairwise (fun L L' => Disjoint L.group L'.group))
    (V : Finset α) (hV : ∀ L ∈ Ls, (L.group.filter (fun e => e ∈ L.state)) ⊆ V) (A : Set α)
    (q : α → ℝ) (φ : Set α → ℝ) (ψ : Finset α → ℝ) :
    bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
      φ (runReverseLayers M hE κ k Ls A C) *
        ψ ((reverseExposureTree M hE κ k Ls A).hybrid C T))) =
      bitsExpectation q V (fun C => φ (runReverseLayers M hE κ k Ls A C)) *
        bitsExpectation q V ψ := by
  have h := (reverseExposureTree M hE κ k Ls A).hybrid_independent q V
    (reverseExposureTree_fresh M hE κ k Ls hdisj V hV A) φ ψ
  simpa only [reverseExposureTree_run M hE κ k Ls hdisj] using h

omit [DecidableEq α] in
lemma runReverseLayers_append (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls Ls' : List (ReverseLayer α)) (A : Set α) (C : Finset α) :
    runReverseLayers M hE κ k (Ls ++ Ls') A C =
      runReverseLayers M hE κ k Ls' (runReverseLayers M hE κ k Ls A C) C := by
  induction Ls generalizing A with
  | nil => rfl
  | cons L Ls ih => exact ih _

def sourceLayer (D S : ℕ → Set α) (G : ℕ → Finset α) (j : ℕ) : ReverseLayer α :=
  ⟨G j, D j, S j, activation j⟩

def sourceLayers (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) : List (ReverseLayer α) :=
  (List.range n).map (sourceLayer D S G)

omit [Fintype α] [DecidableEq α] in
lemma sourceLayers_pairwise (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) :
    (sourceLayers D S G n).Pairwise (fun L L' => Disjoint L.group L'.group) := by
  rw [sourceLayers, List.pairwise_map]
  exact (List.nodup_range (n := n)).pairwise_of_forall_ne (fun _ _ _ _ hij => hG hij)

omit [DecidableEq α] in
lemma runReverseLayers_source (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    runReverseLayers M hE κ k (sourceLayers D S G n)
      (if k < 0 then M.closure ∅ else Set.univ) C =
      reversePrefix M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sourceLayers, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      runReverseLayers_append]
    change layerUpdate M hE κ k (sourceLayer D S G n)
      (runReverseLayers M hE κ k (sourceLayers D S G n)
        (if k < 0 then M.closure ∅ else Set.univ) C) C = _
    rw [ih]
    rfl

theorem source_reverse_hybrid_independent (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (q : α → ℝ) (φ : Set α → ℝ) (ψ : Finset α → ℝ) :
    let tree := reverseExposureTree M hE κ k (sourceLayers D S G n)
      (if k < 0 then M.closure ∅ else Set.univ)
    bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
      φ (reversePrefix M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n) *
        ψ (tree.hybrid C T))) =
      bitsExpectation q V (fun C =>
        φ (reversePrefix M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n)) *
          bitsExpectation q V ψ := by
  dsimp only
  have hv : ∀ L ∈ sourceLayers D S G n, L.group.filter (fun e => e ∈ L.state) ⊆ V := by
    intro L hL
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hL
    exact hV j (List.mem_range.mp hj)
  have h := reverseExposure_hybrid_independent M hE κ k (sourceLayers D S G n)
    (sourceLayers_pairwise D S G n hG) V hv
      (if k < 0 then M.closure ∅ else Set.univ) q φ ψ
  simpa only [runReverseLayers_source] using h

noncomputable def queriedReverseLayers (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) : List (ReverseLayer α) → Set α → Finset α → Finset α
  | [], _, _ => ∅
  | L::Ls, A, C => layerBatch M hE κ k L A ∪
      queriedReverseLayers M hE κ k Ls (layerUpdate M hE κ k L A C) C

lemma queriedReverseLayers_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α)) (A : Set α) (C C' : Finset α)
    (hC : ∀ L ∈ Ls, ∀ e ∈ L.group, (e ∈ C ↔ e ∈ C')) :
    queriedReverseLayers M hE κ k Ls A C = queriedReverseLayers M hE κ k Ls A C' := by
  induction Ls generalizing A with
  | nil => rfl
  | cons L Ls ih =>
    rw [queriedReverseLayers, queriedReverseLayers,
      layerUpdate_congr M hE κ k L A C C' (hC L (by simp))]
    congr 1
    exact ih _ (fun L' hL' => hC L' (by simp [hL']))

lemma reverseExposureTree_queried (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α))
    (hdisj : Ls.Pairwise (fun L L' => Disjoint L.group L'.group))
    (A : Set α) (C : Finset α) :
    (reverseExposureTree M hE κ k Ls A).queried C = queriedReverseLayers M hE κ k Ls A C := by
  induction Ls generalizing A C with
  | nil => rfl
  | cons L Ls ih =>
    rw [List.pairwise_cons] at hdisj
    rw [reverseExposureTree, revealBatch_queried _ (nodup_toList _)]
    simp only [toList_toFinset]
    rw [ih hdisj.2, ← layerUpdate_eq_batch, queriedReverseLayers]
    congr 1
    apply queriedReverseLayers_congr
    intro L' hL' e he
    have heB : e ∉ layerBatch M hE κ k L A := by
      intro hb
      exact Finset.disjoint_left.mp (hdisj.1 L' hL') (mem_filter.mp hb).1 he
    simp [heB]

lemma queriedReverseLayers_append (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls Ls' : List (ReverseLayer α)) (A : Set α) (C : Finset α) :
    queriedReverseLayers M hE κ k (Ls ++ Ls') A C = queriedReverseLayers M hE κ k Ls A C ∪
      queriedReverseLayers M hE κ k Ls' (runReverseLayers M hE κ k Ls A C) C := by
  induction Ls generalizing A with
  | nil => simp [queriedReverseLayers, runReverseLayers]
  | cons L Ls ih =>
    simp only [List.cons_append, queriedReverseLayers, runReverseLayers, ih, union_assoc]

lemma queriedReverseLayers_source (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    queriedReverseLayers M hE κ k (sourceLayers D S G n)
      (if k < 0 then M.closure ∅ else Set.univ) C =
      (Finset.range n).biUnion (fun j => (G j).filter (fun e => e ∈ S j ∧
        e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j)) := by
  induction n with
  | zero => simp [sourceLayers, queriedReverseLayers]
  | succ n ih =>
    simp only [sourceLayers, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      queriedReverseLayers_append]
    change queriedReverseLayers M hE κ k (sourceLayers D S G n)
        (if k < 0 then M.closure ∅ else Set.univ) C ∪
      (layerBatch M hE κ k (sourceLayer D S G n)
        (runReverseLayers M hE κ k (sourceLayers D S G n)
          (if k < 0 then M.closure ∅ else Set.univ) C) ∪ ∅) = _
    rw [ih, runReverseLayers_source]
    simp only [union_empty, Finset.range_add_one, biUnion_insert]
    rw [union_comm]
    rfl

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def sourceReverseTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    RevealTree α (Set α) :=
  reverseExposureTree M hE κ k (sourceLayers D S G n)
    (if k < 0 then M.closure ∅ else Set.univ)

lemma sourceReverseTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V) :
    (sourceReverseTree M hE κ k D S G n).Fresh V := by
  apply reverseExposureTree_fresh M hE κ k _ (sourceLayers_pairwise D S G n hG)
  intro L hL
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hL
  exact hV j (List.mem_range.mp hj)

lemma sourceReverseTree_queried (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α) :
    (sourceReverseTree M hE κ k D S G n).queried C =
      (Finset.range n).biUnion (fun j => (G j).filter (fun e => e ∈ S j ∧
        e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j)) := by
  rw [sourceReverseTree, reverseExposureTree_queried M hE κ k _
    (sourceLayers_pairwise D S G n hG), queriedReverseLayers_source]

lemma sourceReverseTree_queried_coordinate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α)
    {j : ℕ} (hj : j < n) {e : α} (heG : e ∈ G j) (heS : e ∈ S j) :
    e ∈ (sourceReverseTree M hE κ k D S G n).queried C ↔
      e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  rw [sourceReverseTree_queried M hE κ k D S G n hG, mem_biUnion]
  constructor
  · rintro ⟨i, hi, he⟩
    by_cases hij : i = j
    · subst i; exact (mem_filter.mp he).2.2
    · exact (Finset.disjoint_left.mp (hG hij) (mem_filter.mp he).1 heG).elim
  · intro he
    exact ⟨j, mem_range.mpr hj, mem_filter.mpr ⟨heG, heS, he⟩⟩

lemma sourceReverseTree_hybrid_coordinate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (C T : Finset α) (hC : C ⊆ V) (hT : T ⊆ V)
    {j : ℕ} (hj : j < n) {e : α} (heG : e ∈ G j) (heS : e ∈ S j) :
    e ∈ (sourceReverseTree M hE κ k D S G n).hybrid C T ↔
      (e ∈ C ∧ e ∈ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j) ∨
      (e ∈ T ∧ e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j) := by
  rw [(sourceReverseTree M hE κ k D S G n).hybrid_eq_resample V C T
    (sourceReverseTree_fresh M hE κ k D S G n hG V hV) hC hT]
  simp only [mem_union, mem_sdiff, mem_inter,
    sourceReverseTree_queried_coordinate M hE κ k D S G n hG C hj heG heS, not_not]

noncomputable def transitionHybrid (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C T : Finset α) (j : ℕ) : Set α :=
  ((C : Set α) ∩ (G j : Set α) ∩
    reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j) ∪
  ((T : Set α) ∩ (G j : Set α) ∩
    (S j \ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j))

lemma sourceReverseTree_hybrid_guard (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (C T : Finset α) (hC : C ⊆ V) (hT : T ⊆ V) {j : ℕ} (hj : j < n) :
    (((sourceReverseTree M hE κ k D S G n).hybrid C T : Set α) ∩ (G j : Set α)) ∩ S j =
      transitionHybrid M hE κ k D S G C T j ∩ S j := by
  ext e
  by_cases heG : e ∈ G j
  · by_cases heS : e ∈ S j
    · have hh := sourceReverseTree_hybrid_coordinate M hE κ k D S G n hG V hV C T hC hT hj heG heS
      simp only [transitionHybrid, Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff,
        mem_coe, heG, heS, and_true, true_and]
      exact hh
    · simp [transitionHybrid, heS]
  · simp [transitionHybrid, heG]

omit [DecidableEq α] in
lemma reversePrefix_congr_guard_inter (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C C' S : ℕ → Set α) (k : ℤ) (n : ℕ)
    (hC : ∀ j < n, C j ∩ S j = C' j ∩ S j) :
    reversePrefix M hE κ D C S k n = reversePrefix M hE κ D C' S k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [reversePrefix, reversePrefix, ih (fun j hj => hC j (by omega)), hC n (by omega)]

lemma sourceReverseTree_hybrid_output (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (C T : Finset α) (hC : C ⊆ V) (hT : T ⊆ V) :
    reverseNominal M hE κ D
      (fun j => (((sourceReverseTree M hE κ k D S G n).hybrid C T : Set α) ∩ (G j : Set α))) S k n =
    reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n := by
  unfold reverseNominal
  congr 1
  exact reversePrefix_congr_guard_inter M hE κ D _ _ S k n
    (fun j hj => sourceReverseTree_hybrid_guard M hE κ k D S G n hG V hV C T hC hT hj)

theorem reverse_double_exit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (q : α → ℝ) (d : α) :
    bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
      (if d ∉ reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n then 1 else 0) *
      (if d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n then 1 else 0))) =
      (bitsExpectation q V (fun C =>
        if d ∉ reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n then 1 else 0)) ^ 2 := by
  let φ : Set α → ℝ := fun A => if d ∉ densityEnabled M hE κ (D n) (activation n) k A then 1 else 0
  let ψ : Finset α → ℝ := fun C =>
    if d ∉ reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n then 1 else 0
  have hi := source_reverse_hybrid_independent M hE κ k D S G n hG V hV q φ ψ
  change bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
    ψ C * (if d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n then 1 else 0))) =
      (bitsExpectation q V ψ)^2
  have heq : bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
      ψ C * (if d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n then 1 else 0))) =
      bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
        ψ C * ψ ((sourceReverseTree M hE κ k D S G n).hybrid C T))) := by
    apply bitsExpectation_congr
    intro C hC
    apply bitsExpectation_congr
    intro T hT
    dsimp only [ψ]
    rw [sourceReverseTree_hybrid_output M hE κ k D S G n hG V hV C T hC hT]
  rw [heq]
  change bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
    φ (reversePrefix M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n) *
      ψ ((sourceReverseTree M hE κ k D S G n).hybrid C T))) = _
  unfold sourceReverseTree
  rw [hi]
  change bitsExpectation q V ψ * bitsExpectation q V ψ = _
  ring

lemma sourceReverseTree_queried_coordinate_full (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α)
    {j : ℕ} (hj : j < n) {e : α} (heG : e ∈ G j) :
    e ∈ (sourceReverseTree M hE κ k D S G n).queried C ↔
      e ∈ S j ∧ e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  rw [sourceReverseTree_queried M hE κ k D S G n hG, mem_biUnion]
  constructor
  · rintro ⟨i, hi, he⟩
    by_cases hij : i = j
    · subst i; exact (mem_filter.mp he).2
    · exact (Finset.disjoint_left.mp (hG hij) (mem_filter.mp he).1 heG).elim
  · intro he
    exact ⟨j, mem_range.mpr hj, mem_filter.mpr ⟨heG, he⟩⟩

lemma sourceReverseTree_positive_guards (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α)
    {j : ℕ} (hj : j < n) :
    ((C ∩ (sourceReverseTree M hE κ k D S G n).queried C : Finset α) : Set α) ∩ (G j : Set α) =
      departingGuards M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  ext e
  by_cases heG : e ∈ G j
  · have hq := sourceReverseTree_queried_coordinate_full M hE κ k D S G n hG C hj heG
    simp only [departingGuards, Set.mem_inter_iff, Set.mem_sdiff, mem_coe, mem_inter, heG, and_true]
    rw [hq]
  · simp [departingGuards, heG]

lemma sourceReverseTree_positive_nominal (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α)
    {j : ℕ} (hj : j ≤ n) :
    reverseNominal M hE κ D
      (fun i => ((C ∩ (sourceReverseTree M hE κ k D S G n).queried C : Finset α) : Set α) ∩ (G i : Set α))
      S k j = reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  calc
    _ = reverseNominal M hE κ D
        (departingGuards M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k) S k j := by
      apply reverseNominal_congr_before
      · intro i hi
        exact sourceReverseTree_positive_guards M hE κ k D S G n hG C (by omega)
      · exact fun _ _ => rfl
    _ = _ := reverseNominal_departing_only M hE κ D _ S k j

noncomputable def reverseStateTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    RevealTree α (Fin n → Set α) :=
  (sourceReverseTree M hE κ k D S G n).record.map (fun r j =>
    reverseNominal M hE κ D (fun i => (r.positive : Set α) ∩ (G i : Set α)) S k j.val)

lemma reverseStateTree_run (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α) :
    (reverseStateTree M hE κ k D S G n).run C =
      (fun j => reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j.val) := by
  rw [reverseStateTree, RevealTree.run_map, RevealTree.record_run]
  funext j
  exact sourceReverseTree_positive_nominal M hE κ k D S G n hG C j.isLt.le

lemma reverseStateTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V) :
    (reverseStateTree M hE κ k D S G n).Fresh V := by
  rw [reverseStateTree, RevealTree.fresh_map, RevealTree.record_fresh]
  exact sourceReverseTree_fresh M hE κ k D S G n hG V hV

lemma reverseStateTree_queried (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    (reverseStateTree M hE κ k D S G n).queried C =
      (sourceReverseTree M hE κ k D S G n).queried C := by
  rw [reverseStateTree, RevealTree.queried_map, RevealTree.record_queried]

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

inductive QueryProgram (α : Type*) where
  | stop
  | query (e : α) (no yes : QueryProgram α)
  | finish (rest : QueryProgram α)

def QueryProgram.Fresh : QueryProgram α → Finset α → Prop
  | .stop, _ => True
  | .query e no yes, V => e ∈ V ∧ no.Fresh (V.erase e) ∧ yes.Fresh (V.erase e)
  | .finish rest, V => rest.Fresh V

noncomputable def QueryProgram.expected (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) : QueryProgram α → Finset α → ℝ
  | .stop, _ => 0
  | .query e no yes, I => (1 - q e) * no.expected cert q I +
      q e * yes.expected cert q (insert e I)
  | .finish rest, I => (if cert I then 1 else 0) + rest.expected cert q ∅

lemma ratio_resource {p p' a : ℝ} (hp : 0 < p) (hpp' : p ≤ p')
    (ha : 0 ≤ a) (hap : a ≤ p) :
    a / p - a / p' ≤ Real.log p' - Real.log p := by
  have hp' : 0 < p' := lt_of_lt_of_le hp hpp'
  have hz : a / p ≤ 1 := (div_le_one hp).2 hap
  have hz0 : 0 ≤ a / p := div_nonneg ha hp.le
  have hx0 : 0 ≤ 1 - p / p' := by
    have h := (div_le_one hp').2 hpp'
    linarith
  have hm := mul_le_mul_of_nonneg_right hz hx0
  have heq : a / p - a / p' = (a / p) * (1 - p / p') := by
    field_simp
  rw [heq]
  calc
    a / p * (1 - p / p') ≤ 1 - p / p' := by simpa using hm
    _ ≤ Real.log (p' / p) := by
      simpa using Real.one_sub_inv_le_log_of_pos (div_pos hp' hp)
    _ = Real.log p' - Real.log p := Real.log_div hp'.ne' hp.ne'

theorem certificate_budget_of_failure_identities
    (cert : Finset α → Prop) [DecidablePred cert] (q : α → ℝ)
    (q_nonneg : ∀ e, 0 ≤ q e) (q_le_one : ∀ e, q e ≤ 1)
    (failure : Finset α → Finset α → ℝ)
    (positive : ∀ V, 0 < failure V ∅)
    (bounded : ∀ V I, 0 ≤ failure V I ∧ failure V I ≤ failure V ∅)
    (at_most_one : ∀ V, failure V ∅ ≤ 1)
    (depleted : ∀ V e, e ∈ V → failure V ∅ ≤ failure (V.erase e) ∅)
    (split : ∀ V I e, e ∈ V → failure V I =
      (1 - q e) * failure (V.erase e) I + q e * failure (V.erase e) (insert e I))
    (certifies : ∀ V I, cert I → failure V I = 0)
    (prog : QueryProgram α) (V I : Finset α) (fresh : prog.Fresh V) :
    prog.expected cert q I ≤ -Real.log (failure V ∅) + 1 - failure V I / failure V ∅ := by
  induction prog generalizing V I with
  | stop =>
    dsimp [QueryProgram.expected]
    have hlog : Real.log (failure V ∅) ≤ 0 :=
      Real.log_nonpos (positive V).le (at_most_one V)
    have hratio : failure V I / failure V ∅ ≤ 1 :=
      (div_le_one (positive V)).2 (bounded V I).2
    linarith
  | finish rest ih =>
    dsimp [QueryProgram.Fresh] at fresh
    have hr := ih V ∅ fresh
    have hp := positive V
    rw [div_self hp.ne'] at hr
    dsimp [QueryProgram.expected]
    split_ifs with hcert
    · rw [certifies V I hcert, zero_div]
      linarith
    · have hratio : failure V I / failure V ∅ ≤ 1 :=
        (div_le_one hp).2 (bounded V I).2
      linarith
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have hno := ihn (V.erase e) I hn
    have hyes := ihy (V.erase e) (insert e I) hy
    have hqn : 0 ≤ 1 - q e := sub_nonneg.2 (q_le_one e)
    have h0 := mul_le_mul_of_nonneg_left hno hqn
    have h1 := mul_le_mul_of_nonneg_left hyes (q_nonneg e)
    have hp := positive V
    have hp' := positive (V.erase e)
    have hs := split V I e he
    have hresource := ratio_resource hp (depleted V e he) (bounded V I).1 (bounded V I).2
    have hmix : (1 - q e) *
        (-Real.log (failure (V.erase e) ∅) + 1 - failure (V.erase e) I / failure (V.erase e) ∅) +
        q e * (-Real.log (failure (V.erase e) ∅) + 1 -
          failure (V.erase e) (insert e I) / failure (V.erase e) ∅) =
        -Real.log (failure (V.erase e) ∅) + 1 - failure V I / failure (V.erase e) ∅ := by
      rw [hs]
      ring
    dsimp [QueryProgram.expected]
    linarith

theorem disjoint_query_certificates [Fintype α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure cert q univ ∅)
    (prog : QueryProgram α) (fresh : prog.Fresh univ) :
    prog.expected cert q ∅ ≤ Real.log (1 / bitsFailure cert q univ ∅) := by
  have hp (V : Finset α) : 0 < bitsFailure cert q V ∅ :=
    lt_of_lt_of_le hδ (bitsFailure_antitone cert hcert q hq0 hq1 ∅ (subset_univ V))
  have h := certificate_budget_of_failure_identities cert q hq0 hq1
    (bitsFailure cert q) hp
    (fun V I => ⟨bitsFailure_nonneg cert q hq0 hq1 V I,
      bitsFailure_forced_antitone cert hcert q hq0 hq1 V (empty_subset I)⟩)
    (fun V => bitsFailure_le_one cert q hq0 hq1 V ∅)
    (fun V e _ => bitsFailure_antitone cert hcert q hq0 hq1 ∅ (erase_subset e V))
    (bitsFailure_split cert q)
    (bitsFailure_certifies cert hcert q) prog univ ∅ fresh
  simpa [div_self hδ.ne'] using h

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

def QueryProgram.run (cert : Finset α → Prop) [DecidablePred cert]
    (S : Finset α) : QueryProgram α → Finset α → ℝ
  | .stop, _ => 0
  | .query e no yes, I => if e ∈ S then yes.run cert S (insert e I) else no.run cert S I
  | .finish rest, I => (if cert I then 1 else 0) + rest.run cert S ∅

lemma QueryProgram.run_congr (cert : Finset α → Prop) [DecidablePred cert]
    (prog : QueryProgram α) (V I S S' : Finset α) (fresh : prog.Fresh V)
    (agree : ∀ e ∈ V, (e ∈ S ↔ e ∈ S')) :
    prog.run cert S I = prog.run cert S' I := by
  induction prog generalizing V I with
  | stop => rfl
  | finish rest ih =>
    simp only [run]
    rw [ih V ∅ fresh agree]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have ha := agree e he
    have har : ∀ x ∈ V.erase e, (x ∈ S ↔ x ∈ S') :=
      fun x hx => agree x (mem_of_mem_erase hx)
    by_cases h : e ∈ S
    · simp only [run, ite_eq_left h, ite_eq_left (ha.mp h)]
      exact ihy (V.erase e) (insert e I) hy har
    · have h' : e ∉ S' := fun hx => h (ha.mpr hx)
      simp only [run, ite_eq_right h, ite_eq_right h']
      exact ihn (V.erase e) I hn har

lemma QueryProgram.expected_eq_product (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (prog : QueryProgram α) (V I : Finset α) (fresh : prog.Fresh V) :
    bitsExpectation q V (fun S => prog.run cert S I) = prog.expected cert q I := by
  induction prog generalizing V I with
  | stop => simp only [run, expected, bitsExpectation_const]
  | finish rest ih =>
    simp only [run, expected, bitsExpectation_add, bitsExpectation_const]
    rw [ih V ∅ fresh]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have hsplit := bitsExpectation_insert q (V.erase e) e (notMem_erase e V)
      (fun S => (QueryProgram.query e no yes).run cert S I)
    rw [insert_erase he] at hsplit
    have hno : bitsExpectation q (V.erase e)
        (fun S => (QueryProgram.query e no yes).run cert S I) =
        bitsExpectation q (V.erase e) (fun S => no.run cert S I) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun hx => (notMem_erase e V) (hS hx)
      simp only [run, ite_eq_right heS]
    have hyes : bitsExpectation q (V.erase e)
        (fun S => (QueryProgram.query e no yes).run cert (insert e S) I) =
        bitsExpectation q (V.erase e) (fun S => yes.run cert S (insert e I)) := by
      apply bitsExpectation_congr
      intro S hS
      simp only [run, mem_insert_self, ite_true]
      apply yes.run_congr cert (V.erase e) (insert e I) (insert e S) S hy
      intro x hx
      have hxe : x ≠ e := (mem_erase.1 hx).1
      simp only [mem_insert, hxe, false_or]
    rw [hsplit, hno, hyes, ihn (V.erase e) I hn, ihy (V.erase e) (insert e I) hy]
    rfl

theorem disjoint_query_certificates_product [Fintype α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure cert q univ ∅)
    (prog : QueryProgram α) (fresh : prog.Fresh univ) :
    bitsExpectation q univ (fun S => prog.run cert S ∅) ≤
      Real.log (1 / bitsFailure cert q univ ∅) := by
  rw [prog.expected_eq_product cert q univ ∅ fresh]
  exact disjoint_query_certificates cert hcert q hq0 hq1 hδ prog fresh

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α β γ : Type*} [DecidableEq α]

def RevealTree.bind (tree : RevealTree α β) (cont : β → RevealTree α γ) : RevealTree α γ :=
  match tree with
  | .leaf b => cont b
  | .query e no yes => .query e (no.bind cont) (yes.bind cont)

lemma RevealTree.run_bind (tree : RevealTree α β) (cont : β → RevealTree α γ) (S : Finset α) :
    (tree.bind cont).run S = (cont (tree.run S)).run (S \ tree.queried S) := by
  induction tree generalizing S with
  | leaf b => simp [bind, run, queried]
  | query e no yes ihn ihy =>
    by_cases heS : e ∈ S
    · simp only [bind, run, queried, ite_eq_left heS, ihy, erase_sdiff_eq_sdiff_insert]
    · simp only [bind, run, queried, ite_eq_right heS, ihn, erase_sdiff_eq_sdiff_insert]

lemma RevealTree.queried_bind (tree : RevealTree α β) (cont : β → RevealTree α γ) (S : Finset α) :
    (tree.bind cont).queried S =
      tree.queried S ∪ (cont (tree.run S)).queried (S \ tree.queried S) := by
  induction tree generalizing S with
  | leaf b => simp [bind, run, queried]
  | query e no yes ihn ihy =>
    by_cases heS : e ∈ S
    · simp only [bind, run, queried, ite_eq_left heS, ihy, erase_sdiff_eq_sdiff_insert, insert_union]
    · simp only [bind, run, queried, ite_eq_right heS, ihn, erase_sdiff_eq_sdiff_insert, insert_union]

lemma RevealTree.fresh_bind (tree : RevealTree α β) (cont : β → RevealTree α γ)
    (V : Finset α) (fresh : tree.Fresh V)
    (hcont : ∀ S ⊆ V, (cont (tree.run S)).Fresh (V \ tree.queried S)) :
    (tree.bind cont).Fresh V := by
  induction tree generalizing V with
  | leaf b => simpa [bind, run, queried] using hcont ∅ (empty_subset V)
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    refine ⟨he, ihn (V.erase e) hn ?_, ihy (V.erase e) hy ?_⟩
    · intro S hS
      have heS : e ∉ S := fun hs => notMem_erase e V (hS hs)
      have hc := hcont S (hS.trans (erase_subset e V))
      simpa only [run, queried, ite_eq_right heS, erase_eq_of_notMem heS,
        erase_sdiff_eq_sdiff_insert] using hc
    · intro S hS
      have heS : e ∉ S := fun hs => notMem_erase e V (hS hs)
      have hc := hcont (insert e S) (insert_subset he (hS.trans (erase_subset e V)))
      simpa only [run, queried, mem_insert_self, ite_true, erase_insert heS,
        erase_eq_of_notMem heS, erase_sdiff_eq_sdiff_insert] using hc

lemma RevealTree.run_congr (tree : RevealTree α β) (V S S' : Finset α)
    (fresh : tree.Fresh V) (agree : ∀ e ∈ V, (e ∈ S ↔ e ∈ S')) :
    tree.run S = tree.run S' := by
  induction tree generalizing V S S' with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have ha := agree e he
    have har : ∀ x ∈ V.erase e, (x ∈ S.erase e ↔ x ∈ S'.erase e) := by
      intro x hx
      simp only [mem_erase, agree x (mem_of_mem_erase hx)]
    by_cases heS : e ∈ S
    · simp only [run, ite_eq_left heS, ite_eq_left (ha.mp heS)]
      exact ihy _ _ _ hy har
    · have heS' : e ∉ S' := fun h => heS (ha.mpr h)
      simp only [run, ite_eq_right heS, ite_eq_right heS']
      exact ihn _ _ _ hn har

lemma RevealTree.queried_congr (tree : RevealTree α β) (V S S' : Finset α)
    (fresh : tree.Fresh V) (agree : ∀ e ∈ V, (e ∈ S ↔ e ∈ S')) :
    tree.queried S = tree.queried S' := by
  induction tree generalizing V S S' with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have ha := agree e he
    have har : ∀ x ∈ V.erase e, (x ∈ S.erase e ↔ x ∈ S'.erase e) := by
      intro x hx
      simp only [mem_erase, agree x (mem_of_mem_erase hx)]
    by_cases heS : e ∈ S
    · simp only [queried, ite_eq_left heS, ite_eq_left (ha.mp heS)]
      rw [ihy _ _ _ hy har]
    · have heS' : e ∉ S' := fun h => heS (ha.mpr h)
      simp only [queried, ite_eq_right heS, ite_eq_right heS']
      rw [ihn _ _ _ hn har]

def RevealTree.transaction (tree : RevealTree α β) (cont : β → QueryProgram α) : QueryProgram α :=
  match tree with
  | .leaf b => .finish (cont b)
  | .query e no yes => .query e (no.transaction cont) (yes.transaction cont)

lemma RevealTree.transaction_fresh (tree : RevealTree α β) (cont : β → QueryProgram α)
    (V : Finset α) (fresh : tree.Fresh V)
    (hcont : ∀ S ⊆ V, (cont (tree.run S)).Fresh (V \ tree.queried S)) :
    (tree.transaction cont).Fresh V := by
  induction tree generalizing V with
  | leaf b => simpa [transaction, QueryProgram.Fresh, run, queried] using hcont ∅ (empty_subset V)
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    refine ⟨he, ihn (V.erase e) hn ?_, ihy (V.erase e) hy ?_⟩
    · intro S hS
      have heS : e ∉ S := fun hs => notMem_erase e V (hS hs)
      have hc := hcont S (hS.trans (erase_subset e V))
      simpa only [run, queried, ite_eq_right heS, erase_eq_of_notMem heS,
        erase_sdiff_eq_sdiff_insert] using hc
    · intro S hS
      have heS : e ∉ S := fun hs => notMem_erase e V (hS hs)
      have hc := hcont (insert e S) (insert_subset he (hS.trans (erase_subset e V)))
      simpa only [run, queried, mem_insert_self, ite_true, erase_insert heS,
        erase_eq_of_notMem heS, erase_sdiff_eq_sdiff_insert] using hc

lemma RevealTree.transaction_run (tree : RevealTree α β) (cont : β → QueryProgram α)
    (V : Finset α) (fresh : tree.Fresh V) (cert : Finset α → Prop) [DecidablePred cert]
    (S I : Finset α) :
    (tree.transaction cont).run cert S I =
      (if cert (I ∪ (S ∩ tree.queried S)) then 1 else 0) + (cont (tree.run S)).run cert S ∅ := by
  induction tree generalizing V I with
  | leaf b => simp [transaction, QueryProgram.run, run, queried]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have ha : ∀ x ∈ V.erase e, (x ∈ S ↔ x ∈ S.erase e) := by
      intro x hx
      simp only [mem_erase]
      exact ⟨fun hs => ⟨(mem_erase.mp hx).1, hs⟩, fun hs => hs.2⟩
    by_cases heS : e ∈ S
    · rw [transaction, QueryProgram.run, ite_eq_left heS, ihy _ hy]
      rw [yes.run_congr _ S (S.erase e) hy ha, yes.queried_congr _ S (S.erase e) hy ha]
      simp only [run, queried, ite_eq_left heS]
      have heq : insert e I ∪ S ∩ yes.queried (S.erase e) =
          I ∪ S ∩ insert e (yes.queried (S.erase e)) := by
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS]
        · simp [hxe]
      rw [heq]
    · rw [transaction, QueryProgram.run, ite_eq_right heS, ihn _ hn]
      rw [no.run_congr _ S (S.erase e) hn ha, no.queried_congr _ S (S.erase e) hn ha]
      simp only [run, queried, ite_eq_right heS]
      have heq : I ∪ S ∩ no.queried (S.erase e) =
          I ∪ S ∩ insert e (no.queried (S.erase e)) := by
        ext x
        by_cases hxe : x = e
        · subst x; simp [heS]
        · simp [hxe]
      rw [heq]

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

omit [DecidableEq α] in
lemma reversePrefix_flat (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (j : ℕ) :
    M.IsFlat (reversePrefix M hE κ D C S k j) := by
  cases j with
  | zero =>
    by_cases hk : k < 0
    · simpa only [reversePrefix, ite_eq_left hk] using Matroid.isFlat_closure (M := M) ∅
    · simpa only [reversePrefix, ite_eq_right hk, ← hE] using M.ground_isFlat
  | succ j => exact Matroid.isFlat_closure (M := M) _

omit [DecidableEq α] in
lemma reverseNominal_flat (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (j : ℕ) :
    M.IsFlat (reverseNominal M hE κ D C S k j) :=
  densityEnabled_flat M hE κ (D j) (activation j) k (reversePrefix_flat M hE κ D C S k j)

omit [DecidableEq α] in

lemma reversePrefix_into_output (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C B S : ℕ → Set α) {l k : ℤ} (hlk : l ≤ k) (j : ℕ) :
    reversePrefix M hE κ D B (fun i => reverseNominal M hE κ D C S k i) l j ⊆
      reversePrefix M hE κ D C S k j := by
  induction j with
  | zero => exact guardedPath_mono M hE κ D C 0 hlk
  | succ j ih =>
    have hn := densityEnabled_mono M hE κ (D j) (activation j) hlk ih
    have hs : reversePrefix M hE κ D B (fun i => reverseNominal M hE κ D C S k i) l (j+1) ⊆
        reverseNominal M hE κ D C S k j := by
      exact (M.closure_subset_closure (Set.union_subset hn Set.inter_subset_right)).trans_eq
        (reverseNominal_flat M hE κ D C S k j).closure
    exact hs.trans (Set.subset_union_left.trans (M.subset_closure _ (by simp [hE])))

omit [DecidableEq α] in
lemma reverseNominal_into_output (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C B S : ℕ → Set α) {l k : ℤ} (hlk : l ≤ k) (j : ℕ) :
    reverseNominal M hE κ D B (fun i => reverseNominal M hE κ D C S k i) l j ⊆
      reverseNominal M hE κ D C S k j :=
  densityEnabled_mono M hE κ (D j) (activation j) hlk
    (reversePrefix_into_output M hE κ D C B S hlk j)

def ReverseClosed (M : Matroid α) (hE : M.E = Set.univ) (κ : ℕ)
    (D : ℕ → Set α) (k : ℤ) (S : ℕ → Set α) : Prop :=
  ∀ C j, reverseNominal M hE κ D C S k j ⊆ S j

omit [DecidableEq α] in
lemma reverseClosed_univ (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (k : ℤ) :
    ReverseClosed M hE κ D k (fun _ => Set.univ) := fun _ _ => Set.subset_univ _

noncomputable def reverseStepTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    RevealTree α (ℕ → Set α) :=
  (sourceReverseTree M hE κ k D S G n).record.map
    (fun r j => reverseNominal M hE κ D (fun i => (r.positive : Set α) ∩ (G i : Set α)) S k j)

lemma reverseStepTree_run (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    (reverseStepTree M hE κ k D S G n).run C =
      (fun j => reverseNominal M hE κ D
        (fun i => ((C ∩ (sourceReverseTree M hE κ k D S G n).queried C : Finset α) : Set α) ∩ (G i : Set α)) S k j) := by
  rw [reverseStepTree, RevealTree.run_map, RevealTree.record_run]

lemma reverseStepTree_run_coordinate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α) {j : ℕ} (hj : j ≤ n) :
    (reverseStepTree M hE κ k D S G n).run C j =
      reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  rw [reverseStepTree_run]
  exact sourceReverseTree_positive_nominal M hE κ k D S G n hG C hj

lemma reverseStepTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V) :
    (reverseStepTree M hE κ k D S G n).Fresh V := by
  rw [reverseStepTree, RevealTree.fresh_map, RevealTree.record_fresh]
  exact sourceReverseTree_fresh M hE κ k D S G n hG V hV

lemma reverseStepTree_queried (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    (reverseStepTree M hE κ k D S G n).queried C =
      (sourceReverseTree M hE κ k D S G n).queried C := by
  rw [reverseStepTree, RevealTree.queried_map, RevealTree.record_queried]

lemma reverseStepTree_closed (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    ReverseClosed M hE κ D (k-1) ((reverseStepTree M hE κ k D S G n).run C) := by
  rw [reverseStepTree_run]
  intro B j
  exact reverseNominal_into_output M hE κ D _ B S (by omega) j

lemma reverseStepTree_remaining (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    ∀ j < n, (G j).filter (fun e => e ∈ (reverseStepTree M hE κ k D S G n).run C j) ⊆
      V \ (reverseStepTree M hE κ k D S G n).queried C := by
  intro j hj e he
  rcases mem_filter.mp he with ⟨heG, heN⟩
  rw [reverseStepTree_run_coordinate M hE κ k D S G n hG C hj.le] at heN
  refine mem_sdiff.mpr ⟨hV j hj (mem_filter.mpr ⟨heG, closed _ j heN⟩), ?_⟩
  rw [reverseStepTree_queried,
    sourceReverseTree_queried_coordinate_full M hE κ k D S G n hG C hj heG]
  exact fun h => h.2 heN

noncomputable def reverseTransactions (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (stop : ℤ → (ℕ → Set α) → Prop) : ℕ → ℤ → (ℕ → Set α) → QueryProgram α
  | 0, _, _ => .stop
  | m+1, k, S => if stop k S then .stop else
      (reverseStepTree M hE κ k D S G n).transaction
        (fun S' => reverseTransactions M hE κ D G n stop m (k-1) S')

lemma reverseTransactions_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (stop : ℤ → (ℕ → Set α) → Prop) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (closed : ReverseClosed M hE κ D k S) :
    (reverseTransactions M hE κ D G n stop m k S).Fresh V := by
  induction m generalizing k S V with
  | zero => trivial
  | succ m ih =>
    rw [reverseTransactions]
    split_ifs with hs
    · trivial
    · apply RevealTree.transaction_fresh _ _ V (reverseStepTree_fresh M hE κ k D S G n hG V hV)
      intro C hC
      exact ih (k-1) _ _ (reverseStepTree_remaining M hE κ k D S G n hG V hV closed C)
        (reverseStepTree_closed M hE κ k D S G n C)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reverseNonexitCount (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (stop : ℤ → (ℕ → Set α) → Prop) (d : α) (h : ℕ) :
    ℕ → ℤ → (ℕ → Set α) → Finset α → ℝ
  | 0, _, _, _ => 0
  | m+1, k, S, C => if stop k S then 0 else
      (if d ∈ (reverseStepTree M hE κ k D S G n).run C h then 1 else 0) +
        reverseNonexitCount M hE κ D G n stop d h m (k-1)
          ((reverseStepTree M hE κ k D S G n).run C) C

lemma reverseStepTree_contracts (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) (j : ℕ) :
    (reverseStepTree M hE κ k D S G n).run C j ⊆ S j := by
  rw [reverseStepTree_run]
  exact closed _ j

noncomputable def reverseStayEvent (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (d : α) (h : ℕ)
    (C : Finset α) : Prop :=
  d ∈ reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k h

omit [DecidableEq α] in
lemma reverseStayEvent_mono (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (d : α) (h : ℕ) :
    Monotone (reverseStayEvent M hE κ D S G k d h) := by
  intro C C' hCC' he
  exact reverseNominal_mono M hE κ D _ _ S S le_rfl
    (fun j => Set.inter_subset_inter_left _ hCC') (fun _ => Set.Subset.rfl) h he

lemma reverseStepTree_nonexit_certificate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S S₀ : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    {k k₀ : ℤ} (hk : k ≤ k₀) (hS : ∀ j, S j ⊆ S₀ j)
    (C : Finset α) (d : α) (h : ℕ)
    (he : d ∈ (reverseStepTree M hE κ k D S G n).run C h) :
    reverseStayEvent M hE κ D S₀ G k₀ d h
      (C ∩ (reverseStepTree M hE κ k D S G n).queried C) := by
  rw [reverseStepTree_run] at he
  rw [reverseStepTree_queried]
  exact reverseNominal_mono M hE κ D _ _ S S₀ hk
    (fun _ => Set.Subset.rfl) hS h he

lemma reverseNonexitCount_le_transactions (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (stop : ℤ → (ℕ → Set α) → Prop) (d : α) (h : ℕ)
    (S₀ : ℕ → Set α) (k₀ : ℤ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (hk : k ≤ k₀) (hS : ∀ j, S j ⊆ S₀ j) (closed : ReverseClosed M hE κ D k S)
    (C : Finset α) :
    reverseNonexitCount M hE κ D G n stop d h m k S C ≤
      (reverseTransactions M hE κ D G n stop m k S).run
        (reverseStayEvent M hE κ D S₀ G k₀ d h) C ∅ := by
  induction m generalizing k S with
  | zero => simp [reverseNonexitCount, reverseTransactions, QueryProgram.run]
  | succ m ih =>
    rw [reverseNonexitCount, reverseTransactions]
    by_cases hs : stop k S
    · simp only [ite_eq_left hs, QueryProgram.run, le_refl]
    · simp only [ite_eq_right hs]
      rw [RevealTree.transaction_run _ _ univ
        (reverseStepTree_fresh M hE κ k D S G n hG univ (fun _ _ => subset_univ _))]
      simp only [empty_union]
      apply add_le_add
      · by_cases he : d ∈ (reverseStepTree M hE κ k D S G n).run C h
        · rw [ite_eq_left he, ite_eq_left (reverseStepTree_nonexit_certificate M hE κ D S S₀ G n hk hS C d h he)]
        · rw [ite_eq_right he]
          split_ifs <;> norm_num
      · exact ih (k-1) _ (by omega)
          (fun j => (reverseStepTree_contracts M hE κ k D S G n closed C j).trans (hS j))
          (reverseStepTree_closed M hE κ k D S G n C)

theorem reverse_nonexit_budget (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (stop : ℤ → (ℕ → Set α) → Prop) (d : α) (h : ℕ)
    (m : ℕ) (k₀ : ℤ) (S₀ : ℕ → Set α) (closed : ReverseClosed M hE κ D k₀ S₀)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure (reverseStayEvent M hE κ D S₀ G k₀ d h) q univ ∅) :
    bitsExpectation q univ (reverseNonexitCount M hE κ D G n stop d h m k₀ S₀) ≤
      Real.log (1 / bitsFailure (reverseStayEvent M hE κ D S₀ G k₀ d h) q univ ∅) := by
  apply le_trans (bitsExpectation_mono q hq0 hq1 univ
    (fun C _ => reverseNonexitCount_le_transactions M hE κ D G n hG stop d h S₀ k₀ m k₀ S₀
      le_rfl (fun _ => Set.Subset.rfl) closed C))
  exact disjoint_query_certificates_product _ (reverseStayEvent_mono M hE κ D S₀ G k₀ d h)
    q hq0 hq1 hδ _ (reverseTransactions_fresh M hE κ D G n hG stop m k₀ S₀ univ
      (fun _ _ => subset_univ _) closed)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α β : Type*} [DecidableEq α]

theorem RevealTree.continuation_expectation (tree : RevealTree α β)
    (q : α → ℝ) (V : Finset α) (fresh : tree.Fresh V)
    (f : β → Finset α → ℝ) :
    bitsExpectation q V (fun S => f (tree.run S) (S \ tree.queried S)) =
      bitsExpectation q V (fun S => bitsExpectation q (V \ tree.queried S)
        (fun T => f (tree.run S) T)) := by
  induction tree generalizing V with
  | leaf b => simp only [run, queried, sdiff_empty, bitsExpectation_const]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    let W := V.erase e
    have heW : e ∉ W := notMem_erase e V
    have hWV : insert e W = V := insert_erase he
    have leftSplit := bitsExpectation_insert q W e heW
      (fun S => f ((RevealTree.query e no yes).run S)
        (S \ (RevealTree.query e no yes).queried S))
    rw [hWV] at leftSplit
    have rightSplit := bitsExpectation_insert q W e heW
      (fun S => bitsExpectation q (V \ (RevealTree.query e no yes).queried S)
        (fun T => f ((RevealTree.query e no yes).run S) T))
    rw [hWV] at rightSplit
    have hSD (S Q : Finset α) (hS : S ⊆ W) :
        S \ insert e Q = S \ Q ∧ insert e S \ insert e Q = S \ Q := by
      have heS : e ∉ S := fun h => heW (hS h)
      constructor <;> ext x <;> by_cases hxe : x = e
      · subst x; simp [heS]
      · simp [hxe]
      · subst x; simp [heS]
      · simp [hxe]
    have hnoLeft : bitsExpectation q W (fun S => f ((RevealTree.query e no yes).run S)
        (S \ (RevealTree.query e no yes).queried S)) =
        bitsExpectation q W (fun S => f (no.run S) (S \ no.queried S)) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun h => heW (hS h)
      simp only [run, queried, ite_eq_right heS, erase_eq_of_notMem heS, (hSD S _ hS).1]
    have hyesLeft : bitsExpectation q W (fun S => f ((RevealTree.query e no yes).run (insert e S))
        (insert e S \ (RevealTree.query e no yes).queried (insert e S))) =
        bitsExpectation q W (fun S => f (yes.run S) (S \ yes.queried S)) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun h => heW (hS h)
      simp only [run, queried, mem_insert_self, ite_true, erase_insert heS, (hSD S _ hS).2]
    have hnoRight : bitsExpectation q W (fun S =>
        bitsExpectation q (V \ (RevealTree.query e no yes).queried S)
          (fun T => f ((RevealTree.query e no yes).run S) T)) =
        bitsExpectation q W (fun S => bitsExpectation q (W \ no.queried S)
          (fun T => f (no.run S) T)) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun h => heW (hS h)
      simp only [run, queried, ite_eq_right heS, erase_eq_of_notMem heS,
        ← erase_sdiff_eq_sdiff_insert, W]
    have hyesRight : bitsExpectation q W (fun S =>
        bitsExpectation q (V \ (RevealTree.query e no yes).queried (insert e S))
          (fun T => f ((RevealTree.query e no yes).run (insert e S)) T)) =
        bitsExpectation q W (fun S => bitsExpectation q (W \ yes.queried S)
          (fun T => f (yes.run S) T)) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun h => heW (hS h)
      simp only [run, queried, mem_insert_self, ite_true, erase_insert heS,
        ← erase_sdiff_eq_sdiff_insert, W]
    rw [leftSplit, rightSplit, hnoLeft, hyesLeft, hnoRight, hyesRight, ihn W hn, ihy W hy]

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reverseCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) :
    ℕ → ℤ → (ℕ → Set α) → Finset α → ℝ
  | 0, _, _, _ => 0
  | m+1, k, S, C => cost k S ((reverseStepTree M hE κ k D S G n).run C) +
      reverseCost M hE κ D G n cost m (k-1)
        ((reverseStepTree M hE κ k D S G n).run C) C

lemma reverseCost_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S)
    (C C' : Finset α)
    (agree : ∀ j < n, ∀ e ∈ G j, e ∈ S j → (e ∈ C ↔ e ∈ C')) :
    reverseCost M hE κ D G n cost m k S C = reverseCost M hE κ D G n cost m k S C' := by
  induction m generalizing k S with
  | zero => rfl
  | succ m ih =>
    let V := (range n).biUnion (fun j => (G j).filter (fun e => e ∈ S j))
    have hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V := by
      intro j hj e he
      exact mem_biUnion.mpr ⟨j, mem_range.mpr hj, he⟩
    have ha : ∀ e ∈ V, (e ∈ C ↔ e ∈ C') := by
      intro e he
      obtain ⟨j, hj, hje⟩ := mem_biUnion.mp he
      exact agree j (mem_range.mp hj) e (mem_filter.mp hje).1 (mem_filter.mp hje).2
    have hs := (reverseStepTree M hE κ k D S G n).run_congr V C C'
      (reverseStepTree_fresh M hE κ k D S G n hG V hV) ha
    simp only [reverseCost, hs]
    congr 1
    apply ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C')
    intro j hj e heG heS
    exact agree j hj e heG (reverseStepTree_contracts M hE κ k D S G n closed C' j heS)

lemma reverseCost_add (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n (fun k S S' => f k S S' + g k S S') m k S C =
      reverseCost M hE κ D G n f m k S C + reverseCost M hE κ D G n g m k S C := by
  induction m generalizing k S with
  | zero => simp [reverseCost]
  | succ m ih => simp only [reverseCost, ih]; ring

lemma reverseCost_mul (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) (a : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n (fun k S S' => a * f k S S') m k S C =
      a * reverseCost M hE κ D G n f m k S C := by
  induction m generalizing k S with
  | zero => simp [reverseCost]
  | succ m ih => simp only [reverseCost, ih]; ring

lemma reverseCost_mono (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (hfg : ∀ k S S', f k S S' ≤ g k S S')
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n f m k S C ≤ reverseCost M hE κ D G n g m k S C := by
  induction m generalizing k S with
  | zero => exact le_rfl
  | succ m ih => exact add_le_add (hfg _ _ _) (ih _ _)

noncomputable def reverseMeanCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) : ℝ :=
  bitsExpectation q univ (reverseCost M hE κ D G n cost m k S)

lemma reverseCost_erase_step (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    reverseCost M hE κ D G n cost m (k-1) ((reverseStepTree M hE κ k D S G n).run C) C =
      reverseCost M hE κ D G n cost m (k-1) ((reverseStepTree M hE κ k D S G n).run C)
        (C \ (reverseStepTree M hE κ k D S G n).queried C) := by
  apply reverseCost_congr M hE κ D G n hG cost m (k-1) _
    (reverseStepTree_closed M hE κ k D S G n C)
  intro j hj e heG heS
  have he := reverseStepTree_remaining M hE κ k D S G n hG univ
    (fun _ _ => subset_univ _) closed C j hj (mem_filter.mpr ⟨heG, heS⟩)
  simp only [mem_sdiff, (mem_sdiff.mp he).2, not_false_eq_true, and_true]

theorem reverseMeanCost_succ (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q cost (m+1) k S =
      bitsExpectation q univ (fun C => cost k S ((reverseStepTree M hE κ k D S G n).run C) +
        reverseMeanCost M hE κ D G n q cost m (k-1) ((reverseStepTree M hE κ k D S G n).run C)) := by
  let tree := reverseStepTree M hE κ k D S G n
  let f := fun (S' : ℕ → Set α) (C : Finset α) => reverseCost M hE κ D G n cost m (k-1) S' C
  have hfresh : tree.Fresh univ := reverseStepTree_fresh M hE κ k D S G n hG univ
    (fun _ _ => subset_univ _)
  have herase : bitsExpectation q univ (fun C => f (tree.run C) C) =
      bitsExpectation q univ (fun C => f (tree.run C) (C \ tree.queried C)) := by
    apply bitsExpectation_congr
    intro C hC
    exact reverseCost_erase_step M hE κ D G n hG cost m k S closed C
  have hrestrict : bitsExpectation q univ (fun C => bitsExpectation q (univ \ tree.queried C)
      (f (tree.run C))) = bitsExpectation q univ (fun C => bitsExpectation q univ (f (tree.run C))) := by
    apply bitsExpectation_congr
    intro C hC
    symm
    apply bitsExpectation_restrict q univ _ (subset_univ _) (f (tree.run C))
    intro T T' hT
    apply reverseCost_congr M hE κ D G n hG cost m (k-1) _
      (reverseStepTree_closed M hE κ k D S G n C)
    intro j hj e heG heS
    exact hT e (reverseStepTree_remaining M hE κ k D S G n hG univ
      (fun _ _ => subset_univ _) closed C j hj (mem_filter.mpr ⟨heG, heS⟩))
  have htower := tree.continuation_expectation q univ hfresh f
  change bitsExpectation q univ (fun C => cost k S (tree.run C) + f (tree.run C) C) =
    bitsExpectation q univ (fun C => cost k S (tree.run C) + bitsExpectation q univ (f (tree.run C)))
  rw [bitsExpectation_add, bitsExpectation_add, herase, htower, hrestrict]

@[simp] lemma reverseMeanCost_zero (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) (k : ℤ) (S : ℕ → Set α) :
    reverseMeanCost M hE κ D G n q cost 0 k S = 0 := by
  simp only [reverseMeanCost, reverseCost, bitsExpectation_const]

lemma reverseMeanCost_add (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) :
    reverseMeanCost M hE κ D G n q (fun k S S' => f k S S' + g k S S') m k S =
      reverseMeanCost M hE κ D G n q f m k S + reverseMeanCost M hE κ D G n q g m k S := by
  unfold reverseMeanCost
  rw [← bitsExpectation_add]
  exact bitsExpectation_congr q univ (fun C _ => reverseCost_add M hE κ D G n f g m k S C)

lemma reverseMeanCost_mul (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (f : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) (a : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) :
    reverseMeanCost M hE κ D G n q (fun k S S' => a * f k S S') m k S =
      a * reverseMeanCost M hE κ D G n q f m k S := by
  unfold reverseMeanCost
  rw [← bitsExpectation_mul_left]
  exact bitsExpectation_congr q univ (fun C _ => reverseCost_mul M hE κ D G n f a m k S C)

theorem reverseMeanCost_le_of_step (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (hfg : ∀ k S, ReverseClosed M hE κ D k S →
      bitsExpectation q univ (fun C => f k S ((reverseStepTree M hE κ k D S G n).run C)) ≤
      bitsExpectation q univ (fun C => g k S ((reverseStepTree M hE κ k D S G n).run C)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q f m k S ≤ reverseMeanCost M hE κ D G n q g m k S := by
  induction m generalizing k S with
  | zero => simp only [reverseMeanCost_zero, le_refl]
  | succ m ih =>
    rw [reverseMeanCost_succ M hE κ D G n hG q f m k S closed,
      reverseMeanCost_succ M hE κ D G n hG q g m k S closed,
      bitsExpectation_add, bitsExpectation_add]
    apply add_le_add (hfg k S closed)
    apply bitsExpectation_mono q hq0 hq1
    intro C hC
    exact ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)

theorem reverseMeanCost_eq_of_step (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (hfg : ∀ k S, ReverseClosed M hE κ D k S →
      bitsExpectation q univ (fun C => f k S ((reverseStepTree M hE κ k D S G n).run C)) =
      bitsExpectation q univ (fun C => g k S ((reverseStepTree M hE κ k D S G n).run C)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q f m k S = reverseMeanCost M hE κ D G n q g m k S :=
  le_antisymm (reverseMeanCost_le_of_step M hE κ D G n hG q hq0 hq1 f g
    (fun k S hS => (hfg k S hS).le) m k S closed)
    (reverseMeanCost_le_of_step M hE κ D G n hG q hq0 hq1 g f
    (fun k S hS => (hfg k S hS).ge) m k S closed)

lemma reverseCost_sum {ι : Type*} (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (I : Finset ι) (f : ι → ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n (fun k S S' => ∑ i ∈ I, f i k S S') m k S C =
      ∑ i ∈ I, reverseCost M hE κ D G n (f i) m k S C := by
  induction m generalizing k S with
  | zero => simp only [reverseCost, sum_const_zero]
  | succ m ih => simp only [reverseCost, ih, sum_add_distrib]

lemma reverseMeanCost_sum {ι : Type*} (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (I : Finset ι) (f : ι → ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) :
    reverseMeanCost M hE κ D G n q (fun k S S' => ∑ i ∈ I, f i k S S') m k S =
      ∑ i ∈ I, reverseMeanCost M hE κ D G n q (f i) m k S := by
  unfold reverseMeanCost
  rw [← bitsExpectation_sum]
  exact bitsExpectation_congr q univ (fun C _ => reverseCost_sum M hE κ D G n I f m k S C)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reverseHazard (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) : ℝ :=
  bitsFailure (reverseStayEvent M hE κ D S G k d h) q univ ∅

lemma reverseHazard_eq (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) :
    reverseHazard M hE κ D G q d h k S = bitsExpectation q univ (fun C =>
      if d ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k h then 1 else 0) := by
  unfold reverseHazard bitsFailure reverseStayEvent
  apply bitsExpectation_congr
  intro C hC
  simp only [empty_union]
  split_ifs <;> simp_all

lemma reverseHazard_nonneg (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) : 0 ≤ reverseHazard M hE κ D G q d h k S :=
  bitsFailure_nonneg _ q hq0 hq1 _ _

lemma reverseHazard_le_one (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) : reverseHazard M hE κ D G q d h k S ≤ 1 :=
  bitsFailure_le_one _ q hq0 hq1 _ _

lemma reverseHazard_mono (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ)
    {k l : ℤ} (hlk : l ≤ k) (S S' : ℕ → Set α) (hS : ∀ j, S' j ⊆ S j) :
    reverseHazard M hE κ D G q d h k S ≤ reverseHazard M hE κ D G q d h l S' := by
  rw [reverseHazard_eq, reverseHazard_eq]
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  have hn := reverseNominal_mono M hE κ D
    (fun i => (C : Set α) ∩ (G i : Set α)) _ S' S hlk (fun _ => Set.Subset.rfl) hS h
  by_cases he : d ∈ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S' l h
  · simp [he, hn he]
  · simp [he]
    split_ifs <;> norm_num

lemma reverseHazard_step_mono (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    reverseHazard M hE κ D G q d h k S ≤
      reverseHazard M hE κ D G q d h (k-1) ((reverseStepTree M hE κ k D S G n).run C) :=
  reverseHazard_mono M hE κ D G q hq0 hq1 d h (by omega) S _
    (reverseStepTree_contracts M hE κ k D S G n closed C)

lemma reverseHazard_eq_step (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ) (d : α) (h : ℕ) (hh : h ≤ n)
    (k : ℤ) (S : ℕ → Set α) :
    reverseHazard M hE κ D G q d h k S = bitsExpectation q univ (fun C =>
      if d ∉ (reverseStepTree M hE κ k D S G n).run C h then 1 else 0) := by
  rw [reverseHazard_eq]
  apply bitsExpectation_congr
  intro C hC
  rw [reverseStepTree_run_coordinate M hE κ k D S G n hG C hh]

noncomputable def bandNonexitCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (p₀ upper : ℝ) (k : ℤ) (S S' : ℕ → Set α) : ℝ :=
  if p₀ ≤ reverseHazard M hE κ D G q d h k S ∧
      reverseHazard M hE κ D G q d h k S < upper ∧ d ∈ S' h then 1 else 0

lemma bandNonexitCost_zero_above (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (p₀ upper : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S)
    (hu : upper ≤ reverseHazard M hE κ D G q d h k S) (C : Finset α) :
    reverseCost M hE κ D G n (bandNonexitCost M hE κ D G q d h p₀ upper) m k S C = 0 := by
  induction m generalizing k S with
  | zero => rfl
  | succ m ih =>
    rw [reverseCost, bandNonexitCost, ite_eq_right (fun hc => (not_lt_of_ge hu) hc.2.1)]
    have hm := reverseHazard_step_mono M hE κ D G n q hq0 hq1 d h k S closed C
    rw [ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C) (hu.trans hm)]
    exact zero_add 0

lemma bandNonexitCost_eq_count (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (p₀ upper : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S)
    (hl : p₀ ≤ reverseHazard M hE κ D G q d h k S) (C : Finset α) :
    reverseCost M hE κ D G n (bandNonexitCost M hE κ D G q d h p₀ upper) m k S C =
      reverseNonexitCount M hE κ D G n
        (fun k S => upper ≤ reverseHazard M hE κ D G q d h k S) d h m k S C := by
  induction m generalizing k S with
  | zero => rfl
  | succ m ih =>
    by_cases hu : upper ≤ reverseHazard M hE κ D G q d h k S
    · rw [bandNonexitCost_zero_above M hE κ D G n q hq0 hq1 d h p₀ upper (m+1) k S closed hu C,
        reverseNonexitCount, ite_eq_left hu]
    · have hlt := lt_of_not_ge hu
      rw [reverseCost, reverseNonexitCount, ite_eq_right hu]
      simp only [bandNonexitCost, hl, hlt, true_and]
      congr 1
      exact ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)
        (hl.trans (reverseHazard_step_mono M hE κ D G n q hq0 hq1 d h k S closed C))

theorem bandNonexitCost_budget_after_entry (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (p₀ upper : ℝ)
    (hp : 0 < p₀) (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S)
    (hl : p₀ ≤ reverseHazard M hE κ D G q d h k S) :
    reverseMeanCost M hE κ D G n q (bandNonexitCost M hE κ D G q d h p₀ upper) m k S ≤
      Real.log (1 / p₀) := by
  unfold reverseMeanCost
  have heq : bitsExpectation q univ
      (reverseCost M hE κ D G n (bandNonexitCost M hE κ D G q d h p₀ upper) m k S) =
      bitsExpectation q univ (reverseNonexitCount M hE κ D G n
        (fun k S => upper ≤ reverseHazard M hE κ D G q d h k S) d h m k S) := by
    apply bitsExpectation_congr
    intro C hC
    exact bandNonexitCost_eq_count M hE κ D G n q hq0 hq1 d h p₀ upper m k S closed hl C
  rw [heq]
  apply (reverse_nonexit_budget M hE κ D G n hG _ d h m k S closed q hq0 hq1 (hp.trans_le hl)).trans
  apply Real.log_le_log
  · exact one_div_pos.mpr (hp.trans_le hl)
  · exact one_div_le_one_div_of_le hp hl

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

structure ReverseTransition (α : Type*) where
  time : ℤ
  before : ℕ → Set α
  after : ℕ → Set α

noncomputable def reverseTrace (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    ℕ → ℤ → (ℕ → Set α) → Finset α → List (ReverseTransition α)
  | 0, _, _, _ => []
  | m+1, k, S, C =>
      ⟨k, S, (reverseStepTree M hE κ k D S G n).run C⟩ ::
      reverseTrace M hE κ D G n m (k-1) ((reverseStepTree M hE κ k D S G n).run C) C

lemma reverseCost_le_of_trace (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α)
    (hfg : ∀ t ∈ reverseTrace M hE κ D G n m k S C,
      f t.time t.before t.after ≤ g t.time t.before t.after) :
    reverseCost M hE κ D G n f m k S C ≤ reverseCost M hE κ D G n g m k S C := by
  induction m generalizing k S with
  | zero => exact le_rfl
  | succ m ih =>
    rw [reverseCost, reverseCost]
    apply add_le_add (hfg ⟨k, S, (reverseStepTree M hE κ k D S G n).run C⟩ (by simp [reverseTrace]))
    exact ih _ _ (fun t ht => hfg t (by simp only [reverseTrace, List.mem_cons]; exact Or.inr ht))

noncomputable def traceHazards (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ) (d : α) (h : ℕ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) : Finset ℝ :=
  univ.biUnion (fun C : Finset α => ((reverseTrace M hE κ D G n m k S C).map
    (fun t => reverseHazard M hE κ D G q d h t.time t.before)).toFinset)

lemma mem_traceHazards (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ) (d : α) (h : ℕ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) (t : ReverseTransition α)
    (ht : t ∈ reverseTrace M hE κ D G n m k S C) :
    reverseHazard M hE κ D G q d h t.time t.before ∈ traceHazards M hE κ D G n q d h m k S := by
  exact mem_biUnion.mpr ⟨C, mem_univ C, List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, ht, rfl⟩)⟩

noncomputable def reverseFinal (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    ℕ → ℤ → (ℕ → Set α) → Finset α → (ℕ → Set α)
  | 0, _, S, _ => S
  | m+1, k, S, C => reverseFinal M hE κ D G n m (k-1)
      ((reverseStepTree M hE κ k D S G n).run C) C

lemma reverseStepTree_path (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (k : ℤ) (S : ℕ → Set α) (C : Finset α)
    (hS : ∀ j ≤ n, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (k+1))
    {j : ℕ} (hj : j ≤ n) :
    (reverseStepTree M hE κ k D S G n).run C j =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j k := by
  rw [reverseStepTree_run_coordinate M hE κ k D S G n hG C hj]
  calc
    _ = reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
        (fun i => nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) i (k+1)) k j := by
      apply reverseNominal_congr_before
      · intro i hi; rfl
      · intro i hi; exact hS i (by omega)
    _ = _ := reverseNominal_agrees M hE κ D _ k j

lemma reverseFinal_path (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α)
    (hS : ∀ j ≤ n, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (k+1))
    {j : ℕ} (hj : j ≤ n) :
    reverseFinal M hE κ D G n m k S C j =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (k+1-m) := by
  induction m generalizing k S with
  | zero => simpa only [reverseFinal, Nat.cast_zero, sub_zero] using hS j hj
  | succ m ih =>
    rw [reverseFinal]
    have hs' : ∀ i ≤ n, (reverseStepTree M hE κ k D S G n).run C i =
        nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) i (k-1+1) := by
      intro i hi
      simpa only [sub_add_cancel] using reverseStepTree_path M hE κ D G n hG k S C hS hi
    rw [ih (k-1) _ hs']
    congr 1
    omega

lemma reverseFinal_from_univ (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h : ℕ) (hh : h ≤ n) (C : Finset α) :
    reverseFinal M hE κ D G n (pathHorizon h + 1) (-1) (fun _ => Set.univ) C h = M.closure ∅ := by
  rw [reverseFinal_path M hE κ D G n hG (pathHorizon h+1) (-1) (fun _ => Set.univ) C
    (fun j hj => by simpa only [neg_add_cancel] using
      (nominalPath_nonnegative M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (by omega : (0:ℤ) ≤ -1+1)).symm) hh]
  apply nominalPath_early
  unfold pathHorizon activation
  omega

noncomputable def exitCost (d : α) (h : ℕ) (_ : ℤ) (S S' : ℕ → Set α) : ℝ :=
  if d ∈ S h ∧ d ∉ S' h then 1 else 0

lemma reverseCost_exit_telescope (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (d : α) (h : ℕ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    reverseCost M hE κ D G n (exitCost d h) m k S C =
      (if d ∈ S h then 1 else 0) - (if d ∈ reverseFinal M hE κ D G n m k S C h then 1 else 0) := by
  induction m generalizing k S with
  | zero => by_cases hs : d ∈ S h <;> simp [reverseCost, reverseFinal, hs]
  | succ m ih =>
    rw [reverseCost, reverseFinal, ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)]
    have hc := reverseStepTree_contracts M hE κ k D S G n closed C h
    by_cases hs : d ∈ S h <;> by_cases hn : d ∈ (reverseStepTree M hE κ k D S G n).run C h
    · simp [exitCost, hs, hn]
    · simp [exitCost, hs, hn]; ring
    · exact (hs (hc hn)).elim
    · simp [exitCost, hs, hn]

lemma reverse_exit_total_one (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) (hh : h ≤ n) :
    reverseMeanCost M hE κ D G n q (exitCost d h) (pathHorizon h+1) (-1) (fun _ => Set.univ) = 1 := by
  unfold reverseMeanCost
  have hp : ∀ C : Finset α, reverseCost M hE κ D G n (exitCost d h)
      (pathHorizon h+1) (-1) (fun _ => Set.univ) C = 1 := by
    intro C
    rw [reverseCost_exit_telescope M hE κ D G n d h (pathHorizon h+1) (-1) _
      (reverseClosed_univ M hE κ D (-1)) C, reverseFinal_from_univ M hE κ D G n hG h hh C]
    simp [hd]
  exact (bitsExpectation_congr q univ (fun C _ => hp C)).trans (bitsExpectation_const q univ 1)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reversePrefixTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    ℕ → ℤ → (ℕ → Set α) → RevealTree α (ℕ → Set α)
  | 0, _, S => .leaf S
  | m+1, k, S => (reverseStepTree M hE κ k D S G n).bind
      (fun S' => reversePrefixTree M hE κ D G n m (k-1) S')

lemma reversePrefixTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (V : Finset α)
    (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (closed : ReverseClosed M hE κ D k S) :
    (reversePrefixTree M hE κ D G n m k S).Fresh V := by
  induction m generalizing k S V with
  | zero => trivial
  | succ m ih =>
    apply RevealTree.fresh_bind _ _ V (reverseStepTree_fresh M hE κ k D S G n hG V hV)
    intro C hC
    exact ih (k-1) _ _ (reverseStepTree_remaining M hE κ k D S G n hG V hV closed C)
      (reverseStepTree_closed M hE κ k D S G n C)

lemma reversePrefixTree_remaining (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (V : Finset α)
    (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    ∀ j < n, (G j).filter (fun e => e ∈ (reversePrefixTree M hE κ D G n m k S).run C j) ⊆
      V \ (reversePrefixTree M hE κ D G n m k S).queried C := by
  induction m generalizing k S V C with
  | zero => simpa only [reversePrefixTree, RevealTree.run, RevealTree.queried, sdiff_empty] using hV
  | succ m ih =>
    rw [reversePrefixTree, RevealTree.run_bind, RevealTree.queried_bind]
    have hr := ih (k-1) _ _
      (reverseStepTree_remaining M hE κ k D S G n hG V hV closed C)
      (reverseStepTree_closed M hE κ k D S G n C)
      (C \ (reverseStepTree M hE κ k D S G n).queried C)
    intro j hj e he
    have hx := mem_sdiff.mp (hr j hj he)
    have hy := mem_sdiff.mp hx.1
    exact mem_sdiff.mpr ⟨hy.1, fun hm => (mem_union.mp hm).elim hy.2 hx.2⟩

lemma reversePrefixTree_run (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    (reversePrefixTree M hE κ D G n m k S).run C = reverseFinal M hE κ D G n m k S C := by
  induction m generalizing k S C with
  | zero => rfl
  | succ m ih =>
    rw [reversePrefixTree, RevealTree.run_bind, reverseFinal]
    let W := univ \ (reverseStepTree M hE κ k D S G n).queried C
    have hW := reverseStepTree_remaining M hE κ k D S G n hG univ
      (fun _ _ => subset_univ _) closed C
    have hc := reverseStepTree_closed M hE κ k D S G n C
    have hcongr := (reversePrefixTree M hE κ D G n m (k-1)
      ((reverseStepTree M hE κ k D S G n).run C)).run_congr W
      (C \ (reverseStepTree M hE κ k D S G n).queried C) C
      (reversePrefixTree_fresh M hE κ D G n hG m (k-1) _ W hW hc)
      (fun e he => by
        have hne := (mem_sdiff.mp he).2
        simp only [mem_sdiff, hne, not_false_eq_true, and_true])
    rw [hcongr, ih (k-1) _ hc C]

theorem reversePrefixTree_tower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (q : α → ℝ)
    (f : (ℕ → Set α) → Finset α → ℝ)
    (hf : ∀ R C C', (∀ j < n, ∀ e ∈ G j, e ∈ R j → (e ∈ C ↔ e ∈ C')) → f R C = f R C') :
    bitsExpectation q univ (fun C => f ((reversePrefixTree M hE κ D G n m k S).run C) C) =
      bitsExpectation q univ (fun C => bitsExpectation q univ
        (f ((reversePrefixTree M hE κ D G n m k S).run C))) := by
  let tree := reversePrefixTree M hE κ D G n m k S
  have hrem := reversePrefixTree_remaining M hE κ D G n hG m k S univ
    (fun _ _ => subset_univ _) closed
  have he : bitsExpectation q univ (fun C => f (tree.run C) C) =
      bitsExpectation q univ (fun C => f (tree.run C) (C \ tree.queried C)) := by
    apply bitsExpectation_congr
    intro C hC
    apply hf
    intro j hj e heG heR
    have hx := (mem_sdiff.mp (hrem C j hj (mem_filter.mpr ⟨heG, heR⟩))).2
    change e ∉ tree.queried C at hx
    simp only [mem_sdiff, hx, not_false_eq_true, and_true]
  rw [he, tree.continuation_expectation q univ
    (reversePrefixTree_fresh M hE κ D G n hG m k S univ (fun _ _ => subset_univ _) closed)]
  apply bitsExpectation_congr
  intro C hC
  symm
  apply bitsExpectation_restrict q univ _ (subset_univ _) (f (tree.run C))
  intro T T' hTT'
  apply hf
  intro j hj e heG heR
  exact hTT' e (hrem C j hj (mem_filter.mpr ⟨heG, heR⟩))

lemma reverseNominal_mask_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (n : ℕ)
    (C C' : Finset α)
    (hC : ∀ j < n, ∀ e ∈ G j, e ∈ S j → (e ∈ C ↔ e ∈ C')) :
    reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n =
      reverseNominal M hE κ D (fun j => (C' : Set α) ∩ (G j : Set α)) S k n := by
  unfold reverseNominal
  congr 1
  apply reversePrefix_congr_guard_inter
  intro j hj
  ext e
  by_cases heG : e ∈ G j
  · by_cases heS : e ∈ S j
    · simp only [Set.mem_inter_iff, mem_coe, heG, heS, and_true, hC j hj e heG heS]
    · simp [heS]
  · simp [heG]

lemma reverseHybrid_mask_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (n : ℕ)
    (C C' T : Finset α)
    (hC : ∀ j < n, ∀ e ∈ G j, e ∈ S j → (e ∈ C ↔ e ∈ C')) :
    reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n =
      reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C' T) S k n := by
  unfold reverseNominal
  congr 1
  apply reversePrefix_congr_guard_inter
  intro j hj
  have hn := reverseNominal_mask_congr M hE κ D S G k j C C'
    (fun i hi => hC i (by omega))
  ext e
  by_cases heG : e ∈ G j
  · by_cases heS : e ∈ S j
    · simp only [transitionHybrid, hn, Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff,
        mem_coe, heG, heS, true_and, and_true, hC j hj e heG heS]
    · simp [heS]
  · simp [transitionHybrid, heG]

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open Finset

noncomputable def hazardBandBound (l : ℕ) : ℝ :=
  (((l : ℝ) + 1) * Real.log 2 + 1) / 2 ^ l

noncomputable def hazardTailPotential (l : ℕ) : ℝ :=
  2 * (((l : ℝ) + 2) * Real.log 2 + 1) / 2 ^ l

lemma hazardTailPotential_nonneg (l : ℕ) : 0 ≤ hazardTailPotential l := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : 0 ≤ (l : ℝ) + 2 := by positivity
  exact div_nonneg (mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg hl hlog) (by norm_num))) (pow_nonneg (by norm_num) _)

lemma hazardTailPotential_step (l : ℕ) :
    hazardTailPotential l = hazardBandBound l + hazardTailPotential (l + 1) := by
  unfold hazardTailPotential hazardBandBound
  push_cast
  rw [pow_succ]
  field_simp
  ring

lemma hazardBandBound_sum (start length : ℕ) :
    (∑ k ∈ range length, hazardBandBound (start + k)) +
      hazardTailPotential (start + length) = hazardTailPotential start := by
  induction length with
  | zero => simp
  | succ length ih =>
    rw [sum_range_succ]
    have h := hazardTailPotential_step (start + length)
    rw [Nat.add_succ]
    linarith

lemma hazardTailPotential_twelve : hazardTailPotential 12 < (1 : ℝ) / 2 := by
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  unfold hazardTailPotential
  norm_num
  linarith

theorem hazardBandBound_sum_lt_half (length : ℕ) :
    (∑ k ∈ range length, hazardBandBound (12 + k)) < (1 : ℝ) / 2 := by
  have h := hazardBandBound_sum 12 length
  have hn := hazardTailPotential_nonneg (12 + length)
  have hu := hazardTailPotential_twelve
  linarith

theorem squared_exit_mass {ι : Type*} [Fintype ι]
    (mass hazard : ι → ℝ) (eta : ℝ)
    (hmass : ∀ i, 0 ≤ mass i) (hhazard : ∀ i, 0 ≤ hazard i) (heta : 0 ≤ eta)
    (htotal : ∑ i, mass i * hazard i = 1)
    (hlow : (∑ i, if hazard i < eta then mass i * hazard i else 0) ≤ (1 : ℝ) / 2) :
    eta / 2 ≤ ∑ i, mass i * (hazard i) ^ 2 := by
  classical
  have hpoint (i : ι) : eta * (mass i * hazard i) ≤
      mass i * (hazard i)^2 + eta * (if hazard i < eta then mass i * hazard i else 0) := by
    by_cases h : hazard i < eta
    · rw [ite_eq_left h]
      have hn := mul_nonneg (hmass i) (sq_nonneg (hazard i))
      linarith
    · rw [ite_eq_right h]
      have hh : eta ≤ hazard i := le_of_not_gt h
      have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg (hmass i) (hhazard i))
      nlinarith
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => hpoint i)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, htotal] at hsum
  have hl := mul_le_mul_of_nonneg_left hlow heta
  nlinarith

theorem exit_band_bound {ι : Type*} [Fintype ι]
    (mass hazard : ι → ℝ) (upper budget : ℝ)
    (hmass : ∀ i, 0 ≤ mass i) (hupper : 0 ≤ upper)
    (hhazard : ∀ i, hazard i ≤ upper)
    (hsuccess : (∑ i, mass i * (1 - hazard i)) ≤ budget)
    (hexit : (∑ i, mass i * hazard i) ≤ 1) :
    (∑ i, mass i * hazard i) ≤ upper * (budget + 1) := by
  have htotal : (∑ i, mass i) =
      (∑ i, mass i * (1 - hazard i)) + ∑ i, mass i * hazard i := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  have ht : (∑ i, mass i) ≤ budget + 1 := by linarith
  have hb : (∑ i, mass i * hazard i) ≤ upper * ∑ i, mass i := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hhazard i) (hmass i)
  exact hb.trans (mul_le_mul_of_nonneg_left ht hupper)

lemma hazardBandBound_eq_certificate_bound (l : ℕ) :
    2 * (((2 : ℝ) ^ (l + 1))⁻¹) *
      (Real.log (1 / (((2 : ℝ) ^ (l + 1))⁻¹)) + 1) = hazardBandBound l := by
  rw [one_div, inv_inv, Real.log_pow]
  unfold hazardBandBound
  push_cast
  rw [pow_succ]
  field_simp

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

theorem bandNonexitCost_budget (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (p₀ upper : ℝ)
    (hp : 0 < p₀) (hp1 : p₀ ≤ 1) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandNonexitCost M hE κ D G q d h p₀ upper) m k S ≤
      Real.log (1 / p₀) := by
  have hlog : 0 ≤ Real.log (1 / p₀) := Real.log_nonneg ((one_le_div hp).mpr hp1)
  induction m generalizing k S with
  | zero => simpa only [reverseMeanCost_zero] using hlog
  | succ m ih =>
    by_cases hl : p₀ ≤ reverseHazard M hE κ D G q d h k S
    · exact bandNonexitCost_budget_after_entry M hE κ D G n hG q hq0 hq1 d h p₀ upper hp (m+1) k S closed hl
    · rw [reverseMeanCost_succ M hE κ D G n hG q _ m k S closed]
      calc
        _ ≤ bitsExpectation q univ (fun _ => Real.log (1 / p₀)) := by
          apply bitsExpectation_mono q hq0 hq1
          intro C hC
          simp only [bandNonexitCost, hl, false_and, ↓reduceIte, zero_add]
          exact ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)
        _ = _ := bitsExpectation_const q univ _

noncomputable def bandExitCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (p₀ upper : ℝ) (k : ℤ) (S S' : ℕ → Set α) : ℝ :=
  if p₀ ≤ reverseHazard M hE κ D G q d h k S ∧
      reverseHazard M hE κ D G q d h k S < upper ∧ d ∈ S h ∧ d ∉ S' h then 1 else 0

noncomputable def bandCountCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (p₀ upper : ℝ) (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if p₀ ≤ reverseHazard M hE κ D G q d h k S ∧
      reverseHazard M hE κ D G q d h k S < upper ∧ d ∈ S h then 1 else 0

lemma bandCountCost_step_split (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (d : α) (h : ℕ) (p₀ upper : ℝ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    bandCountCost M hE κ D G q d h p₀ upper k S ((reverseStepTree M hE κ k D S G n).run C) =
      bandNonexitCost M hE κ D G q d h p₀ upper k S ((reverseStepTree M hE κ k D S G n).run C) +
      bandExitCost M hE κ D G q d h p₀ upper k S ((reverseStepTree M hE κ k D S G n).run C) := by
  have hc := reverseStepTree_contracts M hE κ k D S G n closed C h
  unfold bandCountCost bandNonexitCost bandExitCost
  by_cases hS : d ∈ S h <;> by_cases hN : d ∈ (reverseStepTree M hE κ k D S G n).run C h
  · simp [hS, hN]
  · simp [hS, hN]
  · exact (hS (hc hN)).elim
  · simp [hS, hN]

lemma bandCountCost_mean_split (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (d : α) (h : ℕ) (p₀ upper : ℝ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandCountCost M hE κ D G q d h p₀ upper) m k S =
      reverseMeanCost M hE κ D G n q (bandNonexitCost M hE κ D G q d h p₀ upper) m k S +
      reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S := by
  have hpoint (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
      reverseCost M hE κ D G n (bandCountCost M hE κ D G q d h p₀ upper) m k S C =
        reverseCost M hE κ D G n (bandNonexitCost M hE κ D G q d h p₀ upper) m k S C +
        reverseCost M hE κ D G n (bandExitCost M hE κ D G q d h p₀ upper) m k S C := by
    induction m generalizing k S with
    | zero => simp only [reverseCost, add_zero]
    | succ m ih =>
      rw [reverseCost, reverseCost, reverseCost, bandCountCost_step_split M hE κ D G n q d h p₀ upper k S closed C,
        ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)]
      ring
  unfold reverseMeanCost
  rw [← bitsExpectation_add]
  exact bitsExpectation_congr q univ (fun C _ => hpoint m k S closed C)

lemma bandExitCost_count_le_one (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (d : α) (h : ℕ) (p₀ upper : ℝ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    reverseCost M hE κ D G n (bandExitCost M hE κ D G q d h p₀ upper) m k S C ≤
      if d ∈ S h then 1 else 0 := by
  induction m generalizing k S with
  | zero => simp only [reverseCost]; split_ifs <;> norm_num
  | succ m ih =>
    have hi := ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)
    have hc := reverseStepTree_contracts M hE κ k D S G n closed C h
    rw [reverseCost]
    by_cases hS : d ∈ S h <;> by_cases hN : d ∈ (reverseStepTree M hE κ k D S G n).run C h
    · simpa [bandExitCost, hS, hN] using hi
    · simp only [hN, ite_false] at hi
      have hb : bandExitCost M hE κ D G q d h p₀ upper k S ((reverseStepTree M hE κ k D S G n).run C) ≤ 1 := by
        unfold bandExitCost
        split_ifs <;> norm_num
      simpa only [hS, ite_true, add_zero] using add_le_add hb hi
    · exact (hS (hc hN)).elim
    · simpa [bandExitCost, hS, hN] using hi

lemma bandExitCost_mean_le_one (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (p₀ upper : ℝ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S ≤ 1 := by
  unfold reverseMeanCost
  calc
    _ ≤ bitsExpectation q univ (fun _ => 1) := by
      apply bitsExpectation_mono q hq0 hq1
      intro C hC
      apply (bandExitCost_count_le_one M hE κ D G n q d h p₀ upper m k S closed C).trans
      split_ifs <;> norm_num
    _ = 1 := bitsExpectation_one q univ

lemma bandExitCost_le_upper_count (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (p₀ upper : ℝ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S ≤
      upper * reverseMeanCost M hE κ D G n q (bandCountCost M hE κ D G q d h p₀ upper) m k S := by
  rw [← reverseMeanCost_mul]
  apply reverseMeanCost_le_of_step M hE κ D G n hG q hq0 hq1
  · intro l R hR
    by_cases hb : p₀ ≤ reverseHazard M hE κ D G q d h l R ∧
        reverseHazard M hE κ D G q d h l R < upper ∧ d ∈ R h
    · have heq : bitsExpectation q univ (fun C => bandExitCost M hE κ D G q d h p₀ upper l R
          ((reverseStepTree M hE κ l D R G n).run C)) = reverseHazard M hE κ D G q d h l R := by
        rw [reverseHazard_eq_step M hE κ D G n hG q d h hh]
        apply bitsExpectation_congr
        intro C hC
        simp only [bandExitCost, hb.1, hb.2.1, hb.2.2, true_and]
      rw [heq]
      simpa only [bandCountCost, hb.1, hb.2.1, hb.2.2, true_and, ite_true, mul_one, bitsExpectation_const] using hb.2.1.le
    · have hz : ∀ C, bandExitCost M hE κ D G q d h p₀ upper l R
          ((reverseStepTree M hE κ l D R G n).run C) = 0 := by
        intro C
        unfold bandExitCost
        apply ite_eq_right
        intro hc
        exact hb ⟨hc.1, hc.2.1, hc.2.2.1⟩
      simp only [hz, bandCountCost, hb, ite_false, mul_zero, bitsExpectation_const, le_refl]
  · exact closed

theorem reverse_exit_band_bound (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (p₀ upper : ℝ) (hp : 0 < p₀) (hp1 : p₀ ≤ 1) (hu : 0 ≤ upper)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S ≤
      upper * (Real.log (1 / p₀) + 1) := by
  have he := bandExitCost_le_upper_count M hE κ D G n hG q hq0 hq1 d h hh p₀ upper m k S closed
  rw [bandCountCost_mean_split M hE κ D G n q d h p₀ upper m k S closed] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ hu
  exact add_le_add (bandNonexitCost_budget M hE κ D G n hG q hq0 hq1 d h p₀ upper hp hp1 m k S closed)
    (bandExitCost_mean_le_one M hE κ D G n q hq0 hq1 d h p₀ upper m k S closed)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset

noncomputable def inHazardBand (p : ℝ) (l : ℕ) : Prop :=
  ((2 : ℝ) ^ (l+1))⁻¹ ≤ p ∧ p < ((2 : ℝ) ^ l)⁻¹

lemma exists_hazard_band {p : ℝ} (hp : 0 < p) (hsmall : p < ((2 : ℝ)^12)⁻¹) :
    ∃ l : ℕ, 12 ≤ l ∧ inHazardBand p l := by
  have hex : ∃ n : ℕ, ((1/2 : ℝ)^n) ≤ p := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hp (by norm_num : (1/2 : ℝ) < 1)
    exact ⟨n, hn.le⟩
  let n := Nat.find hex
  have hn : (1/2 : ℝ)^n ≤ p := Nat.find_spec hex
  have hn12 : 12 < n := by
    by_contra h
    have hle : n ≤ 12 := by omega
    have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) ≤ 1) hle
    have hsmall' : p < (1/2 : ℝ)^12 := by simpa [one_div, inv_pow] using hsmall
    linarith
  refine ⟨n-1, by omega, ?_⟩
  have hpred : p < (1/2 : ℝ)^(n-1) :=
    lt_of_not_ge (Nat.find_min hex (by dsimp only [n]; omega))
  unfold inHazardBand
  have hsucc : n-1+1 = n := by omega
  rw [hsucc]
  simpa only [one_div, inv_pow] using And.intro hn hpred

theorem finite_hazard_cover {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    ∃ length : ℕ, ∀ i, 0 < p i → p i < ((2 : ℝ)^12)⁻¹ →
      ∃ k ∈ range length, inHazardBand (p i) (12+k) := by
  classical
  let band : ι → ℕ := fun i => if h : 0 < p i ∧ p i < ((2 : ℝ)^12)⁻¹
    then (exists_hazard_band h.1 h.2).choose else 12
  let length := (univ : Finset ι).sup band + 1
  refine ⟨length, ?_⟩
  intro i hi hs
  have hband : 12 ≤ band i ∧ inHazardBand (p i) (band i) := by
    dsimp only [band]
    rw [dite_eq_left ⟨hi, hs⟩]
    exact (exists_hazard_band hi hs).choose_spec
  refine ⟨band i-12, mem_range.mpr ?_, ?_⟩
  · have hb := le_sup (f := band) (mem_univ i)
    dsimp only [length]
    omega
  · have heq : 12 + (band i-12) = band i := by omega
    rw [heq]
    exact hband.2

lemma hazard_band_disjoint {p : ℝ} {l k : ℕ}
    (hl : inHazardBand p l) (hk : inHazardBand p k) : l = k := by
  have impossible {a b : ℕ} (hab : a < b)
      (ha : inHazardBand p a) (hb : inHazardBand p b) : False := by
    have hpow : ((2 : ℝ)^b)⁻¹ ≤ ((2 : ℝ)^(a+1))⁻¹ := by
      rw [← inv_pow, ← inv_pow]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact (not_lt_of_ge (hpow.trans ha.1)) hb.2
  exact le_antisymm (le_of_not_gt (fun h => impossible h hk hl))
    (le_of_not_gt (fun h => impossible h hl hk))

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def bandHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (p₀ upper : ℝ) (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if p₀ ≤ reverseHazard M hE κ D G q d h k S ∧
      reverseHazard M hE κ D G q d h k S < upper ∧ d ∈ S h
    then reverseHazard M hE κ D G q d h k S else 0

noncomputable def lowHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (η : ℝ) (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if d ∈ S h ∧ reverseHazard M hE κ D G q d h k S < η
    then reverseHazard M hE κ D G q d h k S else 0

lemma bandHazardCost_mean_eq_exit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (p₀ upper : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandHazardCost M hE κ D G q d h p₀ upper) m k S =
      reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S := by
  apply reverseMeanCost_eq_of_step M hE κ D G n hG q hq0 hq1
  · intro l R hR
    by_cases hb : p₀ ≤ reverseHazard M hE κ D G q d h l R ∧
        reverseHazard M hE κ D G q d h l R < upper ∧ d ∈ R h
    · simp only [bandHazardCost, hb, bitsExpectation_const]
      rw [reverseHazard_eq_step M hE κ D G n hG q d h hh]
      apply bitsExpectation_congr
      intro C hC
      simp only [bandExitCost, hb.1, hb.2.1, hb.2.2, true_and]
    · have hz : ∀ C, bandExitCost M hE κ D G q d h p₀ upper l R
          ((reverseStepTree M hE κ l D R G n).run C) = 0 := by
        intro C
        unfold bandExitCost
        apply ite_eq_right
        intro hc
        exact hb ⟨hc.1, hc.2.1, hc.2.2.1⟩
      simp only [bandHazardCost, hb, ite_false, hz, bitsExpectation_const]
  · exact closed

lemma dyadic_band_hazard_bound (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (l : ℕ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q
      (bandHazardCost M hE κ D G q d h (((2:ℝ)^(l+1))⁻¹) (((2:ℝ)^l)⁻¹)) m k S ≤
        hazardBandBound l := by
  rw [bandHazardCost_mean_eq_exit M hE κ D G n hG q hq0 hq1 d h hh _ _ m k S closed]
  have hp : 0 < ((2:ℝ)^(l+1))⁻¹ := by positivity
  have hp1 : ((2:ℝ)^(l+1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hu : 0 ≤ ((2:ℝ)^l)⁻¹ := by positivity
  have hb := reverse_exit_band_bound M hE κ D G n hG q hq0 hq1 d h hh
    (((2:ℝ)^(l+1))⁻¹) (((2:ℝ)^l)⁻¹) hp hp1 hu m k S closed
  have heq : ((2:ℝ)^l)⁻¹ = 2 * ((2:ℝ)^(l+1))⁻¹ := by
    rw [pow_succ]
    field_simp
  rw [heq, hazardBandBound_eq_certificate_bound] at hb
  simpa only [← heq] using hb

theorem reverse_low_hazard_lt_half (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q
      (lowHazardCost M hE κ D G q d h (((2:ℝ)^12)⁻¹)) m k S < (1:ℝ)/2 := by
  let R := traceHazards M hE κ D G n q d h m k S
  obtain ⟨L, hL⟩ := finite_hazard_cover (fun p : {p : ℝ // p ∈ R} => p.val)
  let B : ℕ → ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ := fun i =>
    bandHazardCost M hE κ D G q d h (((2:ℝ)^(12+i+1))⁻¹) (((2:ℝ)^(12+i))⁻¹)
  have hb0 (i : ℕ) (t : ReverseTransition α) : 0 ≤ B i t.time t.before t.after := by
    dsimp only [B, bandHazardCost]
    split_ifs
    · exact reverseHazard_nonneg M hE κ D G q hq0 hq1 d h _ _
    · exact le_rfl
  have hpoint (C : Finset α) :
      reverseCost M hE κ D G n (lowHazardCost M hE κ D G q d h (((2:ℝ)^12)⁻¹)) m k S C ≤
        ∑ i ∈ range L, reverseCost M hE κ D G n (B i) m k S C := by
    rw [← reverseCost_sum]
    apply reverseCost_le_of_trace
    intro t ht
    dsimp only [lowHazardCost]
    by_cases hs : d ∈ t.before h ∧ reverseHazard M hE κ D G q d h t.time t.before < ((2:ℝ)^12)⁻¹
    · rw [ite_eq_left hs]
      have hp0 := reverseHazard_nonneg M hE κ D G q hq0 hq1 d h t.time t.before
      by_cases hz : reverseHazard M hE κ D G q d h t.time t.before = 0
      · rw [hz]
        exact sum_nonneg (fun i hi => hb0 i t)
      · have hp : 0 < reverseHazard M hE κ D G q d h t.time t.before := lt_of_le_of_ne hp0 (Ne.symm hz)
        have hmem : reverseHazard M hE κ D G q d h t.time t.before ∈ R :=
          mem_traceHazards M hE κ D G n q d h m k S C t ht
        obtain ⟨i, hi, hband⟩ := hL ⟨_, hmem⟩ hp hs.2
        have heq : B i t.time t.before t.after = reverseHazard M hE κ D G q d h t.time t.before := by
          simp only [B, bandHazardCost, hband.1, hband.2, hs.1, true_and, ite_true]
        rw [← heq]
        exact single_le_sum (fun j hj => hb0 j t) hi
    · rw [ite_eq_right hs]
      exact sum_nonneg (fun i hi => hb0 i t)
  have hmean : reverseMeanCost M hE κ D G n q
      (lowHazardCost M hE κ D G q d h (((2:ℝ)^12)⁻¹)) m k S ≤
        ∑ i ∈ range L, reverseMeanCost M hE κ D G n q (B i) m k S := by
    unfold reverseMeanCost
    rw [← bitsExpectation_sum]
    exact bitsExpectation_mono q hq0 hq1 univ (fun C _ => hpoint C)
  apply lt_of_le_of_lt hmean
  apply lt_of_le_of_lt _ (hazardBandBound_sum_lt_half L)
  apply sum_le_sum
  intro i hi
  exact dyadic_band_hazard_bound M hE κ D G n hG q hq0 hq1 d h hh (12+i) m k S closed

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def exitHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if d ∈ S h then reverseHazard M hE κ D G q d h k S else 0

noncomputable def squareHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if d ∈ S h then (reverseHazard M hE κ D G q d h k S)^2 else 0

lemma exitHazardCost_mean_eq_exit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (exitHazardCost M hE κ D G q d h) m k S =
      reverseMeanCost M hE κ D G n q (exitCost d h) m k S := by
  apply reverseMeanCost_eq_of_step M hE κ D G n hG q hq0 hq1
  · intro l R hR
    by_cases hd : d ∈ R h
    · simp only [exitHazardCost, hd, ite_true, bitsExpectation_const, exitCost, true_and]
      exact reverseHazard_eq_step M hE κ D G n hG q d h hh l R
    · simp only [exitHazardCost, hd, ite_false, bitsExpectation_const, exitCost, false_and]
  · exact closed

theorem reverse_squared_exit_mass (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) (hh : h ≤ n) :
    (((2:ℝ)^12)⁻¹) / 2 ≤
      reverseMeanCost M hE κ D G n q (squareHazardCost M hE κ D G q d h)
        (pathHorizon h+1) (-1) (fun _ => Set.univ) := by
  let η : ℝ := ((2:ℝ)^12)⁻¹
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hpoint (k : ℤ) (S S' : ℕ → Set α) :
      η * exitHazardCost M hE κ D G q d h k S S' ≤
        squareHazardCost M hE κ D G q d h k S S' + η * lowHazardCost M hE κ D G q d h η k S S' := by
    by_cases hs : d ∈ S h
    · by_cases hp : reverseHazard M hE κ D G q d h k S < η
      · simp only [exitHazardCost, squareHazardCost, lowHazardCost, hs, hp, true_and, ite_true]
        nlinarith [sq_nonneg (reverseHazard M hE κ D G q d h k S)]
      · have hp' : η ≤ reverseHazard M hE κ D G q d h k S := le_of_not_gt hp
        have hp0 := reverseHazard_nonneg M hE κ D G q hq0 hq1 d h k S
        simp only [exitHazardCost, squareHazardCost, lowHazardCost, hs, hp, true_and, ite_true, ite_false, mul_zero, add_zero]
        nlinarith
    · simp [exitHazardCost, squareHazardCost, lowHazardCost, hs]
  have hmean :
      η * reverseMeanCost M hE κ D G n q (exitHazardCost M hE κ D G q d h) (pathHorizon h+1) (-1) (fun _ => Set.univ) ≤
      reverseMeanCost M hE κ D G n q (squareHazardCost M hE κ D G q d h) (pathHorizon h+1) (-1) (fun _ => Set.univ) +
      η * reverseMeanCost M hE κ D G n q (lowHazardCost M hE κ D G q d h η) (pathHorizon h+1) (-1) (fun _ => Set.univ) := by
    rw [← reverseMeanCost_mul, ← reverseMeanCost_mul, ← reverseMeanCost_add]
    unfold reverseMeanCost
    apply bitsExpectation_mono q hq0 hq1
    intro C hC
    exact reverseCost_mono M hE κ D G n _ _ hpoint _ _ _ C
  rw [exitHazardCost_mean_eq_exit M hE κ D G n hG q hq0 hq1 d h hh _ _ _
    (reverseClosed_univ M hE κ D (-1)), reverse_exit_total_one M hE κ D G n hG q d hd h hh,
    mul_one] at hmean
  have hlow := reverse_low_hazard_lt_half M hE κ D G n hG q hq0 hq1 d h hh
    (pathHorizon h+1) (-1) (fun _ => Set.univ) (reverseClosed_univ M hE κ D (-1))
  change η / 2 ≤ reverseMeanCost M hE κ D G n q _ _ _ _
  change reverseMeanCost M hE κ D G n q (lowHazardCost M hE κ D G q d h η) _ _ _ < _ at hlow
  have hmul := mul_le_mul_of_nonneg_left hlow.le hη
  have hsub := (sub_le_iff_le_add).mpr (hmean.trans (add_le_add le_rfl hmul))
  calc
    η / 2 = η - η * (1 / 2) := by ring
    _ ≤ _ := hsub

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reverseDoubleExit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (h : ℕ) (d : α)
    (C T : Finset α) : ℝ :=
  if d ∈ S h then
    (if d ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k h then 1 else 0) *
    (if d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k h then 1 else 0)
  else 0

lemma reverseDoubleExit_mask_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (h : ℕ) (d : α)
    (C C' T : Finset α)
    (hC : ∀ j < h, ∀ e ∈ G j, e ∈ S j → (e ∈ C ↔ e ∈ C')) :
    reverseDoubleExit M hE κ D S G k h d C T = reverseDoubleExit M hE κ D S G k h d C' T := by
  unfold reverseDoubleExit
  rw [reverseNominal_mask_congr M hE κ D S G k h C C' hC,
    reverseHybrid_mask_congr M hE κ D S G k h C C' T hC]

lemma reverseDoubleExit_expectation (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (h : ℕ) (d : α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ) :
    bitsExpectation q univ (fun C => bitsExpectation q univ (reverseDoubleExit M hE κ D S G k h d C)) =
      if d ∈ S h then (reverseHazard M hE κ D G q d h k S)^2 else 0 := by
  change bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
    reverseDoubleExit M hE κ D S G k h d C T)) = _
  by_cases hd : d ∈ S h
  · simp only [reverseDoubleExit, hd, ite_true]
    rw [reverse_double_exit M hE κ k D S G h hG univ (fun _ _ => subset_univ _) q d,
      reverseHazard_eq]
  · simp only [reverseDoubleExit, hd, ite_false, bitsExpectation_const]

theorem reverseDoubleExit_after_prefix (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (l : ℤ) :
    bitsExpectation q univ (fun C => bitsExpectation q univ
      (reverseDoubleExit M hE κ D ((reversePrefixTree M hE κ D G h m k S).run C) G l h d C)) =
      bitsExpectation q univ (fun C => if d ∈ (reversePrefixTree M hE κ D G h m k S).run C h then
        (reverseHazard M hE κ D G q d h l ((reversePrefixTree M hE κ D G h m k S).run C))^2 else 0) := by
  let f := fun R C => bitsExpectation q univ (reverseDoubleExit M hE κ D R G l h d C)
  have ht := reversePrefixTree_tower M hE κ D G h hG m k S closed q f (by
    intro R C C' hC
    apply bitsExpectation_congr
    intro T hT
    exact reverseDoubleExit_mask_congr M hE κ D R G l h d C C' T hC)
  apply ht.trans
  apply bitsExpectation_congr
  intro C hC
  exact reverseDoubleExit_expectation M hE κ D _ G l h d hG q

lemma reversePrefixTree_from_univ_path (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (m : ℕ) (C : Finset α)
    {j : ℕ} (hj : j ≤ n) :
    (reversePrefixTree M hE κ D G n m (-1) (fun _ => Set.univ)).run C j =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ)) := by
  rw [reversePrefixTree_run M hE κ D G n hG m (-1) _ (reverseClosed_univ M hE κ D (-1)) C]
  have hS : ∀ i ≤ n, (fun _ => Set.univ) i =
      nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) i (-1+1) := by
    intro i hi
    exact (nominalPath_nonnegative M hE κ D _ i (by omega)).symm
  simpa only [neg_add_cancel, zero_sub] using reverseFinal_path M hE κ D G n hG m (-1) _ C hS hj

omit [DecidableEq α] in
lemma reverseNominal_actual_state (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C : Finset α) (b : ℤ) (h : ℕ)
    (hS : ∀ j ≤ h, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b) :
    reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S (b-1) h =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (b-1) := by
  calc
    _ = reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
        (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (b-1+1)) (b-1) h := by
      apply reverseNominal_congr_before
      · intro j hj; rfl
      · intro j hj; simpa only [sub_add_cancel] using hS j (by omega)
    _ = _ := reverseNominal_agrees M hE κ D _ (b-1) h

omit [DecidableEq α] in
lemma hybrid_actual_containment (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C T : Finset α) (b : ℤ) (h : ℕ)
    (hS : ∀ j ≤ h, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b)
    (hb : activation h ≤ b-1) :
    densityExpansion M hE κ (D h)
      (guardedPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (b-2) ∪
        lowerCompetition M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
          (fun i => (T : Set α) ∩ (G i : Set α)) b h) ⊆
      reverseNominal M hE κ D (transitionHybrid M hE κ (b-1) D S G C T) S (b-1) h := by
  have heq : reverseNominal M hE κ D (transitionHybrid M hE κ (b-1) D S G C T) S (b-1) h =
      reverseNominal M hE κ D
        (hybridGuards M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) (fun i => (T : Set α) ∩ (G i : Set α)) b)
        (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b) (b-1) h := by
    apply reverseNominal_congr_before
    · intro j hj
      unfold transitionHybrid hybridGuards
      rw [reverseNominal_actual_state M hE κ D S G C b j (fun i hi => hS i (by omega)), hS j (by omega)]
    · intro j hj; exact hS j (by omega)
  rw [heq]
  exact hybrid_containment M hE κ D _ _ b h hb

noncomputable def safeBirthEvent (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (b : ℤ)
    (C T : Finset α) : Prop :=
  nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = b ∧
    d ∉ densityExpansion M hE κ (D h)
      (guardedPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (b-2) ∪
        lowerCompetition M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
          (fun i => (T : Set α) ∩ (G i : Set α)) b h)

omit [DecidableEq α] in
lemma doubleExit_le_safeBirth (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C T : Finset α) (b : ℤ) (h : ℕ)
    (d : α) (hd : d ∉ M.closure ∅)
    (hS : ∀ j ≤ h, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b)
    (hb : activation h ≤ b-1) :
    reverseDoubleExit M hE κ D S G (b-1) h d C T ≤ if safeBirthEvent M hE κ D G h d b C T then 1 else 0 := by
  unfold reverseDoubleExit
  by_cases hs : d ∈ S h
  · rw [ite_eq_left hs]
    by_cases hn : d ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S (b-1) h
    · rw [ite_eq_left hn, one_mul]
      by_cases hh : d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ (b-1) D S G C T) S (b-1) h
      · rw [ite_eq_left hh]
        have hbirth : nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = b := by
          rw [hS h le_rfl, mem_nominal_iff_birth_le M hE κ D _ h d hd b] at hs
          rw [reverseNominal_actual_state M hE κ D S G C b h hS,
            mem_nominal_iff_birth_le M hE κ D _ h d hd (b-1)] at hn
          omega
        have hsafe : safeBirthEvent M hE κ D G h d b C T :=
          ⟨hbirth, fun he => hh (hybrid_actual_containment M hE κ D S G C T b h hS hb he)⟩
        simp only [ite_eq_left hsafe, le_refl]
      · simp only [ite_eq_right hh]
        split_ifs <;> norm_num
    · simp only [ite_eq_right hn, zero_mul]
      split_ifs <;> norm_num
  · simp only [ite_eq_right hs]
    split_ifs <;> norm_num

lemma reverseHazard_state_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S S' : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (k : ℤ) (h : ℕ) (d : α)
    (hS : ∀ j < h, S j = S' j) :
    reverseHazard M hE κ D G q d h k S = reverseHazard M hE κ D G q d h k S' := by
  rw [reverseHazard_eq, reverseHazard_eq]
  apply bitsExpectation_congr
  intro C hC
  rw [reverseNominal_congr_before M hE κ D _ _ S S' k h (fun _ _ => rfl) hS]

theorem safeBirth_probability (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) (m : ℕ) (hb : activation h + 2 ≤ -(m:ℤ)) :
    bitsExpectation q univ (fun C =>
      if d ∈ nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (-(m:ℤ)) then
        (reverseHazard M hE κ D G q d h (-(m:ℤ)-1)
          (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ))))^2 else 0) ≤
    bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      if safeBirthEvent M hE κ D G h d (-(m:ℤ)) C T then 1 else 0)) := by
  let P := reversePrefixTree M hE κ D G h m (-1) (fun _ => Set.univ)
  have hP (C : Finset α) (j : ℕ) (hj : j ≤ h) : P.run C j =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ)) :=
    reversePrefixTree_from_univ_path M hE κ D G h hG m C hj
  have hid := reverseDoubleExit_after_prefix M hE κ D G h d hG q m (-1) (fun _ => Set.univ)
    (reverseClosed_univ M hE κ D (-1)) (-(m:ℤ)-1)
  have heq : bitsExpectation q univ (fun C =>
      if d ∈ nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (-(m:ℤ)) then
        (reverseHazard M hE κ D G q d h (-(m:ℤ)-1)
          (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ))))^2 else 0) =
      bitsExpectation q univ (fun C => if d ∈ P.run C h then
        (reverseHazard M hE κ D G q d h (-(m:ℤ)-1) (P.run C))^2 else 0) := by
    apply bitsExpectation_congr
    intro C hC
    rw [hP C h le_rfl, reverseHazard_state_congr M hE κ D (P.run C) _ G q _ h d
      (fun j hj => hP C j hj.le)]
  rw [heq, ← hid]
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  apply bitsExpectation_mono q hq0 hq1
  intro T hT
  exact doubleExit_le_safeBirth M hE κ D (P.run C) G C T (-(m:ℤ)) h d hd (hP C) (by omega)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma reverseCost_add_steps (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m r : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n cost (m+r) k S C =
      reverseCost M hE κ D G n cost m k S C +
        reverseCost M hE κ D G n cost r (k-m) (reverseFinal M hE κ D G n m k S C) C := by
  induction m generalizing k S with
  | zero => simp only [reverseCost, reverseFinal, Nat.cast_zero, sub_zero, zero_add]
  | succ m ih =>
    rw [Nat.succ_add, reverseCost, reverseCost, reverseFinal, ih]
    have ht : k - 1 - (m:ℤ) = k - ((m+1:ℕ):ℤ) := by omega
    rw [ht]
    ring

lemma reverseCost_eq_sum (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n cost m k S C =
      ∑ i ∈ range m, cost (k-i) (reverseFinal M hE κ D G n i k S C)
        ((reverseStepTree M hE κ (k-i) D (reverseFinal M hE κ D G n i k S C) G n).run C) := by
  induction m with
  | zero => simp only [reverseCost, range_zero, sum_empty]
  | succ m ih =>
    rw [reverseCost_add_steps M hE κ D G n cost m 1, ih, sum_range_succ]
    simp only [reverseCost, add_zero]

noncomputable def pathExitSquare (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ) (m : ℕ)
    (C : Finset α) : ℝ :=
  if d ∈ nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (-(m:ℤ)) then
    (reverseHazard M hE κ D G q d h (-(m:ℤ)-1)
      (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ))))^2 else 0

lemma reverse_square_eq_path_sum (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (d : α) (h : ℕ) (hh : h ≤ n) (m : ℕ) :
    reverseMeanCost M hE κ D G n q (squareHazardCost M hE κ D G q d h) m (-1) (fun _ => Set.univ) =
      ∑ i ∈ range m, bitsExpectation q univ (pathExitSquare M hE κ D G q d h i) := by
  unfold reverseMeanCost
  rw [← bitsExpectation_sum]
  apply bitsExpectation_congr
  intro C hC
  rw [reverseCost_eq_sum]
  apply sum_congr rfl
  intro i hi
  have hS : ∀ j ≤ n, (fun _ => Set.univ) j =
      nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) j (-1+1) := by
    intro j hj
    exact (nominalPath_nonnegative M hE κ D _ j (by omega)).symm
  have hf (j : ℕ) (hj : j ≤ n) : reverseFinal M hE κ D G n i (-1) (fun _ => Set.univ) C j =
      nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) j (-(i:ℤ)) := by
    simpa only [neg_add_cancel, zero_sub] using reverseFinal_path M hE κ D G n hG i (-1) _ C hS hj
  have ht : (-1:ℤ) - i = -(i:ℤ)-1 := by omega
  simp only [squareHazardCost, pathExitSquare, ht, hf h hh]
  rw [reverseHazard_state_congr M hE κ D _ _ G q _ h d (fun j hj => hf j (by omega))]

theorem path_squared_exit_mass (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) :
    (((2:ℝ)^12)⁻¹) / 2 ≤
      ∑ i ∈ range (pathHorizon h+1), bitsExpectation q univ (pathExitSquare M hE κ D G q d h i) := by
  rw [← reverse_square_eq_path_sum M hE κ D G h hG q d h le_rfl]
  exact reverse_squared_exit_mass M hE κ D G h hG q hq0 hq1 d hd h le_rfl

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma pathExitSquare_nonneg (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h m : ℕ) (C : Finset α) :
    0 ≤ pathExitSquare M hE κ D G q d h m C := by
  unfold pathExitSquare
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

lemma pathExitSquare_eq_doubleExit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (h : ℕ) (d : α) (m : ℕ) :
    bitsExpectation q univ (pathExitSquare M hE κ D G q d h m) =
      bitsExpectation q univ (fun C => bitsExpectation q univ
        (reverseDoubleExit M hE κ D ((reversePrefixTree M hE κ D G h m (-1) (fun _ => Set.univ)).run C)
          G (-(m:ℤ)-1) h d C)) := by
  rw [reverseDoubleExit_after_prefix M hE κ D G h d hG q m (-1) _ (reverseClosed_univ M hE κ D (-1))]
  apply bitsExpectation_congr
  intro C hC
  have hp (j : ℕ) (hj : j ≤ h) := reversePrefixTree_from_univ_path M hE κ D G h hG m C hj
  rw [hp h le_rfl, reverseHazard_state_congr M hE κ D _ _ G q _ h d (fun j hj => hp j hj.le)]
  rfl

omit [DecidableEq α] in
lemma doubleExit_le_birth (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C T : Finset α) (b : ℤ) (h : ℕ)
    (d : α) (hd : d ∉ M.closure ∅)
    (hS : ∀ j ≤ h, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b) :
    reverseDoubleExit M hE κ D S G (b-1) h d C T ≤
      if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = b then 1 else 0 := by
  unfold reverseDoubleExit
  by_cases hs : d ∈ S h
  · rw [ite_eq_left hs]
    by_cases hn : d ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S (b-1) h
    · rw [ite_eq_left hn, one_mul]
      have hbirth : nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = b := by
        rw [hS h le_rfl, mem_nominal_iff_birth_le M hE κ D _ h d hd b] at hs
        rw [reverseNominal_actual_state M hE κ D S G C b h hS,
          mem_nominal_iff_birth_le M hE κ D _ h d hd (b-1)] at hn
        omega
      rw [ite_eq_left hbirth]
      split_ifs <;> norm_num
    · simp only [ite_eq_right hn, zero_mul]
      split_ifs <;> norm_num
  · simp only [ite_eq_right hs]
    split_ifs <;> norm_num

theorem pathExitSquare_le_birth_probability (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) (m : ℕ) :
    bitsExpectation q univ (pathExitSquare M hE κ D G q d h m) ≤
      bitsExpectation q univ (fun C =>
        if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = -(m:ℤ) then 1 else 0) := by
  rw [pathExitSquare_eq_doubleExit M hE κ D G hG q h d m]
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  rw [← bitsExpectation_const q univ (if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = -(m:ℤ) then 1 else 0)]
  apply bitsExpectation_mono q hq0 hq1
  intro T hT
  exact doubleExit_le_birth M hE κ D _ G C T (-(m:ℤ)) h d hd
    (fun j hj => reversePrefixTree_from_univ_path M hE κ D G h hG m C hj)

omit [DecidableEq α] in
lemma nominalBirth_baseline_iff (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) :
    nominalBirth M hE κ D C h d = activation h ↔ d ∈ densityExpansion M hE κ (D h) (M.closure ∅) := by
  have hm := mem_nominal_iff_birth_le M hE κ D C h d hd (activation h)
  rw [nominalPath_baseline] at hm
  have hb := (nominalBirth_bounds M hE κ D C h d).1
  exact ⟨fun he => hm.mpr he.le, fun he => le_antisymm (hm.mp he) hb⟩

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

omit [Fintype α] in
lemma natRank_eq_ncard_of_indep (M : Matroid α) {I : Set α} (hI : M.Indep I) :
    natRank M I = I.ncard := by
  simp only [natRank, hI.eRk_eq_encard, Set.ncard_def]

lemma baseline_density_rank (M : Matroid α) (hE : M.E = Set.univ) (κ : ℕ) (D : Set α) :
    κ * natRank M (densityExpansion M hE κ D (M.closure ∅)) ≤ D.ncard := by
  let Q := densityExpansion M hE κ D (M.closure ∅)
  have hmax := (densityExpansion_spec M hE κ D (M.closure ∅)).1.2.2
    (M.closure ∅) (Matroid.isFlat_closure (M := M) ∅) Set.Subset.rfl
  have hcount := Set.ncard_mono (show D ∩ Q ⊆ D from inter_subset_left)
  have hnn : (0 : ℤ) ≤ (D ∩ M.closure ∅).ncard := by exact_mod_cast Nat.zero_le _
  have hcount' : ((D ∩ Q).ncard : ℤ) ≤ D.ncard := by exact_mod_cast hcount
  have hmax' : (κ : ℤ) * natRank M Q ≤ D.ncard := by
    dsimp only [densityObjective] at hmax
    rw [natRank_closure, natRank_empty] at hmax
    change _ ≤ (D ∩ Q).ncard - (κ : ℤ) * natRank M Q at hmax
    omega
  exact_mod_cast hmax'

lemma baseline_independent_count (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D I : Set α) (hI : M.Indep I) :
    κ * (I ∩ densityExpansion M hE κ D (M.closure ∅)).ncard ≤ D.ncard := by
  have hi := natRank_eq_ncard_of_indep M
    (hI.subset (show I ∩ densityExpansion M hE κ D (M.closure ∅) ⊆ I from inter_subset_left))
  have hr := natRank_mono M (show I ∩ densityExpansion M hE κ D (M.closure ∅) ⊆
      densityExpansion M hE κ D (M.closure ∅) from inter_subset_right)
  rw [hi] at hr
  exact (Nat.mul_le_mul_left κ hr).trans (baseline_density_rank M hE κ D)

lemma baseline_birth_iff (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) :
    nominalBirth M hE κ D C h d = activation h ↔
      d ∈ densityExpansion M hE κ (D h) (M.closure ∅) := by
  rw [← nominalPath_baseline M hE κ D C h,
    mem_nominal_iff_birth_le M hE κ D C h d hd]
  exact ⟨fun he => he.le, fun he => le_antisymm he (nominalBirth_bounds M hE κ D C h d).1⟩

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def safeEndpointCount (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (C T : Finset α) : ℝ :=
  ∑ i ∈ range (pathHorizon h-1), if safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T then 1 else 0

lemma pathHorizon_pos (h : ℕ) : 0 < pathHorizon h := by unfold pathHorizon; omega

theorem safeEndpointCount_lower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) :
    (((2:ℝ)^12)⁻¹) / 2 ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (safeEndpointCount M hE κ D G h d C)) +
        if d ∈ densityExpansion M hE κ (D h) (M.closure ∅) then 1 else 0 := by
  let H := pathHorizon h
  let f := fun i => bitsExpectation q univ (pathExitSquare M hE κ D G q d h i)
  let g : ℕ → ℝ := fun i => bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
    if safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T then 1 else 0))
  have hH : 1 ≤ H := pathHorizon_pos h
  have htime : activation h = -(H:ℤ) := by have ht := activation_add_horizon h; omega
  have hvalid : ∀ i ∈ range (H-1), f i ≤ g i := by
    intro i hi
    exact safeBirth_probability M hE κ D G hG q hq0 hq1 h d hd i (by
      have hi' := mem_range.mp hi
      rw [htime]
      omega)
  have hgap : f (H-1) ≤ 0 := by
    have hb := pathExitSquare_le_birth_probability M hE κ D G hG q hq0 hq1 h d hd (H-1)
    have ht : -((H-1:ℕ):ℤ) = activation h + 1 := by omega
    have hz : bitsExpectation q univ (fun C =>
        if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = -((H-1:ℕ):ℤ)
          then 1 else 0) = 0 := by
      rw [ht]
      simp only [nominalBirth_not_activation_succ, ite_false, bitsExpectation_const]
    exact hb.trans_eq hz
  have hbase : f H ≤ if d ∈ densityExpansion M hE κ (D h) (M.closure ∅) then 1 else 0 := by
    have hb := pathExitSquare_le_birth_probability M hE κ D G hG q hq0 hq1 h d hd H
    have heq : bitsExpectation q univ (fun C =>
        if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = -(H:ℤ)
          then 1 else 0) = if d ∈ densityExpansion M hE κ (D h) (M.closure ∅) then 1 else 0 := by
      rw [← htime]
      simp only [nominalBirth_baseline_iff M hE κ D _ h d hd, bitsExpectation_const]
    exact hb.trans_eq heq
  have hsplit : (∑ i ∈ range (H+1), f i) = (∑ i ∈ range (H-1), f i) + f (H-1) + f H := by
    have hn : H+1 = (H-1+1)+1 := by omega
    rw [hn, sum_range_succ, sum_range_succ, Nat.sub_add_cancel hH]
  have hsum := path_squared_exit_mass M hE κ D G hG q hq0 hq1 d hd h
  change (((2:ℝ)^12)⁻¹)/2 ≤ ∑ i ∈ range (H+1), f i at hsum
  rw [hsplit] at hsum
  have hfg := sum_le_sum (fun i hi => hvalid i hi)
  have heq : bitsExpectation q univ (fun C => bitsExpectation q univ (safeEndpointCount M hE κ D G h d C)) =
      ∑ i ∈ range (H-1), g i := by
    change bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      ∑ i ∈ range (H-1), if safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T then 1 else 0)) = _
    simp_rw [bitsExpectation_sum]
    rfl
  rw [heq]
  linarith

noncomputable def safeCountBeforeParity (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) : ℝ :=
  ∑ d ∈ I, safeEndpointCount M hE κ D G h d C T

omit [Fintype α] [DecidableEq α] in
lemma indep_not_loop (M : Matroid α) (I : Finset α) (hI : M.Indep (I : Set α))
    {d : α} (hd : d ∈ I) : d ∉ M.closure ∅ := by
  intro he
  exact hI.notMem_closure_sdiff_of_mem hd (M.closure_subset_closure (Set.empty_subset _) he)

theorem safeCountBeforeParity_lower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (I : Finset α) (hI : M.Indep (I : Set α)) :
    (((2:ℝ)^12)⁻¹) / 2 * I.card - (D h).ncard / (κ:ℝ) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (safeCountBeforeParity M hE κ D G h I C)) := by
  let Q := densityExpansion M hE κ (D h) (M.closure ∅)
  have hsum := sum_le_sum (fun d hd => safeEndpointCount_lower M hE κ D G hG q hq0 hq1 h d (indep_not_loop M I hI hd))
  have hpre : bitsExpectation q univ (fun C => bitsExpectation q univ (safeCountBeforeParity M hE κ D G h I C)) =
      ∑ d ∈ I, bitsExpectation q univ (fun C => bitsExpectation q univ (safeEndpointCount M hE κ D G h d C)) := by
    change bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      ∑ d ∈ I, safeEndpointCount M hE κ D G h d C T)) = _
    simp_rw [bitsExpectation_sum]
  have hcount : (∑ d ∈ I, if d ∈ Q then (1:ℝ) else 0) = ((I.filter (fun d => d ∈ Q)).card : ℝ) := by
    simp
  have hset : ((I.filter (fun d => d ∈ Q) : Finset α) : Set α) = (I : Set α) ∩ Q := by
    ext d
    simp
  have hb := baseline_independent_count M hE κ (D h) (I : Set α) hI
  change κ * ((I : Set α) ∩ Q).ncard ≤ (D h).ncard at hb
  rw [← hset, Set.ncard_coe_finset] at hb
  have hb' : (κ:ℝ) * ((I.filter (fun d => d ∈ Q)).card : ℝ) ≤ ((D h).ncard:ℝ) := by exact_mod_cast hb
  have hκ' : (0:ℝ) < κ := by exact_mod_cast hκ
  have hb'' : ((I.filter (fun d => d ∈ Q)).card : ℝ) ≤ (D h).ncard / (κ:ℝ) := (le_div_iff₀ hκ').mpr (by simpa [mul_comm] using hb')
  rw [sum_add_distrib] at hsum
  change (∑ _ ∈ I, (((2:ℝ)^12)⁻¹)/2) ≤
    (∑ d ∈ I, bitsExpectation q univ (fun C => bitsExpectation q univ (safeEndpointCount M hE κ D G h d C))) +
      ∑ d ∈ I, if d ∈ Q then (1:ℝ) else 0 at hsum
  rw [hcount, ← hpre] at hsum
  simp only [sum_const, nsmul_eq_mul] at hsum
  linarith

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def safeEndpointParityCount (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (C T : Finset α) (parity : Bool) : ℝ :=
  ∑ i ∈ range (pathHorizon h-1), if safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T ∧
    (-(i:ℤ)) % 2 = (if parity then 1 else 0) then 1 else 0

noncomputable def safeSampleCount (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) (parity : Bool) : ℝ :=
  ∑ d ∈ I, safeEndpointParityCount M hE κ D G h d C T parity

omit [DecidableEq α] in
lemma safeSampleCount_parity_split (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) :
    safeSampleCount M hE κ D G h I C T false + safeSampleCount M hE κ D G h I C T true =
      safeCountBeforeParity M hE κ D G h I C T := by
  unfold safeSampleCount safeCountBeforeParity
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  unfold safeEndpointParityCount safeEndpointCount
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  have hm0 := Int.emod_nonneg (-(i:ℤ)) (by norm_num : (2:ℤ) ≠ 0)
  have hm1 := Int.emod_lt_of_pos (-(i:ℤ)) (by norm_num : (0:ℤ) < 2)
  have hm : (-(i:ℤ)) % 2 = 0 ∨ (-(i:ℤ)) % 2 = 1 := by omega
  by_cases hs : safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T
  · rcases hm with hm | hm <;> simp [hs, hm]
  · simp [hs]

noncomputable def fairParityExpectation (f : Bool → ℝ) : ℝ := (f false + f true) / 2

omit [DecidableEq α] in
lemma safeSampleCount_fair_parity (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) :
    fairParityExpectation (safeSampleCount M hE κ D G h I C T) =
      safeCountBeforeParity M hE κ D G h I C T / 2 := by
  unfold fairParityExpectation
  rw [safeSampleCount_parity_split]

theorem safeSampleCount_lower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (I : Finset α) (hI : M.Indep (I : Set α)) :
    (((2:ℝ)^12)⁻¹) / 4 * I.card - (D h).ncard / (κ:ℝ) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (safeSampleCount M hE κ D G h I C T))) := by
  have hpre := safeCountBeforeParity_lower M hE κ hκ D G hG q hq0 hq1 h I hI
  have heq : bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (safeSampleCount M hE κ D G h I C T))) =
      (bitsExpectation q univ (fun C => bitsExpectation q univ (safeCountBeforeParity M hE κ D G h I C))) / 2 := by
    simp only [safeSampleCount_fair_parity, div_eq_mul_inv]
    rw [show bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      safeCountBeforeParity M hE κ D G h I C T * (2:ℝ)⁻¹)) =
        bitsExpectation q univ (fun C => bitsExpectation q univ (safeCountBeforeParity M hE κ D G h I C) * (2:ℝ)⁻¹) from by
          apply bitsExpectation_congr; intro C hC; exact bitsExpectation_mul_right q univ _ _]
    exact bitsExpectation_mul_right q univ _ _
  rw [heq]
  have hnonneg : 0 ≤ (D h).ncard / (κ:ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  linarith

omit [Fintype α] [DecidableEq α] in
lemma sum_unique_indicators {ι : Type*} (J : Finset ι) (p : ι → Prop) [DecidablePred p]
    (huniq : ∀ i ∈ J, ∀ j ∈ J, p i → p j → i = j) :
    (∑ i ∈ J, if p i then (1:ℝ) else 0) = if ∃ i ∈ J, p i then 1 else 0 := by
  classical
  by_cases hex : ∃ i ∈ J, p i
  · obtain ⟨i, hi, hp⟩ := hex
    rw [ite_eq_left ⟨i, hi, hp⟩]
    calc
      _ = if p i then (1:ℝ) else 0 := by
        apply sum_eq_single i
        · intro j hj hji
          exact ite_eq_right (fun hjp => hji (huniq j hj i hi hjp hp))
        · intro hnot
          exact (hnot hi).elim
      _ = 1 := ite_eq_left hp
  · rw [ite_eq_right hex]
    apply sum_eq_zero
    intro i hi
    exact ite_eq_right (fun hp => hex ⟨i, hi, hp⟩)

noncomputable def IsSafeSample (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (C T : Finset α) (parity : Bool) : Prop :=
  let b := nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d
  activation h + 2 ≤ b ∧ b ≤ 0 ∧ b % 2 = (if parity then 1 else 0) ∧
    d ∉ densityExpansion M hE κ (D h)
      (guardedPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (b-2) ∪
        lowerCompetition M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
          (fun i => (T : Set α) ∩ (G i : Set α)) b h)

omit [DecidableEq α] in
lemma isSafeSample_iff_endpoint (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (C T : Finset α) (parity : Bool) :
    IsSafeSample M hE κ D G h d C T parity ↔ ∃ i ∈ range (pathHorizon h-1),
      safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T ∧ (-(i:ℤ)) % 2 = (if parity then 1 else 0) := by
  let b := nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d
  have ht := activation_add_horizon h
  have hH := pathHorizon_pos h
  constructor
  · rintro ⟨hlo, hhi, hp, hs⟩
    have hi0 : 0 ≤ -b := by omega
    have hieq : -(((-b).toNat:ℕ):ℤ) = b := by rw [Int.toNat_of_nonneg hi0]; omega
    refine ⟨(-b).toNat, mem_range.mpr ?_, ?_, ?_⟩
    · have hiNat := Int.toNat_of_nonneg hi0
      change activation h + 2 ≤ b at hlo
      omega
    · rw [hieq]
      exact ⟨rfl, hs⟩
    · simpa only [hieq] using hp
  · rintro ⟨i, hi, hs, hp⟩
    have hbirth := hs.1
    have hbound := mem_range.mp hi
    change _ ∧ _ ∧ _ ∧ _
    rw [hbirth]
    exact ⟨by omega, by omega, hp, hs.2⟩

noncomputable def safeSampleSet (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) (parity : Bool) : Finset α :=
  I.filter (fun d => IsSafeSample M hE κ D G h d C T parity)

omit [DecidableEq α] in

lemma safeSampleCount_eq_card (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) (parity : Bool) :
    safeSampleCount M hE κ D G h I C T parity = (safeSampleSet M hE κ D G h I C T parity).card := by
  unfold safeSampleCount safeSampleSet
  have hpoint (d : α) : safeEndpointParityCount M hE κ D G h d C T parity =
      if IsSafeSample M hE κ D G h d C T parity then 1 else 0 := by
    unfold safeEndpointParityCount
    rw [sum_unique_indicators]
    · simp only [← isSafeSample_iff_endpoint]
    · intro i hi j hj hsi hsj
      have hbi := hsi.1.1
      have hbj := hsj.1.1
      omega
  simp_rw [hpoint]
  simp

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α B : Type*} [Fintype α] [Fintype B]

lemma exists_rankWitness (M : Matroid α) (hE : M.E = Set.univ) (A S : Set α) :
    ∃ Z : Set α, Z ⊆ S ∧ Z.ncard = conditionalRank M S A ∧ S ⊆ M.closure (A ∪ Z) := by
  obtain ⟨Z, hZ, hgen, hcard⟩ := exists_extension_generators M hE (M.closure A) S
    (M.closure (M.closure A ∪ S)) (Matroid.isFlat_closure (M := M) _) rfl
  refine ⟨Z, hZ.trans sdiff_subset, ?_, ?_⟩
  · simp only [natRank_closure] at hcard
    have hrank : natRank M (M.closure A ∪ S) = natRank M (A ∪ S) := by
      simp only [natRank, M.eRk_union_closure_left_eq]
    rw [hrank] at hcard
    have hr := conditionalRank_add_base M S A
    rw [union_comm S A] at hr
    omega
  · rw [M.closure_union_closure_left_eq, M.closure_union_closure_left_eq] at hgen
    rw [hgen]
    exact subset_union_right.trans (M.subset_closure _ (by simp [hE]))

lemma collect_disjoint_witnesses (W : B → Set α) (U : Finset α)
    (hW : ∀ b, W b ⊆ (U : Set α))
    (hdisj : Pairwise (fun b c => Disjoint (W b) (W c))) :
    ∃ Z : Finset α, Z ⊆ U ∧ Z.card ≤ ∑ b, (W b).ncard ∧
      ∃ β : Z → B, ∀ b, (fun w : Z => w.val) '' {w | β w = b} = W b := by
  classical
  let Z := (⋃ b, W b).toFinset
  have hmem (w : Z) : ∃ b, w.val ∈ W b := by
    exact mem_iUnion.mp (Set.mem_toFinset.mp w.property)
  let β : Z → B := fun w => (hmem w).choose
  have hβ (w : Z) : w.val ∈ W (β w) := (hmem w).choose_spec
  refine ⟨Z, ?_, ?_, β, ?_⟩
  · intro e he
    obtain ⟨b, hb⟩ := mem_iUnion.mp (Set.mem_toFinset.mp he)
    exact hW b hb
  · rw [show Z.card = (⋃ b, W b).ncard from (Set.ncard_eq_toFinset_card' _).symm]
    exact Set.ncard_iUnion_le_of_fintype W
  · intro b
    ext e
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [← hw]
      exact hβ w
    · intro he
      let w : Z := ⟨e, Set.mem_toFinset.mpr (mem_iUnion.mpr ⟨b, he⟩)⟩
      have heq : β w = b := by
        by_contra hne
        exact Set.disjoint_left.mp (hdisj hne) (hβ w) he
      exact ⟨w, heq, rfl⟩

lemma residualUnion_subset_mask
    {α : Type u_1} {B : Type u_2} [Fintype α] [Fintype B]
    (M : Matroid α) (P A W : B → Set α) (O : Set α)
    (hspan : ∀ b, P b \ O ⊆ M.closure (A b ∪ W b)) :
    (⋃ b, P b \ M.closure (A b ∪ W b)) ⊆ O := by
  intro e he
  obtain ⟨b, hb⟩ := mem_iUnion.mp he
  by_contra hn
  exact hb.2 (hspan b ⟨hb.1, hn⟩)

lemma residualUnion_ncard (M : Matroid α) (P A W : B → Set α)
    (hdisj : Pairwise (fun b c => Disjoint (P b) (P c))) :
    (⋃ b, P b \ M.closure (A b ∪ W b)).ncard =
      ∑ b, (P b \ M.closure (A b ∪ W b)).ncard := by
  have hd : Pairwise (fun b c => Disjoint (P b \ M.closure (A b ∪ W b))
      (P c \ M.closure (A c ∪ W c))) := by
    intro b c hbc
    exact (hdisj hbc).mono sdiff_subset sdiff_subset
  simpa only [finsum_eq_sum_of_fintype] using Set.ncard_iUnion_of_finite (fun b => Set.toFinite _) hd

lemma nominal_rank_witnesses (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U : Finset α) (O : Set α) (ε : Fin 2) :
    ∃ W : ParityWindow (activation h) ε → Set α,
      (∀ b, W b ⊆ nominalLayerSet M hE κ D C h (U : Set α) ε b \ O) ∧
      (∑ b, (W b).ncard) = nominalRankStatistic M hE κ D C T h (U : Set α) O ε ∧
      (∀ b, nominalLayerSet M hE κ D C h (U : Set α) ε b \ O ⊆
        M.closure ((nominalPath M hE κ D C h (b.val.val - 2) ∪
          lowerCompetition M hE κ D C T b.val.val h) ∪ W b)) ∧
      ∃ Z : Finset α, Z ⊆ U ∧ Z.card ≤ nominalRankStatistic M hE κ D C T h (U : Set α) O ε ∧
        ∃ β : Z → ParityWindow (activation h) ε,
          ∀ b, (fun w : Z => w.val) '' {w | β w = b} = W b := by
  classical
  choose W hW hc hs using fun b : ParityWindow (activation h) ε => exists_rankWitness M hE
    (nominalPath M hE κ D C h (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)
    (nominalLayerSet M hE κ D C h (U : Set α) ε b \ O)
  have heq : (∑ b, (W b).ncard) = nominalRankStatistic M hE κ D C T h (U : Set α) O ε := by
    unfold nominalRankStatistic
    exact sum_congr rfl (fun b _ => hc b)
  have hd : Pairwise (fun b c => Disjoint (W b) (W c)) := by
    intro b c hbc
    exact (nominalLayerSet_disjoint M hE κ D C h (U : Set α) ε hbc).mono
      ((hW b).trans sdiff_subset) ((hW c).trans sdiff_subset)
  obtain ⟨Z, hZU, hZcard, β, hβ⟩ := collect_disjoint_witnesses W U
    (fun b => ((hW b).trans sdiff_subset).trans (nominalLayerSet_subset M hE κ D C h _ ε b)) hd
  refine ⟨W, hW, heq, hs, Z, hZU, ?_, β, hβ⟩
  rwa [heq] at hZcard

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [LinearOrder α]

noncomputable def groupLabel (U : Finset α) (i : Fin U.card) : α := (U.equivFin.symm i).val

lemma groupLabel_mem
    {α : Type u_1} [Fintype α] [LinearOrder α] (U : Finset α) (i : Fin U.card) :
    groupLabel U i ∈ U :=
  (U.equivFin.symm i).property

lemma exists_groupLabel
    {α : Type u_1} [Fintype α] [LinearOrder α] (U : Finset α) {e : α} (he : e ∈ U) :
    ∃ i, groupLabel U i = e := by
  refine ⟨U.equivFin ⟨e, he⟩, ?_⟩
  simp [groupLabel]

noncomputable def labeledResidualFamily (M : Matroid α) (U : Finset α) (κ : ℕ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α) : Finset (Finset α) :=
  (integerResidualFamily M U (U.card / κ) F a ε K (groupLabel U)).image
    (fun R => R.image (groupLabel U))

lemma labeledResidualFamily_subsets (M : Matroid α) (U : Finset α) (κ : ℕ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α) :
    ∀ R ∈ labeledResidualFamily M U κ F a ε K, R ⊆ U := by
  rintro R hR e he
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
  exact groupLabel_mem U i

lemma labeledResidualFamily_card (M : Matroid α) (hE : M.E = Set.univ)
    (U : Finset α) (hU : U.Nonempty) (κ : ℕ) (hκ : 2 ≤ κ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α) :
    ((labeledResidualFamily M U κ F a ε K).card : ℝ) ≤
      Real.exp (1000 * Real.log (κ : ℝ) / (κ : ℝ) * U.card) := by
  obtain ⟨d, hd⟩ := hU
  have hc : (labeledResidualFamily M U κ F a ε K).card ≤
      (integerResidualFamily M U (U.card / κ) F a ε K (groupLabel U)).card := Finset.card_image_le
  exact (show ((labeledResidualFamily M U κ F a ε K).card : ℝ) ≤
    (integerResidualFamily M U (U.card / κ) F a ε K (groupLabel U)).card by exact_mod_cast hc).trans
      (integerResidualFamily_card_le_exp M hE d U κ hκ F a ε K (groupLabel U) rfl)

noncomputable def nominalResidualSet (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2)
    (W : ParityWindow (activation h) ε → Set α) : Set α :=
  ⋃ b, nominalLayerSet M hE κ D C h U ε b \
    M.closure ((nominalPath M hE κ D C h (b.val.val - 2) ∪
      lowerCompetition M hE κ D C T b.val.val h) ∪ W b)

lemma nominalResidualSet_subset
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2)
    (W : ParityWindow (activation h) ε → Set α) :
    nominalResidualSet M hE κ D C T h U ε W ⊆ U := by
  intro e he
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp he
  exact hb.1.1

lemma nominalResidualSet_eq_labeled (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U Z : Finset α) (ε : Fin 2)
    (W : ParityWindow (activation h) ε → Set α) (β : Z → ParityWindow (activation h) ε)
    (hβ : ∀ b, (fun w : Z => w.val) '' {w | β w = b} = W b) :
    (integerResidual M (nominalPath M hE κ D C h) (groupLabel U) (activation h) ε
      (fun b => lowerCompetition M hE κ D C T b.val.val h) (fun w : Z => w.val) β).image (groupLabel U) =
        (Set.toFinite (nominalResidualSet M hE κ D C T h (U : Set α) ε W)).toFinset := by
  classical
  ext e
  simp only [Finset.mem_image, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨b, hb, hn⟩ := (Finset.mem_filter.mp hi).2
    have hl := (Finset.mem_filter.mp hb).2
    apply Set.mem_iUnion.mpr
    refine ⟨b, ?_, ?_⟩
    · exact ⟨groupLabel_mem U i, hl⟩
    · simpa only [hβ b] using hn
  · intro he
    obtain ⟨b, hb, hn⟩ := Set.mem_iUnion.mp he
    obtain ⟨i, hi⟩ := exists_groupLabel U hb.1
    refine ⟨i, ?_, hi⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, b, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hi] using hb.2⟩
    · simpa only [hi, hβ b] using hn

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [LinearOrder α]

lemma safeLayer_le_witness_residual
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (hI : I ⊆ D h)
    (ε : Fin 2) (b : ParityWindow (activation h) ε) (W : Set α) :
    (safeLayerSet M hE κ D C T h U I ε b).ncard ≤ κ * W.ncard +
      (nominalLayerSet M hE κ D C h U ε b \
        M.closure (nominalPath M hE κ D C h (b.val.val - 2) ∪
          lowerCompetition M hE κ D C T b.val.val h ∪ W)).ncard := by
  by_cases hv : activation h + 2 ≤ b.val.val ∧ b.val.val ≤ 0
  · have hx : nominalPath M hE κ D C h (b.val.val - 2) =
        densityExpansion M hE κ (D h) (guardedPath M hE κ D C h (b.val.val - 2)) := by
      unfold nominalPath densityEnabled
      rw [ite_eq_left (by omega)]
    rw [hx]
    apply safe_layer_le_witness_residual M hE κ (D h)
      (guardedPath M hE κ D C h (b.val.val - 2)) (lowerCompetition M hE κ D C T b.val.val h)
      W (nominalLayerSet M hE κ D C h U ε b) (safeLayerSet M hE κ D C T h U I ε b)
    intro e he
    exact ⟨⟨hI he.1.1, he.1.2⟩, he.2⟩
  · have he : nominalLayerSet M hE κ D C h U ε b = ∅ := by
      ext e
      constructor
      · exact fun he => (hv ⟨he.2.1, he.2.2.1⟩).elim
      · simp
    simp [safeLayerSet, he]

lemma safeStatistic_le_witness_residual (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (hI : I ⊆ D h)
    (ε : Fin 2) (W : ParityWindow (activation h) ε → Set α) :
    safeLayerStatistic M hE κ D C T h U I ε ≤ κ * (∑ b, (W b).ncard) +
      (nominalResidualSet M hE κ D C T h U ε W).ncard := by
  unfold safeLayerStatistic
  calc
    _ ≤ ∑ b, (κ * (W b).ncard +
        (nominalLayerSet M hE κ D C h U ε b \
          M.closure ((nominalPath M hE κ D C h (b.val.val - 2) ∪
            lowerCompetition M hE κ D C T b.val.val h) ∪ W b)).ncard) :=
      sum_le_sum (fun b _ => safeLayer_le_witness_residual M hE κ D C T h U I hI ε b (W b))
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum, ← residualUnion_ncard M _ _ W
        (nominalLayerSet_disjoint M hE κ D C h U ε)]
      rfl

lemma exists_captured_residual (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h : ℕ) (U : Finset α) (O I : Set α)
    (hDU : D h ⊆ (U : Set α)) (hI : I ⊆ D h)
    (hnonloop : ∀ e ∈ U, e ∉ M.closure ∅) (ε : Fin 2)
    (hzsmall : nominalRankStatistic M hE κ D C T h (U : Set α) O ε ≤ U.card / κ) :
    ∃ R ∈ labeledResidualFamily M U κ (guardedPath M hE κ D C h) (activation h) ε
        (fun b => lowerCompetition M hE κ D C T b.val.val h),
      (R : Set α) ⊆ O ∧ safeLayerStatistic M hE κ D C T h (U : Set α) I ε ≤
        κ * nominalRankStatistic M hE κ D C T h (U : Set α) O ε + R.card := by
  classical
  obtain ⟨W, hW, hsum, hspan, Z, hZU, hZcard, β, hβ⟩ :=
    nominal_rank_witnesses M hE κ D C T h U O ε
  let R := (Set.toFinite (nominalResidualSet M hE κ D C T h (U : Set α) ε W)).toFinset
  have hmask : (R : Set α) ⊆ O := by
    intro e he
    exact residualUnion_subset_mask M _ _ W O hspan ((Set.Finite.mem_toFinset _).mp he)
  have hdet : safeLayerStatistic M hE κ D C T h (U : Set α) I ε ≤
      κ * nominalRankStatistic M hE κ D C T h (U : Set α) O ε + R.card := by
    have h := safeStatistic_le_witness_residual M hE κ D C T h (U : Set α) I hI ε W
    rwa [hsum, Set.ncard_eq_toFinset_card] at h
  refine ⟨R, ?_, hmask, hdet⟩
  apply Finset.mem_image.mpr
  refine ⟨integerResidual M (nominalPath M hE κ D C h) (groupLabel U) (activation h) ε
      (fun b => lowerCompetition M hE κ D C T b.val.val h) (fun w : Z => w.val) β, ?_, ?_⟩
  · apply nominal_residual_mem_family M hE κ hκ D C h U Z hDU hZU (hZcard.trans hzsmall) ε
      (fun b => lowerCompetition M hE κ D C T b.val.val h)
      (fun b => lowerCompetition_subset_guarded M hE κ D C T b.val.val h) β
    · intro w
      have hw : w.val ∈ W (β w) := by
        rw [← hβ (β w)]
        exact ⟨w, rfl, rfl⟩
      exact (hW (β w) hw).1.2.2.2.1
    · exact fun i => hnonloop _ (groupLabel_mem U i)
  · exact nominalResidualSet_eq_labeled M hE κ D C T h U Z ε W β hβ

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [LinearOrder α]

lemma safeLayerStatistic_le_ncard
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (ε : Fin 2) :
    safeLayerStatistic M hE κ D C T h U I ε ≤ U.ncard := by
  let L := safeLayerSet M hE κ D C T h U I ε
  have hd : Pairwise (fun b c => Disjoint (L b) (L c)) := by
    intro b c hbc
    exact (nominalLayerSet_disjoint M hE κ D C h U ε hbc).mono
      (fun _ he => he.1.2) (fun _ he => he.1.2)
  have heq : (⋃ b, L b).ncard = ∑ b, (L b).ncard := by
    simpa only [finsum_eq_sum_of_fintype] using
      Set.ncard_iUnion_of_finite (fun b => Set.toFinite (L b)) hd
  rw [show safeLayerStatistic M hE κ D C T h U I ε = ∑ b, (L b).ncard from rfl, ← heq]
  apply Set.ncard_le_ncard _ (Set.toFinite U)
  intro e he
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp he
  exact hb.1.2.1

noncomputable def nominalTransferGap (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U O I : Set α) (ε : Fin 2) : ℝ :=
  max ((safeLayerStatistic M hE κ D C T h U I ε : ℝ) -
    (κ : ℝ) * nominalRankStatistic M hE κ D C T h U O ε) 0

lemma safe_le_rank_add_gap
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U O I : Set α) (ε : Fin 2) :
    (safeLayerStatistic M hE κ D C T h U I ε : ℝ) ≤
      (κ : ℝ) * nominalRankStatistic M hE κ D C T h U O ε +
        nominalTransferGap M hE κ D C T h U O I ε := by
  have hx := le_max_left ((safeLayerStatistic M hE κ D C T h U I ε : ℝ) -
    (κ : ℝ) * nominalRankStatistic M hE κ D C T h U O ε) 0
  unfold nominalTransferGap
  linarith

lemma nominalTransferGap_le_bad (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h : ℕ) (U S : Finset α) (O I : Set α)
    (hDU : D h ⊆ (U : Set α)) (hI : I ⊆ D h) (hS : S ⊆ U)
    (hOS : O ∩ (U : Set α) ⊆ (S : Set α))
    (hnonloop : ∀ e ∈ U, e ∉ M.closure ∅) (ε : Fin 2) :
    nominalTransferGap M hE κ D C T h (U : Set α) O I ε ≤
      residualDelta * U.card + (U.card : ℝ) * residualBadIndicator
        (labeledResidualFamily M U κ (guardedPath M hE κ D C h) (activation h) ε
          (fun b => lowerCompetition M hE κ D C T b.val.val h))
        (residualDelta * U.card) S := by
  classical
  let F := labeledResidualFamily M U κ (guardedPath M hE κ D C h) (activation h) ε
    (fun b => lowerCompetition M hE κ D C T b.val.val h)
  have hn : 0 ≤ residualDelta * (U.card : ℝ) + (U.card : ℝ) *
      residualBadIndicator F (residualDelta * U.card) S := by
    apply add_nonneg (mul_nonneg residualDelta_nonneg (Nat.cast_nonneg _))
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold residualBadIndicator
    split_ifs <;> norm_num
  by_cases hz : nominalRankStatistic M hE κ D C T h (U : Set α) O ε ≤ U.card / κ
  · obtain ⟨R, hR, hRO, hdet⟩ := exists_captured_residual M hE κ hκ D C T h U O I
      hDU hI hnonloop ε hz
    have hRU : R ⊆ U := labeledResidualFamily_subsets M U κ _ _ ε _ R hR
    have hRS : R ⊆ S := fun e he => hOS ⟨hRO he, hRU he⟩
    have hcap := capturedResidual_le U S R F hS hR hRS
    have hdet' : (safeLayerStatistic M hE κ D C T h (U : Set α) I ε : ℝ) ≤
        (κ : ℝ) * nominalRankStatistic M hE κ D C T h (U : Set α) O ε + R.card := by
      exact_mod_cast hdet
    exact max_le (by linarith) hn
  · have hnz : U.card < κ * nominalRankStatistic M hE κ D C T h (U : Set α) O ε := by
      have hz' := Nat.div_lt_iff_lt_mul hκ |>.mp (lt_of_not_ge hz)
      simpa only [Nat.mul_comm] using hz'
    have hs := safeLayerStatistic_le_ncard M hE κ D C T h (U : Set α) I ε
    rw [Set.ncard_coe_finset] at hs
    have hsz : (safeLayerStatistic M hE κ D C T h (U : Set α) I ε : ℝ) ≤
        (κ : ℝ) * nominalRankStatistic M hE κ D C T h (U : Set α) O ε := by
      exact_mod_cast hs.trans hnz.le
    exact max_le (by linarith) hn

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset Pivots
variable {n : ℕ}

noncomputable def listedTransferGap (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (ε : Fin 2) : ℝ :=
  max ((listedSafeStatistic M hE κ d s i Y ε : ℝ) -
    (κ : ℝ) * listedRankStatistic M hE κ d s i ε) 0

lemma trueGroup_nonloop (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) :
    ∀ e ∈ trueGroup M d s i, e ∉ M.closure ∅ := by
  intro e he hl
  have hc := (mem_trueGroup M d s i e).mp he
  exact hc.1.2.2 (M.closure_mono (Set.empty_subset _) hl)

noncomputable def focalResidualFamily (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (ε : Fin 2) :
    Finset (Finset (Fin n)) :=
  let r := focalReference M d s i
  labeledResidualFamily M (trueGroup M d s i) κ
    (guardedPath M hE κ (groupMask M r s r.D) (groupMask M r s r.C) (focalIndex M d s i))
    (activation (focalIndex M d s i)) ε
    (fun b => lowerCompetition M hE κ (groupMask M r s r.D) (groupMask M r s r.C)
      (groupMask M r s r.T) b.val.val (focalIndex M d s i))

lemma listedTransferGap_focal_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (ε : Fin 2) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) :
    listedTransferGap M hE κ (focalMasks d (trueGroup M d s i) A B C) s i Y ε ≤
      residualDelta * (trueGroup M d s i).card + ((trueGroup M d s i).card : ℝ) *
        residualBadIndicator (focalResidualFamily M hE κ d s i ε)
          (residualDelta * (trueGroup M d s i).card) (A ∪ B) := by
  classical
  by_cases hne : A.Nonempty
  · let f := focalMasks d (trueGroup M d s i) A B C
    have hg : groupMask M f s f.D (focalIndex M d s i) = (A : Set (Fin n)) :=
      focal_group_mask M d s i A B C d.D A hA hne hA
    have hDU : groupMask M f s f.D (focalIndex M d s i) ⊆ (trueGroup M d s i : Set (Fin n)) := by
      rw [hg]
      exact hA
    have hI : (f.D : Set (Fin n)) ∩ Y ⊆ groupMask M f s f.D (focalIndex M d s i) := by
      rw [hg, focal_density_inter M d s i A B C Y hY]
      exact Set.inter_subset_left
    have hOS : ((f.H ∪ f.D ∪ f.C : Finset (Fin n)) : Set (Fin n)) ∩
        (trueGroup M d s i : Set (Fin n)) ⊆ ((A ∪ B : Finset (Fin n)) : Set (Fin n)) := by
      have he := congrArg (fun X : Finset (Fin n) => (X : Set (Fin n)))
        (focal_observed_inter M d s i A B C hA hB)
      simpa only [coe_inter] using he.subset
    have h := nominalTransferGap_le_bad M hE κ hκ (groupMask M f s f.D)
      (groupMask M f s f.C) (groupMask M f s f.T) (focalIndex M d s i)
      (trueGroup M d s i) (A ∪ B) ((f.H ∪ f.D ∪ f.C : Finset (Fin n)) : Set (Fin n))
      ((f.D : Set (Fin n)) ∩ Y) hDU hI (union_subset hA hB) hOS
      (trueGroup_nonloop M d s i) ε
    have hF := funext (focal_incoming_path M hE κ d s i A B C hA hB hC hne)
    have hK := funext (fun b : ParityWindow (activation (focalIndex M d s i)) ε =>
      focal_lowerCompetition M hE κ d s i A B C hA hB hC hne b.val.val)
    rw [hF, hK] at h
    simpa only [listedTransferGap, listedSafeStatistic_focal_nonempty M hE κ d s i A B C Y ε hA hne,
      listedRankStatistic_focal_nonempty M hE κ d s i A B C ε hA hne,
      nominalTransferGap, focalResidualFamily] using h
  · have hAe : A = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst A
    rw [listedTransferGap, listedSafeStatistic_focal_empty, listedRankStatistic_focal_empty]
    simp only [Nat.cast_zero, mul_zero, sub_zero, max_self]
    apply add_nonneg (mul_nonneg residualDelta_nonneg (Nat.cast_nonneg _))
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold residualBadIndicator
    split_ifs <;> norm_num

lemma focalTransferGap_expectation_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
    (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) (ε : Fin 2) :
    tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
      (trueGroup M d s i) (fun A B C =>
        listedTransferGap M hE (2^100) (focalMasks d (trueGroup M d s i) A B C) s i Y ε) ≤
      2 * residualDelta * (trueGroup M d s i).card := by
  have ht0 : 0 ≤ thinningRate := constants_positive.2.2.1.le
  have ht1 : thinningRate ≤ 1 := by norm_num [thinningRate]
  have hu : (1:ℝ)/4 + (1-(1:ℝ)/4)*thinningRate ≤ 1/2 := by norm_num [thinningRate]
  have hne : (trueGroup M d s i).Nonempty := by
    apply card_pos.mp
    have hp := lt_of_lt_of_le constants_positive.2.1 hn
    exact_mod_cast hp
  apply tripleMask_residual_error_le (fun _ => (1:ℝ)/4) (fun _ => thinningRate)
    (fun _ => thinningRate) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => ht0) (fun _ => ht1) (fun _ => ht0) (fun _ => ht1) (fun _ => hu)
    (trueGroup M d s i) (focalResidualFamily M hE (2^100) d s i ε)
  · exact labeledResidualFamily_subsets M _ _ _ _ ε _
  · have hc := labeledResidualFamily_card M hE (trueGroup M d s i) hne (2^100)
        (by norm_num) (guardedPath M hE (2^100)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).D)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).C) (focalIndex M d s i))
        (activation (focalIndex M d s i)) ε
        (fun b => lowerCompetition M hE (2^100)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).D)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).C)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).T) b.val.val (focalIndex M d s i))
    simpa only [Nat.cast_pow, Nat.cast_ofNat, densityThreshold, focalResidualFamily] using hc
  · exact hn
  · intro A hA B hB C hC
    exact listedTransferGap_focal_le M hE (2^100) (by positivity) d s i Y hY ε A B C hA hB hC

end MatroidProphet.MainAlgorithm

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma tripleMaskExpectation_split (p q r : α → ℝ) (V U : Finset α) (hU : U ⊆ V)
    (f : Finset α → Finset α → Finset α → ℝ) :
    tripleMaskExpectation p q r V f =
      tripleMaskExpectation p q r (V \ U) (fun D C T =>
        tripleMaskExpectation p q r U (fun A B X => f (D ∪ A) (C ∪ B) (T ∪ X))) := by
  unfold tripleMaskExpectation
  rw [bitsExpectation_split p V U hU]
  apply bitsExpectation_congr
  intro D hD
  simp_rw [bitsExpectation_split q V U hU]
  rw [bitsExpectation_comm p q U (V \ U)]
  apply bitsExpectation_congr
  intro C hC
  simp_rw [bitsExpectation_split r V U hU]
  simp_rw [bitsExpectation_comm q r U (V \ U)]
  rw [bitsExpectation_comm p r U (V \ U)]

lemma tripleMaskExpectation_const (p q r : α → ℝ) (V : Finset α) (c : ℝ) :
    tripleMaskExpectation p q r V (fun _ _ _ => c) = c := by
  simp only [tripleMaskExpectation, bitsExpectation_const]

lemma tripleMaskExpectation_congr (p q r : α → ℝ) (V : Finset α)
    {f g : Finset α → Finset α → Finset α → ℝ}
    (h : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V, f D C T = g D C T) :
    tripleMaskExpectation p q r V f = tripleMaskExpectation p q r V g := by
  apply bitsExpectation_congr
  intro D hD
  apply bitsExpectation_congr
  intro C hC
  exact bitsExpectation_congr r V (fun T hT => h D hD C hC T hT)

namespace MainAlgorithm
variable {n : ℕ}

lemma focalMasks_withMasks (d : MainMasks n) (U D C T A B X : Finset (Fin n))
    (hD : D ⊆ univ \ U) (hC : C ⊆ univ \ U) (hT : T ⊆ univ \ U) :
    focalMasks (withMasks d D C T) U A B X = withMasks d (D ∪ A) (C ∪ B) (T ∪ X) := by
  have hD' : D \ U = D := by ext e; simp only [mem_sdiff]; exact ⟨And.left, fun he => ⟨he, (mem_sdiff.mp (hD he)).2⟩⟩
  have hC' : C \ U = C := by ext e; simp only [mem_sdiff]; exact ⟨And.left, fun he => ⟨he, (mem_sdiff.mp (hC he)).2⟩⟩
  have hT' : T \ U = T := by ext e; simp only [mem_sdiff]; exact ⟨And.left, fun he => ⟨he, (mem_sdiff.mp (hT he)).2⟩⟩
  simp only [focalMasks, withMasks, hD', hC', hT']

lemma listedTransferGap_expectation_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
    (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) (ε : Fin 2) :
    tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
      univ (fun A B C => listedTransferGap M hE (2^100) (withMasks d A B C) s i Y ε) ≤
      2 * residualDelta * (trueGroup M d s i).card := by
  rw [tripleMaskExpectation_split _ _ _ univ (trueGroup M d s i) (subset_univ _)]
  have ht0 : 0 ≤ thinningRate := constants_positive.2.2.1.le
  have ht1 : thinningRate ≤ 1 := by norm_num [thinningRate]
  calc
    _ ≤ tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
        (univ \ trueGroup M d s i) (fun _ _ _ => 2 * residualDelta * (trueGroup M d s i).card) := by
      apply tripleMaskExpectation_mono _ _ _ (fun _ => by norm_num) (fun _ => by norm_num)
        (fun _ => ht0) (fun _ => ht1) (fun _ => ht0) (fun _ => ht1)
      intro D hD C hC T hT
      have hh := focalTransferGap_expectation_le M hE (withMasks d D C T) s i Y hY hn ε
      apply le_trans ?_ hh
      apply le_of_eq
      apply tripleMaskExpectation_congr
      intro A hA B hB X hX
      rw [trueGroup_withMasks, focalMasks_withMasks d _ D C T A B X hD hC hT]
    _ = _ := tripleMaskExpectation_const _ _ _ _ _

lemma listedTransferGap_parity_expectation_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
    (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) :
    tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
      univ (fun A B C => fairParityExpectation (fun p =>
        listedTransferGap M hE (2^100) (withMasks d A B C) s i Y (boolParity p))) ≤
      2 * residualDelta * (trueGroup M d s i).card := by
  have h0 := listedTransferGap_expectation_le M hE d s i Y hY hn (boolParity false)
  have h1 := listedTransferGap_expectation_le M hE d s i Y hY hn (boolParity true)
  simp only [fairParityExpectation, div_eq_mul_inv, mul_comm _ ((2:ℝ)⁻¹)]
  rw [tripleMaskExpectation_mul, tripleMaskExpectation_add]
  linarith

end MainAlgorithm
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset

lemma fairParityExpectation_mono {f g : Bool → ℝ} (h : ∀ p, f p ≤ g p) :
    fairParityExpectation f ≤ fairParityExpectation g := by
  have h0 := h false
  have h1 := h true
  unfold fairParityExpectation
  linarith

lemma fairParityExpectation_const (c : ℝ) : fairParityExpectation (fun _ => c) = c := by
  unfold fairParityExpectation
  ring

lemma fairParityExpectation_add (f g : Bool → ℝ) :
    fairParityExpectation (fun p => f p + g p) = fairParityExpectation f + fairParityExpectation g := by
  unfold fairParityExpectation
  ring

lemma fairParityExpectation_mul (c : ℝ) (f : Bool → ℝ) :
    fairParityExpectation (fun p => c * f p) = c * fairParityExpectation f := by
  unfold fairParityExpectation
  ring

lemma bitsExpectation_fairParity {α : Type*} [DecidableEq α] (q : α → ℝ)
    (V : Finset α) (f : Finset α → Bool → ℝ) :
    bitsExpectation q V (fun T => fairParityExpectation (f T)) =
      fairParityExpectation (fun p => bitsExpectation q V (fun T => f T p)) := by
  simp only [fairParityExpectation, div_eq_mul_inv]
  rw [bitsExpectation_mul_right, bitsExpectation_add]

namespace MainAlgorithm
variable {n : ℕ}

noncomputable def mainMean (d : MainMasks n) (f : MainMasks n → ℝ) : ℝ :=
  tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
    univ (fun D C T => fairParityExpectation (fun p => f {withMasks d D C T with odd := p}))

lemma mainMean_mono (d : MainMasks n) {f g : MainMasks n → ℝ}
    (h : ∀ d', d'.H = d.H → f d' ≤ g d') : mainMean d f ≤ mainMean d g := by
  apply tripleMaskExpectation_mono _ _ _ (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => constants_positive.2.2.1.le) (fun _ => by norm_num [thinningRate])
    (fun _ => constants_positive.2.2.1.le) (fun _ => by norm_num [thinningRate])
  intro D hD C hC T hT
  exact fairParityExpectation_mono (fun p => h _ rfl)

lemma mainMean_const (d : MainMasks n) (c : ℝ) : mainMean d (fun _ => c) = c := by
  simp only [mainMean, fairParityExpectation_const, tripleMaskExpectation_const]

lemma mainMean_add (d : MainMasks n) (f g : MainMasks n → ℝ) :
    mainMean d (fun d' => f d' + g d') = mainMean d f + mainMean d g := by
  simp only [mainMean, fairParityExpectation_add, tripleMaskExpectation_add]

lemma mainMean_mul (d : MainMasks n) (c : ℝ) (f : MainMasks n → ℝ) :
    mainMean d (fun d' => c * f d') = c * mainMean d f := by
  simp only [mainMean, fairParityExpectation_mul, tripleMaskExpectation_mul]

lemma mainMean_guard_count (d : MainMasks n) (K : Finset (Fin n)) :
    mainMean d (fun d' => ((d'.C ∩ K).card : ℝ)) = thinningRate * K.card := by
  unfold mainMean tripleMaskExpectation MainAlgorithm.withMasks
  simp only [fairParityExpectation_const, bitsExpectation_const]
  have hc : bitsExpectation (fun _ : Fin n => thinningRate) univ
      (fun C => ((C ∩ K).card : ℝ)) = thinningRate * K.card := by
    simp_rw [Finset.inter_comm _ K]
    rw [bitsExpectation_card_inter _ univ K (subset_univ _)]
    simp [mul_comm]
  rw [hc]

end MainAlgorithm
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset

lemma sum_zpow_lt_upper (B : ℝ) (hB : 1 < B) (s : Finset ℤ) (l : ℤ)
    (hsl : ∀ i ∈ s, i < l) :
    (∑ i ∈ s, B ^ i) < B ^ l / (B - 1) := by
  classical
  induction s using Finset.strongInductionOn generalizing l with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · let m := s.max' hs
      have hm : m ∈ s := s.max'_mem hs
      have hrest : ∀ i ∈ s.erase m, i < m := by
        intro i hi
        exact lt_of_le_of_ne (s.le_max' i (mem_of_mem_erase hi)) (ne_of_mem_erase hi)
      have hsum := ih (s.erase m) (erase_ssubset hm) m hrest
      have hml : m + 1 ≤ l := by have := hsl m hm; omega
      have hp : B ^ (m + 1) ≤ B ^ l := zpow_le_zpow_right₀ hB.le hml
      have hden : 0 < B - 1 := sub_pos.mpr hB
      have heq : B ^ m / (B - 1) + B ^ m = B ^ (m + 1) / (B - 1) := by
        rw [zpow_add_one₀ (ne_of_gt (zero_lt_one.trans hB))]
        field_simp
        ring
      calc
        (∑ i ∈ s, B ^ i) = (∑ i ∈ s.erase m, B ^ i) + B ^ m :=
          (sum_erase_add _ _ hm).symm
        _ < B ^ m / (B - 1) + B ^ m := by linarith
        _ = B ^ (m + 1) / (B - 1) := heq
        _ ≤ B ^ l / (B - 1) := div_le_div_of_nonneg_right hp hden.le
    · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
      simp only [he, sum_empty]
      exact div_pos (zpow_pos (zero_lt_one.trans hB) _) (sub_pos.mpr hB)

lemma sum_zpow_le_two (B : ℝ) (hB : 2 ≤ B) (s : Finset ℤ) (l : ℤ)
    (hsl : ∀ i ∈ s, i ≤ l) :
    (∑ i ∈ s, B ^ i) ≤ 2 * B ^ l := by
  have hB1 : 1 < B := lt_of_lt_of_le (by norm_num) hB
  have hs := sum_zpow_lt_upper B hB1 s (l+1) (fun i hi => by have := hsl i hi; omega)
  have hp : 0 < B ^ l := zpow_pos (by linarith) _
  have hden : 0 < B - 1 := by linarith
  have hratio : B / (B - 1) ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
  rw [zpow_add_one₀ (ne_of_gt (zero_lt_one.trans hB1)), mul_div_assoc] at hs
  nlinarith

theorem higher_weight_cost (B : ℝ) (hB : 1 < B) (levels analyzed : Finset ℤ)
    (n : ℤ → ℝ) (hn : ∀ i ∈ levels, 0 ≤ n i) :
    (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, n l) ≤
      (∑ l ∈ levels, B ^ l * n l) / (B - 1) := by
  classical
  have heq : (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, n l) =
      ∑ l ∈ levels, (∑ i ∈ analyzed with i < l, B ^ i) * n l := by
    simp only [sum_filter, mul_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro l hl
    apply sum_congr rfl
    intro i hi
    split_ifs <;> simp_all
  rw [heq, sum_div]
  apply sum_le_sum
  intro l hl
  have hs := sum_zpow_lt_upper B hB (analyzed.filter (· < l)) l
    (fun i hi => (mem_filter.mp hi).2)
  have hm := mul_le_mul_of_nonneg_right hs.le (hn l hl)
  simpa [div_mul_eq_mul_div] using hm

theorem cumulative_weight_bound {α : Type*} [DecidableEq α]
    (B : ℝ) (hB : 2 ≤ B) (A : Finset α) (level : α → ℤ) (analyzed : Finset ℤ) :
    (∑ i ∈ analyzed, B ^ i * ((A.filter (fun e => i ≤ level e)).card : ℝ)) ≤
      2 * ∑ e ∈ A, B ^ level e := by
  classical
  have heq : (∑ i ∈ analyzed, B ^ i * ((A.filter (fun e => i ≤ level e)).card : ℝ)) =
      ∑ e ∈ A, ∑ i ∈ analyzed with i ≤ level e, B ^ i := by
    simp_rw [sum_filter]
    conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [← sum_filter]
    simp [mul_comm]
  rw [heq, mul_sum]
  exact sum_le_sum fun e _ => sum_zpow_le_two B hB _ _
    (fun i hi => (mem_filter.mp hi).2)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset

lemma cumulative_option_weight_bound {α : Type*} [DecidableEq α]
    (B : ℝ) (hB : 2 ≤ B) (A : Finset α) (level : α → Option ℤ) (analyzed : Finset ℤ) :
    (∑ i ∈ analyzed, B ^ i * ((A.filter (fun e => ∃ j, level e = some j ∧ i ≤ j)).card : ℝ)) ≤
      2 * ∑ e ∈ A, levelWeight B (level e) := by
  classical
  let P := A.filter (fun e => level e ≠ none)
  have hfilter (i : ℤ) : P.filter (fun e => i ≤ (level e).getD 0) =
      A.filter (fun e => ∃ j, level e = some j ∧ i ≤ j) := by
    ext e
    cases he : level e <;> simp [P, he]
  have hsum : (∑ e ∈ P, B ^ (level e).getD 0) = ∑ e ∈ A, levelWeight B (level e) := by
    unfold P
    rw [sum_filter]
    apply sum_congr rfl
    intro e he
    cases level e <;> simp [levelWeight]
  have hc := cumulative_weight_bound B hB P (fun e => (level e).getD 0) analyzed
  simpa only [hfilter, hsum] using hc

namespace MainAlgorithm
variable {n : ℕ}

noncomputable def mainWorstRounded (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) : ℝ := by
  classical
  exact univ.inf' univ_nonempty (fun π : ArrivalOrder n =>
    ∑ e ∈ selection M hE d w π, levelWeight weightBase (w e))

lemma mainWorstRounded_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n) :
    mainWorstRounded M hE d w ≤ ∑ e ∈ selection M hE d w π, levelWeight weightBase (w e) := by
  classical
  exact inf'_le _ (mem_univ π)

lemma mainWorstRounded_nonneg (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) : 0 ≤ mainWorstRounded M hE d w := by
  classical
  apply le_inf'
  intro π hπ
  apply sum_nonneg
  intro e he
  cases w e with
  | none => exact le_rfl
  | some i => exact (zpow_pos (by norm_num [weightBase]) i).le

lemma weighted_trueLambda_le_selection (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (analyzed : Finset ℤ) (π : ArrivalOrder n) :
    (1/2 : ℝ) * ∑ i ∈ analyzed, weightBase ^ i * (trueLambda M hE d w i : ℝ) ≤
      ∑ e ∈ selection M hE d w π, levelWeight weightBase (w e) := by
  have hc := cumulative_option_weight_bound weightBase (by norm_num [weightBase])
    (selection M hE d w π) w analyzed
  have hr : (∑ i ∈ analyzed, weightBase ^ i * (trueLambda M hE d w i : ℝ)) ≤
      ∑ i ∈ analyzed, weightBase ^ i *
        (((selection M hE d w π).filter (fun e => ∃ j, w e = some j ∧ i ≤ j)).card : ℝ) := by
    apply sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (zpow_pos (by norm_num [weightBase]) i).le
    exact_mod_cast trueLambda_le_count M hE d w π i
  linarith

lemma weighted_trueLambda_le_mainWorstRounded (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (analyzed : Finset ℤ) :
    (1/2 : ℝ) * ∑ i ∈ analyzed, weightBase ^ i * (trueLambda M hE d w i : ℝ) ≤
      mainWorstRounded M hE d w := by
  classical
  apply le_inf'
  intro π hπ
  exact weighted_trueLambda_le_selection M hE d w analyzed π

lemma mainMean_sum {β : Type*} (d : MainMasks n) (I : Finset β) (f : β → MainMasks n → ℝ) :
    mainMean d (fun d' => ∑ i ∈ I, f i d') = ∑ i ∈ I, mainMean d (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [sum_empty, mainMean_const]
  | @insert a I ha ih => simp only [sum_insert ha, mainMean_add, ih]

lemma weighted_mean_trueLambda_le_mainWorstRounded (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (analyzed : Finset ℤ) :
    (1/2 : ℝ) * ∑ i ∈ analyzed, weightBase ^ i * mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)) ≤
      mainMean d (fun d' => mainWorstRounded M hE d' w) := by
  have hh := mainMean_mono d (fun d' _ => weighted_trueLambda_le_mainWorstRounded M hE d' w analyzed)
  simpa only [mainMean_mul, mainMean_sum] using hh

lemma mainWorstRounded_le_hiddenWorstReward (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (r : Seed (mainSeedBits n)) (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    mainWorstRounded M hE (mainMasks r) (fun e => roundedLevel weightBase (w e)) ≤
      hiddenWorstReward (hidden M hE) w r := by
  classical
  apply le_inf'
  intro π hπ
  exact (mainWorstRounded_le M hE (mainMasks r) _ π).trans
    (rounded_selection_le_hiddenReward M hE r w hw π)

end MainAlgorithm
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset
variable {n : ℕ}

lemma groupMask_function_eq_inter (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) :
    groupMask M d w mask = fun j => (mask : Set (Fin n)) ∩ (pathGroups M d w j : Set (Fin n)) := by
  funext j
  exact groupMask_eq_inter M d w mask j

lemma listedZ_update_T (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (T : Finset (Fin n)) :
    listedZ M hE {d with T := T} w h =
      nominalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
        (fun j => (T : Set (Fin n)) ∩ (pathGroups M d w j : Set (Fin n))) h (pathGroups M d w h)
        ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd) := by
  unfold listedZ
  change nominalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w T) h (groupMask M d w univ h)
      ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd) = _
  rw [groupMask_function_eq_inter M d w T, ← pathGroups_coe]

lemma listedLambda_update_T (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (T : Finset (Fin n)) :
    listedLambda M hE {d with T := T} w h =
      finalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
        (fun j => (T : Set (Fin n)) ∩ (pathGroups M d w j : Set (Fin n))) h (groups M d w).length
        (pathGroups M d w h) ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n))
        (T : Set (Fin n)) (boolParity d.odd) := by
  unfold listedLambda
  change finalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w T) h (groups M d w).length (groupMask M d w univ h)
      ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (T : Set (Fin n)) (boolParity d.odd) = _
  rw [groupMask_function_eq_inter M d w T, ← pathGroups_coe]

theorem listed_expected_nominal_to_final (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (hh : h < (groups M d w).length)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    densityThreshold * t * bitsExpectation (fun _ : Fin n => t) univ (fun T =>
      (listedZ M hE {d with T := T} w h : ℝ)) ≤
    densityThreshold * bitsExpectation (fun _ : Fin n => t) univ (fun T =>
      (listedLambda M hE {d with T := T} w h : ℝ)) +
      t * ((2^100) * (groupMask M d w d.C h).ncard +
        ∑ j ∈ range ((groups M d w).length-(h+1)),
          ((2^100) * (groupMask M d w d.C (h+1+j)).ncard +
            (groupMask M d w d.D (h+1+j)).ncard) : ℕ) := by
  have hc := expected_nominal_to_final M hE (2^100) (by positivity)
    (groupMask M d w d.D) (groupMask M d w d.C) (pathGroups M d w)
    (pathGroups_disjoint M d w) h ((groups M d w).length-(h+1))
    ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd) t ht0 ht1
  have hlen : h+1+((groups M d w).length-(h+1)) = (groups M d w).length := by omega
  rw [hlen] at hc
  simp only [listedZ_update_T, listedLambda_update_T]
  convert hc using 1 <;> norm_num [densityThreshold]

end MatroidProphet.MainAlgorithm

end OAI
end
end

section
section
namespace OAI

open Finset Set

namespace MatroidProphet
namespace Candidates

variable {n : ℕ}

def prior (time : Fin n → ℕ) (H : Finset (Fin n)) (e : Fin n) : Set (Fin n) :=
  {f | f ∈ H ∧ time f < time e}

noncomputable def greedy (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (H : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact H.filter fun e => e ∉ M.closure (prior time H e)

noncomputable def candidates (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (V H : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact (V \ H).filter fun e => e ∉ M.closure (prior time H e)

lemma prior_insert_self (time : Fin n → ℕ) (H : Finset (Fin n)) (e : Fin n) :
    prior time (insert e H) e = prior time H e := by
  ext f
  simp only [prior, Set.mem_ofPred_eq, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hf, hlt⟩
    · exact (lt_irrefl _ hlt).elim
    · exact ⟨hf, hlt⟩
  · rintro ⟨hf, hlt⟩
    exact ⟨Or.inr hf, hlt⟩

lemma prior_mono (time : Fin n → ℕ) {H V : Finset (Fin n)} (h : H ⊆ V)
    (e : Fin n) : prior time H e ⊆ prior time V e :=
  fun _ hf => ⟨h hf.1, hf.2⟩

lemma greedy_indep (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (ht : Function.Injective time) (H : Finset (Fin n))
    (hground : ∀ e ∈ H, e ∈ M.E) : M.Indep (greedy M time H : Set (Fin n)) := by
  classical
  let label : H → Fin n := Subtype.val
  let arrival : H → ℕ := fun e => time e.val
  have htime : Function.Injective arrival := fun _ _ h => Subtype.ext (ht h)
  have hp (e : H) : label '' {p : H | arrival p < arrival e} = prior time H e.val := by
    ext f
    simp [label, arrival, prior, and_comm]
  have hi := Pivots.keptOccurrences_indep M label arrival (fun e => hground e.val e.property) htime
  have heq : label '' (Pivots.keptOccurrences M label arrival : Set H) =
      (greedy M time H : Set (Fin n)) := by
    ext e
    simp only [Set.mem_image, Finset.mem_coe, Pivots.keptOccurrences, Finset.mem_filter,
      Finset.mem_univ, true_and, greedy]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f.property, by simpa only [hp] using hf⟩
    · rintro ⟨he, hp'⟩
      refine ⟨⟨e, he⟩, ?_, rfl⟩
      simpa only [hp] using hp'
  rwa [heq] at hi

lemma greedy_sdiff_subset_candidates (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (V H : Finset (Fin n)) (hHV : H ⊆ V) :
    greedy M time V \ H ⊆ candidates M time V H := by
  classical
  intro e he
  rcases Finset.mem_sdiff.mp he with ⟨heG, heH⟩
  rcases Finset.mem_filter.mp heG with ⟨heV, hecl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨heV, heH⟩, ?_⟩
  exact fun h => hecl (M.closure_subset_closure (prior_mono time hHV e) h)

lemma expectation_sum (q : Fin n → ℝ) (V I : Finset (Fin n))
    (f : Fin n → Finset (Fin n) → ℝ) :
    bitsExpectation q V (fun H => ∑ e ∈ I, f e H) =
      ∑ e ∈ I, bitsExpectation q V (f e) := by
  simp only [bitsExpectation, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma expectation_not_mem (q : Fin n → ℝ) (V : Finset (Fin n))
    (e : Fin n) (he : e ∈ V) (c : ℝ) :
    bitsExpectation q V (fun H => if e ∉ H then c else 0) = (1 - q e) * c := by
  have hno : bitsExpectation q (V.erase e) (fun H => if e ∉ H then c else 0) = c := by
    calc
      _ = bitsExpectation q (V.erase e) (fun _ => c) := by
        apply bitsExpectation_congr
        intro H hH
        have heH : e ∉ H := fun hh => (Finset.mem_erase.mp (hH hh)).1 rfl
        simp [heH]
      _ = c := bitsExpectation_const q _ c
  have hyes : bitsExpectation q (V.erase e) (fun H => if e ∉ insert e H then c else 0) = 0 := by
    simp only [Finset.mem_insert_self, not_true_eq_false, ite_false]
    exact bitsExpectation_const q _ 0
  calc
    _ = bitsExpectation q (insert e (V.erase e)) (fun H => if e ∉ H then c else 0) := by
      rw [Finset.insert_erase he]
    _ = (1 - q e) * c := by
      rw [bitsExpectation_insert q _ e (by simp), hno, hyes]
      ring

lemma expectation_sdiff_fair (V I : Finset (Fin n)) (hIV : I ⊆ V) (w : Weights n) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) V (fun H => ∑ e ∈ I \ H, w e) =
      (∑ e ∈ I, w e) / 2 := by
  classical
  have hsum (H : Finset (Fin n)) :
      (∑ e ∈ I \ H, w e) = ∑ e ∈ I, if e ∉ H then w e else 0 := by
    rw [Finset.sdiff_eq_filter, Finset.sum_filter]
  simp_rw [hsum]
  rw [expectation_sum]
  calc
    (∑ e ∈ I, bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => if e ∉ H then w e else 0)) =
        ∑ e ∈ I, (1 - (1 / 2 : ℝ)) * w e := by
      apply Finset.sum_congr rfl
      intro e he
      exact expectation_not_mem _ V e (hIV he) (w e)
    _ = (∑ e ∈ I, w e) / 2 := by
      rw [← Finset.mul_sum]
      ring

lemma greedy_sdiff_indep (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (ht : Function.Injective time) (V H : Finset (Fin n))
    (hground : ∀ e ∈ V, e ∈ M.E) :
    M.Indep (greedy M time V \ H : Set (Fin n)) := by
  apply (greedy_indep M time ht V hground).subset
  intro e he
  exact he.1

lemma expectation_greedy_sdiff_fair (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (V : Finset (Fin n)) (w : Weights n) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) V (fun H => ∑ e ∈ greedy M time V \ H, w e) =
      (∑ e ∈ greedy M time V, w e) / 2 := by
  classical
  apply expectation_sdiff_fair
  exact Finset.filter_subset _ _

lemma expectation_fair_balance (V : Finset (Fin n)) (e : Fin n) (he : e ∈ V)
    (p : Finset (Fin n) → Prop) [DecidablePred p] (hp : ∀ H, p (insert e H) ↔ p H) (c : ℝ) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => if e ∈ H then 0 else if p H then c else 0) =
      bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => if e ∈ H then (if p H then c else 0) else 0) := by
  classical
  let q : Fin n → ℝ := fun _ => 1 / 2
  let f : Finset (Fin n) → ℝ := fun H => if p H then c else 0
  have heH : ∀ H ⊆ V.erase e, e ∉ H := by
    intro H hH he'
    exact (Finset.mem_erase.mp (hH he')).1 rfl
  have hn0 : bitsExpectation q (V.erase e)
      (fun H => if e ∈ H then 0 else if p H then c else 0) =
        bitsExpectation q (V.erase e) f := by
    apply bitsExpectation_congr
    intro H hH
    simp [heH H hH, f]
  have hn1 : bitsExpectation q (V.erase e)
      (fun H => if e ∈ insert e H then 0 else if p (insert e H) then c else 0) = 0 := by
    simp only [Finset.mem_insert_self, ite_true]
    exact bitsExpectation_const q _ 0
  have hy0 : bitsExpectation q (V.erase e)
      (fun H => if e ∈ H then (if p H then c else 0) else 0) = 0 := by
    calc
      _ = bitsExpectation q (V.erase e) (fun _ => 0) := by
        apply bitsExpectation_congr
        intro H hH
        simp [heH H hH]
      _ = 0 := bitsExpectation_const q _ 0
  have hy1 : bitsExpectation q (V.erase e)
      (fun H => if e ∈ insert e H then (if p (insert e H) then c else 0) else 0) =
        bitsExpectation q (V.erase e) f := by
    apply bitsExpectation_congr
    intro H _
    simp [hp H, f]
  change bitsExpectation q V _ = bitsExpectation q V _
  conv_lhs => rw [← Finset.insert_erase he]
  conv_rhs => rw [← Finset.insert_erase he]
  rw [bitsExpectation_insert q _ e (by simp),
    bitsExpectation_insert q _ e (by simp), hn0, hn1, hy0, hy1]
  dsimp [q]
  ring

lemma expectation_candidates_eq_greedy (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (V : Finset (Fin n)) (w : Weights n) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => ∑ e ∈ candidates M time V H, w e) =
      bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => ∑ e ∈ greedy M time H, w e) := by
  classical
  let p : Fin n → Finset (Fin n) → Prop := fun e H => e ∉ M.closure (prior time H e)
  have hc (H : Finset (Fin n)) :
      (∑ e ∈ candidates M time V H, w e) =
        ∑ e ∈ V, if e ∈ H then 0 else if p e H then w e else 0 := by
    simp [candidates, Finset.sdiff_eq_filter, Finset.sum_filter, p]
  have hg (H : Finset (Fin n)) (hH : H ⊆ V) :
      (∑ e ∈ greedy M time H, w e) =
        ∑ e ∈ V, if e ∈ H then (if p e H then w e else 0) else 0 := by
    have hset : greedy M time H = V.filter (fun e => e ∈ H ∧ p e H) := by
      ext e
      simp only [greedy, Finset.mem_filter, p]
      constructor
      · intro he
        exact ⟨hH he.1, he⟩
      · intro he
        exact he.2
    rw [hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e ∈ H <;> simp [he]
  calc
    _ = bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => ∑ e ∈ V, if e ∈ H then 0 else if p e H then w e else 0) := by
      apply bitsExpectation_congr
      intro H _
      exact hc H
    _ = ∑ e ∈ V, bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => if e ∈ H then 0 else if p e H then w e else 0) := expectation_sum _ _ _ _
    _ = ∑ e ∈ V, bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => if e ∈ H then (if p e H then w e else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      apply expectation_fair_balance V e he (p e) _ (w e)
      intro H
      simp [p, prior_insert_self]
    _ = bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => ∑ e ∈ V, if e ∈ H then (if p e H then w e else 0) else 0) :=
      (expectation_sum _ _ _ _).symm
    _ = _ := by
      apply bitsExpectation_congr
      intro H hH
      exact (hg H hH).symm

theorem expectation_candidates_le_optimum (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (ht : Function.Injective time) (V : Finset (Fin n))
    (hground : ∀ e ∈ V, e ∈ M.E) (w : Weights n) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => ∑ e ∈ candidates M time V H, w e) ≤ optimum M w := by
  rw [expectation_candidates_eq_greedy]
  calc
    _ ≤ bitsExpectation (fun _ => (1 / 2 : ℝ)) V (fun _ => optimum M w) := by
      apply bitsExpectation_mono _ (by intro e; norm_num) (by intro e; norm_num)
      intro H hH
      exact sum_le_optimum M w _ (greedy_indep M time ht H (fun e he => hground e (hH he)))
    _ = _ := bitsExpectation_const _ _ _

end Candidates
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Maximum

open MeasureTheory Finset Set

variable {n bits : ℕ} {K : Type*} [Countable K] [MeasurableSpace K]
  [MeasurableSingletonClass K]

noncomputable def firstRule (key : ℝ → K) (hkey : Measurable key)
    (allowed : Seed bits → (Fin n → K) → (Fin n × K) → Prop) : OnlineRule n bits := by
  classical
  exact discreteOnlineRule key hkey (fun k r s hist => decide
    (allowed r s (hist ⟨k.val, Nat.lt_succ_self _⟩) ∧
      ∀ j : Fin (k.val + 1), j.val < k.val → ¬ allowed r s (hist j)))

lemma firstRule_decision (key : ℝ → K) (hkey : Measurable key)
    (allowed : Seed bits → (Fin n → K) → (Fin n × K) → Prop)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (k : Fin n) :
    decisionAt (firstRule key hkey allowed) r s v π k = true ↔
      allowed r (fun e => key (s e)) (π k, key (v (π k))) ∧
      ∀ i : Fin n, i.val < k.val →
        ¬ allowed r (fun e => key (s e)) (π i, key (v (π i))) := by
  classical
  change decide (allowed r (fun e => key (s e)) (π k, key (v (π k))) ∧
    ∀ j : Fin (k.val + 1), j.val < k.val →
      ¬ allowed r (fun e => key (s e))
        (π (prefixIndex k j), key (v (π (prefixIndex k j))))) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨hc, fun i hi => ?_⟩
    exact hp ⟨i.val, by omega⟩ hi
  · rintro ⟨hc, hp⟩
    exact ⟨hc, fun j hj => hp (prefixIndex k j) hj⟩

lemma firstRule_unique (key : ℝ → K) (hkey : Measurable key)
    (allowed : Seed bits → (Fin n → K) → (Fin n × K) → Prop)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ)
    {e f : Fin n}
    (he : e ∈ acceptedThrough (firstRule key hkey allowed) r s v π t)
    (hf : f ∈ acceptedThrough (firstRule key hkey allowed) r s v π t) : e = f := by
  have he' := (firstRule_decision key hkey allowed r s v π (π.symm e)).1
    ((Finset.mem_filter.mp he).2).2
  have hf' := (firstRule_decision key hkey allowed r s v π (π.symm f)).1
    ((Finset.mem_filter.mp hf).2).2
  rcases lt_trichotomy (π.symm e).val (π.symm f).val with hlt | heq | hgt
  · exact False.elim (hf'.2 (π.symm e) hlt he'.1)
  · exact π.symm.injective (Fin.ext heq)
  · exact False.elim (he'.2 (π.symm f) hgt hf'.1)

lemma firstRule_feasible (M : Matroid (Fin n)) (key : ℝ → K) (hkey : Measurable key)
    (allowed : Seed bits → (Fin n → K) → (Fin n × K) → Prop)
    (ha : ∀ r s x, allowed r s x → M.Indep ({x.1} : Set (Fin n))) :
    Feasible M (firstRule key hkey allowed) := by
  intro r s v π t _ _
  classical
  by_cases h : (acceptedThrough (firstRule key hkey allowed) r s v π t).Nonempty
  · obtain ⟨e, he⟩ := h
    have ha' := (firstRule_decision key hkey allowed r s v π (π.symm e)).1
      ((Finset.mem_filter.mp he).2).2
    have hi : M.Indep ({e} : Set (Fin n)) := by
      simpa only [Equiv.apply_symm_apply] using ha r (fun f => key (s f)) _ ha'.1
    apply hi.subset
    intro f hf
    exact Set.mem_singleton_iff.mpr (firstRule_unique key hkey allowed r s v π t hf he)
  · have he : acceptedThrough (firstRule key hkey allowed) r s v π t = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    simp [he]

lemma firstRule_single_qualifier (key : ℝ → K) (hkey : Measurable key)
    (allowed : Seed bits → (Fin n → K) → (Fin n × K) → Prop)
    (r : Seed bits) (s v : Weights n) (g : Fin n)
    (ha : ∀ e, allowed r (fun f => key (s f)) (e, key (v e)) ↔ e = g)
    (π : ArrivalOrder n) : accepted (firstRule key hkey allowed) r s v π = {g} := by
  classical
  ext e
  simp only [accepted, acceptedThrough, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨_, hd⟩
    have hc := ((firstRule_decision key hkey allowed r s v π (π.symm e)).1 hd).1
    exact (ha e).1 (by simpa using hc)
  · intro heg
    subst e
    refine ⟨(π.symm g).isLt, (firstRule_decision key hkey allowed r s v π (π.symm g)).2 ?_⟩
    constructor
    · simpa using (ha g).2 rfl
    · intro i hi hallowed
      have heq : π i = g := (ha (π i)).1 hallowed
      have hieq : i = π.symm g := by simpa using congrArg π.symm heq
      exact Nat.lt_irrefl _ (hieq ▸ hi)

def higher [LinearOrder K] (x y : Fin n × K) : Prop :=
  y.2 < x.2 ∨ (x.2 = y.2 ∧ x.1 < y.1)

def threshold [LinearOrder K] (M : Matroid (Fin n)) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) (r : Seed bits) (s : Fin n → K)
    (x : Fin n × K) : Prop :=
  x.1 ∉ mask r ∧ M.Indep ({x.1} : Set (Fin n)) ∧ active x.2 ∧
    ∀ f ∈ mask r, M.Indep ({f} : Set (Fin n)) → active (s f) → higher x (f, s f)

noncomputable def maximumRule [LinearOrder K] (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) : OnlineRule n bits :=
  firstRule key hkey (threshold M active mask)

lemma maximumRule_feasible [LinearOrder K] (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) : Feasible M (maximumRule M key hkey active mask) :=
  firstRule_feasible M key hkey _ (fun _ _ _ hx => hx.2.1)

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma higher_irrefl [LinearOrder K] (x : Fin n × K) : ¬ higher x x := by
  simp [higher]

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma higher_trans [LinearOrder K] {x y z : Fin n × K}
    (hxy : higher x y) (hyz : higher y z) : higher x z := by
  rcases hxy with hxy | ⟨hxy, hxy'⟩ <;> rcases hyz with hyz | ⟨hyz, hyz'⟩
  · exact Or.inl (hyz.trans hxy)
  · exact Or.inl (hyz ▸ hxy)
  · exact Or.inl (hxy ▸ hyz)
  · exact Or.inr ⟨hxy.trans hyz, hxy'.trans hyz'⟩

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma higher_total [LinearOrder K] {x y : Fin n × K} (h : x ≠ y) :
    higher x y ∨ higher y x := by
  rcases lt_trichotomy x.2 y.2 with hlt | heq | hgt
  · exact Or.inr (Or.inl hlt)
  · have hn : x.1 ≠ y.1 := fun hxy => h (Prod.ext hxy heq)
    rcases lt_or_gt_of_ne hn with hxy | hyx
    · exact Or.inl (Or.inr ⟨heq, hxy⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hyx⟩)
  · exact Or.inl (Or.inl hgt)

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in

lemma threshold_top_two [LinearOrder K] (M : Matroid (Fin n))
    (active : K → Prop) (mask : Seed bits → Finset (Fin n))
    (r : Seed bits) (a : Fin n → K) (g h : Fin n)
    (hg : M.Indep ({g} : Set (Fin n))) (hag : active (a g))
    (hh : M.Indep ({h} : Set (Fin n))) (hah : active (a h))
    (htop : ∀ f, M.Indep ({f} : Set (Fin n)) → active (a f) → f ≠ g →
      higher (g, a g) (f, a f))
    (hsecond : ∀ f, M.Indep ({f} : Set (Fin n)) → active (a f) → f ≠ g → f ≠ h →
      higher (h, a h) (f, a f))
    (hgm : g ∉ mask r) (hhm : h ∈ mask r) :
    ∀ e, threshold M active mask r a (e, a e) ↔ e = g := by
  intro e
  constructor
  · intro he
    by_contra heg
    have heh : e ≠ h := fun heq => he.1 (heq ▸ hhm)
    have heh' := he.2.2.2 h hhm hh hah
    exact higher_irrefl _ (higher_trans heh' (hsecond e he.2.1 he.2.2.1 heg heh))
  · rintro rfl
    refine ⟨hgm, hg, hag, ?_⟩
    intro f hfm hf haf
    exact htop f hf haf (fun hfg => hgm (hfg ▸ hfm))

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma threshold_congr_samples [LinearOrder K] (M : Matroid (Fin n))
    (active : K → Prop) (mask : Seed bits → Finset (Fin n)) (r : Seed bits)
    (s t : Fin n → K) (hst : ∀ f ∈ mask r, s f = t f) (x : Fin n × K) :
    threshold M active mask r s x ↔ threshold M active mask r t x := by
  unfold threshold
  constructor <;> rintro ⟨hm, hi, ha, h⟩ <;> refine ⟨hm, hi, ha, ?_⟩
  · intro f hf hfi hfa
    simpa only [hst f hf] using h f hf hfi (by simpa only [hst f hf] using hfa)
  · intro f hf hfi hfa
    simpa only [hst f hf] using h f hf hfi (by simpa only [hst f hf] using hfa)

noncomputable def maximumHidden [LinearOrder K] (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) : HiddenRule n bits :=
  ⟨mask, maximumRule M key hkey active mask⟩

lemma maximumHidden_feasible [LinearOrder K] (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) (w : Weights n) (hw : ∀ e, 0 ≤ w e)
    (r : Seed bits) (π : ArrivalOrder n) (t : ℕ) :
    M.Indep (hiddenAcceptedThrough (maximumHidden M key hkey active mask) r w π t :
      Set (Fin n)) := by
  apply (maximumRule_feasible M key hkey active mask r
    (observed (maximumHidden M key hkey active mask) r w) w π t ?_ hw).subset
  · intro e he
    exact (Finset.mem_sdiff.mp he).1
  · intro e
    classical
    simp only [observed]
    split_ifs
    · exact hw e
    · exact le_rfl

lemma maximumHidden_single_qualifier [LinearOrder K] (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) (w : Weights n) (r : Seed bits) (g : Fin n)
    (hg : g ∉ mask r)
    (ha : ∀ e, threshold M active mask r (fun f => key (w f)) (e, key (w e)) ↔ e = g)
    (π : ArrivalOrder n) :
    hiddenReward (maximumHidden M key hkey active mask) r w π = w g := by
  classical
  let A := maximumHidden M key hkey active mask
  have hsingle : accepted A.core r (observed A r w) w π = {g} := by
    apply firstRule_single_qualifier key hkey (threshold M active mask)
    intro e
    rw [threshold_congr_samples M active mask r
      (fun f => key (observed A r w f)) (fun f => key (w f))]
    · exact ha e
    · intro f hf
      simp [observed, A, maximumHidden, hf]
  change (∑ e ∈ accepted A.core r (observed A r w) w π \ mask r, w e) = w g
  rw [hsingle]
  have hd : ({g} : Finset (Fin n)) \ mask r = {g} := by
    apply Finset.sdiff_eq_self_of_disjoint
    simpa only [Finset.disjoint_singleton_left] using hg
  rw [hd, Finset.sum_singleton]

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma exists_top [LinearOrder K] (a : Fin n → K) (V : Finset (Fin n)) (hV : V.Nonempty) :
    ∃ g ∈ V, ∀ f ∈ V, f ≠ g → higher (g, a g) (f, a f) := by
  classical
  induction V using Finset.induction_on with
  | empty => simp at hV
  | @insert e V he ih =>
    by_cases hn : V.Nonempty
    · obtain ⟨g, hg, htop⟩ := ih hn
      have heg : e ≠ g := fun heq => he (heq ▸ hg)
      by_cases heg' : higher (e, a e) (g, a g)
      · refine ⟨e, Finset.mem_insert_self _ _, ?_⟩
        intro f hf hfe
        have hfV : f ∈ V := (Finset.mem_insert.mp hf).resolve_left hfe
        by_cases hfg : f = g
        · simpa [hfg] using heg'
        · exact higher_trans heg' (htop f hfV hfg)
      · refine ⟨g, Finset.mem_insert_of_mem hg, ?_⟩
        intro f hf hfg
        rcases Finset.mem_insert.mp hf with hfe | hfV
        · subst f
          exact (higher_total (show (e, a e) ≠ (g, a g) from
            fun h => heg (congrArg Prod.fst h))).resolve_left heg'
        · exact htop f hfV hfg
    · have hv : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst V
      exact ⟨e, by simp, by simp⟩

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma threshold_only_positive [LinearOrder K] (M : Matroid (Fin n))
    (active : K → Prop) (mask : Seed bits → Finset (Fin n))
    (r : Seed bits) (a : Fin n → K) (g : Fin n)
    (hg : M.Indep ({g} : Set (Fin n))) (hag : active (a g))
    (honly : ∀ f, M.Indep ({f} : Set (Fin n)) → active (a f) → f = g)
    (hgm : g ∉ mask r) :
    ∀ e, threshold M active mask r a (e, a e) ↔ e = g := by
  intro e
  constructor
  · intro he
    exact honly e he.2.1 he.2.2.1
  · intro heq
    subst e
    refine ⟨hgm, hg, hag, ?_⟩
    intro f hfm hf haf
    exact False.elim (hgm (honly f hf haf ▸ hfm))

end Maximum
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
namespace Candidates

open Finset Set

variable {n : ℕ}

noncomputable def prefixCount (time : Fin n → ℕ) (I : Finset (Fin n)) (k : ℕ) : ℝ :=
  ((I.filter fun e => time e < k).card : ℝ)

noncomputable def timeCount (time : Fin n → ℕ) (I : Finset (Fin n)) (k : ℕ) : ℝ :=
  ∑ e ∈ I, if time e = k then 1 else 0

lemma sum_timeCount (time : Fin n → ℕ) (I : Finset (Fin n)) (k : ℕ) :
    (∑ i ∈ range k, timeCount time I i) = prefixCount time I k := by
  classical
  unfold timeCount prefixCount
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_range, ← Finset.sum_filter]
  simp

lemma sum_weight_timeCount (time : Fin n → ℕ) (ht : ∀ e, time e < n)
    (I : Finset (Fin n)) (a : ℕ → ℝ) :
    (∑ i ∈ range n, a i * timeCount time I i) = ∑ e ∈ I, a (time e) := by
  classical
  unfold timeCount
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [mul_ite, ht e]

lemma sum_weight_le_of_prefixCount (time : Fin n → ℕ) (ht : ∀ e, time e < n)
    (I J : Finset (Fin n)) (a : ℕ → ℝ)
    (ha : ∀ i < n - 1, a (i + 1) ≤ a i) (hzero : 0 ≤ a (n - 1))
    (hprefix : ∀ k ≤ n, prefixCount time I k ≤ prefixCount time J k) :
    (∑ e ∈ I, a (time e)) ≤ ∑ e ∈ J, a (time e) := by
  rw [← sum_weight_timeCount time ht I a, ← sum_weight_timeCount time ht J a]
  have hi := Finset.sum_range_by_parts a (timeCount time I) n
  have hj := Finset.sum_range_by_parts a (timeCount time J) n
  simp only [smul_eq_mul, sum_timeCount] at hi hj
  rw [hi, hj]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_left (hprefix n le_rfl) hzero
  · apply Finset.sum_le_sum
    intro i hi
    have hin : i < n - 1 := Finset.mem_range.mp hi
    exact mul_le_mul_of_nonpos_left (hprefix (i + 1) (by omega)) (sub_nonpos.mpr (ha i hin))

lemma greedy_univ_prefix_closure (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (time : Fin n → ℕ) (k : ℕ) :
    M.closure {e | time e < k} =
      M.closure {e | e ∈ greedy M time Finset.univ ∧ time e < k} := by
  classical
  have h := Pivots.greedy_prefix_closure M (fun e : Fin n => e) time
    (fun _ => by simp [hE]) k
  simpa [Pivots.keptOccurrences, greedy, prior] using h

lemma prefixCount_le_greedy (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (time : Fin n → ℕ) (ht : Function.Injective time)
    (I : Finset (Fin n)) (hI : M.Indep (I : Set (Fin n))) (k : ℕ) :
    prefixCount time I k ≤ prefixCount time (greedy M time Finset.univ) k := by
  classical
  let G := greedy M time Finset.univ
  let IP := I.filter fun e => time e < k
  let GP := G.filter fun e => time e < k
  have hi : M.Indep (IP : Set (Fin n)) := hI.subset (by
    intro e he
    exact (Finset.mem_filter.mp he).1)
  have hg : M.Indep (GP : Set (Fin n)) :=
    (greedy_indep M time ht Finset.univ (fun _ _ => by simp [hE])).subset (by
      intro e he
      exact (Finset.mem_filter.mp he).1)
  have hsub : (IP : Set (Fin n)) ⊆ M.closure (GP : Set (Fin n)) := by
    intro e he
    have he' := (Finset.mem_filter.mp he).2
    have hc : e ∈ M.closure {e | time e < k} :=
      M.mem_closure_of_mem he' (by simp [hE])
    rw [greedy_univ_prefix_closure M hE time k] at hc
    simpa [GP, G] using hc
  have hcard : (IP : Set (Fin n)).encard ≤ (GP : Set (Fin n)).encard := by
    calc
      _ = M.eRk (IP : Set (Fin n)) := hi.eRk_eq_encard.symm
      _ ≤ M.eRk (M.closure (GP : Set (Fin n))) := M.eRk_mono hsub
      _ = M.eRk (GP : Set (Fin n)) := M.eRk_closure_eq _
      _ = _ := hg.eRk_eq_encard
  have hcNat : IP.card ≤ GP.card := by exact_mod_cast hcard
  change (IP.card : ℝ) ≤ (GP.card : ℝ)
  exact_mod_cast hcNat

noncomputable def orderedWeights (w : Weights n) (order : ArrivalOrder n) (i : ℕ) : ℝ :=
  if hi : i < n then w (order ⟨i, hi⟩) else 0

def priorityTime (order : ArrivalOrder n) (e : Fin n) : ℕ := (order.symm e).val

lemma priorityTime_injective (order : ArrivalOrder n) : Function.Injective (priorityTime order) := by
  intro a b h
  exact order.symm.injective (Fin.ext h)

@[simp] lemma orderedWeights_priorityTime (w : Weights n) (order : ArrivalOrder n) (e : Fin n) :
    orderedWeights w order (priorityTime order e) = w e := by
  simp [orderedWeights, priorityTime]

lemma greedy_dominates_independent (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (order : ArrivalOrder n)
    (hsorted : Antitone (fun i : Fin n => w (order i)))
    (I : Finset (Fin n)) (hI : M.Indep (I : Set (Fin n))) :
    (∑ e ∈ I, w e) ≤ ∑ e ∈ greedy M (priorityTime order) Finset.univ, w e := by
  have ha : ∀ i < n - 1, orderedWeights w order (i + 1) ≤ orderedWeights w order i := by
    intro i hi
    have hi' : i < n := by omega
    have his : i + 1 < n := by omega
    simpa only [orderedWeights, dite_eq_left hi', dite_eq_left his] using
      hsorted (show (⟨i, hi'⟩ : Fin n) ≤ ⟨i + 1, his⟩ from Nat.le_succ i)
  have hn : 0 ≤ orderedWeights w order (n - 1) := by
    unfold orderedWeights
    split_ifs with h
    · exact hw _
    · exact le_rfl
  have h := sum_weight_le_of_prefixCount (priorityTime order) (fun e => (order.symm e).isLt)
    I (greedy M (priorityTime order) Finset.univ) (orderedWeights w order) ha hn
    (fun k _ => prefixCount_le_greedy M hE _ (priorityTime_injective order) I hI k)
  simpa only [orderedWeights_priorityTime] using h

theorem greedy_weight_eq_optimum (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (order : ArrivalOrder n)
    (hsorted : Antitone (fun i : Fin n => w (order i))) :
    (∑ e ∈ greedy M (priorityTime order) Finset.univ, w e) = optimum M w := by
  classical
  apply le_antisymm
  · exact sum_le_optimum M w _ (greedy_indep M _ (priorityTime_injective order)
      Finset.univ (fun _ _ => by simp [hE]))
  · unfold optimum
    apply Finset.sup'_le
    intro I _
    split_ifs with hi
    · exact greedy_dominates_independent M hE w hw order hsorted I hi
    · exact Finset.sum_nonneg fun e _ => hw e

end Candidates
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
lemma levelWeight_mono {B : ℝ} (hB : 1 < B) :
    Monotone (fun a : WithBot ℤ => levelWeight B a) := by
  intro a b hab
  cases a with
  | bot =>
    cases b with
    | bot => exact le_rfl
    | coe j => exact (zpow_pos (zero_lt_one.trans hB) j).le
  | coe i =>
    cases b with
    | bot => exact False.elim (WithBot.not_coe_le_bot i hab)
    | coe j => exact zpow_le_zpow_right₀ hB.le (WithBot.coe_le_coe.mp hab)

namespace Priority

def asLevel (x : Option ℤ) : WithBot ℤ := x

@[simp] lemma asLevel_none : asLevel none = ⊥ := rfl
@[simp] lemma asLevel_some (i : ℤ) : asLevel (some i) = (i : WithBot ℤ) := rfl

open Finset Set

variable {n : ℕ}

def Higher (a : Fin n → Option ℤ) (e f : Fin n) : Prop :=
  Maximum.higher (K := WithBot ℤ) (e, asLevel (a e)) (f, asLevel (a f))

noncomputable def earlier (a : Fin n → Option ℤ) (e : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => Higher a f e

noncomputable def time (a : Fin n → Option ℤ) (e : Fin n) : ℕ := (earlier a e).card

lemma higher_trans (a : Fin n → Option ℤ) {e f g : Fin n}
    (hef : Higher a e f) (hfg : Higher a f g) : Higher a e g :=
  Maximum.higher_trans hef hfg

lemma higher_irrefl (a : Fin n → Option ℤ) (e : Fin n) : ¬ Higher a e e :=
  Maximum.higher_irrefl _

lemma higher_total (a : Fin n → Option ℤ) {e f : Fin n} (hef : e ≠ f) :
    Higher a e f ∨ Higher a f e :=
  Maximum.higher_total (fun h => hef (congrArg Prod.fst h))

lemma time_lt_of_higher (a : Fin n → Option ℤ) {e f : Fin n} (hef : Higher a e f) :
    time a e < time a f := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro g hg
    simp only [earlier, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    exact higher_trans a hg hef
  · intro heq
    have he : e ∈ earlier a f := by simp [earlier, hef]
    rw [← heq] at he
    exact higher_irrefl a e (by simpa [earlier] using he)

lemma time_lt_iff_higher (a : Fin n → Option ℤ) (e f : Fin n) :
    time a e < time a f ↔ Higher a e f := by
  constructor
  · intro h
    by_cases hef : e = f
    · subst f
      exact False.elim (Nat.lt_irrefl _ h)
    · rcases higher_total a hef with hh | hh
      · exact hh
      · exact False.elim ((time_lt_of_higher a hh).not_gt h)
  · exact time_lt_of_higher a

lemma time_injective (a : Fin n → Option ℤ) : Function.Injective (time a) := by
  intro e f h
  by_contra hef
  rcases higher_total a hef with hh | hh
  · have := time_lt_of_higher a hh
    omega
  · have := time_lt_of_higher a hh
    omega

lemma time_lt_card (a : Fin n → Option ℤ) (e : Fin n) : time a e < n := by
  classical
  have hss : earlier a e ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have he : e ∈ earlier a e := heq.symm ▸ Finset.mem_univ e
    exact higher_irrefl a e (by simpa [earlier] using he)
  simpa [time] using Finset.card_lt_card hss

noncomputable def timeEquiv (a : Fin n → Option ℤ) : Fin n ≃ Fin n :=
  Equiv.ofBijective (fun e => ⟨time a e, time_lt_card a e⟩)
    (by
      have hi : Function.Injective (fun e => (⟨time a e, time_lt_card a e⟩ : Fin n)) :=
        fun e f h => time_injective a (congrArg Fin.val h)
      exact ⟨hi, Finite.surjective_of_injective hi⟩)

noncomputable def order (a : Fin n → Option ℤ) : ArrivalOrder n := (timeEquiv a).symm

@[simp] lemma priorityTime_order (a : Fin n → Option ℤ) :
    Candidates.priorityTime (order a) = time a := rfl

lemma main_higher_iff (a : Fin n → Option ℤ) (e f : Fin n) (hf : a f ≠ none) :
    MainAlgorithm.higher e (a e) f (a f) ↔ Higher a e f := by
  cases heq : a e with
  | none => cases hfq : a f <;> simp_all [MainAlgorithm.higher, Higher, Maximum.higher]
  | some i => cases hfq : a f <;> simp_all [MainAlgorithm.higher, Higher, Maximum.higher, eq_comm]

lemma main_higher_iff_time (a : Fin n → Option ℤ) (e f : Fin n) (hf : a f ≠ none) :
    MainAlgorithm.higher e (a e) f (a f) ↔ time a e < time a f :=
  (main_higher_iff a e f hf).trans (time_lt_iff_higher a e f).symm

lemma higher_key_le (a : Fin n → Option ℤ) {e f : Fin n} (h : Higher a e f) :
    asLevel (a f) ≤ asLevel (a e) := by
  rcases h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.symm.le

lemma order_antitone_levelWeight (a : Fin n → Option ℤ) {B : ℝ} (hB : 1 < B) :
    Antitone (fun i => levelWeight B (a (order a i))) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · apply levelWeight_mono hB
    apply higher_key_le a
    apply (time_lt_iff_higher a _ _).1
    have htime (k : Fin n) : time a (order a k) = k.val := by
      have h := congrArg Fin.val ((timeEquiv a).apply_symm_apply k)
      exact h
    simpa only [htime] using (show i.val < j.val from hij)
  · exact le_rfl

lemma rounded_greedy_optimal (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) {B : ℝ} (hB : 1 < B) :
    (∑ e ∈ Candidates.greedy M (time (fun e => roundedLevel B (w e))) Finset.univ,
      roundedWeight B (w e)) = optimum M (fun e => roundedWeight B (w e)) := by
  have h := Candidates.greedy_weight_eq_optimum M hE (fun e => roundedWeight B (w e))
    (fun e => roundedWeight_nonneg (zero_lt_one.trans hB) (w e))
    (order (fun e => roundedLevel B (w e)))
    (order_antitone_levelWeight (fun e => roundedLevel B (w e)) hB)
  simpa only [priorityTime_order] using h

end Priority
end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset Set

variable {n : ℕ}

noncomputable def candidateSet (M : Matroid (Fin n)) (d : MainMasks n)
    (a : Fin n → Option ℤ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun e => candidate M d a e (a e)

noncomputable def candidateLabels (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : Finset (Fin n) := candidateSet M ⟨H, ∅, ∅, ∅, false⟩ a

lemma candidateSet_eq_candidateLabels (M : Matroid (Fin n)) (d : MainMasks n)
    (a : Fin n → Option ℤ) : candidateSet M d a = candidateLabels M a d.H := rfl

lemma candidate_congr_observed (M : Matroid (Fin n)) (d : MainMasks n)
    (a seen : Fin n → Option ℤ) (hseen : ∀ f ∈ d.H, seen f = a f)
    (e : Fin n) (x : Option ℤ) : candidate M d seen e x ↔ candidate M d a e x := by
  have hs : {f | f ∈ d.H ∧ higher f (seen f) e x} =
      {f | f ∈ d.H ∧ higher f (a f) e x} := by
    ext f
    by_cases hf : f ∈ d.H
    · simp [hf, hseen f hf]
    · simp [hf]
  simp only [candidate, hs]

lemma candidateSet_eq_filter (M : Matroid (Fin n)) (d : MainMasks n)
    (a : Fin n → Option ℤ) :
    candidateSet M d a =
      (Candidates.candidates M (Priority.time a) Finset.univ d.H).filter (fun e => a e ≠ none) := by
  classical
  ext e
  by_cases ha : a e = none
  · constructor
    · intro he
      exact False.elim (((Finset.mem_filter.mp he).2).1 ha)
    · intro he
      exact False.elim ((Finset.mem_filter.mp he).2 ha)
  · have hs : {f | f ∈ d.H ∧ higher f (a f) e (a e)} =
        Candidates.prior (Priority.time a) d.H e := by
      ext f
      simp only [Candidates.prior, Set.mem_ofPred_eq, Priority.main_higher_iff_time a f e ha]
    simp [candidateSet, candidate, Candidates.candidates, ha, hs, and_comm, and_left_comm]

lemma sum_candidateLabels (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) (B : ℝ) :
    (∑ e ∈ candidateLabels M a H, levelWeight B (a e)) =
      ∑ e ∈ Candidates.candidates M (Priority.time a) Finset.univ H, levelWeight B (a e) := by
  classical
  rw [candidateLabels, candidateSet_eq_filter]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hnot
  have hz : a e = none := by simpa only [Finset.mem_filter, he, true_and, not_not] using hnot
  simp [hz, levelWeight]

noncomputable def positiveGreedy (M : Matroid (Fin n)) (a : Fin n → Option ℤ) : Finset (Fin n) := by
  classical
  exact (Candidates.greedy M (Priority.time a) Finset.univ).filter fun e => a e ≠ none

lemma positiveGreedy_indep (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (a : Fin n → Option ℤ) : M.Indep (positiveGreedy M a : Set (Fin n)) := by
  apply (Candidates.greedy_indep M (Priority.time a) (Priority.time_injective a)
    Finset.univ (fun e _ => by simp [hE])).subset
  exact Finset.filter_subset _ _

lemma positiveGreedy_survivors_subset (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : positiveGreedy M a \ H ⊆ candidateLabels M a H := by
  classical
  intro e he
  obtain ⟨heG, heH⟩ := Finset.mem_sdiff.mp he
  obtain ⟨heFull, hea⟩ := Finset.mem_filter.mp heG
  have heC := Candidates.greedy_sdiff_subset_candidates M (Priority.time a) Finset.univ H
    (Finset.subset_univ H) (Finset.mem_sdiff.mpr ⟨heFull, heH⟩)
  rw [candidateLabels, candidateSet_eq_filter]
  exact Finset.mem_filter.mpr ⟨heC, hea⟩

lemma sum_positiveGreedy (M : Matroid (Fin n)) (a : Fin n → Option ℤ) (B : ℝ) :
    (∑ e ∈ positiveGreedy M a, levelWeight B (a e)) =
      ∑ e ∈ Candidates.greedy M (Priority.time a) Finset.univ, levelWeight B (a e) := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hnot
  have hz : a e = none := by simpa only [positiveGreedy, Finset.mem_filter, he,
    true_and, not_not] using hnot
  simp [hz, levelWeight]

theorem expectation_positiveGreedy_survivors (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) {B : ℝ} (hB : 1 < B) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ positiveGreedy M (fun e => roundedLevel B (w e)) \ H,
        roundedWeight B (w e)) = optimum M (fun e => roundedWeight B (w e)) / 2 := by
  rw [Candidates.expectation_sdiff_fair Finset.univ _ (Finset.subset_univ _) _]
  rw [show (∑ e ∈ positiveGreedy M (fun e => roundedLevel B (w e)), roundedWeight B (w e)) =
      ∑ e ∈ Candidates.greedy M (Priority.time (fun e => roundedLevel B (w e))) Finset.univ,
        roundedWeight B (w e) from sum_positiveGreedy M _ B]
  rw [Priority.rounded_greedy_optimal M hE w hB]

theorem expectation_candidateLabels_le_optimum (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (B : ℝ) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ candidateLabels M (fun e => roundedLevel B (w e)) H,
        roundedWeight B (w e)) ≤ optimum M (fun e => roundedWeight B (w e)) := by
  have heq : bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ candidateLabels M (fun e => roundedLevel B (w e)) H,
        roundedWeight B (w e)) =
      bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ Candidates.candidates M (Priority.time (fun e => roundedLevel B (w e)))
        Finset.univ H, roundedWeight B (w e)) := by
    apply bitsExpectation_congr
    intro H _
    exact sum_candidateLabels M _ H B
  rw [heq]
  exact Candidates.expectation_candidates_le_optimum M _ (Priority.time_injective _)
    Finset.univ (fun e _ => by simp [hE]) _

lemma candidate_observed_hidden (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (r : Seed (mainSeedBits n)) (e : Fin n) (x : Option ℤ) (B : ℝ) :
    candidate M (mainMasks r)
      (fun f => roundedLevel B (observed (hidden M hE) r w f)) e x ↔
    candidate M (mainMasks r) (fun f => roundedLevel B (w f)) e x := by
  apply candidate_congr_observed
  intro f hf
  have hm : f ∈ (hidden M hE).mask r :=
    Finset.mem_union_left _ (Finset.mem_union_left _ hf)
  simp only [observed, ite_eq_left hm]

lemma positiveGreedy_survivors_indep (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (a : Fin n → Option ℤ) (H : Finset (Fin n)) :
    M.Indep ((positiveGreedy M a \ H : Finset (Fin n)) : Set (Fin n)) :=
  (positiveGreedy_indep M hE a).subset (fun _ he => (Finset.mem_sdiff.mp he).1)

lemma candidate_not_mem_closure_empty (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (e : Fin n) (x : Option ℤ)
    (he : candidate M d seen e x) : e ∉ M.closure ∅ := by
  intro hm
  exact he.2.2 (M.closure_subset_closure (Set.empty_subset _) hm)

lemma candidate_singleton_indep (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (x : Option ℤ)
    (he : candidate M d seen e x) : M.Indep ({e} : Set (Fin n)) := by
  have hn := candidate_not_mem_closure_empty M d seen e x he
  simpa using (M.empty_indep.insert_indep_iff_of_notMem (by simp : e ∉ (∅ : Set (Fin n)))).2
    ⟨by simp [hE], hn⟩

end MatroidProphet.MainAlgorithm

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma sum_groupMask_card_le {ι : Type*} (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (J : Finset ι) (idx : ι → ℕ) (hinj : Set.InjOn idx (J : Set ι))
    (mask target : Finset (Fin n))
    (hsub : ∀ j ∈ J, groupMask M d w mask (idx j) ⊆ (target : Set (Fin n))) :
    (∑ j ∈ J, (groupMask M d w mask (idx j)).ncard) ≤ target.card := by
  classical
  let f : ι → Finset (Fin n) := fun j => (groupMask M d w mask (idx j)).toFinset
  have hf (j : ι) : f j ⊆ pathGroups M d w (idx j) := by
    intro e he
    have hx : e ∈ groupMask M d w mask (idx j) := by simpa [f] using he
    have hg : e ∈ groupMask M d w univ (idx j) := ⟨mem_univ _, hx.2⟩
    simpa [pathGroups] using hg
  have hd : (J : Set ι).PairwiseDisjoint f := by
    intro i hi j hj hij
    have hij' : idx i ≠ idx j := fun heq => hij (hinj hi hj heq)
    exact (pathGroups_disjoint M d w hij').mono (hf i) (hf j)
  have hs : J.biUnion f ⊆ target := by
    intro e he
    obtain ⟨j, hj, hej⟩ := mem_biUnion.mp he
    exact hsub j hj (by simpa [f] using hej)
  have hcard := Finset.card_le_card hs
  rw [card_biUnion hd] at hcard
  simpa only [f, ← Set.ncard_eq_toFinset_card'] using hcard

lemma groupMask_eq_focal (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) {h : ℕ} {i : ℤ}
    (hi : (groups M d w)[h]? = some i) :
    (groupMask M d w mask h).toFinset =
      mask ∩ ((candidateLabels M w d.H).filter (fun e => w e = some i)) := by
  classical
  ext e
  simp only [Set.mem_toFinset, Finset.mem_inter, mem_filter, candidateLabels, candidateSet, Finset.mem_univ, true_and]
  change (e ∈ mask ∧ candidate M d w e (w e) ∧ w e = (groups M d w)[h]?) ↔
    (e ∈ mask ∧ candidate M d w e (w e) ∧ w e = some i)
  simp only [hi]

lemma groupMask_later_subset (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) {h j : ℕ} {i : ℤ}
    (hi : (groups M d w)[h]? = some i) (hj : j < (groups M d w).length) (hhj : h < j) :
    groupMask M d w mask j ⊆
      (mask ∩ ((candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k)) :
        Finset (Fin n)) := by
  intro e he
  have hjget : (groups M d w)[j]? = some ((groups M d w)[j]) := List.getElem?_eq_getElem hj
  obtain ⟨k, hk, hkj⟩ := groups_earlier_key M d w hjget hhj
  have hki : k = i := Option.some.inj (hk.symm.trans hi)
  subst k
  exact Finset.mem_inter.mpr ⟨he.1, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, he.2.1⟩,
    _, he.2.2.trans hjget, hkj⟩⟩

theorem listed_cost_le_true_counts (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) {h : ℕ} {i : ℤ} (hi : (groups M d w)[h]? = some i) (κ : ℕ) :
    κ * (groupMask M d w d.C h).ncard +
      ∑ j ∈ range ((groups M d w).length-(h+1)),
        (κ * (groupMask M d w d.C (h+1+j)).ncard +
          (groupMask M d w d.D (h+1+j)).ncard) ≤
    κ * (d.C ∩ ((candidateLabels M w d.H).filter (fun e => w e = some i))).card +
      κ * (d.C ∩ ((candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k))).card +
        ((candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k)).card := by
  classical
  let J := range ((groups M d w).length-(h+1))
  let high := (candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k)
  have hh := (List.getElem?_eq_some_iff.mp hi).1
  have hc : (∑ j ∈ J, (groupMask M d w d.C (h+1+j)).ncard) ≤ (d.C ∩ high).card := by
    apply sum_groupMask_card_le M d w J (fun j => h+1+j) (by intro a _ b _ hab; change h+1+a = h+1+b at hab; omega)
    intro j hj
    exact groupMask_later_subset M d w d.C hi (by have := mem_range.mp hj; omega) (by omega)
  have hd : (∑ j ∈ J, (groupMask M d w d.D (h+1+j)).ncard) ≤ high.card := by
    apply sum_groupMask_card_le M d w J (fun j => h+1+j) (by intro a _ b _ hab; change h+1+a = h+1+b at hab; omega)
    intro j hj e he
    have hm := groupMask_later_subset M d w d.D hi
      (by have := mem_range.mp hj; omega) (by omega) he
    exact (Finset.mem_inter.mp hm).2
  have hf : (groupMask M d w d.C h).ncard =
      (d.C ∩ ((candidateLabels M w d.H).filter (fun e => w e = some i))).card := by
    rw [Set.ncard_eq_toFinset_card', groupMask_eq_focal M d w d.C hi]
  rw [hf, sum_add_distrib, ← mul_sum]
  have hm := Nat.mul_le_mul_left κ hc
  change _ ≤ _ at hd
  dsimp [J, high] at hm hd
  omega

end MatroidProphet.MainAlgorithm

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet
open Finset Pivots
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

omit [DecidableEq α] in
lemma nominalBirth_eq_iff_departure (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) (b : ℤ) :
    nominalBirth M hE κ D C h d = b ↔
      d ∈ nominalPath M hE κ D C h b ∧ d ∉ nominalPath M hE κ D C h (b-1) := by
  rw [mem_nominal_iff_birth_le M hE κ D C h d hd b,
    mem_nominal_iff_birth_le M hE κ D C h d hd (b-1)]
  omega

omit [DecidableEq α] in
lemma isSafeSample_iff_window (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (U : Set α) (I C T : Finset α)
    (hIU : (I : Set α) ⊆ U) (d : α) (hdI : d ∈ I) (hd : d ∉ M.closure ∅) (parity : Bool) :
    IsSafeSample M hE κ D G h d C T parity ↔
      ∃ b : ParityWindow (activation h) (boolParity parity),
        d ∈ safeLayerSet M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
          (fun i => (T : Set α) ∩ (G i : Set α)) h U (I : Set α) (boolParity parity) b := by
  constructor
  · intro hs
    obtain ⟨hlo, hhi, hp, hex⟩ := hs
    let birth := nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d
    have hbwin : birth ∈ Set.Icc (activation h-2) 1 := by
      change activation h+2 ≤ birth at hlo
      change birth ≤ 0 at hhi
      constructor <;> omega
    have hbpar : birth % 2 = ((boolParity parity).val : ℤ) := by
      rw [boolParity_val]
      exact hp
    refine ⟨⟨⟨birth, hbwin⟩, hbpar⟩, ?_⟩
    have hdep := (nominalBirth_eq_iff_departure M hE κ D _ h d hd birth).mp rfl
    exact ⟨⟨hdI, hIU hdI, hlo, hhi, hdep.1, hdep.2⟩, hex⟩
  · rintro ⟨b, hb⟩
    rcases hb with ⟨⟨_, _, hlo, hhi, hmem, hnot⟩, hex⟩
    have hbirth := (nominalBirth_eq_iff_departure M hE κ D _ h d hd b.val.val).mpr ⟨hmem, hnot⟩
    unfold IsSafeSample
    rw [hbirth]
    have hp := b.property.trans (boolParity_val parity)
    exact ⟨hlo, hhi, hp, hex⟩

theorem safeSampleCount_eq_layerStatistic
    {α : Type u_1} [Fintype α] [DecidableEq α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (U : Set α) (I C T : Finset α)
    (hIU : (I : Set α) ⊆ U) (hIL : ∀ d ∈ I, d ∉ M.closure ∅) (parity : Bool) :
    safeSampleCount M hE κ D G h I C T parity =
      (safeLayerStatistic M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
        (fun i => (T : Set α) ∩ (G i : Set α)) h U (I : Set α) (boolParity parity) : ℝ) := by
  let W := ParityWindow (activation h) (boolParity parity)
  let L : W → Set α := safeLayerSet M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
    (fun i => (T : Set α) ∩ (G i : Set α)) h U (I : Set α) (boolParity parity)
  have hcount (b : W) : (L b).ncard = (I.filter (fun d => d ∈ L b)).card := by
    have hs : L b = ((I.filter (fun d => d ∈ L b) : Finset α) : Set α) := by
      ext d
      constructor
      · intro hd
        exact mem_filter.mpr ⟨hd.1.1, hd⟩
      · intro hd
        exact (mem_filter.mp hd).2
    exact (congrArg Set.ncard hs).trans (Set.ncard_coe_finset _)
  have hlabel (d : α) (hd : d ∈ I) :
      (∑ b : W, if d ∈ L b then (1:ℝ) else 0) = if IsSafeSample M hE κ D G h d C T parity then 1 else 0 := by
    rw [sum_unique_indicators]
    · have he : (∃ b ∈ (univ : Finset W), d ∈ L b) ↔ IsSafeSample M hE κ D G h d C T parity := by
        simp only [mem_univ, true_and]
        exact (isSafeSample_iff_window M hE κ D G h U I C T hIU d hd (hIL d hd) parity).symm
      simp only [he]
    · intro b hb c hc hdb hdc
      by_contra hbc
      have hdisj := nominalLayerSet_disjoint M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
        h U (boolParity parity) hbc
      exact Set.disjoint_left.mp hdisj hdb.1.2 hdc.1.2
  calc
    safeSampleCount M hE κ D G h I C T parity =
        ∑ d ∈ I, if IsSafeSample M hE κ D G h d C T parity then (1:ℝ) else 0 := by
      rw [safeSampleCount_eq_card]
      simp [safeSampleSet]
    _ = ∑ d ∈ I, ∑ b : W, if d ∈ L b then (1:ℝ) else 0 :=
      sum_congr rfl (fun d hd => (hlabel d hd).symm)
    _ = ∑ b : W, ∑ d ∈ I, if d ∈ L b then (1:ℝ) else 0 := sum_comm
    _ = ∑ b : W, ((L b).ncard : ℝ) := by
      apply sum_congr rfl
      intro b hb
      rw [hcount]
      simp
    _ = _ := by simp only [safeLayerStatistic, Nat.cast_sum]; rfl

theorem safeLayerStatistic_lower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (U I : Set α) (hIU : I ⊆ U) (hI : M.Indep I) :
    (((2:ℝ)^12)⁻¹) / 4 * I.ncard - (D h).ncard / (κ:ℝ) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (fun parity => (safeLayerStatistic M hE κ D
          (fun i => (C : Set α) ∩ (G i : Set α)) (fun i => (T : Set α) ∩ (G i : Set α))
          h U I (boolParity parity) : ℝ)))) := by
  let J := I.toFinset
  have hJI : (J : Set α) = I := by simp [J]
  have hJcard : J.card = I.ncard := by rw [← Set.ncard_coe_finset, hJI]
  have hJ : M.Indep (J : Set α) := hJI.symm ▸ hI
  have hJU : (J : Set α) ⊆ U := hJI.symm ▸ hIU
  have hl := safeSampleCount_lower M hE κ hκ D G hG q hq0 hq1 h J hJ
  rw [hJcard] at hl
  have heq : bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      fairParityExpectation (safeSampleCount M hE κ D G h J C T))) =
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (fun parity => (safeLayerStatistic M hE κ D
          (fun i => (C : Set α) ∩ (G i : Set α)) (fun i => (T : Set α) ∩ (G i : Set α))
          h U I (boolParity parity) : ℝ)))) := by
    apply bitsExpectation_congr
    intro C hC
    apply bitsExpectation_congr
    intro T hT
    congr 1
    funext parity
    rw [safeSampleCount_eq_layerStatistic M hE κ D G h U J C T hJU
      (fun d hd => indep_not_loop M J hJ hd) parity, hJI]
  exact hl.trans_eq heq

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def groupGround (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (j : ℕ) : Finset (Fin n) :=
  (groupMask M d s univ j).toFinset

lemma mem_groupGround (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (j : ℕ) (e : Fin n) :
    e ∈ groupGround M d s j ↔ candidate M d s e (s e) ∧ s e = (groups M d s)[j]? := by
  rw [groupGround, Set.mem_toFinset]
  simp [groupMask]

lemma groupGround_disjoint (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) : Pairwise (fun i j => Disjoint (groupGround M d s i) (groupGround M d s j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro e hei hej
  obtain ⟨hc, hei⟩ := (mem_groupGround M d s i e).mp hei
  obtain ⟨_, hej⟩ := (mem_groupGround M d s j e).mp hej
  have hi : i < (groups M d s).length := by
    by_contra hi
    exact hc.1 (hei.trans (List.getElem?_eq_none (by omega)))
  exact hij ((List.getElem?_inj hi (groups_nodup M d s)).mp (hei.symm.trans hej))

lemma groupMask_eq_inter_ground (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (A : Finset (Fin n)) (j : ℕ) :
    groupMask M d s A j = (A : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)) := by
  ext e
  simp only [groupMask, Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_coe, mem_groupGround]

lemma listedSafeStatistic_guards (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (ε : Fin 2) (C T : Finset (Fin n))
    (hi : i ∈ groups M d s) :
    listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y ε =
      safeLayerStatistic M hE κ (groupMask M d s d.D)
        (fun j => (C : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)))
        (fun j => (T : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)))
        ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
        ((d.D : Set (Fin n)) ∩ Y) ε := by
  change (if i ∈ groups M d s then _ else _) = _
  rw [ite_eq_left hi]
  change safeLayerStatistic M hE κ (groupMask M d s d.D)
    (groupMask M d s C) (groupMask M d s T) ((groups M d s).idxOf i)
    (trueGroup M d s i : Set (Fin n)) ((d.D : Set (Fin n)) ∩ Y) ε = _
  congr 1
  · funext j
    exact groupMask_eq_inter_ground M d s C j
  · funext j
    exact groupMask_eq_inter_ground M d s T j

lemma unlisted_density_inter_empty (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (hi : i ∉ groups M d s)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) :
    (d.D : Set (Fin n)) ∩ Y = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro e ⟨heD, heY⟩
  exact hi ((mem_groups M d s i).mpr ((mem_listed_iff M d s i).mpr ⟨e, heD, hY heY⟩))

theorem listedSafeStatistic_fixed_density (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) (hI : M.Indep Y)
    (q : Fin n → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) :
    (((2:ℝ)^12)⁻¹) / 4 * ((d.D : Set (Fin n)) ∩ Y).ncard -
        (trueGroup M d s i).card / (κ:ℝ) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (fun p =>
          (listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y (boolParity p) : ℝ)))) := by
  by_cases hi : i ∈ groups M d s
  · have hsafe := safeLayerStatistic_lower M hE κ hκ (groupMask M d s d.D)
      (groupGround M d s) (groupGround_disjoint M d s) q hq0 hq1
      ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
      ((d.D : Set (Fin n)) ∩ Y) (Set.inter_subset_right.trans hY) (hI.subset Set.inter_subset_right)
    have hcard : (groupMask M d s d.D ((groups M d s).idxOf i)).ncard ≤ (trueGroup M d s i).card := by
      rw [groupMask_at_key M d s d.D _ i (groups_get?_idxOf M d s i hi), Set.ncard_coe_finset]
      exact card_le_card inter_subset_right
    have hdiv : ((groupMask M d s d.D ((groups M d s).idxOf i)).ncard : ℝ) / (κ:ℝ) ≤
        (trueGroup M d s i).card / (κ:ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg κ)
    have heq : bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (fun p =>
          (listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y (boolParity p) : ℝ)))) =
        bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
          fairParityExpectation (fun p => (safeLayerStatistic M hE κ (groupMask M d s d.D)
            (fun j => (C : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)))
            (fun j => (T : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)))
            ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
            ((d.D : Set (Fin n)) ∩ Y) (boolParity p) : ℝ)))) := by
      apply bitsExpectation_congr
      intro C hC
      apply bitsExpectation_congr
      intro T hT
      congr 1
      funext p
      rw [listedSafeStatistic_guards M hE κ d s i Y (boolParity p) C T hi]
    rw [heq]
    exact (sub_le_sub_left hdiv _).trans hsafe
  · have hempty := unlisted_density_inter_empty M d s i hi Y hY
    have hzero (C T : Finset (Fin n)) (p : Bool) :
        listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y (boolParity p) = 0 := by
      change (if i ∈ groups M d s then _ else 0) = 0
      rw [ite_eq_right hi]
    simp only [hempty, Set.ncard_empty, Nat.cast_zero, mul_zero, zero_sub, hzero,
      fairParityExpectation, zero_add, zero_div, bitsExpectation_const]
    exact neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem listedSafeStatistic_lower (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) (hI : M.Indep Y)
    (q : Fin n → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) :
    retainedFraction * Y.ncard - (trueGroup M d s i).card / (κ:ℝ) ≤
      tripleMaskExpectation (fun _ => (1:ℝ)/4) q q univ (fun D C T =>
        fairParityExpectation (fun p =>
          (listedSafeStatistic M hE κ (withMasks d D C T) s i Y (boolParity p) : ℝ))) := by
  have hfixed (D : Finset (Fin n)) :
      (((2:ℝ)^12)⁻¹) / 4 * ((D : Set (Fin n)) ∩ Y).ncard -
          (trueGroup M d s i).card / (κ:ℝ) ≤
        bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
          fairParityExpectation (fun p =>
            (listedSafeStatistic M hE κ (withMasks d D C T) s i Y (boolParity p) : ℝ)))) :=
    listedSafeStatistic_fixed_density M hE κ hκ (withMasks d D ∅ ∅) s i Y hY hI q hq0 hq1
  have hmean := bitsExpectation_mono (fun _ : Fin n => (1:ℝ)/4) (by intro e; norm_num)
    (by intro e; norm_num) univ (fun D _ => hfixed D)
  have hcard : bitsExpectation (fun _ : Fin n => (1:ℝ)/4) univ
      (fun D => (((D : Set (Fin n)) ∩ Y).ncard : ℝ)) = Y.ncard / 4 := by
    have hset (D : Finset (Fin n)) : (D : Set (Fin n)) ∩ Y =
        ((Y.toFinset ∩ D : Finset (Fin n)) : Set (Fin n)) := by
      ext e
      simp only [Set.mem_inter_iff, Finset.mem_coe, mem_inter, Set.mem_toFinset]
      exact and_comm
    simp only [hset, Set.ncard_coe_finset]
    rw [bitsExpectation_card_inter (fun _ : Fin n => (1:ℝ)/4) univ Y.toFinset (subset_univ _)]
    simp only [sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card']
    ring
  have hnum : (((2:ℝ)^12)⁻¹) / 4 / 4 = retainedFraction := by
    norm_num [retainedFraction]
  have heq : bitsExpectation (fun _ : Fin n => (1:ℝ)/4) univ
      (fun D => (((2:ℝ)^12)⁻¹) / 4 * ((D : Set (Fin n)) ∩ Y).ncard -
        (trueGroup M d s i).card / (κ:ℝ)) =
      retainedFraction * Y.ncard - (trueGroup M d s i).card / (κ:ℝ) := by
    simp only [sub_eq_add_neg, bitsExpectation_add, bitsExpectation_mul_const,
      bitsExpectation_const, hcard]
    congr 1
    calc
      (((2:ℝ)^12)⁻¹) / 4 * (Y.ncard / 4) =
        ((((2:ℝ)^12)⁻¹) / 4 / 4) * Y.ncard := by ring
      _ = retainedFraction * Y.ncard := by rw [hnum]
  rw [heq] at hmean
  exact hmean

end MatroidProphet.MainAlgorithm

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}

lemma listedSafe_le_rank_gap (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (ε : Fin 2) :
    (listedSafeStatistic M hE κ d s i Y ε : ℝ) ≤
      (κ : ℝ) * listedRankStatistic M hE κ d s i ε + listedTransferGap M hE κ d s i Y ε := by
  unfold listedTransferGap
  have hh := le_max_left ((listedSafeStatistic M hE κ d s i Y ε : ℝ) -
    (κ : ℝ) * listedRankStatistic M hE κ d s i ε) 0
  linarith

theorem listedRankStatistic_lower (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
    (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) (hI : M.Indep Y)
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) :
    (retainedFraction * Y.ncard - ((2:ℝ)^23)⁻¹ * (trueGroup M d s i).card) / densityThreshold ≤
      tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
        univ (fun D C T => fairParityExpectation (fun p =>
          (listedRankStatistic M hE (2^100) (withMasks d D C T) s i (boolParity p) : ℝ))) := by
  have ht0 : 0 ≤ thinningRate := constants_positive.2.2.1.le
  have ht1 : thinningRate ≤ 1 := by norm_num [thinningRate]
  have hsafe := listedSafeStatistic_lower M hE (2^100) (by positivity) d s i Y hY hI
    (fun _ => thinningRate) (fun _ => ht0) (fun _ => ht1)
  have herr := listedTransferGap_parity_expectation_le M hE d s i Y hY hn
  have hkcast : ((2^100 : ℕ) : ℝ) = densityThreshold := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, densityThreshold]
  rw [hkcast] at hsafe
  have hdet (D C T : Finset (Fin n)) :
      fairParityExpectation (fun p => (listedSafeStatistic M hE (2^100)
        (withMasks d D C T) s i Y (boolParity p) : ℝ)) ≤
      densityThreshold * fairParityExpectation (fun p => (listedRankStatistic M hE (2^100)
        (withMasks d D C T) s i (boolParity p) : ℝ)) +
      fairParityExpectation (fun p => listedTransferGap M hE (2^100)
        (withMasks d D C T) s i Y (boolParity p)) := by
    have h0 := listedSafe_le_rank_gap M hE (2^100) (withMasks d D C T) s i Y (boolParity false)
    have h1 := listedSafe_le_rank_gap M hE (2^100) (withMasks d D C T) s i Y (boolParity true)
    rw [hkcast] at h0 h1
    dsimp only [fairParityExpectation]
    calc
      _ ≤ _ := div_le_div_of_nonneg_right (add_le_add h0 h1) (by norm_num : (0:ℝ) ≤ 2)
      _ = _ := by ring
  have hmean := tripleMaskExpectation_mono (fun _ : Fin n => (1:ℝ)/4)
    (fun _ => thinningRate) (fun _ => thinningRate) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => ht0) (fun _ => ht1) (fun _ => ht0) (fun _ => ht1) univ
    (fun D _ C _ T _ => hdet D C T)
  rw [tripleMaskExpectation_add, tripleMaskExpectation_mul] at hmean
  have hc := mul_le_mul_of_nonneg_right residual_error_constant
    (Nat.cast_nonneg (trueGroup M d s i).card)
  apply (div_le_iff₀ constants_positive.2.1).2
  rw [div_eq_mul_inv] at hsafe
  nlinarith

end MatroidProphet.MainAlgorithm

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma trueGroup_eq_candidate_filter (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) :
    trueGroup M d w i = (candidateLabels M w d.H).filter (fun e => w e = some i) := by
  unfold trueGroup candidateLabels candidateSet
  ext e
  simp only [mem_filter, mem_univ, true_and]
  rfl

noncomputable def higherTrueGroups (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) : Finset (Fin n) :=
  (candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k)

lemma trueZ_eq_listedRankStatistic (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) :
    trueZ M hE d w i = listedRankStatistic M hE (2^100) d w i (boolParity d.odd) := by
  unfold trueZ listedRankStatistic
  split_ifs with hi
  · unfold listedZ
    rw [groupMask_at_key M d w univ _ i (groups_get?_idxOf M d w i hi), univ_inter]
  · rfl

lemma mainMean_trueZ (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) :
    mainMean d (fun d' => (trueZ M hE d' w i : ℝ)) =
      tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
        univ (fun D C T => fairParityExpectation (fun p =>
          (listedRankStatistic M hE (2^100) (withMasks d D C T) w i (boolParity p) : ℝ))) := by
  unfold mainMean
  apply tripleMaskExpectation_congr
  intro D hD C hC T hT
  congr 1
  funext p
  dsimp only
  rw [trueZ_eq_listedRankStatistic]
  rfl

theorem mainMean_trueZ_lower (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d w i : Set (Fin n))) (hI : M.Indep Y)
    (hn : densityThreshold ≤ ((trueGroup M d w i).card : ℝ)) :
    (retainedFraction * Y.ncard - ((2:ℝ)^23)⁻¹ * (trueGroup M d w i).card) / densityThreshold ≤
      mainMean d (fun d' => (trueZ M hE d' w i : ℝ)) := by
  rw [mainMean_trueZ]
  exact listedRankStatistic_lower M hE d w i Y hY hI hn

lemma true_expected_nominal_to_final (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    densityThreshold * t * bitsExpectation (fun _ : Fin n => t) univ (fun T =>
      (trueZ M hE {d with T := T} w i : ℝ)) ≤
    densityThreshold * bitsExpectation (fun _ : Fin n => t) univ (fun T =>
      (trueLambda M hE {d with T := T} w i : ℝ)) +
      t * (densityThreshold * (d.C ∩ trueGroup M d w i).card +
        densityThreshold * (d.C ∩ higherTrueGroups M d w i).card +
          (higherTrueGroups M d w i).card) := by
  by_cases hi : i ∈ groups M d w
  · have hh : (groups M d w).idxOf i < (groups M d w).length := List.idxOf_lt_length_of_mem hi
    have hl := listed_expected_nominal_to_final M hE d w _ hh t ht0 ht1
    have hc := listed_cost_le_true_counts M d w (groups_get?_idxOf M d w i hi) (2^100)
    rw [← trueGroup_eq_candidate_filter M d w i] at hc
    have hc' : (((2^100) * (groupMask M d w d.C ((groups M d w).idxOf i)).ncard +
        ∑ j ∈ range ((groups M d w).length-((groups M d w).idxOf i+1)),
          ((2^100) * (groupMask M d w d.C ((groups M d w).idxOf i+1+j)).ncard +
            (groupMask M d w d.D ((groups M d w).idxOf i+1+j)).ncard) : ℕ) : ℝ) ≤
        densityThreshold * (d.C ∩ trueGroup M d w i).card +
          densityThreshold * (d.C ∩ higherTrueGroups M d w i).card +
            (higherTrueGroups M d w i).card := by
      calc
        _ ≤ (((2^100) * (d.C ∩ trueGroup M d w i).card +
          (2^100) * (d.C ∩ higherTrueGroups M d w i).card +
          (higherTrueGroups M d w i).card : ℕ) : ℝ) := by exact_mod_cast hc
        _ = _ := by norm_num [densityThreshold]
    have hz (T : Finset (Fin n)) : trueZ M hE {d with T := T} w i =
        listedZ M hE {d with T := T} w ((groups M d w).idxOf i) := by
      change (if i ∈ groups M d w then _ else 0) = _
      rw [ite_eq_left hi]
      rfl
    have hLam (T : Finset (Fin n)) : trueLambda M hE {d with T := T} w i =
        listedLambda M hE {d with T := T} w ((groups M d w).idxOf i) := by
      change (if i ∈ groups M d w then _ else 0) = _
      rw [ite_eq_left hi]
      rfl
    simp only [hz, hLam]
    exact hl.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc' ht0))
  · have hz (T : Finset (Fin n)) : trueZ M hE {d with T := T} w i = 0 := by
      change (if i ∈ groups M d w then _ else 0) = _
      rw [ite_eq_right hi]
    have hLam (T : Finset (Fin n)) : trueLambda M hE {d with T := T} w i = 0 := by
      change (if i ∈ groups M d w then _ else 0) = _
      rw [ite_eq_right hi]
    simp only [hz, hLam, Nat.cast_zero, bitsExpectation_const, mul_zero, zero_add]
    apply mul_nonneg ht0
    exact add_nonneg (add_nonneg
      (mul_nonneg constants_positive.2.1.le (Nat.cast_nonneg _))
      (mul_nonneg constants_positive.2.1.le (Nat.cast_nonneg _))) (Nat.cast_nonneg _)

lemma trueGroup_eq_of_H_eq (M : Matroid (Fin n)) (d d' : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) (hH : d'.H = d.H) :
    trueGroup M d' w i = trueGroup M d w i := by
  rw [trueGroup_eq_candidate_filter, trueGroup_eq_candidate_filter, hH]

lemma higherTrueGroups_eq_of_H_eq (M : Matroid (Fin n)) (d d' : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) (hH : d'.H = d.H) :
    higherTrueGroups M d' w i = higherTrueGroups M d w i := by
  simp only [higherTrueGroups, hH]

lemma mainMean_resample_test (d : MainMasks n) (f : MainMasks n → ℝ) :
    mainMean d (fun d' => bitsExpectation (fun _ : Fin n => thinningRate) univ
      (fun T => f {d' with T := T})) = mainMean d f := by
  unfold mainMean tripleMaskExpectation
  apply bitsExpectation_congr
  intro D hD
  apply bitsExpectation_congr
  intro C hC
  change bitsExpectation (fun _ : Fin n => thinningRate) univ (fun _ =>
      fairParityExpectation (fun p => bitsExpectation (fun _ : Fin n => thinningRate) univ
        (fun T => f {withMasks d D C T with odd := p}))) = _
  rw [bitsExpectation_const, ← bitsExpectation_fairParity]

theorem mainMean_nominal_to_final (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) :
    densityThreshold * thinningRate * mainMean d (fun d' => (trueZ M hE d' w i : ℝ)) ≤
      densityThreshold * mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)) +
        thinningRate * (densityThreshold * thinningRate * (trueGroup M d w i).card +
          densityThreshold * thinningRate * (higherTrueGroups M d w i).card +
            (higherTrueGroups M d w i).card) := by
  have hmean : mainMean d (fun d' => densityThreshold * thinningRate *
      bitsExpectation (fun _ : Fin n => thinningRate) univ (fun T =>
        (trueZ M hE {d' with T := T} w i : ℝ))) ≤
      mainMean d (fun d' => densityThreshold *
        bitsExpectation (fun _ : Fin n => thinningRate) univ (fun T =>
          (trueLambda M hE {d' with T := T} w i : ℝ)) +
        thinningRate * (densityThreshold * (d'.C ∩ trueGroup M d w i).card +
          densityThreshold * (d'.C ∩ higherTrueGroups M d w i).card +
            (higherTrueGroups M d w i).card)) := by
    apply mainMean_mono
    intro d' hH
    have hp := true_expected_nominal_to_final M hE d' w i thinningRate
      constants_positive.2.2.1.le (by norm_num [thinningRate])
    rwa [trueGroup_eq_of_H_eq M d d' w i hH,
      higherTrueGroups_eq_of_H_eq M d d' w i hH] at hp
  simp only [mainMean_add, mainMean_mul, mainMean_const, mainMean_guard_count] at hmean
  rw [mainMean_resample_test d (fun d' => (trueZ M hE d' w i : ℝ)),
    mainMean_resample_test d (fun d' => (trueLambda M hE d' w i : ℝ))] at hmean
  simpa only [mul_assoc] using hmean

theorem true_group_payoff (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d w i : Set (Fin n))) (hI : M.Indep Y)
    (hn : densityThreshold ≤ ((trueGroup M d w i).card : ℝ)) :
    thinningRate / densityThreshold *
        (retainedFraction * Y.ncard -
          (((2:ℝ)^23)⁻¹ + thinningRate * densityThreshold) * (trueGroup M d w i).card -
          (1 + thinningRate * densityThreshold) * (higherTrueGroups M d w i).card) ≤
      mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)) := by
  have hZ := mainMean_trueZ_lower M hE d w i Y hY hI hn
  have hcost := mainMean_nominal_to_final M hE d w i
  have hk : 0 < densityThreshold := constants_positive.2.1
  have ht : 0 ≤ thinningRate := constants_positive.2.2.1.le
  have hmul := mul_le_mul_of_nonneg_left hZ (mul_nonneg hk.le ht)
  have hcancel : densityThreshold * thinningRate *
      ((retainedFraction * Y.ncard - ((2:ℝ)^23)⁻¹ * (trueGroup M d w i).card) / densityThreshold) =
      thinningRate * (retainedFraction * Y.ncard - ((2:ℝ)^23)⁻¹ * (trueGroup M d w i).card) := by
    field_simp
  rw [hcancel] at hmul
  have hboth := hmul.trans hcost
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hk).mpr
  nlinarith [hboth]

end MatroidProphet.MainAlgorithm

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open Finset

variable {n : ℕ}

noncomputable def weightLevels (a : Fin n → Option ℤ) (U : Finset (Fin n)) : Finset ℤ :=
  U.biUnion fun e => (a e).toFinset

lemma mem_weightLevels (a : Fin n → Option ℤ) (U : Finset (Fin n)) (i : ℤ) :
    i ∈ weightLevels a U ↔ ∃ e ∈ U, a e = some i := by
  classical
  simp [weightLevels]

lemma sum_weightGroups (a : Fin n → Option ℤ) (U : Finset (Fin n))
    (levels : Finset ℤ) (hlevels : weightLevels a U ⊆ levels)
    (f : ℤ → ℝ) :
    (∑ i ∈ levels, f i * ((U.filter fun e => a e = some i).card : ℝ)) =
      ∑ e ∈ U, (a e).elim 0 f := by
  classical
  have heq (i : ℤ) : f i * ((U.filter fun e => a e = some i).card : ℝ) =
      ∑ e ∈ U, if a e = some i then f i else 0 := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  simp_rw [heq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  cases ha : a e with
  | none => simp
  | some i =>
    have hi : i ∈ levels := hlevels ((mem_weightLevels a U i).2 ⟨e, he, ha⟩)
    simp [hi]

lemma sum_weightGroups_mass (a : Fin n → Option ℤ) (U : Finset (Fin n))
    (levels : Finset ℤ) (hlevels : weightLevels a U ⊆ levels) (B : ℝ) :
    (∑ i ∈ levels, B ^ i * ((U.filter fun e => a e = some i).card : ℝ)) =
      ∑ e ∈ U, levelWeight B (a e) := by
  rw [sum_weightGroups a U levels hlevels]
  apply Finset.sum_congr rfl
  intro e _
  cases a e <;> rfl

lemma highGroup_card (a : Fin n → Option ℤ) (U : Finset (Fin n))
    (levels : Finset ℤ) (hlevels : weightLevels a U ⊆ levels) (i : ℤ) :
    (((U.filter fun e => ∃ j, a e = some j ∧ i < j).card) : ℝ) =
      ∑ j ∈ levels with i < j, ((U.filter fun e => a e = some j).card : ℝ) := by
  classical
  have hs := sum_weightGroups a U levels hlevels (fun j => if i < j then 1 else 0)
  rw [Finset.sum_filter]
  have hleft : (∑ j ∈ levels, (if i < j then 1 else 0) *
      ((U.filter fun e => a e = some j).card : ℝ)) =
      ∑ j ∈ levels, if i < j then ((U.filter fun e => a e = some j).card : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hleft] at hs
  rw [hs]
  have hcount : (((U.filter fun e => ∃ j, a e = some j ∧ i < j).card) : ℝ) =
      ∑ e ∈ U, if (∃ j, a e = some j ∧ i < j) then 1 else 0 := by simp
  rw [hcount]
  apply Finset.sum_congr rfl
  intro e _
  cases a e <;> simp

lemma weightLevels_mono (a : Fin n → Option ℤ) {U V : Finset (Fin n)} (h : U ⊆ V) :
    weightLevels a U ⊆ weightLevels a V := by
  intro i hi
  obtain ⟨e, he, hi⟩ := (mem_weightLevels a U i).1 hi
  exact (mem_weightLevels a V i).2 ⟨e, h he, hi⟩

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open Finset

lemma weighted_group_payoff (B t κ γ a b ε : ℝ)
    (hB : 1 < B) (ht : 0 ≤ t) (hκ : 0 < κ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (herr : a + b / (B - 1) ≤ ε)
    (levels analyzed : Finset ℤ) (hsub : analyzed ⊆ levels)
    (N Y Λ : ℤ → ℝ) (hN : ∀ i ∈ levels, 0 ≤ N i)
    (hgroup : ∀ i ∈ analyzed,
      t / κ * (γ * Y i - a * N i - b * ∑ l ∈ levels with i < l, N l) ≤ Λ i) :
    t / (2 * κ) * (γ * ∑ i ∈ analyzed, B ^ i * Y i - ε * ∑ i ∈ levels, B ^ i * N i) ≤
      (1 / 2 : ℝ) * ∑ i ∈ analyzed, B ^ i * Λ i := by
  have hB0 : 0 < B := zero_lt_one.trans hB
  have htotal : 0 ≤ ∑ i ∈ levels, B ^ i * N i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (zpow_pos hB0 i).le (hN i hi)
  have hNsum : (∑ i ∈ analyzed, B ^ i * N i) ≤ ∑ i ∈ levels, B ^ i * N i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ =>
      mul_nonneg (zpow_pos hB0 i).le (hN i hi))
  have hcost := higher_weight_cost B hB levels analyzed N hN
  have herrors : a * (∑ i ∈ analyzed, B ^ i * N i) +
      b * (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, N l) ≤
      ε * ∑ i ∈ levels, B ^ i * N i := by
    calc
      _ ≤ a * (∑ i ∈ levels, B ^ i * N i) +
          b * ((∑ i ∈ levels, B ^ i * N i) / (B - 1)) :=
        add_le_add (mul_le_mul_of_nonneg_left hNsum ha) (mul_le_mul_of_nonneg_left hcost hb)
      _ = (a + b / (B - 1)) * ∑ i ∈ levels, B ^ i * N i := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right herr htotal
  have hsum : (∑ i ∈ analyzed,
      B ^ i * (t / κ * (γ * Y i - a * N i - b * ∑ l ∈ levels with i < l, N l))) ≤
      ∑ i ∈ analyzed, B ^ i * Λ i :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hgroup i hi) (zpow_pos hB0 i).le
  have heq : (∑ i ∈ analyzed,
      B ^ i * (t / κ * (γ * Y i - a * N i - b * ∑ l ∈ levels with i < l, N l))) =
      t / κ * (γ * (∑ i ∈ analyzed, B ^ i * Y i) -
        (a * (∑ i ∈ analyzed, B ^ i * N i) +
          b * (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, N l))) := by
    have hi (i : ℤ) : B ^ i * (t / κ * (γ * Y i - a * N i -
        b * ∑ l ∈ levels with i < l, N l)) =
        (t / κ * γ) * (B ^ i * Y i) - (t / κ * a) * (B ^ i * N i) -
          (t / κ * b) * (B ^ i * ∑ l ∈ levels with i < l, N l) := by ring
    simp_rw [hi]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [heq] at hsum
  have hbudget := mul_le_mul_of_nonneg_left
    (sub_le_sub_left herrors (γ * ∑ i ∈ analyzed, B ^ i * Y i)) (div_nonneg ht hκ.le)
  have hresult := hbudget.trans hsum
  calc
    _ = (1 / 2 : ℝ) * (t / κ *
        (γ * ∑ i ∈ analyzed, B ^ i * Y i - ε * ∑ i ∈ levels, B ^ i * N i)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hresult (by norm_num)

lemma source_weighted_group_payoff (levels analyzed : Finset ℤ) (hsub : analyzed ⊆ levels)
    (N Y Λ : ℤ → ℝ) (hN : ∀ i ∈ levels, 0 ≤ N i)
    (hgroup : ∀ i ∈ analyzed,
      thinningRate / densityThreshold *
        (retainedFraction * Y i - (((2 : ℝ) ^ 23)⁻¹ + thinningRate * densityThreshold) * N i -
          (1 + thinningRate * densityThreshold) * ∑ l ∈ levels with i < l, N l) ≤ Λ i) :
    thinningRate / (2 * densityThreshold) *
      (retainedFraction * ∑ i ∈ analyzed, weightBase ^ i * Y i -
        ((2 : ℝ) ^ 21)⁻¹ * ∑ i ∈ levels, weightBase ^ i * N i) ≤
      (1 / 2 : ℝ) * ∑ i ∈ analyzed, weightBase ^ i * Λ i := by
  apply weighted_group_payoff weightBase thinningRate densityThreshold retainedFraction
    (((2 : ℝ) ^ 23)⁻¹ + thinningRate * densityThreshold) (1 + thinningRate * densityThreshold)
    (((2 : ℝ) ^ 21)⁻¹) (by norm_num [weightBase])
    constants_positive.2.2.1.le constants_positive.2.1
  · norm_num [thinningRate, densityThreshold]
  · norm_num [thinningRate, densityThreshold]
  · exact error_constant.le
  · exact hsub
  · exact hN
  · exact hgroup

lemma sum_zpow_le_two_of_bound (B : ℝ) (hB : 2 ≤ B) (levels : Finset ℤ)
    (m : ℝ) (hm : 0 ≤ m) (hbound : ∀ i ∈ levels, B ^ i ≤ m) :
    (∑ i ∈ levels, B ^ i) ≤ 2 * m := by
  classical
  by_cases hn : levels.Nonempty
  · have h := sum_zpow_le_two B hB levels (levels.max' hn)
      (fun i hi => levels.le_max' i hi)
    exact h.trans (mul_le_mul_of_nonneg_left (hbound _ (levels.max'_mem hn)) (by norm_num))
  · have he : levels = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty]
    positivity

lemma small_group_mass_bound (B κ m : ℝ) (hB : 2 ≤ B) (hκ : 0 ≤ κ) (hm : 0 ≤ m)
    (levels : Finset ℤ) (Y : ℤ → ℝ) (hY : ∀ i ∈ levels, Y i ≤ κ)
    (hbound : ∀ i ∈ levels, B ^ i ≤ m) :
    (∑ i ∈ levels, B ^ i * Y i) ≤ 2 * κ * m := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  calc
    _ ≤ ∑ i ∈ levels, B ^ i * κ :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hY i hi) (zpow_pos hB0 i).le
    _ = κ * ∑ i ∈ levels, B ^ i := by rw [← Finset.sum_mul]; ring
    _ ≤ κ * (2 * m) := mul_le_mul_of_nonneg_left
      (sum_zpow_le_two_of_bound B hB levels m hm hbound) hκ
    _ = _ := by ring

lemma bitsExpectation_sub {α : Type*} [DecidableEq α] (q : α → ℝ) (V : Finset α)
    (f g : Finset α → ℝ) :
    bitsExpectation q V (fun H => f H - g H) = bitsExpectation q V f - bitsExpectation q V g := by
  simp only [bitsExpectation, mul_sub, Finset.sum_sub_distrib]

lemma main_branch_from_filter {α : Type*} [DecidableEq α] (V : Finset α)
    (bigY allY massU payoff : Finset α → ℝ) (W m : ℝ)
    (hW : 0 ≤ W) (hm : m ≤ W / (8 * densityThreshold))
    (hY : bitsExpectation (fun _ => (1 / 2 : ℝ)) V allY = W / 2)
    (hU : bitsExpectation (fun _ => (1 / 2 : ℝ)) V massU ≤ W)
    (hsmall : ∀ H ⊆ V, allY H ≤ bigY H + 2 * densityThreshold * m)
    (hpay : ∀ H ⊆ V, thinningRate / (2 * densityThreshold) *
      (retainedFraction * bigY H - ((2 : ℝ) ^ 21)⁻¹ * massU H) ≤ payoff H) :
    thinningRate * retainedFraction / (16 * densityThreshold) * W ≤
      bitsExpectation (fun _ => (1 / 2 : ℝ)) V payoff := by
  let q : α → ℝ := fun _ => 1 / 2
  have hq0 : ∀ e, 0 ≤ q e := fun _ => by norm_num [q]
  have hq1 : ∀ e, q e ≤ 1 := fun _ => by norm_num [q]
  have hybig := bitsExpectation_mono q hq0 hq1 V hsmall
  rw [bitsExpectation_add, bitsExpectation_const, hY] at hybig
  have hbig : W / 4 ≤ bitsExpectation q V bigY := by
    have hk : 0 < densityThreshold := constants_positive.2.1
    have hmul := (le_div_iff₀ (by positivity : 0 < 8 * densityThreshold)).mp hm
    nlinarith
  have hpaid := bitsExpectation_mono q hq0 hq1 V hpay
  rw [bitsExpectation_mul_const, bitsExpectation_sub,
    bitsExpectation_mul_const, bitsExpectation_mul_const] at hpaid
  have hinner : retainedFraction / 8 * W ≤
      retainedFraction * bitsExpectation q V bigY -
        ((2 : ℝ) ^ 21)⁻¹ * bitsExpectation q V massU := by
    have hγ := constants_positive.2.2.2.2
    have h1 := mul_le_mul_of_nonneg_left hbig hγ.le
    have h2 := mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ ((2 : ℝ) ^ 21)⁻¹)
    have h3 := mul_le_mul_of_nonneg_right retained_fraction_slack hW
    nlinarith
  have hscale : 0 ≤ thinningRate / (2 * densityThreshold) :=
    div_nonneg constants_positive.2.2.1.le
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) constants_positive.2.1.le)
  have hscaled := mul_le_mul_of_nonneg_left hinner hscale
  have hfinal := hscaled.trans hpaid
  have he : thinningRate / (2 * densityThreshold) * (retainedFraction / 8 * W) =
      thinningRate * retainedFraction / (16 * densityThreshold) * W := by ring
  rw [he] at hfinal
  exact hfinal

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.Maximum

open Finset

variable {n : ℕ}

lemma expectation_mem (q : Fin n → ℝ) (V : Finset (Fin n))
    (e : Fin n) (he : e ∈ V) (c : ℝ) :
    bitsExpectation q V (fun H => if e ∈ H then c else 0) = q e * c := by
  have hno : bitsExpectation q (V.erase e) (fun H => if e ∈ H then c else 0) = 0 := by
    calc
      _ = bitsExpectation q (V.erase e) (fun _ => 0) := by
        apply bitsExpectation_congr
        intro H hH
        have heH : e ∉ H := fun hh => (Finset.mem_erase.mp (hH hh)).1 rfl
        simp [heH]
      _ = 0 := bitsExpectation_const q _ 0
  have hyes : bitsExpectation q (V.erase e) (fun H => if e ∈ insert e H then c else 0) = c := by
    simp only [Finset.mem_insert_self, ite_true]
    exact bitsExpectation_const q _ c
  calc
    _ = bitsExpectation q (insert e (V.erase e)) (fun H => if e ∈ H then c else 0) := by
      rw [Finset.insert_erase he]
    _ = q e * c := by
      rw [bitsExpectation_insert q _ e (by simp), hno, hyes]
      ring

lemma expectation_top_two_event (V : Finset (Fin n)) (g h : Fin n)
    (hg : g ∈ V) (hh : h ∈ V) (hgh : g ≠ h) (c : ℝ) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) V
      (fun H => if g ∈ H then 0 else if h ∈ H then c else 0) = c / 4 := by
  let q : Fin n → ℝ := fun _ => 1 / 2
  have hno : bitsExpectation q (V.erase g)
      (fun H => if g ∈ H then 0 else if h ∈ H then c else 0) = (1 / 2 : ℝ) * c := by
    calc
      _ = bitsExpectation q (V.erase g) (fun H => if h ∈ H then c else 0) := by
        apply bitsExpectation_congr
        intro H hH
        have hgH : g ∉ H := fun hm => (Finset.mem_erase.mp (hH hm)).1 rfl
        simp [hgH]
      _ = _ := expectation_mem q (V.erase g) h (Finset.mem_erase.mpr ⟨hgh.symm, hh⟩) c
  have hyes : bitsExpectation q (V.erase g)
      (fun H => if g ∈ insert g H then 0 else if h ∈ insert g H then c else 0) = 0 := by
    simp only [Finset.mem_insert_self, ite_true]
    exact bitsExpectation_const q _ 0
  change bitsExpectation q V _ = _
  conv_lhs => rw [← Finset.insert_erase hg]
  rw [bitsExpectation_insert q _ g (by simp), hno, hyes]
  dsimp [q]
  ring

theorem maximum_expectation_two (V : Finset (Fin n)) (g h : Fin n)
    (hg : g ∈ V) (hh : h ∈ V) (hgh : g ≠ h)
    (F : Finset (Fin n) → ℝ) (c : ℝ)
    (hF : ∀ H ⊆ V, 0 ≤ F H)
    (hsuccess : ∀ H ⊆ V, g ∉ H → h ∈ H → c ≤ F H) :
    c / 4 ≤ bitsExpectation (fun _ => (1 / 2 : ℝ)) V F := by
  rw [← expectation_top_two_event V g h hg hh hgh c]
  apply bitsExpectation_mono _ (fun _ => by norm_num) (fun _ => by norm_num)
  intro H hH
  split_ifs with hgH hhH
  · exact hF H hH
  · exact hsuccess H hH hgH hhH
  · exact hF H hH

theorem maximum_expectation_one (V : Finset (Fin n)) (g : Fin n) (hg : g ∈ V)
    (F : Finset (Fin n) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hF : ∀ H ⊆ V, 0 ≤ F H)
    (hsuccess : ∀ H ⊆ V, g ∉ H → c ≤ F H) :
    c / 4 ≤ bitsExpectation (fun _ => (1 / 2 : ℝ)) V F := by
  have hhalf : c / 2 ≤ bitsExpectation (fun _ => (1 / 2 : ℝ)) V F := by
    have hevent := Candidates.expectation_not_mem (fun _ => (1 / 2 : ℝ)) V g hg c
    have hevent' : bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => if g ∉ H then c else 0) = c / 2 := by
      rw [hevent]
      ring
    rw [← hevent']
    apply bitsExpectation_mono _ (fun _ => by norm_num) (fun _ => by norm_num)
    intro H hH
    by_cases hgH : g ∈ H
    · simpa only [hgH, not_true_eq_false, ite_false] using hF H hH
    · simpa only [hgH, not_false_eq_true, ite_true] using hsuccess H hH hgH
  linarith

end MatroidProphet.Maximum

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

noncomputable def seedSet {bits : ℕ} (r : Seed bits) : Finset (Fin bits) :=
  Finset.univ.filter fun e => r e = true

noncomputable def setSeed {bits : ℕ} (S : Finset (Fin bits)) : Seed bits :=
  fun e => decide (e ∈ S)

@[simp] lemma seedSet_setSeed {bits : ℕ} (S : Finset (Fin bits)) : seedSet (setSeed S) = S := by
  classical
  ext e
  simp [seedSet, setSeed]

@[simp] lemma setSeed_seedSet {bits : ℕ} (r : Seed bits) : setSeed (seedSet r) = r := by
  funext e
  simp [seedSet, setSeed]

noncomputable def seedFinsetEquiv (bits : ℕ) : Seed bits ≃ Finset (Fin bits) where
  toFun := seedSet
  invFun := setSeed
  left_inv := setSeed_seedSet
  right_inv := seedSet_setSeed

lemma seedWeight_sum {bits : ℕ} (q : Fin bits → ℝ) :
    (∑ r : Seed bits, bitsWeight q Finset.univ (seedSet r)) = 1 := by
  classical
  have h := (seedFinsetEquiv bits).sum_comp (bitsWeight q Finset.univ)
  change (∑ r, bitsWeight q Finset.univ ((seedFinsetEquiv bits) r)) = 1
  rw [h]
  simpa only [bitsExpectation, Finset.powerset_univ, mul_one] using
    bitsExpectation_one q Finset.univ

noncomputable def seedPMF {bits : ℕ} (q : Fin bits → ℝ)
    (h0 : ∀ e, 0 ≤ q e) (h1 : ∀ e, q e ≤ 1) : PMF (Seed bits) :=
  PMF.ofFintype (fun r => ENNReal.ofReal (bitsWeight q Finset.univ (seedSet r))) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => bitsWeight_nonneg q h0 h1 _ _),
      seedWeight_sum, ENNReal.ofReal_one])

noncomputable def bernoulliSeedLaw {bits : ℕ} (q : Fin bits → ℝ)
    (h0 : ∀ e, 0 ≤ q e) (h1 : ∀ e, q e ≤ 1) : Measure (Seed bits) :=
  (seedPMF q h0 h1).toMeasure

instance bernoulliSeedLaw_probability {bits : ℕ} (q : Fin bits → ℝ)
    (h0 : ∀ e, 0 ≤ q e) (h1 : ∀ e, q e ≤ 1) :
    IsProbabilityMeasure (bernoulliSeedLaw q h0 h1) := by
  unfold bernoulliSeedLaw
  infer_instance

theorem integral_bernoulliSeedLaw {bits : ℕ} (q : Fin bits → ℝ)
    (h0 : ∀ e, 0 ≤ q e) (h1 : ∀ e, q e ≤ 1) (f : Seed bits → ℝ) :
    (∫ r, f r ∂bernoulliSeedLaw q h0 h1) =
      bitsExpectation q Finset.univ (fun S => f (setSeed S)) := by
  classical
  rw [bernoulliSeedLaw, PMF.integral_eq_sum]
  simp only [seedPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal
    (bitsWeight_nonneg q h0 h1 _ _), smul_eq_mul]
  have h := (seedFinsetEquiv bits).sum_comp
    (fun S => bitsWeight q Finset.univ S * f (setSeed S))
  simpa only [seedFinsetEquiv, Equiv.coe_fn_mk, setSeed_seedSet,
    bitsExpectation, Finset.powerset_univ] using h

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory

namespace MatroidProphet

noncomputable def glue {n : ℕ} (mask : Finset (Fin n)) (s v : Weights n) : Weights n := by
  classical
  exact fun e => if e ∈ mask then s e else v e

lemma measurable_glue {n : ℕ} (mask : Finset (Fin n)) :
    Measurable (fun x : Weights n × Weights n => glue mask x.1 x.2) := by
  classical
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ mask
  · simpa [glue, he, Function.comp_def] using (measurable_pi_apply e).comp measurable_fst
  · simpa [glue, he, Function.comp_def] using (measurable_pi_apply e).comp measurable_snd

lemma measurable_glue_seed {n bits : ℕ} (mask : Seed bits → Finset (Fin n)) :
    Measurable (fun x : Seed bits × (Weights n × Weights n) =>
      glue (mask x.1) x.2.1 x.2.2) := by
  apply measurable_from_prod_countable_right
  intro r
  exact measurable_glue (mask r)

theorem glue_fixed_law {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S V : Ω → Weights n) (hS : Measurable S) (hV : Measurable V)
    (hi : iIndepFun (pairedCoordinates S V) μ)
    (hlaw : ∀ e, μ.map (fun ω => S ω e) = μ.map (fun ω => V ω e))
    (mask : Finset (Fin n)) :
    μ.map (fun ω => glue mask (S ω) (V ω)) = μ.map V := by
  classical
  let select : Fin n → Fin n × Bool := fun e => (e, decide (e ∈ mask))
  have hs : Function.Injective select := by
    intro a b h
    exact congrArg Prod.fst h
  have hg : iIndepFun (fun e ω => glue mask (S ω) (V ω) e) μ := by
    convert hi.precomp hs using 1
    funext e ω
    by_cases he : e ∈ mask <;> simp [select, pairedCoordinates, glue, he]
  have hv : iIndepFun (fun e ω => V ω e) μ := by
    have hj : Function.Injective (fun e : Fin n => (e, false)) := by
      intro a b h
      exact congrArg Prod.fst h
    simpa [pairedCoordinates] using hi.precomp hj
  have hgm : ∀ e, AEMeasurable (fun ω => glue mask (S ω) (V ω) e) μ := by
    intro e
    exact ((measurable_pi_apply e).comp
      ((measurable_glue mask).comp (hS.prodMk hV))).aemeasurable
  have hvm : ∀ e, AEMeasurable (fun ω => V ω e) μ := by
    intro e
    exact ((measurable_pi_apply e).comp hV).aemeasurable
  calc
    μ.map (fun ω => glue mask (S ω) (V ω)) =
        Measure.pi (fun e => μ.map (fun ω => glue mask (S ω) (V ω) e)) :=
      hg.map_fun_eq_pi_map hgm
    _ = Measure.pi (fun e => μ.map (fun ω => V ω e)) := by
      congr 1
      funext e
      by_cases he : e ∈ mask
      · simpa [glue, he, Function.comp_def] using hlaw e
      · simp [glue, he]
    _ = μ.map V := (hv.map_fun_eq_pi_map hvm).symm

theorem glue_seed_joint_law {n bits : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure (Seed bits)) [IsProbabilityMeasure ν]
    (S V : Ω → Weights n) (R : Ω → Seed bits)
    (hS : Measurable S) (hV : Measurable V) (hR : Measurable R)
    (hi : iIndepFun (pairedCoordinates S V) μ)
    (hlaw : ∀ e, μ.map (fun ω => S ω e) = μ.map (fun ω => V ω e))
    (hseed : IndepFun (fun ω => (S ω, V ω)) R μ)
    (hRlaw : μ.map R = ν) (mask : Seed bits → Finset (Fin n)) :
    MeasurePreserving (fun ω => (R ω, glue (mask (R ω)) (S ω) (V ω)))
      μ (ν.prod (μ.map V)) := by
  have hfiber (r : Seed bits) :
      (μ.map (fun ω => (S ω, V ω))).map (fun d => glue (mask r) d.1 d.2) =
        μ.map V := by
    rw [Measure.map_map (measurable_glue (mask r)) (hS.prodMk hV)]
    exact glue_fixed_law μ S V hS hV hi hlaw (mask r)
  have hstart : MeasurePreserving (fun ω => (R ω, (S ω, V ω))) μ
      (ν.prod (μ.map (fun ω => (S ω, V ω)))) := by
    refine ⟨hR.prodMk (hS.prodMk hV), ?_⟩
    rw [hseed.symm.map_prod_eq_prod_map_map hR.aemeasurable
      (hS.prodMk hV).aemeasurable, hRlaw]
  have hend := (MeasurePreserving.id ν).skew_product
    (g := fun (r : Seed bits) (d : Weights n × Weights n) => glue (mask r) d.1 d.2)
    (measurable_glue_seed mask) (ae_of_all _ hfiber)
  exact hend.comp hstart

theorem glue_seed_law {n bits : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure (Seed bits)) [IsProbabilityMeasure ν]
    (S V : Ω → Weights n) (R : Ω → Seed bits)
    (hS : Measurable S) (hV : Measurable V) (hR : Measurable R)
    (hi : iIndepFun (pairedCoordinates S V) μ)
    (hlaw : ∀ e, μ.map (fun ω => S ω e) = μ.map (fun ω => V ω e))
    (hseed : IndepFun (fun ω => (S ω, V ω)) R μ)
    (hRlaw : μ.map R = ν) (mask : Seed bits → Finset (Fin n)) :
    μ.map (fun ω => glue (mask (R ω)) (S ω) (V ω)) = μ.map V := by
  have hj := glue_seed_joint_law μ ν S V R hS hV hR hi hlaw hseed hRlaw mask
  exact ((measurePreserving_snd (μ := ν) (ν := μ.map V)).comp hj).map_eq

lemma measurable_weight_eval {n : ℕ} :
    Measurable (fun x : Weights n × Fin n => x.1 x.2) :=
  measurable_from_prod_countable_left fun e => measurable_pi_apply e

noncomputable def simulationHistory {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (s : Weights n) {k : Fin n} (h : History n k) : History n k := by
  classical
  exact fun j => ((h j).1, if (h j).1 ∈ A.mask r then s (h j).1 else (h j).2)

lemma measurable_simulationHistory {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (k : Fin n) :
    Measurable (fun x : Weights n × History n k => simulationHistory A r x.1 x.2) := by
  classical
  apply Measurable.of_eval
  intro j
  have hh : Measurable (fun x : Weights n × History n k => x.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  have hm : MeasurableSet {x : Weights n × History n k | (x.2 j).1 ∈ A.mask r} :=
    (measurable_fst.comp hh) (by trivial)
  exact (measurable_fst.comp hh).prodMk (Measurable.ite hm
    (measurable_weight_eval.comp (measurable_fst.prodMk (measurable_fst.comp hh)))
    (measurable_snd.comp hh))

lemma measurable_observed {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits) :
    Measurable (observed A r) := by
  classical
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ A.mask r
  · simpa [observed, he] using (measurable_pi_apply e : Measurable (fun w : Weights n => w e))
  · simp [observed, he]

def currentLabel {n : ℕ} {k : Fin n} (h : History n k) : Fin n :=
  (h ⟨k.val, Nat.lt_succ_self _⟩).1

noncomputable def sampleSimulation {n bits : ℕ} (A : HiddenRule n bits) : OnlineRule n bits where
  decide k r s h := if currentLabel h ∈ A.mask r then false
    else A.core.decide k r (observed A r s) (simulationHistory A r s h)
  measurable_decide k := by
    classical
    apply measurable_from_prod_countable_right
    intro r
    have hc : Measurable (fun x : Weights n × History n k => currentLabel x.2) :=
      measurable_fst.comp ((measurable_pi_apply (⟨k.val, Nat.lt_succ_self _⟩ : Fin (k.val + 1))).comp measurable_snd)
    have hm : MeasurableSet {x : Weights n × History n k | currentLabel x.2 ∈ A.mask r} :=
      hc (by trivial)
    exact Measurable.ite hm measurable_const
      ((A.core.measurable_decide k).comp (measurable_const.prodMk
        (((measurable_observed A r).comp measurable_fst).prodMk
          (measurable_simulationHistory A r k))))

lemma observed_glue {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (s v : Weights n) : observed A r (glue (A.mask r) s v) = observed A r s := by
  classical
  funext e
  by_cases he : e ∈ A.mask r <;> simp [observed, glue, he]

lemma simulationHistory_eq {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (k : Fin n) :
    simulationHistory A r s (history v π k) = history (glue (A.mask r) s v) π k := by
  classical
  rfl

@[simp] lemma currentLabel_history {n : ℕ} (v : Weights n)
    (π : ArrivalOrder n) (k : Fin n) : currentLabel (history v π k) = π k := by
  rfl

theorem sampleSimulation_acceptedThrough {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    acceptedThrough (sampleSimulation A) r s v π t =
      hiddenAcceptedThrough A r (glue (A.mask r) s v) π t := by
  classical
  ext e
  by_cases he : e ∈ A.mask r <;>
    simp [acceptedThrough, hiddenAcceptedThrough, decisionAt, sampleSimulation,
      simulationHistory_eq, observed_glue, he]

theorem sampleSimulation_reward {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) :
    reward (sampleSimulation A) r s v π = hiddenReward A r (glue (A.mask r) s v) π := by
  classical
  unfold reward accepted hiddenReward
  rw [sampleSimulation_acceptedThrough]
  apply Finset.sum_congr rfl
  intro e he
  have he' : e ∉ A.mask r := (Finset.mem_sdiff.mp he).2
  simp [glue, he']

theorem sampleSimulation_feasible {n bits : ℕ} (M : Matroid (Fin n))
    (A : HiddenRule n bits)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n))) :
    Feasible M (sampleSimulation A) := by
  intro r s v π t hs hv
  rw [sampleSimulation_acceptedThrough]
  apply hA
  intro e
  classical
  by_cases he : e ∈ A.mask r
  · simpa [glue, he, Function.comp_def] using hs e
  · simpa [glue, he, Function.comp_def] using hv e

@[simp] lemma glue_self {n : ℕ} (mask : Finset (Fin n)) (w : Weights n) :
    glue mask w w = w := by
  classical
  funext e
  simp [glue]

lemma hiddenWorstReward_le {n bits : ℕ} (A : HiddenRule n bits) (w : Weights n)
    (r : Seed bits) (π : ArrivalOrder n) :
    hiddenWorstReward A w r ≤ hiddenReward A r w π := by
  classical
  exact Finset.inf'_le (hiddenReward A r w) (Finset.mem_univ π)

lemma hiddenWorstReward_nonneg {n bits : ℕ} (A : HiddenRule n bits) (w : Weights n)
    (hw : ∀ e, 0 ≤ w e) (r : Seed bits) : 0 ≤ hiddenWorstReward A w r := by
  classical
  apply Finset.le_inf'
  intro π _
  exact Finset.sum_nonneg fun e _ => hw e

lemma hiddenWorstReward_le_optimum {n bits : ℕ} (M : Matroid (Fin n))
    (A : HiddenRule n bits)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (r : Seed bits) :
    hiddenWorstReward A w r ≤ optimum M w := by
  apply (hiddenWorstReward_le A w r (Equiv.refl _)).trans
  exact sum_le_optimum M w _ (hA w hw r (Equiv.refl _) n)

lemma measurable_hiddenReward {n bits : ℕ} (A : HiddenRule n bits) (π : ArrivalOrder n) :
    Measurable (fun x : Seed bits × Weights n => hiddenReward A x.1 x.2 π) := by
  have hm := (measurable_reward_fixed_order (sampleSimulation A) π).comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd))
  simpa only [Function.comp_def, sampleSimulation_reward, glue_self] using hm

lemma measurable_hiddenWorstReward {n bits : ℕ} (A : HiddenRule n bits) :
    Measurable (fun x : Seed bits × Weights n => hiddenWorstReward A x.2 x.1) := by
  classical
  have hm : Measurable ((Finset.univ : Finset (ArrivalOrder n)).inf'
      Finset.univ_nonempty (fun π (x : Seed bits × Weights n) => hiddenReward A x.1 x.2 π)) :=
    Finset.inf'_induction Finset.univ_nonempty _
      (fun _ hf _ hg => hf.inf hg) (fun π _ => measurable_hiddenReward A π)
  convert hm using 1
  ext x
  simp only [hiddenWorstReward, Finset.inf'_apply]

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.Maximum

open MeasureTheory Finset Set

variable {n : ℕ} {K : Type*} [Countable K] [MeasurableSpace K]
  [MeasurableSingletonClass K] [LinearOrder K]

lemma le_hiddenWorstReward {bits : ℕ} (A : HiddenRule n bits) (w : Weights n)
    (r : Seed bits) (c : ℝ) (h : ∀ π, c ≤ hiddenReward A r w π) :
    c ≤ hiddenWorstReward A w r := by
  classical
  apply Finset.le_inf'
  intro π _
  exact h π

theorem maximum_integral_top (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (g : Fin n)
    (hg : M.Indep ({g} : Set (Fin n))) (hag : active (key (w g)))
    (htop : ∀ f, M.Indep ({f} : Set (Fin n)) → active (key (w f)) → f ≠ g →
      higher (g, key (w g)) (f, key (w f))) :
    w g / 4 ≤ ∫ r, hiddenWorstReward
      (maximumHidden M key hkey active (seedSet (bits := n))) w r
      ∂bernoulliSeedLaw (fun _ => (1 / 2 : ℝ))
        (fun _ => by norm_num) (fun _ => by norm_num) := by
  classical
  let A := maximumHidden M key hkey active (seedSet (bits := n))
  let F : Finset (Fin n) → ℝ := fun H => hiddenWorstReward A w (setSeed H)
  rw [integral_bernoulliSeedLaw]
  change w g / 4 ≤ bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ F
  have hF : ∀ H ⊆ Finset.univ, 0 ≤ F H :=
    fun H _ => hiddenWorstReward_nonneg A w hw (setSeed H)
  let P : Finset (Fin n) := Finset.univ.filter fun f =>
    M.Indep ({f} : Set (Fin n)) ∧ active (key (w f)) ∧ f ≠ g
  by_cases hP : P.Nonempty
  · obtain ⟨h, hhP, hsecond⟩ := exists_top (fun f => key (w f)) P hP
    have hh := (Finset.mem_filter.mp hhP).2
    apply maximum_expectation_two Finset.univ g h (Finset.mem_univ _) (Finset.mem_univ _)
      (Ne.symm hh.2.2) F (w g) hF
    intro H _ hgH hhH
    apply le_hiddenWorstReward
    intro π
    have hqual := threshold_top_two M active (seedSet (bits := n)) (setSeed H)
      (fun f => key (w f)) g h hg hag hh.1 hh.2.1 htop
      (fun f hf haf hfg hfh => hsecond f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf, haf, hfg⟩) hfh)
      (by simpa using hgH) (by simpa using hhH)
    exact (maximumHidden_single_qualifier M key hkey active seedSet w (setSeed H) g
      (by simpa using hgH) hqual π).symm.le
  · apply maximum_expectation_one Finset.univ g (Finset.mem_univ _) F (w g) (hw g) hF
    intro H _ hgH
    apply le_hiddenWorstReward
    intro π
    have honly : ∀ f, M.Indep ({f} : Set (Fin n)) → active (key (w f)) → f = g := by
      intro f hf haf
      by_contra hfg
      exact hP ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf, haf, hfg⟩⟩
    have hqual := threshold_only_positive M active (seedSet (bits := n)) (setSeed H)
      (fun f => key (w f)) g hg hag honly (by simpa using hgH)
    exact (maximumHidden_single_qualifier M key hkey active seedSet w (setSeed H) g
      (by simpa using hgH) hqual π).symm.le

end MatroidProphet.Maximum

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open MeasureTheory

noncomputable def branchOnlineRule {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : OnlineRule n bits) : OnlineRule n bits where
  decide k r s h := if branch r then A.decide k r s h else B.decide k r s h
  measurable_decide k := by
    have hb : Measurable (fun x : Seed bits × (Weights n × History n k) => branch x.1) :=
      (measurable_of_countable branch).comp measurable_fst
    exact Measurable.ite (hb (measurableSet_singleton true))
      (A.measurable_decide k) (B.measurable_decide k)

noncomputable def branchHiddenRule {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : HiddenRule n bits) : HiddenRule n bits where
  mask r := if branch r then A.mask r else B.mask r
  core := branchOnlineRule branch A.core B.core

lemma branchOnlineRule_acceptedThrough {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : OnlineRule n bits) (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    acceptedThrough (branchOnlineRule branch A B) r s v π t =
      if branch r then acceptedThrough A r s v π t else acceptedThrough B r s v π t := by
  classical
  cases hb : branch r <;> simp [acceptedThrough, decisionAt, branchOnlineRule, hb] <;> rfl

lemma branchHiddenRule_observed {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : HiddenRule n bits) (r : Seed bits) (w : Weights n) :
    observed (branchHiddenRule branch A B) r w =
      if branch r then observed A r w else observed B r w := by
  funext e
  cases hb : branch r <;> simp only [observed, branchHiddenRule, hb, Bool.false_eq_true,
    ↓reduceIte]

lemma branchHiddenRule_acceptedThrough {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : HiddenRule n bits) (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    hiddenAcceptedThrough (branchHiddenRule branch A B) r w π t =
      if branch r then hiddenAcceptedThrough A r w π t else hiddenAcceptedThrough B r w π t := by
  change acceptedThrough (branchOnlineRule branch A.core B.core) r
    (observed (branchHiddenRule branch A B) r w) w π t \ (if branch r then A.mask r else B.mask r) = _
  rw [branchHiddenRule_observed, branchOnlineRule_acceptedThrough]
  cases branch r <;> simp only [Bool.false_eq_true, ↓reduceIte, hiddenAcceptedThrough]

lemma branchHiddenRule_reward {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : HiddenRule n bits) (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) :
    hiddenReward (branchHiddenRule branch A B) r w π =
      if branch r then hiddenReward A r w π else hiddenReward B r w π := by
  cases hb : branch r <;> simp [hiddenReward, branchHiddenRule_acceptedThrough, hb]

lemma branchHiddenRule_worst {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : HiddenRule n bits) (r : Seed bits) (w : Weights n) :
    hiddenWorstReward (branchHiddenRule branch A B) w r =
      if branch r then hiddenWorstReward A w r else hiddenWorstReward B w r := by
  classical
  cases hb : branch r <;> simp [hiddenWorstReward, branchHiddenRule_reward, hb]

instance withBotIntMeasurableSpace : MeasurableSpace (WithBot ℤ) := ⊤
instance withBotIntMeasurableSingletonClass : MeasurableSingletonClass (WithBot ℤ) :=
  ⟨fun _ => trivial⟩

noncomputable def roundedMaximumHidden {n : ℕ} (M : Matroid (Fin n))
    {bits : ℕ} (mask : Seed bits → Finset (Fin n)) : HiddenRule n bits :=
  Maximum.maximumHidden M (fun x => Priority.asLevel (roundedLevel weightBase x))
    ((measurable_of_countable Priority.asLevel).comp (measurable_roundedLevel weightBase))
    (fun a => a ≠ ⊥) mask

noncomputable def completeHiddenRule {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    HiddenRule n (mainSeedBits n) :=
  branchHiddenRule mainBranch (MainAlgorithm.hidden M hE)
    (roundedMaximumHidden M (fun r => (mainMasks r).H))

lemma branchHiddenRule_feasible {n bits : ℕ} (M : Matroid (Fin n))
    (branch : Seed bits → Bool) (A B : HiddenRule n bits)
    (hA : ∀ w, (∀ e, 0 ≤ w e) → ∀ r π t,
      M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (hB : ∀ w, (∀ e, 0 ≤ w e) → ∀ r π t,
      M.Indep (hiddenAcceptedThrough B r w π t : Set (Fin n)))
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (r : Seed bits) (π : ArrivalOrder n) (t : ℕ) :
    M.Indep (hiddenAcceptedThrough (branchHiddenRule branch A B) r w π t : Set (Fin n)) := by
  rw [branchHiddenRule_acceptedThrough]
  cases hb : branch r
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hB w hw r π t
  · simp only [↓reduceIte]
    exact hA w hw r π t

lemma roundedMaximumHidden_feasible {n bits : ℕ} (M : Matroid (Fin n))
    (mask : Seed bits → Finset (Fin n)) (w : Weights n) (hw : ∀ e, 0 ≤ w e)
    (r : Seed bits) (π : ArrivalOrder n) (t : ℕ) :
    M.Indep (hiddenAcceptedThrough (roundedMaximumHidden M mask) r w π t : Set (Fin n)) :=
  Maximum.maximumHidden_feasible M _ _ _ _ w hw r π t

lemma completeHiddenRule_feasible {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (r : Seed (mainSeedBits n))
    (π : ArrivalOrder n) (t : ℕ) :
    M.Indep (hiddenAcceptedThrough (completeHiddenRule M hE) r w π t : Set (Fin n)) :=
  branchHiddenRule_feasible M mainBranch _ _ (MainAlgorithm.hidden_feasible M hE)
    (roundedMaximumHidden_feasible M _) w hw r π t

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

noncomputable def maximumRounded {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (fun o : Option (Fin n) =>
    match o with
    | none => 0
    | some e => if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0)

lemma maximumRounded_nonneg {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) :
    0 ≤ maximumRounded M w := by
  classical
  exact Finset.le_sup' (s := Finset.univ)
    (f := fun o : Option (Fin n) => match o with
      | none => 0
      | some e => if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0)
    (Finset.mem_univ none)

lemma roundedWeight_le_maximumRounded {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (e : Fin n) (he : M.Indep ({e} : Set (Fin n))) :
    roundedWeight weightBase (w e) ≤ maximumRounded M w := by
  classical
  have h := Finset.le_sup' (s := Finset.univ)
    (f := fun o : Option (Fin n) => match o with
      | none => 0
      | some e => if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0)
    (Finset.mem_univ (some e))
  change (if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0) ≤
    maximumRounded M w at h
  rwa [ite_eq_left he] at h

noncomputable def maximumPayoff {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) : ℝ :=
  ∫ r, hiddenWorstReward (roundedMaximumHidden M (seedSet (bits := n))) w r
    ∂bernoulliSeedLaw (fun _ => (1 / 2 : ℝ)) (fun _ => by norm_num) (fun _ => by norm_num)

lemma maximumPayoff_nonneg {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    0 ≤ maximumPayoff M w :=
  integral_nonneg (fun r => hiddenWorstReward_nonneg _ w hw r)

lemma roundedWeight_le_four_maximumPayoff {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (hw : ∀ e, 0 ≤ w e) (e : Fin n) (he : M.Indep ({e} : Set (Fin n))) :
    roundedWeight weightBase (w e) ≤ 4 * maximumPayoff M w := by
  classical
  let a : Fin n → WithBot ℤ := fun f => Priority.asLevel (roundedLevel weightBase (w f))
  by_cases hea : a e = ⊥
  · have hu : roundedWeight weightBase (w e) = 0 := by
      change levelWeight weightBase (a e) = 0
      rw [hea]
      rfl
    rw [hu]
    exact mul_nonneg (by norm_num) (maximumPayoff_nonneg M w hw)
  · let P : Finset (Fin n) := Finset.univ.filter fun f => M.Indep ({f} : Set (Fin n)) ∧ a f ≠ ⊥
    have heP : e ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ e, he, hea⟩
    obtain ⟨g, hgP, htop⟩ := Maximum.exists_top a P ⟨e, heP⟩
    have hg := (Finset.mem_filter.mp hgP).2
    have hwin : w g / 4 ≤ maximumPayoff M w :=
      Maximum.maximum_integral_top M (fun x => Priority.asLevel (roundedLevel weightBase x))
        ((measurable_of_countable Priority.asLevel).comp (measurable_roundedLevel weightBase))
        (fun x => x ≠ ⊥) w hw g hg.1 hg.2
        (fun f hf haf hfg => htop f (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf, haf⟩) hfg)
    have hkey : a e ≤ a g := by
      by_cases heg : e = g
      · exact heg ▸ le_rfl
      · rcases htop e heP heg with hlt | ⟨heq, _⟩
        · exact hlt.le
        · exact heq.symm.le
    have hu : roundedWeight weightBase (w e) ≤ roundedWeight weightBase (w g) :=
      levelWeight_mono (by norm_num [weightBase]) hkey
    have hraw := roundedWeight_le (by norm_num [weightBase] : 1 < weightBase) (hw g)
    nlinarith

theorem maximum_branch_guarantee {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (hw : ∀ e, 0 ≤ w e) : maximumRounded M w / 4 ≤ maximumPayoff M w := by
  classical
  have hnonneg := maximumPayoff_nonneg M w hw
  have hfour : maximumRounded M w ≤ 4 * maximumPayoff M w := by
    apply Finset.sup'_le
    intro o _
    cases o with
    | none => exact mul_nonneg (by norm_num) hnonneg
    | some e =>
      change (if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0) ≤ _
      split_ifs with he
      · exact roundedWeight_le_four_maximumPayoff M w hw e he
      · exact mul_nonneg (by norm_num) hnonneg
  nlinarith

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset

variable {n : ℕ}

noncomputable def trueLevels (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : Finset ℤ := weightLevels a (candidateLabels M a H)

noncomputable def analyzedLevels (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : Finset ℤ := by
  classical
  exact (trueLevels M a H).filter fun i =>
    densityThreshold ≤ ((candidateLabels M a H).filter (fun e => a e = some i)).card

noncomputable def comparisonMass (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : ℝ :=
  ∑ e ∈ positiveGreedy M a \ H, levelWeight weightBase (a e)

noncomputable def analyzedComparisonMass (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : ℝ := by
  classical
  exact ∑ i ∈ analyzedLevels M a H, weightBase ^ i *
    (((positiveGreedy M a \ H).filter (fun e => a e = some i)).card : ℝ)

lemma candidate_level_le_maximumRounded (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (H : Finset (Fin n)) (i : ℤ)
    (hi : i ∈ trueLevels M (fun e => roundedLevel weightBase (w e)) H) :
    weightBase ^ i ≤ maximumRounded M w := by
  classical
  obtain ⟨e, he, hei⟩ := (mem_weightLevels _ _ i).1 hi
  have hc : candidate M ⟨H, ∅, ∅, ∅, false⟩ (fun e => roundedLevel weightBase (w e)) e
      (roundedLevel weightBase (w e)) := (Finset.mem_filter.mp he).2
  have heI := candidate_singleton_indep M hE _ _ e _ hc
  have h := roundedWeight_le_maximumRounded M w e heI
  simpa only [roundedWeight, hei, levelWeight] using h

lemma comparisonMass_partition (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) :
    comparisonMass M a H =
      ∑ i ∈ trueLevels M a H, weightBase ^ i *
        (((positiveGreedy M a \ H).filter (fun e => a e = some i)).card : ℝ) := by
  exact (sum_weightGroups_mass a _ _
    (weightLevels_mono a (positiveGreedy_survivors_subset M a H)) weightBase).symm

lemma small_comparison_mass (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (H : Finset (Fin n)) :
    comparisonMass M (fun e => roundedLevel weightBase (w e)) H ≤
      analyzedComparisonMass M (fun e => roundedLevel weightBase (w e)) H +
        2 * densityThreshold * maximumRounded M w := by
  classical
  let a : Fin n → Option ℤ := fun e => roundedLevel weightBase (w e)
  let Y := positiveGreedy M a \ H
  let U := candidateLabels M a H
  let L := trueLevels M a H
  let A := analyzedLevels M a H
  have hAU : A ⊆ L := Finset.filter_subset _ _
  have hsmall : ∀ i ∈ L \ A, ((Y.filter (fun e => a e = some i)).card : ℝ) ≤ densityThreshold := by
    intro i hi
    obtain ⟨hiL, hiA⟩ := Finset.mem_sdiff.mp hi
    have hn : ¬densityThreshold ≤ ((U.filter (fun e => a e = some i)).card : ℝ) := by
      intro hh
      exact hiA (Finset.mem_filter.mpr ⟨hiL, hh⟩)
    have hc : (Y.filter (fun e => a e = some i)).card ≤ (U.filter (fun e => a e = some i)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (positiveGreedy_survivors_subset M a H))
    have hcR : ((Y.filter (fun e => a e = some i)).card : ℝ) ≤
        ((U.filter (fun e => a e = some i)).card : ℝ) := by exact_mod_cast hc
    exact hcR.trans (le_of_lt (lt_of_not_ge hn))
  have hbound := small_group_mass_bound weightBase densityThreshold (maximumRounded M w)
    (by norm_num [weightBase]) constants_positive.2.1.le (maximumRounded_nonneg M w)
    (L \ A) (fun i => ((Y.filter (fun e => a e = some i)).card : ℝ)) hsmall
    (fun i hi => candidate_level_le_maximumRounded M hE w H i (Finset.mem_sdiff.mp hi).1)
  have hpartition := Finset.sum_sdiff hAU
    (f := fun i => weightBase ^ i * ((Y.filter (fun e => a e = some i)).card : ℝ))
  rw [comparisonMass_partition]
  change (∑ i ∈ L, weightBase ^ i * ((Y.filter (fun e => a e = some i)).card : ℝ)) ≤
    (∑ i ∈ A, weightBase ^ i * ((Y.filter (fun e => a e = some i)).card : ℝ)) + _
  linarith

end MatroidProphet.MainAlgorithm

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}

lemma higherTrueGroups_card_eq_sum (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) :
    ((higherTrueGroups M d w i).card : ℝ) =
      ∑ j ∈ trueLevels M w d.H with i < j, ((trueGroup M d w j).card : ℝ) := by
  simp only [trueGroup_eq_candidate_filter, higherTrueGroups]
  exact highGroup_card w (candidateLabels M w d.H) (trueLevels M w d.H) Subset.rfl i

theorem conditional_main_payoff (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) :
    thinningRate / (2 * densityThreshold) *
      (retainedFraction * analyzedComparisonMass M w d.H - ((2:ℝ)^21)⁻¹ *
        ∑ e ∈ candidateLabels M w d.H, levelWeight weightBase (w e)) ≤
      mainMean d (fun d' => mainWorstRounded M hE d' w) := by
  classical
  let J := positiveGreedy M w \ d.H
  let Y : ℤ → Finset (Fin n) := fun i => J.filter (fun e => w e = some i)
  have hY (i : ℤ) : (Y i : Set (Fin n)) ⊆ (trueGroup M d w i : Set (Fin n)) := by
    rw [trueGroup_eq_candidate_filter]
    intro e he
    obtain ⟨heJ, hew⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨positiveGreedy_survivors_subset M w d.H heJ, hew⟩
  have hI (i : ℤ) : M.Indep (Y i : Set (Fin n)) :=
    (positiveGreedy_survivors_indep M hE w d.H).subset (filter_subset _ _)
  have hgroup (i : ℤ) (hi : i ∈ analyzedLevels M w d.H) :
      thinningRate / densityThreshold *
        (retainedFraction * (Y i).card -
          (((2:ℝ)^23)⁻¹ + thinningRate * densityThreshold) * (trueGroup M d w i).card -
          (1 + thinningRate * densityThreshold) *
            ∑ l ∈ trueLevels M w d.H with i < l, ((trueGroup M d w l).card : ℝ)) ≤
        mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)) := by
    have hn : densityThreshold ≤ ((trueGroup M d w i).card : ℝ) := by
      rw [trueGroup_eq_candidate_filter]
      exact (mem_filter.mp hi).2
    have hp := true_group_payoff M hE d w i (Y i : Set (Fin n)) (hY i) (hI i) hn
    simpa only [Set.ncard_coe_finset, higherTrueGroups_card_eq_sum] using hp
  have hpaid := source_weighted_group_payoff (trueLevels M w d.H) (analyzedLevels M w d.H)
    (filter_subset _ _) (fun i => ((trueGroup M d w i).card : ℝ))
    (fun i => ((Y i).card : ℝ)) (fun i => mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)))
    (fun i hi => Nat.cast_nonneg _) hgroup
  have hmass : (∑ i ∈ trueLevels M w d.H, weightBase ^ i * ((trueGroup M d w i).card : ℝ)) =
      ∑ e ∈ candidateLabels M w d.H, levelWeight weightBase (w e) := by
    simp only [trueGroup_eq_candidate_filter]
    exact sum_weightGroups_mass w (candidateLabels M w d.H) (trueLevels M w d.H) Subset.rfl weightBase
  rw [hmass] at hpaid
  exact hpaid.trans (weighted_mean_trueLambda_le_mainWorstRounded M hE d w (analyzedLevels M w d.H))

end MatroidProphet.MainAlgorithm

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

abbrev MainSeedBlocks (n : ℕ) := Seed n × (Seed n × (Seed n × (Seed n × Seed 2)))

noncomputable def encodeMainSeed {n : ℕ} (b : MainSeedBlocks n) : Seed (mainSeedBits n) :=
  fun i => if hi : i.val < 4*n then
    let e : Fin n := ⟨i.val / 4, by omega⟩
    if i.val % 4 = 0 then b.1 e else
    if i.val % 4 = 1 then b.2.1 e else
    if i.val % 4 = 2 then b.2.2.1 e else b.2.2.2.1 e
  else b.2.2.2.2 ⟨i.val-4*n, by have := i.isLt; dsimp [mainSeedBits] at this; omega⟩

lemma encodeMainSeed_mask {n : ℕ} (b : MainSeedBlocks n) :
    seedMask (encodeMainSeed b) 0 = seedSet b.1 ∧
    seedMask (encodeMainSeed b) 1 = seedSet b.2.1 ∧
    seedMask (encodeMainSeed b) 2 = seedSet b.2.2.1 ∧
    seedMask (encodeMainSeed b) 3 = seedSet b.2.2.2.1 := by
  have h0 : ∀ e : Fin n, 4*e.val+0 < 4*n := fun e => by omega
  have h1 : ∀ e : Fin n, 4*e.val+1 < 4*n := fun e => by omega
  have h2 : ∀ e : Fin n, 4*e.val+2 < 4*n := fun e => by omega
  have h3 : ∀ e : Fin n, 4*e.val+3 < 4*n := fun e => by omega
  repeat' constructor
  all_goals
    ext e
    simp_all [seedMask, seedSet, encodeMainSeed, Nat.add_mod, Nat.mul_add_div]

lemma encodeMainSeed_branch {n : ℕ} (b : MainSeedBlocks n) :
    mainBranch (encodeMainSeed b) = b.2.2.2.2 0 := by
  simp [mainBranch, encodeMainSeed]

lemma encodeMainSeed_odd {n : ℕ} (b : MainSeedBlocks n) :
    (mainMasks (encodeMainSeed b)).odd = b.2.2.2.2 1 := by
  have h : ¬ 4*n+1 < 4*n := by omega
  simp [mainMasks, encodeMainSeed, h]

noncomputable def maskCoinLaw (n : ℕ) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Measure (Seed n) :=
  bernoulliSeedLaw (fun _ => p) (fun _ => h0) (fun _ => h1)

instance maskCoinLaw_probability (n : ℕ) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbabilityMeasure (maskCoinLaw n p h0 h1) := by
  unfold maskCoinLaw
  infer_instance

noncomputable def mainBlockLaw (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) : Measure (MainSeedBlocks n) :=
  (maskCoinLaw n (q 0) (h0 0) (h1 0)).prod
    ((maskCoinLaw n (q 1) (h0 1) (h1 1)).prod
      ((maskCoinLaw n (q 2) (h0 2) (h1 2)).prod
        ((maskCoinLaw n (q 3) (h0 3) (h1 3)).prod
          (maskCoinLaw 2 (q 4) (h0 4) (h1 4)))))

instance mainBlockLaw_probability (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) :
    IsProbabilityMeasure (mainBlockLaw n q h0 h1) := by
  unfold mainBlockLaw
  infer_instance

noncomputable def mainSeedLaw (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) : Measure (Seed (mainSeedBits n)) :=
  (mainBlockLaw n q h0 h1).map encodeMainSeed

instance mainSeedLaw_probability (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) :
    IsProbabilityMeasure (mainSeedLaw n q h0 h1) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

lemma integral_mainSeedLaw (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) (f : Seed (mainSeedBits n) → ℝ) :
    (∫ r, f r ∂mainSeedLaw n q h0 h1) =
      ∫ H, ∫ D, ∫ C, ∫ T, ∫ b, f (encodeMainSeed (H, D, C, T, b))
        ∂maskCoinLaw 2 (q 4) (h0 4) (h1 4)
        ∂maskCoinLaw n (q 3) (h0 3) (h1 3)
        ∂maskCoinLaw n (q 2) (h0 2) (h1 2)
        ∂maskCoinLaw n (q 1) (h0 1) (h1 1)
        ∂maskCoinLaw n (q 0) (h0 0) (h1 0) := by
  rw [mainSeedLaw, integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable f).stronglyMeasurable]
  simp only [mainBlockLaw]
  rw [integral_prod _ Integrable.of_finite]
  apply integral_congr_ae
  exact ae_of_all _ fun H => by
    dsimp only
    rw [integral_prod _ Integrable.of_finite]
    apply integral_congr_ae
    exact ae_of_all _ fun D => by
      dsimp only
      rw [integral_prod _ Integrable.of_finite]
      apply integral_congr_ae
      exact ae_of_all _ fun C => by
        dsimp only
        rw [integral_prod _ Integrable.of_finite]

lemma mainSeedLaw_expectation (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) (f : Seed (mainSeedBits n) → ℝ) :
    (∫ r, f r ∂mainSeedLaw n q h0 h1) =
      bitsExpectation (fun _ : Fin n => q 0) Finset.univ (fun H =>
        bitsExpectation (fun _ : Fin n => q 1) Finset.univ (fun D =>
          bitsExpectation (fun _ : Fin n => q 2) Finset.univ (fun C =>
            bitsExpectation (fun _ : Fin n => q 3) Finset.univ (fun T =>
              bitsExpectation (fun _ : Fin 2 => q 4) Finset.univ (fun b =>
                f (encodeMainSeed (setSeed H, setSeed D, setSeed C, setSeed T, setSeed b))))))) := by
  rw [integral_mainSeedLaw]
  simp only [maskCoinLaw, integral_bernoulliSeedLaw]

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

noncomputable def sourceCoinProbability (j : Fin 5) : ℝ :=
  if j.val = 0 then 1/2 else if j.val = 1 then 1/4 else if j.val = 4 then 1/2 else thinningRate

lemma sourceCoinProbability_nonneg (j : Fin 5) : 0 ≤ sourceCoinProbability j := by
  unfold sourceCoinProbability
  split_ifs <;> norm_num [thinningRate]

lemma sourceCoinProbability_le_one (j : Fin 5) : sourceCoinProbability j ≤ 1 := by
  unfold sourceCoinProbability
  split_ifs <;> norm_num [thinningRate]

noncomputable def sourceSeedLaw (n : ℕ) : Measure (Seed (mainSeedBits n)) :=
  mainSeedLaw n sourceCoinProbability sourceCoinProbability_nonneg sourceCoinProbability_le_one

instance sourceSeedLaw_probability (n : ℕ) : IsProbabilityMeasure (sourceSeedLaw n) := by
  unfold sourceSeedLaw
  infer_instance

lemma mainMasks_encodeMainSeed {n : ℕ} (b : MainSeedBlocks n) :
    mainMasks (encodeMainSeed b) =
      ⟨seedSet b.1, seedSet b.2.1, seedSet b.2.2.1, seedSet b.2.2.2.1, b.2.2.2.2 1⟩ := by
  obtain ⟨hH, hD, hC, hT⟩ := encodeMainSeed_mask b
  have ho := encodeMainSeed_odd b
  change (encodeMainSeed b) _ = _ at ho
  simp only [mainMasks, hH, hD, hC, hT, ho]

lemma fairTwoBits (f : Bool → Bool → ℝ) :
    bitsExpectation (fun _ : Fin 2 => (1/2 : ℝ)) Finset.univ
      (fun S => f (setSeed S 0) (setSeed S 1)) =
      fairParityExpectation (fun p => fairParityExpectation (fun b => f b p)) := by
  have hu : (Finset.univ : Finset (Fin 2)) = insert 0 (insert 1 ∅) := by decide
  rw [hu, bitsExpectation_insert _ _ 0 (by decide)]
  rw [bitsExpectation_insert _ _ 1 (by decide), bitsExpectation_insert _ _ 1 (by decide)]
  simp [bitsExpectation_empty, setSeed, fairParityExpectation]
  ring

lemma integral_sourceSeedLaw {n : ℕ} (f : MainMasks n → Bool → ℝ) :
    (∫ r, f (mainMasks r) (mainBranch r) ∂sourceSeedLaw n) =
      bitsExpectation (fun _ : Fin n => (1/2 : ℝ)) Finset.univ (fun H =>
        bitsExpectation (fun _ : Fin n => (1/4 : ℝ)) Finset.univ (fun D =>
          bitsExpectation (fun _ : Fin n => thinningRate) Finset.univ (fun C =>
            bitsExpectation (fun _ : Fin n => thinningRate) Finset.univ (fun T =>
              fairParityExpectation (fun p => fairParityExpectation (fun b => f ⟨H,D,C,T,p⟩ b)))))) := by
  rw [sourceSeedLaw, mainSeedLaw_expectation]
  simp only [sourceCoinProbability]
  norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, ite_true, ite_false,
    OfNat.ofNat_ne_zero]
  simp only [mainMasks_encodeMainSeed, encodeMainSeed_branch, seedSet_setSeed]
  apply bitsExpectation_congr
  intro H _
  apply bitsExpectation_congr
  intro D _
  apply bitsExpectation_congr
  intro C _
  apply bitsExpectation_congr
  intro T _
  exact fairTwoBits (fun b p => f ⟨H,D,C,T,p⟩ b)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet.Maximum

open MeasureTheory Finset

lemma maximumHidden_mask_congr {n bits bits' : ℕ} {K : Type*} [Countable K]
    [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
    (M : Matroid (Fin n)) (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) (mask' : Seed bits' → Finset (Fin n))
    (r : Seed bits) (r' : Seed bits') (hm : mask r = mask' r')
    (w : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    hiddenAcceptedThrough (maximumHidden M key hkey active mask) r w π t =
      hiddenAcceptedThrough (maximumHidden M key hkey active mask') r' w π t := by
  classical
  have hd (k : Fin n) :
      decisionAt (maximumRule M key hkey active mask) r
        (observed (maximumHidden M key hkey active mask) r w) w π k = true ↔
      decisionAt (maximumRule M key hkey active mask') r'
        (observed (maximumHidden M key hkey active mask') r' w) w π k = true := by
    unfold maximumRule
    rw [firstRule_decision, firstRule_decision]
    simp only [threshold, observed, maximumHidden, hm]
    rfl
  ext e
  change e ∈ acceptedThrough (maximumRule M key hkey active mask) r
      (observed (maximumHidden M key hkey active mask) r w) w π t \ mask r ↔
    e ∈ acceptedThrough (maximumRule M key hkey active mask') r'
      (observed (maximumHidden M key hkey active mask') r' w) w π t \ mask' r'
  rw [Finset.mem_sdiff, Finset.mem_sdiff]
  constructor
  · rintro ⟨he, hn⟩
    obtain ⟨_, ht, ha⟩ := Finset.mem_filter.mp he
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, (hd _).mp ha⟩,
      by simpa only [hm] using hn⟩
  · rintro ⟨he, hn⟩
    obtain ⟨_, ht, ha⟩ := Finset.mem_filter.mp he
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, (hd _).mpr ha⟩,
      by simpa only [hm] using hn⟩

lemma maximumHidden_worst_mask_congr {n bits bits' : ℕ} {K : Type*} [Countable K]
    [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
    (M : Matroid (Fin n)) (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) (mask' : Seed bits' → Finset (Fin n))
    (r : Seed bits) (r' : Seed bits') (hm : mask r = mask' r') (w : Weights n) :
    hiddenWorstReward (maximumHidden M key hkey active mask) w r =
      hiddenWorstReward (maximumHidden M key hkey active mask') w r' := by
  classical
  unfold hiddenWorstReward
  congr 1
  funext π
  unfold hiddenReward
  rw [maximumHidden_mask_congr M key hkey active mask mask' r r' hm]

end MatroidProphet.Maximum

namespace MatroidProphet

noncomputable def maximumForMask {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (H : Finset (Fin n)) : ℝ :=
  hiddenWorstReward (roundedMaximumHidden M (seedSet (bits := n))) w (setSeed H)

lemma roundedMaximum_worst_mask {n bits : ℕ} (M : Matroid (Fin n))
    (mask : Seed bits → Finset (Fin n)) (r : Seed bits) (w : Weights n) :
    hiddenWorstReward (roundedMaximumHidden M mask) w r = maximumForMask M w (mask r) := by
  apply Maximum.maximumHidden_worst_mask_congr
  exact (seedSet_setSeed _).symm

lemma maximumPayoff_eq_masks {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) :
    maximumPayoff M w = bitsExpectation (fun _ => (1/2 : ℝ)) Finset.univ (maximumForMask M w) := by
  exact integral_bernoulliSeedLaw _ _ _ _

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open MeasureTheory Finset MainAlgorithm

noncomputable def mainPayoff {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) : ℝ :=
  bitsExpectation (fun _ => (1/2 : ℝ)) Finset.univ (fun H =>
    mainMean ⟨H, ∅, ∅, ∅, false⟩
      (fun d => mainWorstRounded M hE d (fun e => roundedLevel weightBase (w e))))

lemma mainPayoff_nonneg {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) : 0 ≤ mainPayoff M hE w := by
  apply bitsExpectation_nonneg _ (fun _ => by norm_num) (fun _ => by norm_num)
  intro H _
  have h := mainMean_mono (⟨H, ∅, ∅, ∅, false⟩ : MainMasks n)
    (fun d _ => mainWorstRounded_nonneg M hE d (fun e => roundedLevel weightBase (w e)))
  simpa only [mainMean_const] using h

lemma mainMean_H {n : ℕ} (d : MainMasks n) (f : Finset (Fin n) → ℝ) :
    mainMean d (fun d' => f d'.H) = f d.H := by
  simp only [mainMean, tripleMaskExpectation, withMasks,
    fairParityExpectation_const, bitsExpectation_const]

lemma integral_sourceSeedLaw_mainMean {n : ℕ} (f : MainMasks n → Bool → ℝ) :
    (∫ r, f (mainMasks r) (mainBranch r) ∂sourceSeedLaw n) =
      bitsExpectation (fun _ => (1/2 : ℝ)) Finset.univ (fun H =>
        mainMean ⟨H, ∅, ∅, ∅, false⟩ (fun d => fairParityExpectation (fun b => f d b))) := by
  simpa only [mainMean, tripleMaskExpectation, withMasks] using integral_sourceSeedLaw f

lemma completeHiddenRule_lower {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (r : Seed (mainSeedBits n)) :
    (if mainBranch r then
      mainWorstRounded M hE (mainMasks r) (fun e => roundedLevel weightBase (w e))
    else maximumForMask M w (mainMasks r).H) ≤
      hiddenWorstReward (completeHiddenRule M hE) w r := by
  rw [completeHiddenRule, branchHiddenRule_worst]
  cases hb : mainBranch r
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [roundedMaximum_worst_mask]
  · simp only [↓reduceIte]
    exact mainWorstRounded_le_hiddenWorstReward M hE r w hw

lemma integrated_branch_lower {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    (mainPayoff M hE w + maximumPayoff M w) / 2 ≤
      ∫ r, hiddenWorstReward (completeHiddenRule M hE) w r ∂sourceSeedLaw n := by
  have h := integral_mono (μ := sourceSeedLaw n) Integrable.of_finite Integrable.of_finite
    (fun r => completeHiddenRule_lower M hE w hw r)
  have heq : (∫ r, (if mainBranch r then
      mainWorstRounded M hE (mainMasks r) (fun e => roundedLevel weightBase (w e))
      else maximumForMask M w (mainMasks r).H) ∂sourceSeedLaw n) =
      (mainPayoff M hE w + maximumPayoff M w) / 2 := by
    rw [integral_sourceSeedLaw_mainMean (fun d b => if b then
      mainWorstRounded M hE d (fun e => roundedLevel weightBase (w e))
      else maximumForMask M w d.H)]
    have hf : (fun d : MainMasks n => fairParityExpectation (fun b => if b then
        mainWorstRounded M hE d (fun e => roundedLevel weightBase (w e))
        else maximumForMask M w d.H)) =
        (fun d => (1/2 : ℝ) *
          (mainWorstRounded M hE d (fun e => roundedLevel weightBase (w e)) + maximumForMask M w d.H)) := by
      funext d
      simp only [fairParityExpectation, Bool.false_eq_true, ↓reduceIte]
      ring
    rw [hf]
    simp_rw [mainMean_mul, mainMean_add, mainMean_H]
    rw [bitsExpectation_mul_const, bitsExpectation_add, ← maximumPayoff_eq_masks]
    change (1/2 : ℝ) * (mainPayoff M hE w + maximumPayoff M w) = _
    ring
  rw [heq] at h
  exact h

end MatroidProphet

end OAI
end
end

section
section
/-!
# Hidden-vector matroid selection

The observation mask depends only on the initial seed, before weights are seen.
Observed labels are sacrificed. The minimum over all arrival permutations is
taken separately for each seed, inside the expectation.
-/
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory

namespace MatroidProphet

lemma measurableSet_nonnegative (n : ℕ) :
    MeasurableSet {w : Weights n | ∀ e, 0 ≤ w e} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun e => measurableSet_le measurable_const (measurable_pi_apply e)

lemma integrable_hidden_product {n bits : ℕ} (M : Matroid (Fin n)) (A : HiddenRule n bits)
    (ν : Measure (Seed bits)) [IsProbabilityMeasure ν] (ρ : Measure (Weights n)) [SFinite ρ]
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (hNN : ∀ᵐ w ∂ρ, ∀ e, 0 ≤ w e) (hopt : Integrable (optimum M) ρ) :
    Integrable (fun x : Seed bits × Weights n => hiddenWorstReward A x.2 x.1)
      (ν.prod ρ) := by
  apply (hopt.comp_snd ν).mono' (measurable_hiddenWorstReward A).aestronglyMeasurable
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ρ)).ae hNN] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hiddenWorstReward_nonneg A x.2 hx x.1)]
  exact hiddenWorstReward_le_optimum M A hA x.2 hx x.1

lemma hidden_product_integral_bound {n bits : ℕ} (M : Matroid (Fin n))
    (A : HiddenRule n bits) (ν : Measure (Seed bits)) [IsProbabilityMeasure ν]
    (ρ : Measure (Weights n)) [IsProbabilityMeasure ρ] (c : ℝ)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (hNN : ∀ᵐ w ∂ρ, ∀ e, 0 ≤ w e) (hopt : Integrable (optimum M) ρ)
    (hbound : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      c * optimum M w ≤ ∫ r, hiddenWorstReward A w r ∂ν) :
    c * (∫ w, optimum M w ∂ρ) ≤
      ∫ x : Seed bits × Weights n, hiddenWorstReward A x.2 x.1 ∂ν.prod ρ := by
  have hip := integrable_hidden_product M A ν ρ hA hNN hopt
  rw [← integral_const_mul]
  calc
    _ ≤ ∫ w, ∫ r, hiddenWorstReward A w r ∂ν ∂ρ := by
      apply integral_mono_ae (hopt.const_mul c) hip.integral_prod_right
      filter_upwards [hNN] with w hw
      exact hbound w hw
    _ = _ := (integral_prod_symm _ hip).symm

lemma integrable_feasible_reward {n bits : ℕ} (M : Matroid (Fin n))
    (A : OnlineRule n bits) (hA : Feasible M A)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S V : Ω → Weights n) (R : Ω → Seed bits) (π : Ω → ArrivalOrder n)
    (hS : Measurable S) (hV : Measurable V) (hR : Measurable R) (hπ : Measurable π)
    (hSN : ∀ᵐ ω ∂μ, ∀ e, 0 ≤ S ω e) (hVN : ∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e)
    (hopt : Integrable (fun ω => optimum M (V ω)) μ) :
    Integrable (fun ω => reward A (R ω) (S ω) (V ω) (π ω)) μ := by
  have hrm := (measurable_reward A).comp (hπ.prodMk (hR.prodMk (hS.prodMk hV)))
  apply hopt.mono' hrm.aestronglyMeasurable
  filter_upwards [hSN, hVN] with ω hs hv
  change ‖reward A (R ω) (S ω) (V ω) (π ω)‖ ≤ optimum M (V ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (reward_nonneg A (R ω) (S ω) (V ω) (π ω) hv)]
  exact reward_le_optimum M A hA (R ω) (S ω) (V ω) (π ω) hs hv

theorem oneSample_of_hidden {n bits : ℕ} (M : Matroid (Fin n)) (A : HiddenRule n bits)
    (ν : Measure (Seed bits)) [IsProbabilityMeasure ν] (c : ℝ)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (hbound : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      c * optimum M w ≤ ∫ r, hiddenWorstReward A w r ∂ν)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S V : Ω → Weights n) (R : Ω → Seed bits)
    (hS : Measurable S) (hV : Measurable V) (hR : Measurable R)
    (hSN : ∀ᵐ ω ∂μ, ∀ e, 0 ≤ S ω e) (hVN : ∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e)
    (hi : iIndepFun (pairedCoordinates S V) μ)
    (hlaw : ∀ e, μ.map (fun ω => S ω e) = μ.map (fun ω => V ω e))
    (hseed : IndepFun (fun ω => (S ω, V ω)) R μ)
    (hRlaw : μ.map R = ν)
    (hopt : Integrable (fun ω => optimum M (V ω)) μ)
    (π : Ω → ArrivalOrder n) (hπ : Measurable π) :
    Integrable (fun ω => reward (sampleSimulation A) (R ω) (S ω) (V ω) (π ω)) μ ∧
      c * (∫ ω, optimum M (V ω) ∂μ) ≤
        ∫ ω, reward (sampleSimulation A) (R ω) (S ω) (V ω) (π ω) ∂μ := by
  have hj := glue_seed_joint_law μ ν S V R hS hV hR hi hlaw hseed hRlaw A.mask
  have hoptLaw : Integrable (optimum M) (μ.map V) :=
    (integrable_map_measure (measurable_optimum M).aestronglyMeasurable hV.aemeasurable).2 hopt
  have hNNLaw : ∀ᵐ w ∂μ.map V, ∀ e, 0 ≤ w e :=
    (ae_map_iff hV.aemeasurable (measurableSet_nonnegative n)).2 hVN
  have hip := integrable_hidden_product M A ν (μ.map V) hA hNNLaw hoptLaw
  have him := hj.integrable_comp_of_integrable hip
  have hri := integrable_feasible_reward M (sampleSimulation A)
    (sampleSimulation_feasible M A hA) μ S V R π hS hV hR hπ hSN hVN hopt
  have : IsProbabilityMeasure (μ.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  have hb := hidden_product_integral_bound M A ν (μ.map V) c hA hNNLaw hoptLaw hbound
  have hoptEq := integral_map_of_stronglyMeasurable (μ := μ) hV
    (measurable_optimum M).stronglyMeasurable
  have hminEq := integral_map_of_stronglyMeasurable (μ := μ) hj.measurable
    (measurable_hiddenWorstReward A).stronglyMeasurable
  rw [hj.map_eq] at hminEq
  rw [hoptEq, hminEq] at hb
  refine ⟨hri, hb.trans (integral_mono_ae him hri (ae_of_all _ ?_))⟩
  intro ω
  change hiddenWorstReward A (glue (A.mask (R ω)) (S ω) (V ω)) (R ω) ≤
    reward (sampleSimulation A) (R ω) (S ω) (V ω) (π ω)
  rw [sampleSimulation_reward]
  exact hiddenWorstReward_le A _ (R ω) (π ω)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory

namespace MatroidProphet

theorem hiddenVectorChallenge_implies_oneSampleChallenge.{u}
    (hh : HiddenVectorChallenge) : OneSampleChallenge.{u} := by
  intro n M hM
  obtain ⟨bits, ν, hν, A, hA, hbound⟩ := hh n M hM
  let := hν
  refine ⟨bits, ν, hν, sampleSimulation A, sampleSimulation_feasible M A hA, ?_⟩
  intro Ω mΩ μ hμ S V R hS hV hR hSN hVN hi hlaw hseed hRlaw hopt π hπ
  obtain ⟨hri, hpay⟩ := oneSample_of_hidden M A ν (((2 : ℝ) ^ 293)⁻¹) hA hbound
    μ S V R hS hV hR hSN hVN hi hlaw hseed hRlaw hopt π hπ
  refine ⟨hri, le_trans ?_ hpay⟩
  apply mul_le_mul_of_nonneg_right
  · exact inv_anti₀ (pow_pos (by norm_num : (0 : ℝ) < 2) 293)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 293 ≤ 310))
  · exact integral_nonneg fun ω => optimum_nonneg M (V ω)

end MatroidProphet

end OAI
end
end

section
section
namespace OAI

namespace MatroidProphet

open MeasureTheory Finset MainAlgorithm

lemma main_branch_guarantee_small {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n)
    (hm : maximumRounded M w ≤ optimum M (fun e => roundedWeight weightBase (w e)) /
      (8 * densityThreshold)) :
    thinningRate * retainedFraction / (16 * densityThreshold) *
      optimum M (fun e => roundedWeight weightBase (w e)) ≤ mainPayoff M hE w := by
  apply main_branch_from_filter Finset.univ
    (analyzedComparisonMass M (fun e => roundedLevel weightBase (w e)))
    (comparisonMass M (fun e => roundedLevel weightBase (w e)))
    (fun H => ∑ e ∈ candidateLabels M (fun e => roundedLevel weightBase (w e)) H,
      roundedWeight weightBase (w e))
    (fun H => mainMean ⟨H, ∅, ∅, ∅, false⟩
      (fun d => mainWorstRounded M hE d (fun e => roundedLevel weightBase (w e))))
    (optimum M (fun e => roundedWeight weightBase (w e))) (maximumRounded M w)
    (optimum_nonneg M _) hm
  · exact expectation_positiveGreedy_survivors M hE w (by norm_num [weightBase])
  · exact expectation_candidateLabels_le_optimum M hE w weightBase
  · intro H _
    exact small_comparison_mass M hE w H
  · intro H _
    exact conditional_main_payoff M hE ⟨H, ∅, ∅, ∅, false⟩ _

theorem complete_hidden_guarantee {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    ((2 : ℝ) ^ 293)⁻¹ * optimum M w ≤
      ∫ r, hiddenWorstReward (completeHiddenRule M hE) w r ∂sourceSeedLaw n := by
  let W := optimum M (fun e => roundedWeight weightBase (w e))
  have hb := branch_mixture_lower W (maximumRounded M w) (mainPayoff M hE w) (maximumPayoff M w)
    (optimum_nonneg M _) (maximumRounded_nonneg M w) (mainPayoff_nonneg M hE w)
    (maximum_branch_guarantee M w hw) (main_branch_guarantee_small M hE w)
  have hi := integrated_branch_lower M hE w hw
  have hr := optimum_rounding_bound M weightBase (by norm_num [weightBase]) w hw
  have hc0 : 0 ≤ thinningRate * retainedFraction / (32 * densityThreshold * weightBase) :=
    div_nonneg (mul_nonneg constants_positive.2.2.1.le constants_positive.2.2.2.2.le)
      (mul_nonneg (mul_nonneg (by norm_num) constants_positive.2.1.le) constants_positive.1.le)
  have hscaled := mul_le_mul_of_nonneg_left hr hc0
  have hcancel : thinningRate * retainedFraction / (32 * densityThreshold * weightBase) *
      (weightBase * W) = thinningRate * retainedFraction / (32 * densityThreshold) * W := by
    field_simp [ne_of_gt constants_positive.1, ne_of_gt constants_positive.2.1]
  rw [hcancel] at hscaled
  rw [hidden_fraction_exact] at hscaled
  exact hscaled.trans (hb.trans hi)

theorem hidden_vector : HiddenVectorChallenge := by
  intro n M hE
  refine ⟨mainSeedBits n, sourceSeedLaw n, inferInstance, completeHiddenRule M hE, ?_, ?_⟩
  · exact completeHiddenRule_feasible M hE
  · exact complete_hidden_guarantee M hE

theorem one_sample_oai.{u} : OneSampleChallenge.{u} :=
  hiddenVectorChallenge_implies_oneSampleChallenge hidden_vector

end MatroidProphet

end OAI
end
end

theorem solution : type_of% @OAI.MatroidProphet.one_sample_oai := @OAI.MatroidProphet.one_sample_oai
