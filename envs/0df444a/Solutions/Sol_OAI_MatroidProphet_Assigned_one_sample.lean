-- Prove2me | solution 1 for OAI.MatroidProphet.Assigned.one_sample
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:28:49.84991+00:00
-- url     : https://prove2.me/submissions/112570a8-d35c-45e0-9715-071f5805d550

import Mathlib
import Definitions.Def_MatroidSecretary
import Definitions.Def_OAIW2MS000
import Theorems.Thm_OAI_MatroidProphet_MainAlgorithm_conditional_main_payoff

section
-- module Solutions.OAIW2_MatroidSec.Compat
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Basic
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set

variable {α : Type*} [Fintype α]

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

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Guarded
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

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

lemma guarded_subset_nominal (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    guardedPath M hE κ D C h k ⊆ nominalPath M hE κ D C h k :=
  densityEnabled_extensive M hE κ (D h) (activation h) k _

lemma nominal_subset_guarded (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    nominalPath M hE κ D C h k ⊆ guardedPath M hE κ D C (h+1) k :=
  subset_union_left.trans (M.subset_closure _ (by simp [hE]))

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Birth
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

lemma nominalBirth_mem (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    e ∈ nominalPath M hE κ D C h (nominalBirth M hE κ D C h e) :=
  Nat.find_spec (exists_nominal_member M hE κ D C h e)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_LayerGreedy
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma layerGreedy_subset (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ) :
    layerGreedy M E base layer time ⊆ E := by
  classical
  exact filter_subset _ _

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

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Constants
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

noncomputable section

theorem constants_positive : 0 < weightBase ∧ 0 < densityThreshold ∧
    0 < thinningRate ∧ 0 < exitThreshold ∧ 0 < retainedFraction := by
  norm_num [weightBase, densityThreshold, thinningRate, exitThreshold, retainedFraction]

theorem retained_fraction_slack :
    retainedFraction / 8 ≤ retainedFraction / 4 - ((2 : ℝ) ^ 21)⁻¹ := by
  norm_num [retainedFraction]

theorem hidden_fraction_exact :
    thinningRate * retainedFraction / (32 * densityThreshold * weightBase) =
      ((2 : ℝ) ^ 293)⁻¹ := by
  rw [show 293 = 140 + 153 from rfl, pow_add]
  norm_num [thinningRate, retainedFraction, densityThreshold, weightBase]

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Information
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.bernoulliSeedLaw_probability _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace MatroidProphet

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Rounding
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open MeasureTheory

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_LayerOnline
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.bernoulliSeedLaw_probability _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Feasible
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.bernoulliSeedLaw_probability _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_FiniteBits
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

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

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_GreedyScan
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α β : Type*} [Fintype β] [DecidableEq β]

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Probability
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

lemma bitsExpectation_mul_const (q : α → ℝ) (V : Finset α) (c : ℝ) (f : Finset α → ℝ) :
    bitsExpectation q V (fun S => c * f S) = c * bitsExpectation q V f := by
  simp only [bitsExpectation, mul_sum]
  apply sum_congr rfl
  intro S hS
  ring

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Transfer
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

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

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Cost
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

@[simp] lemma reverseMeanCost_zero (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) (k : ℤ) (S : ℕ → Set α) :
    reverseMeanCost M hE κ D G n q cost 0 k S = 0 := by
  simp only [reverseMeanCost, reverseCost, bitsExpectation_const]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Global
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma tripleMaskExpectation_const (p q r : α → ℝ) (V : Finset α) (c : ℝ) :
    tripleMaskExpectation p q r V (fun _ _ _ => c) = c := by
  simp only [tripleMaskExpectation, bitsExpectation_const]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Mean
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

namespace MainAlgorithm
variable {n : ℕ}

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

end MainAlgorithm
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Observed
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.bernoulliSeedLaw_probability _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_SeedLaw
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_SeedLaw
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Selection
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.bernoulliSeedLaw_probability _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset
variable {n : ℕ}

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_WeightedAccounting
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Worst
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.bernoulliSeedLaw_probability _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset

namespace MainAlgorithm
variable {n : ℕ}

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Candidates
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Finset Set

namespace MatroidProphet
namespace Candidates

variable {n : ℕ}

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Maximum_Basic
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.bernoulliSeedLaw_probability _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Maximum

open MeasureTheory Finset Set

variable {n bits : ℕ} {K : Type*} [Countable K] [MeasurableSpace K]
  [MeasurableSingletonClass K]

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

lemma maximumRule_feasible [LinearOrder K] (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) : Feasible M (maximumRule M key hkey active mask) :=
  firstRule_feasible M key hkey _ (fun _ _ _ hx => hx.2.1)

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Maximum_Probability
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Simulation
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.bernoulliSeedLaw_probability _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory

namespace MatroidProphet

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Maximum_Guarantee
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_GreedyOptimal
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Candidates

open Finset Set

variable {n : ℕ}

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

lemma priorityTime_injective (order : ArrivalOrder n) : Function.Injective (priorityTime order) := by
  intro a b h
  exact order.symm.injective (Fin.ext h)

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Priority
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

open Finset Set

variable {n : ℕ}

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_BranchMix
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open MeasureTheory

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Maximum_Score
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_CandidateFilter
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset Set

variable {n : ℕ}

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_WeightGroups
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {n : ℕ}

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

lemma weightLevels_mono (a : Fin n → Option ℤ) {U V : Finset (Fin n)} (h : U ⊆ V) :
    weightLevels a U ⊆ weightLevels a V := by
  intro i hi
  obtain ⟨e, he, hi⟩ := (mem_weightLevels a U i).1 hi
  exact (mem_weightLevels a V i).2 ⟨e, h he, hi⟩

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_WeightedPayoff
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_AnalyzedMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset

variable {n : ℕ}

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Maximum_Mask
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Seed
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_CompletePayoff
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset MainAlgorithm

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Gluing
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.bernoulliSeedLaw_probability _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reduction
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability _root_.OAI.MatroidProphet.bernoulliSeedLaw_probability _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability _root_.OAI.MatroidProphet.sourceSeedLaw_probability _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Main
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

theorem one_sample.{u} : OneSampleChallenge.{u} :=
  hiddenVectorChallenge_implies_oneSampleChallenge hidden_vector

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidSecretary_Secretary_Seed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise and probabilistic preservation of the complete secretary seed. -/

open MeasureTheory ProbabilityTheory
namespace MatroidProphet

section Reindex
variable {n : ℕ} {Q Q' : Type*} [MeasurableSpace Q] [MeasurableSpace Q']
    (A : SecretaryRule n Q) (f : Q' → Q) (hf : Measurable f)

@[simp] theorem reindexSecretarySeed_prefixLength (q : Q') :
    (reindexSecretarySeed A f hf).prefixLength q = A.prefixLength (f q) := rfl

@[simp] theorem reindexSecretarySeed_decisionAt (q : Q') (w : Weights n)
    (π : ArrivalOrder n) (k : Fin n) :
    secretaryDecisionAt (reindexSecretarySeed A f hf) q w π k =
      secretaryDecisionAt A (f q) w π k := rfl

@[simp] theorem reindexSecretarySeed_acceptedThrough (q : Q') (w : Weights n)
    (π : ArrivalOrder n) (t : ℕ) :
    secretaryAcceptedThrough (reindexSecretarySeed A f hf) q w π t =
      secretaryAcceptedThrough A (f q) w π t := rfl

@[simp] theorem reindexSecretarySeed_reward (q : Q') (w : Weights n)
    (π : ArrivalOrder n) :
    secretaryReward (reindexSecretarySeed A f hf) q w π =
      secretaryReward A (f q) w π := rfl

end Reindex

section Finite
variable {n : ℕ} {Q : Type*} [Fintype Q] [MeasurableSpace Q]
    (A : SecretaryRule n Q)

@[simp] theorem secretaryFinSeed_prefixLength (q : Q) :
    (secretaryFinSeed A).prefixLength ((Fintype.equivFin Q) q) = A.prefixLength q := by
  simp [secretaryFinSeed, reindexSecretarySeed]

@[simp] theorem secretaryFinSeed_decisionAt (q : Q) (w : Weights n)
    (π : ArrivalOrder n) (k : Fin n) :
    secretaryDecisionAt (secretaryFinSeed A) ((Fintype.equivFin Q) q) w π k =
      secretaryDecisionAt A q w π k := by
  simp [secretaryFinSeed, reindexSecretarySeed_decisionAt]

@[simp] theorem secretaryFinSeed_acceptedThrough (q : Q) (w : Weights n)
    (π : ArrivalOrder n) (t : ℕ) :
    secretaryAcceptedThrough (secretaryFinSeed A) ((Fintype.equivFin Q) q) w π t =
      secretaryAcceptedThrough A q w π t := by
  simp [secretaryFinSeed, reindexSecretarySeed_acceptedThrough]

@[simp] theorem secretaryFinSeed_reward (q : Q) (w : Weights n) (π : ArrivalOrder n) :
    secretaryReward (secretaryFinSeed A) ((Fintype.equivFin Q) q) w π =
      secretaryReward A q w π := by
  simp [secretaryFinSeed, reindexSecretarySeed_reward]

variable [MeasurableSingletonClass Q]

instance secretaryFinSeedLaw_isProbability (ν : Measure Q) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (secretaryFinSeedLaw ν) := by
  unfold secretaryFinSeedLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

end Finite

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidSecretary_Contracts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Assigned

open Finset MainAlgorithm MeasureTheory
attribute [local instance] Classical.propDecidable

theorem one_sample_oai.{u} : MatroidProphet.OneSampleChallenge.{u} :=
  MatroidProphet.one_sample

end MatroidProphet.Assigned

end OAI
end

theorem solution.{u} : type_of% @OAI.MatroidProphet.Assigned.one_sample_oai.{u} := @OAI.MatroidProphet.Assigned.one_sample_oai.{u}
