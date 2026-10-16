-- Prove2me | solution 1 for OAI.RandomKSAT.blockKill_individual
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T15:30:59.971156+00:00
-- url     : https://prove2.me/submissions/95ec808c-c7dc-4193-9800-20fa9ebf38c7

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/BlockKilling.lean:L76-L96
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.blockKill_individual. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement

-- ---- from OAI.Probability.SATVariance.ClauseCombinatorics ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma support_card (n k : ℕ) :
    Fintype.card {s : Finset (Fin n) // s.card = k} = n.choose k := by
  classical
  rw [Fintype.card_of_subtype ((Finset.univ : Finset (Fin n)).powersetCard k)
    (by intro s; simp)]
  simp

lemma clause_card (n k : ℕ) : Fintype.card (Clause n k) = n.choose k * 2 ^ k := by
  classical
  change Fintype.card ((s : {s : Finset (Fin n) // s.card = k}) × (s.1 → Bool)) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  trans ∑ _ : {s : Finset (Fin n) // s.card = k}, 2 ^ k
  · apply Finset.sum_congr rfl
    intro s _
    rw [s.property]
  · rw [Finset.sum_const, Finset.card_univ, support_card, smul_eq_mul]

lemma clause_nonempty (n k : ℕ) (hkn : k ≤ n) : Nonempty (Clause n k) := by
  rw [← Fintype.card_pos_iff, clause_card]
  exact Nat.mul_pos (Nat.choose_pos hkn) (pow_pos (by decide) _)

lemma clauseLaw_probability (n k : ℕ) (hkn : k ≤ n) :
    IsProbabilityMeasure (clauseLaw n k) := by
  let := clause_nonempty n k hkn
  unfold clauseLaw
  infer_instance

lemma streamLaw_probability (n k : ℕ) (hkn : k ≤ n) :
    IsProbabilityMeasure (streamLaw n k) := by
  let := clauseLaw_probability n k hkn
  unfold streamLaw
  infer_instance

lemma killing_card {n k : ℕ} {S : Finset (Assignment n)} (hS : S.Nonempty) :
    Fintype.card {c : Clause n k // Kills S c} = (frozen S).card.choose k := by
  classical
  obtain ⟨a₀, ha₀⟩ := hS
  rw [Fintype.card_congr (killingEquiv ha₀)]
  rw [Fintype.card_of_subtype ((frozen S).powersetCard k) (by intro s; simp)]
  exact Finset.card_powersetCard _ _

lemma count_set_fintype.{u_1} {α : Type u_1} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] (s : Set α) :
    Measure.count s = (Fintype.card s : ℝ≥0∞) := by
  rw [Measure.count_apply (Set.toFinite s).measurableSet,
    Set.encard_eq_coe_toFinset_card]
  simp

lemma clauseLaw_kills {n k : ℕ} {S : Finset (Assignment n)} (hS : S.Nonempty) :
    clauseLaw n k {c | Kills S c} =
      ((frozen S).card.choose k : ℝ≥0∞) / ((n.choose k : ℝ≥0∞) * 2 ^ k) := by
  rw [clauseLaw, uniformOn_univ, count_set_fintype]
  have hc : Fintype.card ↑{c : Clause n k | Kills S c} = (frozen S).card.choose k := by
    simpa only [Fintype.card_subtype, Set.mem_ofPred_eq] using (killing_card hS)
  rw [hc, clause_card]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.BlockKilling ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma measurableSet_setSAT (u s : ℕ) (S : Finset (Assignment u)) (g : ℕ) :
    MeasurableSet {ω : Stream u s | SetSAT S ω g} := by
  simp only [SetSAT, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro a
  by_cases ha : a ∈ S
  · simp only [ha, true_and, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro _
    exact (Set.toFinite {c : Clause u s | Satisfies c a}).measurableSet.preimage
      (measurable_pi_apply i)
  · simp only [ha, false_and, Set.ofPred_false]
    exact MeasurableSet.empty

lemma blockKill_compl {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (g : ℕ) :
    blockKill u s S g = 1 - (streamLaw u s {ω | SetSAT S ω g}).toReal := by
  let := streamLaw_probability u s hsu
  have he : {ω : Stream u s | ¬ SetSAT S ω g} = {ω | SetSAT S ω g}ᶜ := rfl
  rw [blockKill, he, measure_compl (measurableSet_setSAT u s S g) (measure_ne_top _ _),
    measure_univ, ENNReal.toReal_sub_of_le prob_le_one (by simp), ENNReal.toReal_one]

lemma clauseLaw_kills_toReal {u s : ℕ} {S : Finset (Assignment u)} (hS : S.Nonempty) :
    (clauseLaw u s {c | Kills S c}).toReal = killRatio u (frozen S).card s := by
  rw [clauseLaw_kills hS]
  simp [killRatio, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, mul_comm]

lemma blockKill_individual {u s : ℕ} (hsu : s ≤ u) {S : Finset (Assignment u)}
    (hS : S.Nonempty) (g : ℕ) :
    1 - (1 - killRatio u (frozen S).card s)^g ≤ blockKill u s S g := by
  let := clauseLaw_probability u s hsu
  let := streamLaw_probability u s hsu
  have hsub : {ω : Stream u s | SetSAT S ω g} ⊆
      Set.pi (Finset.range g) (fun _ => {c : Clause u s | ¬ Kills S c}) := by
    rintro ω ⟨a, ha, hω⟩ i hi hk
    exact hk a ha (hω i (Finset.mem_range.mp hi))
  have ht := measure_mono (μ := streamLaw u s) hsub
  rw [streamLaw, Measure.infinitePi_pi _ (fun _ _ => (Set.toFinite _).measurableSet)] at ht
  have he : clauseLaw u s {c | ¬ Kills S c} = 1-clauseLaw u s {c | Kills S c} := by
    exact (measure_compl (Set.toFinite _).measurableSet (measure_ne_top _ _)).trans
      (by rw [measure_univ]; rfl)
  simp only [he, Finset.prod_const, Finset.card_range] at ht
  have ht' := ENNReal.toReal_mono (by finiteness) ht
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le prob_le_one (by simp),
    ENNReal.toReal_one, clauseLaw_kills_toReal hS] at ht'
  rw [blockKill_compl hsu]
  change ((streamLaw u s) {ω | SetSAT S ω g}).toReal ≤ _ at ht'
  linarith

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.blockKill_individual := @_root_.OAI.RandomKSAT.blockKill_individual
