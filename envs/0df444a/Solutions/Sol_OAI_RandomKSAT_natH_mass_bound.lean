-- Prove2me | solution 1 for OAI.RandomKSAT.natH_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:57:04.753982+00:00
-- url     : https://prove2.me/submissions/7a209488-3e6f-401f-a4fa-065b375e8bbb

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/Moments.lean:L26-L53
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.natH_mass_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Theorems.Thm_OAI_RandomKSAT_lt_firstFailure_iff
import Theorems.Thm_OAI_RandomKSAT_measurable_firstFailure

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

lemma frozen_singleton {n : ℕ} (a : Assignment n) : frozen {a} = Finset.univ := by
  ext v
  simp [frozen]

lemma clauseLaw_not_satisfies {n k : ℕ} (hkn : k ≤ n) (a : Assignment n) :
    clauseLaw n k {c | ¬ Satisfies c a} = ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  have he : {c : Clause n k | ¬ Satisfies c a} = {c | Kills {a} c} := by
    ext c
    simp [Kills]
  rw [he, clauseLaw_kills (Finset.singleton_nonempty a), frozen_singleton,
    Finset.card_univ, Fintype.card_fin]
  have hc : (n.choose k : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hkn).ne'
  rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc)
    (Or.inl (ENNReal.natCast_ne_top _)), ← mul_assoc,
    ENNReal.mul_inv_cancel hc (ENNReal.natCast_ne_top _), one_mul]

lemma clauseLaw_satisfies {n k : ℕ} (hkn : k ≤ n) (a : Assignment n) :
    clauseLaw n k {c | Satisfies c a} = 1 - ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  let := clauseLaw_probability n k hkn
  have he : {c : Clause n k | Satisfies c a} = {c | ¬ Satisfies c a}ᶜ := by
    ext c
    simp
  rw [he, measure_compl (Set.toFinite _).measurableSet (measure_ne_top _ _),
    measure_univ, clauseLaw_not_satisfies hkn]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FirstFailure ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma assignment_survival {n k : ℕ} (hkn : k ≤ n) (a : Assignment n) (m : ℕ) :
    streamLaw n k {ω | ∀ i < m, Satisfies (ω i) a} =
      (1 - ((2 : ℝ≥0∞) ^ k)⁻¹) ^ m := by
  let := clauseLaw_probability n k hkn
  have he : {ω : Stream n k | ∀ i < m, Satisfies (ω i) a} =
      Set.pi (Finset.range m) (fun _ => {c : Clause n k | Satisfies c a}) := by
    ext ω
    simp
  rw [he, streamLaw, Measure.infinitePi_pi]
  · simp [clauseLaw_satisfies hkn]
  · intro i _
    exact (Set.toFinite _).measurableSet

lemma first_moment_tail {n k : ℕ} (hkn : k ≤ n) (m : ℕ) :
    streamLaw n k {ω | (m : ℕ∞) < firstFailure ω} ≤
      (2 : ℝ≥0∞) ^ n * (1 - ((2 : ℝ≥0∞) ^ k)⁻¹) ^ m := by
  have he : {ω : Stream n k | (m : ℕ∞) < firstFailure ω} =
      ⋃ a : Assignment n, {ω | ∀ i < m, Satisfies (ω i) a} := by
    ext ω
    simp [lt_firstFailure_iff, PrefixSAT]
  rw [he]
  calc
    _ ≤ ∑ a : Assignment n, streamLaw n k {ω | ∀ i < m, Satisfies (ω i) a} :=
      measure_iUnion_fintype_le _ _
    _ = _ := by simp [assignment_survival hkn]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.BlockKilling ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma rate_toReal (s : ℕ) :
    (1-((2 : ℝ≥0∞)^s)⁻¹).toReal = 1-((2 : ℝ)^s)⁻¹ := by
  rw [ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr (one_le_pow₀ (by norm_num)))
    (by simp)]
  simp

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.Moments ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma real_rate_pos {k : ℕ} (hk : 1 ≤ k) : 0 < 1-((2 : ℝ)^k)⁻¹ := by
  have hp : (2 : ℝ) ≤ (2 : ℝ)^k := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
  exact sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr (by linarith))

lemma real_rate_lt_one (k : ℕ) : 1-((2 : ℝ)^k)⁻¹ < 1 := by
  have h : 0 < ((2 : ℝ)^k)⁻¹ := by positivity
  linarith

lemma measurable_natH (n k : ℕ) :
    Measurable (fun ω : Stream n k => (firstFailure ω).toNat) :=
  (measurable_of_countable fun x : ℕ∞ => x.toNat).comp (measurable_firstFailure n k)

lemma natH_mass_bound {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (m : ℕ) :
    ((streamLaw n k).map (fun ω => (firstFailure ω).toNat) {m}).toReal ≤
      ((2 : ℝ)^n/(1-((2 : ℝ)^k)⁻¹))*(1-((2 : ℝ)^k)⁻¹)^m := by
  let := streamLaw_probability n k hkn
  have hq := real_rate_pos hk
  rw [Measure.map_apply (measurable_natH n k) (by measurability)]
  cases m with
  | zero =>
    simp only [pow_zero, mul_one]
    apply (measureReal_le_one (μ := streamLaw n k)).trans
    apply (le_div_iff₀ hq).2
    have hp := one_le_pow₀ (n := n) (by norm_num : (1 : ℝ) ≤ 2)
    have hr := real_rate_lt_one k
    linarith
  | succ m =>
    have hs : (fun ω : Stream n k => (firstFailure ω).toNat) ⁻¹' {m+1} ⊆
        {ω | (m : ℕ∞) < firstFailure ω} := by
      intro ω hω
      have he : firstFailure ω = ((m+1 : ℕ) : ℕ∞) :=
        (ENat.toNat_eq_iff (by omega)).mp hω
      change (m : ℕ∞) < firstFailure ω
      rw [he]
      exact_mod_cast Nat.lt_succ_self m
    have hh := ENNReal.toReal_mono (by finiteness)
      ((measure_mono hs).trans (first_moment_tail hkn m))
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, rate_toReal] at hh
    apply hh.trans_eq
    rw [pow_succ, ← mul_assoc, mul_right_comm, div_mul_cancel₀ _ hq.ne']

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.natH_mass_bound := @_root_.OAI.RandomKSAT.natH_mass_bound
