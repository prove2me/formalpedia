-- Prove2me | solution 1 for OAI.RandomKSAT.one_replacement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:52:05.505832+00:00
-- url     : https://prove2.me/submissions/097ec127-687c-47f8-ab0e-e5284b57c4e1

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/BlockKilling.lean:L277-L293
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.one_replacement. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Theorems.Thm_OAI_RandomKSAT_killRatio_le_density_pow
import Theorems.Thm_OAI_RandomKSAT_replacement_numeric

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

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FrozenReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma killRatio_le_half_pow {u b s : ℕ} (hu : 0 < u) (hbu : b ≤ u) (hsu : s ≤ u) :
    killRatio u b s ≤ ((1 : ℝ)/2)^s := by
  apply (killRatio_le_density_pow hbu hsu).trans
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*u)).2
  have hb : (b : ℝ) ≤ u := by exact_mod_cast hbu
  nlinarith

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

lemma blockKill_nonneg (u s : ℕ) (S : Finset (Assignment u)) (g : ℕ) :
    0 ≤ blockKill u s S g := ENNReal.toReal_nonneg

lemma blockKill_empty {u s : ℕ} (hsu : s ≤ u) (g : ℕ) :
    blockKill u s ∅ g = 1 := by
  let := streamLaw_probability u s hsu
  simp [blockKill, SetSAT]

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

lemma blockKill_one {u s : ℕ} (hsu : s ≤ u) {S : Finset (Assignment u)} (hS : S.Nonempty) :
    blockKill u s S 1 = killRatio u (frozen S).card s := by
  let := clauseLaw_probability u s hsu
  have he : {ω : Stream u s | ¬ SetSAT S ω 1} =
      Set.pi ({0} : Finset ℕ) (fun _ => {c : Clause u s | Kills S c}) := by
    ext ω
    simp [SetSAT, Kills]
  rw [blockKill, he, streamLaw, Measure.infinitePi_pi]
  · simpa using clauseLaw_kills_toReal hS
  · intro _ _
    exact (Set.toFinite _).measurableSet

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

lemma set_survival_le {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (g : ℕ) :
    streamLaw u s {ω | SetSAT S ω g} ≤
      (S.card : ℝ≥0∞) * (1-((2 : ℝ≥0∞)^s)⁻¹)^g := by
  have he : {ω : Stream u s | SetSAT S ω g} =
      ⋃ a : S, {ω | ∀ i < g, Satisfies (ω i) a} := by
    ext ω
    simp [SetSAT]
  rw [he]
  apply (measure_iUnion_fintype_le _ _).trans_eq
  simp [assignment_survival hsu]

lemma frozen_card_le {u : ℕ} (S : Finset (Assignment u)) : (frozen S).card ≤ u := by
  simpa using Finset.card_le_univ (frozen S)

lemma rate_toReal (s : ℕ) :
    (1-((2 : ℝ≥0∞)^s)⁻¹).toReal = 1-((2 : ℝ)^s)⁻¹ := by
  rw [ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr (one_le_pow₀ (by norm_num)))
    (by simp)]
  simp

lemma real_rate_nonneg (s : ℕ) : 0 ≤ 1-((2 : ℝ)^s)⁻¹ := by
  exact sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num)))

lemma survival_exp_bound {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (g : ℕ) :
    (streamLaw u s {ω | SetSAT S ω g}).toReal ≤
      (S.card : ℝ) * Real.exp (-((2 : ℝ)^s)⁻¹ * g) := by
  have ht := ENNReal.toReal_mono (by finiteness) (set_survival_le hsu S g)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow, rate_toReal] at ht
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have he : 1-((2 : ℝ)^s)⁻¹ ≤ Real.exp (-((2 : ℝ)^s)⁻¹) := by
    linarith [Real.add_one_le_exp (-((2 : ℝ)^s)⁻¹)]
  calc
    _ ≤ (Real.exp (-((2 : ℝ)^s)⁻¹))^g := pow_le_pow_left₀ (real_rate_nonneg s) he g
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma blockKill_exp_full {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (g : ℕ) :
    1 - (2 : ℝ)^u * Real.exp (-((2 : ℝ)^s)⁻¹ * g) ≤ blockKill u s S g := by
  have hScard : (S.card : ℝ) ≤ (2 : ℝ)^u := by
    exact_mod_cast (by simpa using Finset.card_le_univ S : S.card ≤ 2^u)
  have ht := (survival_exp_bound hsu S g).trans
    (mul_le_mul_of_nonneg_right hScard (Real.exp_nonneg _))
  rw [blockKill_compl hsu]
  linarith

lemma blockKill_exp_individual {u s : ℕ} (hu : 0 < u) (hsu : s ≤ u)
    {S : Finset (Assignment u)} (hS : S.Nonempty) (g : ℕ) :
    1 - Real.exp (-(g : ℝ)*killRatio u (frozen S).card s) ≤ blockKill u s S g := by
  have hk : killRatio u (frozen S).card s ≤ 1 :=
    (killRatio_le_half_pow hu (frozen_card_le S) hsu).trans
      (pow_le_one₀ (by norm_num) (by norm_num))
  have he : 1-killRatio u (frozen S).card s ≤
      Real.exp (-killRatio u (frozen S).card s) := by
    linarith [Real.add_one_le_exp (-killRatio u (frozen S).card s)]
  have ht := pow_le_pow_left₀ (sub_nonneg.mpr hk) he g
  rw [← Real.exp_nat_mul] at ht
  have hm := blockKill_individual hsu hS g
  have hx : (g : ℝ) * (-killRatio u (frozen S).card s) =
      -(g : ℝ) * killRatio u (frozen S).card s := by ring
  rw [hx] at ht
  exact le_trans (sub_le_sub_left ht 1) hm

lemma blockKill_long {u s g : ℕ} (hu : 0 < u) (hsu : s ≤ u)
    (hg : (2 : ℝ)^(s+1)*u ≤ g) (S : Finset (Assignment u)) :
    (1 : ℝ)/3 ≤ blockKill u s S g := by
  have he : -((2 : ℝ)^s)⁻¹ * g ≤ -2*u := by
    have h2 : (0 : ℝ) < (2 : ℝ)^s := by positivity
    rw [pow_succ] at hg
    have h := mul_le_mul_of_nonneg_left hg (le_of_lt (inv_pos.mpr h2))
    have hc : ((2 : ℝ)^s)⁻¹ * ((2:ℝ)^s*2*u) = 2*u := by field_simp
    rw [hc] at h
    linarith
  have hexp : (2 : ℝ)*Real.exp (-2) ≤ 2/3 := by
    have ht : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    have hi := inv_anti₀ (by norm_num : (0 : ℝ)<3) ht
    rw [Real.exp_neg]
    linarith
  have hh : (2 : ℝ)^u * Real.exp (-2*u) ≤ 2/3 := by
    have hi : (1 : ℕ) ≤ u := hu
    calc
      _ = (2*Real.exp (-2))^u := by rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
      _ ≤ ((2 : ℝ)/3)^u := pow_le_pow_left₀ (by positivity) hexp u
      _ ≤ ((2 : ℝ)/3)^1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
      _ = _ := by norm_num
  have hb := blockKill_exp_full hsu S g
  have ht := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (by positivity : (0 : ℝ) ≤ (2:ℝ)^u)
  linarith

lemma replacementK_succ (r : ℕ) : replacementK (r+1) = ((2 : ℝ)^(r+1)*r)^r := by
  simp [replacementK]

lemma one_replacement {u r g : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hg : 1 ≤ g)
    (S : Finset (Assignment u)) :
    blockKill u r S 1 - replacementK (r+1)/(g : ℝ)^r ≤ blockKill u (r+1) S g := by
  by_cases hS : S.Nonempty
  · rw [blockKill_one (by omega) hS]
    apply replacement_numeric hr (frozen_card_le S) hru hg (blockKill_nonneg _ _ _ _)
    · exact blockKill_exp_individual (by omega) hru hS g
    · intro hlong
      apply blockKill_long (by omega) hru _ S
      simpa [Nat.add_assoc] using hlong
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rw [blockKill_empty (by omega), blockKill_empty hru]
    have hK : 0 ≤ replacementK (r+1)/(g : ℝ)^r := by
      rw [replacementK_succ]
      positivity
    linarith

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.one_replacement := @_root_.OAI.RandomKSAT.one_replacement
