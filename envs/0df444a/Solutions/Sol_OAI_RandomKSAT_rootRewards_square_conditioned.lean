-- Prove2me | solution 1 for OAI.RandomKSAT.rootRewards_square_conditioned
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:26:28.045426+00:00
-- url     : https://prove2.me/submissions/e0037838-c77d-45c9-8d38-ae2e72b1efb0

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/WeightedRewards.lean:L347-L384
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.rootRewards_square_conditioned. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Theorems.Thm_OAI_RandomKSAT_forcedPrefix_probability
import Theorems.Thm_OAI_RandomKSAT_integrated_occupationReward
import Theorems.Thm_OAI_RandomKSAT_lifetime_product
import Theorems.Thm_OAI_RandomKSAT_pairEvolution_fibre_operator
import Theorems.Thm_OAI_RandomKSAT_pathReward_sq_potential
import Theorems.Thm_OAI_RandomKSAT_rootPath_eq_rewards

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

lemma blockKill_le_one {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (g : ℕ) :
    blockKill u s S g ≤ 1 := by
  let := streamLaw_probability u s hsu
  exact measureReal_le_one (μ := streamLaw u s)

lemma blockKill_compl {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (g : ℕ) :
    blockKill u s S g = 1 - (streamLaw u s {ω | SetSAT S ω g}).toReal := by
  let := streamLaw_probability u s hsu
  have he : {ω : Stream u s | ¬ SetSAT S ω g} = {ω | SetSAT S ω g}ᶜ := rfl
  rw [blockKill, he, measure_compl (measurableSet_setSAT u s S g) (measure_ne_top _ _),
    measure_univ, ENNReal.toReal_sub_of_le prob_le_one (by simp), ENNReal.toReal_one]

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

lemma rate_toReal (s : ℕ) :
    (1-((2 : ℝ≥0∞)^s)⁻¹).toReal = 1-((2 : ℝ)^s)⁻¹ := by
  rw [ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr (one_le_pow₀ (by norm_num)))
    (by simp)]
  simp

lemma real_rate_nonneg (s : ℕ) : 0 ≤ 1-((2 : ℝ)^s)⁻¹ := by
  exact sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num)))

lemma replacementK_succ (r : ℕ) : replacementK (r+1) = ((2 : ℝ)^(r+1)*r)^r := by
  simp [replacementK]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_mono.{u_1} {α : Type u_1} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    favg f ≤ favg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

lemma favg_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (c : ℝ) :
    favg (fun _ : α => c) = c := by
  simp [favg, Fintype.card_ne_zero]

lemma favg_add.{u_1} {α : Type u_1} [Fintype α] (f g : α → ℝ) :
    favg (fun a => f a + g a) = favg f + favg g := by
  simp only [favg, Finset.sum_add_distrib, add_div]

lemma favg_equiv.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    favg (fun a => f (e a)) = favg f := by
  rw [favg, favg, e.sum_comp f, Fintype.card_congr e]

lemma favg_comm.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    favg (fun a => favg (f a)) = favg (fun b => favg (fun a => f a b)) := by
  simp only [favg, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

lemma favg_prod.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    favg f = favg (fun a => favg fun b => f (a,b)) := by
  simp only [favg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

lemma uniformOn_real.{u_1} {α : Type u_1} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (s : Set α) :
    (uniformOn Set.univ s).toReal = favg (fun a => if a ∈ s then 1 else 0) := by
  rw [uniformOn_univ, count_set_fintype]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, favg]
  congr 1
  simp [Fintype.card_subtype]

lemma prefixLaw {u s : ℕ} (hsu : s ≤ u) (m : ℕ) :
    (streamLaw u s).map (fun ω (i : Fin m) => ω i) =
      uniformOn (Set.univ : Set (Fin m → Clause u s)) := by
  let := clauseLaw_probability u s hsu
  rw [streamLaw, Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
    Measure.infinitePi_eq_pi]
  simpa only [Set.pi_univ, clauseLaw] using
    (uniformOn_pi (f := fun _ : Fin m => (Set.univ : Set (Clause u s)))).symm

lemma residual_cons {u s m : ℕ} (S : Finset (Assignment u)) (c : Clause u s)
    (cs : Fin m → Clause u s) :
    residual S (Fin.cons c cs) = residual (S.filter (Satisfies c)) cs := by
  ext a
  simp [residual, Fin.forall_fin_succ, and_assoc]

lemma clauseStep_mono (u s : ℕ) : Monotone (clauseStep u s) := by
  intro f g h S
  exact favg_mono fun c => h _

lemma clauseStep_const {u s : ℕ} (hsu : s ≤ u) (c : ℝ) :
    clauseStep u s (fun _ => c) = fun _ => c := by
  let := clause_nonempty u s hsu
  funext S
  exact favg_const c

lemma clauseStep_iterate_avg (u s m : ℕ) (f : Finset (Assignment u) → ℝ)
    (S : Finset (Assignment u)) :
    (clauseStep u s)^[m] f S = favg (fun cs : Fin m → Clause u s => f (residual S cs)) := by
  induction m generalizing S with
  | zero => simp [residual, favg]
  | succ m ih =>
    rw [Function.iterate_succ_apply', clauseStep]
    simp_rw [ih]
    rw [← favg_prod (fun p : Clause u s × (Fin m → Clause u s) =>
      f (residual (S.filter (Satisfies p.1)) p.2)),
      ← favg_equiv (Fin.consEquiv (fun _ : Fin (m+1) => Clause u s))]
    congr 1
    funext p
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, residual_cons]

lemma blockKill_iterate {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (m : ℕ) :
    blockKill u s S m = 1 - (clauseStep u s)^[m] (alive u) S := by
  rw [blockKill_compl hsu, clauseStep_iterate_avg]
  congr 1
  have he : {ω : Stream u s | SetSAT S ω m} =
      (fun ω (i : Fin m) => ω i) ⁻¹' {cs | (residual S cs).Nonempty} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetSAT, residual,
      Finset.Nonempty, Finset.mem_filter]
    exact exists_congr fun a => and_congr_right fun _ => (Fin.forall_iff (p := fun i : Fin m => Satisfies (ω i) a)).symm
  rw [he, ← Measure.map_apply (by fun_prop) (Set.toFinite _).measurableSet, prefixLaw hsu,
    uniformOn_real]
  simp only [alive, Set.mem_ofPred_eq]
  congr 1
  funext cs
  split_ifs <;> rfl

lemma favg_mul.{u_1} {α : Type u_1} [Fintype α] (c : ℝ) (f : α → ℝ) :
    favg (fun a => c*f a) = c*favg f := by
  simp only [favg, ← Finset.mul_sum]
  ring

lemma favg_nonneg.{u_1} {α : Type u_1} [Fintype α] {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ favg f := by
  exact div_nonneg (Finset.sum_nonneg fun a _ => h a) (by positivity)

lemma residual_mono.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι]
    {S T : Finset (Assignment u)} (h : S ⊆ T) (cs : ι → Clause u s) :
    residual S cs ⊆ residual T cs := Finset.filter_subset_filter _ h

lemma alive_nonneg (u : ℕ) (S : Finset (Assignment u)) : 0 ≤ alive u S := by
  unfold alive
  split_ifs <;> norm_num

lemma alive_le_one (u : ℕ) (S : Finset (Assignment u)) : alive u S ≤ 1 := by
  unfold alive
  split_ifs <;> norm_num

lemma alive_mono {u : ℕ} {S T : Finset (Assignment u)} (h : S ⊆ T) :
    alive u S ≤ alive u T := by
  unfold alive
  by_cases hS : S.Nonempty
  · simp [hS, hS.mono h]
  · simp only [hS, ite_false]
    split_ifs <;> norm_num

lemma survival_avg (u s : ℕ) (S : Finset (Assignment u)) (m : ℕ) :
    survival u s S m = favg fun cs : Fin m → Clause u s => alive u (residual S cs) :=
  clauseStep_iterate_avg _ _ _ _ _

lemma survival_nonneg (u s : ℕ) (S : Finset (Assignment u)) (m : ℕ) :
    0 ≤ survival u s S m := by
  rw [survival_avg]
  exact favg_nonneg fun _ => alive_nonneg _ _

lemma survival_mono {u s : ℕ} {S T : Finset (Assignment u)} (h : S ⊆ T) (m : ℕ) :
    survival u s S m ≤ survival u s T m := by
  rw [survival_avg, survival_avg]
  exact favg_mono fun _ => alive_mono (residual_mono h _)

lemma survival_eq_prob {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (m : ℕ) :
    survival u s S m = (streamLaw u s {ω | SetSAT S ω m}).toReal := by
  have h := blockKill_iterate hsu S m
  rw [blockKill_compl hsu] at h
  change _ = 1 - survival u s S m at h
  linarith

lemma survival_summable {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) :
    Summable (survival u s S) := by
  have hr : 1-((2 : ℝ)^s)⁻¹ < 1 := by
    have h : 0 < ((2 : ℝ)^s)⁻¹ := by positivity
    linarith
  apply Summable.of_nonneg_of_le (survival_nonneg u s S) _
    ((summable_geometric_of_lt_one (real_rate_nonneg s) hr).mul_left (S.card : ℝ))
  intro m
  rw [survival_eq_prob hsu]
  have h := ENNReal.toReal_mono (by finiteness) (set_survival_le hsu S m)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow, rate_toReal] using h

lemma lifetime_nonneg (u s : ℕ) (S : Finset (Assignment u)) : 0 ≤ lifetime u s S :=
  tsum_nonneg (survival_nonneg u s S)

lemma replacementK_one_le {r : ℕ} (hr : 1 ≤ r) : 1 ≤ replacementK (r+1) := by
  rw [replacementK_succ]
  apply one_le_pow₀
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (by exact_mod_cast hr)

lemma lifetimeBeta_succ {r : ℕ} (hr : 0 < r) : lifetimeBeta (r+1) = 1+(r : ℝ)⁻¹ := by
  simp only [lifetimeBeta, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hr₀ : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  field_simp

lemma lifetimeC_pos {r : ℕ} (hr : 1 ≤ r) : 0 < lifetimeC (r+1) := by
  have hK := replacementK_one_le hr
  unfold lifetimeC
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FiniteVariance ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_sum.{u_1, u_2} {α : Type u_1} {ι : Type u_2} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    favg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, favg (f i) := by
  simp only [favg, Finset.sum_div]
  exact Finset.sum_comm

lemma favg_cons.{u_1} {α : Type u_1} [Fintype α] {m : ℕ} (f : (Fin (m+1) → α) → ℝ) :
    favg f = favg (fun t : Fin m → α => favg (fun a : α => f (Fin.cons a t))) := by
  rw [← favg_equiv (Fin.consEquiv (fun _ : Fin (m+1) => α)) f, favg_prod, favg_comm]
  rfl

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.LifetimePotential ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_tsum.{u_1} {α : Type u_1} [Fintype α] (f : α → ℕ → ℝ)
    (hf : ∀ a, Summable (f a)) :
    favg (fun a => ∑' m, f a m) = ∑' m, favg (fun a => f a m) := by
  unfold favg
  rw [← Summable.tsum_finsetSum (fun a _ => hf a), tsum_div_const]

lemma lifetime_mono {u s : ℕ} (hsu : s ≤ u) {S T : Finset (Assignment u)} (hST : S ⊆ T) :
    lifetime u s S ≤ lifetime u s T := by
  exact Summable.tsum_le_tsum (survival_mono hST) (survival_summable hsu S)
    (survival_summable hsu T)

lemma lifetime_bellman {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) :
    lifetime u s S = alive u S + clauseStep u s (lifetime u s) S := by
  unfold clauseStep
  simp_rw [lifetime]
  rw [favg_tsum _ (fun _ => survival_summable hsu _)]
  have hs := survival_summable hsu S
  rw [tsum_eq_zero_add' (hs.comp_injective (fun _ _ h => Nat.add_right_cancel h))]
  congr 1
  congr 1
  funext m
  change (clauseStep u s)^[m+1] (alive u) S = _
  rw [Function.iterate_succ_apply']
  rfl

lemma markovSum_mono.{u_1} {X : Type u_1} (P : ℕ → (X → ℝ) → X → ℝ)
    (hP : ∀ i, Monotone (P i)) {f g : X → ℝ} (hfg : f ≤ g) (m : ℕ) :
    markovSum P f m ≤ markovSum P g m := by
  induction m generalizing P with
  | zero => exact le_rfl
  | succ m ih =>
    intro x
    exact add_le_add (hfg x) (hP 0 (ih _ (fun i => hP (i+1))) x)

lemma scheduledStep_mono (u k : ℕ) (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ) :
    Monotone (scheduledStep u k ordinary mask i) := by
  intro f g h S
  unfold scheduledStep
  split
  · exact clauseStep_mono u k h S
  · exact h _

lemma scheduledStep_const {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ) (c : ℝ) :
    scheduledStep u k ordinary mask i (fun _ => c) = fun _ => c := by
  funext S
  unfold scheduledStep
  split
  · exact congrFun (clauseStep_const hku c) S
  · rfl

lemma scheduledStep_drift {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ) (S : Finset (Assignment u)) :
    alive u S + scheduledStep u k ordinary mask i (lifetime u k) S ≤
      lifetime u k S + if ordinary i then 0 else 1 := by
  unfold scheduledStep
  split
  · simpa using (lifetime_bellman hku S).ge
  · have ht := lifetime_mono hku (Finset.inter_subset_left : S ∩ mask i ⊆ S)
    have hf := alive_le_one u S
    linarith

lemma markovSum_const.{u_1} {X : Type u_1} (P : ℕ → (X → ℝ) → X → ℝ)
    (hPc : ∀ i c, P i (fun _ => c) = fun _ => c) (c : ℝ) (m : ℕ) :
    markovSum P (fun _ => c) m = fun _ => m*c := by
  induction m generalizing P with
  | zero => funext x; simp [markovSum]
  | succ m ih =>
    funext x
    simp only [markovSum, ih _ (fun i => hPc (i+1)), hPc]
    push_cast
    ring

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FiberRefresh ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma pathReward_avg.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] [Nonempty α]
    (step : ℕ → α → X → X) (f : X → ℝ) (m : ℕ) (x : X) :
    favg (fun z : Fin m → α => pathReward step f m z x) =
      markovSum (uniformStep step) f m x := by
  induction m generalizing step x with
  | zero => simp [pathReward, markovSum, favg_const]
  | succ m ih =>
    rw [favg_cons, favg_comm]
    simp only [pathReward, Fin.cons_zero, Fin.tail_cons, favg_add, favg_const]
    simp_rw [ih]
    rfl

lemma markovSum_mul.{u_1} {X : Type u_1} (P : ℕ → (X → ℝ) → X → ℝ)
    (hP : ∀ i c f, P i (fun x => c*f x) = fun x => c*P i f x)
    (c : ℝ) (f : X → ℝ) (m : ℕ) :
    markovSum P (fun x => c*f x) m = fun x => c*markovSum P f m x := by
  induction m generalizing P with
  | zero => funext x; simp [markovSum]
  | succ m ih =>
    rw [markovSum, ih _ (fun i => hP (i+1)), hP]
    funext x
    simp only [markovSum]
    ring

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.PairEvolution ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma rootSatisfies_zero {k : ℕ} (t : RootType k) (h : rootSize t = 0) (a : Assignment k) :
    ¬ RootSatisfies t a := by
  rintro ⟨j,hj⟩
  have hm : j ∈ rootSupport t := by simp [rootSupport, hj]
  have he : rootSupport t = ∅ := Finset.card_eq_zero.mp h
  rw [he] at hm
  exact Finset.notMem_empty j hm

lemma satisfies_cast {u s t : ℕ} (h : s = t) (c : Clause u s) (b : Assignment u) :
    Satisfies (clauseCastEquiv h c) b ↔ Satisfies c b := by
  subst t
  rfl

lemma forcedReward_nonneg {u k : ℕ} (a : Assignment k) (S : PairState u k) :
    0 ≤ forcedReward a S := by unfold forcedReward; split <;> norm_num

lemma forcedReward_le_one {u k : ℕ} (a : Assignment k) (S : PairState u k) :
    forcedReward a S ≤ 1 := by unfold forcedReward; split <;> norm_num

lemma forcedReward_le_alive {u k : ℕ} (a : Assignment k) (S : PairState u k) :
    forcedReward a S ≤ alive u (fibre a S) := by
  unfold forcedReward
  split_ifs with h
  · obtain ⟨x,hx⟩ := h.1
    have hf : (fibre a S).Nonempty := by
      refine ⟨x.2, ?_⟩
      have he : (a,x.2) = x := by rw [← h.2 x hx]
      simp [fibre, he, hx]
    simp [alive, hf]
  · exact alive_nonneg _ _

lemma pairEvolution_drift {u k : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : ℕ → RootData u k) (i : ℕ) (S : PairState u k) :
    forcedReward a S + uniformStep (pairEvolution a env) i (fun T => lifetime u k (fibre a T)) S ≤
      lifetime u k (fibre a S) + (if rootSize (env i).1 = 0 then 0 else 1) := by
  rw [pairEvolution_fibre_operator hku]
  have hd := scheduledStep_drift hku (fun i => rootSize (env i).1 = 0)
    (fun i => dataMask (env i) a) i (fibre a S)
  linarith [forcedReward_le_alive a S]

lemma rootPath_square {u k : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : ℕ → RootData u k) (m : ℕ) {Z : ℝ}
    (hZ : (∑ i ∈ Finset.range m, if rootSize (env i).1 = 0 then (0 : ℝ) else 1) ≤ Z)
    (S : PairState u k) :
    favg (fun w : Fin m → RefreshNoise u k =>
      (pathReward (pairEvolution a env) (forcedReward a) m w S)^2) ≤
      2 * markovSum (uniformStep (pairEvolution a env))
        (fun T => forcedReward a T * (lifetime u k (fibre a T)+Z)) m S := by
  let := clause_nonempty u k hku
  let := clause_nonempty u (k-1) (by omega)
  exact pathReward_sq_potential _ _ _ (forcedReward_nonneg a)
    (fun T => lifetime_nonneg _ _ _) _ (fun _ => by split <;> norm_num)
    (pairEvolution_drift hku a env) m hZ S

lemma rootRewards_avg {u k : ℕ} (hku : k ≤ u) (a : Assignment k) (env : ℕ → RootData u k)
    (f : PairState u k → ℝ) (M : ℕ) (S : PairState u k) :
    favg (fun z : Fin M → RefreshNoise u k =>
      dataRewards f S (fun i => refreshData a (env i) (z i))) =
      markovSum (uniformStep (pairEvolution a env)) f M S := by
  let := clause_nonempty u k hku
  let := clause_nonempty u (k-1) (by omega)
  simp_rw [← rootPath_eq_rewards]
  exact pathReward_avg _ _ _ _

lemma favg_noiseWord {u k M : ℕ} (f : (Fin M → RefreshNoise u k) → ℝ) :
    favg f = favg (fun o : Fin M → Clause u k =>
      favg (fun ys : Fin k → Fin M → Clause u (k-1) => f (fun i => (o i, fun j => ys j i)))) := by
  rw [← favg_equiv (noiseWordEquiv u k M).symm f, favg_prod]
  rfl

lemma dataSatisfies_refresh_fixed {u k : ℕ} (a : Assignment k) (p : RootData u k)
    (z : RefreshNoise u k) (b : Assignment u) :
    DataSatisfies (refreshData a p z) (a,b) ↔
      if rootSize p.1 = 0 then Satisfies z.1 b else DataSatisfies p (a,b) := by
  by_cases h : rootSize p.1 = 0
  · simp [DataSatisfies, refreshData, refreshPart, h, rootSatisfies_zero p.1 h a,
      satisfies_cast]
  · by_cases ht : rootSize p.1 = 1 ∧ RootSatisfies p.1 a
    · simp [DataSatisfies, refreshData, refreshPart, ht]
    · simp [DataSatisfies, refreshData, refreshPart, h, ht]

lemma fibre_pairPrefix_refresh {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (o : Fin M → Clause u k) (ys : Fin k → Fin M → Clause u (k-1)) (m : ℕ) :
    fibre a (pairPrefix Finset.univ (fun i => refreshData a (env i) (o i, fun j => ys j i)) m) =
      fibrePrefix a env o m := by
  ext b
  simp only [fibre, pairPrefix, fibrePrefix, Finset.mem_filter, Finset.mem_univ, true_and,
    dataSatisfies_refresh_fixed]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.WeightedRewards ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma markovSum_projection.{u_1, u_2} {X : Type u_1} {Y : Type u_2}
    (P : ℕ → (X → ℝ) → X → ℝ) (Q : ℕ → (Y → ℝ) → Y → ℝ)
    (π : X → Y) (hπ : ∀ i f x, P i (fun y => f (π y)) x = Q i f (π x))
    (f : Y → ℝ) (M : ℕ) (x : X) :
    markovSum P (fun y => f (π y)) M x = markovSum Q f M (π x) := by
  induction M generalizing P Q x with
  | zero => rfl
  | succ M ih =>
    simp only [markovSum]
    have he : markovSum (fun i => P (i+1)) (fun y => f (π y)) M =
        fun y => markovSum (fun i => Q (i+1)) f M (π y) := by
      funext y
      exact ih _ _ (fun i => hπ (i+1)) y
    rw [he, hπ]

lemma rootSum_projection {u k : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : ℕ → RootData u k) (f : Finset (Assignment u) → ℝ) (M : ℕ) (S : PairState u k) :
    markovSum (uniformStep (pairEvolution a env)) (fun T => f (fibre a T)) M S =
      markovSum (scheduledStep u k (fun i => rootSize (env i).1 = 0)
        (fun i => dataMask (env i) a)) f M (fibre a S) :=
  markovSum_projection _ _ _ (pairEvolution_fibre_operator hku a env) f M S

lemma fibre_univ {u k : ℕ} (a : Assignment k) :
    fibre (u := u) a Finset.univ = Finset.univ := by ext b; simp [fibre]

lemma rootSum_test_bound {u k M d : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : ℕ → RootData u k) (J : Finset (Fin k))
    (hJ : ∀ j ∈ J, Available a (fun i : Fin M => env i) j)
    (hd : ∀ m j, (testIndices a (fun i : Fin M => env i) m j).card ≤ d)
    (w : Finset (Assignment u) → ℝ) (hw : ∀ S, 0 ≤ w S) :
    markovSum (uniformStep (pairEvolution a env))
      (fun T => forcedReward a T * w (fibre a T)) M Finset.univ ≤
    markovSum (scheduledStep u k (fun i => rootSize (env i).1 = 0)
      (fun i => dataMask (env i) a))
      (fun S => w S * (alive u S * blockKill u (k-1) S d ^ J.card)) M Finset.univ := by
  let := clause_nonempty u k hku
  let := clause_nonempty u (k-1) (by omega)
  rw [← fibre_univ (u := u) a, ← rootSum_projection hku]
  rw [← rootRewards_avg hku, ← rootRewards_avg hku]
  rw [favg_noiseWord, favg_noiseWord]
  apply favg_mono
  intro o
  unfold dataRewards
  rw [favg_sum, favg_sum]
  apply Finset.sum_le_sum
  intro m _
  simp only [fibre_pairPrefix_refresh]
  have he : favg (fun ys : Fin k → Fin M → Clause u (k-1) =>
      forcedReward a (pairPrefix Finset.univ
        (fun i => refreshData a (env i) (o i,fun j => ys j i)) m.val) *
        w (fibrePrefix a (fun i : Fin M => env i) o m.val)) =
      w (fibrePrefix a (fun i : Fin M => env i) o m.val) *
      favg (fun ys : Fin k → Fin M → Clause u (k-1) =>
        forcedReward a (pairPrefix Finset.univ
          (fun i => refreshData a (env i) (o i,fun j => ys j i)) m.val)) := by
    simp_rw [mul_comm _ (w _)]
    exact favg_mul _ _
  rw [he, favg_const]
  exact mul_le_mul_of_nonneg_left (forcedPrefix_probability hku a _ o m.val J hJ (hd _)) (hw _)

lemma testIndices_card_le {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (m : ℕ) (j : Fin k) : (testIndices a env m j).card ≤ (incidentSet env).card := by
  apply Finset.card_le_card
  intro i hi
  have hh := (Finset.mem_filter.mp hi).2.2.1
  simp [incidentSet, hh]

lemma incidentSet_sum {u k : ℕ} (env : ℕ → RootData u k) (M : ℕ) :
    (∑ i ∈ Finset.range M, if rootSize (env i).1 = 0 then (0 : ℝ) else 1) =
      ((incidentSet (fun i : Fin M => env i)).card : ℝ) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [incidentSet, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

lemma available_of_no_collision {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (hV : (collisionSet env).card = 0) (j : Fin k) : Available a env j := by
  intro i hi
  have hm : i ∈ collisionSet env := by simp [collisionSet, hi]
  rw [Finset.card_eq_zero.mp hV] at hm
  exact (Finset.notMem_empty i hm).elim

lemma uniqueTrue_injective {k : ℕ} (t : RootType k) (a : Assignment k) {i j : Fin k}
    (hi : UniqueTrue t a i) (hj : UniqueTrue t a j) : i = j := by
  by_contra h
  exact hj.2 i h hi.1

lemma available_except_one {u k M : ℕ} (hk : 1 ≤ k) (a : Assignment k)
    (env : Fin M → RootData u k) (hV : (collisionSet env).card ≤ 1) :
    ∃ j₀ : Fin k, ∀ j, j ≠ j₀ → Available a env j := by
  by_cases hbad : ∃ j : Fin k, ¬ Available a env j
  · obtain ⟨j₀,hj₀⟩ := hbad
    refine ⟨j₀,fun j hj i hi hij => ?_⟩
    obtain ⟨i₀,hi₀,hij₀⟩ : ∃ i, 2 ≤ rootSize (env i).1 ∧ UniqueTrue (env i).1 a j₀ := by
      simp only [Available] at hj₀
      push Not at hj₀
      exact hj₀
    have he : i = i₀ := Finset.card_le_one.mp hV i
      (by simp [collisionSet, hi]) i₀ (by simp [collisionSet, hi₀])
    subst i₀
    exact hj (uniqueTrue_injective _ _ hij hij₀)
  · refine ⟨⟨0, by omega⟩, fun j _ => ?_⟩
    by_contra hj
    exact hbad ⟨j,hj⟩

lemma lifetimeBeta_bounds {r : ℕ} (hr : 2 ≤ r) :
    1 ≤ lifetimeBeta (r+1) ∧ lifetimeBeta (r+1) ≤ (r : ℝ) ∧
      2*lifetimeBeta (r+1) ≤ 3 := by
  rw [lifetimeBeta_succ (by omega)]
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hi : (0 : ℝ) ≤ (r : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hj : (r : ℝ)⁻¹ ≤ 1/2 := by
    apply (inv_le_iff_one_le_mul₀ (by positivity)).2
    linarith
  constructor
  · linarith
  constructor <;> linarith

lemma deletionQ_nonneg {r d : ℕ} (hr : 2 ≤ r) : 0 ≤ deletionQ (r+1) d := by
  unfold deletionQ
  exact mul_nonneg (by linarith [lifetimeC_pos (by omega : 1 ≤ r)])
    (Real.rpow_nonneg (by positivity) _)

lemma lifetime_weight_product {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    {Z : ℝ} (hZ : 0 ≤ Z) (hZd : Z ≤ d) (S : Finset (Assignment u)) :
    (lifetime u (r+1) S+Z) * (blockKill u r S d)^(lifetimeBeta (r+1)) ≤ deletionQ (r+1) d := by
  have hb := lifetimeBeta_bounds hr
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (d : ℝ) ≤ (d : ℝ)^(lifetimeBeta (r+1)) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hd1 hb.1
  have hq := Real.rpow_le_one (blockKill_nonneg u r S d) (blockKill_le_one (by omega) S d)
    (by linarith : 0 ≤ lifetimeBeta (r+1))
  have ht := lifetime_product hr hru hd S
  unfold deletionQ
  nlinarith [mul_nonneg hZ (sub_nonneg.mpr hq)]

lemma weighted_all_tests {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    {Z : ℝ} (hZ : 0 ≤ Z) (hZd : Z ≤ d) (S : Finset (Assignment u)) :
    (lifetime u (r+1) S+Z) * (alive u S * blockKill u r S d ^ (r+1)) ≤
      deletionQ (r+1) d * occupationReward u r d S := by
  by_cases hS : S.Nonempty
  · simp only [alive, occupationReward, ite_eq_left hS, one_mul]
    by_cases hq : blockKill u r S d = 0
    · simp only [hq, zero_pow (by omega : r+1 ≠ 0), mul_zero]
      exact mul_nonneg (deletionQ_nonneg hr) (Real.rpow_nonneg (by norm_num) _)
    · have hqp : 0 < blockKill u r S d := lt_of_le_of_ne (blockKill_nonneg _ _ _ _) (Ne.symm hq)
      have he : (blockKill u r S d)^(r+1) =
          (blockKill u r S d)^(lifetimeBeta (r+1)) * (blockKill u r S d)^(occupationGamma (r+1)) := by
        rw [← Real.rpow_add hqp, occupationGamma]
        simp only [add_sub_cancel, Real.rpow_natCast]
      rw [he, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (lifetime_weight_product hr hru hd hZ hZd S)
        (Real.rpow_nonneg hqp.le _)
  · simp [alive, occupationReward, hS]

lemma weighted_all_but_one_test {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    {Z : ℝ} (hZ : 0 ≤ Z) (hZd : Z ≤ d) (S : Finset (Assignment u)) :
    (lifetime u (r+1) S+Z) * (alive u S * blockKill u r S d ^ r) ≤ deletionQ (r+1) d := by
  by_cases hS : S.Nonempty
  · simp only [alive, ite_eq_left hS, one_mul]
    by_cases hq : blockKill u r S d = 0
    · simpa only [hq, zero_pow (by omega : r ≠ 0), mul_zero] using deletionQ_nonneg (d := d) hr
    · have hqp : 0 < blockKill u r S d := lt_of_le_of_ne (blockKill_nonneg _ _ _ _) (Ne.symm hq)
      have hpow : (blockKill u r S d)^r ≤ (blockKill u r S d)^(lifetimeBeta (r+1)) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge hqp (blockKill_le_one (by omega) S d)
          (lifetimeBeta_bounds hr).2.1
      exact (mul_le_mul_of_nonneg_left hpow (add_nonneg (lifetime_nonneg _ _ _) hZ)).trans
        (lifetime_weight_product hr hru hd hZ hZd S)
  · simp only [alive, ite_eq_right hS, zero_mul, mul_zero]
    exact deletionQ_nonneg hr

lemma scheduledStep_mul (u k : ℕ) (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ) (c : ℝ) (f : Finset (Assignment u) → ℝ) :
    scheduledStep u k ordinary mask i (fun S => c*f S) =
      fun S => c*scheduledStep u k ordinary mask i f S := by
  funext S
  unfold scheduledStep
  split
  · exact favg_mul c _
  · rfl

lemma rootRewards_square_test_bound {u k M d : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : ℕ → RootData u k) (J : Finset (Fin k))
    (hJ : ∀ j ∈ J, Available a (fun i : Fin M => env i) j)
    (hd : ∀ m j, (testIndices a (fun i : Fin M => env i) m j).card ≤ d)
    {Z : ℝ} (hZ : 0 ≤ Z)
    (hcount : ((incidentSet (fun i : Fin M => env i)).card : ℝ) ≤ Z) :
    favg (fun z : Fin M → RefreshNoise u k =>
      (dataRewards (forcedReward a) Finset.univ (fun i => refreshData a (env i) (z i)))^2) ≤
      2*markovSum (scheduledStep u k (fun i => rootSize (env i).1 = 0)
        (fun i => dataMask (env i) a))
        (fun S => (lifetime u k S+Z)*(alive u S * blockKill u (k-1) S d ^ J.card)) M Finset.univ := by
  have hh := rootPath_square hku a env M (Z := Z) (by rw [incidentSet_sum]; exact hcount) (Finset.univ : PairState u k)
  simp_rw [rootPath_eq_rewards] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (rootSum_test_bound hku a env J hJ hd (fun S : Finset (Assignment u) => lifetime u k S+Z)
      (fun S => add_nonneg (lifetime_nonneg _ _ _) hZ)) (by norm_num))

lemma durationLog_one_le (k M : ℕ) : 1 ≤ durationLog k M := by
  unfold durationLog
  split
  · have h : (1 : ℝ) ≤ M+1 := by linarith [Nat.cast_nonneg (α := ℝ) M]
    linarith [Real.log_nonneg h]
  · rfl

lemma rootRewards_square_no_collision {u r M d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (hd : 1 ≤ d) (a : Assignment (r+1)) (env : ℕ → RootData u (r+1))
    (hV : (collisionSet (fun i : Fin M => env i)).card = 0)
    {Z : ℝ} (hZ : 0 ≤ Z) (hZd : Z ≤ d)
    (hcount : ((incidentSet (fun i : Fin M => env i)).card : ℝ) ≤ Z) :
    favg (fun z : Fin M → RefreshNoise u (r+1) =>
      (dataRewards (forcedReward a) Finset.univ (fun i => refreshData a (env i) (z i)))^2) ≤
      8*(deletionQ (r+1) d)^2*durationLog (r+1) M := by
  have htests (m) (j : Fin (r+1)) :
      (testIndices a (fun i : Fin M => env i) m j).card ≤ d := by
    have hh := testIndices_card_le a (fun i : Fin M => env i) m j
    have hh' : ((incidentSet (fun i : Fin M => env i)).card : ℝ) ≤ d := hcount.trans hZd
    exact hh.trans (by exact_mod_cast hh')
  have hh := rootRewards_square_test_bound hru a env Finset.univ
    (fun j _ => available_of_no_collision a _ hV j) htests hZ hcount
  simp only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] at hh
  have hm := markovSum_mono _
    (scheduledStep_mono u (r+1) (fun i => rootSize (env i).1 = 0) (fun i => dataMask (env i) a))
    (weighted_all_tests hr hru hd hZ hZd) M (Finset.univ : Finset (Assignment u))
  rw [markovSum_mul _ (scheduledStep_mul _ _ _ _)] at hm
  have ho := integrated_occupationReward hr hru hd (fun i => rootSize (env i).1 = 0)
    (fun i => dataMask (env i) a) M hZ hZd (by rw [incidentSet_sum]; exact hcount) Finset.univ
  have hp := mul_le_mul_of_nonneg_left ho (deletionQ_nonneg (d := d) hr)
  nlinarith

lemma rootRewards_square_one_collision {u r M d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (hd : 1 ≤ d) (a : Assignment (r+1)) (env : ℕ → RootData u (r+1))
    (hV : (collisionSet (fun i : Fin M => env i)).card ≤ 1)
    {Z : ℝ} (hZ : 0 ≤ Z) (hZd : Z ≤ d)
    (hcount : ((incidentSet (fun i : Fin M => env i)).card : ℝ) ≤ Z) :
    favg (fun z : Fin M → RefreshNoise u (r+1) =>
      (dataRewards (forcedReward a) Finset.univ (fun i => refreshData a (env i) (z i)))^2) ≤
      2*M*deletionQ (r+1) d := by
  obtain ⟨j₀,hj₀⟩ := available_except_one (by omega : 1 ≤ r+1) a _ hV
  have htests (m) (j : Fin (r+1)) :
      (testIndices a (fun i : Fin M => env i) m j).card ≤ d := by
    have hh := testIndices_card_le a (fun i : Fin M => env i) m j
    have hh' : ((incidentSet (fun i : Fin M => env i)).card : ℝ) ≤ d := hcount.trans hZd
    exact hh.trans (by exact_mod_cast hh')
  have hh := rootRewards_square_test_bound hru a env (Finset.univ.erase j₀)
    (fun j hj => hj₀ j (Finset.mem_erase.mp hj).1) htests hZ hcount
  have hc : (Finset.univ.erase j₀).card = r := by simp
  rw [hc] at hh
  simp only [Nat.add_sub_cancel] at hh
  have hm := markovSum_mono _
    (scheduledStep_mono u (r+1) (fun i => rootSize (env i).1 = 0) (fun i => dataMask (env i) a))
    (weighted_all_but_one_test hr hru hd hZ hZd) M (Finset.univ : Finset (Assignment u))
  rw [markovSum_const _ (scheduledStep_const hru _ _)] at hm
  nlinarith

lemma dataRewards_nonneg {u k M : ℕ} (a : Assignment k) (S : PairState u k)
    (ps : Fin M → RootData u k) : 0 ≤ dataRewards (forcedReward a) S ps :=
  Finset.sum_nonneg fun _ _ => forcedReward_nonneg _ _

lemma dataRewards_le_length {u k M : ℕ} (a : Assignment k) (S : PairState u k)
    (ps : Fin M → RootData u k) : dataRewards (forcedReward a) S ps ≤ M := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M))) (fun i _ => forcedReward_le_one a (pairPrefix S ps i.val))
  simpa [dataRewards] using hh

lemma rootRewards_square_conditioned {u r M : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (a : Assignment (r+1)) (env : ℕ → RootData u (r+1)) :
    let Z := (incidentSet (fun i : Fin M => env i)).card
    let V : ℝ := (collisionSet (fun i : Fin M => env i)).card
    let Q := deletionQ (r+1) (max 1 Z)
    favg (fun z : Fin M → RefreshNoise u (r+1) =>
      (dataRewards (forcedReward a) Finset.univ (fun i => refreshData a (env i) (z i)))^2) ≤
      8*Q^2*durationLog (r+1) M + 2*M*Q*V + (M : ℝ)^2*V*(V-1) := by
  dsimp only
  let Z := (incidentSet (fun i : Fin M => env i)).card
  let V := (collisionSet (fun i : Fin M => env i)).card
  let Q := deletionQ (r+1) (max 1 Z)
  have hQ : 0 ≤ Q := deletionQ_nonneg hr
  have hZF : (Z : ℝ) ≤ (max 1 Z : ℕ) := by exact_mod_cast le_max_right 1 Z
  have hterm : 0 ≤ 8*Q^2*durationLog (r+1) M := by
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (le_trans (by norm_num) (durationLog_one_le _ _))
  change _ ≤ 8*Q^2*durationLog (r+1) M+2*M*Q*(V : ℝ)+(M : ℝ)^2*V*(V-1)
  by_cases hV : V = 0
  · have hh := rootRewards_square_no_collision hr hru (le_max_left 1 Z) a env hV
      (Nat.cast_nonneg Z) hZF (le_refl (Z : ℝ))
    simpa only [hV, Nat.cast_zero, mul_zero, zero_mul, add_zero] using hh
  by_cases hV1 : V ≤ 1
  · have he : V = 1 := by omega
    have hh := rootRewards_square_one_collision hr hru (le_max_left 1 Z) a env hV1
      (Nat.cast_nonneg Z) hZF (le_refl (Z : ℝ))
    simp only [he, Nat.cast_one, mul_one, sub_self, mul_zero, add_zero]
    exact hh.trans (le_add_of_nonneg_left hterm)
  · have hv : (2 : ℝ) ≤ V := by exact_mod_cast (by omega : 2 ≤ V)
    have htriv : favg (fun z : Fin M → RefreshNoise u (r+1) =>
        (dataRewards (forcedReward a) Finset.univ (fun i => refreshData a (env i) (z i)))^2) ≤ (M : ℝ)^2 := by
      let := clause_nonempty u (r+1) hru
      let := clause_nonempty u ((r+1)-1) (by omega)
      exact (favg_mono (fun z => pow_le_pow_left₀ (dataRewards_nonneg a _ _) (dataRewards_le_length a _ _) 2)).trans_eq (favg_const _)
    have hfac : 1 ≤ (V : ℝ)*(V-1) := by nlinarith
    have hmfac := mul_le_mul_of_nonneg_left hfac (sq_nonneg (M : ℝ))
    have hmQ : 0 ≤ 2*M*Q*(V : ℝ) := by positivity
    nlinarith

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.rootRewards_square_conditioned := @_root_.OAI.RandomKSAT.rootRewards_square_conditioned
