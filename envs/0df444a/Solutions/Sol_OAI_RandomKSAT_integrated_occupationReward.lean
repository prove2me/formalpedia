-- Prove2me | solution 1 for OAI.RandomKSAT.integrated_occupationReward
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:22:57.973361+00:00
-- url     : https://prove2.me/submissions/4b650faf-ef6b-4949-8b76-574ff1b85f93

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/WeightedRewards.lean:L235-L286
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.integrated_occupationReward. The node keeps its source
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
import Theorems.Thm_OAI_RandomKSAT_lifetime_product
import Theorems.Thm_OAI_RandomKSAT_markovSum_potential
import Theorems.Thm_OAI_RandomKSAT_scheduled_reward_integrated_critical

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

lemma clauseStep_add (u s : ℕ) (f g : Finset (Assignment u) → ℝ) :
    clauseStep u s (f+g) = clauseStep u s f + clauseStep u s g := by
  funext S
  exact favg_add _ _

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

lemma clauseStep_add_const {u s : ℕ} (hsu : s ≤ u)
    (f : Finset (Assignment u) → ℝ) (c : ℝ) :
    clauseStep u s (f + fun _ => c) = clauseStep u s f + fun _ => c := by
  rw [clauseStep_add, clauseStep_const hsu]

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

-- ---- from OAI.Probability.SATVariance.OccupationBounds ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma integrated_tail_subcritical {F : ℝ → ℝ} (hF : Antitone F)
    {A θ : ℝ} (hθ : θ < 1)
    (hbound : ∀ a ∈ Set.Ioo (0 : ℝ) 1, F a ≤ A * a^(-θ)) :
    (∫ a in (0 : ℝ)..1, F a) ≤ A / (1-θ) := by
  have hp : -1 < -θ := by linarith
  calc
    (∫ a in (0 : ℝ)..1, F a) ≤ ∫ a in (0 : ℝ)..1, A*a^(-θ) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
        hF.intervalIntegrable ((intervalIntegral.intervalIntegrable_rpow' hp).const_mul A)
      exact hbound
    _ = A/(1-θ) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hp),
        Real.one_rpow, Real.zero_rpow (by linarith : -θ+1 ≠ 0)]
      ring

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.LifetimePotential ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

lemma markovSum_level.{u_1} {X : Type u_1} (P : ℕ → (X → ℝ) → X → ℝ)
    (hP : ∀ i, Monotone (P i))
    (hPc : ∀ i f c, P i (fun x => f x+c) = fun x => P i f x+c)
    (hPconst : ∀ i c, P i (fun _ => c) = fun _ => c)
    (f τ : X → ℝ) (hτ : ∀ x, 0 ≤ τ x) (z : ℕ → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hdrift : ∀ i x, f x + P i τ x ≤ τ x + z i)
    (e : X → ℝ) (hef : e ≤ f) {C : ℝ} (hC : 0 ≤ C)
    (hlevel : ∀ x, e x ≠ 0 → τ x ≤ C) (m : ℕ) (x : X) :
    markovSum P e m x ≤ C + ∑ i ∈ Finset.range m, z i := by
  induction m generalizing P z x with
  | zero => simpa [markovSum] using hC
  | succ m ih =>
    by_cases he : e x = 0
    · have hi := hP 0 (fun y => ih (fun i => P (i+1)) (fun i => hP (i+1))
        (fun i => hPc (i+1)) (fun i => hPconst (i+1)) (fun i => z (i+1))
        (fun i => hz (i+1)) (fun i => hdrift (i+1)) y)
      rw [hPconst] at hi
      change e x + _ ≤ _
      rw [he, zero_add, Finset.sum_range_succ']
      linarith [hi x, hz 0]
    · exact (markovSum_mono P hP hef (m+1) x).trans
        ((markovSum_potential P hP hPc f τ hτ z hdrift (m+1) x).trans
          (by linarith [hlevel x he]))

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

lemma scheduledStep_add_const {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ)
    (f : Finset (Assignment u) → ℝ) (c : ℝ) :
    scheduledStep u k ordinary mask i (fun S => f S+c) =
      fun S => scheduledStep u k ordinary mask i f S+c := by
  funext S
  unfold scheduledStep
  split
  · exact congrFun (clauseStep_add_const hku f c) S
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

lemma tailIndicator_antitone (x : ℝ) :
    Antitone (fun a : ℝ => if a ≤ x then (1 : ℝ) else 0) := by
  intro a b hab
  dsimp only
  by_cases hb : b ≤ x
  · simp [hb, hab.trans hb]
  · simp only [ite_eq_right hb]
    split <;> norm_num

lemma integral_tailIndicator {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (∫ a in (0 : ℝ)..1, if a ≤ x then (1 : ℝ) else 0) = x := by
  have h := intervalIntegral.integral_indicator (μ := volume)
    (f := fun _ : ℝ => (1 : ℝ)) (show x ∈ Set.Icc 0 1 from ⟨hx, hx1⟩)
  simpa [Set.indicator, intervalIntegral.integral_const] using h

lemma favg_integral.{u_1} {α : Type u_1} [Fintype α] (f : α → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ x, IntervalIntegrable (f x) volume a b) :
    favg (fun x => ∫ t in a..b, f x t) = ∫ t in a..b, favg (fun x => f x t) := by
  unfold favg
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum (fun x _ => hf x)]

lemma scheduledStep_antitone {u k : ℕ}
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ)
    (f : ℝ → Finset (Assignment u) → ℝ) (hf : ∀ S, Antitone (fun a => f a S))
    (S : Finset (Assignment u)) :
    Antitone (fun a => scheduledStep u k ordinary mask i (f a) S) := by
  intro a b hab
  exact scheduledStep_mono u k ordinary mask i (fun T => hf T hab) S

lemma scheduledStep_integral {u k : ℕ}
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ)
    (f : ℝ → Finset (Assignment u) → ℝ) (hf : ∀ S, Antitone (fun a => f a S))
    (S : Finset (Assignment u)) (a b : ℝ) :
    scheduledStep u k ordinary mask i (fun T => ∫ t in a..b, f t T) S =
      ∫ t in a..b, scheduledStep u k ordinary mask i (f t) S := by
  unfold scheduledStep
  split
  · simpa only [clauseStep] using favg_integral
      (fun c : Clause u k => fun t => f t (S.filter (Satisfies c)))
      (fun c => (hf _).intervalIntegrable)
  · rfl

lemma scheduledSum_antitone {u k : ℕ}
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u))
    (f : ℝ → Finset (Assignment u) → ℝ) (hf : ∀ S, Antitone (fun a => f a S))
    (L : ℕ) (S : Finset (Assignment u)) :
    Antitone (fun a => markovSum (scheduledStep u k ordinary mask) (f a) L S) := by
  intro a b hab
  exact markovSum_mono _ (scheduledStep_mono u k ordinary mask) (fun T => hf T hab) L S

lemma scheduledSum_integral {u k : ℕ}
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u))
    (f : ℝ → Finset (Assignment u) → ℝ) (hf : ∀ S, Antitone (fun a => f a S))
    (L : ℕ) (S : Finset (Assignment u)) (a b : ℝ) :
    markovSum (scheduledStep u k ordinary mask) (fun T => ∫ t in a..b, f t T) L S =
      ∫ t in a..b, markovSum (scheduledStep u k ordinary mask) (f t) L S := by
  induction L generalizing ordinary mask S with
  | zero => simp [markovSum]
  | succ L ih =>
    change (∫ t in a..b, f t S) + scheduledStep u k ordinary mask 0
      (markovSum (scheduledStep u k (fun i => ordinary (i+1)) (fun i => mask (i+1)))
        (fun T => ∫ t in a..b, f t T) L) S = _
    have he : markovSum (scheduledStep u k (fun i => ordinary (i+1)) (fun i => mask (i+1)))
        (fun T => ∫ t in a..b, f t T) L =
        fun T => ∫ t in a..b, markovSum
          (scheduledStep u k (fun i => ordinary (i+1)) (fun i => mask (i+1))) (f t) L T := by
      funext T
      exact ih _ _ T
    rw [he, scheduledStep_integral _ _ _ _
      (fun T => scheduledSum_antitone _ _ f hf L T)]
    exact (intervalIntegral.integral_add (hf S).intervalIntegrable
      (scheduledStep_antitone _ _ _ _
        (fun T => scheduledSum_antitone _ _ f hf L T) S).intervalIntegrable).symm

lemma scheduled_layercake {u k : ℕ}
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (f : Finset (Assignment u) → ℝ)
    (hf : ∀ S, 0 ≤ f S) (hf1 : ∀ S, f S ≤ 1)
    (L : ℕ) (S : Finset (Assignment u)) :
    markovSum (scheduledStep u k ordinary mask) f L S =
      ∫ a in (0 : ℝ)..1, markovSum (scheduledStep u k ordinary mask)
        (fun T => if a ≤ f T then 1 else 0) L S := by
  have he : f = fun T => ∫ a in (0 : ℝ)..1, if a ≤ f T then (1 : ℝ) else 0 := by
    funext T
    exact (integral_tailIndicator (hf T) (hf1 T)).symm
  conv_lhs => rw [he]
  exact scheduledSum_integral _ _ _ (fun T => tailIndicator_antitone (f T)) L S 0 1

lemma scheduled_reward_tail {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (f : Finset (Assignment u) → ℝ)
    (hfempty : f ∅ = 0) {θ Q : ℝ}
    (hθ : 0 ≤ θ) (hQ : 0 ≤ Q)
    (hprod : ∀ S, lifetime u k S * (f S)^θ ≤ Q) (L : ℕ)
    (S : Finset (Assignment u)) {a : ℝ} (ha : 0 < a) :
    markovSum (scheduledStep u k ordinary mask)
      (fun T => if a ≤ f T then 1 else 0) L S ≤ Q*a^(-θ) +
        ∑ i ∈ Finset.range L, if ordinary i then (0 : ℝ) else 1 := by
  apply markovSum_level _ (scheduledStep_mono u k ordinary mask)
    (scheduledStep_add_const hku ordinary mask) (scheduledStep_const hku ordinary mask)
    (alive u) (lifetime u k) (lifetime_nonneg _ _) _
    (fun _ => by split <;> norm_num) (scheduledStep_drift hku ordinary mask)
  · intro T
    dsimp only
    by_cases hT : T.Nonempty
    · simp only [alive, ite_eq_left hT]
      split <;> norm_num
    · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      subst T
      simp [alive, hfempty, not_le.mpr ha]
  · exact mul_nonneg hQ (Real.rpow_nonneg ha.le _)
  · intro T hT
    have hTa : a ≤ f T := by
      split_ifs at hT with h
      · exact h
      · exact (hT rfl).elim
    have hp := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le hTa hθ)
      (lifetime_nonneg u k T)
    rw [Real.rpow_neg ha.le, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos ha _)).2 (hp.trans (hprod T))

lemma scheduled_reward_tail_bound {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (f : Finset (Assignment u) → ℝ)
    (hfempty : f ∅ = 0) {θ Q Z : ℝ} (hθ : 0 ≤ θ) (hQ : 0 ≤ Q) (hZ : 0 ≤ Z)
    (hprod : ∀ S, lifetime u k S * (f S)^θ ≤ Q) (L : ℕ)
    (hcount : (∑ i ∈ Finset.range L, if ordinary i then (0 : ℝ) else 1) ≤ Z)
    (S : Finset (Assignment u)) {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    markovSum (scheduledStep u k ordinary mask)
      (fun T => if a ≤ f T then 1 else 0) L S ≤ (Q+Z+1)*a^(-θ) := by
  have hp : 1 ≤ a^(-θ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    ha.1 ha.2.le (neg_nonpos.mpr hθ)
  have ht := scheduled_reward_tail hku ordinary mask f hfempty hθ hQ hprod L S ha.1
  nlinarith [mul_nonneg hZ (sub_nonneg.mpr hp)]

lemma scheduled_reward_integrated_subcritical {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (f : Finset (Assignment u) → ℝ)
    (hfempty : f ∅ = 0) (hf : ∀ S, 0 ≤ f S) (hf1 : ∀ S, f S ≤ 1)
    {θ Q Z : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hQ : 0 ≤ Q) (hZ : 0 ≤ Z)
    (hprod : ∀ S, lifetime u k S * (f S)^θ ≤ Q) (L : ℕ)
    (hcount : (∑ i ∈ Finset.range L, if ordinary i then (0 : ℝ) else 1) ≤ Z)
    (S : Finset (Assignment u)) :
    markovSum (scheduledStep u k ordinary mask) f L S ≤ (Q+Z+1)/(1-θ) := by
  rw [scheduled_layercake ordinary mask f hf hf1 L S]
  apply integrated_tail_subcritical
    (scheduledSum_antitone ordinary mask _ (fun T => tailIndicator_antitone (f T)) L S) hθ1
  intro a ha
  exact scheduled_reward_tail_bound hku ordinary mask f hfempty hθ hQ hZ hprod L hcount S ha

lemma occupationGamma_succ {r : ℕ} (hr : 2 ≤ r) :
    occupationGamma (r+1) = lifetimeBeta (r+1) * ((r-1 : ℕ) : ℝ) := by
  rw [occupationGamma, lifetimeBeta_succ (by omega), Nat.cast_add, Nat.cast_one,
    Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  have hr₀ : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  field_simp

lemma occupationGamma_pos {r : ℕ} (hr : 2 ≤ r) : 0 < occupationGamma (r+1) := by
  rw [occupationGamma_succ hr, lifetimeBeta_succ (by omega)]
  have h : (0 : ℝ) < ((r-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r-1)
  positivity

lemma occupationReward_nonneg (u r d : ℕ) (S : Finset (Assignment u)) :
    0 ≤ occupationReward u r d S := by
  unfold occupationReward
  split
  · exact Real.rpow_nonneg (blockKill_nonneg _ _ _ _) _
  · rfl

lemma occupationReward_le_one {u r : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (d : ℕ) (S : Finset (Assignment u)) : occupationReward u r d S ≤ 1 := by
  unfold occupationReward
  split
  · exact Real.rpow_le_one (blockKill_nonneg _ _ _ _) (blockKill_le_one (by omega) _ _)
      (occupationGamma_pos hr).le
  · norm_num

lemma occupationReward_product {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    (S : Finset (Assignment u)) :
    lifetime u (r+1) S * (occupationReward u r d S)^(((r-1 : ℕ) : ℝ)⁻¹) ≤
      lifetimeC (r+1) * (d : ℝ)^(lifetimeBeta (r+1)) := by
  have hθ : (0 : ℝ) < (((r-1 : ℕ) : ℝ)⁻¹) := by
    exact inv_pos.mpr (by exact_mod_cast (by omega : 0 < r-1))
  unfold occupationReward
  split
  · rw [← Real.rpow_mul (blockKill_nonneg _ _ _ _), occupationGamma_succ hr,
      mul_inv_cancel_right₀ (by exact_mod_cast (by omega : r-1 ≠ 0) : ((r-1 : ℕ) : ℝ) ≠ 0)]
    exact lifetime_product hr hru hd S
  · rw [Real.zero_rpow hθ.ne', mul_zero]
    exact mul_nonneg (lifetimeC_pos (by omega : 1 ≤ r)).le (Real.rpow_nonneg (by positivity) _)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.WeightedRewards ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

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

lemma durationLog_one_le (k M : ℕ) : 1 ≤ durationLog k M := by
  unfold durationLog
  split
  · have h : (1 : ℝ) ≤ M+1 := by linarith [Nat.cast_nonneg (α := ℝ) M]
    linarith [Real.log_nonneg h]
  · rfl

lemma integrated_occupationReward {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    (ordinary : ℕ → Prop) [DecidablePred ordinary] (mask : ℕ → Finset (Assignment u))
    (M : ℕ) {Z : ℝ} (hZ : 0 ≤ Z) (hZd : Z ≤ d)
    (hcount : (∑ i ∈ Finset.range M, if ordinary i then (0 : ℝ) else 1) ≤ Z)
    (S : Finset (Assignment u)) :
    markovSum (scheduledStep u (r+1) ordinary mask) (occupationReward u r d) M S ≤
      4*deletionQ (r+1) d * durationLog (r+1) M := by
  let Q := lifetimeC (r+1)*(d : ℝ)^(lifetimeBeta (r+1))
  have hQ : 0 ≤ Q := mul_nonneg (lifetimeC_pos (by omega : 1 ≤ r)).le (Real.rpow_nonneg (by positivity) _)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (d : ℝ) ≤ (d : ℝ)^(lifetimeBeta (r+1)) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hd1 (lifetimeBeta_bounds hr).1
  have hbound : Q+Z+1 ≤ 2*deletionQ (r+1) d := by
    dsimp only [Q, deletionQ]
    have hc := lifetimeC_pos (by omega : 1 ≤ r)
    nlinarith [Real.rpow_nonneg (x := (d : ℝ)) (by positivity) (lifetimeBeta (r+1))]
  have he : occupationReward u r d ∅ = 0 := by simp [occupationReward]
  by_cases hr2 : r = 2
  · subst r
    by_cases hM : M = 0
    · subst M
      simp only [markovSum]
      exact mul_nonneg (mul_nonneg (by norm_num) (deletionQ_nonneg (by omega)))
        (le_trans (by norm_num) (durationLog_one_le _ _))
    · have hp (T : Finset (Assignment u)) : lifetime u 3 T * occupationReward u 2 d T ≤ Q := by
        simpa using occupationReward_product (by omega : 2 ≤ 2) hru hd T
      have hh := scheduled_reward_integrated_critical hru ordinary mask (occupationReward u 2 d)
        he (occupationReward_nonneg _ _ _) (occupationReward_le_one (by omega) hru d)
        hQ hZ hp (by omega : 1 ≤ M) hcount S
      have hlog := Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) (by norm_num : (M : ℝ) ≤ M+1)
      have hpos : 0 ≤ 1+Real.log (M : ℝ) := by
        have h := Real.log_nonneg (show (1 : ℝ) ≤ (M : ℝ) by exact_mod_cast (by omega : 1 ≤ M))
        linarith
      simp only [durationLog, show 2+1=3 from rfl, ↓reduceIte]
      have hbprod := mul_le_mul_of_nonneg_right hbound hpos
      nlinarith [mul_nonneg (deletionQ_nonneg (d := d) (by omega : 2 ≤ 2))
        (sub_nonneg.mpr hlog), mul_nonneg (deletionQ_nonneg (d := d) (by omega : 2 ≤ 2)) hpos]
  · have hr3 : 3 ≤ r := by omega
    have hθ : 0 ≤ (((r-1 : ℕ) : ℝ)⁻¹) := by positivity
    have hθ2 : (((r-1 : ℕ) : ℝ)⁻¹) ≤ 1/2 := by
      apply (inv_le_iff_one_le_mul₀ (by exact_mod_cast (by omega : 0 < r-1))).2
      have h : (2 : ℝ) ≤ (r-1 : ℕ) := by exact_mod_cast (by omega : 2 ≤ r-1)
      linarith
    have hθ1 : (((r-1 : ℕ) : ℝ)⁻¹) < 1 := by linarith
    have hh := scheduled_reward_integrated_subcritical hru ordinary mask (occupationReward u r d)
      he (occupationReward_nonneg _ _ _) (occupationReward_le_one hr hru d)
      hθ hθ1 hQ hZ (occupationReward_product hr hru hd) M hcount S
    have hdiv : (Q+Z+1)/(1-(((r-1 : ℕ) : ℝ)⁻¹)) ≤ 2*(Q+Z+1) := by
      apply (div_le_iff₀ (by linarith)).2
      nlinarith
    simp only [durationLog, ite_eq_right (by omega : r+1 ≠ 3), mul_one]
    exact hh.trans (hdiv.trans (by linarith))

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.integrated_occupationReward := @_root_.OAI.RandomKSAT.integrated_occupationReward
