-- Prove2me | solution 1 for OAI.RandomKSAT.scheduled_reward_integrated_critical
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:06:46.397977+00:00
-- url     : https://prove2.me/submissions/64aa2aa9-64b0-450a-9fda-fe2d6ae5c4f3

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/LifetimePotential.lean:L352-L371
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.scheduled_reward_integrated_critical. The node keeps its source
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
import Theorems.Thm_OAI_RandomKSAT_integrated_tail_critical
import Theorems.Thm_OAI_RandomKSAT_markovSum_potential

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

lemma scheduled_occupation_le_length {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (e : Finset (Assignment u) → ℝ)
    (he : ∀ S, e S ≤ 1) (L : ℕ) (S : Finset (Assignment u)) :
    markovSum (scheduledStep u k ordinary mask) e L S ≤ L := by
  have hm := markovSum_mono _ (scheduledStep_mono u k ordinary mask) he L S
  rw [markovSum_const _ (scheduledStep_const hku ordinary mask) 1] at hm
  simpa using hm

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

lemma scheduled_reward_integrated_critical {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (f : Finset (Assignment u) → ℝ)
    (hfempty : f ∅ = 0) (hf : ∀ S, 0 ≤ f S) (hf1 : ∀ S, f S ≤ 1)
    {Q Z : ℝ} (hQ : 0 ≤ Q) (hZ : 0 ≤ Z)
    (hprod : ∀ S, lifetime u k S * f S ≤ Q) {L : ℕ} (hL : 1 ≤ L)
    (hcount : (∑ i ∈ Finset.range L, if ordinary i then (0 : ℝ) else 1) ≤ Z)
    (S : Finset (Assignment u)) :
    markovSum (scheduledStep u k ordinary mask) f L S ≤ (Q+Z+1)*(1+Real.log L) := by
  rw [scheduled_layercake ordinary mask f hf hf1 L S]
  apply integrated_tail_critical
    (scheduledSum_antitone ordinary mask _ (fun T => tailIndicator_antitone (f T)) L S)
    (by linarith) (by exact_mod_cast hL)
  · intro a
    exact scheduled_occupation_le_length hku ordinary mask _
      (fun T => by split <;> norm_num) L S
  · intro a ha
    have ht := scheduled_reward_tail_bound hku ordinary mask f hfempty
      (by norm_num : (0 : ℝ) ≤ 1) hQ hZ (by simpa using hprod) L hcount S ha
    simpa [Real.rpow_neg_one, div_eq_mul_inv] using ht

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.scheduled_reward_integrated_critical := @_root_.OAI.RandomKSAT.scheduled_reward_integrated_critical
