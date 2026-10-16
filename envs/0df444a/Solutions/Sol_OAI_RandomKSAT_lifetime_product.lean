-- Prove2me | solution 1 for OAI.RandomKSAT.lifetime_product
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:53:34.386979+00:00
-- url     : https://prove2.me/submissions/c7cba3f7-0b75-4d3c-9358-349a2a6d72f0

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/MarkovReplacement.lean:L381-L425
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.lifetime_product. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Theorems.Thm_OAI_RandomKSAT_one_replacement

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

lemma clauseStep_add (u s : ℕ) (f g : Finset (Assignment u) → ℝ) :
    clauseStep u s (f+g) = clauseStep u s f + clauseStep u s g := by
  funext S
  exact favg_add _ _

lemma clauseStep_comm (u r s : ℕ) : Function.Commute (clauseStep u r) (clauseStep u s) := by
  intro f
  funext S
  unfold clauseStep
  rw [favg_comm]
  congr 1
  funext d
  congr 1
  funext c
  congr 1
  ext a
  simp only [Finset.mem_filter]
  tauto

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

lemma iterate_add_const.{u_1} {α : Type u_1} (A : (α → ℝ) → (α → ℝ))
    (hA : ∀ f c, A (f + fun _ => c) = A f + fun _ => c)
    (m : ℕ) (f : α → ℝ) (c : ℝ) :
    A^[m] (f + fun _ => c) = A^[m] f + fun _ => c := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, hA, Function.iterate_succ_apply']

lemma markov_telescoping.{u_1} {α : Type u_1} (A B : (α → ℝ) → (α → ℝ))
    (hA : Monotone A) (hB : Monotone B)
    (hAc : ∀ f c, A (f + fun _ => c) = A f + fun _ => c)
    (hBc : ∀ f c, B (f + fun _ => c) = B f + fun _ => c)
    (hcomm : Function.Commute A B) (f : α → ℝ) (δ : ℝ)
    (hone : A f ≤ B f + fun _ => δ) (d : ℕ) :
    A^[d] f ≤ B^[d] f + fun _ => (d : ℝ)*δ := by
  induction d with
  | zero => intro x; simp
  | succ d ih =>
    have h₁ := hA.iterate d hone
    rw [iterate_add_const A hAc, hcomm.iterate_left d f] at h₁
    have h₂ := hB ih
    rw [hBc, ← Function.iterate_succ_apply' B d f] at h₂
    intro x
    have h₁x := h₁ x
    have h₂x := h₂ x
    simp only [Pi.add_apply] at h₁x h₂x
    rw [Function.iterate_succ_apply]
    change A^[d] (A f) x ≤ B^[d+1] f x + ((d+1 : ℕ) : ℝ)*δ
    push_cast
    linarith

lemma clauseStep_add_const {u s : ℕ} (hsu : s ≤ u)
    (f : Finset (Assignment u) → ℝ) (c : ℝ) :
    clauseStep u s (f + fun _ => c) = clauseStep u s f + fun _ => c := by
  rw [clauseStep_add, clauseStep_const hsu]

lemma sequential_replacement {u r g : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hg : 1 ≤ g)
    (S : Finset (Assignment u)) (d : ℕ) :
    blockKill u r S d - (d : ℝ)*replacementK (r+1)/(g : ℝ)^r ≤
      blockKill u (r+1) S (d*g) := by
  have hru' : r ≤ u := by omega
  have hone : (clauseStep u (r+1))^[g] (alive u) ≤
      clauseStep u r (alive u) + fun _ => replacementK (r+1)/(g : ℝ)^r := by
    intro S'
    have h := one_replacement hr hru hg S'
    rw [blockKill_iterate hru', blockKill_iterate hru, Function.iterate_one] at h
    change _ ≤ clauseStep u r (alive u) S' + replacementK (r+1)/(g : ℝ)^r
    linarith
  have hh := markov_telescoping (clauseStep u (r+1))^[g] (clauseStep u r)
    ((clauseStep_mono u (r+1)).iterate g) (clauseStep_mono u r)
    (iterate_add_const _ (clauseStep_add_const hru) g)
    (clauseStep_add_const hru') ((clauseStep_comm u (r+1) r).iterate_left g)
    (alive u) (replacementK (r+1)/(g : ℝ)^r) hone d S
  rw [← Function.iterate_mul, Nat.mul_comm g d] at hh
  rw [blockKill_iterate hru', blockKill_iterate hru]
  change _ ≤ _
  simp only [Pi.add_apply, ← mul_div_assoc] at hh
  linarith

lemma favg_mul.{u_1} {α : Type u_1} [Fintype α] (c : ℝ) (f : α → ℝ) :
    favg (fun a => c*f a) = c*favg f := by
  simp only [favg, ← Finset.mul_sum]
  ring

lemma favg_nonneg.{u_1} {α : Type u_1} [Fintype α] {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ favg f := by
  exact div_nonneg (Finset.sum_nonneg fun a _ => h a) (by positivity)

lemma residual_subset.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι]
    (S : Finset (Assignment u)) (cs : ι → Clause u s) : residual S cs ⊆ S :=
  Finset.filter_subset _ _

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

lemma survival_empty (u s m : ℕ) : survival u s ∅ m = 0 := by
  simp [survival_avg, residual, alive, favg]

lemma survival_nonneg (u s : ℕ) (S : Finset (Assignment u)) (m : ℕ) :
    0 ≤ survival u s S m := by
  rw [survival_avg]
  exact favg_nonneg fun _ => alive_nonneg _ _

lemma survival_le_one {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (m : ℕ) :
    survival u s S m ≤ 1 := by
  let := clause_nonempty u s hsu
  rw [survival_avg, ← favg_const (α := Fin m → Clause u s) (1 : ℝ)]
  exact favg_mono fun _ => alive_le_one _ _

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

lemma survival_add (u s : ℕ) (S : Finset (Assignment u)) (m j : ℕ) :
    survival u s S (m+j) =
      favg fun cs : Fin m → Clause u s => survival u s (residual S cs) j := by
  unfold survival
  rw [Function.iterate_add_apply, clauseStep_iterate_avg]

lemma survival_submultiplicative (u s : ℕ) (S : Finset (Assignment u)) (m j : ℕ) :
    survival u s S (m+j) ≤ survival u s S m * survival u s S j := by
  rw [survival_add]
  calc
    _ ≤ favg (fun cs : Fin m → Clause u s =>
        survival u s S j * alive u (residual S cs)) := by
      apply favg_mono
      intro cs
      by_cases he : (residual S cs).Nonempty
      · simpa [alive, he] using survival_mono (residual_subset S cs) j
      · have he' := Finset.not_nonempty_iff_eq_empty.mp he
        simp [he', alive, survival_empty]
    _ = _ := by rw [favg_mul, ← survival_avg]; ring

lemma lifetime_block {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (m : ℕ)
    (hR : 0 < blockKill u s S m) :
    lifetime u s S ≤ (m : ℝ) / blockKill u s S m := by
  have hsum := survival_summable hsu S
  have hsplit := hsum.sum_add_tsum_nat_add m
  have hhead : ∑ i ∈ Finset.range m, survival u s S i ≤ (m : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range m, (1 : ℝ) := Finset.sum_le_sum fun i _ => survival_le_one hsu S i
      _ = _ := by simp
  have htail : (∑' j, survival u s S (j+m)) ≤ survival u s S m * lifetime u s S := by
    rw [lifetime, ← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h))
      (hsum.mul_left _)
    intro j
    change survival u s S (j+m) ≤ _
    rw [Nat.add_comm j m]
    exact survival_submultiplicative u s S m j
  apply (le_div_iff₀ hR).2
  rw [blockKill_iterate hsu]
  change lifetime u s S * (1 - survival u s S m) ≤ (m : ℝ)
  change _ + _ = lifetime u s S at hsplit
  nlinarith

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

lemma replacement_block_choice {r d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d)
    {q : ℝ} (hq : 0 < q) (hq₁ : q ≤ 1) :
    ∃ g : ℕ, 1 ≤ g ∧
      (d : ℝ)*replacementK (r+1)/(g : ℝ)^r ≤ q/2 ∧
      (g : ℝ) ≤ 2*(2*replacementK (r+1)*d/q)^((r : ℝ)⁻¹) := by
  let x : ℝ := (2*replacementK (r+1)*d/q)^((r : ℝ)⁻¹)
  have hK := replacementK_one_le hr
  have hd₀ : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hz : (1 : ℝ) ≤ 2*replacementK (r+1)*d/q := by
    apply (le_div_iff₀ hq).2
    nlinarith
  have hx : 1 ≤ x := Real.one_le_rpow hz (by positivity)
  have hg : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hg₀ : (0 : ℝ) < ⌈x⌉₊ := by exact_mod_cast (by omega : 0 < ⌈x⌉₊)
  refine ⟨⌈x⌉₊, hg, ?_, ?_⟩
  · have hp : 2*replacementK (r+1)*d/q ≤ (⌈x⌉₊ : ℝ)^r := by
      calc
        _ = x^r := (Real.rpow_inv_natCast_pow (by positivity) (by omega : r ≠ 0)).symm
        _ ≤ _ := pow_le_pow_left₀ (by linarith : 0 ≤ x) (Nat.le_ceil x) r
    apply (div_le_iff₀ (pow_pos hg₀ r)).2
    have hh := (div_le_iff₀ hq).mp hp
    nlinarith
  · exact (Nat.ceil_lt_add_one (by linarith : 0 ≤ x)).le.trans (by linarith)

lemma lifetime_product {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    (S : Finset (Assignment u)) :
    lifetime u (r+1) S * (blockKill u r S d)^(lifetimeBeta (r+1)) ≤
      lifetimeC (r+1) * (d : ℝ)^(lifetimeBeta (r+1)) := by
  let q := blockKill u r S d
  have hq₀ : 0 ≤ q := blockKill_nonneg _ _ _ _
  have hq₁ : q ≤ 1 := blockKill_le_one (by omega) _ _
  have hβ : 0 < lifetimeBeta (r+1) := by
    rw [lifetimeBeta_succ (by omega)]
    positivity
  have hK := replacementK_one_le (by omega : 1 ≤ r)
  have hC := lifetimeC_pos (by omega : 1 ≤ r)
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases hq : q = 0
  · change lifetime u (r+1) S * q^_ ≤ _
    rw [hq, Real.zero_rpow (ne_of_gt hβ), mul_zero]
    exact mul_nonneg hC.le (Real.rpow_nonneg hd₀.le _)
  · have hq : 0 < q := lt_of_le_of_ne hq₀ (Ne.symm hq)
    obtain ⟨g, hg, herr, hgub⟩ := replacement_block_choice (by omega : 1 ≤ r) hd hq hq₁
    have hR : q/2 ≤ blockKill u (r+1) S (d*g) := by
      have hh := sequential_replacement hr hru hg S d
      change q - _ ≤ _ at hh
      linarith
    have hR₀ : 0 < blockKill u (r+1) S (d*g) := lt_of_lt_of_le (by linarith) hR
    have hτ : lifetime u (r+1) S ≤ 4 * (2*replacementK (r+1))^((r : ℝ)⁻¹) *
        ((d : ℝ)/q)^(1+(r : ℝ)⁻¹) := by
      calc
        _ ≤ (d*g : ℕ)/blockKill u (r+1) S (d*g) := lifetime_block hru S (d*g) hR₀
        _ ≤ (d*g : ℕ)/(q/2) := div_le_div_of_nonneg_left (by positivity) (by linarith) hR
        _ ≤ (d : ℝ)*(2*(2*replacementK (r+1)*d/q)^((r : ℝ)⁻¹))/(q/2) := by
          push_cast
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgub hd₀.le) (by positivity)
        _ = _ := by
          rw [show 2*replacementK (r+1)*(d : ℝ)/q =
            (2*replacementK (r+1))*((d : ℝ)/q) by ring,
            Real.mul_rpow (by linarith) (by positivity), Real.rpow_add (by positivity),
            Real.rpow_one]
          ring
    have hCeq : lifetimeC (r+1) = 4 * (2*replacementK (r+1))^((r : ℝ)⁻¹) := by
      simp [lifetimeC]
    rw [← lifetimeBeta_succ (by omega), ← hCeq] at hτ
    rw [Real.div_rpow hd₀.le hq.le] at hτ
    change lifetime u (r+1) S * q^_ ≤ _
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hq _)).mp
    simpa only [mul_div_assoc] using hτ

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.lifetime_product := @_root_.OAI.RandomKSAT.lifetime_product
